/*
 * symmetry.c
 *
 * Routines for detecting symmetries
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */

#include <stdlib.h>
#include <stdio.h>
#include <memory.h>
#include "Globals.h"
#include "Intern.h"

struct switch_list {
    struct switch_list *next;
    struct _ex_intern *t1, *t2;
};

static struct _ex_intern *trail;

static struct _ex_intern *sv(struct env *env, struct _ex_intern *e, struct _ex_intern *v1, struct _ex_intern *v2)
{
    if (e==v1) return v2;
    if (e==v2) return v1;

    if (e->user2) return e->user2;

    if (e->type==EXP_APPL) {
        struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
        int i, change;
        change = 0;
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = sv(env,e->u.appl.args[i],v1,v2);
            if (args[i] != e->u.appl.args[i]) change = 1;
        }
        e->next_cache = trail;
        trail = e;
        if (change) {
            return e->user2 = _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
        } else {
            return e->user2 = e;
        }
    }

    return e;
}

static struct _ex_intern *swap_vars(struct env *env, struct _ex_intern *e, struct _ex_intern *v1, struct _ex_intern *v2)
{
    struct _ex_intern *res;
    
    trail = NULL;

    res = sv(env,e,v1,v2);

    while (trail) {
        trail->user2 = NULL;
        trail = trail->next_cache;
    }

    return res;
}

static struct switch_list *symmetric_vars(struct env *env, struct _ex_intern *e)
{
    unsigned *fv;
    int count;
    int i, j;
    struct _ex_intern **vars;
    struct switch_list *s, *sl = NULL;

    fv = _th_get_free_vars(e,&count);
    vars = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
    for (i = 0; i < count; ++i) {
        vars[i] = _ex_intern_var(fv[i]);
    }

    //printf("count = %d\n", count);
    if (count > 200) return NULL;
    for (i = 0; i < count; ++i) {
        //printf("i = %d\n", i);
        for (j = i+1; j < count; ++j) {
            if (_th_get_var_type(env,vars[i]->u.var)==_th_get_var_type(env,vars[j]->u.var)) {
                if (swap_vars(env,e,vars[i],vars[j])==e) {
                    s = (struct switch_list *)_th_alloc(REWRITE_SPACE,sizeof(struct switch_list));
                    s->next = sl;
                    s->t1 = vars[i];
                    s->t2 = vars[j];
                    sl = s;
                    //printf("Symmetric vars %s %s\n", _th_intern_decode(vars[i]->u.var), _th_intern_decode(vars[j]->u.var));
                    _tree_print2("Symmetric vars %s %s", _th_intern_decode(vars[i]->u.var), _th_intern_decode(vars[j]->u.var));
                }
            }
        }
    }

    return sl;
}

static struct add_list *cp(struct env *env, struct _ex_intern *e, struct add_list *tail)
{
    struct add_list *a;

    if (e->user2) return tail;

    e->next_cache = trail;
    trail = e;
    e->user2 = e;

    if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_AND  || e->u.appl.functor==INTERN_OR || e->u.appl.functor==INTERN_NOT ||
        e->u.appl.functor==INTERN_ITE)) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            tail = cp(env,e->u.appl.args[i],tail);
        }
        return tail;
    }
    a = tail;
    while (a) {
        if (a->e==e) return tail;
        a = a->next;
    }

    a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
    a->next = tail;
    a->e = e;

    return a;
}

static int is_un(struct _ex_intern *exp, struct _ex_intern *pred)
{
    int i;

    for (i = 0; i < exp->u.appl.count; ++i) {
        if (pred==exp->u.appl.args[i]) return 1;
        if (exp->u.appl.args[i]->type==EXP_APPL && exp->u.appl.args[i]->u.appl.functor==INTERN_NOT &&
            pred==exp->u.appl.args[i]->u.appl.args[0]) return 1;
    }

    return 0;
}

static struct add_list *filter_unates(struct _ex_intern *e, struct add_list *res)
{
    struct add_list *ret, *prev;

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) e = e->u.appl.args[0];

    if (e->type != EXP_APPL || e->u.appl.functor != INTERN_AND && e->u.appl.functor != INTERN_OR) return res;

    ret = res;
    prev = NULL;
    while (res) {
        if (is_un(e,res->e)) {
            if (prev==NULL) {
                ret = res->next;
            } else {
                prev->next = res->next;
            }
        } else {
            prev = res;
        }
        res = res->next;
    }

    return ret;
}

static struct add_list *collect_predicates(struct env *env, struct _ex_intern *e)
{
    struct add_list *res;

    trail = NULL;

    res = cp(env,e,NULL);

    while (trail) {
        trail->user2 = NULL;
        trail = trail->next_cache;
    }

    res = filter_unates(e,res);

    return res;
}

#define PREDICATE_PAIR_HASH 255

struct pair_info {
    struct pair_info *next;
    struct _ex_intern *term;
    struct add_list *matches[PREDICATE_PAIR_HASH];
};

struct pair_info *pairs[PREDICATE_PAIR_HASH];

static void build_pair_info(struct switch_list *list)
{
    int i;

    for (i = 0; i < PREDICATE_PAIR_HASH; ++i) {
        pairs[i] = NULL;
    }

    while (list) {
        int hash1 = (((int)list->t1)/4)%PREDICATE_PAIR_HASH;
        int hash2 = (((int)list->t2)/4)%PREDICATE_PAIR_HASH;
        struct pair_info *p1;
        struct add_list *p2;

        p1 = pairs[hash1];
        while (p1) {
            if (p1->term==list->t1) goto cont;
            p1 = p1->next;
        }
        p1 = (struct pair_info *)_th_alloc(REWRITE_SPACE,sizeof(struct pair_info));
        p1->next = pairs[hash1];
        pairs[hash1] = p1;
        p1->term = list->t1;
        for (i = 0; i < PREDICATE_PAIR_HASH; ++i) {
            p1->matches[i] = NULL;
        }
cont:
        p2 = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        p2->next = p1->matches[hash2];
        p1->matches[hash2] = p2;
        p2->e = list->t2;
        list = list->next;
    }
}

static int swappable_terms(struct _ex_intern *t1, struct _ex_intern *t2)
{
    struct pair_info *p1;
    struct add_list *p2;
    int hash1, hash2;

    if (t1->type==EXP_VAR && t1==t2) return 0;

    hash1 = (((int)t1)/4)%PREDICATE_PAIR_HASH;
    hash2 = (((int)t2)/4)%PREDICATE_PAIR_HASH;

    p1 = pairs[hash1];
    while (p1) {
        if (p1->term==t1) goto cont;
        p1 = p1->next;
    }
    goto cont1;
cont:
    p2 = p1->matches[hash2];
    while (p2) {
        if (p2->e==t2) {
            return 1;
        }
        p2 = p2->next;
    }
cont1:
    hash1 = (((int)t2)/4)%PREDICATE_PAIR_HASH;
    hash2 = (((int)t1)/4)%PREDICATE_PAIR_HASH;

    p1 = pairs[hash1];
    while (p1) {
        if (p1->term==t2) goto cont2;
        p1 = p1->next;
    }
    return 0;
cont2:
    p2 = p1->matches[hash2];
    while (p2) {
        if (p2->e==t1) {
            return 1;
        }
        p2 = p2->next;
    }

    return 0;
}

struct pair_map {
    struct pair_map *next;
    struct _ex_intern *e1, *e2;
};

static struct pair_map *swappable_predicates(struct env *env, struct pair_map *mapped, struct _ex_intern *p1, struct _ex_intern *p2);

static struct pair_map *rec_check_swap(struct env *env, struct pair_map *mapped, struct _ex_intern *p1, struct _ex_intern *p2, char *block, int pos)
{
    int i;
    struct pair_map *res;

    if (pos==p1->u.appl.count) return mapped;

    for (i = 0; i < p1->u.appl.count; ++i) {
        if (block[i]) {
            block[i] = 0;
            res = swappable_predicates(env,mapped,p1->u.appl.args[pos],p2->u.appl.args[i]);
            if (res) {
                res = rec_check_swap(env,res,p1,p2,block,pos+1);
                if (res) return res;
            }
            block[i] = 1;
        }
    }

    return NULL;
}

static struct pair_map *swappable_predicates(struct env *env, struct pair_map *mapped, struct _ex_intern *p1, struct _ex_intern *p2)
{
    if (swappable_terms(p1,p2)) {
        struct pair_map *new_map;
        new_map = mapped;
        while (new_map) {
            if (p1==new_map->e1 && p2==new_map->e2) return mapped;
            if (p1==new_map->e1 || p2==new_map->e2) return NULL;
            new_map = new_map->next;
        }
        new_map = (struct pair_map *)_th_alloc(REWRITE_SPACE,sizeof(struct pair_map));
        new_map->next = mapped;
        new_map->e1 = p1;
        new_map->e2 = p2;
        return new_map;
    }

    if (p1->type==EXP_APPL && p2->type==EXP_APPL && p1->u.appl.functor==p2->u.appl.functor &&
        p1->u.appl.count==p2->u.appl.count) {
        int i;
        if (_th_is_ac_or_c(env,p1->u.appl.functor)) {
            char *block = (char *)ALLOCA(sizeof(char) * p1->u.appl.count);
            for (i = 0; i < p1->u.appl.count; ++i) {
                block[i] = 1;
            }
            //printf("AC check for %s\n", _th_print_exp(p1));
            //printf("    and %s\n", _th_print_exp(p2));
            mapped = rec_check_swap(env,mapped,p1,p2,block,0);
            //printf("res %d\n", mapped);
            return mapped;
        } else {
            //printf("non-AC check for %s\n", _th_print_exp(p1));
            //printf("    and %s\n", _th_print_exp(p2));
            for (i = 0; i < p1->u.appl.count; ++i) {
                if (!(mapped = swappable_predicates(env,mapped,p1->u.appl.args[i],p2->u.appl.args[i]))) return NULL;
            }
            return mapped;
        }
    }

    return NULL;
}

struct swap_groups {
    struct swap_groups *next;
    struct add_list *group;
};

static struct swap_groups *get_swap_groups(struct env *env, struct _ex_intern *e)
{
    struct add_list *predicates, *p;
    struct switch_list *list;
    struct swap_groups *groups = NULL, *g;

    //printf("Here0\n");
    //fflush(stdout);
    predicates = collect_predicates(env,e);
    //printf("Here1\n");
    //p = predicates;
    //while (p) {
    //    printf("    %s\n", _th_print_exp(p->e));
    //    p = p->next;
    //}
    //fflush(stdout);
    list = symmetric_vars(env,e);
    if (list==NULL) return NULL;
    //printf("Here2\n");
    //fflush(stdout);
    build_pair_info(list);
    //printf("Here3\n");
    //fflush(stdout);

    while (predicates) {
        //printf("Checking %s\n", _th_print_exp(predicates->e));
        g = groups;
        while (g) {
            //printf("Checking group\n");
            p = g->group;
            while (p) {
                //printf("Checking term %s\n", _th_print_exp(p->e));
                if (!swappable_predicates(env,NULL,predicates->e,p->e)) goto cont;
                p = p->next;
            }
            p = predicates->next;
            predicates->next = g->group;
            g->group = predicates;
            goto cont2;
cont:
            g = g->next;
        }
        p = predicates->next;
        g = (struct swap_groups *)_th_alloc(REWRITE_SPACE,sizeof(struct swap_groups));
        g->next = groups;
        groups = g;
        g->group = predicates;
        predicates->next = NULL;
cont2:
        predicates = p;
    }

    return groups;
}

struct _ex_intern *_th_augment_with_symmetries(struct env *env, struct _ex_intern *e)
{
    struct add_list *a, *terms = NULL, *t;
    struct swap_groups *groups, *mgroup;
    int count = 0, i, gcount;
    struct _ex_intern **args;

    _tree_print0("Symmetry analysis");
    _tree_indent();

    groups = get_swap_groups(env,e);

    if (groups==NULL) {
        _tree_print0("No symmetries");
        _tree_undent();
        return e;
    }

    _tree_print0("Groups");
    _tree_indent();
    mgroup = groups;
    while (mgroup) {
        _tree_print0("group");
        _tree_indent();
        a = mgroup->group;
        while (a) {
            _tree_print_exp("e",a->e);
            a = a->next;
        }
        _tree_undent();
        mgroup = mgroup->next;
    }
    _tree_undent();

    gcount = 0;
    while (groups) {
        a = groups->group;
        i = 0;
        while (a) {
            ++i;
            a = a->next;
        }
        if (i > gcount) {
            gcount = i;
            mgroup = groups;
        }
        groups = groups->next;
    }
    if (mgroup->group->next) {
        a = mgroup->group;
        while (a->next) {
            t = (struct add_list *)ALLOCA(sizeof(struct add_list));
            t->next = terms;
            terms = t;
            t->e = _ex_intern_appl2_env(env,INTERN_AND,a->e,_ex_intern_appl1_env(env,INTERN_NOT,a->next->e));
            ++count;
            a = a->next;
        }
    }

#ifndef FAST
    a = mgroup->group;
    _tree_print0("Symmetric group");
    _tree_indent();
    while (a) {
        _tree_print_exp("term", a->e);
        a = a->next;
    }
    _tree_undent();
#endif
    //printf("Group:\n");
    //while (a) {
    //    printf("    %s\n", _th_print_exp(a->e));
    //    a = a->next;
    //}

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (count + 1));
    i = 0;
    _tree_print0("Adding terms");
    _tree_indent();
    while (terms) {
        _tree_print_exp("term", terms->e);
        args[i++] = terms->e;
        terms = terms->next;
    }
    _tree_undent();
    args[i++] = e;

    _tree_undent();
    return _th_flatten_top(env,_ex_intern_appl_env(env,INTERN_OR,i,args));
}
