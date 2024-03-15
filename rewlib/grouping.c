/*
 * grouping.c
 *
 * Routines for discovering groupings.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"

static struct _ex_intern *trail = NULL;

struct signed_list {
    struct signed_list *next;
    struct _ex_intern *e;
    int source;
    int sign;
    int count;
    unsigned *fv;
};

static struct signed_list *terms = NULL;

static int collect = 0;

int _th_block_bigs = 0;

static int is_a_bool(struct env *env, struct _ex_intern *e)
{
    if (e->type==EXP_VAR) {
        return _th_get_var_type(env,e->u.var)==_ex_bool;
    } else if (e->type==EXP_APPL) {
        if (e->u.appl.functor==INTERN_AND || e->u.appl.functor==INTERN_OR ||
            e->u.appl.functor==INTERN_NOT ||
            e->u.appl.functor==INTERN_TRUE || e->u.appl.functor==INTERN_FALSE) {
            return 1;
        }
        if (e->u.appl.functor==INTERN_ITE) {
            return is_a_bool(env,e->u.appl.args[1]) || is_a_bool(env,e->u.appl.args[2]);
        }
        if (e->u.appl.functor==INTERN_EQUAL) {
            return is_a_bool(env,e->u.appl.args[1]) || is_a_bool(env,e->u.appl.args[0]);
        }
    }
    return 0;
}

static void collect_terms(struct env *env, struct _ex_intern *e, int sign)
{
    int i;
    struct signed_list *a;
    struct signed_list *prev = NULL;

    if (e->user2) {
        if (sign&((int)e->user1)) return;
        prev = terms;
        while (prev && prev->e != e) {
            prev = prev->next;
        }
        e->user1 = sign = 3;
    } else {
        e->user2 = trail;
        e->user1 = sign;
        trail = e;
    }

    //printf("Processing %s\n", _th_print_exp(e));
    //printf("    user2 %s\n", _th_print_exp(e->user2));

    ++collect;

    switch (e->type) {
        case EXP_VAR:
            return;
        case EXP_APPL:
            switch (e->u.appl.functor) {
                case INTERN_ITE:
                    collect_terms(env,e->u.appl.args[0],3);
                    collect_terms(env,e->u.appl.args[1],sign);
                    collect_terms(env,e->u.appl.args[2],sign);
                    return;
                case INTERN_NOT:
                    collect_terms(env,e->u.appl.args[0],2*(sign&1)+(sign&2)/2);
                    return;
                case INTERN_AND:
                case INTERN_OR:
                case INTERN_TRUE:
                case INTERN_FALSE:
                    for (i = 0; i < e->u.appl.count; ++i) {
                        collect_terms(env,e->u.appl.args[i],sign);
                    }
                    return;
                case INTERN_EQUAL:
                    if (is_a_bool(env,e->u.appl.args[0]) || is_a_bool(env,e->u.appl.args[1])) {
                        //printf("Skipping collection of %s\n", _th_print_exp(e));
                        collect_terms(env,e->u.appl.args[0],3);
                        collect_terms(env,e->u.appl.args[1],3);
                        return;
                    }
                    //printf("Collecting %s\n", _th_print_exp(e));
            }
            break;
    }

    if (prev) {
        prev->sign = sign;
    } else {
        a = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
        a->next = terms;
        a->sign = sign;
        a->source = 0;
        a->count = 0;
        a->fv = NULL;
        terms = a;
        a->e = e;
    }
}

struct group_list {
    struct group_list *next;
    struct _ex_intern *e;
    struct signed_list *group;
    int count;
    unsigned *fv;
    int can_subout;
    struct group_list *conflicts;
    int edges_added;
    int conflict_count;
    int cycle_count;
    int is_trivial;
};

static int subsumed(struct signed_list *a, struct signed_list *c)
{
    struct signed_list *c1;

    while (a) {
        c1 = c;
        while (c1) {
            if (c1->e==a->e) goto cont;
            c1 = c1->next;
        }
        return 0;
cont:
        a = a->next;
    }

    return 1;
}

static int check_subsumed(struct signed_list *a, struct group_list *g)
{
    if (g==NULL) return 0;

    if (subsumed(g->group,a)) return 1;

    return check_subsumed(a,g->next);
}

static int member(struct _ex_intern *e, struct add_list *l)
{
    while (l) {
        if (e==l->e) return 1;
        l = l->next;
    }

    return 0;
}

static struct group_list *collect_conflicts(struct env *env, struct signed_list *group, struct signed_list *tail, struct group_list *conflicts)
{
    struct signed_list *a;
    struct group_list *g;

    if (group==NULL) return conflicts;

    conflicts = collect_conflicts(env, group->next, tail, conflicts);

    _th_derive_push(env);
    
    a = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
    a->next = tail;
    a->e = group->e;
    a->sign = group->sign;
    a->source = 0;
    a->count = 0;
    a->fv = NULL;
    
    if (_th_assert_predicate(env,a->e)) {
        if (!check_subsumed(a,conflicts)) {
            g = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
            g->next = conflicts;
            g->group = a;
            conflicts = g;
        }
    } else {
        conflicts = collect_conflicts(env, group->next, a, conflicts);
    }
    
    _th_derive_pop(env);
    
    _th_derive_push(env);
    
    a = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
    a->next = tail;
    a->e = _ex_intern_appl1_env(env,INTERN_NOT,group->e);
    a->sign = group->sign;
    a->source = 0;
    a->count = 0;
    a->fv = NULL;
    
    if (_th_assert_predicate(env,a->e)) {
        if (!check_subsumed(a,conflicts)) {
            g = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
            g->next = conflicts;
            g->group = a;
            conflicts = g;
        }
    } else {
        conflicts = collect_conflicts(env, group->next, a, conflicts);
    }
    
    _th_derive_pop(env);

    return conflicts;
}

static struct group_list *group_by_vars(struct env *env, struct signed_list *list)
{
    struct group_list *group, *g;
    struct signed_list *a;
    unsigned *fv, *fvars;
    int count, c, i;
    struct signed_list *ll;

    group = NULL;

    while (list) {
        fv = _th_get_free_vars(list->e,&count);
        fvars = (unsigned *)ALLOCA(sizeof(unsigned) * count);
        for (c = 0; c < count; ++c) {
            fvars[c] = fv[c];
        }
        g = group;
        while (g) {
            fv = _th_get_free_vars(g->group->e,&c);
            if (c == count) {
                while (c) {
                    if (!_th_is_free_in(g->group->e,fvars[--c])) goto con;
                }
                goto cont;
            }
con:
            g = g->next;
        }
        g = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
        g->next = group;
        g->group = NULL;
        g->count = count;
        g->fv = (unsigned *)_th_alloc(REWRITE_SPACE,sizeof(unsigned) * count);
        for (i = 0; i < count; ++i) {
            g->fv[i] = fvars[i];
        }
        group = g;
cont:
        ll = g->group;
        while (ll) {
            if (ll->e==list->e) {
                fprintf(stderr, "Duplicate symbol %s\n", _th_print_exp(list->e));
                exit(1);
            }
            ll = ll->next;
        }
        a = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
        a->next = g->group;
        g->group = a;
        a->e = list->e;
        a->sign = list->sign;
        a->source = 1;
        a->count = 0;
        a->fv = NULL;
        list = list->next;
    }

    return group;
}

static int is_assigned(struct _ex_intern *e)
{
    while (e->find && e->find != e) {
        e = e->find;
    }
    return e==_ex_true || e==_ex_false;
}

static struct _ex_intern *get_find(struct _ex_intern *e)
{
    while (e->find && e->find != e) {
        e = e->find;
    }
    return e;
}

static int limit_counter;

static struct group_list *check_equality_conflicts(struct env *env, struct learn_info *info, struct signed_list *group, struct signed_list *tail, struct group_list *conflicts)
{
    while (group && (group->e->type!=EXP_APPL || group->e->u.appl.functor != INTERN_EQUAL)) {
           group = group->next;
    }
    if (group==NULL) {
        --limit_counter;
        return conflicts;
    }

    if (get_find(group->e) != _ex_true) {
        _th_derive_push(env);
        
        if (_th_assert_predicate(env,group->e)) {
            struct signed_list *c = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
            struct group_list *n = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
            c->next = tail;
            c->sign = group->sign;
            c->source = group->source;
            c->e = group->e;
            c->count = 0;
            c->fv = NULL;
            n->next = conflicts;
            conflicts = n;
            n->group = c;
            _th_add_tuple_from_list(env,info,(struct add_list *)c);
            if (--limit_counter < 0) {
                _th_derive_pop(env);
                return conflicts;
            }
        } else {
            struct signed_list *t = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
            struct add_list *lu, *nlu;
            struct _ex_intern *e;
            t->count = 0;
            t->fv = NULL;
            t->next = tail;
            t->e = group->e;
            _th_create_add_assignment(env,info,group->e,0);
            lu = NULL;
            while (e = _th_learned_non_domain_unate_case(env,info,NULL)) {
                nlu = (struct add_list *)ALLOCA(sizeof(struct add_list));
                nlu->next = lu;
                nlu->e = e;
                lu = nlu;
                _th_assert_predicate(env,nlu->e);
                _th_create_add_assignment(env,info,nlu->e,0);
            }
            conflicts = check_equality_conflicts(env,info,group->next,t,conflicts);
            if (limit_counter < 0) {
                _th_derive_pop(env);
                return NULL;
            }
            while (lu) {
                _th_delete_assignment(env,info,lu->e);
                lu = lu->next;
            }
            _th_delete_assignment(env,info,group->e);
        }
        
        _th_derive_pop(env);
    }

    return check_equality_conflicts(env,info,group->next,tail,conflicts);
}

static struct group_list *check_all_conflicts(struct env *env, struct learn_info *info, struct signed_list *group, struct signed_list *tail, struct group_list *conflicts)
{
    if (group==NULL) {
        --limit_counter;
        return conflicts;
    }

    _tree_print_exp("Check all conflicts", group->e);
    _tree_indent();

    if (get_find(group->e) != _ex_true) {

        _th_derive_push(env);

        if (_th_assert_predicate(env,group->e)) {
            struct signed_list *c = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
            struct group_list *n = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
            _tree_print0("Assert conflict");
            c->next = tail;
            c->e = group->e;
            c->sign = group->sign;
            c->source = group->source;
            c->count = 0;
            c->fv = NULL;
            n->next = conflicts;
            conflicts = n;
            n->group = c;
            _th_add_tuple_from_list(env,info,(struct add_list *)c);
            if (--limit_counter < 0) {
                _th_derive_pop(env);
                _tree_undent();
                return conflicts;
            }
        } else {
            struct signed_list *t = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
            struct add_list *lu, *nlu;
            struct _ex_intern *e;
            _tree_print0("Assert check");
            t->count = 0;
            t->fv = NULL;
            t->next = tail;
            t->e = group->e;
            t->source = group->source;
            _th_create_add_assignment(env,info,group->e,0);
            lu = NULL;
            while (e = _th_learned_non_domain_unate_case(env,info,NULL)) {
                nlu = (struct add_list *)ALLOCA(sizeof(struct add_list));
                nlu->next = lu;
                nlu->e = e;
                lu = nlu;
                _th_assert_predicate(env,nlu->e);
                _th_create_add_assignment(env,info,nlu->e,0);
            }
            conflicts = check_all_conflicts(env,info,group->next,t,conflicts);
            if (limit_counter < 0) {
                _th_derive_pop(env);
                _tree_undent();
                return NULL;
            }
            while (lu) {
                _th_delete_assignment(env,info,lu->e);
                lu = lu->next;
            }
            _th_delete_assignment(env,info,group->e);
        }
        
        _th_derive_pop(env);
    }

    if (get_find(group->e) != _ex_false) {
        
        _th_derive_push(env);
        
        if (_th_deny_predicate(env,group->e)) {
            struct signed_list *c = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
            struct group_list *n = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
            _tree_print0("Deny conflict");
            c->next = tail;
            c->e = _ex_intern_appl1_env(env,INTERN_NOT,group->e);
            c->sign = group->sign;
            c->source = group->source;
            c->count = 0;
            c->fv = NULL;
            n->next = conflicts;
            conflicts = n;
            n->group = c;
            _th_add_tuple_from_list(env,info,(struct add_list *)c);
            if (--limit_counter < 0) {
                _th_derive_pop(env);
                _tree_undent();
                return conflicts;
            }
        } else {
            struct signed_list *t = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
            struct add_list *lu, *nlu;
            struct _ex_intern *e;
            struct _ex_intern *ne = _ex_intern_appl1_env(env,INTERN_NOT,group->e);
            _tree_print0("Deny check");
            t->next = tail;
            t->e = ne;
            t->source = 0;
            t->sign = 0;
            t->count = 0;
            t->fv = NULL;
            _th_create_add_assignment(env,info,ne,0);
            lu = NULL;
            while (e = _th_learned_non_domain_unate_case(env,info,NULL)) {
                nlu = (struct add_list *)ALLOCA(sizeof(struct add_list));
                nlu->next = lu;
                nlu->e = e;
                lu = nlu;
                _th_assert_predicate(env,nlu->e);
                _th_create_add_assignment(env,info,nlu->e,0);
            }
            conflicts = check_all_conflicts(env,info,group->next,t,conflicts);
            if (limit_counter < 0) {
                _th_derive_pop(env);
                _tree_undent();
                return NULL;
            }
            while (lu) {
                _th_delete_assignment(env,info,lu->e);
                lu = lu->next;
            }
            _th_delete_assignment(env,info,ne);
        }
        
        _th_derive_pop(env);
    }
        
    _tree_print0("Ignore case");
    conflicts = check_all_conflicts(env,info,group->next,tail,conflicts);
    _tree_undent();

    return conflicts;
}

//#define CHECK_TUPLE

#ifdef CHECK_TUPLE
static void check_tuple(struct env *env, struct signed_list *l, char *place)
{
    struct signed_list *l1 = l;

    if (l->next==NULL) {
        fprintf(stderr, "One term tuple (%s) %s\n", place, _th_print_exp(l->e));
        exit(1);
    }
    //if (place[0]=='e' && place[1]=='q' && place[2]==' ') {
        printf("place %s\n", place);
        while (l) {
            printf("    %s\n", _th_print_exp(l->e));
            l = l->next;
        }
        _th_derive_push(env);
        while (l1) {
            if (_th_assert_predicate(env,l1->e)) goto cont;
            l1 = l1->next;
        }
        printf("Illegal tuple\n");
cont:
        _th_derive_pop(env);
    //}
}
#else
#define check_tuple(a,b,c)
#endif

#ifdef XX
static struct group_list *get_diff_common_var_conflicts(struct env *env, struct signed_list *group, struct group_list *conflicts)
{
    struct signed_list *g2, *g3;
    struct _ex_intern *t1, *t2, *t3;
    struct signed_list *c1, *c2, *c3;
    struct group_list *c;
    char *mark1, *mark2, *mark3;

#ifndef FAST
    int cc = 0;
    g2 = group;
    while (g2) {
        ++cc;
        g2 = g2->next;
    }
    _tree_print1("Group conflicts %d", cc);
    _tree_indent();
    _tree_print0("group");
    g2 = group;
    _tree_indent();
    while (g2) {
        _tree_print3("g %s %d %d", _th_print_exp(g2->e), g2->sign, g2->source);
        g2 = g2->next;
    }
    _tree_undent();
#endif

    while (group) {
        t1 = group->e;
        mark1 = _th_alloc_mark(ENVIRONMENT_SPACE);
        _th_derive_push(env);
        _th_assert_predicate(env,t1);
        g2 = group->next;
        while (g2) {
            t2 = g2->e;
            mark2 = _th_alloc_mark(ENVIRONMENT_SPACE);
            _th_derive_push(env);
            if (_th_assert_predicate(env,t2)) {
                c1 = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                c2 = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                c1->next = c2;
                c2->next = NULL;
                c1->e = t1;
                c1->sign = 0;
                c1->source = 0;
                c2->e = t2;
                c2->sign = 0;
                c2->source = 0;
                c1->count = c2->count = 0;
                c1->fv = c2->fv = NULL;
                c = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
                c->next = conflicts;
                c->group = c1;
                check_tuple(env,c1,"common 1");
                conflicts = c;
#ifndef FAST
                _tree_print_exp("Adding conflict", t1);
                _tree_print_exp("and", t2);
#endif
            }
            _th_derive_pop(env);
            _th_alloc_release(ENVIRONMENT_SPACE,mark2);
            t2 = _ex_intern_appl1_env(env,INTERN_NOT,g2->e);
            _th_derive_push(env);
            if (_th_assert_predicate(env,t2)) {
                c1 = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                c2 = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                c1->next = c2;
                c2->next = NULL;
                c1->e = t1;
                c1->sign = 0;
                c1->source = 0;
                c2->e = t2;
                c2->sign = 0;
                c2->source = 0;
                c1->count = c2->count = 0;
                c1->fv = c2->fv = NULL;
                c = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
                c->next = conflicts;
                c->group = c1;
                check_tuple(env,c1,"common 2");
                conflicts = c;
#ifndef FAST
                _tree_print_exp("Adding conflict", t1);
                _tree_print_exp("and", t2);
#endif
            }
            _th_derive_pop(env);
            _th_alloc_release(ENVIRONMENT_SPACE,mark2);
            g2 =g2->next;
        }
        _th_derive_pop(env);
        _th_alloc_release(ENVIRONMENT_SPACE,mark1);
        t1 = _ex_intern_appl1_env(env,INTERN_NOT,group->e);
        _th_derive_push(env);
        _th_assert_predicate(env,t1);
        g2 = group->next;
        while (g2) {
            t2 = g2->e;
     		mark2 = _th_alloc_mark(ENVIRONMENT_SPACE);
            _th_derive_push(env);
            if (_th_assert_predicate(env,t2)) {
                c1 = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                c2 = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                c1->next = c2;
                c2->next = NULL;
                c1->e = t1;
                c1->sign = 0;
                c1->source = 0;
                c2->e = t2;
                c2->sign = 0;
                c2->source = 0;
                c1->count = c2->count = 0;
                c1->fv = c2->fv = NULL;
                c = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
                c->next = conflicts;
                c->group = c1;
                check_tuple(env,c1,"common 3");
                conflicts = c;
#ifndef FAST
                _tree_print_exp("Adding conflict", t1);
                _tree_print_exp("and", t2);
#endif
            }
            _th_derive_pop(env);
            _th_alloc_release(ENVIRONMENT_SPACE,mark2);
            t2 = _ex_intern_appl1_env(env,INTERN_NOT,g2->e);
            _th_derive_push(env);
            if (_th_assert_predicate(env,t2)) {
                c1 = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                c2 = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                c1->next = c2;
                c2->next = NULL;
                c1->e = t1;
                c1->sign = 0;
                c1->source = 0;
                c2->e = t2;
                c2->sign = 0;
                c2->source = 0;
                c1->count = c2->count = 0;
                c1->fv = c2->fv = NULL;
                c = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
                c->next = conflicts;
                check_tuple(env,c1,"common 4");
                c->group = c1;
                conflicts = c;
#ifndef FAST
                _tree_print_exp("Adding conflict", t1);
                _tree_print_exp("and", t2);
#endif
            } else {
                g3 = g2->next;
                while (g3) {
                    t3 = _ex_intern_appl1_env(env,INTERN_NOT,g3->e);
             		mark3 = _th_alloc_mark(ENVIRONMENT_SPACE);
                    _th_derive_push(env);
                    if (_th_assert_predicate(env,t3)) {
                        c1 = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                        c2 = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                        c3 = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                        c1->next = c2;
                        c2->next = c3;
                        c3->next = NULL;
                        c1->e = t1;
                        c1->sign = 0;
                        c1->source = 0;
                        c2->e = t2;
                        c2->sign = 0;
                        c2->source = 0;
                        c3->e = t3;
                        c3->sign = 0;
                        c3->source = 0;
                        c1->count = c2->count = c3->count = 0;
                        c1->fv = c2->fv = c3->fv = NULL;
                        c = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                        c->next = conflicts;
                        c->group = c1;
                        c->count = 0;
                        c->fv = NULL;
                        check_tuple(env,c1,"common 5");
                        conflicts = c;
#ifndef FAST
                        _tree_print_exp("Adding conflict", t1);
                        _tree_print_exp("and", t2);
#endif
                    }
                    _th_derive_pop(env);
                    _th_alloc_release(ENVIRONMENT_SPACE,mark3);
                    g3 = g3->next;
                }
            }
            _th_derive_pop(env);
            _th_alloc_release(ENVIRONMENT_SPACE,mark2);
            g2 =g2->next;
        }
        group = group->next;
        _th_derive_pop(env);
        _th_alloc_release(ENVIRONMENT_SPACE,mark1);
    }

    _tree_undent();

    return conflicts;
}
#endif

static int is_contradiction(struct env *env, struct _ex_intern *left1, struct _ex_intern *right1, struct _ex_intern *diff1, int is_equal_term1,
                                             struct _ex_intern *left2, struct _ex_intern *right2, struct _ex_intern *diff2, int is_equal_term2)
{
    if (left1==right2 && right1==left2 && !is_equal_term1 && !is_equal_term2) {
        struct _ex_intern *sum = _th_add_rationals(diff1,diff2);
        if (_th_big_is_negative(sum->u.rational.numerator)) return 7;
        //if (sum->u.rational.numerator[0]==1 && sum->u.rational.numerator[1]==0) return 0;
        return 1;
    }
    if (left1==left2 && right1==right2 && !is_equal_term1 && !is_equal_term2) {
        struct _ex_intern *sum = _th_subtract_rationals(diff1,diff2);
        if (_th_big_is_negative(sum->u.rational.numerator)) {
            return 5;
        } else {
            return 3;
        }
    }
    if (left1==right1 && left2==right2 && !is_equal_term1 && is_equal_term2) {
        struct _ex_intern *sum = _th_subtract_rationals(diff1,diff2);
        if (_th_big_is_negative(sum->u.rational.numerator)) {
            return 3;
        } else {
            return 1;
        }
    }
    if (left1==right2 && left2==right1 && !is_equal_term1 && is_equal_term2) {
        struct _ex_intern *sum = _th_add_rationals(diff1,diff2);
        if (_th_big_is_negative(sum->u.rational.numerator)) {
            return 3;
        } else {
            return 1;
        }
    }
    if (left1==left2 && right1==right2 && is_equal_term1 && !is_equal_term2) {
        struct _ex_intern *sum = _th_subtract_rationals(diff2,diff1);
        if (_th_big_is_negative(sum->u.rational.numerator)) {
            return 5;
        } else {
            return 1;
        }
    }
    if (left1==right2 && left2==right1 && is_equal_term1 && !is_equal_term2) {
        struct _ex_intern *sum = _th_add_rationals(diff2,diff1);
        if (_th_big_is_negative(sum->u.rational.numerator)) {
            return 5;
        } else {
            return 1;
        }
    }
    if (is_equal_term1 && is_equal_term2) {
        return 1;
    }
    return 0;
}

static int is_triple_prefix(struct env *env, struct _ex_intern *left1, struct _ex_intern *right1, struct _ex_intern *diff1, int is_equal_term1,
                                             struct _ex_intern *left2, struct _ex_intern *right2, struct _ex_intern *diff2, int is_equal_term2)
{
    struct _ex_intern *sum;

    if (is_equal_term1) {
        if (is_equal_term2) {
            return 0;
        } else {
            if (left1==left2) {
                return diff1==diff2;
            } else {
                sum = _th_add_rationals(diff1,diff2);
                return sum->u.rational.numerator[0]==1 && sum->u.rational.numerator[1]==0;
            }
        }
    } else {
        if (is_equal_term2) {
            if (left1==left2) {
                return diff1==diff2;
            } else {
                sum = _th_add_rationals(diff1,diff2);
                return sum->u.rational.numerator[0]==1 && sum->u.rational.numerator[1]==0;
            }
        } else {
            if (left1==left2) return 0;
            sum = _th_add_rationals(diff1,diff2);
            if (sum->u.rational.numerator[0]==1 && sum->u.rational.numerator[1]==0) return 1;
            return 0;
        }
    }
}

static int is_triple(struct env *env, struct _ex_intern *left1, struct _ex_intern *right1, struct _ex_intern *diff1, int is_equal_term1,
                                      struct _ex_intern *left2, struct _ex_intern *right2, struct _ex_intern *diff2, int is_equal_term2,
                                      struct _ex_intern *left3, struct _ex_intern *right3, struct _ex_intern *diff3, int is_equal_term3)
{
    struct _ex_intern *lefte, *righte, *diffe;
    struct _ex_intern *sum;

    if (is_equal_term1) {
        lefte = left1;
        righte = right1;
        diffe = diff1;
        left1 = left3;
        right1 = right3;
        diff1 = diff3;
        is_equal_term1 = is_equal_term3;
    } else if (is_equal_term2) {
        lefte = left2;
        righte = right2;
        diffe = diff2;
        left2 = left3;
        right2 = right3;
        diff2 = diff3;
        is_equal_term2 = is_equal_term3;
    } else if (is_equal_term3) {
        lefte = left3;
        righte = right3;
        diffe = diff3;
    } else {
        return 0;
    }
    if (is_equal_term1 || is_equal_term2) return 0;
    if (left1==left2) return 0;
    sum = _th_add_rationals(diff1,diff2);
    if (sum->u.rational.numerator[0]!=1 || sum->u.rational.numerator[1]!=0) return 0;
    if (left1==lefte) {
        return diff1==diffe;
    } else {
        return diff2==diffe;
    }
}

static struct group_list *get_diff_common_var_conflicts(struct env *env, struct signed_list *group, struct group_list *conflicts)
{
    struct signed_list *g2, *g3;
    struct _ex_intern *t1, *t2, *t3;
    struct signed_list *c1, *c2, *c3;
    struct group_list *c;
    int conflict;

#ifndef FAST
    int cc = 0;
    g2 = group;
    while (g2) {
        ++cc;
        g2 = g2->next;
    }
    _tree_print1("Group conflicts %d", cc);
    _tree_indent();
    _tree_print0("group");
    g2 = group;
    _tree_indent();
    while (g2) {
        _tree_print3("g %s %d %d", _th_print_exp(g2->e), g2->sign, g2->source);
        g2 = g2->next;
    }
    _tree_undent();
#endif

    while (group) {
        int delta1, is_equal_term1;
        struct _ex_intern *left1, *right1, *diff1;
        t1 = group->e;
        if (!_th_extract_relationship(env,t1)) {
            fprintf(stderr, "Error extracting relationship from %s\n", _th_print_exp(t1));
            exit(1);
        }
        left1 = _th_left;
        right1 = _th_right;
        delta1 = _th_delta;
        is_equal_term1 = _th_is_equal_term;
        diff1 = _th_diff;
        g2 = group->next;
		_tree_print_exp("Testing", t1);
		_tree_indent();
        while (g2) {
            int delta2, is_equal_term2;
            struct _ex_intern *left2, *right2, *diff2;
            t2 = g2->e;
            if (!_th_extract_relationship(env,t2)) {
                fprintf(stderr, "Error extracting relationship from %s\n", _th_print_exp(t2));
                exit(1);
            }
            left2 = _th_left;
            right2 = _th_right;
            delta2 = _th_delta;
            is_equal_term2 = _th_is_equal_term;
            diff2 = _th_diff;
			_tree_print_exp("Testing contradiction", t2);
			_tree_print_exp("left1", left1);
			_tree_print_exp("right1", right1);
			_tree_print_exp("left2", left2);
			_tree_print_exp("right2", right2);
			_tree_print_exp("diff1", diff1);
			_tree_print_exp("diff2", diff2);
            _tree_print2("is_equal_term1, is_equal_term2 %d %d", is_equal_term1, is_equal_term2);
            if (conflict = is_contradiction(env,left1,right1,diff1,is_equal_term1,left2,right2,diff2,is_equal_term2)) {
				_tree_indent();
				_tree_print0("yes");
				_tree_undent();
                c1 = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                c2 = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                c1->next = c2;
                c2->next = NULL;
                if (conflict & 2) {
                    c1->e = _ex_intern_appl1_env(env,INTERN_NOT,t1);
                } else {
                    c1->e = t1;
                }
                c1->sign = 0;
                c1->source = 0;
                if (conflict & 4) {
                    c2->e = _ex_intern_appl1_env(env,INTERN_NOT,t2);
                } else {
                    c2->e = t2;
                }
                c2->sign = 0;
                c2->source = 0;
                c1->count = c2->count = 0;
                c1->fv = c2->fv = NULL;
                c = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
                c->next = conflicts;
                check_tuple(env,c1,"common 4");
                c->group = c1;
                conflicts = c;
#ifndef FAST
                _tree_print_exp("Adding conflict", t1);
                _tree_print_exp("and", t2);
#endif
            }
			_tree_print1("Conflict %d", conflict);
            if (is_triple_prefix(env,left1,right1,diff1,is_equal_term1,left2,right2,diff2,is_equal_term2)) {
                g3 = g2->next;
                while (g3) {
                    t3 = _ex_intern_appl1_env(env,INTERN_NOT,g3->e);
                    if (!_th_extract_relationship(env,t3)) {
                        fprintf(stderr, "Error extracting relationship from %s\n", _th_print_exp(t3));
                        exit(1);
                    }
                    if (is_triple(env,left1,right1,diff1,is_equal_term1,
                                      left2,right2,diff2,is_equal_term2,
                                      _th_left,_th_right,_th_diff,_th_is_equal_term)) {
                        c1 = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                        c2 = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                        c3 = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                        c1->next = c2;
                        c2->next = c3;
                        c3->next = NULL;
                        c1->e = t1;
                        c1->sign = 0;
                        c1->source = 0;
                        c2->e = t2;
                        c2->sign = 0;
                        c2->source = 0;
                        c3->e = t3;
                        c3->sign = 0;
                        c3->source = 0;
                        c1->count = c2->count = c3->count = 0;
                        c1->fv = c2->fv = c3->fv = NULL;
                        c = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
                        c->next = conflicts;
                        c->group = c1;
                        check_tuple(env,c1,"common 5");
                        conflicts = c;
#ifndef FAST
                        _tree_print_exp("Adding conflict", t1);
                        _tree_print_exp("and", t2);
#endif
                    }
                    g3 = g3->next;
                }
            }
            g2 =g2->next;
        }
		_tree_undent();
        group = group->next;
    }

    _tree_undent();

    return conflicts;
}

static struct group_list *search_common_var_conflicts(struct env *env, struct learn_info *info, struct signed_list *group, struct group_list *conflicts)
{
    
#ifndef FAST
    struct signed_list *l;
    _tree_print0("Group conflicts");
    _tree_indent();
    _tree_print0("group");
    l = group;
    _tree_indent();
    while (l) {
        _tree_print3("g %s %d %d", _th_print_exp(l->e), l->sign, l->source);
        l = l->next;
    }
    _tree_undent();
#endif

    _tree_print0("Equality conflicts");
    _tree_indent();
    conflicts = check_equality_conflicts(env, info, group, NULL, conflicts);
    _tree_undent();
    _tree_print0("All conflicts");
    _tree_indent();
    conflicts = check_all_conflicts(env, info, group, NULL, conflicts);
    _tree_undent();

#ifndef FAST
    if (limit_counter >= 0) {
        struct group_list *c = conflicts;
        _tree_print0("Conflicts");
        _tree_indent();
        while (c) {
            _tree_print0("conflict");
            _tree_indent();
            l = c->group;
            while (l != NULL) {
                _tree_print_exp("c", l->e);
                l = l->next;
            }
            _tree_undent();
            c = c->next;
        }
        _tree_undent();
    }
#endif

    _tree_undent();

    return conflicts;
}

static struct group_list *search_conflicts(struct env *env, struct add_list *group, struct add_list *checked, struct add_list *tail, struct group_list *conflicts)
{
    struct _ex_intern *next_term = NULL;
    struct add_list *search = group;
    int fvc = 100000;

    while (search) {
        if (!member(search->e,checked)) {
            int c;
            _th_get_free_vars(search->e,&c);
            if (c > fvc) {
                next_term = search->e;
                fvc = c;
            }
        }
        search = search->next;
    }

    if (!next_term) return conflicts;
}

//unsigned largest_var_usage(struct signed_list *list)
//{
//    struct signed_list *l;
//}

struct node_list {
    struct node_list *next;
    unsigned var;
    struct signed_list *edge;
};

struct route_list {
    struct route_list *next;
    struct node_list *path;
};

struct travel_list {
    struct travel_list *next;
    unsigned source;
    unsigned dest;
    struct route_list *paths;
};

static int node_member(unsigned v, struct node_list *l)
{
    while (l) {
        if (l->var==v) return 1;
        l = l->next;
    }

    return 0;
}

struct cycles_list {
    struct cycles_list *next;
    struct cycles *cycle;
};

struct edge_node {
    struct cycles_list *cycles;
    unsigned v1, v2;
    struct signed_list *terms;
    int edge_in_tree;
};

struct edge_list {
    struct edge_list *next;
    unsigned var;
    struct edge_node *node;
};

struct cycles {
    struct cycles *next;
    int number;
    struct edge_list *edges;
    struct node_list *path;
    struct cycles *parent;
    struct edge_list *parent_edge;
    struct cycles_list *children;
    int processed;
};

struct range_info {
    struct range_info *next;
    unsigned var;
    struct _ex_intern *range, *low, *high;
};

static int has_chord(unsigned var, struct node_list *path, struct group_list *all_edges)
{
    unsigned *fv;
    int count;

    while (path) {
        struct group_list *edge = all_edges;
        while (edge) {
            unsigned v1, v2;
            fv = _th_get_free_vars(edge->group->e,&count);
            v1 = fv[0];
            if (count > 1) {
                v2 = fv[1];
            } else {
                v2 = 0;
            }
            if (v1==var && v2 == path->var) return 1;
            if (v2==var && v1 == path->var) return 1;
            edge = edge->next;
        }
        path = path->next;
    }
    return 0;
}

static int has_tail_chord(unsigned var, struct node_list *path, struct group_list *all_edges)
{
    unsigned *fv;
    int count;

    while (path && path->next) {
        struct group_list *edge = all_edges;
        while (edge) {
            unsigned v1, v2;
            fv = _th_get_free_vars(edge->group->e,&count);
            v1 = fv[0];
            if (count > 1) {
                v2 = fv[1];
            } else {
                v2 = 0;
            }
            if (v1==var && v2 == path->var) return 1;
            if (v2==var && v1 == path->var) return 1;
            edge = edge->next;
        }
        path = path->next;
    }
    return 0;
}

static struct travel_list *add_cyclic_paths(unsigned v1, struct signed_list *edge, struct travel_list *list, struct route_list *paths, struct group_list *all_edges)
{
    struct travel_list *l = list;
    struct route_list *npaths, *n;
    struct node_list *node;

    _tree_print1("Add cycle paths %s", _th_intern_decode(v1));

    while (l) {
        if (l->source==l->dest && l->dest==v1) {
            goto cont;
        }
        l = l->next;
    }
    l = (struct travel_list *)_th_alloc(REWRITE_SPACE,sizeof(struct travel_list));
    l->next = list;
    list = l;
    l->paths = NULL;
    l->source = l->dest = v1;

cont:
    npaths = l->paths;
    while (paths) {
        //if (!node_member(v,paths->path)) {
#ifndef FAST
            node = paths->path;
            _tree_print0("Path");
            _tree_indent();
            while (node) {
                _tree_print1("Node %s", _th_intern_decode(node->var));
                node = node->next;
            }
            _tree_undent();
#endif
            n = (struct route_list *)_th_alloc(REWRITE_SPACE,sizeof(struct route_list));
            n->next = npaths;
            npaths = n;
            n->path = node = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
            node->next = paths->path;
            node->edge = edge;
            node->var = v1;
        //}
        paths = paths->next;
    }

    l->paths = npaths;

    _tree_print1("paths %x", l->paths);
    return list;
}

static struct travel_list *add_source_paths(unsigned v1, unsigned v2, struct signed_list *edge, struct travel_list *list, struct route_list *paths, struct group_list *all_edges)
{
    struct travel_list *l = list;
    struct route_list *npaths, *n;
    struct node_list *node;

    _tree_print4("Add source paths %s %s %s %s", _th_intern_decode(v1), _th_intern_decode(v2), _th_intern_decode(list->source), _th_intern_decode(list->dest));
    _tree_indent();

    while (l) {
        if (l->source==v1 && l->dest==v2) {
            goto cont;
        }
        l = l->next;
    }
    l = (struct travel_list *)_th_alloc(REWRITE_SPACE,sizeof(struct travel_list));
    l->next = list;
    list = l;
    l->paths = NULL;
    l->source = v1;
    l->dest = v2;

cont:
    npaths = l->paths;
    while (paths) {
        if (!node_member(v1,paths->path) && !has_chord(v1,paths->path->next,all_edges)) {
#ifndef FAST
            node = paths->path;
            _tree_print0("Path");
            _tree_indent();
            while (node) {
                _tree_print1("Node %s", _th_intern_decode(node->var));
                node = node->next;
            }
            _tree_undent();
#endif
            n = (struct route_list *)_th_alloc(REWRITE_SPACE,sizeof(struct route_list));
            n->next = npaths;
            npaths = n;
            n->path = node = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
            node->next = paths->path;
            node->edge = edge;
            node->var = v1;
        }
        paths = paths->next;
    }

    l->paths = npaths;

    _tree_undent();
    _tree_print1("paths %x", l->paths);
    return list;
}

static struct travel_list *add_dest_paths(unsigned v1, unsigned v2, unsigned old_v2, struct signed_list *edge, struct travel_list *list, struct route_list *paths, struct group_list *all_edges)
{
    struct travel_list *l = list;
    struct route_list *npaths, *n;
    struct node_list *node, *nnode, *pnode;

    _tree_print4("Add dest paths %s %s %s %s", _th_intern_decode(v1), _th_intern_decode(v2), _th_intern_decode(list->source), _th_intern_decode(list->dest));

    while (l) {
        if (l->source==v1 && l->dest==v2) {
            goto cont;
        }
        l = l->next;
    }
    l = (struct travel_list *)_th_alloc(REWRITE_SPACE,sizeof(struct travel_list));
    l->next = list;
    list = l;
    l->paths = NULL;
    l->source = v1;
    l->dest = v2;

cont:
    npaths = l->paths;
    while (paths) {
#ifndef FAST
        node = paths->path;
        _tree_print0("Path");
        _tree_indent();
        while (node) {
            _tree_print1("Node %s", _th_intern_decode(node->var));
            node = node->next;
        }
        _tree_undent();
#endif
        if (!node_member(old_v2,paths->path) && !has_tail_chord(old_v2,paths->path,all_edges)) {
            _tree_print0("Adding");
            n = (struct route_list *)_th_alloc(REWRITE_SPACE,sizeof(struct route_list));
            n->next = npaths;
            npaths = n;
            node = paths->path;
            pnode = NULL;
            while (node) {
                nnode = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
                if (pnode) {
                    pnode->next = nnode;
                } else {
                    n->path = nnode;
                }
                nnode->var = node->var;
                nnode->edge = node->edge;
                pnode = nnode;
                node = node->next;
            }
            pnode->next = node = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
            node->next = NULL;
            node->edge = edge;
            node->var = old_v2;
        }
        paths = paths->next;
    }

    l->paths = npaths;

    _tree_print1("paths %x", l->paths);
    return list;
}

static struct travel_list *add_travel_edge(struct travel_list *list, struct signed_list *edge, struct group_list *all_edges)
{
    unsigned *fv, v1, v2;
    int count;
    struct travel_list *l;
    struct route_list *p;
    struct node_list *n;

    fv = _th_get_free_vars(edge->e,&count);
    v1 = fv[0];
    if (count > 1) {
        v2 = fv[1];
    } else {
        v2 = 0;
    }

    _tree_print2("Add travel edge %s %s", _th_intern_decode(v1), _th_intern_decode(v2));
    _tree_indent();

    l = list;
    while (l) {
        _tree_print2("Processing entry %s %s", _th_intern_decode(l->source), _th_intern_decode(l->dest));
        if (l->source==v1 && l->dest==v2) {
            list = add_cyclic_paths(v2,edge,list,l->paths,all_edges);
        } else if (l->source==v2 && l->dest==v1) {
            list = add_cyclic_paths(v1,edge,list,l->paths,all_edges);
        } else if (l->source==v1 && l->dest != v1) {
            list = add_source_paths(v2,l->dest,edge,list,l->paths,all_edges);
        } else if (l->source==v2 && l->dest != v2) {
            list = add_source_paths(v1,l->dest,edge,list,l->paths,all_edges);
        } else if (l->dest==v1 && l->source != v1) {
            list = add_dest_paths(l->source,v2,l->dest,edge,list,l->paths,all_edges);
        } else if (l->dest==v2 && l->source != v2) {
            list = add_dest_paths(l->source,v1,l->dest,edge,list,l->paths,all_edges);
        }
        l = l->next;
    }

    l = list;
    while (l) {
        if ((l->source==v1 && l->dest==v2) || (l->source==v2 && l->dest==v1)) {
            goto cont;
        }
        l = l->next;
    }
    l = (struct travel_list *)_th_alloc(REWRITE_SPACE,sizeof(struct travel_list));
    l->next = list;
    list = l;
    l->paths = NULL;
    l->source = v1;
    l->dest = v2;

cont:
    p = (struct route_list *)_th_alloc(REWRITE_SPACE,sizeof(struct route_list));
    p->next = l->paths;
    l->paths = p;
    n = p->path = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
    n->next = NULL;
    n->var = v1;
    n->edge = edge;

    _tree_undent();

    return list;
}

static int is_chord(struct signed_list *edge, struct node_list *cycle)
{
    unsigned *fv, v1, v2;
    int count;
    struct node_list *first = cycle;

    if (edge->fv) {
        fv = edge->fv;
        count = edge->count;
    } else {
        int i;
        fv = _th_get_free_vars(edge->e,&count);
        edge->fv = (unsigned *)_th_alloc(REWRITE_SPACE,sizeof(unsigned) * count);
        for (i = 0; i < count; ++i) {
            edge->fv[i] = fv[i];
        }
        edge->count = count;
    }
    v1 = fv[0];
    if (count > 1) {
        v2 = fv[1];
    } else {
        v2 = 0;
    }

    count = 0;
    while (cycle) {
        struct node_list *next = cycle->next;
        if (next==NULL) next = first;
        if (v1==cycle->var && next->var != v2) ++count;
        if (v2==cycle->var && next->var != v1) ++count;
        cycle = cycle->next;
    }

    return count==2;
}

static int duplicate_cycle(struct node_list *cycle1, struct node_list *cycle2)
{
    unsigned v = cycle1->var;
    struct node_list *c;
    int count1, count2;

    count1 = 0;
    c = cycle1;
    while (c) {
        ++count1;
        c = c->next;
    }
    count2 = 0;
    c = cycle2;
    while (c) {
        ++count2;
        c = c->next;
    }
    if (count1 != count2) return 0;

    while (cycle1) {
        c = cycle2;
        while (c) {
            if (cycle1->var==c->var) goto cont;
            c = c->next;
        }
        return 0;
cont:
        cycle1 = cycle1->next;
    }
    return 1;
}

int valid_cycle_to_add(struct cycles *cycles, struct group_list *groups, struct node_list *c)
{
    while (groups) {
        if (is_chord(groups->group,c)) return 0;
        groups = groups->next;
    }

    while (cycles) {
        if (duplicate_cycle(c,cycles->path)) return 0;
        cycles = cycles->next;
    }

    return 1;
}

void add_cycle_edges(struct env *env, struct cycles *cycles)
{
    struct cycles *c = cycles;

    while (c) {
        struct node_list *n = c->path;
        while (n) {
            struct edge_node *edge = (struct edge_node *)n->edge->e->user2;
            struct edge_list *nedge;
            nedge = (struct edge_list *)_th_alloc(REWRITE_SPACE,sizeof(struct edge_list));
            nedge->next = c->edges;
            nedge->var = n->var;
            c->edges = nedge;
            if (edge) {
                struct cycles_list *ncycle = (struct cycles_list *)_th_alloc(REWRITE_SPACE,sizeof(struct cycles_list));
                nedge->node = edge;
                ncycle->next = nedge->node->cycles;
                nedge->node->cycles = ncycle;
                ncycle->cycle = c;
            } else {
                int count;
                unsigned v1,v2;
                unsigned *fv;
                fv = _th_get_free_vars(n->edge->e,&count);
                v1 = fv[0];
                if (count>1) {
                    v2 = fv[1];
                } else {
                    v2 = 0;
                }
                if (v1 != n->var) {
                    int t = v2;
                    v2 = v1;
                    v1 = t;
                }
                nedge->node = (struct edge_node *)_th_alloc(REWRITE_SPACE,sizeof(struct edge_node));
                nedge->node->cycles = (struct cycles_list *)_th_alloc(REWRITE_SPACE,sizeof(struct cycles_list));
                nedge->node->cycles->next = NULL;
                nedge->node->cycles->cycle = c;
                nedge->node->terms = n->edge;
                //printf("v1 v2 %s %s\n", _th_intern_decode(v1), _th_intern_decode(v2));
                //printf("v1 v2 count n->var %d %d %d %d\n", v1, v2, count, n->var);
                //fflush(stdout);
                nedge->node->v1 = v1;
                nedge->node->v2 = v2;
                nedge->node->edge_in_tree = 0;
                n->edge->e->next_cache = trail;
                trail = n->edge->e;
                n->edge->e->user2 = (struct _ex_intern *)nedge->node;
            }
            n = n->next;
        }
        c = c->next;
    }

    while (trail) {
        trail->user2 = NULL;
        trail = trail->next_cache;
    }
}

static struct cycles *old_collect_all_cycles(struct env *env, struct group_list *groups)
{
    struct group_list *g = groups;
    struct travel_list *t = NULL;
    struct route_list *r;
    struct cycles *c, *cycles;
    int count;

    _tree_print0("Collect all cycles");
    _tree_indent();

    while (g) {
        t = add_travel_edge(t,g->group, groups);
        g = g->next;
    }

    cycles = NULL;
    count = 0;

    while (t) {
        if (t->source==t->dest) {
            _tree_print2("Testing edge %s %s", _th_intern_decode(t->source), _th_intern_decode(t->dest));
            r = t->paths;
            _tree_indent();
            while (r) {
#ifndef FAST
                struct node_list *np;
                np = r->path;
                _tree_print0("Testing path");
                _tree_indent();
                while (np) {
                    _tree_print1("node %s", _th_intern_decode(np->var));
                    np = np->next;
                }
                _tree_undent();
#endif
                if (valid_cycle_to_add(cycles, groups, r->path)) {
                    _tree_print0("Adding cycle");
                    c = (struct cycles *)_th_alloc(REWRITE_SPACE,sizeof(struct cycles));
                    c->next = cycles;
                    c->path = r->path;
                    c->number = ++count;
                    c->edges = NULL;
                    cycles = c;
                }
                r = r->next;
            }
            _tree_undent();
        }
        t = t->next;
    }

    _tree_undent();

    add_cycle_edges(env,cycles);

    return cycles;

}

struct edge_pair_list {
    struct edge_pair_list *next;
    struct signed_list *edge1, *edge2;
    unsigned common_vertex, edge1_vertex, edge2_vertex;
    int touched;
    int searched;
};

struct vertex_edge_trail {
    struct vertex_edge_trail *next;
    unsigned vertex;
    struct signed_list *edge;
};

struct path_table {
    struct path_table *next;
    unsigned var;
    struct node_list *path;
    int length;
};

struct distance_table {
    struct distance_table *next;
    unsigned var;
    int index;
    struct path_table *table;
};

static struct distance_table *build_distance_table(struct group_list *list)
{
    struct distance_table *table, *t, *tt;
    struct group_list *l;
    unsigned v1, v2, *fv;
    struct path_table *p;
    struct node_list *n, *node, *pp, *nn;
    struct node_list ***path_table;
    int **distance, i, j, v1i,v2i;
    int count, index;

	//printf("\n    **** Building distance table ****\n\n");

    l = list;
    table = NULL;
    index = 0;
    while (l) {
        fv = _th_get_free_vars(l->group->e,&count);
        v1 = fv[0];
        if (count > 1) {
            v2 = fv[1];
        } else {
            v2 = 0;
        }
        t = table;
        while (t) {
            if (t->var==v1) goto cont1;
            t = t->next;
        }
        t = (struct distance_table *)_th_alloc(REWRITE_SPACE,sizeof(struct distance_table));
        t->next = table;
        table = t;
        t->index = index++;
        t->var = v1;
        t->table = NULL;
        //printf("Adding var %s %d\n", _th_intern_decode(v1), t->index);
cont1:
        t = table;
        while (t) {
            if (t->var==v2) goto cont2;
            t = t->next;
        }
        t = (struct distance_table *)_th_alloc(REWRITE_SPACE,sizeof(struct distance_table));
        t->next = table;
        table = t;
        t->index = index++;
        t->var = v2;
        t->table = NULL;
        //printf("Adding var %s %d\n", _th_intern_decode(v2), t->index);
cont2:
        l = l->next;
    }

    distance = (int **)ALLOCA(sizeof(int *) * index);
    path_table = (struct node_list ***)ALLOCA(sizeof(struct node_list **) * index);

    for (i = 0; i < index; ++i) {
        distance[i] = (int *)ALLOCA(sizeof(int) *index);
        path_table[i] = (struct node_list **)ALLOCA(sizeof(struct node_list *) * index);
        for (j = 0; j < index; ++j) {
            if (i==j) {
                distance[i][j] = 0;
            } else {
                distance[i][j] = 10000000;
            }
            path_table[i][j] = NULL;
        }
    }
	
    l = list;
	while (l) {
		fv = _th_get_free_vars(l->group->e,&count);
		v1 = fv[0];
		if (count > 1) {
			v2 = fv[1];
		} else {
			v2 = 0;
		}
		tt = table;
		while (tt) {
			if (tt->var==v1) v1i = tt->index;
			if (tt->var==v2) v2i = tt->index;
			tt = tt->next;
		}
		//printf("Adding edge %d %d\n", v1i, v2i);

		distance[v1i][v2i] = distance[v2i][v1i] = 1;
		n = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
		n->next = NULL;
		n->edge = l->group;
		n->var = v1;
		path_table[v1i][v2i] = n;

		n = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
		n->next = NULL;
		n->edge = l->group;
		n->var = v2;
		path_table[v2i][v1i] = n;

		l = l->next;
	}

    t = table;
    while (t) {
		for (i = 0; i < index; ++i) {
			for (j = 0; j < index; ++j) {
				if (distance[i][t->index]+distance[t->index][j] < distance[i][j]) {
					distance[i][j] = distance[i][t->index]+distance[t->index][j];
					//printf("Shortening %d to %d with %d\n", i, j, t->index);
					pp = NULL;
					n = path_table[i][t->index];
					while (n) {
						nn = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
						if (pp) {
							pp->next = nn;
						} else {
							node = nn;
						}
						nn->edge = n->edge;
						nn->var = n->var;
						pp = nn;
						n = n->next;
					}
					if (pp) {
						pp->next = path_table[t->index][j];
					} else {
						node = path_table[t->index][j];
					}
					//printf("Assigning %x to path_table[%d][%d]\n", node, i, t->index);
					path_table[i][t->index] = node;
				}
			}
		}
		t = t->next;
	}

#ifdef OLD
	t = table;
    while (t) {
        printf("*** CHECKING VAR %s %d ***\n", _th_intern_decode(t->var), t->index);
        l = list;
        while (l) {
            fv = _th_get_free_vars(l->group->e,&count);
            v1 = fv[0];
            if (count > 1) {
                v2 = fv[1];
            } else {
                v2 = 0;
            }
            tt = table;
            while (tt) {
                if (tt->var==v1) v1i = tt->index;
                if (tt->var==v2) v2i = tt->index;
                tt = tt->next;
            }
            printf("Adding edge %s %d %s %d\n", _th_intern_decode(v1), v1i, _th_intern_decode(v2), v2i);
            if (v1==t->var) {
                for (i = 0; i < index; ++i) {
                    if (v1i != i && distance[v1i][i] > distance[v2i][i]+1) {
                        distance[v1i][i] = distance[v2i][i]+1;
                        n = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
                        n->next = path_table[v2i][i];
                        n->edge = l->group;
                        n->var = v1;
                        printf("    Shortening path 1 from %s to (%d) to %d\n", _th_intern_decode(v1), i, distance[v1i][i]);
                        path_table[v1i][i] = n;
#ifdef XX
                        tt = table;
                        if (n==NULL) {
                            printf("NULL exit\n");
                            exit(1);
                        }
                        while (tt) {
                            if (tt->index==v1i && path_table[v1i][i]->var != tt->var) {
                                printf("tt->var = %s\n", _th_intern_decode(tt->var));
                                printf("n->var = %s\n", _th_intern_decode(n->var));
                                exit(1);
                            }
                            tt = tt->next;
                        }
#endif
                    }
                    if (v1i != i && distance[i][v1i] > distance[i][v2i]+1 && path_table[i][v2i]) {
                        distance[i][v1i] = distance[i][v2i]+1;
                        pp = NULL;
                        n = path_table[i][v2i];
                        while (n) {
                            nn = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
                            if (pp) {
                                pp->next = nn;
                            } else {
                                node = nn;
                            }
                            nn->edge = n->edge;
                            nn->var = n->var;
                            pp = nn;
                            n = n->next;
                        }
                        n = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
                        n->next = NULL;
                        if (pp) {
                            pp->next = n;
                        } else {
                            node = n;
                        }
                        n->edge = l->group;
                        n->var = v2;
                        path_table[i][v1i] = node;
                        printf("    Shortening path 2 from (%d) to %s to %d\n", i, _th_intern_decode(v1), distance[v1i][i]);
#ifdef XX
                        if (node==NULL) {
                            printf("NULL exit\n");
                            exit(1);
                        }
                        tt = table;
                        while (tt) {
                            if (tt->index==i && path_table[i][v1i]->var != tt->var) {
                                printf("tt->var = %s\n", _th_intern_decode(tt->var));
                                printf("node->var = %s\n", _th_intern_decode(node->var));
                                exit(1);
                            }
                            tt = tt->next;
                        }
#endif
                    }
                }

            }
            if (v2==t->var) {
                for (i = 0; i < index; ++i) {
					printf("Testing v1i=%d v2i=%d i=%d %d %d\n", v1i, v2i, i, distance[v2i][i], distance[v1i][i]);
                    if (v2i != i && distance[v2i][i] > distance[v1i][i]+1) {
                        distance[v2i][i] = distance[v1i][i]+1;
                        n = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
                        n->next = path_table[v1i][i];
                        n->edge = l->group;
                        n->var = v2;
                        path_table[v2i][i] = n;
                        printf("    Shortening path 3 from %s to (%d,%d) to %d\n", _th_intern_decode(v2), v2i,i, distance[v2i][i]);
#ifdef XX
                        if (n==NULL) {
                            printf("NULL exit\n");
                            exit(1);
                        }
                        tt = table;
                        while (tt) {
                            if (tt->index==v2i && path_table[v2i][i]->var != tt->var) {
                                exit(1);
                            }
                            tt = tt->next;
                        }
#endif
                    }
					printf("Testing b v1i=%d v2i=%d i=%d %d %d\n", v1i, v2i, i, distance[i][v1i], distance[i][v2i]);
                    if (v1i != i && distance[i][v1i] > distance[i][v2i]+1) {
                        distance[i][v1i] = distance[i][v2i]+1;
                        pp = NULL;
                        n = path_table[i][v2i];
                        printf("i, v1i = %d %d\n", i, v1i);
                        if (n) printf("n->var = %s\n", _th_intern_decode(n->var));
                        while (n) {
                            nn = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
                            if (pp) {
                                pp->next = nn;
                            } else {
                                node = nn;
                            }
                            nn->edge = n->edge;
                            nn->var = n->var;
                            pp = nn;
                            n = n->next;
                        }
                        n = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
                        n->next = NULL;
                        if (pp) {
                            pp->next = n;
                        } else {
                            node = n;
                        }
                        n->edge = l->group;
                        n->var = v1;
                        path_table[i][v2i] = node;
                        printf("    Shortening path 4 from (%d) to %s to %d\n", i, _th_intern_decode(v2), distance[v2i][i]);
#ifdef XX
                        if (node==NULL) {
                            printf("NULL exit\n");
                            exit(1);
                        }
                        tt = table;
                        while (tt) {
                            if (tt->index==i && path_table[i][v2i]->var != tt->var) {
                                printf("tt->var = %s\n", _th_intern_decode(tt->var));
                                printf("node->var = %s\n", _th_intern_decode(node->var));
                                exit(1);
                            }
                            tt = tt->next;
                        }
#endif
                    }
                }

            }
            l = l->next;
        }
        for (i = 0; i < index; ++i) {
            for (j = 0; j < index; ++j) {
                if (i != j) {
                    if (distance[i][j] > distance[i][t->index]+distance[t->index][j]) {
                        distance[i][j] = distance[i][t->index]+distance[t->index][j];
                        pp = NULL;
                        n = path_table[i][t->index];
                        while (n) {
                            nn = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
                            if (pp) {
                                pp->next = nn;
                            } else {
                                node = nn;
                            }
                            nn->edge = n->edge;
                            nn->var = n->var;
                            pp = nn;
                            n = n->next;
                        }
                        if (pp) {
                            pp->next = path_table[t->index][j];
                        } else {
                            node = path_table[t->index][j];
                        }
#ifdef XX
                        if (node==NULL) {
                            printf("NULL exit 3\n");
                            exit(1);
                        }
#endif
                        path_table[i][j] = node;
                    }
                }
            }
        }
        t = t->next;
    }
#endif

    t = table;
    while (t) {
        //printf("Table for var %s\n", _th_intern_decode(t->var));
        for (i = 0; i < index; ++i) {
            if (distance[t->index][i] < 10000000) {
                struct node_list *path;
                p = (struct path_table *)_th_alloc(REWRITE_SPACE,sizeof(struct path_table));
                p->next = t->table;
                t->table = p;
                p->length = distance[t->index][i];
                p->path = path_table[t->index][i];
                tt = table;
                while (tt) {
                    if (tt->index==i) {
                        p->var = tt->var;
                    }
                    tt = tt->next;
                }
                //printf("    to %s is %d\n", _th_intern_decode(p->var), p->length);
#ifdef XX
                path = p->path;
                while (path) {
                    printf("        node %s\n", _th_intern_decode(path->var));
                    path = path->next;
                }
#endif
            }
        }
        t = t->next;
    }
    //fflush(stdout);

    return table;
}

static struct signed_list *find_edge(struct group_list *list, unsigned v1, unsigned v2)
{
    while (list) {
        if (list->count==1) {
            if (v1==0) {
                v1 = v2;
            } else if (v2!=0) {
                goto cont;
            }
            if (v1 != list->fv[0]) goto cont;
            return list->group;
        }
        if ((v1==list->fv[0] && v2==list->fv[1]) || (v1==list->fv[1] && v2==list->fv[0])) return list->group;
cont:
        list = list->next;
    }
    return NULL;
}

static int in_vertex_trail(unsigned vertex, struct vertex_edge_trail *t)
{
    while (t) {
        if (t->vertex==vertex) return 1;
        t = t->next;
    }

    return 0;
}

static struct node_list *get_path(unsigned v1, unsigned v2, int max_path, struct distance_table *dt)
{
    struct path_table *p;

    while (dt && dt->var != v1) {
        dt = dt->next;
    }
    if (dt==NULL) return NULL;

    p = dt->table;
    while (p && p->var != v2) {
        p = p->next;
    }
	if (p==NULL) return NULL;

	_tree_print3("Path %s %s is %d\n", _th_intern_decode(v1), _th_intern_decode(v2), p->length);
    if (p->length <= max_path) return p->path;
    
    return NULL;
}

static int has_big_chord(struct distance_table *dt, struct node_list *cycle)
{
    int count = 0, count1, count2;
    struct node_list *c = cycle;
    struct distance_table *d;
    struct path_table *p;

    while (c) {
        ++count;
        c = c->next;
    }

    while (cycle) {
        c = cycle->next;
        count1 = 1;
        count2 = count-1;
        while (c) {
            int cnt = count1;
            if (count2 < cnt) cnt = count2;
            d = dt;
            while (d && d->var != cycle->var) {
                d = d->next;
            }
            p = d->table;
            while (p && p->var != c->var) {
                p = p->next;
            }
            if (p && p->length < cnt) return 1;
            c = c->next;
        }
        cycle = cycle->next;
    }

    return 0;
}

#define PAIR_HASH_SIZE 1024

static struct cycles *find_big_cycles(unsigned p_vertex, unsigned vertex, struct edge_pair_list *phash[], struct vertex_edge_trail *trail, struct group_list *groups, struct distance_table *dt, struct cycles *cycles)
{
    struct vertex_edge_trail *t = trail, *tt;
    struct edge_pair_list *p, *pp;
    struct node_list *path;
    //int has_chord;
    int len = 0;

    _tree_print2("Finding big cycle %s %s", _th_intern_decode(p_vertex), _th_intern_decode(vertex));
    _tree_indent();

    while (t) {
        //printf("Testing vertex %d %s\n", len, _th_intern_decode(t->vertex));
        if (path = get_path(vertex,t->vertex,len,dt)) {
            struct node_list *n, *nodes, *pn;
            struct cycles *c;
            //printf("Adding big cycle %d %s %s\n", len, _th_intern_decode(vertex), _th_intern_decode(t->vertex));
            _tree_print1("Wrap back to %s", _th_intern_decode(t->vertex));
            nodes = NULL;
            tt = trail;
            while (tt != t) {
                //printf("    1 %s\n", _th_intern_decode(tt->vertex));
                n = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
                n->next = nodes;
                if (nodes==NULL) pn = n;
                n->edge = tt->edge;
                n->var = tt->vertex;
                nodes = n;
                tt = tt->next;
            }
            //printf("    2 %s\n", _th_intern_decode(tt->vertex));
            n = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
            n->next = nodes;
            if (nodes==NULL) pn = n;
            n->edge = tt->edge;
            n->var = tt->vertex;
            nodes = n;
            pn->next = path;
            //while (path) {
            //    n = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
            //    n->next = NULL;
            //    n->edge = path->edge;
            //    n->var = path->var;
            //    printf("    3 %s\n", _th_intern_decode(path->var));
            //    nodes = n;
            //    path = path->next;
            //}
            //printf("    %s\n", _th_intern_decode(t->vertex));
            //fflush(stdout);
            if (valid_cycle_to_add(cycles,groups,nodes) && !has_big_chord(dt, nodes)) {
                c = (struct cycles *)_th_alloc(REWRITE_SPACE,sizeof(struct cycles));
                c->next = cycles;
                c->path = nodes;
                c->edges = NULL;
                c->parent = NULL;
                c->children = NULL;
                if (c->next==NULL) {
                    c->number = 1;
                } else {
                    c->number = c->next->number + 1;
                }
#ifndef FAST
                _tree_indent();
                while (nodes) {
                    _tree_print1("v %s", _th_intern_decode(nodes->var));
                    nodes = nodes->next;
                }
                _tree_undent();
#endif
                cycles = c;
            }
            _tree_undent();
            return cycles;
        }
        ++len;
        t = t->next;
    }
    //printf("trail size %d\n", len);

    p = phash[vertex%PAIR_HASH_SIZE];
	pp = NULL;
    //printf("find big cycles %s %s\n", _th_intern_decode(p_vertex), _th_intern_decode(vertex));
    while (p) {
        if (p->edge1_vertex==p_vertex && p->common_vertex==vertex && !p->searched) {
            t = (struct vertex_edge_trail *)_th_alloc(REWRITE_SPACE,sizeof(struct vertex_edge_trail));
            t->next = trail;
            t->vertex = vertex;
            t->edge = p->edge2;
            p->touched = 1;
            //printf("    Checking edge %s %s %s\n", _th_intern_decode(p->edge1_vertex), _th_intern_decode(p->common_vertex), _th_intern_decode(p->edge2_vertex));
            cycles = find_big_cycles(vertex,p->edge2_vertex,phash,t,groups,dt,cycles);
            p->searched = 1;
			if (pp) {
				pp->next = p->next;
			} else {
				phash[vertex%PAIR_HASH_SIZE] = p->next;
			}
        } else if (p->edge2_vertex==p_vertex && p->common_vertex==vertex && !p->searched) {
            t = (struct vertex_edge_trail *)_th_alloc(REWRITE_SPACE,sizeof(struct vertex_edge_trail));
            t->next = trail;
            t->vertex = vertex;
            t->edge = p->edge1;
            p->touched = 1;
            //printf("    Checking edge %s %s %s\n", _th_intern_decode(p->edge2_vertex), _th_intern_decode(p->common_vertex), _th_intern_decode(p->edge1_vertex));
            cycles = find_big_cycles(vertex,p->edge1_vertex,phash,t,groups,dt,cycles);
            p->searched = 1;
			if (pp) {
				pp->next = p->next;
			} else {
				phash[vertex%PAIR_HASH_SIZE] = p->next;
			}
		} else {
		    pp = p;
		}
        p = p->next;
    }

    _tree_undent();

    return cycles;
}

static struct cycles *collect_all_cycles(struct env *env, struct group_list *groups)
{
    struct group_list *g1 = groups, *g2;
    unsigned g1v1, g1v2, g2v1, g2v2, *fv;
    struct edge_pair_list *pairs, *p, *pp, *phash[PAIR_HASH_SIZE];
    struct cycles *c, *cycles;
    int count, i;
    struct distance_table *dt = build_distance_table(groups);

    _tree_print0("Collect all cycles");
    _tree_indent();

    pairs = NULL;

    while (g1) {
        fv = _th_get_free_vars(g1->group->e,&count);
        g1v1 = fv[0];
        if (count > 1) {
            g1v2 = fv[1];
        } else {
            g1v2 = 0;
        }
        g2 = groups;
        while (g2) {
            fv = _th_get_free_vars(g2->group->e,&count);
            g2v1 = fv[0];
            if (count > 1) {
                g2v2 = fv[1];
            } else {
                g2v2 = 0;
            }
            //p = NULL;
            if (g1v1==g2v1 && g1v2!=g2v2) {
                p = (struct edge_pair_list *)_th_alloc(REWRITE_SPACE,sizeof(struct edge_pair_list));
                p->next = pairs;
                pairs = p;
                p->edge1 = g1->group;
                p->edge2 = g2->group;
                p->common_vertex = g1v1;
                p->edge1_vertex = g1v2;
                p->edge2_vertex = g2v2;
                p->touched = 0;
                p->searched = 0;
            } else if (g1v1==g2v2 && g1v2!=g2v1) {
                p = (struct edge_pair_list *)_th_alloc(REWRITE_SPACE,sizeof(struct edge_pair_list));
                p->next = pairs;
                pairs = p;
                p->edge1 = g1->group;
                p->edge2 = g2->group;
                p->common_vertex = g1v1;
                p->edge1_vertex = g1v2;
                p->edge2_vertex = g2v1;
                p->touched = 0;
                p->searched = 0;
            } else if (g1v2==g2v1 && g1v1!=g2v2) {
                p = (struct edge_pair_list *)_th_alloc(REWRITE_SPACE,sizeof(struct edge_pair_list));
                p->next = pairs;
                pairs = p;
                p->edge1 = g1->group;
                p->edge2 = g2->group;
                p->common_vertex = g2v1;
                p->edge1_vertex = g1v1;
                p->edge2_vertex = g2v2;
                p->touched = 0;
                p->searched = 0;
            } else if (g1v2==g2v2 && g1v1!=g2v1) {
                p = (struct edge_pair_list *)_th_alloc(REWRITE_SPACE,sizeof(struct edge_pair_list));
                p->next = pairs;
                pairs = p;
                p->edge1 = g1->group;
                p->edge2 = g2->group;
                p->common_vertex = g1v2;
                p->edge1_vertex = g1v1;
                p->edge2_vertex = g2v1;
                p->touched = 0;
                p->searched = 0;
            }
            //if (p) {
            //    if (p->edge1_vertex==NULL || p->edge2_vertex==NULL || p->common_vertex==NULL) {
            //        fprintf(stderr, "NULL vertex\n");
            //        exit(1);
            //    }
            //}
            g2 = g2->next;
        }
        g1 = g1->next;
    }

    cycles = NULL;
    count = 0;

	for (i = 0; i < PAIR_HASH_SIZE; ++i) {
		phash[i] = NULL;
	}

	pp = NULL;
	p = pairs;
	while (p) {
		struct signed_list *edge = find_edge(groups,p->edge1_vertex,p->edge2_vertex);
		if (edge) {
			struct node_list *n1, *n2, *n3;
			if (pp) {
				pp->next = p->next;
			} else {
				pairs = p->next;
			}
			n1 = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
			n2 = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
			n3 = (struct node_list *)_th_alloc(REWRITE_SPACE,sizeof(struct node_list));
			n1->next = n2;
			n2->next = n3;
			n3->next = NULL;
			n1->edge = p->edge1;
			n1->var = p->edge1_vertex;
			n2->edge = p->edge2;
			n2->var = p->common_vertex;
			n3->edge = edge;
			n3->var = p->edge2_vertex;
			if (valid_cycle_to_add(cycles, groups, n1)) {
				_tree_print3("Adding triangle %s %s %s", _th_intern_decode(n1->var), _th_intern_decode(n2->var), _th_intern_decode(n3->var));
				c = (struct cycles *)_th_alloc(REWRITE_SPACE,sizeof(struct cycles));
				c->next = cycles;
				c->path = n1;
				c->number = ++count;
				c->edges = NULL;
				c->parent = NULL;
				c->children = NULL;
				cycles = c;
			}
		} else {
			pp = p;
		}
		p = p->next;
	}

#ifdef XX
    p = pairs;
    while (p) {
        printf("Pair %s %s %s\n", _th_intern_decode(p->edge1_vertex), _th_intern_decode(p->common_vertex), _th_intern_decode(p->edge2_vertex));
        p = p->next;
    }
    fflush(stdout);
#endif
    p = pairs;
	while (p) {
		int hash = p->common_vertex%PAIR_HASH_SIZE;
        pp = p->next;
		p->next = phash[hash];
		phash[hash] = p;
		p = pp;
	}

	for (i = 0; i < PAIR_HASH_SIZE; ++i) {
		p = phash[i];
		//count = 0;
		while (p) {
			if (!p->touched) {
				struct vertex_edge_trail *trail, *t;
				t = (struct vertex_edge_trail *)ALLOCA(sizeof(struct vertex_edge_trail));
				t->next = NULL;
				t->vertex = p->edge1_vertex;
				t->edge = p->edge1;
				trail = (struct vertex_edge_trail *)ALLOCA(sizeof(struct vertex_edge_trail));
				trail->next = t;
				trail->vertex = p->common_vertex;
				trail->edge = p->edge2;
				//printf("Starting search %s %s %s\n", _th_intern_decode(p->edge1_vertex), _th_intern_decode(p->common_vertex), _th_intern_decode(p->edge2_vertex));
				p->touched = 1;
				cycles = find_big_cycles(p->common_vertex,p->edge2_vertex,phash,trail,groups,dt,cycles);
				//++count;
				//if (count%500==0) printf("count = %d\n", count);
			}
			p = p->next;
		}
	}
	//printf("count = %d\n", count);
    //printf("Done\n");
    //fflush(stdout);

#ifndef FAST
    c = cycles;
    while (c) {
        struct node_list *n = c->path;
        _tree_print1("cycle %d", c->number);
        _tree_indent();
        while (n) {
            _tree_print1("vertex %s", _th_intern_decode(n->var));
            n = n->next;
        }
        _tree_undent();
        c = c->next;
    }
#endif

    _tree_undent();

    add_cycle_edges(env,cycles);

    return cycles;

}

static struct _ex_intern *_th_get_equality_offset(struct env *env, unsigned vertex, struct _ex_intern *e)
{
    if (!_th_extract_relationship(env,e)) return NULL;
    if (!_th_is_equal_term) return NULL;
    if (_th_right->u.var==vertex || (_th_right->type==EXP_RATIONAL && vertex==0)) {
        char *mark = _th_alloc_mark(REWRITE_SPACE);
        struct _ex_intern *r = _ex_intern_rational(
            _th_big_copy(REWRITE_SPACE,_th_complement(_th_diff->u.rational.numerator)),
            _th_diff->u.rational.denominator);
        _th_alloc_release(REWRITE_SPACE,mark);
        return r;
    }
    return _th_diff;
}

static struct _ex_intern *_th_get_less_offset(struct env *env, unsigned vertex, struct _ex_intern *e, int *dir)
{
    if (!_th_extract_relationship(env,e)) return NULL;
    if (_th_is_equal_term) {
        _th_delta = 0;
        if (_th_left->u.var==vertex || (vertex==0 && _th_left->type==EXP_RATIONAL)) {
            return _th_diff;
        } else {
            char *mark = _th_alloc_mark(REWRITE_SPACE);
            struct _ex_intern *res;
            res = _ex_intern_rational(
                _th_big_copy(REWRITE_SPACE,_th_complement(_th_diff->u.rational.numerator)),
                _th_diff->u.rational.denominator);
            _th_alloc_release(REWRITE_SPACE,mark);
            return res;
        }
    }
    if (_th_right->u.var==vertex || (_th_right->type==EXP_RATIONAL && vertex==0)) {
        char *mark = _th_alloc_mark(REWRITE_SPACE);
        struct _ex_intern *res;
        _th_delta = !_th_delta;
        if (dir) *dir = ((*dir)&4)*2+((*dir)&8)/2;
        res = _ex_intern_rational(
            _th_big_copy(REWRITE_SPACE,_th_complement(_th_diff->u.rational.numerator)),
            _th_diff->u.rational.denominator);
        _th_alloc_release(REWRITE_SPACE,mark);
        return res;
    }
    return _th_diff;
}

static struct _ex_intern *_th_get_greater_offset(struct env *env, unsigned vertex, struct _ex_intern *e)
{
    if (!_th_extract_relationship(env,e)) return NULL;
    if (_th_is_equal_term) {
        _th_delta = 0;
        if (_th_right->u.var==vertex) {
            return _th_diff;
        } else {
            return _ex_intern_rational(
                _th_big_copy(REWRITE_SPACE,_th_complement(_th_diff->u.rational.numerator)),
                _th_diff->u.rational.denominator);
        }
    }
    if (_th_left->u.var==vertex) {
        _th_delta = !_th_delta;
        return _ex_intern_rational(
            _th_big_copy(REWRITE_SPACE,_th_complement(_th_diff->u.rational.numerator)),
            _th_diff->u.rational.denominator);
    }
    return _th_diff;
}

static struct _ex_intern *_th_build_less(struct env *env, unsigned v1, unsigned v2, struct _ex_intern *offset, int delta)
{
    if (delta) {
        return _ex_intern_appl2_env(env,INTERN_RAT_LESS,_ex_intern_appl2_env(env,INTERN_RAT_PLUS,offset,_ex_intern_var(v1)),_ex_intern_var(v2));
    } else {
        return _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_RAT_LESS,_ex_intern_var(v2),_ex_intern_appl2_env(env,INTERN_RAT_PLUS,offset,_ex_intern_var(v1))));
    }
}

static struct _ex_intern *_th_build_equal(struct env *env, unsigned v1, unsigned v2, struct _ex_intern *offset)
{
    struct _ex_intern *x;
    //printf(     "v1, v2, offset = %s %s %s\n", _th_intern_decode(v1), _th_intern_decode(v2), _th_print_exp(offset));
    x = _ex_intern_equal(env,_ex_real,_ex_intern_appl2_env(env,INTERN_RAT_PLUS,offset,_ex_intern_var(v1)),_ex_intern_var(v2));
    return _th_nc_rewrite(env,x);
}

static struct _ex_intern *get_less_dir(struct env *env, unsigned v, struct _ex_intern *e, int *u)
{
    if (!_th_extract_relationship(env,e)) return NULL;
    if ((_th_left->type==EXP_VAR && _th_left->u.var==v) ||
        (_th_left->type==EXP_RATIONAL && !v) ||
        _th_is_equal_term) {
        return e;
    } else {
        if (u) *u = (*u&4)*2+(*u&8)/2;
        return _ex_intern_appl1_env(env,INTERN_NOT,e);
    }
}

static struct _ex_intern *get_greater_dir(struct env *env, unsigned v, struct _ex_intern *e,int *u)
{
    if (!_th_extract_relationship(env,e)) return NULL;
    if ((_th_left->type==EXP_VAR && _th_left->u.var!=v) ||
        (_th_left->type==EXP_RATIONAL && v) ||
        _th_is_equal_term) {
        return e;
    } else {
        if (u) *u = (*u&4)*2+(*u&8)/2;
        return _ex_intern_appl1_env(env,INTERN_NOT,e);
    }
}

static struct _ex_intern *get_ne_term(struct env *env, struct _ex_intern *e, struct edge_node *node)
{
    if (!_th_extract_relationship(env,e)) return NULL;
    if (_th_is_equal_term) {
        return NULL;
    //} else if (!_th_delta) {
    //    return _ex_intern_appl1_env(env,INTERN_NOT,
    //               _ex_intern_appl2_env(env,INTERN_EQUAL,
    //                   _th_left,
    //                   _ex_intern_appl2_env(env,INTERN_RAT_PLUS,_th_right,_th_diff)));
    } else {
        struct signed_list *l = node->terms;
        struct _ex_intern *r =
                   _ex_intern_equal(env,_ex_real,
                       _th_right,
                       _ex_intern_appl2_env(env,INTERN_RAT_PLUS,_th_left,_th_diff));
        while (l) {
            if (l->e==r) return _ex_intern_appl1_env(env,INTERN_NOT,r);
            l = l->next;
        }
        return NULL;
    }
}

struct ve_list {
    struct ve_list *next;
    struct edge_node *node;
    unsigned v1, v2;
    int sign;
    struct _ex_intern *e;
};

static int edges_added = 0;
static int implication_limit = 0;

//static struct _ex_intern *test;

static void add_edge_term(struct env *env, struct edge_node *node, struct _ex_intern *e, int number, struct group_list *group)
{
     struct signed_list *n;
     struct _ex_intern *x;

     if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) e = e->u.appl.args[0];

     e = _th_nc_rewrite(env,e);

     //if (e->u.appl.functor==INTERN_RAT_LESS) {
     //    fprintf(stderr, "Adding less edge %s\n", _th_print_exp(e));
     //    exit(1);
     //}

     n = node->terms;
     while (n) {
         if (n->e==e) {
             //printf("Skipping\n");
             _tree_print_exp("Skipping edge", e);
             return;
         }
         n = n->next;
     }

     n = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
     n->next = node->terms;
     node->terms = n;
     n->e = e;
     n->sign = 0;
     n->source = 2;
     n->count = 0;
     n->fv = NULL;

     x = _th_simp(env,e);
     if (x==_ex_true) {
         n->sign = 4;
     } else if (x==_ex_false) {
         n->sign = 8;
     }

     //printf("Adding edge %s %d\n", _th_print_exp(e), n->sign);

     _tree_print_exp("Adding edge", e);
     //if (test==NULL) {
     //    test = _th_parse(env,"(rless x_272 x_274)");
     //}
     //if (e==test) {
     //    _tree_undent();
     //    _tree_undent();
     //    _tree_undent();
     //    _tree_undent();
     //    _tree_print0("Edge added here");
     //    _tree_indent();
     //    _tree_indent();
     //    _tree_indent();
     //    _tree_indent();
     //}
     n = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
     n->next = group->group;
     group->group = n;
     n->e = e;
     n->sign = 0;
     n->source = 2;
     n->count = 0;
     n->fv = NULL;
     ++edges_added;
}

static int sum_in_range(struct env *env, struct range_info *ri, unsigned v1, unsigned v2, struct _ex_intern *sum)
{
    struct _ex_intern *limit1 = NULL, *limit2 = NULL;
    char *mark = _th_alloc_mark(REWRITE_SPACE);
    int res;

    while (ri) {
        if (ri->var==v1) {
            limit1 = ri->range;
        }
        if (ri->var==v2) {
            limit2 = ri->range;
        }
        ri = ri->next;
    }

    if (limit1==NULL || (limit2 != NULL && _th_rational_less(limit1,limit2))) {
        limit1 = limit2;
    }
    if (_th_big_is_negative(sum->u.rational.numerator)) {
        sum = _ex_intern_rational(
            _th_big_copy(REWRITE_SPACE,_th_complement(sum->u.rational.numerator)),
            sum->u.rational.denominator);
    }
    res = (limit1==NULL || !_th_rational_less(limit1,sum));
    _th_alloc_release(REWRITE_SPACE,mark);

    return res;
}

struct _ex_intern *range_var, *range_sum;

static void gc(struct env *env, struct edge_list *all_edges, struct edge_list *edge, struct ve_list *tail,int number, struct group_list *group, struct range_info *ri)
{
    if (all_edges==edge) {
        gc(env,all_edges->next,edge,tail,number,group,ri);
    } else if (all_edges==NULL && number > 0) {
        int delta = 0;
        int un = 0;
        struct _ex_intern *sum = _ex_intern_small_rational(0,1);
        struct _ex_intern *esum = _ex_intern_small_rational(0,1);
        _tree_print0("Processing sequence");
        _tree_indent();
        while (tail) {
            struct _ex_intern *s;
            _tree_print2("term %s %s", _th_intern_decode(tail->v1), _th_print_exp(tail->e));
            if (esum) {
                //if (tail->sign & 8) {
                //    esum = NULL;
                //} else {
                    s = _th_get_equality_offset(env,tail->v1,tail->e);
                    _tree_print1("e offset %s", _th_print_exp(s));
                    if (s) {
                        esum = _th_add_rationals(s,esum);
                        //sum = _th_add_rationals(s,sum);
                    } else {
                        esum = NULL;
                    }
                //}
            }
            if (sum) {
                int u = tail->sign;
                //if ((tail->sign & 8) && tail->e->u.appl.functor==INTERN_EQUAL) {
                //    sum = NULL;
                //} else {
                    s = _th_get_less_offset(env,tail->v1,tail->e, &u);
                    un |= u;
                    _tree_print3("offset delta u %s %d %d", _th_print_exp(s), _th_delta, u);
                    if ((un & 12)==12) {
                        sum = NULL;
                    } else {
                        if (s) {
                            sum = _th_add_rationals(s,sum);
                        } else {
                            sum = NULL;
                        }
                    }
                //}
                delta = (delta || _th_delta);
            }
            tail = tail->next;
        }
        _tree_print_exp("sum", sum);
        _tree_print_exp("esum", esum);
        _tree_print1("delta %d", delta);
        if (esum) {
            if (sum_in_range(env,ri,edge->node->v1,edge->node->v2,esum)) {
                add_edge_term(env,edge->node,_th_build_equal(env,edge->node->v2,edge->node->v1,esum),number,group);
            } else {
                _tree_undent();
                _tree_print0("Out of range eq");
                _tree_indent();
            }
        } else if (sum) {
            if (sum_in_range(env,ri,edge->node->v1,edge->node->v2,sum)) {
                add_edge_term(env,edge->node,_th_build_less(env,edge->node->v2,edge->node->v1,sum,delta),number,group);
            } else {
                _tree_undent();
                _tree_print0("Out of range");
                _tree_indent();
            }
        }
        _tree_undent();
    } else if (all_edges != NULL) {
        struct signed_list *l = all_edges->node->terms;
        while (l) {
            int n;
            //if (l->source != 2) {
                struct ve_list *v;
                _th_extract_relationship(env,l->e);
                if (!_th_is_equal_term && range_sum && (_th_left==range_var || _th_right==range_var) && (l->sign & 12)) goto cont;
                v = (struct ve_list *)ALLOCA(sizeof(struct ve_list));
                v->next = tail;
                v->e = l->e;
                v->v1 = all_edges->var;
                if (all_edges->var==all_edges->node->v1) {
                    v->v2 = all_edges->node->v2;
                } else {
                    v->v2 = all_edges->node->v1;
                }
                v->sign = l->sign;
                n = number;
                if (l->source==1) n = 1;
                gc(env,all_edges->next,edge,v,n,group,ri);
                if (edges_added > implication_limit) return;
cont:;
            //}
            l = l->next;
        }
    }
}

static void gc_zero_case(struct env *env, struct edge_list *all_edges, struct ve_list *tail, int number, struct group_list *group)
{
    if (all_edges==NULL) {
        int pos_delta = 0, neg_delta = 0;
        int un = 0;
        struct ve_list *t = tail;
        struct _ex_intern *sum = _ex_intern_small_rational(0,1);
        struct _ex_intern *esum = _ex_intern_small_rational(0,1);
        _tree_print0("Processing sequence");
        _tree_indent();
        printf("    TESTING SEQUENCE\n");
        while (tail) {
            struct _ex_intern *s;
            //printf("        %s %d\n", _th_print_exp(tail->e), tail->sign);
            _tree_print2("term %s %s", _th_intern_decode(tail->v1), _th_print_exp(tail->e));
            if (esum) {
                //if (tail->sign & 8) {
                //    esum = NULL;
                //} else {
                    s = _th_get_equality_offset(env,tail->v1,tail->e);
                    //printf("            equality offset %s\n", _th_print_exp(s));
                    if (s) {
                        esum = _th_add_rationals(s,esum);
                        //sum = _th_add_rationals(s,sum);
                    } else {
                        esum = NULL;
                    }
                //}
            }
            if (sum) {
                int u = tail->sign;
                s = _th_get_less_offset(env,tail->v1,tail->e, &u);
                //printf("            less offset %s %d\n", _th_print_exp(s), u);
                un |= u;
                _tree_print2("offset delta %s %d", _th_print_exp(s), _th_delta);
                if ((un & 12)==12) {
                    sum = NULL;
                } else {
                    if (s) {
                        sum = _th_add_rationals(s,sum);
                    } else {
                        sum = NULL;
                    }
                }
                if (!_th_is_equal_term) {
                    if (_th_delta) {
                        pos_delta = 1;
                    } else {
                        neg_delta = 1;
                    }
                }
            }
            tail = tail->next;
        }
        tail = t;
        _tree_print_exp("sum", sum);
        _tree_print_exp("esum", esum);
        //printf("    sum %s\n", _th_print_exp(sum));
        //printf("    esum %s\n", _th_print_exp(esum));
        //printf("    delta %d %d\n", pos_delta, neg_delta);
        _tree_print2("delta %d %d", pos_delta, neg_delta);
        if (!esum && sum && sum->u.rational.numerator[0]==1 && sum->u.rational.numerator[1]==0) {
            printf("Checking add gc_zero %d %d\n", pos_delta, neg_delta);
            if (pos_delta && !neg_delta) {
                t = tail;
                while (t) {
                    struct _ex_intern *e = _th_get_less_offset(env,t->v1,t->e,NULL);
                    //printf("Checking add %s %s\n", _th_print_exp(t->e), _th_intern_decode(t->v1));
                    //printf("    offset %s\n", _th_print_exp(e));
                    add_edge_term(env,t->node,(sum = _th_build_equal(env,t->v1,t->v2,e)),number,group);
                    //printf("    added %s\n", _th_print_exp(sum));
                    t = t->next;
                }
            } else if (neg_delta && !pos_delta) {
                t = tail;
                while (t) {
                    struct _ex_intern *e = _th_get_less_offset(env,t->v2,t->e,NULL);
                    //printf("Checking add 2 %s %s\n", _th_print_exp(t->e), _th_intern_decode(t->v2));
                    //printf("    offset %s\n", _th_print_exp(e));
                    add_edge_term(env,t->node,(sum = _th_build_equal(env,t->v2,t->v1,e)),number,group);
                    printf("    added %s\n", _th_print_exp(sum));
                    t = t->next;
                }
            }
        }
        _tree_undent();
    } else {
        struct signed_list *l = all_edges->node->terms;
        while (l) {
            //if (l->source != number) {
                struct ve_list *v;
                _th_extract_relationship(env,l->e);
                if (!_th_is_equal_term && range_sum && (_th_left==range_var || _th_right==range_var) && (l->sign & 12)) goto cont;
                v = (struct ve_list *)ALLOCA(sizeof(struct ve_list));
                v->next = tail;
                v->e = l->e;
                v->v1 = all_edges->var;
                if (all_edges->var==all_edges->node->v1) {
                    v->v2 = all_edges->node->v2;
                } else {
                    v->v2 = all_edges->node->v1;
                }
                v->sign = l->sign;
                v->node = all_edges->node;
                gc_zero_case(env,all_edges->next,v,number,group);
                //if (edges_added > implication_limit) return;
            //}
cont:
            l = l->next;
        }
    }
}

static void generate_completions(struct env *env, struct cycles *cycle, struct edge_list *edge, struct group_list *group, struct range_info *ri)
{
    struct edge_list *all_edges = cycle->edges;
    //struct signed_list *t;
    int x = edges_added;

    _tree_print3("Processing edge %s %s %d", _th_intern_decode(edge->node->v1), _th_intern_decode(edge->node->v2), implication_limit-edges_added);
    //_th_derive_push(env);
    //t = terms;
    //while (t) {
    //    if (t->sign & 4) {
    //        _th_assert_predicate(env,t->e);
    //    } else if (t->sign & 8) {
    //        _th_deny_predicate(env,t->e);
    //    }
    //    t = t->next;
    //}
    //printf("Processing cycle %d %s %s %s\n", cycle->number,
    //       _th_intern_decode(cycle->edges->var), _th_intern_decode(cycle->edges->next->var), _th_intern_decode(cycle->edges->next->next->var));
    _tree_indent();
    gc(env,all_edges,edge,NULL,0,group,ri);
    _tree_print1("Edges added %d", edges_added - x);
    //_th_derive_pop(env);
    _tree_undent();
}

static int edge_in_cycle(struct cycles *cycles, struct edge_list *edge)
{
    struct edge_list *e;
    while (cycles) {
        e = cycles->edges;
        while (e) {
            if (e->node==edge->node) return 1;
            e = e->next;
        }
        cycles = cycles->next;
    }
    return 0;
}

static int check_complete(struct env *env, struct edge_list *all_edges, struct _ex_intern *sum)
{
    if (all_edges==NULL) {
        if (sum->u.rational.numerator[0] != 1 || sum->u.rational.numerator[1] != 0) return 0;
        return 1;
    } else {
        struct signed_list *l = all_edges->node->terms;
        while (l) {
            struct _ex_intern *s;
            unsigned v;

            if (all_edges->var==all_edges->node->v1) {
                v = all_edges->node->v2;
            } else {
                v = all_edges->node->v1;
            }

            s = _th_get_less_offset(env,v,l->e,NULL);

            s = _th_add_rationals(s,sum);

            if (!check_complete(env,all_edges->next,s)) return 0;
            l = l->next;
        }
        return 1;
    }
}

static int is_complete_cycle(struct env *env, struct cycles *cycle)
{
    return check_complete(env,cycle->edges,_ex_intern_small_rational(0,1));

    cycle->edges;
}

static struct edge_list *shared_edge(struct cycles *cycle1, struct cycles *cycle2)
{
    struct edge_list *e1 = cycle1->edges;
    struct edge_list *e2;

    while (e1) {
        e2 = cycle2->edges;
        while (e2) {
            if (e1->node==e2->node) return e1;
            e2 = e2->next;
        }
        e1 = e1->next;
    }

    return NULL;
}

static int edge_in_tree(struct edge_node *edge)
{
    struct cycles_list *cl = edge->cycles;

    //_tree_print2("Testing edge_in_tree %s %s", _th_intern_decode(edge->v1), _th_intern_decode(edge->v2));
    //_tree_indent();

    while (cl) {
        //_tree_print1("Testing cycle %x", cl->cycle);
        if (cl->cycle->parent) {
            //_tree_undent();
            //_tree_print0("Good");
            return 1;
        }
        cl = cl->next;
    }

    //_tree_undent();
    return 0;
}

static int contiguous_edge_in_tree(struct cycles *cycle)
{
    struct edge_list *el = cycle->edges;
    if (edge_in_tree(el->node)) {
        el = el->next;
        while (el && edge_in_tree(el->node)) {
            el = el->next;
        }
        if (!el) return 1;
        while (el && !edge_in_tree(el->node)) {
            el = el->next;
        }
        if (!el) return 1;
        while (el && edge_in_tree(el->node)) {
            el = el->next;
        }
        return (el==NULL);
    } else {
        el = el->next;
        while (el && !edge_in_tree(el->node)) {
            el = el->next;
        }
        if (!el) return 0;
        while (el && edge_in_tree(el->node)) {
            el = el->next;
        }
        if (!el) return 1;
        while (el && !edge_in_tree(el->node)) {
            el = el->next;
        }
        return (el==NULL);
    }

}

static int cycle_level(struct cycles *cycle)
{
    int level = 0;
    if (cycle->parent==NULL) return -1;
    while (cycle->parent && cycle->parent != cycle) {
        cycle = cycle->parent;
        ++level;
    }
    return level;
}

static int edge_level(struct edge_node *node)
{
    struct cycles_list *cl = node->cycles;
    struct cycles *c;
    int level;

    while (cl && cl->cycle->parent==NULL) {
        cl = cl->next;
    }
    if (!cl) return -1;

    c = cl->cycle;
    level = cycle_level(c);
    cl = cl->next;
    while (cl) {
        c = cl->cycle;
        if (c->parent) {
            int l = cycle_level(c);
            if (l < level) level = l;
        }
        cl = cl->next;
    }

    return level;
}

static void build_tree(struct env *env, struct cycles *cycles)
{
    struct cycles *c = cycles;
    struct cycles *root, *choice, *parent;
    struct cycles_list *child;
    struct edge_list *el;
    struct edge_list *node;
    int is_complete, ic;
    int level, l;
#ifndef FAST
    struct node_list *n;
#endif

    _tree_print0("Building tree");
    _tree_indent();

    if (cycles==NULL) {
        _tree_undent();
        return;
    }

    while (c) {
        if (!is_complete_cycle(env,c)) {
            root = c;
            root->parent = root;
            goto cont;
        }
        c = c->next;
    }
    root = cycles;
    root->parent = root;
    root->parent_edge = NULL;
cont:
#ifndef FAST
    _tree_print1("Root %x", root);
    _tree_indent();
    n = root->path;
    while(n) {
        _tree_print1("node %s", _th_intern_decode(n->var));
        n = n->next;
    }
    _tree_undent();
#endif
    while (1) {
        c = cycles;
        choice = NULL;
        while (c) {
            //_tree_print2("Testing cycle %x %x\n", c, c->parent);
            if (c->parent==NULL && contiguous_edge_in_tree(c)) {
                ic = is_complete_cycle(env,c);
                if (choice==NULL || (is_complete && !ic)) {
                    choice = c;
                    is_complete = ic;
                    parent = NULL;
                    el = c->edges;
                    while (el) {
                        if (edge_in_tree(el->node)) {
                            struct cycles_list *p = el->node->cycles;
                            while (p) {
                                if (p->cycle->parent) {
                                    l = cycle_level(p->cycle);
                                    if (is_complete) {
                                        if (parent==NULL || l > level) {
                                            level = l;
                                            parent = p->cycle;
                                            node = el;
                                        }
                                    } else {
                                        if (parent==NULL || l < level) {
                                            level = l;
                                            parent = p->cycle;
                                            node = el;
                                        }
                                    }
                                }
                                p = p->next;
                            }
                        }
                        el = el->next;
                    }
                } else if (is_complete && ic) {
                    el = c->edges;
                    while (el) {
                        if (edge_in_tree(el->node)) {
                            struct cycles_list *p = el->node->cycles;
                            while (p) {
                                if (p->cycle->parent) {
                                    l = cycle_level(p->cycle);
                                    if (parent==NULL || l > level) {
                                        level = l;
                                        parent = p->cycle;
                                        choice = c;
                                        node = el;
                                    }
                                }
                                p = p->next;
                            }
                        }
                        el = el->next;
                    }
                } else if (!is_complete && !ic) {
                    el = c->edges;
                    while (el) {
                        if (edge_in_tree(el->node)) {
                            struct cycles_list *p = el->node->cycles;
                            while (p) {
                                if (p->cycle->parent) {
                                    l = cycle_level(p->cycle);
                                    if (parent==NULL || l < level) {
                                        level = l;
                                        parent = p->cycle;
                                        choice = c;
                                        node = el;
                                    }
                                }
                                p = p->next;
                            }
                        }
                        el = el->next;
                    }
                }
            }
            c = c->next;
        }
        if (choice==NULL) {
            _tree_undent();
            return;
        }
#ifndef FAST
        _tree_print1("Adding child %x", choice);
        _tree_indent();
        n = choice->path;
        while(n) {
            _tree_print1("node %s", _th_intern_decode(n->var));
            n = n->next;
        }
        _tree_undent();
#endif
        choice->parent = parent;
        choice->parent_edge = node;
        child = (struct cycles_list *)_th_alloc(REWRITE_SPACE,sizeof(struct cycles_list));
        child->next = parent->children;
        parent->children = child;
        child->cycle = choice;
    }
}

static void update_source_info(struct cycles *cycles)
{
    struct cycles *c = cycles;
    struct edge_list *edge;
    struct signed_list *l;

    while (c) {
        edge = c->edges;
        while (edge) {
            l = edge->node->terms;
            while (l) {
                if (l->source < 16 && l->source > 1) {
                    l->source += 16;
                }
                l = l->next;
            }
            edge = edge->next;
        }
        c = c->next;
    }

    c = cycles;
    while (c) {
        edge = c->edges;
        while (edge) {
            l = edge->node->terms;
            while (l) {
                l->source &= 15;
                l = l->next;
            }
            edge = edge->next;
        }
        c = c->next;
    }
}

static struct edge_list *single_connected_edge(struct cycles *cycle)
{
    struct edge_list *edge;
    struct edge_list *single = NULL;

    edge = cycle->edges;
    while (edge) {
        struct cycles_list *c = edge->node->cycles;
        while (c) {
            if (!c->cycle->parent && c->cycle != cycle) {
                if (single==NULL) {
                    single = edge;
                } else {
                    return NULL;
                }
                goto cont;
            }
            c = c->next;
        }
cont:
        edge = edge->next;
    }
    return single;
}

static int no_connected_edge(struct cycles *cycle)
{
    struct edge_list *edge;
    struct edge_list *single = NULL;

    edge = cycle->edges;
    while (edge) {
        struct cycles_list *c = edge->node->cycles;
        while (c) {
            if (!c->cycle->parent && c->cycle != cycle) {
                return 0;
            }
            c = c->next;
        }
        edge = edge->next;
    }
    return 1;
}

#define ABSOLUTE_LIMIT 10000

static int add_implication_edges(struct env *env, struct cycles *cycles, struct group_list *group, struct range_info *ri,int count)
{
    struct cycles *c = cycles;
    int change;
    //struct edge_list *edge;
    struct signed_list *t;
    struct range_info *rii;
    int check_limit = 1;

    range_sum = NULL;
    if (ri) {
        if (_th_is_integer_logic()) {
            check_limit = 0;
        }
        range_sum = ri->range;
        _tree_print_exp("range_var", range_var);
        _tree_print_exp("range_sum", range_sum);
        rii = ri->next;
        while (rii) {
            if (rii->range != ri->range) {
                range_sum = NULL;
                goto cont1;
            }
            rii = rii->next;
        }
    }
cont1:

    implication_limit = count;
    //while (c) {
    //    struct edge_list *edge = c->edges;
    //    while (edge) {
    //        struct signed_list *s = edge->node->terms;
    //        implication_limit += 10;
    //        //while (s) {
    //        //    implication_limit += 1;
    //        //    s = s->next;
    //        //}
    //        edge = edge->next;
    //    }
    //    c = c->next;
    //}

    _tree_print0("Adding implication edges");
    edges_added = 0;
    _tree_indent();
    _tree_print1("Limit %d", implication_limit);

    _th_derive_push(env);
    if (cycles) {
        t = terms;
        while (t) {
            if (t->sign & 4) {
                _th_assert_predicate(env,t->e);
            } else if (t->sign & 8) {
                _th_deny_predicate(env,t->e);
            }
            t = t->next;
        }
    }

    change = 1;
    while (change) {
        change = 0;
        c = cycles;
        while (c) {
            if (c->parent==NULL) {
                struct edge_list *edge = single_connected_edge(c);
                if (edge) {
                    struct signed_list *t = edge->node->terms;
                    int ec = 0;
                    int ea = edges_added;
#ifndef FAST
                    struct edge_list *e1;
                    _tree_print1("Cycle has parent %d", c->number);
                    _tree_indent();
                    e1 = c->edges;
                    while (e1) {
                        _tree_print2("Vertex %s %s", _th_intern_decode(e1->node->v1), _th_intern_decode(e1->node->v2));
                        e1 = e1->next;
                    }
                    _tree_undent();
#endif
                    while (t) {
                        ++ec;
                        t = t->next;
                    }
                    implication_limit = edges_added;
                    implication_limit += ec*5;
                    //if (edge_in_cycle(c->next,edge)) {
                    generate_completions(env,c,edge,group,ri);
                    //} else {
                    //    _tree_print2("Not processing edge %s %s", _th_intern_decode(edge->node->v1), _th_intern_decode(edge->node->v2));
                    //}
                    if ((check_limit && (edges_added > implication_limit)) || edges_added > ABSOLUTE_LIMIT) {
                        _th_derive_pop(env);
                        _tree_undent();
                        return 1;
                    }
                    c->parent = c;
                    change = 1;
                } else if (no_connected_edge(c)) {
                    _tree_print1("Root cycle %d", c->number);
                    c->parent = c;
                }
            }
            c = c->next;
        }
    }

    change = 1;
    while (change) {
        change = 0;
        c = cycles;
        _tree_print1("Round %d", edges_added);
        _tree_indent();
        while (c) {
            if (c->parent==NULL) {
                struct edge_list *edge = c->edges;
#ifndef FAST
                _tree_print1("Cycle %d", c->number);
                _tree_indent();
                while (edge) {
                    _tree_print2("Vertex %s %s", _th_intern_decode(edge->node->v1), _th_intern_decode(edge->node->v2));
                    edge = edge->next;
                }
                _tree_undent();
                edge = c->edges;
#endif
                while (edge) {
                    struct signed_list *t = edge->node->terms;
                    int ec = 0;
                    int ea = edges_added;
                    while (t) {
                        if (t->source<2) ++ec;
                        t = t->next;
                    }
                    _tree_print1("Edge count %d", ec);
                    implication_limit = edges_added;
                    implication_limit += ec*5;
                    //if (edge_in_cycle(c->next,edge)) {
                    generate_completions(env,c,edge,group,ri);
                    //} else {
                    //    _tree_print2("Not processing edge %s %s", _th_intern_decode(edge->node->v1), _th_intern_decode(edge->node->v2));
                    //}
                    if ((check_limit && (edges_added > implication_limit)) || edges_added > ABSOLUTE_LIMIT) {
                        _th_derive_pop(env);
                        _tree_undent();
                        _tree_undent();
                        return 1;
                    }
                    if (edges_added != ea) change = 1;
                    edge = edge->next;
                }
                //_tree_print1("Edges added so far %d", edges_added);
            }
            c = c->next;
        }
        _tree_undent();
        update_source_info(cycles);
    }
    //cycles = c;
    //while (cycles) {
    //    printf("gc_zero_case %d\n", cycles->number);
    //    gc_zero_case(env,cycles->edges,NULL,cycles->number,group);
    //    printf("done gc_zero_case\n");
    //    cycles = cycles->next;
    //}
    _th_derive_pop(env);
    _tree_undent();
    return 0;
}

static int added_conflict;

#define CONFLICT_LIMIT 100000
static int conflicts_generated;

struct group_list *equality_out_of_bounds_conflicts(struct env *env, struct ve_list *tail, struct group_list *conflicts, struct range_info *ri)
{
    struct ve_list *pos = tail, *prev = NULL;
    struct _ex_intern *s, *esum;
    struct signed_list *sterm, *n, *nn, *build;
    struct group_list *nc;
    int count, pcount;

    sterm = NULL;
    while (pos) {
        struct ve_list *check = pos;
        count = 0;
        esum = _ex_intern_small_rational(0,1);
        build = NULL;
        while (check != prev) {
            ++count;
            s = _th_get_equality_offset(env,check->v1,check->e);
            esum = _th_add_rationals(s,esum);
            n = (struct signed_list *)ALLOCA(sizeof(struct signed_list));
            n->count = 0;
            n->fv = NULL;
            n->next = build;
            build = n;
            build->e = check->e;
            build->sign = check->sign;
            build->source = 0;
            if (!sum_in_range(env,ri,pos->v1,check->v2,esum)) {
                if (sterm && pcount <= count) {
                    nc = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
                    nc->next = conflicts;
                    n = NULL;
                    //printf("Adding tuple c\n");
                    _tree_print0("Adding out of bounds tuple 1");
                    _tree_indent();
                    while (sterm) {
                        //printf("    term %s\n", _th_print_exp(sterm->e));
                        //_tree_print2("sign,exp %d %s", sterm->sign, _th_print_exp(sterm->e));
                        //if (sterm->sign&8) {
                        //    _tree_undent();
                        //    goto cont1;
                        //}
                        //if ((sterm->sign&4)==0) {
                            nn = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                            nn->next = n;
                            n = nn;
                            n->e = sterm->e;
                            _tree_print_exp("e", n->e);
                            n->sign = sterm->sign;
                            n->source = sterm->source;
                            n->count = 0;
                            n->fv = NULL;
                        //}
                        sterm = sterm->next;
                    }
                    _tree_undent();
                    pcount = count;
                    check_tuple(env,n,"equality1");
                    nc->group = n;
                    conflicts = nc;
                    ++conflicts_generated;
                }
//cont1:
                sterm = build;
                pcount = count;
                goto cont;
            }
            check = check->next;
            if (prev && check==NULL) check = tail;
        }
cont:
        prev = pos;
        pos = pos->next;
    }
    if (sterm) {
        nc = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
        nc->next = conflicts;
        n = NULL;
        //printf("Adding tuple d\n");
        _tree_print0("Adding out of bounds tuple 2");
        _tree_indent();
        while (sterm) {
            //printf("    term %s\n", _th_print_exp(sterm->e));
            nn = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
            nn->next = n;
            n = nn;
            n->e = sterm->e;
            _tree_print_exp("term",n->e);
            n->sign = sterm->sign;
            n->source = sterm->source;
            n->count = 0;
            n->fv = NULL;
            sterm = sterm->next;
        }
        _tree_undent();
        check_tuple(env,n,"equality2");
        nc->group = n;
        conflicts = nc;
        ++conflicts_generated;
    }

    return conflicts;
}

struct group_list *inequality_out_of_bounds_conflicts(struct env *env, struct ve_list *tail, struct group_list *conflicts, struct range_info *ri)
{
    struct ve_list *pos = tail, *prev = NULL;
    struct _ex_intern *s, *sum, *ssum;
    struct signed_list *sterm, *n, *nn, *build;
    struct group_list *nc;
    int count, pcount;

    _tree_print0("inequality out of bounds");
    _tree_indent();

    sterm = NULL;
    while (pos) {
        struct ve_list *check = pos;
        count = 0;
        sum = _ex_intern_small_rational(0,1);
        build = NULL;
        _tree_print3("Checking start %s %s %s", _th_intern_decode(pos->v1), _th_intern_decode(pos->v2), _th_print_exp(pos->e));
        _tree_indent();
        while (check != prev) {
            _tree_print_exp("Checking", check->e);
            ++count;
            //printf("Getting less offset of %s %s\n", _th_intern_decode(check->v1), _th_print_exp(check->e));
            s = _th_get_less_offset(env,check->v1,check->e,NULL);
            sum = _th_add_rationals(s,sum);
            _tree_print_exp("sum", sum);
            n = (struct signed_list *)ALLOCA(sizeof(struct signed_list));
            n->next = build;
            build = n;
            build->e = check->e;
            build->sign = check->sign;
            build->source = check->v1;
            if (!sum_in_range(env,ri,pos->v1,check->v2,sum)) {
                _tree_print0("Adding tuple");
                //printf("Adding tuple\n");
                if (sterm && pcount <= count) {
                    //printf("Here\n");
                    _tree_print0("Adding new tuple");
                    nc = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
                    nc->next = conflicts;
                    n = NULL;
                    _tree_print0("tuple");
                    _tree_indent();
                    while (sterm) {
                        struct _ex_intern *e;
                        unsigned u = sterm->sign;
                        //printf("    ");
                        if (_th_big_is_negative(ssum->u.rational.numerator)) {
                            //printf("f %d %s", u, _th_intern_decode(sterm->source));
                            e = get_greater_dir(env,sterm->source,sterm->e,&u);
                            //printf("%s\n", _th_print_exp(e));
                            _tree_print_exp("e", e);
                            if (u&8) {
                                _tree_print0("cancel");
                                _tree_undent();
                                goto cont1;
                            }
                            if ((u&4)==0) {
                                nn = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                                nn->next = n;
                                n = nn;
                                //if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                                //    n->e = e->u.appl.args[0];
                                //} else {
                                //    n->e = _ex_intern_appl1_env(env,INTERN_NOT,e);
                                //}
                                n->e = e;
                                n->sign = sterm->sign;
                                n->source = sterm->source;
                                n->count = 0;
                                n->fv = NULL;
                            }
                        } else {
                            //printf("b %d %s", u, _th_intern_decode(sterm->source));
                            e = get_less_dir(env,sterm->source,sterm->e,&u);
                            //printf("%s\n", _th_print_exp(e));
                            _tree_print_exp("e", e);
                            if (u&8) {
                                _tree_print0("cancel");
                                _tree_undent();
                                goto cont1;
                            }
                            if ((u&4)==0) {
                                nn = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                                nn->next = n;
                                n = nn;
                                n->e = e;
                                n->sign = sterm->sign;
                                n->source = sterm->source;
                                n->count = 0;
                                n->fv = NULL;
                            }
                        }
                        sterm = sterm->next;
                    }
                    _tree_undent();
                    pcount = count;
                    nc->group = n;
                    check_tuple(env,n,"inequality1");
                    conflicts = nc;
                    ++conflicts_generated;
                }
cont1:
                sterm = build;
                ssum = sum;
                pcount = count;
                goto cont;
            }
            check = check->next;
            if (prev && check==NULL) check = tail;
        }
cont:
        _tree_undent();
        prev = pos;
        pos = pos->next;
    }
    if (sterm) {
        _tree_print0("Adding new tuple b");
        nc = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
        nc->next = conflicts;
        n = NULL;
        _tree_print0("Tuple");
        _tree_indent();
        //printf("Adding tuple b\n");
        while (sterm) {
            struct _ex_intern *e;
            unsigned u = sterm->sign;
            //printf("    ");
            if (_th_big_is_negative(ssum->u.rational.numerator)) {
                //printf("f %d %s", u, _th_intern_decode(sterm->source));
                e = get_greater_dir(env,sterm->source,sterm->e,&u);
                //printf("%s\n", _th_print_exp(e));
                _tree_print_exp("e", e);
                if (u&8) {
                    _tree_print0("cancel");
                    _tree_undent();
                    goto cont2;
                }
                if ((u&4)==0) {
                    nn = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                    nn->next = n;
                    n = nn;
                    //if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                    //    n->e = e->u.appl.args[0];
                    //} else {
                    //    n->e = _ex_intern_appl1_env(env,INTERN_NOT,e);
                    //}
                    n->e = e;
                    n->sign = sterm->sign;
                    n->source = sterm->source;
                    n->count = 0;
                    n->fv = NULL;
                }
            } else {
                //printf("b %d %s", u, _th_intern_decode(sterm->source));
                e = get_less_dir(env,sterm->source,sterm->e,&u);
                //printf("%s\n", _th_print_exp(e));
                _tree_print_exp("e", e);
                if (u&8) {
                    _tree_print0("cancel");
                    _tree_undent();
                    goto cont2;
                }
                if ((u&4)==0) {
                    nn = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                    nn->next = n;
                    n = nn;
                    n->e = e;
                    n->sign = sterm->sign;
                    n->source = sterm->source;
                    n->count = 0;
                    n->fv = NULL;
                }
            }
            sterm = sterm->next;
        }
        _tree_undent();
        nc->group = n;
        check_tuple(env,n,"inequality2");
        conflicts = nc;
        ++conflicts_generated;
    }

cont2:
    _tree_undent();
    return conflicts;
}

static struct group_list *generate_cycle_conflicts(struct env *env, struct edge_list *all_edges, struct ve_list *tail, int number, struct group_list *conflicts, struct range_info *ri)
{
    if (all_edges==NULL) {
        int delta = 0, pos_delta = 0, neg_delta = 0;
        int do_add = 0;
        struct _ex_intern *sum = _ex_intern_small_rational(0,1);
        struct _ex_intern *esum = _ex_intern_small_rational(0,1);
        struct signed_list *c, *n;
        struct group_list *nc;
        struct ve_list *t;
        _tree_print0("Processing sequence");
        _tree_indent();
        t = tail;
        while (t) {
            struct _ex_intern *s;
            int u = t->sign;
            _tree_print3("term %s %s %d", _th_intern_decode(t->v1), _th_print_exp(t->e), t->sign);
            if (t->sign & 16) do_add = 1;
            if (esum) {
                s = _th_get_equality_offset(env,t->v1,t->e);
                _tree_print1("e offset %s", _th_print_exp(s));
                if (s) {
                    esum = _th_add_rationals(s,esum);
                } else {
                    esum = NULL;
                }
            }
            if (sum) {
                s = _th_get_less_offset(env,t->v1,t->e,&u);
                _tree_print2("offset delta %s %d", _th_print_exp(s), _th_delta);
                if (s && !(u&8)) {
                    sum = _th_add_rationals(s,sum);
                } else {
                    sum = NULL;
                }
                delta = (delta || _th_delta);
                if (!_th_is_equal_term) {
                    if (_th_delta) {
                        pos_delta = 1;
                    } else {
                        neg_delta = 1;
                    }
                }
            }
            t = t->next;
        }
        _tree_print1("delta %d", delta);
        _tree_print_exp("sum", sum);
        _tree_print_exp("esum", esum);
        if (do_add) {
            if (esum) {
                nc = equality_out_of_bounds_conflicts(env,tail,conflicts,ri);
                if (nc != conflicts) {
                    //_tree_undent();
                    //_tree_undent();
                    //_tree_print0("Out of bounds conflicts eq");
                    //_tree_indent();
                    //_tree_indent();
                    conflicts = nc;
                    added_conflict = 1;
                } else if (esum->u.rational.numerator[0]==1 && esum->u.rational.numerator[1]==0) {
                    struct ve_list *neg = tail;
                    while (neg) {
                        struct ve_list *t = tail;
                        while (t != NULL) {
                            if (t==neg) {
                                if ((t->sign&1)==0) goto cont;
                            } else {
                                if ((t->sign&2)==0) goto cont;
                            }
                            t = t->next;
                        }
                        t = tail;
                        c = NULL;
                        _tree_print0("Adding inequality conflict");
                        _tree_indent();
                        while (t) {
                            //if ((t != neg && (t->sign&4)==0) || (t==neg && (t->sign&8)==0)) {
                                n = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                                n->next = c;
                                c = n;
                                n->sign = t->sign;
                                n->source = number;
                                n->count = 0;
                                n->fv = NULL;
                                if (t==neg) {
                                    n->e = _ex_intern_appl1_env(env,INTERN_NOT,t->e);
                                    if ((t->sign&2)==0) t->sign |= 32;
                                    t->sign |= 2;
                                } else {
                                    n->e = t->e;
                                    if ((t->sign&1)==0) t->sign |= 32;
                                    t->sign |= 1;
                                }
                                //_tree_print_exp("e",n->e);
                            //}
                            t = t->next;
                        }
                        _tree_undent();
                        check_tuple(env, c, "equal");
                        nc = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
                        nc->next = conflicts;
                        conflicts = nc;
                        ++conflicts_generated;
                        nc->group = c;
                        neg = neg->next;
                        added_conflict = 1;
                    }
                } else {
                    struct ve_list *t = tail;
                    while (t != NULL) {
                        if ((t->sign&2)==0) {
                            _tree_undent();
                            _tree_undent();
                            _tree_undent();
                            _tree_print0("Skipping due to sign aa");
                            _tree_indent();
                            _tree_indent();
                            _tree_indent();
                            goto cont;
                        }
                        t = t->next;
                    }
                    t = tail;
                    c = NULL;
                    _tree_print0("Adding equality conflict");
                    _tree_indent();
                    while (t) {
                        _tree_print_exp("e",t->e);
                        //if ((t->sign&4)==0) {
                            n = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                            n->next = c;
                            c = n;
                            n->sign = t->sign;
                            n->source = number;
                            n->e = t->e;
                            n->count = 0;
                            n->fv = NULL;
                            if ((t->sign&1)==0) t->sign |= 32;
                            t->sign |= 1;
                        //}
                        t = t->next;
                    }
                    _tree_undent();
                    check_tuple(env, c, "equal 2");
                    nc = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
                    nc->next = conflicts;
                    conflicts = nc;
                    nc->group = c;
                    ++conflicts_generated;
                    added_conflict = 1;
                }
            } else if (sum) {
                nc = inequality_out_of_bounds_conflicts(env,tail,conflicts,ri);
                if (nc != conflicts) {
                    added_conflict = 1;
                    conflicts = nc;
                    //_tree_undent();
                    //_tree_undent();
                    //_tree_print0("Out of bounds conflicts");
                    //_tree_indent();
                    //_tree_indent();
                } else if (_th_big_is_negative(sum->u.rational.numerator) ||
                    (sum->u.rational.numerator[0]==1 && sum->u.rational.numerator[1]==0 &&
                    !delta)) {
                    struct ve_list *t = tail;
                    while (t != NULL) {
                        if ((t->sign&2)==0) {
                            //_tree_undent();
                            //_tree_undent();
                            //_tree_undent();
                            //_tree_print0("Skipping due to sign a");
                            //_tree_indent();
                            //_tree_indent();
                            //_tree_indent();
                            goto cont;
                        }
                        t = t->next;
                    }
                    t = tail;
                    c = NULL;
                    _tree_print0("Adding greater conflict");
                    _tree_indent();
                    while (t) {
                        int u = t->sign;
                        n = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                        n->next = c;
                        c = n;
                        n->sign = t->sign;
                        n->source = number;
                        n->e = get_greater_dir(env,t->v1,t->e, &u);
                        n->count = 0;
                        n->fv = NULL;
                        if (u&8) {
                            _tree_undent();
                            _tree_undent();
                            _tree_print0("Skip greater");
                            _tree_indent();
                            goto skip_greater;
                        }
                        if (n->e->type==EXP_APPL && n->e->u.appl.functor==INTERN_NOT) {
                            if ((t->sign&2)==0) t->sign |= 32;
                            t->sign |= 2;
                        } else {
                            if ((t->sign&1)==0) t->sign |= 32;
                            t->sign |= 1;
                        }
                        _tree_print_exp("e",n->e);
                        t = t->next;
                    }
                    check_tuple(env, c, "greater");
                    _tree_undent();
                    nc = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
                    nc->next = conflicts;
                    conflicts = nc;
                    nc->group = c;
                    ++conflicts_generated;
                    added_conflict = 1;
skip_greater:;
                } else {
                    struct ve_list *t = tail;
                    while (t != NULL) {
                        if ((t->sign&2)==0) {
                            _tree_undent();
                            _tree_undent();
                            _tree_undent();
                            _tree_print0("Skipping due to sign");
                            _tree_indent();
                            _tree_indent();
                            _tree_indent();
                            goto cont;
                        }
                        t = t->next;
                    }
                    t = tail;
                    c = NULL;
                    _tree_print0("Adding less conflict");
                    _tree_indent();
                    while (t) {
                        int u = t->sign;
                        n = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                        n->next = c;
                        c = n;
                        n->sign = t->sign;
                        n->source = number;
                        _tree_print1("vertex %s", _th_intern_decode(t->v1));
                        n->e = get_less_dir(env,t->v1,t->e,&u);
                        n->count = 0;
                        n->fv = NULL;
                        if (u&8) {
                            _tree_undent();
                            _tree_undent();
                            _tree_print0("skip less");
                            _tree_indent();
                            goto skip_less;
                        }
                        if (n->e->type==EXP_APPL && n->e->u.appl.functor==INTERN_NOT) {
                            if ((t->sign&2)==0) t->sign |= 32;
                            t->sign |= 2;
                        } else {
                            if ((t->sign&1)==0) t->sign |= 32;
                            t->sign |= 1;
                        }
                        _tree_print_exp("e",n->e);
                        t = t->next;
                    }
                    check_tuple(env, c, "less");
                    _tree_undent();
                    nc = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
                    nc->next = conflicts;
                    conflicts = nc;
                    nc->group = c;
                    ++conflicts_generated;
                    added_conflict = 1;
skip_less:;
                }
            }   
            if (esum==NULL && sum && sum->u.rational.numerator[0]==1 && sum->u.rational.numerator[1]==0 &&
                pos_delta && neg_delta) {
                struct ve_list *t = tail;
                while (t != NULL) {
                    if (t->sign&1==0) {
                        _tree_undent();
                        _tree_undent();
                        _tree_undent();
                        _tree_print0("Skipping due to sign c");
                        _tree_indent();
                        _tree_indent();
                        _tree_indent();
                        goto cont;
                    }
                    t = t->next;
                }
                t = tail;
                c = NULL;
                _tree_print0("Adding greater conflict b");
                _tree_indent();
                while (t) {
                    int u = t->sign;
                    n = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                    n->next = c;
                    c = n;
                    n->sign = t->sign;
                    n->source = number;
                    n->e = get_greater_dir(env,t->v1,t->e, &u);
                    if (u&8) {
                        _tree_undent();
                        _tree_undent();
                        _tree_print0("Skip greater a");
                        _tree_indent();
                        goto skip_greater2;
                    }
                    if (n->e->type==EXP_APPL && n->e->u.appl.functor==INTERN_NOT) {
                        if (t->sign&2==0) t->sign |= 32;
                        t->sign |= 2;
                    } else {
                        if (t->sign&1==0) t->sign |= 32;
                        t->sign |= 1;
                    }
                    _tree_print_exp("e",n->e);
                    n->count = 0;
                    n->fv = NULL;
                    t = t->next;
                }
                check_tuple(env, c, "eq add 1");
                _tree_undent();
                nc = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
                nc->next = conflicts;
                conflicts = nc;
                nc->group = c;
                ++conflicts_generated;
                added_conflict = 1;
skip_greater2:;
            }
            if (esum==NULL && sum && sum->u.rational.numerator[0]==1 && sum->u.rational.numerator[1]==0 &&
                pos_delta && !neg_delta) {
                struct ve_list *t = tail;
                while (t != NULL) {
                    if ((t->sign&1)==0) {
                        _tree_undent();
                        _tree_undent();
                        _tree_undent();
                        _tree_print0("Skipping due to sign d");
                        _tree_indent();
                        _tree_indent();
                        _tree_indent();
                        goto cont;
                    }
                    t = t->next;
                }
                t = tail;
                c = NULL;
                _tree_print0("Adding greater conflict c");
                _tree_indent();
                while (t) {
                    int u = t->sign;
                    n = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                    n->next = c;
                    c = n;
                    n->sign = t->sign;
                    n->source = number;
                    n->e = get_greater_dir(env,t->v1,t->e, &u);
                    if (u&8) {
                        _tree_undent();
                        _tree_undent();
                        _tree_print0("Skip greater b");
                        _tree_indent();
                        goto skip_greater3;
                    }
                    if (n->e->type==EXP_APPL && n->e->u.appl.functor==INTERN_NOT) {
                        if ((t->sign&2)==0) t->sign |= 32;
                        t->sign |= 2;
                    } else {
                        if ((t->sign&1)==0) t->sign |= 32;
                        t->sign |= 1;
                    }
                    _tree_print_exp("e",n->e);
                    n->count = 0;
                    n->fv = NULL;
                    t = t->next;
                }
                t = tail;
                //printf("ne terms\n");
                while (t) {
                    struct _ex_intern *ne = get_ne_term(env,t->e,t->node);
                    //printf("    ne term %d %s\n", number, _th_print_exp(t->e));
                    //printf("    ne term %s\n", _th_print_exp(ne));
                    if (ne) {
                        n = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                        n->next = c;
                        n->sign = t->sign;
                        n->source = number;
                        n->e = ne;
                        nc = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
                        nc->next = conflicts;
                        conflicts = nc;
                        nc->group = n;
                        n->count = 0;
                        n->fv = NULL;
                        check_tuple(env, n, "eq add 2");
                        //add_edge_term(env,edge->node,ne->u.appl.args[0],number,group);
                    }
                    t = t->next;
                }
                added_conflict = 1;
                ++conflicts_generated;
                _tree_undent();
skip_greater3:;
            }
            if (esum==NULL && sum && sum->u.rational.numerator[0]==1 && sum->u.rational.numerator[1]==0 &&
                pos_delta && !neg_delta) {
                struct ve_list *t = tail;
                while (t != NULL) {
                    if ((t->sign&1)==0) {
                        _tree_undent();
                        _tree_undent();
                        _tree_undent();
                        _tree_print0("Skipping due to sign d");
                        _tree_indent();
                        _tree_indent();
                        _tree_indent();
                        goto cont;
                    }
                    t = t->next;
                }
                t = tail;
                c = NULL;
                _tree_print0("Adding greater conflict d");
                _tree_indent();
                while (t) {
                    int u = t->sign;
                    n = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                    n->next = c;
                    c = n;
                    n->sign = t->sign;
                    n->source = number;
                    n->count = 0;
                    n->fv = NULL;
                    n->e = get_less_dir(env,t->v1,t->e, &u);
                    if (u&8) {
                        _tree_undent();
                        _tree_undent();
                        _tree_print0("Skip less 2");
                        _tree_indent();
                        goto skip_less2;
                    }
                    if (n->e->type==EXP_APPL && n->e->u.appl.functor==INTERN_NOT) {
                        if ((t->sign&2)==0) t->sign |= 32;
                        t->sign |= 2;
                    } else {
                        if ((t->sign&1)==0) t->sign |= 32;
                        t->sign |= 1;
                    }
                    _tree_print_exp("e",n->e);
                    t = t->next;
                }
                t = tail;
                //printf("ne terms 2\n");
                while (t) {
                    struct _ex_intern *ne = get_ne_term(env,t->e,t->node);
                    //printf("    ne term %d %s\n", number, _th_print_exp(t->e));
                    //printf("    ne term %s\n", _th_print_exp(ne));
                    if (ne) {
                        n = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                        n->next = c;
                        n->sign = t->sign;
                        n->source = number;
                        n->e = ne;
                        n->count = 0;
                        n->fv = NULL;
                        nc = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
                        nc->next = conflicts;
                        conflicts = nc;
                        nc->group = n;
                        //add_edge_term(env,edge->node,ne->u.appl.args[0],number,group);
                        check_tuple(env, n, "eq add 3");
                    }
                    t = t->next;
                }
                added_conflict = 1;
                ++conflicts_generated;
                _tree_undent();
skip_less2:;
            }
        }
cont:
        _tree_undent();
    } else {
        struct signed_list *l = all_edges->node->terms;
        while (l) {
            //if (l->source >= number || l->source==0) {
                struct ve_list *v = (struct ve_list *)ALLOCA(sizeof(struct ve_list));
                v->next = tail;
                v->e = l->e;
                v->sign = l->sign;
                v->v1 = all_edges->var;
                v->node = all_edges->node;
                if (all_edges->node->v1==v->v1) {
                    v->v2 = all_edges->node->v2;
                } else {
                    v->v2 = all_edges->node->v1;
                }
                conflicts = generate_cycle_conflicts(env,all_edges->next,v,number,conflicts,ri);
                if (conflicts_generated > CONFLICT_LIMIT) return conflicts;
                l->sign = v->sign;
            //} else {
            //    _tree_print3("Skipping term %s %d %d", _th_print_exp(l->e), l->source, number);
            //}
            l = l->next;
        }
    }
    return conflicts;
}

static struct group_list *collect_cycle_conflicts(struct env *env, struct cycles *cycles, struct group_list *conflicts, struct group_list *group, struct range_info *ri,int count)
{
    struct cycles *c;
    struct edge_list *edge;
    struct signed_list *s;
    added_conflict = 0;

    if (add_implication_edges(env,cycles,group,ri,count)) return NULL;
    
    //_tree_print("Here1\n");

    added_conflict = 1;
    c = cycles;
    while (c) {
        edge = c->edges;
        while (edge) {
            s = edge->node->terms;
            while (s) {
                s->sign |= 32;
                s = s->next;
            }
            edge = edge->next;
        }
        c = c->next;
    }
    while (added_conflict) {
        _tree_print0("Add edge round");
        _tree_indent();
        added_conflict = 0;
        c = cycles;
        while (c) {
            edge = c->edges;
            while (edge) {
                s = edge->node->terms;
                while (s) {
                    s->sign |= 64;
                    s = s->next;
                }
                edge = edge->next;
            }
            c = c->next;
        }
        c = cycles;
        while (c) {
            edge = c->edges;
            while (edge) {
                s = edge->node->terms;
                while (s) {
                    if (s->sign&64) {
                        if (s->sign&32) {
                            s->sign = (s->sign&15)+16;
                        } else {
                            s->sign = (s->sign&15);
                        }
                    }
                    s = s->next;
                }
                edge = edge->next;
            }
            c = c->next;
        }
        c = cycles;
        while (c) {
#ifndef FAST
            struct edge_list *edge = c->edges;
            _tree_print5("Processing cycle %s %s %s %d %d", _th_intern_decode(c->edges->var), _th_intern_decode(c->edges->next->var), _th_intern_decode(c->edges->next->next->var), c->edges->next->next->next, c->number);
            _tree_indent();
            _tree_print0("Cycle");
            _tree_indent();
            while (edge) {
				struct signed_list *n = edge->node->terms;
                _tree_print2("Vertex %s %s", _th_intern_decode(edge->node->v1), _th_intern_decode(edge->node->v2));
				_tree_indent();
				while (n) {
					_tree_print_exp("n", n->e);
					n = n->next;
				}
				_tree_undent();
                edge = edge->next;
            }
            _tree_undent();
#endif
            conflicts_generated = 0;
            conflicts = generate_cycle_conflicts(env,c->edges,NULL,c->number,conflicts,ri);
            if (conflicts_generated > CONFLICT_LIMIT) {
                _tree_undent();
                return NULL;
            }
            c = c->next;
            _tree_undent();
            _tree_print1("Conflicts %d", conflicts_generated);
        }
        _tree_undent();
    }
    return conflicts;
}

static struct _ex_intern *sub_rationals(struct _ex_intern *r1, struct _ex_intern *r2)
{
    unsigned *tmp1, *tmp2, *accumulate;

    if (r1->u.rational.denominator[0]==1 && r1->u.rational.denominator[1]==1 &&
        r2->u.rational.denominator[0]==1 && r2->u.rational.denominator[1]==1) {
        return _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_big_sub(r1->u.rational.numerator,r2->u.rational.numerator)),r1->u.rational.denominator);
    } else {
		printf("sub_rationals grouping\n");
        tmp1 = r1->u.rational.numerator;
        tmp2 = r1->u.rational.denominator;
        accumulate = _th_big_gcd(r1->u.rational.denominator,r2->u.rational.denominator);
        tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_divide(_th_big_multiply(r1->u.rational.numerator,r2->u.rational.denominator),accumulate));
        tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_sub(tmp1,_th_big_copy(REWRITE_SPACE,_th_big_divide(_th_big_multiply(r2->u.rational.numerator,r1->u.rational.denominator),accumulate))));
        tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_divide(_th_big_multiply(r1->u.rational.denominator,r2->u.rational.denominator),accumulate));
        printf("end sub_rationals grouping\n");
        return _ex_intern_rational(tmp1,tmp2);
    }
}

static struct range_info *small_world_range_info(struct env *env, struct signed_list *terms)
{
    int count, c, i, j;
    unsigned *fv, *fvars;
    struct signed_list *t;
    unsigned v;
    struct range_info *ret, *r;
    struct _ex_intern *min, *max;

    count = 0;
    t = terms;
    while (t) {
        fv = _th_get_free_vars(t->e,&c);
        count += c;
        t = t->next;
    }
    fvars = (unsigned *)ALLOCA(count * sizeof(unsigned));

    count = 0;
    t = terms;
    while (t) {
        fv = _th_get_free_vars(t->e,&c);
        for (i = 0; i < c; ++i) {
            for (j = 0; j < count; ++j) {
                if (fv[i]==fvars[j]) goto cont;
            }
            fvars[count++] = fv[i];
cont:;
        }
        t = t->next;
    }

    for (i = 0; i < count; ++i) {
        //_tree_print1("Checking var %s", _th_intern_decode(fvars[i]));
        //_tree_indent();
        for (j = 0; j < count; ++j) {
            fv[j] = 0;
        }
		min = max = _ex_intern_small_rational(0,1);
        t = terms;
        while (t) {
            if (_th_extract_relationship(env,t->e)) {
				if (_th_right->u.var==fvars[i]) {
                    _th_diff = _ex_intern_rational(
                        _th_big_copy(REWRITE_SPACE,_th_complement(_th_diff->u.rational.numerator)),
                        _th_diff->u.rational.denominator);
					if (_th_rational_less(_th_diff,min)) min = _th_diff;
					if (_th_rational_less(max,_th_diff)) max = _th_diff;
				} else if (_th_left->u.var==fvars[i]) {
					if (_th_rational_less(_th_diff,min)) min = _th_diff;
					if (_th_rational_less(max,_th_diff)) max = _th_diff;
 				} else if (_th_diff->u.rational.numerator[0] != 1 || _th_diff->u.rational.numerator[1] != 0) goto cont2;
            }
            t =  t->next;
        }
        ret = NULL;
        for (j = 0; j < count; ++j) {
            if (i != j) {
                r = (struct range_info *)_th_alloc(REWRITE_SPACE,sizeof(struct range_info));
                r->next = ret;
                ret = r;
                r->var = fvars[j];
                r->range = sub_rationals(max,min);
				r->high = max;
				r->low = min;
            }
        }
        //_tree_undent();
        range_var = _ex_intern_var(fvars[i]);
        return ret;
cont2:;
        //_tree_undent();
    }
    return NULL;
}

static struct range_info *collect_range_info(struct env *env, struct signed_list *terms)
{
    int count, c, i, j;
    unsigned *fv, *fvars;
    struct _ex_intern **min, **max;
    struct signed_list *t;
    unsigned v;
    struct range_info *ret, *r;

    count = 0;
    t = terms;
    while (t) {
        fv = _th_get_free_vars(t->e,&c);
        count += c;
        t = t->next;
    }
    fvars = (unsigned *)ALLOCA(count * sizeof(unsigned));

    count = 0;
    t = terms;
    while (t) {
        fv = _th_get_free_vars(t->e,&c);
        for (i = 0; i < c; ++i) {
            for (j = 0; j < count; ++j) {
                if (fv[i]==fvars[j]) goto cont;
            }
            fvars[count++] = fv[i];
cont:;
        }
        t = t->next;
    }

    fv = (unsigned *)ALLOCA(count * sizeof(unsigned));
    min = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
    max = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
    for (i = 0; i < count; ++i) {
        //_tree_print1("Checking var %s", _th_intern_decode(fvars[i]));
        //_tree_indent();
        for (j = 0; j < count; ++j) {
            fv[j] = 0;
        }
        t = terms;
        while (t) {
            //_tree_print2("Checking term %d %s", t->sign, _th_print_exp(t->e));
            if (t->sign & 12) {
                if (_th_extract_relationship(env,t->e)) {
                    if (t->sign & 4) {
                        //if (_th_is_equal_term && (_th_left->u.var==fvars[i] || _th_right->u.var==fvars[i])) {
                        //    v = _th_right->u.var;
                        //    for (j = 0; j < count; ++j) {
                        //        if (fvars[j]==v) break;
                        //    }
                        //    fv[j] |= 3;
                        //    min[j] = max[j] = _th_diff;
                        //    //_tree_print1("both for %s", _th_intern_decode(fvars[j]));
                        //}
                        if (!_th_is_equal_term && _th_left->u.var==fvars[i]) {
                            v = _th_right->u.var;
                            for (j = 0; j < count; ++j) {
                                if (fvars[j]==v) break;
                            }
                            fv[j] |= 1;
                            min[j] = _th_diff;
                            //_tree_print1("min 1 for %s", _th_intern_decode(fvars[j]));
                        }
                        if (!_th_is_equal_term && _th_right->u.var==fvars[i]) {
                            v = _th_left->u.var;
                            for (j = 0; j < count; ++j) {
                                if (fvars[j]==v) break;
                            }
                            fv[j] |= 2;
                            max[j] = _ex_intern_rational(
                                         _th_big_copy(REWRITE_SPACE,_th_complement(_th_diff->u.rational.numerator)),
                                         _th_diff->u.rational.denominator);
                            //_tree_print1("max 1 for %s", _th_intern_decode(fvars[j]));
                        }
                    }
                    if (t->sign & 8) {
                        if (!_th_is_equal_term && _th_left->u.var==fvars[i]) {
                            v = _th_right->u.var;
                            for (j = 0; j < count; ++j) {
                                if (fvars[j]==v) break;
                            }
                            fv[j] |= 2;
                            max[j] = _th_diff;
                            //_tree_print1("max 2 for %s", _th_intern_decode(fvars[j]));
                        }
                        if (!_th_is_equal_term && _th_right->u.var==fvars[i]) {
                            v = _th_left->u.var;
                            for (j = 0; j < count; ++j) {
                                if (fvars[j]==v) break;
                            }
                            fv[j] |= 1;
                            min[j] = _ex_intern_rational(
                                         _th_big_copy(REWRITE_SPACE,_th_complement(_th_diff->u.rational.numerator)),
                                         _th_diff->u.rational.denominator);
                            //_tree_print1("min 2 for %s", _th_intern_decode(fvars[j]));
                        }
                    }
                }
            }
            t =  t->next;
        }
        for (j = 0; j < count; ++j) {
            if (fv[j] != 3 && j != i) {
                //_tree_print2("Missed %d %s", fv[j], _th_intern_decode(fvars[j]));
                goto cont2;
            }
        }
        ret = NULL;
        for (j = 0; j < count; ++j) {
            if (i != j) {
                r = (struct range_info *)_th_alloc(REWRITE_SPACE,sizeof(struct range_info));
                r->next = ret;
                ret = r;
                r->var = fvars[j];
                r->high = r->range = sub_rationals(max[j],min[j]);
				r->low = _ex_intern_small_rational(0,1);
            }
        }
        //_tree_undent();
        range_var = _ex_intern_var(fvars[i]);
        return ret;
cont2:;
        //_tree_undent();
    }
    return NULL;
}

static void build_conflict_set(struct env *env, struct group_list *group, struct parent_list *unates)
{
    struct group_list *gv;
    struct group_list *gvars;
    struct learn_info *info = _th_new_learn_info(env);
    struct group_list *conflicts = NULL;
    struct signed_list *g;
    struct cycles *cycles, *c;
    struct range_info *ri, *rii;
    int count = 0, c1;
    static struct _ex_intern *zero = NULL, *one = NULL;

#ifndef FAST
    struct node_list *nodes;
#endif
    g = group->group;
    while (g) {
        ++count;
        g = g->next;
    }
#ifndef FAST
    _tree_print1("Processing group %d", count);
    //if (count > 100) {
    //    group->can_subout = 0;
    //    return;
    //}
    _tree_indent();
    g = group->group;
    _tree_print0("Terms");
    _tree_indent();
    while (g) {
        _tree_print2("g %s %d", _th_print_exp(g->e), g->sign);
        g = g->next;
    }
    _tree_undent();
#endif

    g = group->group;
    while (g) {
        if (!_th_extract_relationship(env,g->e)) {
            _tree_undent();
            _tree_print_exp("Not difference logic", g->e);
            group->can_subout = 0;
            return;
        }
        g = g->next;
    }

    ri = collect_range_info(env,group->group);
	if (ri==NULL) {
		ri = small_world_range_info(env,group->group);
	}
    if (zero==NULL) {
        zero = _ex_intern_small_rational(0,1);
        one = _ex_intern_small_rational(1,1);
    }
	if (ri && _th_is_integer_logic()) {
        rii = ri;
        while (rii) {
            struct _ex_intern *term, *pos;
            pos = rii->low;
            _tree_print_exp("Range var is", range_var);
            while (!_th_rational_less(rii->high,pos)) {
                if (pos==zero) {
                    term = _ex_intern_equal(env,_ex_real,_ex_intern_var(rii->var),range_var);
                } else {
                    term = _ex_intern_appl2_env(env,INTERN_RAT_LESS,_ex_intern_var(rii->var),_ex_intern_appl2_env(env,INTERN_RAT_PLUS,pos,range_var));
                }
                term = _th_nc_rewrite(env,term);
                _tree_print_exp("Adding term", term);
                g = group->group;
                while (g) {
                    if (g->e==term) goto skip;
                    g = g->next;
                }
                _tree_print0("Actually adding");
                g = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                g->next = group->group;
                group->group = g;
                g->source = 1;
                g->e = term;
                g->sign = 2;
                g->fv = NULL;
                g->count = 0;
skip:
                pos = _th_add_rationals(pos,one);
            }
            rii = rii->next;
        }
    }
	gv = group_by_vars(env, group->group);
    gvars = gv;
#ifndef FAST
    _tree_print0("Range info");
    _tree_indent();
    rii = ri;
    while (rii) {
        _tree_print2("range %s %s", _th_intern_decode(rii->var), _th_print_exp(rii->range));
        rii = rii->next;
    }
    _tree_undent();
#endif

    _th_add_unate_tail(env,info,unates);

    g = group->group;
    limit_counter = _th_do_grouping;
    if (limit_counter < 0) {
        _tree_undent();
        _tree_print0("Failed grouping");
        group->can_subout = 0;
        return;
    }

    group->can_subout = 1;
    cycles = collect_all_cycles(env,gvars);
    group->is_trivial = (cycles==NULL);
    c1 = 0;
    c = cycles;
    while (c) {
        ++c1;
        c = c->next;
    }
    group->cycle_count = c1;
    if (_th_block_bigs && cycles) {
        group->can_subout = 0;
        _tree_undent();
        return;
    }
    conflicts = collect_cycle_conflicts(env,cycles,conflicts,group,ri,count);
    if (conflicts==NULL && cycles != NULL) {
        group->can_subout = 0;
        _tree_print0("Too many implication edges generated");
        _tree_undent();
        return;
    }
    if (ri && _th_is_difference_logic())
    {
        rii = ri;
        while (rii) {
            struct _ex_intern *term, *pos;
            struct group_list *conf = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
            conf->next = conflicts;
            //printf("Adding conflict for %s\n", _th_intern_decode(rii->var));
            //printf("    range %s\n", _th_print_exp(ri->range));
            conflicts = conf;
            conf->group = NULL;
            pos = zero;
            while (!_th_rational_less(rii->range,pos)) {
                if (pos==zero) {
                    term = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_equal(env,_ex_real,_ex_intern_var(rii->var),range_var));
                } else {
                    term = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_equal(env,_ex_real,_ex_intern_var(rii->var),_ex_intern_appl2_env(env,INTERN_RAT_PLUS,pos,range_var)));
                }
                term = _th_nc_rewrite(env,term);
                //printf("        %s\n", _th_print_exp(term));
                g = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                g->next = conf->group;
                conf->group = g;
                g->source = 1;
                g->e = term;
                g->sign = 2;
                g->fv = NULL;
                g->count = 0;
                pos = _th_add_rationals(pos,one);
            }
            rii = rii->next;
        }
    }
    while (gv) {
        gv->group->source = 1;
        //limit_counter = _th_do_grouping;
        //conflicts = search_common_var_conflicts(env, info, gv->group, conflicts);
        //if (limit_counter < 0) {
        //    _tree_print0("Too many nodes");
        //    _tree_undent();
        //    group->can_subout = 0;
        //    return;
        //}
        gv = gv->next;
    }

    gv = conflicts;
    count = 0;
    while (gv) {
        ++count;
        gv = gv->next;
    }
    _tree_print1("Non-pair conflicts %d", count);

    if (cycles==NULL) {
        gv = gvars;
        while (gv) {
            conflicts = get_diff_common_var_conflicts(env, gv->group, conflicts);
            gv = gv->next;
        }
    } else {
        c = cycles;
        while (c) {
            struct edge_list *e = c->edges;
            while (e) {
                if (e->node->terms->source) {
                    e->node->terms->source = 0;
                    limit_counter = _th_do_grouping;
                    conflicts = get_diff_common_var_conflicts(env, e->node->terms, conflicts);
                    if (limit_counter < 0) {
                        _tree_print0("Too many nodes");
                        _tree_undent();
                        group->can_subout = 0;
                        return;
                    }
                }
                e = e->next;
            }
            c = c->next;
        }
    }
#ifndef FAST
    _tree_print0("Cycle set");
    _tree_indent();
    while (cycles != NULL) {
        _tree_print0("Cycle");
        _tree_indent();
        nodes = cycles->path;
        while (nodes) {
            _tree_print1("Var %s", _th_intern_decode(nodes->var));
            g = nodes->edge;
            _tree_indent();
            while (g) {
                _tree_print2("term %d %s", g->sign, _th_print_exp(g->e));
                g = g->next;
            }
            _tree_undent();
            nodes = nodes->next;
        }
        _tree_undent();
        cycles = cycles->next;
    }
    _tree_undent();

    gv = conflicts;
    _tree_print0("Final conflict set");
    _tree_indent();
    count = 0;
    while (gv) {
        check_tuple(env,gv->group,"final");
        _tree_print0("Conflict set");
        _tree_indent();
        g = gv->group;
        while (g) {
            _tree_print_exp("c", g->e);
            g = g->next;
        }
        _tree_undent();
#ifdef CHECK_CONFLICTS
        g = gv->group;
        while (g) {
            struct _ex_intern *v = _th_yices_ce_value(env,g->e);
            if (v==_ex_false) goto not_bad;
            if (v != _ex_true) {
                printf("No value for %s\n", _th_print_exp(g->e));
                exit(1);
            }
            g = g->next;
        }
        g = gv->group;
        printf("Bad conflict\n");
        while (g != NULL) {
            printf("    %s\n", _th_print_exp(g->e));
            g = g->next;
        }
not_bad:
#endif
#ifdef CHECK_CONFLICTSB
        _th_derive_push(env);
        g = gv->group;
        while (g) {
            if (_th_assert_predicate(env,_th_simp(env,_th_nc_rewrite(env,g->e)))) goto not_bad;
            g = g->next;
        }
        g = gv->group;
        printf("Bad conflict\n");
        while (g != NULL) {
            printf("    %s\n", _th_print_exp(g->e));
            g = g->next;
        }
not_bad:
        _th_derive_pop(env);
#endif
        ++count;
        gv = gv->next;
    }
    _tree_undent();
    _tree_print1("Number of conflicts %d", count);
    _tree_print1("Number of edges %d", edges_added);
#endif
    group->edges_added = edges_added;
    group->conflict_count = count;
    _tree_undent();
    group->conflicts = conflicts;
}

static int var_pos = 0;

static unsigned new_var(struct env *env, struct learn_info *info, struct _ex_intern *type)
{
    char name[20];
    unsigned v;

try_again:
    sprintf(name, "abs%d", ++var_pos);
    v = _th_intern(name);

    if (_th_get_var_type(env,v)) goto try_again;
    _th_set_var_type(env,v,type);
	_th_set_var_type(_th_learn_get_env(info),v,type);

    return v;
}

//static int se = 0;
//static int subout = 0;

static struct _ex_intern *sub_terms(struct env *env, struct _ex_intern *e)
{
    int i;
    struct _ex_intern **args, *r;

    //_tree_print_exp("Sub term", e);
    if (e->user2) {
        //_tree_print_exp("res", e->user2);
        //if (e->user2->type!=EXP_VAR && subout) {
        //    fprintf(stderr, "Sub error %s\n", _th_print_exp(e));
        //    fprintf(stderr, "    user2 %s\n", _th_print_exp(e->user2));
        //    se = 1;
        //}
        return e->user2;
    }

    if (e->type==EXP_APPL) {
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
        //_tree_indent();
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = sub_terms(env,e->u.appl.args[i]);
        }
        //_tree_undent();
        r = _ex_intern_appl_equal_env(env,e->u.appl.functor,e->u.appl.count,args,e->type_inst);
        //_tree_print_exp("res c", r);
        if (r->user2) {
            fprintf(stderr, "Error term %s has sub\n", _th_print_exp(r));
            fprintf(stderr, "    orig: %s\n", _th_print_exp(e));
            exit(1);
        }
        //if (se) {
        //    fprintf(stderr,"e = %s\n", _th_print_exp(e));
        //    fprintf(stderr,"r = %s\n", _th_print_exp(r));
        //    if (se==2) exit(1);
        //    ++se;
        //}
        e->next_cache = trail;
        trail = e;
        e->user2 = r;
        return r;
    }

    //_tree_print_exp("res b", e);
    return e;
}

//#define CHECK_CE

#ifdef CHECK_CE
static void read_signs(struct signed_list *group)
{
    FILE *f = fopen("assign","r");
    char line[200];
    unsigned tok;
    struct signed_list *g;

    if (f==NULL) {
        fprintf(stderr, "Failed to open 'assign'\n");
        exit(1);
    }
    g = group;
    while (g) {
        g->sign = 0;
        g = g->next;
    }
    while (!feof(f)) {
        line[0] = 0;
        fgets(line,199,f);
        line[strlen(line)-1] = 0;
        tok = _th_intern(line);
        g = group;
        while (g) {
            if (g->e->user2->u.var==tok) {
                g->sign = 1;
            }
            g = g->next;
        }
    }
}

static void check_ce(struct env *env, struct signed_list *group)
{
    struct signed_list *g, *p, *flist;

    g = group;
    flist = NULL;

    _th_derive_push(env);
    while (g) {
        if (g->sign) {
            if (_th_deny_predicate(env,g->e)) {
                fprintf(stderr, "Group failure %d %s\n", g->sign, _th_print_exp(g->e));
                _th_derive_pop(env);
                goto find_failure;
            }
        } else {
            if (_th_assert_predicate(env,g->e)) {
                fprintf(stderr, "Group failure %d %s\n", g->sign, _th_print_exp(g->e));
                _th_derive_pop(env);
                goto find_failure;
            }
        }
        g = g->next;
    }
    _th_derive_pop(env);
    return;
find_failure:
    p = (struct signed_list *)ALLOCA(sizeof(struct signed_list));
    p->next = flist;
    p->e = g->e;
    p->sign = g->sign;
    flist = p;

    _th_derive_push(env);
    while (p) {
        if (p->sign) {
            if (_th_deny_predicate(env,p->e)) {
                goto done_failure;
            }
        } else {
            if (_th_assert_predicate(env,p->e)) {
                goto done_failure;
            }
        }
        p = p->next;
    }

    g = group;
    while (g) {
        if (g->sign) {
            if (_th_deny_predicate(env,g->e)) {
                fprintf(stderr, "    term %d %s\n", g->sign, _th_print_exp(g->e));
                _th_derive_pop(env);
                goto find_failure;
            }
        } else {
            if (_th_assert_predicate(env,g->e)) {
                fprintf(stderr, "    term %d %s\n", g->sign, _th_print_exp(g->e));
                _th_derive_pop(env);
                goto find_failure;
            }
        }
        g = g->next;
    }
    _th_derive_pop(env);
    fprintf(stderr, "Double failure!!!\n");
    exit(1);
done_failure:
    while (flist) {
        fprintf(stderr, "Term: %d %s\n", flist->sign, _th_print_exp(flist->e));
        flist = flist->next;
    }
    exit(1);
}
#endif

static struct _ex_intern *c1 = NULL, *c2 = NULL;

void has_c1c2(struct _ex_intern *e, char *n)
{
    int i;
    int has_c1 = 0;
    int has_c2 = 0;

    if (c1==NULL || c2==NULL) return;

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_OR) {
        for (i = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]==c1) has_c1 = 1;
            if (e->u.appl.args[i]==c2) has_c2 = 1;
        }
    }
    if (!has_c1) {
        fprintf(stderr, "c1 gone %s\n", n);
        exit(1);
    }
    if (!has_c2) {
        fprintf(stderr, "c2 gone %s\n", n);
        exit(1);
    }
}

static struct _ex_intern *subout_group(struct env *env, struct _ex_intern *e, struct signed_list *group, struct group_list *conflicts, struct parent_list *unates, struct learn_info *info)
{
    struct signed_list *a;
    struct group_list *c;
    int j, count;
    struct _ex_intern **args, **args2;
//    char *emark;

    //subout = 1;

#ifdef XX
    a = group;
    count = 0;
    while (a) {
        ++count;
        a = a->next;
    }

    if (count > _th_do_grouping) {
#ifndef FAST
        _tree_print0("Group too big");
        _tree_indent();
        a = group;
        while (a) {
            _tree_print_exp("g", a->e);
            a = a->next;
        }
        _tree_undent();
#endif
        return e;
    }

    emark = _th_alloc_mark(_th_get_space(env));
    _th_derive_push(env);
    conflicts = collect_conflicts(env,group,NULL,NULL);
    _th_derive_pop(env);
    _th_alloc_release(_th_get_space(env),emark);

#endif

    _tree_print0("Breaking group");
    _tree_indent();
#ifdef CHECK_CE
    read_signs(group);
#endif

    count = 0;
    c = conflicts;
    while (c) {
        ++count;
        c = c->next;
    }

    args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (count + 1));
    args2[0] = e;
    j = 1;
    c = conflicts;
    count = 0;
    while (c) {
        int k;
        a = c->group;
        k = 0;
        while (a) {
            ++k;
            a = a->next;
        }
        if (k > count) count = k;
        c = c->next;
    }
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
    c = conflicts;
    //_tree_print("Here1");
    //_tree_indent();

    _tree_print0("Group");
    _tree_indent();
    a = group;
    //printf("Group\n");
    while (a) {
        //int c;
        //unsigned *fv = _th_get_free_vars(a->e,&c);
        //if ((fv[0]==_th_intern("x_116") || fv[0]==_th_intern("x_117") ||
        //    fv[0]==_th_intern("x_118") || fv[0]==_th_intern("x_134")) &&
        //    a->e->u.appl.functor==INTERN_RAT_LESS && a->e->u.appl.args[0]->type==EXP_VAR &&
        //    a->e->u.appl.args[1]->type==EXP_VAR) {
        //    _tree_print0("***************** LOOK HERE ***********************");
        //}
        a->e->user2 = _ex_intern_var(new_var(env,info,_ex_bool));
        //printf("    %s is ", _th_print_exp(a->e));
        //printf("    %s\n", _th_print_exp(a->e->user2));
        //if (a->e->type==EXP_APPL && a->e->u.appl.functor==INTERN_EQUAL) {
        //    a->e->u.appl.args[0]->user2 = _ex_true;
        //    a->e->u.appl.args[1]->user2 = _ex_true;
        //}
        _tree_print2("%s => %s", _th_intern_decode(a->e->user2->u.var), _th_print_exp(a->e));
        a = a->next;
    }
    _tree_undent();
    trail = NULL;

    while (c) {
        int k;
        struct _ex_intern *t;
        a = c->group;
        count = 0;
        //check_tuple(env,c->group,"subout");
        //_tree_print("place a");
        while (a) {
            ++count;
            a = a->next;
        }
        //_tree_print0("Processing b");
        a = c->group;
        count = 0;
        //_tree_print("place b");
        while (a) {
            args[count++] = a->e;
            a = a->next;
        }
        //_tree_print("place c");
        t = _ex_intern_appl_env(env,INTERN_AND,count,args);
        //_tree_print("place d");
        for (k = 0; k < j; ++k) {
            if (args2[k]==t) goto skip;
        }
        //_tree_print("place e");
        _th_transfer_to_learn(env,info,unates,sub_terms(env,t));
        //args2[j] = t;
        //if (check_for_term(t)) _tree_print2("Blocked tuple %d %s", j, _th_print_exp(t));
        //if (j==6976 && c1==NULL) c1=t;
        //if (j==7015 && c2==NULL) c2=t;
        //++j;
        //_tree_print("place f");
skip:
        c = c->next;
    }
    //_tree_indent();
    //_tree_print("Here2");

    //e = _th_flatten_top(env,_ex_intern_appl_env(env,INTERN_OR,j,args2));
    //has_c1c2(e, "jb");

    //_tree_print_exp("c1", c1);
    //_tree_print_exp("c2", c2);
    //if (c1) c1 = sub_terms(env,c1);
    //if (c2) c2 = sub_terms(env,c2);
    //_tree_print_exp("c1 after", c1);
    //_tree_print_exp("c2 after", c2);

    e = sub_terms(env,e);

    while (unates) {
        if (unates->split) {
            if (unates->split->user2) {
                unates->split = unates->split->user2;
            } else if (unates->split->type==EXP_APPL && unates->split->u.appl.functor==INTERN_NOT &&
                unates->split->u.appl.args[0]->user2) {
                unates->split = _ex_intern_appl1_env(env,INTERN_NOT,unates->split->u.appl.args[0]->user2);
            }
        }
        unates = unates->next;
    }
    //has_c1c2(e, "ja");

    _th_abstract_tuples(env,info);

    a = group;
    while (a) {
        a->e->user2 = 0;
        //if (a->e->type==EXP_APPL && a->e->u.appl.functor==INTERN_EQUAL) {
        //    a->e->u.appl.args[0]->user2 = 0;
        //    a->e->u.appl.args[1]->user2 = 0;
        //}
        a = a->next;
    }
    while (trail) {
        trail->user2 = NULL;
        trail = trail->next_cache;
    }

    _tree_print_exp("result", e);
    _tree_undent();

#ifdef CHECK_CE
    check_ce(env, group);
#endif

    //subout = 0;

    return e;
}

static struct group_list *collect_groups(struct env *env, struct _ex_intern *ue, struct _ex_intern *e, unsigned exclude)
{
    unsigned *fv;
    int count, i;
    struct signed_list *a, *n;
    struct group_list *g, *ng;

    fv = _th_get_free_vars(ue,&count);

    for (i = 0; i < count; ++i) {
        _th_intern_set_data2(fv[i],0);
    }

    a = terms;
    while (a) {
        fv = _th_get_free_vars(a->e,&count);
        for (i = 0; i < count; ++i) {
            n = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
            n->next = (struct signed_list *)_th_intern_get_data2(fv[i]);
            n->e = a->e;
            n->sign = a->sign;
            n->source = a->source;
            n->count = 0;
            n->fv = NULL;
            _th_intern_set_data2(fv[i],(unsigned)n);
        }
        a = a->next;
    }

    fv = _th_get_free_vars(ue,&count);

    a = terms;
    while (a) {
        a->e->user2 = a->e;
        a = a->next;
    }

    //printf("Here1 %d %d\n", collect, count);
    //fflush(stdout);

    for (i = 0; i < count; ++i) {
        struct _ex_intern *t1, *t2;
        if (fv[i]==exclude) goto cont;
        a = (struct signed_list *)_th_intern_get_data2(fv[i]);
        //printf("Processing %s\n", _th_intern_decode(fv[i]));
        while (a && a->next) {
            t1 = a->e;
            t2 = a->next->e;
            while (t1->user2 != t1) t1 = t1->user2;
            while (t2->user2 != t2) {
                t2 = t2->user2;
            }
            if (t1 < t2) {
                t2->user2 = t1;
            } else if (t2 < t1) {
                t1->user2 = t2;
            }
            a = a->next;
        }
cont:
        _th_intern_set_data2(fv[i],0);
    }

    a = terms;
    g = NULL;
    while (a) {
        struct _ex_intern *t = a->e;
        while (t->user2 != t) {
            t = t->user2;
        }
        ng = g;
        while (ng) {
            if (ng->e==t) break;
            ng = ng->next;
        }
        if (ng==NULL) {
            ng = (struct group_list *)_th_alloc(REWRITE_SPACE,sizeof(struct group_list));
            ng->next = g;
            g = ng;
            ng->e = t;
            ng->group = NULL;
        }
        n = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
        n->next = ng->group;
        ng->group = n;
        n->e = a->e;
        n->sign = a->sign;
        n->source = a->source;
        n->count = 0;
        n->fv = NULL;

        a = a->next;
    }
    a = terms;
    while (a) {
        a->e->user2 = NULL;
        a = a->next;
    }

    return g;
}

static unsigned *ue_fv = NULL;
static int count_groups(struct env *env, struct _ex_intern *ue, unsigned exclude)
{
    unsigned *fv;
    int count, i;
    struct signed_list *a;
    int union_count = 0, s;
    unsigned p, spos;
    static int ue_count;

    if (ue_fv==NULL) {
        fv = _th_get_free_vars(ue,&count);
        ue_count = count;
        ue_fv = (unsigned *)_th_alloc(REWRITE_SPACE,sizeof(unsigned) * ue_count);
        for (i = 0; i < count; ++i) {
            ue_fv[i] = fv[i];
        }
    }
    fv = ue_fv;
    count = ue_count;

    for (i = 0; i < count; ++i) {
        _th_intern_set_data2(fv[i],0);
    }

    a = terms;
    while (a) {
        unsigned pos, pos2;
        if (a->fv) {
            fv = a->fv;
            count = a->count;
        } else {
            fv = _th_get_free_vars(a->e,&count);
            a->count = count;
            a->fv = (unsigned *)_th_alloc(REWRITE_SPACE,sizeof(unsigned) * count);
            for (i = 0; i < count; ++i) {
                a->fv[i] = fv[i];
            }
        }
        pos = fv[0];
        s = 1;
        if (pos==exclude) {
            s = 2;
            pos = fv[1];
        }
        spos = pos;
		p = _th_intern_get_data2(pos);
        while (p) {
            pos = p;
            p = _th_intern_get_data2(pos);
        }
		p = _th_intern_get_data2(spos);
		if (p) _th_intern_set_data2(spos,pos);
        while (p) {
            spos = p;
            p = _th_intern_get_data2(spos);
			if (p) _th_intern_set_data2(spos,pos);
        }
        for (i = s; i < count; ++i) {
            if (fv[i] != exclude) {
                pos2 = fv[i];
				spos = pos2;
                p = _th_intern_get_data2(pos2);
                while (p) {
                    pos2 = p;
                    p = _th_intern_get_data2(pos2);
                }
                if (pos != pos2) {
                    ++union_count;
                    pos2 = fv[i];
                    p = _th_intern_get_data2(pos2);
                    _th_intern_set_data2(pos2,pos);
                    while (p) {
                        pos2 = p;
                        p = _th_intern_get_data2(pos2);
                        _th_intern_set_data2(pos2,pos);
                    }
				} else {
					p = _th_intern_get_data2(spos);
					if (p) _th_intern_set_data2(spos,pos2);
					while (p) {
						spos = p;
						p = _th_intern_get_data2(spos);
						if (p) _th_intern_set_data2(spos,pos2);
					}
				}
            }
        }
        a = a->next;
    }

    fv = ue_fv;
    count = ue_count;

    for (i = 0; i < count; ++i) {
        _th_intern_set_data2(fv[i],0);
    }

    return union_count;
}

int _th_print_grouping_data = 0;

/*#define HACK_OUT*/

struct _ex_intern *_th_simplify_groupings(struct env *env, struct _ex_intern *e, struct parent_list *unates, struct learn_info *info)
{
    struct group_list *g, *gr;
    char *rmark;
    struct signed_list *t;
    int te = 0, tc = 0;
    int gg = 0, bg = 0, tg = 0;
    int tcyc = 0;
    struct _ex_intern *ue = e, *f;
    struct parent_list *u = unates;
#ifdef HACK_OUT
	int hack_out = 10;
#endif

    _tree_print_exp("Encoding groupings", e);
    _tree_indent();

    rmark = _th_alloc_mark(_th_get_space(env));
    _th_derive_push(env);

    //printf("Here0\n");
    //fflush(stdout);

    terms = NULL;
    trail = _ex_true;
    _ex_true->user2 = NULL;

    collect_terms(env,e,1);

    while (trail) {
        struct _ex_intern *t = trail->user2;
        trail->user2 = NULL;
        trail = t;
    }

    f = _th_get_first_neg_tuple(info);
    while (f) {
        if (f->type==EXP_APPL && f->u.appl.functor==INTERN_OR) {
            int i, sign;
            for (i = 0; i < f->u.appl.count; ++i) {
                struct _ex_intern *e = f->u.appl.args[i];
                sign = 3;
                if (e->type == EXP_APPL && e->u.appl.functor == INTERN_NOT) {
                    e = e->u.appl.args[0];
                }
                if (e->type != EXP_VAR) {
                    struct signed_list *s, *ps;
                    //printf("Adding term %s\n", _th_print_exp(e));
                    t = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                    t->next = terms;
                    t->source = 0;
                    t->sign = sign;
                    t->count = 0;
                    t->fv = NULL;
                    t->e = e;
                    s = terms;
                    ps =t;
                    terms = t;
                    while (s) {
                        if (s->e==t->e) {
                            ps->next = s->next;
                        }
                        ps = s;
                        s = s->next;
                    }
                    ue = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_OR,e,ue));
                }
            }
        } else {
            return 0;
        }
        f = _th_get_next_neg_tuple(info);
    }

    while (unates) {
        if (unates->split != _ex_true && unates->split != _ex_false &&
            unates->split->type != EXP_VAR &&
            (unates->split->type != EXP_APPL || unates->split->u.appl.functor != INTERN_NOT ||
             unates->split->u.appl.args[0]->type != EXP_VAR)) {
            struct signed_list *s, *ps;
            t = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
            t->next = terms;
            t->source = 0;
            t->count = 0;
            t->fv = NULL;
            if (unates->split->type==EXP_APPL && unates->split->u.appl.functor==INTERN_NOT) {
                t->e = unates->split->u.appl.args[0];
                t->sign = 9;
            } else {
                t->e = unates->split;
                t->sign = 6;
            }
            s = terms;
            ps =t;
            terms = t;
            while (s) {
                if (s->e==t->e) {
                    ps->next = s->next;
                }
                ps = s;
                s = s->next;
            }
            ue = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_OR,_ex_intern_appl1_env(env,INTERN_NOT,unates->split),ue));
            //printf("Adding unate %s\n", _th_print_exp(unates->split));
        }
        unates = unates->next;
    }
    unates = u;

    //t = terms;
    //while (t) {
    //    _th_simp(env,t->e);
    //    t = t->next;
    //}
    //u = unates;
    //while (u) {
    //    _th_simp(env,u->split);
    //    u = u->next;
    //}

    //t = terms;
    //while (t) {
    //    printf("term: %s\n", _th_print_exp(t->e));
    //    t = t->next;
    //}
    gr = g = collect_groups(env,ue,e,0);

    //while (unates) {
    //    _th_assert_predicate(env,unates->split);
    //    unates = unates->next;
    //}
    while (gr) {
        build_conflict_set(env,gr,unates);
        gr = gr->next;
    }
    _th_derive_pop(env);
    _th_alloc_release(_th_get_space(env),rmark);

    tcyc = 0;
    while (g) {
        tcyc += g->cycle_count;
        if (g->is_trivial) ++tg;
#ifdef HACK_OUT
        if (g->can_subout && hack_out-- > 0) {
#else
        if (g->can_subout) {
#endif
		++gg;
            tc += g->conflict_count;
            te += g->edges_added;
            e = subout_group(env,e,g->group,g->conflicts,unates,info);
        } else {
            ++bg;
        }
        //printf("Group: %s\n", _th_print_exp(g->e));
        //a = g->group;
        //while (a) {
        //    printf("    Term: %s\n", _th_print_exp(a->e));
        //    a = a->next;
        //}
        g = g->next;
    }

    _tree_print1("Total conflicts %d", tc);
    _tree_print1("Total cycles %d", tcyc);
    _tree_print1("Total edges %d", te);
    _tree_print1("Good groups %d", gg);
    _tree_print1("Bad groups %d", bg);
    if (_th_print_grouping_data) {
        printf("Total conflicts %d\n", tc);
        printf("Total cycles %d\n", tcyc);
        printf("Total edges %d\n", te);
        printf("Good groups %d\n", gg);
        printf("Bad groups %d\n", bg);
        printf("Trivial groups %d\n", tg);
    }
    _tree_undent();
    return e;
}

struct fv_pair {
    unsigned fv;
    int count;
};

static struct _ex_intern *replace_v(struct env *env, struct _ex_intern *e, unsigned v, struct _ex_intern *rep)
{
    int i;
    struct _ex_intern **args, *r;

    if (e->type==EXP_VAR && e->u.var==v) return rep;

    if (e->type==EXP_APPL) {
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = replace_v(env,e->u.appl.args[i],v,rep);
        }
        r = _ex_intern_appl_equal_env(env,e->u.appl.functor,e->u.appl.count,args,e->type_inst);
        return r;
    }

    return e;
}

static int total_count_groups = -1;

static int flower_count(struct env *env, struct _ex_intern *ue, struct _ex_intern *e, struct parent_list *unates, unsigned flower, struct learn_info *info)
{
    unsigned *fv;
    int count, i;
    struct signed_list *a = terms;
    int countr;

    while (a != NULL) {
        fv = _th_get_free_vars(a->e,&count);
        for (i = 0; i < count; ++i) {
            if (fv[i]==flower) {
                if (count < 2 || !_th_is_difference_term(env,a->e)) {
                    return 0;
                }
                goto cont;
            }
        }
cont:
        a = a->next;
    }
    //g = collect_groups(env, ue, e, 0);
	if (total_count_groups >= 0) {
		countr = total_count_groups;
	} else {
        total_count_groups = countr = count_groups(env, ue, 0);
	}
    //while (g) {
    //    ++count;
    //    g = g->next;
    //}
    //g1 = g = collect_groups(env, ue, e, flower);
    count = count_groups(env, ue, flower);
    //while (g1) {
    //    ++countr;
    //    g1 = g1->next;
    //}
    //_tree_print3("counts %d %d %s", count, countr, _th_intern_decode(flower));

    return countr - count - 1;
}

static struct _ex_intern *uer;

static struct _ex_intern *break_flower(struct env *env, struct _ex_intern *ue, struct _ex_intern *e, struct parent_list *unates, unsigned flower, struct learn_info *info)
{
    unsigned *fv;
    int i, count;
    struct signed_list *a = terms;
    struct group_list *g, *g1;

    while (a != NULL) {
        fv = _th_get_free_vars(a->e,&count);
        for (i = 0; i < count; ++i) {
            if (fv[i]==flower) {
                if (count < 2 || !_th_is_difference_term(env,a->e)) {
                    return NULL;
                }
                goto cont;
            }
        }
cont:
        a = a->next;
    }
    g1 = g = collect_groups(env, ue, e, flower);
    while (g1) {
        g1 = g1->next;
    }

    //printf("Flower %s\n", _th_intern_decode(flower));

    while (g != NULL) {
        struct _ex_intern *nv;
        a = g->group;
        while (a) {
            if (_th_is_free_in(a->e,flower)) {
                goto do_sub;
            }
            a = a->next;
        }
#ifndef FAST
        _tree_print0("Skip group");
        _tree_indent();
        a = g->group;
        while (a) {
            _tree_print_exp("g", a->e);
            a = a->next;
        }
        _tree_undent();
#endif
        goto skip_sub;
do_sub:
        nv = _ex_intern_var(new_var(env,info,_th_get_var_type(env,flower)));
        //printf("Group %s\n", _th_print_exp(nv));
        _tree_print_exp("Flower group", nv);
        _tree_indent();
        a = g->group;
        while (a) {
            _tree_print_exp("g", a->e);
            //printf("sub term %s => ", _th_print_exp(a->e));
            a->e->user2 = replace_v(env,a->e,flower,nv);
            //printf("%s\n", _th_print_exp(a->e->user2));
            a = a->next;
        }
        _tree_undent();
skip_sub:
        g = g->next;
    }
    trail = NULL;

    //++_th_block_complex;
    //printf("Before e %s\n", _th_print_exp(e));
    e = sub_terms(env,e);
    uer = sub_terms(env,ue);
    //printf("After e %s\n", _th_print_exp(e));
    //--_th_block_complex;
    _th_abstract_tuples(env,info);

    while (unates) {
        //printf("Processing unate %s =>", _th_print_exp(unates->split));
        if (unates->split->user2) unates->split = unates->split->user2;
        if (unates->split->type==EXP_APPL && unates->split->u.appl.functor==INTERN_NOT &&
            unates->split->u.appl.args[0]->user2) {
            unates->split = _ex_intern_appl1_env(env,INTERN_NOT,unates->split->u.appl.args[0]->user2);
        }
        //printf(" %s\n", _th_print_exp(unates->split));
        unates = unates->next;
    }

    a = terms;

    while (a) {
        struct _ex_intern *e = a->e;
        if (a->e->user2) a->e = a->e->user2;
        e->user2 = NULL;
        a = a->next;
    }
    while (trail) {
        trail->user2 = NULL;
        trail = trail->next_cache;
    }

    return _th_nc_rewrite(env,e);
}

static int rcmp(struct fv_pair *pair1, struct fv_pair *pair2)
{
    return pair2->count - pair1->count;
}

static struct _ex_intern *vtest = NULL;

void check_user2(struct env *env, char *pos)
{
    if (vtest==NULL) {
        vtest = _th_parse(env,"(rless (rplus #-1/1 x1) x0__2)");
    }
    if (vtest->user2==_ex_true) {
        fprintf(stderr, "Failure at %s\n", pos);
        exit(1);
    }
}

struct _ex_intern *_th_break_flower(struct env *env, struct _ex_intern *e, struct parent_list *unates, struct learn_info *info)
{
    unsigned *fv;
    int count, i, j, c;
    struct fv_pair *fvars;
    struct signed_list *a;
    char *rmark;
    struct parent_list *u;
    struct signed_list *t;
    struct _ex_intern *fve, *f, *r;
    int max, maxc;
    unsigned maxv;

    _tree_print_exp("break flower", e);
    _tree_indent();

    ue_fv = NULL;
    rmark = _th_alloc_mark(REWRITE_SPACE);

    //check_user2(env, "begin");

    collect_terms(env,e,1);
    f = _th_get_first_neg_tuple(info);
    fve = e;
    while (f) {
        if (f->type==EXP_APPL && f->u.appl.functor==INTERN_OR) {
            int i, sign;
            for (i = 0; i < f->u.appl.count; ++i) {
                struct _ex_intern *e = f->u.appl.args[i];
                sign = 1;
                if (e->type == EXP_APPL && e->u.appl.functor == INTERN_NOT) {
                    e = e->u.appl.args[0];
                    sign = 2;
                }
                if (e->type != EXP_VAR) {
                    struct signed_list *s, *ps;
                    //printf("Adding term %s\n", _th_print_exp(e));
                    t = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
                    t->next = terms;
                    t->source = 0;
                    t->sign = sign;
                    t->e = e;
                    t->count = 0;
                    t->fv = NULL;
                    s = terms;
                    ps =t;
                    terms = t;
                    while (s) {
                        if (s->e==t->e) {
                            ps->next = s->next;
                        }
                        ps = s;
                        s = s->next;
                    }
                    fve = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_OR,e,fve));
                }
            }
        } else {
            return 0;
        }
        f = _th_get_next_neg_tuple(info);
    }

    u = unates;
    while (u) {
        if (u->split != _ex_true && u->split != _ex_false && u->split->type != EXP_VAR &&
            (u->split->type != EXP_APPL || u->split->u.appl.functor != INTERN_NOT ||
             u->split->u.appl.args[0]->type != EXP_VAR)) {
            struct signed_list *s, *ps;
            t = (struct signed_list *)_th_alloc(REWRITE_SPACE,sizeof(struct signed_list));
            t->count = 0;
            t->fv = NULL;
            t->next = terms;
            terms = t;
            if (u->split->type==EXP_APPL && u->split->u.appl.functor==INTERN_NOT) {
                t->e = u->split->u.appl.args[0];
                t->sign = 9;
            } else {
                t->e = u->split;
                t->sign = 6;
            }
            s = terms;
            ps = t;
            terms = t;
            while (s) {
                if (s->e==t->e) {
                    ps->next = s->next;
                }
                ps = s;
                s = s->next;
            }
            fve = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_OR,_ex_intern_appl1_env(env,INTERN_NOT,u->split),fve));
        }
        u = u->next;
    }

#ifndef FAST
    _tree_print0("Terms");
    t = terms;
    _tree_indent();
    c = 0;
    while (t) {
        _tree_print_exp("t", t->e);
        ++c;
        t = t->next;
    }
    _tree_print1("count = %d", c);
    _tree_undent();
#endif

break_another:
    while (trail) {
        struct _ex_intern *t = trail->user2;
        trail->user2 = NULL;
        trail = t;
    }

    fv = _th_get_free_vars(fve,&count);

    fvars = (struct fv_pair *)ALLOCA(sizeof(struct fv_pair) * count);
    for (i = 0; i < count; ++i) {
        fvars[i].fv = fv[i];
        fvars[i].count = 0;
    }

    a = terms;
    while (a) {
        fv = _th_get_free_vars(a->e,&c);
        a = a->next;
        for (i = 0; i < c; ++i) {
            for (j = 0; j < count; ++j) {
                if (fv[i]==fvars[j].fv) ++fvars[j].count;
            }
        }
    }

    //_tree_print("Here\n");

    qsort(fvars, count, sizeof(struct fv_pair), (void *)rcmp);

    max = 0;
    //_tree_print("Finding flower");
    //_tree_indent();
	total_count_groups = -1;
    for (i = 0; i < count; ++i) {
        int x;
        //_tree_print1("Processing %s", _th_intern_decode(fvars[i].fv));
        //if (i%100==0) printf("At point %d\n", i);
        if (fvars[i].count > 1) {
            //_tree_print1("Testing %s", _th_intern_decode(fvars[i].fv));
            x = flower_count(env, fve, e, unates, fvars[i].fv, info);
            //_tree_print1("count %d", x);
            if (x > max) {
                max = x;
                maxv = fvars[i].fv;
                maxc = fvars[i].count;
                goto cont;
            }
        }
    }

cont:
    //_tree_undent();

    if (max > 0) {
        //++_th_block_complex;
        //_tree_print1("Flower var %s", _th_intern_decode(maxv));
        r = break_flower(env, fve, e, unates, maxv, info);
        //--_th_block_complex;
        //_tree_print1("Breaking %s", _th_intern_decode(maxv));
        //printf("%s - %d\n", ,maxv, maxc);
        if (r) {
            //++_th_block_complex;
            //_tree_print_exp("Broken flower", r);
            //--_th_block_complex;
            //_tree_undent();
            e = r;
            fve = uer;
            //++_th_block_complex;
            //_tree_print_exp("Broken fve", fve);
            //--_th_block_complex;
            goto break_another;
        }
    }
    _tree_undent();
    _th_alloc_release(REWRITE_SPACE,rmark);

    //check_user2(env, "end");

    return e;
}
