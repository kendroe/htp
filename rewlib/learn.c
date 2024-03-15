#define DOMAIN_PROPAGATE
/*
 * learn.c
 *
 * Routines to learn minimal sets of contradictory conditions.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdio.h>
#include <stdlib.h>
#include "Globals.h"
#include "Intern.h"
#include <stdlib.h>

struct tuple {
    struct tuple *next;
    int size;
    int abstract_skip;
    struct _ex_intern **terms;
    struct tuple **term_next;
    struct term_info_list **term_info;
    int *term_next_index;
    struct tuple *check_next;
    int from_implication;
    int used_count;
    int add_mode;
    int var1;
    int var2;
    struct tuple *var1_next;
    struct tuple *var2_next;
    struct tuple *unate_next;
    struct tuple *unate_prev;
};

#define TERM_HASH 127

struct tuple_list {
    struct tuple_list *next;
    struct tuple *tuple;
};

struct tuple_dlist {
    struct tuple_dlist *next, *prev;
    struct tuple *tuple;
};

struct score_list {
    struct score_list *next;
    struct term_info_list *term;
    int is_implication;
};

struct term_info_list {
    struct term_info_list *next;
    struct score_list *score_list;
    struct _ex_intern *term;
    struct tuple *tuple;
    int index;
    struct tuple *check;
    int count;
    int reject_count;
    struct _ex_intern *assignment;
    int true_implications;
    int false_implications;
    struct tuple *var1_list;
    struct tuple *var2_list;
    int decision_level;
    int passed;
	double pos_score, neg_score;
};

struct assignments {
    struct asignments *next;
    struct term_info_list *term;
    struct _ex_intern *value;
};

#define SHARE_SIZE 16383

struct pair_list {
    struct pair_list *next;
    struct _ex_intern *e1, *e2;
    int share;
};

struct learn_info {
    int have_unate_tail;
    int add_count;
	int term_count;
    struct parent_list *unate_tail;
    struct tuple *tuples;
    struct term_info_list *tuples_by_term[TERM_HASH];
    struct env *env;
    int generalized_tuples;
    int learns;
    //struct assignments *assignments;
    struct tuple *unates;
    struct pair_list **share_hash;
	double bump_size;
};

struct antecedant_set {
    struct antecedant_set *next;
    struct add_list *antecedant;
};

static struct tuple *current;

struct _ex_intern *_th_get_next_neg_tuple(struct learn_info *info)
{
    struct _ex_intern **args, *r;
    int i;

    while (current != NULL && current->abstract_skip) {
        current = current->next;
    }

    if (current==NULL) return NULL;

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * current->size);
    for (i = 0; i < current->size; ++i) {
        if (current->terms[i]->type==EXP_APPL && current->terms[i]->u.appl.functor==INTERN_NOT) {
            args[i] = current->terms[i]->u.appl.args[0];
        } else {
            args[i] = _ex_intern_appl1_env(info->env,INTERN_NOT,current->terms[i]);
        }
    }

    r = _ex_intern_appl_env(info->env,INTERN_OR,current->size,args);
    current = current->next;

    return r;
}

struct _ex_intern *_th_get_first_neg_tuple(struct learn_info *info)
{
    current = info->tuples;
    while (current != NULL && current->abstract_skip) {
        current = current->next;
    }
    return _th_get_next_neg_tuple(info);
}

void check_user2_error(struct learn_info *info)
{
    int i, j;

    if (info==NULL) return;

    for (i = 0; i < TERM_HASH; ++i) {
        struct term_info_list *t = info->tuples_by_term[i];
        while (t) {
            if (t->term->user2) {
                fprintf(stderr, "User2 error in %s\n", _th_print_exp(t->term));
                exit(1);
            }
            if (t->term->type==EXP_APPL) {
                for (j = 0; j < t->term->u.appl.count; ++j) {
                    if (t->term->u.appl.args[j]->user2) {
                        fprintf(stderr, " User2 error in position %d of %s\n", j, _th_print_exp(t->term));
                        exit(1);
                    }
                }
            }
            t = t->next;
        }
    }
}

struct learn_info *dinfo;

void check_missed_term(struct env *env, struct add_list *l)
{
    int i;
    struct add_list *l1;

    if (dinfo==NULL) return;

    for (i = 0; i < TERM_HASH; ++i) {
        struct term_info_list *t = dinfo->tuples_by_term[i];
        while (t) {
            struct _ex_intern *x = _th_get_quick_implication(env,t->term,NULL);
            if (x && x!=t->term) {
                l1 = l;
                while (l1) {
                    if (l1->e==t->term) goto cont;
                    l1 = l1->next;
                }
                fprintf(stderr, "Missed term %s\n", _th_print_exp(t->term));
                _th_print_difference_table(env);
                exit(1);
cont:;
            }
            t = t->next;
        }
    }
}

int _th_learn_term_count(struct learn_info *info)
{
    int i, count;

    for (i = 0, count = 0; i < TERM_HASH; ++i) {
        struct term_info_list *t = info->tuples_by_term[i];
        while (t) {
            ++count;
            t = t->next;
        }
    }

    return count;
}

void _th_learn_print_assignments(struct learn_info *info)
{
    int i;

    for (i = 0; i < TERM_HASH; ++i) {
        struct term_info_list *t = info->tuples_by_term[i];
        while (t) {
            if (t->assignment==_ex_true) {
                _tree_print1("%s => TRUE", _th_print_exp(t->term));
            } else if (t->assignment==_ex_false) {
                _tree_print1("%s => FALSE", _th_print_exp(t->term));
            } else {
                _tree_print1("%s => unassigned", _th_print_exp(t->term));
            }
            t = t->next;
        }
    }
}

struct _ex_intern *_th_add_learn_terms(struct learn_info *info, struct _ex_intern *e)
{
    int i;
    int count;
    struct _ex_intern **args;

    count = 0;
    for (i = 0; i < TERM_HASH; ++i) {
        struct term_info_list *t = info->tuples_by_term[i];
        while (t) {
            ++count;
            t = t->next;
        }
    }
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (count + 1));
    count = 0;
    for (i = 0; i < TERM_HASH; ++i) {
        struct term_info_list *t = info->tuples_by_term[i];
        while (t) {
            args[count++] = t->term;
            t = t->next;
        }
    }

    args[count++] = e;

    //printf("Adding learn %s\n", _th_print_exp(e));

    return _ex_intern_appl_env(info->env,INTERN_OR,count,args);
}

static int ucmp(const void *i1,const void *i2)
{
    struct _ex_intern *e1 = *((struct _ex_intern **)i1);
    struct _ex_intern *e2 = *((struct _ex_intern **)i2);
    return ((int)e2)-((int)e1);
}

static int cmp(const void *i1,const void *i2)
{
    struct _ex_intern *e1 = *((struct _ex_intern **)i1);
    struct _ex_intern *e2 = *((struct _ex_intern **)i2);
    if (e1->type==EXP_APPL && e1->u.appl.functor==INTERN_NOT) e1 = e1->u.appl.args[0];
    if (e2->type==EXP_APPL && e2->u.appl.functor==INTERN_NOT) e2 = e2->u.appl.args[0];
    return ((int)e2)-((int)e1);
}

static int added_unate_tuple;

void validate_learn(struct learn_info *info)
{
    static int got_info = 0;
    if (info==NULL) return;
    if (got_info && !info->tuples_by_term[16]) {
        fprintf(stderr, "Learn info destroyed\n");
        exit(1);
    }
    if (info->tuples_by_term[16]) got_info = 1;
}

static struct term_info_list *get_term_info(struct env *env, struct learn_info *learn, struct _ex_intern *term, int add)
{
    struct term_info_list *t;
    int hash;

    if (term->type==EXP_APPL && term->u.appl.functor==INTERN_NOT) term = term->u.appl.args[0];
    hash = (((int)term)/4)%TERM_HASH;

    t = learn->tuples_by_term[hash];
    while (t != NULL) {
        if (t->term==term) return t;
        t = t->next;
    }

    if (!add) return NULL;

    t = (struct term_info_list *)_th_alloc(HEURISTIC_SPACE,sizeof(struct term_info_list));
    t->score_list = NULL;
    t->next = learn->tuples_by_term[hash];
    learn->tuples_by_term[hash] = t;
    t->count = 0;
	t->pos_score = 0;
	t->neg_score = 0;
    t->reject_count = 0;
    t->index = 0;
    t->term = term;
    t->tuple = NULL;
    t->assignment = NULL;
    t->true_implications = t->false_implications = 0;
    t->var1_list = NULL;
    t->var2_list = NULL;

    return t;
#ifdef OLD
    struct term_info_list *t;
    int hash, i;
    struct _ex_intern *find, *f;

    //_tree_print_exp("Term lookup", term);

    if (term->type==EXP_APPL && term->u.appl.functor==INTERN_NOT) term = term->u.appl.args[0];
    //_tree_print_exp("Original", term);
    hash = (((int)term)/4)%TERM_HASH;

    t = learn->tuples_by_term[hash];
    while (t != NULL) {
        if (t->term==term) return t;
        t = t->next;
    }
    f = term;
    if (term->original) _zone_print1("original type %d", term->original->type);
    _zone_print_exp("get_term_info: Original", term->original);
    if (term->original) term = term->original;
    hash = (((int)term)/4)%TERM_HASH;
    t = learn->tuples_by_term[hash];
    while (t != NULL) {
        if (t->term==term) return t;
        t = t->next;
    }
    _zone_print_exp("get_term_info: here1", term);
    find = term;
    while (find->find && find->find != find) find = find->find;
    _zone_print_exp("get_term_info: find", find);
    if (find==_ex_true || find==_ex_false) {
        i = 0;
        fprintf(stderr, "Internal error: Cannot get information on assigned term %s\n", _th_print_exp(f));
        fflush(stderr);
        i = 1/i;
        exit(1);
    }
    for (i = 0; i < TERM_HASH; ++i) {
        t = learn->tuples_by_term[i];
        while (t) {
            f = t->term;
            while (f->find && f != f->find) {
                f = f->find;
            }
            //printf("Checking term %s\n", _th_print_exp(t->term));
            //printf("    find %s\n", _th_print_exp(f));
            if (f==find) {
                if (env) {
                    //printf("%d: Adding original %s", _tree_zone, _th_print_exp(term));
                    //printf(" = %s\n", _th_print_exp(t->term));
                    if (t->term->type==0) {
                        fprintf(stderr, "Illegal original term\n");
                        exit(1);
                    }
                    _th_add_original(env,term,t->term);
                }
                _tree_print1("get_term_info: env %d", env);
                _tree_print_exp("get_term_info: returning", t->term);
                return t;
            }
            t = t->next;
        }
    }
    _zone_print0("get_term_info: not there");
    if (!add) return NULL;
    _zone_print0("get_term_info: add term");
    //printf("%d: Entering 1 %s\n", _tree_zone, _th_print_exp(term));
    t = (struct term_info_list *)_th_alloc(HEURISTIC_SPACE,sizeof(struct term_info_list));
    //printf("Entering 6 %d %s\n", _tree_zone, _th_print_exp(term));
    t->score_list = NULL;
    t->next = learn->tuples_by_term[hash];
    learn->tuples_by_term[hash] = t;
    t->count = 0;
    t->reject_count = 0;
    t->index = 0;
    //if (!term->in_hash) {
    //    fprintf(stderr, "Error: not in hash 4 %s\n", _th_print_exp(term));
    //    fprintf(stderr, "find: %s\n", _th_print_exp(find));
    //    exit(1);
    //}
    t->term = term;
    t->tuple = NULL;
    t->assignment = NULL;
    t->true_implications = t->false_implications = 0;
    t->var1_list = NULL;
    t->var2_list = NULL;

    return t;
#endif
}

void _th_learn_add_score_dependencies(struct env *env, struct learn_info *info)
{
    int i;

    for (i = 0; i < TERM_HASH;++i) {
        struct term_info_list *t;
        struct score_list *s;
        t = info->tuples_by_term[i];
        while (t) {
            struct dependencies *d = _th_get_dependencies(t->term);
            while (d) {
                struct term_info_list *nt = get_term_info(env,info,d->term->e,0);
                if (nt) {
                    s = (struct score_list *)_th_alloc(HEURISTIC_SPACE,sizeof(struct score_list));
                    s->next = t->score_list;
                    t->score_list = s;
                    s->is_implication = (d->reduction==_ex_true || d->reduction==_ex_false);
                    s->term = nt;
                }
                d = d->next;
            }
            d = _th_get_neg_dependencies(t->term);
            while (d) {
                struct term_info_list *nt = get_term_info(env,info,d->term->e,0);
                if (nt) {
                    s = (struct score_list *)_th_alloc(HEURISTIC_SPACE,sizeof(struct score_list));
                    s->next = t->score_list;
                    t->score_list = s;
                    s->is_implication = (d->reduction==_ex_true || d->reduction==_ex_false);
                    s->term = nt;
                }
                d = d->next;
            }
            t = t->next;
        }
    }
}

int _th_get_reject_count(struct env *env, struct learn_info *learn, struct _ex_intern *term)
{
    struct term_info_list *t;
    
    //printf("reject count\n");
    t = get_term_info(env, learn, term, 0);

    if (t==NULL) {
        return 0;
    } else {
        return t->reject_count;
    }
}

//int no_recurse;
static struct tuple *n_tuple;
//static struct parent_list *pl;

static struct tuple *has_conflicting_group(struct learn_info *info, struct parent_list *list)
{
    struct tuple *tuple = info->tuples;
    struct parent_list *l;
    int i;

    while (tuple) {
        for (i = 0; i < tuple->size; ++i) {
            l = list;
            while (l) {
                //if (l->split->type==EXP_APPL && l->split->u.appl.functor==INTERN_NOT) {
                //    if (l->split->u.appl.args[0]==tuple->terms[i]) goto cont;
                //}
                //if (tuple->terms[i]->type==EXP_APPL && tuple->terms[i]->u.appl.args[0]==l->split) goto cont;
                if (tuple->terms[i]==l->split) goto cont;
                l = l->next;
            }
            goto next;
cont:;
        }
        return tuple;
next:
        tuple = tuple->next;
    }

    return NULL;
}

#define SCORE_LIMIT 1.0e100

static void divide_scores(struct learn_info *info)
{
	int i;
	struct term_info_list *l;

	info->bump_size /= SCORE_LIMIT;
	for (i = 0; i < TERM_HASH; ++i) {
		l = info->tuples_by_term[i];
		while (l) {
			l->pos_score /= SCORE_LIMIT;
			l->neg_score /= SCORE_LIMIT;
			l = l->next;
		}
	}
}

static int add_group(struct env *env, struct learn_info *learn, int count, struct _ex_intern **args, int add_mode)
{
    struct _ex_intern **terms;
    int i;
    char *mark = _th_alloc_mark(HEURISTIC_SPACE);
    int hash;
    struct term_info_list *t;
    struct _ex_intern *base;
    struct tuple *tuple;
    int disagree_count;

    added_unate_tuple = 0;

    terms = (struct _ex_intern **)_th_alloc(HEURISTIC_SPACE,sizeof(struct _ex_intern *) * count);
    //printf("Adding group %d %d\n", add_mode, _tree_zone);
    _zone_print1("Adding group %d", count);
    if (count==0) {
        //struct tuple *tuple;
        //return 0;
        //fprintf(stderr, "Error: adding group of size 0\n");
        //_th_alloc_shutdown();
        //_tree_shutdown();
        //dump_state(env,pl);
        //tuple = has_conflicting_group(learn,pl);
        //if (tuple) {
        //    fprintf(stderr, "Conflicting tuple %d\n", tuple->add_mode);
        //    for (i = 0; i < tuple->size; ++i) {
        //        fprintf(stderr, "    %s ", _th_print_exp(tuple->terms[i]));
        //        fprintf(stderr, "(%s)\n", _th_print_exp(tuple->term_info[i]->assignment));
        //    }
        //}
        //exit(1);
        return 1;
    }
    _tree_indent();

    for (i = 0; i < count; ++i) {
        _zone_print_exp("cond", args[i]);
        //printf("    %s\n", _th_print_exp(args[i]));
        terms[i] = args[i];
        //if (terms[i]->original) terms[i] = terms[i]->original;
        
        //_tree_print_exp("term", terms[i]);
#ifndef FAST
        if (terms[i]==_ex_true || terms[i]==_ex_false) {
            fprintf(stderr, "Error: %s not legal in group\n", _th_print_exp(terms[i]));
            exit(1);
        }
#endif
    }
    _tree_undent();

    qsort(terms,count,sizeof(struct _ex_intern *),cmp);

    //_tree_print0("Sorted");
    //_tree_indent();
    //for (i = 0; i < count; ++i) {
    //    _tree_print_exp("cond", terms[i]);
    //    //printf("    %s\n", _th_print_exp(args[i]));
    //}
    //_tree_undent();

    base = terms[0];
    if (base->type==EXP_APPL && base->u.appl.functor==INTERN_NOT) base = base->u.appl.args[0];
    hash = (((int)base)/4)%TERM_HASH;
    //_tree_print("hash 0 %d", hash);
    t = learn->tuples_by_term[hash];
    while (t != NULL && t->term != base) {
        t = t->next;
    }
    if (t) {
        int index = t->index;
        tuple = t->tuple;
        while (tuple) {
            int in;
            if (tuple->size==count) {
                for (i = 0; i < count; ++i) {
                    if (terms[i] != tuple->terms[i]) goto cont;
                }
#ifndef FAST
                _tree_print0("Already present");
                n_tuple = tuple;
//#ifdef XX
                if (add_mode) {
                    //int n = 0;
                    //printf("Already present %d\n", add_mode);
                    _tree_indent();
                    for (i = 0; i < tuple->size; ++i) {
                        char *v;
                        if (tuple->term_info[i]->assignment) {
                            if (tuple->term_info[i]->assignment==_ex_true) {
                                v = "<<TRUE>>";
                            } else {
                                v = "<<FALSE>>";
                            }
                        } else {
                            v = "<<Null>>";
                            //n = 1;
                        }
                        _tree_print2("term %s %s", _th_print_exp(tuple->terms[i]), v);
                        //printf("    %s", _th_print_exp(tuple->terms[i]));
                        //printf(" (%s)\n", _th_print_exp(tuple->term_info[i]->assignment));
                    }
                    _tree_undent();
                    //fflush(stdout);
                    //if (n) exit(1);
                }
//#endif
#endif
                //if (no_recurse) {
                //    fprintf(stderr, "Attempt to learn existing tuple\n");
                //    exit(1);
                //}
                return 0;
            }
cont:
            in = tuple->term_next_index[index];
            tuple = tuple->term_next[index];
            index = in;
        }
    }

    if (t==NULL) {
        t = (struct term_info_list *)_th_alloc(HEURISTIC_SPACE,sizeof(struct term_info_list));
        t->score_list = NULL;
        t->next = learn->tuples_by_term[hash];
        learn->tuples_by_term[hash] = t;
        t->count = 0;
		t->pos_score = 0;
		t->neg_score = 0;
        t->index = 0;
        t->term = base;
        //printf("%d: Entering 2 %s\n", _tree_zone, _th_print_exp(base));
        //if (!base->in_hash) {
        //    fprintf(stderr, "Term not in hash 2: %s\n", _th_print_exp(base));
        //    exit(1);
        //}
        t->tuple = NULL;
        t->assignment = NULL;
        t->true_implications = t->false_implications = 0;
        t->var1_list = NULL;
        t->var2_list = NULL;
		++learn->term_count;
    }
    tuple = (struct tuple *)_th_alloc(HEURISTIC_SPACE,sizeof(struct tuple));
    tuple->abstract_skip = 0;
    tuple->unate_next = tuple->unate_prev = NULL;
    tuple->terms = terms;
    tuple->term_next = (struct tuple **)_th_alloc(HEURISTIC_SPACE,sizeof(struct tuple *) * count);
    tuple->term_next_index = (int *)_th_alloc(HEURISTIC_SPACE,sizeof(int) * count);
    tuple->term_info =  (struct term_info_list **)_th_alloc(HEURISTIC_SPACE,sizeof(struct term_info_list *) * count);
    tuple->next = learn->tuples;
    learn->tuples = tuple;
    tuple->term_next[0] = t->tuple;
    tuple->term_next_index[0] = t->index;
    tuple->term_info[0] = t;
    tuple->size = count;
    tuple->add_mode = add_mode;
    if (tuple->size==1) added_unate_tuple = 1;
    tuple->from_implication = 0;
    tuple->used_count = 0;
    t->tuple = tuple;
    t->index = 0;
    t->reject_count = 0;
    if (add_mode) {
        t->count += 2;
    } else {
        ++t->count;
    }

	if (tuple->terms[0]==base) {
        t->pos_score += learn->bump_size;
		if (t->pos_score > SCORE_LIMIT) divide_scores(learn);
	} else {
        t->neg_score += learn->bump_size;
		if (t->pos_score > SCORE_LIMIT) divide_scores(learn);
	}
    _zone_print1("count = %d", count);
    for (i = 1; i < count; ++i) {
        base = terms[i];
        if (base->type==EXP_APPL && base->u.appl.functor==INTERN_NOT) base = base->u.appl.args[0];
        hash = (((int)base)/4)%TERM_HASH;
        //_tree_print2("hash %d %d", i, hash);
        t = learn->tuples_by_term[hash];
        while (t != NULL && t->term != base) {
            t = t->next;
        }
        if (t==NULL) {
            t = (struct term_info_list *)_th_alloc(HEURISTIC_SPACE,sizeof(struct term_info_list));
            t->score_list = NULL;
            t->next = learn->tuples_by_term[hash];
            learn->tuples_by_term[hash] = t;
            t->count = 0;
            t->reject_count = 0;
            t->index = i;
            //if (!base->in_hash) {
            //    fprintf(stderr, "Term not in hash 3: %s\n", _th_print_exp(base));
            //    exit(1);
            //}
            t->term = base;
            //printf("%d: Entering 3 %d %s\n", _tree_zone, add_mode, _th_print_exp(base));
            t->tuple = NULL;
            t->assignment = NULL;
            t->true_implications = t->false_implications = 0;
            t->var1_list = NULL;
            t->var2_list = NULL;
    		++learn->term_count;
        }
        tuple->term_next[i] = t->tuple;
        tuple->term_next_index[i] = t->index;
        tuple->term_info[i] = t;
        t->tuple = tuple;
        t->index = i;
        if (add_mode) {
            t->count += 2;
        } else {
            ++t->count;
        }
		if (tuple->terms[i]==base) {
			t->pos_score += learn->bump_size;
			if (t->pos_score > SCORE_LIMIT) divide_scores(learn);
		} else {
			t->neg_score += learn->bump_size;
			if (t->pos_score > SCORE_LIMIT) divide_scores(learn);
		}
        t->reject_count = 0;
    }

    disagree_count = 0;
    for (i = 0; i < tuple->size; ++i) {
        if (tuple->term_info[i]->assignment==NULL) {
            tuple->var1 = i;
            tuple->var1_next = tuple->term_info[i]->var1_list;
            tuple->term_info[i]->var1_list = tuple;
            goto cont1;
        } else {
            if (tuple->term_info[i]->assignment==_ex_true) {
                if (tuple->terms[i]->type==EXP_APPL && tuple->terms[i]->u.appl.functor==INTERN_NOT) {
                    ++disagree_count;
                }
            } else {
                if (tuple->terms[i]->type!=EXP_APPL || tuple->terms[i]->u.appl.functor!=INTERN_NOT) {
                    ++disagree_count;
                }
            }
        }
    }
    tuple->var1 = tuple->var2 = -1;
    //printf("Adding tuple %x %d %d %d\n", tuple, tuple->size, tuple->var1, tuple->var2);
    n_tuple = tuple;
    //printf("Good add 1\n");
    goto vsids;
cont1:
    for (++i; i < tuple->size; ++i) {
        if (tuple->term_info[i]->assignment==NULL) {
            tuple->var2 = i;
            tuple->var2_next = tuple->term_info[i]->var2_list;
            tuple->term_info[i]->var2_list = tuple;
            //if (tuple->var2_next==tuple) {
            //    fprintf(stderr, "Fail1\n");
            //    exit(1);
            //}
            goto cont2;
        } else {
            if (tuple->term_info[i]->assignment==_ex_true) {
                if (tuple->terms[i]->type==EXP_APPL && tuple->terms[i]->u.appl.functor==INTERN_NOT) {
                    ++disagree_count;
                }
            } else {
                if (tuple->terms[i]->type!=EXP_APPL || tuple->terms[i]->u.appl.functor!=INTERN_NOT) {
                    ++disagree_count;
                }
            }
        }
    }
    tuple->var2 = -1;
    if (disagree_count==0) {
        tuple->unate_next = learn->unates;
        tuple->unate_prev = NULL;
        learn->unates = tuple;
        if (tuple->unate_next) {
            tuple->unate_next->unate_prev = tuple;
        }
        t = tuple->term_info[tuple->var1];
        if (tuple->terms[tuple->var1]->type==EXP_APPL && tuple->terms[tuple->var1]->u.appl.functor==INTERN_NOT) {
            ++t->true_implications;
        } else {
            ++t->false_implications;
        }
    } else {
        tuple->unate_next = NULL;
    }
cont2:
    n_tuple = tuple;
    //printf("Adding group %d\n", add_mode);
    //if (add_mode) {
    //    for (i = 0; i < tuple->size; ++i) {
    //        printf("    %s", _th_print_exp(tuple->terms[i]));
    //        printf(" (%s)\n", _th_print_exp(tuple->term_info[i]->assignment));
    //    }
    //    fflush(stdout);
    //}
    //printf("Good add 2\n");
vsids:
    ++learn->add_count;
    if (learn->add_count==100) {
        learn->add_count = 0;
        for (i = 0; i < TERM_HASH; ++i) {
            t = learn->tuples_by_term[i];
            while (t) {
                t->count = t->count/2;
                t = t->next;
            }
        }
    }
    return 1;
}

void _th_abstract_tuples(struct env *env, struct learn_info *info)
{
    struct tuple *c;

    c = info->tuples;

    //printf("Calling abstract_tuples\n");

    while (c) {
        if (!c->abstract_skip) {
            int i;
            struct _ex_intern **args;
            for (i = 0; i < c->size; ++i) {
                if (c->terms[i]->user2 || (c->terms[i]->type==EXP_APPL && c->terms[i]->u.appl.functor==INTERN_NOT && c->terms[i]->u.appl.args[0]->user2)) goto cont;
            }
            goto next;
cont:
            //printf("Abstracting tuple\n");
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * c->size);
            for (i = 0; i < c->size; ++i) {
                //printf("    %s\n", _th_print_exp(c->terms[i]));
                if (c->terms[i]->user2) {
                    args[i] = c->terms[i]->user2;
                } else if (c->terms[i]->type==EXP_APPL && c->terms[i]->u.appl.functor==INTERN_NOT && c->terms[i]->u.appl.args[0]->user2) {
                    args[i] = _ex_intern_appl1_env(env,INTERN_NOT,c->terms[i]->u.appl.args[0]->user2);
                } else {
                    args[i] = c->terms[i];
                }
                if (args[i] != c->terms[i]) c->abstract_skip = 1;
                //printf("    %s\n", _th_print_exp(args[i]));
            }
            add_group(env,info,i,args,0);
        }
next:
        c = c->next;
    }
}

int _th_learn_has_non_unity(struct env *env, struct learn_info *info)
{
    struct tuple *c;

    c = info->tuples;

    //printf("Calling abstract_tuples\n");

    while (c) {
        if (!c->abstract_skip) {
            int i;
            for (i = 0; i < c->size; ++i) {
                if (_th_has_non_unity(env,c->terms[i])) return 1;
            }
        }
//next:
        c = c->next;
    }
    
    return 1;
}

void _th_elim_var(struct env *env, struct learn_info *info, unsigned var, struct _ex_intern *exp)
{
    struct tuple *c;

    c = info->tuples;

    //printf("Calling abstract_tuples\n");

    while (c) {
        if (!c->abstract_skip) {
            int i;
            struct _ex_intern **args;
            for (i = 0; i < c->size; ++i) {
                if (_th_is_free_in(c->terms[i],var)) goto cont;
            }
            goto next;
cont:
            //printf("Abstracting tuple\n");
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * c->size);
            for (i = 0; i < c->size; ++i) {
                if (_th_is_free_in(c->terms[i],var)) {
                    struct _ex_unifier *u = _th_new_unifier(REWRITE_SPACE);
                    u = _th_add_pair(REWRITE_SPACE,u,var,exp);
                    args[i] = _th_subst(env,u,c->terms[i]);
                } else {
                    args[i] = c->terms[i];
                }
                if (args[i] != c->terms[i]) c->abstract_skip = 1;
                //printf("    %s\n", _th_print_exp(args[i]));
            }
            add_group(env,info,i,args,0);
        }
next:
        c = c->next;
    }
}

void _th_elim_simp_var(struct env *env, struct learn_info *info)
{
    struct tuple *c;

    c = info->tuples;

    //printf("Calling abstract_tuples\n");

    while (c) {
        if (!c->abstract_skip) {
            int i;
            struct _ex_intern **args;
            //printf("Abstracting tuple\n");
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * c->size);
            for (i = 0; i < c->size; ++i) {
                args[i] = _th_simp(env,c->terms[i]);
                if (args[i] != c->terms[i]) {
                    c->abstract_skip = 1;
                    //printf("abstracting %s\n", _th_print_exp(c->terms[i]));
                    //printf("    to %s\n", _th_print_exp(args[i]));
                }
            }
            if (c->abstract_skip) add_group(env,info,i,args,0);
        }
        c = c->next;
    }
}

int _th_add_list(struct env *env, struct learn_info *info, struct parent_list *list)
{
    int count, i;
    struct parent_list *l;
    struct _ex_intern **args;

    //printf("Entering _th_solved_case\n");
    //fflush(stdout);

    if (info->have_unate_tail==0) return 0;

    l = list;
    count = 0;
    while (l && l != info->unate_tail) {
        ++count;
        l = l->next;
    }
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
    l = list;
    i = 0;
    while (l && l != info->unate_tail) {
        args[i++] = l->split;
        l =l->next;
    }

    //pl = list;
    return add_group(env,info,count,args,4);
}

void add_pair(struct env *env, struct learn_info *learn, struct _ex_intern *e1, struct _ex_intern *e2)
{
    int hash;
    struct term_info_list *ti;
    struct tuple *t;
    int i;
    struct _ex_intern *e1base, *e2base;

    e1base = e1;
    if (e1base->type==EXP_APPL && e1base->u.appl.functor==INTERN_NOT) e1base = e1base->u.appl.args[0];
    e2base = e2;
    if (e2base->type==EXP_APPL && e2base->u.appl.functor==INTERN_NOT) e2base = e2base->u.appl.args[0];

    if (((int)e2base) > ((int)e1base)) {
        struct _ex_intern *t = e1;
        e1 = e2;
        e2 = t;
        t = e1base;
        e1base = e2base;
        e2base = t;
    }

    hash = (((int)e1base)/4)%TERM_HASH;

    ti = learn->tuples_by_term[hash];
    while (ti != NULL && ti->term != e1base) {
        ti = ti->next;
    }

    if (ti != NULL) {
        t = ti->tuple;
        i = ti->index;
        while (t) {
            int in;
            if (t->size==2 && t->terms[i]==e1 && t->terms[1-i]==e2) break;
            in = t->term_next_index[i];
            t = t->term_next[i];
            i = in;
        }
    } else {
        ti = (struct term_info_list *)_th_alloc(HEURISTIC_SPACE,sizeof(struct term_info_list));
        //printf("entering 4 %d %s\n", _tree_zone, _th_print_exp(e1base));
        ti->score_list = NULL;
        ti->next = learn->tuples_by_term[hash];
        learn->tuples_by_term[hash] = ti;
        ti->term = e1base;
        ti->tuple = NULL;
        ti->index = 0;
        t = NULL;
        ti->count = 0;
        ti->reject_count = 0;
        ti->var1_list = NULL;
        ti->var2_list = NULL;
    }

    if (t==NULL) {
        t = (struct tuple *)_th_alloc(HEURISTIC_SPACE,sizeof(struct tuple));
        t->abstract_skip = 0;
        t->unate_next = t->unate_prev = NULL;
        t->next = learn->tuples;
        learn->tuples = t;
        t->terms = (struct _ex_intern **)_th_alloc(HEURISTIC_SPACE,sizeof(struct tuple *) * 2);
        t->term_next = (struct tuple **)_th_alloc(HEURISTIC_SPACE,sizeof(struct tuple *) * 2);
        t->term_next_index = (int *)_th_alloc(HEURISTIC_SPACE,sizeof(int) * 2);
        t->terms[0] = e1;
        t->terms[1] = e2;
        t->term_next[0] = ti->tuple;
        t->term_next_index[0] = ti->index;
        t->size = 2;
        t->from_implication = 1;
        t->used_count = 0;
        ti->tuple = t;
        ti->index = 0;
        hash = (((int)e2base)/4)%TERM_HASH;
        ti = learn->tuples_by_term[hash];
        while (ti != NULL && ti->term != e2base) {
            ti = ti->next;
        }
        if (ti == NULL) {
            ti = (struct term_info_list *)_th_alloc(HEURISTIC_SPACE,sizeof(struct term_info_list));
            //printf("entering 5 %d %s\n", _tree_zone, _th_print_exp(e2base));
            ti->score_list = NULL;
            ti->next = learn->tuples_by_term[hash];
            learn->tuples_by_term[hash] = ti;
            ti->term = e2base;
            ti->tuple = NULL;
            ti->index = 1;
            ti->count = 0;
            ti->reject_count = 0;
            ti->var1_list = ti->var2_list = NULL;
        }
        t->term_next[1] = ti->tuple;
        t->term_next_index[1] = ti->index;
        ti->tuple = t;
        ti->index = 1;
    }
}

void print_term_assignments(struct learn_info *info)
{
    struct term_info_list *t;
    int i;
    for (i = 0; i < TERM_HASH; ++i) {
        t = info->tuples_by_term[i];
        while (t) {
            if (t->assignment != _ex_true) {
                printf("Term: %s", _th_print_exp(t->term));
                printf(" <<%s>>\n", _th_print_exp(t->assignment));
            }
            t = t->next;
        }
    }
}

void check_unates(struct learn_info *info, struct parent_list *list, char *place)
{
    struct tuple *tuple, *unates;
    struct term_info_list *ti;
    int i, j;
    int errors = 0;

    tuple = info->tuples;

    if (list != NULL) {
        while (list && list != info->unate_tail) {
            list = list->next;
        }
    }
    while (tuple) {
        if (tuple->var1==-1 || tuple->var2==-1) {
            for (i = 0; i < tuple->size; ++i) {
                if (i != tuple->var1 && i != tuple->var2) {
                    if (tuple->term_info[i]->assignment==NULL) {
                        fprintf(stderr, "Structure error 1: tuple %x has var1==-1 || var2==-1 and another unassigned term.\n");
                        exit(1);
                    }
                }
            }
            //if (tuple->var1!=-1||tuple->var2!=-1) {
            //    int agree = 1;
            //    for (i = 0; i < tuple->size; ++i) {
            //    }
            //}
        }
        j = -1;
        for (i = 0; i < tuple->size; ++i) {
            if (tuple->term_info[i]->assignment==NULL) {
                if (j==-1) {
                    j = i;
                } else {
                    goto cont;
                }
            }
            if (tuple->terms[i]->type==EXP_APPL && tuple->terms[i]->u.appl.functor==INTERN_NOT) {
                if (tuple->term_info[i]->assignment==_ex_true) goto cont;
            } else {
                if (tuple->term_info[i]->assignment==_ex_false) goto cont;
            }
        }
        if (j < 0) {
            fprintf(stderr, "Tuple completely assigned\n");
            for (i = 0; i < tuple->size; ++i) {
                fprintf(stderr, "    %s ", _th_print_exp(tuple->terms[i]));
                fprintf(stderr, " (%s)\n", _th_print_exp(tuple->term_info[i]->assignment));
            }
            errors = 1;
            goto cont;
        }
        unates = info->unates;
        while (unates) {
            if (unates==tuple) goto cont;
            unates = unates->unate_next;
        }
        fprintf(stderr, "Missing unate for tuple\n");
        for (i = 0; i < tuple->size; ++i) {
            fprintf(stderr, "    %s ", _th_print_exp(tuple->terms[i]));
            fprintf(stderr, " (%s)\n", _th_print_exp(tuple->term_info[i]->assignment));
        }
        errors = 1;
cont:
        tuple = tuple->next;
    }
    for (i = 0; i < TERM_HASH; ++i) {
        ti = info->tuples_by_term[i];
        while (ti) {
            int pcount = 0, ncount = 0;
            tuple = info->tuples;
            while (tuple) {
                if (tuple->var1 >= 0 && tuple->var2 < 0) {
                    struct _ex_intern *e = tuple->terms[tuple->var1];
                    if (ti->term==e || (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT && ti->term==e->u.appl.args[0])) {
                        int agree = 1;
                        //printf("%s: Unate tuple(1) %x\n", place, tuple);
                        for (j = 0; j < tuple->size; ++j) {
                            if (tuple->term_info[j]->assignment==_ex_true) {
                                if (tuple->terms[j]->type==EXP_APPL && tuple->terms[j]->u.appl.functor==INTERN_NOT) agree = 0;
                                //printf("    %s -> True\n", _th_print_exp(tuple->terms[j]));
                            } else if (tuple->term_info[j]->assignment==_ex_false) {
                                if (tuple->terms[j]->type!=EXP_APPL || tuple->terms[j]->u.appl.functor!=INTERN_NOT) agree = 0;
                                //printf("    %s -> True\n", _th_print_exp(tuple->terms[j]));
                            } else {
                                //printf("    %s\n", _th_print_exp(tuple->terms[j]));
                            }
                        }
                        if (agree) {
                            if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                                e = e->u.appl.args[0];
                                if (e==ti->term) ++pcount;
                            } else {
                                if (e==ti->term) ++ncount;
                            }
                        }
                    }
                } else if (tuple->var1 < 0 && tuple->var2 >= 0) {
                    struct _ex_intern *e = tuple->terms[tuple->var2];
                    if (ti->term==e || (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT && ti->term==e->u.appl.args[0])) {
                        int agree = 1;
                        //printf("%s: Unate tuple(2) %x\n", place, tuple);
                        for (j = 0; j < tuple->size; ++j) {
                            if (tuple->term_info[j]->assignment==_ex_true) {
                                if (tuple->terms[j]->type==EXP_APPL && tuple->terms[j]->u.appl.functor==INTERN_NOT) agree = 0;
                                //printf("    %s -> True\n", _th_print_exp(tuple->terms[j]));
                            } else if (tuple->term_info[j]->assignment==_ex_false) {
                                if (tuple->terms[j]->type!=EXP_APPL || tuple->terms[j]->u.appl.functor!=INTERN_NOT) agree = 0;
                                //printf("    %s -> True\n", _th_print_exp(tuple->terms[j]));
                            } else {
                                //printf("    %s\n", _th_print_exp(tuple->terms[j]));
                            }
                        }
                        if (agree) {
                            if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                                e = e->u.appl.args[0];
                                if (e==ti->term) ++pcount;
                            } else {
                                if (e==ti->term) ++ncount;
                            }
                        }
                    }
                }
                tuple = tuple->next;
            }
            if (pcount != ti->true_implications) {
                fprintf(stderr, "%s: pcount error %d %d %s\n", place, pcount, ti->true_implications, _th_print_exp(ti->term));
                errors = 1;
            }
            if (ncount != ti->false_implications) {
                fprintf(stderr, "%s: ncount error %d %d %s\n", place, ncount, ti->false_implications, _th_print_exp(ti->term));
                errors = 1;
            }
            ti = ti->next;
        }
    }
    if (errors) {
        fprintf(stderr, "check_unates: Error exit\n");
        exit(1);
    }
}

struct _ex_intern *_th_get_assignment(struct env *env, struct learn_info *info, struct _ex_intern *e)
{
    struct term_info_list *ti;

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        e = e->u.appl.args[0];
    }

    ti = get_term_info(env, info, e, 0);

    if (ti==NULL) {
        _tree_print1("_th_get_assignment of %s is NULL", _th_print_exp(e));
        return NULL;
    }

    //_tree_print_exp("_th_get_assignment", e);
    //_tree_print_exp("is", ti->assignment);

    return ti->assignment;
}

int add_assignment(struct env *env, struct learn_info *info, struct term_info_list *ti, struct _ex_intern *value, int d)
{
    struct tuple *tuple;
    int i, j;
    int contradiction = 0;
    int agree;

    //_tree_print_exp("Actual term", ti->term);
    if (ti->assignment) {
        fprintf(stderr, "Term already has assignment %s\n", _th_print_exp(ti->term));
        exit(1);
    }
    
    //printf("unate counts %d %d\n", ti->true_implications, ti->false_implications);

    ti->decision_level = d;

    if (ti->assignment) {
        if (value==ti->assignment) return 0;
        ti->assignment = value;
    } else {
        ti->assignment = value;
        tuple = ti->var1_list;
        while (tuple) {
            struct _ex_intern *e = tuple->terms[tuple->var1];
            struct tuple *nt = tuple->var1_next;
            //printf("Processing tuple %x %d %d\n", tuple, tuple->var1, tuple->var2);
            //fflush(stdout);
            for (i = 0; i < tuple->size; ++i) {
                if (tuple->term_info[i]->assignment==NULL && i != tuple->var2) {
                    tuple->var1 = i;
                    tuple->var1_next = tuple->term_info[i]->var1_list;
                    tuple->term_info[i]->var1_list = tuple;
                    goto cont1;
                }
            }
            j = tuple->var1;
            tuple->var1 = -1;
            agree = 1;
            for (i = 0; i < tuple->size; ++i) {
                if (tuple->term_info[i]->assignment==_ex_true) {
                    if (tuple->terms[i]->type==EXP_APPL && tuple->terms[i]->u.appl.functor==INTERN_NOT) {
                        agree = 0;
                    }
                } else if (tuple->term_info[i]->assignment==_ex_false) {
                    if (tuple->terms[i]->type!=EXP_APPL || tuple->terms[i]->u.appl.functor!=INTERN_NOT) {
                        agree = 0;
                    }
                }
            }
            if (tuple->var2==-1) {
                if (agree) {
                    contradiction = 1;
                    //printf("Contradiction\n");
                    //for (i = 0; i < tuple->size; ++i) {
                    //    printf("    %s", _th_print_exp(tuple->terms[i]));
                    //    printf(" (%s)\n", _th_print_exp(tuple->term_info[i]->assignment));
                    //}
                    ++tuple->used_count;
                    _zone_print0("_th_add_asignment contradiction 1");
                    //_tree_indent();
                    //for (i = 0; i < tuple->size; ++i) {
                    //    _tree_print_exp("r", tuple->terms[i]);
                    //}
                    //_tree_undent();
                }
                if (tuple->unate_prev ||info->unates==tuple) {
                    if (tuple->unate_next) {
                        tuple->unate_next->unate_prev = tuple->unate_prev;
                    }
                    if (tuple->unate_prev) {
                        tuple->unate_prev->unate_next = tuple->unate_next;
                    } else {
                        info->unates = tuple->unate_next;
                        //printf("setting info->unates 1 %x\n", info->unates);
                    }
                    if (tuple->terms[j]->type==EXP_APPL && tuple->terms[j]->u.appl.functor==INTERN_NOT) {
                        //printf("decrementing true %s\n", _th_print_exp(ti->term));
                        //_tree_print_exp("Decrement true", ti->term);
                        --ti->true_implications;
                    } else {
                        //printf("decrementing false %s\n", _th_print_exp(ti->term));
                        //_tree_print_exp("Decrement false 1", ti->term);
                        --ti->false_implications;
                    }
                }
                //printf("Deleting unate(a) %x\n", tuple);
            } else {
                if (agree) {
                    struct term_info_list *t;
                    tuple->unate_next = info->unates;
                    info->unates = tuple;
                    //printf("setting info->unates 2 %x\n", info->unates);
                    tuple->unate_prev = NULL;
                    if (tuple->unate_next) {
                        tuple->unate_next->unate_prev = tuple;
                    }
                    t = tuple->term_info[tuple->var2];
                    if (tuple->terms[tuple->var2]->type==EXP_APPL && tuple->terms[tuple->var2]->u.appl.functor==INTERN_NOT) {
                        //_tree_print_exp("Increment true", t->term);
                        ++t->true_implications;
                        if (t->false_implications) {
                            //int i;
                            _zone_print_exp("Contradiction 2", t->term);
                            ++tuple->used_count;
                            contradiction = 1;
                            //printf("Contradiction 2 %s %d %d\n", _th_print_exp(t->term), t->false_implications, t->true_implications);
                            //for (i = 0; i < tuple->size; ++i) {
                            //    printf("    %s", _th_print_exp(tuple->terms[i]));
                            //    printf(" (%s)\n", _th_print_exp(tuple->term_info[i]->assignment));
                            //}
                        }
                    } else {
                        //_tree_print_exp("Increment false", t->term);
                        ++t->false_implications;
                        if (t->true_implications) {
                            //int i;
                            //printf("Contradiction 3\n");
                            //for (i = 0; i < tuple->size; ++i) {
                            //    printf("    %s", _th_print_exp(tuple->terms[i]));
                            //    printf(" (%s)\n", _th_print_exp(tuple->term_info[i]->assignment));
                            //}
                            _zone_print_exp("Contradiction 3", t->term);
                            ++tuple->used_count;
                            contradiction = 1;
                        }
                    }
                    //printf("Adding unate(a) %x %s\n", tuple, _th_print_exp(t->term));
                } else {
                    tuple->unate_next = tuple->unate_prev = NULL;
                }
            }
cont1:
            //printf("new var1 %x %d %d\n", tuple, tuple->var1, tuple->var2);
            tuple = nt;
        }
        tuple = ti->var2_list;
        while (tuple) {
            struct _ex_intern *e = tuple->terms[tuple->var1];
            struct tuple *nt = tuple->var2_next;
            //printf("Processing(b) tuple %x %d %d\n", tuple, tuple->var1, tuple->var2);
            for (i = 0; i < tuple->size; ++i) {
                if (tuple->term_info[i]->assignment==NULL && i != tuple->var1) {
                    tuple->var2 = i;
                    tuple->var2_next = tuple->term_info[i]->var2_list;
                    tuple->term_info[i]->var2_list = tuple;
                    //if (tuple->var2_next==tuple) {
                    //    fprintf(stderr, "Fail2\n");
                    //    exit(1);
                    //}
                    goto cont2;
                }
            }
            j = tuple->var2;
            tuple->var2 = -1;
            agree = 1;
            for (i = 0; i < tuple->size; ++i) {
                if (tuple->term_info[i]->assignment==_ex_true) {
                    if (tuple->terms[i]->type==EXP_APPL && tuple->terms[i]->u.appl.functor==INTERN_NOT) {
                        agree = 0;
                    }
                } else if (tuple->term_info[i]->assignment==_ex_false) {
                    if (tuple->terms[i]->type!=EXP_APPL || tuple->terms[i]->u.appl.functor!=INTERN_NOT) {
                        agree = 0;
                    }
                }
            }
            if (tuple->var1==-1) {
                if (agree) {
                    //int i;
                    //printf("Contradiction 4\n");
                    //for (i = 0; i < tuple->size; ++i) {
                    //    printf("    %s", _th_print_exp(tuple->terms[i]));
                    //    printf(" (%s)\n", _th_print_exp(tuple->term_info[i]->assignment));
                    //}
                    contradiction = 1;
                    ++tuple->used_count;
                    _zone_print0("_th_add_asignment contradiction 4");
                    //_tree_indent();
                    //for (i = 0; i < tuple->size; ++i) {
                    //    _tree_print_exp("r", tuple->terms[i]);
                    //}
                    //_tree_undent();
                }
                if (tuple->unate_prev || info->unates==tuple) {
                    if (tuple->unate_next) {
                        tuple->unate_next->unate_prev = tuple->unate_prev;
                    }
                    if (tuple->unate_prev) {
                        tuple->unate_prev->unate_next = tuple->unate_next;
                    } else {
                        info->unates = tuple->unate_next;
                        //printf("setting info->unates 3 %x\n", info->unates);
                    }
                    if (tuple->terms[j]->type==EXP_APPL && tuple->terms[j]->u.appl.functor==INTERN_NOT) {
                        //printf("decrementing true %s\n", _th_print_exp(ti->term));
                        --ti->true_implications;
                        //_tree_print_exp("Decrement true", ti->term);
                    } else {
                        //printf("decrementing false %s\n", _th_print_exp(ti->term));
                        --ti->false_implications;
                        //_tree_print_exp("Decrement false 2", ti->term);
                    }
                }
                //printf("Deleting unate(b) %x\n", tuple);
            } else {
                if (agree) {
                    struct term_info_list *t;
                    tuple->unate_next = info->unates;
                    info->unates = tuple;
                    //printf("setting info->unates 4 %x\n", info->unates);
                    tuple->unate_prev = NULL;
                    if (tuple->unate_next) {
                        tuple->unate_next->unate_prev = tuple;
                    }
                    t = tuple->term_info[tuple->var1];
                    if (tuple->terms[tuple->var1]->type==EXP_APPL && tuple->terms[tuple->var1]->u.appl.functor==INTERN_NOT) {
                        //_tree_print_exp("Increment true", t->term);
                        ++t->true_implications;
                        if (t->false_implications) {
                            _zone_print_exp("Contradiction 5", t->term);
                            //_tree_print("cont %x %d %d", t, t->true_implications, t->false_implications);
                            //_tree_indent();
                            //for (i = 0; i < tuple->size; ++i) {
                            //    _tree_print_exp("r", tuple->terms[i]);
                            //}
                            //_tree_undent();
                            ++tuple->used_count;
                            contradiction = 1;
                        }
                    } else {
                        //_tree_print_exp("Increment false", t->term);
                        //int i;
                        //printf("Contradiction 5\n");
                        //for (i = 0; i < tuple->size; ++i) {
                        //    printf("    %s", _th_print_exp(tuple->terms[i]));
                        //    printf(" (%s)\n", _th_print_exp(tuple->term_info[i]->assignment));
                        //}
                        ++t->false_implications;
                        if (t->true_implications) {
                            _zone_print_exp("Contradiction 6", t->term);
                            ++tuple->used_count;
                            contradiction = 1;
                        }
                    }
                    //printf("var1, var2 = %d %d\n", tuple->var1, tuple->var2);
                    //printf("Adding unate(b) %x %s\n", tuple, _th_print_exp(t->term));
                } else {
                    tuple->unate_next = tuple->unate_prev = NULL;
                }
            }
cont2:
            //printf("new var2 %x %d %d\n", tuple, tuple->var1, tuple->var2);
            tuple = nt;
        }
    }

    //if (!contradiction) check_unates(info, NULL, "after add");

    return contradiction;
}

int _th_add_assignment(struct env *env, struct learn_info *info, struct _ex_intern *e, int d)
{
    struct _ex_intern *value = _ex_true;
    struct term_info_list *ti;

    //_tree_print_exp("Adding assignment", e);

    //printf("Adding %s\n", _th_print_exp(e));
    //check_unates(info, NULL, "before add");

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        e = e->u.appl.args[0];
        value = _ex_false;
    }

    //printf("Add assignment %s\n", _th_print_exp(e));
    ti = get_term_info(env, info, e, 0);
    if (ti==NULL) {
        return 0;
    }

    return add_assignment(env,info,ti,value,d);
}

struct env *_th_learn_get_env(struct learn_info *info)
{
    return info->env;
}

int _th_create_add_assignment(struct env *env, struct learn_info *info, struct _ex_intern *e, int d)
{
    struct _ex_intern *value = _ex_true;
    struct term_info_list *ti;

    //_tree_print_exp("Adding assignment", e);

    //printf("Adding %s\n", _th_print_exp(e));
    //check_unates(info, NULL, "before add");

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        e = e->u.appl.args[0];
        value = _ex_false;
    }

    //printf("Add assignment %s\n", _th_print_exp(e));
    ti = get_term_info(env, info, e, 1);

    return add_assignment(env,info,ti,value,d);
}

void _th_delete_assignment(struct env *env, struct learn_info *info, struct _ex_intern *e)
{
    struct term_info_list *ti;
    int index, n;
    struct tuple *tuple;
    int i;

    //_tree_print_exp("Deleting assignment", e);

    //check_unates(info, NULL, "before delete");

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) e = e->u.appl.args[0];

    //printf("Delete assignment\n");
    ti = get_term_info(env, info, e, 0);
    if (ti==NULL) return;
    if (ti->assignment==NULL) {
        return;
        //fprintf(stderr, "Error: deleting empty assignment %s\n", _th_print_exp(e));
        //exit(1);
    }
    ti->var1_list = NULL;
    ti->var2_list = NULL;
    ti->assignment = NULL;

    tuple = ti->tuple;
    index = ti->index;
    while (tuple) {
        //printf("Delete processing %x %d %d\n", tuple, tuple->var1, tuple->var2);
        if (tuple->var1==-1) {
            tuple->var1 = index;
            tuple->var1_next = ti->var1_list;
            ti->var1_list = tuple;
            if (tuple->var2 >= 0) {
                struct _ex_intern *e = tuple->terms[tuple->var2];
                if (info->unates==tuple || tuple->unate_prev != NULL) {
                    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                        --tuple->term_info[tuple->var2]->true_implications;
                    } else {
                        --tuple->term_info[tuple->var2]->false_implications;
                    }
                    if (tuple->unate_prev) {
                        tuple->unate_prev->unate_next = tuple->unate_next;
                    } else {
                        info->unates = info->unates->unate_next;
                        //printf("setting info->unates 5 %x\n", info->unates);
                    }
                    if (tuple->unate_next) {
                        tuple->unate_next->unate_prev = tuple->unate_prev;
                    }
                    //printf("Deleting unate %x\n", tuple);
                }
            } else {
                int agree = 1;
                for (i = 0; i < tuple->size; ++i) {
                    if (tuple->term_info[i]->assignment==_ex_true) {
                        if (tuple->terms[i]->type==EXP_APPL && tuple->terms[i]->u.appl.functor==INTERN_NOT) {
                            agree = 0;
                        }
                    } else if (tuple->term_info[i]->assignment==_ex_false) {
                        if (tuple->terms[i]->type!=EXP_APPL || tuple->terms[i]->u.appl.functor!=INTERN_NOT) {
                            agree = 0;
                        }
                    }
                }
                if (agree) {
                    struct term_info_list *t;
                    tuple->unate_next = info->unates;
                    info->unates = tuple;
                    //printf("setting info->unates 6 %x\n", info->unates);
                    tuple->unate_prev = NULL;
                    if (tuple->unate_next) {
                        tuple->unate_next->unate_prev = tuple;
                    }
                    t = tuple->term_info[tuple->var1];
                    if (tuple->terms[tuple->var1]->type==EXP_APPL && tuple->terms[tuple->var1]->u.appl.functor==INTERN_NOT) {
                        ++t->true_implications;
                    } else {
                        ++t->false_implications;
                    }
                    //printf("Adding unate %x\n", tuple);
                } else {
                    tuple->unate_next = tuple->unate_prev = NULL;
                }
            }
            //printf("del new var1 %x %d %d\n", tuple, tuple->var1, tuple->var2);
        } else if (tuple->var2==-1) {
            tuple->var2 = index;
            tuple->var2_next = ti->var2_list;
            //if (tuple->var2_next==tuple) {
            //    fprintf(stderr, "Fail3\n");
            //    exit(1);
            //}
            ti->var2_list = tuple;
            if (tuple->var1 >= 0) {
                struct _ex_intern *e = tuple->terms[tuple->var1];
                if (info->unates==tuple || tuple->unate_prev != NULL) {
                    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                        --tuple->term_info[tuple->var1]->true_implications;
                    } else {
                        --tuple->term_info[tuple->var1]->false_implications;
                    }
                    if (tuple->unate_prev) {
                        tuple->unate_prev->unate_next = tuple->unate_next;
                    } else {
                        info->unates = info->unates->unate_next;
                        //printf("setting info->unates 7 %x\n", info->unates);
                    }
                    if (tuple->unate_next) {
                        tuple->unate_next->unate_prev = tuple->unate_prev;
                    }
                }
            } else {
                int agree = 1;
                for (i = 0; i < tuple->size; ++i) {
                    if (tuple->term_info[i]->assignment==_ex_true) {
                        if (tuple->terms[i]->type==EXP_APPL && tuple->terms[i]->u.appl.functor==INTERN_NOT) {
                            agree = 0;
                        }
                    } else if (tuple->term_info[i]->assignment==_ex_false) {
                        if (tuple->terms[i]->type!=EXP_APPL || tuple->terms[i]->u.appl.functor!=INTERN_NOT) {
                            agree = 0;
                        }
                    }
                }
                if (agree) {
                    struct term_info_list *t;
                    tuple->unate_next = info->unates;
                    info->unates = tuple;
                    //printf("setting info->unates 8 %x\n", info->unates);
                    tuple->unate_prev = NULL;
                    if (tuple->unate_next) {
                        tuple->unate_next->unate_prev = tuple;
                    }
                    t = tuple->term_info[tuple->var1];
                    if (tuple->terms[tuple->var1]->type==EXP_APPL && tuple->terms[tuple->var1]->u.appl.functor==INTERN_NOT) {
                        ++t->true_implications;
                    } else {
                        ++t->false_implications;
                    }
                } else {
                    tuple->unate_next = tuple->unate_prev = NULL;
                }
            }
            //printf("del new var2 %x %d %d\n", tuple, tuple->var1, tuple->var2);
        }

        n = tuple->term_next_index[index];
        tuple = tuple->term_next[index];
        index = n;
    }

    //check_unates(info, NULL, "after delete");
}

#ifdef XX
void check_structure(struct learn_info *info)
{
    struct tuple *tuple;
    int i, var;

    tuple = info->tuples;

    while (tuple) {
        tuple = tuple->next;
        if (tuple->var1==-1 || tuple->var2==-1) {
            for (i = 0; i < tuple->size; ++i) {
                if (i != tuple->var1 && i != tuple->var2) {
                    if (tuple->term_info[i]->assignment==NULL) {
                        fprintf(stderr, "Structure error 1: tuple %x has var1==1 || var2==-1 and another unassigned term.\n");
                        exit(1);
                    }
                }
            }
            if (tuple->var1!=-1||tuple->var2!=-1) {
                int agree = 1;
                for (i = 0; i < tuple->size; ++i) {
                }
            }
        }
    }
}
#endif

static int basic_term(struct _ex_intern *e)
{
    if (e->type != EXP_APPL) return 1;
    if (e->u.appl.functor != INTERN_AND && e->u.appl.functor != INTERN_OR &&
        e->u.appl.functor != INTERN_ITE && e->u.appl.functor != INTERN_NOT &&
        e->u.appl.functor != INTERN_XOR) return 1;
    return 0;
}

int _th_add_tuple_from_list(struct env *env, struct learn_info *info, struct add_list *list)
{
    int count;
    struct add_list *l;
    struct _ex_intern **args;

    l = list;
    count = 0;
    while (l) {
        ++count;
        l = l->next;
    }
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
    count = 0;
    l = list;
    while (l) {
        args[count++] = l->e;
        l = l->next;
    }
    return add_group(env,info,count,args,0);
}

struct _ex_intern *_th_transfer_to_learn(struct env *env, struct learn_info *info,struct parent_list *list, struct _ex_intern *e)
{
    struct _ex_intern **args;
    int i, j, k;
    struct _ex_intern *f;
    static int trcount = 0;

    //printf("Transfer to learn %s\n", _th_print_exp(e));

    //pl = list;
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_AND) {
        e = _ex_intern_appl1_env(env,INTERN_OR,e);
    }
    if (e->type != EXP_APPL || e->u.appl.functor != INTERN_OR) return e;

    //printf("transfer: %s\n", _th_print_exp(e));

    //for (i = 0; i < e->u.appl.count; ++i) {
    //    if (e->u.appl.functor==INTERN_RAT_PLUS) {
    //        fprintf(stderr, "Illegal arg %s\n", _th_print_exp(e));
    //        exit(1);
    //    }
    //}

    while (list) {
        if (!list->unate) return e;
        list = list->next;
    }

    //++_th_block_complex;
    _zone_print2("Transfering to learn %d %s", ++trcount, _th_print_exp(e));
    //--_th_block_complex;
    _tree_indent();

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);

    for (i = 0, j = 0; i < e->u.appl.count; ++i) {
        int count;
        f = e->u.appl.args[i];
        if (f->type==EXP_APPL && f->u.appl.functor==INTERN_AND) {
            struct _ex_intern **args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * f->u.appl.count);
            for (k = 0; k < f->u.appl.count; ++k) {
                struct _ex_intern *g = f->u.appl.args[k];
                //if (g->type!=EXP_VAR && (g->type!=EXP_APPL || g->u.appl.functor!=INTERN_NOT || g->u.appl.args[0]->type!=EXP_VAR)) {
                //    //int i = 0;
                //    printf("g = %d %s\n", trcount, _th_print_exp(g));
                //    //i = 1/i;
                //    exit(1);
                //}
                if (!basic_term(g) && (g->type != EXP_APPL || g->u.appl.functor != INTERN_NOT || !basic_term(g->u.appl.args[0]))) {
                    goto cont;
                }
                args2[k] = g;
            }
            //for (k = 0; k < f->u.appl.count; ++k) {
                //args2[k] = _th_simp(env,args2[k]);
                //printf("Adding at %d args2[%d] %s\n", _tree_zone, k, _th_print_exp(args2[k]));
            //}
            count = f->u.appl.count;
            //printf("Round\n");
            for (k = 0; k < count; ++k) {
                args2[k] = _th_nc_rewrite(env,args2[k]);
                //printf("args2[%d] = %s\n", k, _th_print_exp(args2[k]));
                if (args2[k]==_ex_false) goto cont1;
                if (args2[k]==_ex_true) {
                    args2[k--] = args2[--count];
                }
            }
            add_group(env,info,count,args2,0);
cont1:;
        } else {
cont:
            args[j++] = f;
        }
    }

    _tree_undent();

    if (j==0) return _ex_false;
    if (j==1) return args[0];
    return _ex_intern_appl_env(env,INTERN_OR,j,args);
}

struct learn_info *_th_new_learn_info(struct env *env)
{
    int i;
    struct learn_info *learn = (struct learn_info *)_th_alloc(HEURISTIC_SPACE,sizeof(struct learn_info));

    learn->tuples = NULL;
    for (i = 0; i < TERM_HASH; ++i) {
        learn->tuples_by_term[i] = NULL;
    }
    learn->generalized_tuples = 0;
    learn->learns = 0;
    learn->add_count = 0;
	learn->bump_size = 1;
	learn->term_count = 0;
    learn->env = _th_default_env(HEURISTIC_SPACE);
	_th_copy_var_types(learn->env, env);
    learn->unates = NULL;
    learn->share_hash = (struct pair_list **)_th_alloc(HEURISTIC_SPACE,sizeof(struct pair_list *) * SHARE_SIZE);
    for (i = 0; i < SHARE_SIZE; ++i) {
        learn->share_hash[i] = NULL;
    }

#ifdef XX
    while (terms != NULL) {
        struct dependencies *d = terms->dependencies;
        struct _ex_intern *e = terms->e;
        while (d != NULL) {
            if (d->reduction==_ex_true) {
                struct _ex_intern *t = d->term->e;
                if (t->type==EXP_APPL && t->u.appl.functor==INTERN_NOT) {
                    t = t->u.appl.args[0];
                } else {
                    t = _ex_intern_appl1_env(env,INTERN_NOT,t);
                }
                add_pair(env,learn,e,t);
            } else if (d->reduction==_ex_false) {
                add_pair(env,learn,e,d->term->e);
            }
            d = d->next;
        }
        d = terms->neg_dependencies;
        e = terms->e;
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
            e = e->u.appl.args[0];
        } else {
            e = _ex_intern_appl1_env(env,INTERN_NOT,e);
        }
        while (d != NULL) {
            if (d->reduction==_ex_true) {
                struct _ex_intern *t = d->term->e;
                if (t->type==EXP_APPL && t->u.appl.functor==INTERN_NOT) {
                    t = t->u.appl.args[0];
                } else {
                    t = _ex_intern_appl1_env(env,INTERN_NOT,t);
                }
                add_pair(env,learn,e,t);
            } else if (d->reduction==_ex_false) {
                add_pair(env,learn,e,d->term->e);
            }
            d = d->next;
        }
        terms = terms->next;
    }
#endif

    learn->have_unate_tail = 0;
    learn->unate_tail = NULL;

    //dinfo = learn;

    return learn;
}

static int all_unates(struct parent_list *l)
{
    while (l) {
        if (!l->unate) return 0;
        l = l->next;
    }
    return 1;
}

static int good_tuple(struct env *env, struct learn_info *info, int count, struct _ex_intern **args, struct parent_list *gen, struct _ex_intern *exp)
{
    char *mark = _th_alloc_mark(REWRITE_SPACE);
    int i;
    struct parent_list *pl;
    struct _ex_intern *push;
    //struct _ex_intern *e;
    int ret = 0;

    _zone_print0("good tuple");
    _tree_indent();

    for (i = 0; i < count; ++i) {
        pl = (struct parent_list *)_th_alloc(REWRITE_SPACE,sizeof(struct parent_list));
        pl->next = gen;
        pl->split = args[i];
    }

#ifdef XX
    push = e = _th_learned_unate_case(env,info,pl);
    if (push) {
        _th_derive_push(env);
    }
    while (e) {
        struct _ex_intern *p = _th_derive_prepare(env,_th_mark_vars(env,e));
        _zone_print_exp("Adding learned unate", e);
        _th_derive_add_prepared(env,p);
        p->rule_original = 1;
        pl = (struct parent_list *)_th_alloc(REWRITE_SPACE,sizeof(struct parent_list));
        pl->next = gen;
        pl->split = args[i];
        e = _th_learned_unate_case(env,info,pl);
    }
#endif
    push = NULL;

    exp = _th_nc_rewrite(env,exp);

    if (exp==_ex_true) {
        ret = 1;
    }

#ifdef XX
    if (push) {
        _th_derive_pop(env);
        while(pl) {
            struct _ex_intern *p = _th_derive_prepare(env,_th_mark_vars(env,pl->split));
            p->rule_original = 0;
            pl = pl->next;
        }
    }
#endif

    _th_alloc_release(REWRITE_SPACE,mark);

    _tree_undent();
    return ret;
}

static struct _ex_intern *find_failure(struct env *env, struct learn_info *info, struct parent_list *list)
{
    struct _ex_intern *e;
    //struct _ex_intern *r;
    //struct rule *cr;

    if (info->unate_tail) {
        e = _th_nc_rewrite(env,info->unate_tail->exp);
        return info->unate_tail->exp;
    } else {
        while (list->next) {
            list = list->next;
        }
        e = _th_nc_rewrite(env,list->exp);
        return list->exp;
    }

#ifdef XX
    r = _th_get_first_context_rule(env, &cr);
    while (r != NULL) {
        _zone_print_exp("Checking rule", r);
        _tree_indent();
        if (r->rule_original) {
            r->rule_original = 0;
            e = _th_nc_rewrite(env,_th_unmark_vars(env,r));
            r->rule_original = 1;
            if (e==_ex_false) {
                _tree_undent();
                return _ex_intern_appl1_env(env,INTERN_NOT,_th_unmark_vars(env,r));
            }
        }
        _tree_undent();
        r = _th_get_next_rule(env,&cr);
    }
#endif

//#ifdef _DEBUG
//    exit(1);
//#endif

    return NULL;
}

static int has_learned_unate(struct learn_info *info, struct _ex_intern *exp)
{
    struct tuple *t = info->tuples;

    while (t) {
        if (t->size==1 && t->terms[0]==exp) return 1;
        t = t->next;
    }

    return 0;
}

static int check_unate_contradiction(struct env *env, struct learn_info *info, struct _ex_intern *exp)
{
    struct tuple *t = info->tuples;
    int ret;

    _th_derive_push(env);

    while (t) {
        if (t->size==1) {
            struct _ex_intern *e = t->terms[0];
            if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                e = e->u.appl.args[0];
            } else {
                e = _ex_intern_appl1_env(env,INTERN_NOT,e);
            }
            _th_assert_predicate(env,e);
        }
        t = t->next;
    }
    ret = (_th_nc_rewrite(env,exp)==_ex_true);

    _th_derive_pop(env);

    return ret;
}

static int share_variables(struct learn_info *info, struct _ex_intern *t1, struct _ex_intern *t2)
{
    int count;
    unsigned *fv;
    int i;
    int hash = (((int)t1)+((int)t2))%SHARE_SIZE;
    int res = 0;
    struct pair_list *p = info->share_hash[hash];

    while (p) {
        if ((p->e1==t1 && p->e2==t2) ||
            (p->e2==t1 && p->e1==t2)) return p->share;
        p = p->next;
    }

    fv = _th_get_free_vars(t1, &count);
    for (i = 0; i < count; ++i) {
        if (_th_is_free_in(t2, fv[i])) {
            res = 1;
            goto cont;
        }
    }

cont:
    p = (struct pair_list *)_th_alloc(HEURISTIC_SPACE,sizeof(struct pair_list));
    p->next = info->share_hash[hash];
    info->share_hash[hash] = p;
    p->e1 = t1;
    p->e2 = t2;
    p->share = res;

    return res;
}

int _th_cycle_limit = 50;

static int brute_force_domain_antecedant(struct env *env, struct learn_info *info, struct parent_list *list, struct _ex_intern *e)
{
    struct parent_list *l;
    int count;
    struct _ex_intern **args, **old_args;
    int *use;
    int i, j, k, n;
#ifndef FAST
    int za = _zone_active();
#endif

    _tree_print0("domain antecedant");
    _tree_indent();

    //pl = list;

    //printf("**** DOMAIN ANTECEDANT ****\n");

    l = list;
    count = 0;
    while (l) {
        ++count;
        l = l->next;
    }

    ++count;
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
    old_args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
    use = (int *)ALLOCA(sizeof(int) * count);
    l = list;
    for (i = 0; i < count-1; ++i) {
        old_args[i] = l->split;
        use[i] = 1;
        l = l->next;
    }
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        old_args[i] = e->u.appl.args[0];
    } else {
        old_args[i] = _ex_intern_appl1_env(env,INTERN_NOT,e);
    }
    args[0] = old_args[0];
    old_args[0] = NULL;
    list = list->next;
    n = 1;
    k = 0;
    for (i = 0; i < n; ++i) {
        for (j = 0; j < count; ++j) {
            if (old_args[j] && share_variables(info,old_args[j],args[i])) {
                args[n++] = old_args[j];
                old_args[j] = NULL;
            }
        }
    }

    count = n;

    for (i = 0; i < count; ++i) {
        l = info->unate_tail;
        while (l) {
            if (args[i]==l->split) args[i] = NULL;
            l = l->next;
        }
    }

    for (i = 0, j = 0; i < count; ++i) {
        if (args[i]) {
            args[j++] = args[i];
        }
    }

    count = j;

    _th_remove_cache(env);
    _th_install_cache(info->env);

    j = 0;
    k = count;

#ifndef FAST
    //if (za) {
        _tree_print1("count = %d", count);
        _tree_indent();
        for (i = 0; i < count; ++i) {
            _tree_print_exp("term", args[i]);
        }
        _tree_undent();
    //}
#endif

    for (n = 0; n < _th_cycle_limit; n += 2) {
#ifdef CYCLE
        _th_derive_push(info->env);

        //printf("*** CYCLE\n");

        _tree_print2("cycle %d %d", j, k);
        _tree_indent();
#ifndef FAST
        za = _zone_active();
#endif

        if (k <= j) {
            goto add_tuple;
        }

        for (i = 0; i < j; ++i) {
            if (args[i]) {
                _zone_print1("Adding %d", i);
                _tree_indent();
                if (_th_assert_predicate(info->env,args[i])) {
                    _tree_undent();
                    goto add_tuple;
                }
#ifndef FAST
                //if (za) _th_collect_and_print_classes(env,1);
#endif
                _tree_undent();
            }
        }
        for (i = k; i < count; ++i) {
            if (args[i]) {
                _zone_print1("Adding %d", i);
                _tree_indent();
                if (_th_assert_predicate(info->env,args[i])) {
                    _tree_undent();
                    goto add_tuple;
                }
#ifndef FAST
                //if (za) _th_collect_and_print_classes(env,1);
#endif
                _tree_undent();
            }
        }

        for (i = j; i < k; ++i) {
            _zone_print1("Asserting %d", i);
            _tree_indent();
            if (args[i] != NULL && _th_assert_predicate(info->env,args[i])) {
                int m = i+1;
                while (m < k) {
                    _tree_print1("NULL out %d", m);
                    args[m++] = NULL;
                }
                _tree_print1("New end %d", i);
                k = i;
                _th_derive_pop(info->env);
                _tree_undent();
                goto cont1;
            }
#ifndef FAST
            //if (za) _th_collect_and_print_classes(env,1);
#endif
            _tree_undent();
        }
        //fprintf(stderr, "domain_antecedant: Internal error 1\n");
        //exit(1);
        _th_derive_pop(info->env);
        _th_remove_cache(info->env);
        _th_install_cache(env);
        _zone_print0("Failure 1");
        _tree_undent();
        _tree_undent();
        return 0;
cont1:
#endif
        _th_derive_push(info->env);

        //printf("*** CYCLE\n");

        if (k <= j) {
            goto add_tuple;
        }
        _tree_undent();

        _tree_print2("back cycle %d %d", j, k);
        _tree_indent();
#ifndef FAST
        za = _zone_active();
#endif

        for (i = 0; i < j; ++i) {
            if (args[i]) {
                _zone_print1("Adding %d", i);
                _tree_indent();
                if (_th_assert_predicate(info->env,args[i])) {
                    _tree_undent();
                    goto add_tuple;
                }
#ifndef FAST
                //if (za) _th_collect_and_print_classes(env,1);
#endif
                _tree_undent();
            }
        }
        for (i = k; i < count; ++i) {
            if (args[i]) {
                _zone_print1("Adding %d", i);
                _tree_indent();
                if (_th_assert_predicate(info->env,args[i])) {
                    _tree_undent();
                    goto add_tuple;
                }
#ifndef FAST
                //if (za) _th_collect_and_print_classes(env,1);
#endif
                _tree_undent();
            }
        }

        for (i = k-1; i >= j; --i) {
            _zone_print1("Asserting %d", i);
            _tree_indent();
            if (args[i] != NULL && _th_assert_predicate(info->env,args[i])) {
                int m = j;
                while (m < i) {
                    _tree_print1("NULL out %d", m);
                    args[m++] = NULL;
                }
                j = i+1;
                _tree_print1("New begin %d", j);
                _th_derive_pop(info->env);
                _tree_undent();
                goto cont2;
            }
#ifndef FAST
            //if (za) _th_collect_and_print_classes(env,1);
#endif
            _tree_undent();
        }
        //fprintf(stderr, "domain_antecedant: Internal error 2\n");
        //exit(1);
        _th_derive_pop(info->env);
        _th_remove_cache(info->env);
        _th_install_cache(env);
        _zone_print0("Failure 2");
        _tree_undent();
        _tree_undent();
        return 0;
cont2:;
        _tree_undent();

    }

    j = k = 0;
    _tree_indent();

add_tuple:
    _th_derive_pop(info->env);
    _tree_undent();

    _th_remove_cache(info->env);
    _th_install_cache(env);

    for (i = 0, n = 0; i < j; ++i) {
        if (args[i]) args[n++] = args[i];
    }
    for (i = k; i < count; ++i) {
        if (args[i]) args[n++] = args[i];
    }

    _tree_undent();
    if (n < count) {
        while (list && list != info->unate_tail) {
            list->used_in_learn = 0;
            for (i = 0; i < n; ++i) {
                if (list->split==args[i]) {
                    list->used_in_learn = 1;
                    goto cont3;
                }
            }
cont3:
            list = list->next;
        }

        return add_group(env,info,n,args,2);
    } else {
        return 0;
    }
}

//#define SANITY_CHECK
int _th_quit_on_no_antecedant = 1;

static int domain_antecedant(struct env *env, struct learn_info *info, struct parent_list *list, struct _ex_intern *e)
{
    struct add_list *explanation;
    struct add_list *expl;
    struct parent_list *l;
    struct _ex_intern **args;
    int count, i, j;
#ifdef SANITY_CHECK
    int start_count;
#endif
    struct _ex_intern *ne;
    int fail = 0;
    char *mark;

    _tree_print_exp("Domain antecedant of", e);
    _tree_indent();

    //pl = list;

    //printf("Domain antecedant\n");
    //printf("Here d0\n");
    //fflush(stdout);

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        ne = e->u.appl.args[0];
    } else {
        ne = _ex_intern_appl1_env(env,INTERN_NOT,e);
    }

    //printf("Here d1\n");
    //fflush(stdout);

    //printf("Retrieving explanation for %s\n", _th_print_exp(e));
    //fflush(stdout);

    //explanation = _th_retrieve_explanation(env,e);
	if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
		explanation = ne->explanation;
		if (explanation==NULL) {
    		struct _ex_intern *r = _th_check_cycle_rless(env,ne,&explanation);
			if (r != _ex_false) {
				explanation = NULL;
			}
		}
	} else {
		explanation = e->explanation;
		if (explanation==NULL) {
    		struct _ex_intern *r = _th_check_cycle_rless(env,e,&explanation);
			if (r != _ex_true) {
				explanation = NULL;
			}
		}
	}
    _tree_print_exp("Retrieving explanation for", e);
    if (explanation==NULL || (e->type==EXP_APPL &&
        (e->u.appl.functor==INTERN_AND || e->u.appl.functor==INTERN_OR || e->u.appl.functor==INTERN_ITE) && explanation->next==NULL &&
        explanation->e==e)) {
	    //struct add_list *al;
		//struct _ex_intern *l;
		int i = 0;
        fprintf(stderr, "No explanation 3 for %s\n", _th_print_exp(e));
#ifdef PRINT1
		fprintf(stderr, "explanation %s\n", _th_print_exp(explanation));
		fprintf(stderr, "e->merge = %s\n", _th_print_exp(e->merge));
		al = e->explanation;
		while (al) {
			fprintf(stderr, "    %s\n", _th_print_exp(al->e));
			al = al->next;
		}
		fprintf(stderr, "e->u.appl.args[0]->merge = %s\n", _th_print_exp(e->u.appl.args[0]->merge));
		al = e->u.appl.args[0]->explanation;
		while (al) {
			fprintf(stderr, "    %s\n", _th_print_exp(al->e));
			al = al->next;
		}
		fprintf(stderr, "e->u.appl.args[1]->merge = %s\n", _th_print_exp(e->u.appl.args[1]->merge));
		al = e->u.appl.args[1]->explanation;
		while (al) {
			fprintf(stderr, "    %s\n", _th_print_exp(al->e));
			al = al->next;
		}
		fprintf(stderr, "%s\n", _th_print_exp(_ex_true->merge));
		fprintf(stderr, "%s\n", _th_print_exp(_ex_false->merge));
		al = _ex_false->explanation;
		while (al) {
			fprintf(stderr, "    %s\n", _th_print_exp(al->e));
			al = al->next;
		}
		l = e->u.appl.args[0];
        fprintf(stderr, "Left\n");
		while (l) {
			fprintf(stderr, "    %s\n", _th_print_exp(l));
			l = l->merge;
		}
		l = e->u.appl.args[1];
        fprintf(stderr, "Right\n");
		while (l) {
			fprintf(stderr, "    %s\n", _th_print_exp(l));
			l = l->merge;
		}
#endif
		while (list) {
			printf("assertion %s\n", _th_print_exp(list->split));
			list = list->next;
		}
		_th_display_difference_table(env);
		//i = 1 / i;
		exit(1);
        return 0;
    }
    _tree_print0("Has explanation");

    //printf("Here d2\n");
    //fflush(stdout);


    ne->user2 = _ex_true;

    //printf("Here d3\n");
    //fflush(stdout);

    expl = explanation;
    _tree_print0("Complete explanation");
    _tree_indent();
    while (expl) {
        _tree_print_exp("expl", expl->e);
        expl->e->user2 = NULL;
        expl = expl->next;
    }
    _tree_undent();
    l = info->unate_tail;
    while (l) {
        l->split->user2 = _ex_true;
        l = l->next;
    }
    count = 0;
    expl = explanation;
    while (expl) {
        if (!expl->e->user2) {
            //_zone_print_exp("used expl", expl->e);
            ++count;
            expl->e->user2 = _ex_true;
        }
        expl = expl->next;
    }
    //printf("count(a) = %d\n", count);
    expl = explanation;
    while (expl) {
        expl->e->user2 = NULL;
        expl = expl->next;
    }
    l = info->unate_tail;
    while (l) {
        l->split->user2 = _ex_true;
        l = l->next;
    }

    //printf("Here d4 %d\n", count);
    //fflush(stdout);

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (count+1));

    //printf("Here d5\n");
    //fflush(stdout);

    count = 0;
    expl = explanation;
    _tree_print0("Used explanation");
    _tree_indent();
    while (expl) {
        if (!expl->e->user2) {
            //struct _ex_intern *orig = expl->e;
            //if (orig->type==EXP_APPL && orig->u.appl.functor==INTERN_NOT) {
            //    orig = _ex_intern_appl1_env(env,INTERN_NOT,orig->u.appl.args[0]->original);
            //} else {
            //    orig = expl->e->original;
            //}
            args[count++] = expl->e;
            _tree_print_exp("expl", expl->e);
            expl->e->user2 = _ex_true;
        }
        expl = expl->next;
    }
    _tree_undent();
    //printf("count(b) = %d\n", count);

    //printf("Here d6\n");
    //fflush(stdout);

    for (i = 0; i < count; ++i) {
        if (args[i]==ne) goto cont_expl;
    }
    args[count++] = ne;
cont_expl:

    for (i = 0; i < count; ++i) {
        args[i]->user2 = NULL;
    }
    ne->user2 = NULL;

    //printf("Here d7\n");
    //fflush(stdout);

    l = info->unate_tail;
    while (l) {
        l->split->user2 = NULL;
        l = l->next;
    }

    _th_remove_cache(env);
    _th_install_cache(info->env);
    mark = _th_alloc_mark(LEARN_ENV_SPACE);
    _th_derive_push(info->env);

#ifdef SANITY_CHECK
    start_count = count;
    printf("Start count %d\n", count);
    //for (i = 0; i < start_count; ++i) {
    //    printf("    %s\n", _th_print_exp(args[i]));
    //}
#endif
    //printf("Here d8\n");
    //fflush(stdout);

    //for (i = 0; i < count; ++i) {
    //    args[i] = _th_nc_rewrite(info->env,args[i]);
    //}

    for (i = count-1; i >= 0; --i) {
        if (args[i] != ne) {
            fail = 0;
            _tree_print1("Testing position %d", i);
            _tree_indent();
            _th_derive_push(info->env);
            for (j = 0; j < count; ++j) {
                if (i != j) {
                    struct _ex_intern *p = _th_simp(info->env,_th_nc_rewrite(info->env,args[j]));
                    if (p==_ex_false || _th_assert_predicate(info->env,p)) {
                        fail = 1;
                        goto finish_loop;
                    }
                }
            }
finish_loop:
            _th_derive_pop(info->env);
            _tree_undent();
            if (fail) {
                _tree_indent();
                _tree_print0("Eliminating");
                _tree_undent();
                for (j = i; j < count-1; ++j) {
                    args[j] = args[j+1];
                }
                --count;
            }
        }
    }
    //printf("Here d9\n");
    //fflush(stdout);
    _th_derive_pop(info->env);
    _th_alloc_release(LEARN_ENV_SPACE,mark);
    _th_remove_cache(info->env);
    _th_install_cache(env);

#ifdef SANITY_CHECK
    if (start_count != count) {
        l = info->unate_tail;
        while (l) {
            l->split->user2 = _ex_false;
            l = l->next;
        }
        expl = explanation;
        printf("Original explanation\n");
        while (expl) {
            if (expl->e->user2==_ex_false) {
                printf("    tail: %s\n", _th_print_exp(expl->e));
                expl->e->user2 = _ex_true;
            }
            if (!expl->e->user2) {
                printf("    %s\n", _th_print_exp(expl->e));
                expl->e->user2 = _ex_true;
            }
            expl = expl->next;
        }
        if (!ne->user2) {
            printf("    %s\n", _th_print_exp(ne));
        }
        //printf("count(a) = %d\n", count);
        expl = explanation;
        while (expl) {
            expl->e->user2 = NULL;
            expl = expl->next;
        }
        l = info->unate_tail;
        while (l) {
            l->split->user2 = _ex_true;
            l = l->next;
        }
        printf("Reduced set\n");
        for (i = 0; i < count; ++i) {
            printf("    %s\n", _th_print_exp(args[i]));
        }
    }
    l = list;
    i = 0; j = 0;
    while (l) {
        //fprintf(stderr, "l->split = %s\n", _th_print_exp(l->split));
        l->split->user2 = _ex_true;
        if (!j && l != info->unate_tail) {
            ++i;
        } else {
            j = 1;
        }
        l = l->next;
    }
    printf("%d reduced to %d\n", i, count);
    expl = explanation;
    while (expl) {
        //struct _ex_intern *orig = expl->e;
        //if (orig->type==EXP_APPL && orig->u.appl.functor==INTERN_NOT) {
        //    orig = _ex_intern_appl1_env(env,INTERN_NOT,orig->u.appl.args[0]->original);
        //} else {
        //    orig = expl->e->original;
        //}
        //if (orig->user2==NULL && expl->e->user2==NULL && expl->e != e && expl->e != ne &&
        //    orig != e && orig != ne) {
        if (expl->e->user2==NULL && expl->e != e && expl->e != ne) {
            fprintf(stderr, "ne = %s\n", _th_print_exp(ne));
            fprintf(stderr, "e = %s\n", _th_print_exp(e));
            fprintf(stderr, "Explanation term not in assertion list %s\n", _th_print_exp(expl->e));
            //fprintf(stderr, "Original: %s\n", _th_print_exp(orig));
            expl = explanation;
            while (expl) {
                fprintf(stderr, "    %s\n", _th_print_exp(expl->e));
                expl = expl->next;
            }
            printf("List:\n");
            while (list) {
                printf("    %s\n", _th_print_exp(list->split));
                list = list->next;
            }
            exit(1);
        }
        expl = expl->next;
    }
    l = list;
    while (l) {
        l->split->user2 = NULL;
        l = l->next;
    }
    _th_remove_cache(env);
    _th_install_cache(info->env);
    _th_derive_push(info->env);
    expl = explanation;
    //printf("\n*** RECONSTRUCTING PROOF ***\n\n");
    while (expl) {
        if (_th_assert_predicate(info->env,_th_simp(info->env,expl->e))) {
            _zone_print0("Failure");
            fail = 1;
        }
        expl = expl->next;
    }
    if (!fail && _th_simp(info->env,e) != _ex_true) {
        if (!_th_assert_predicate(info->env,_th_simp(info->env,ne))) {
            fprintf(stderr, "Explanation not valid 1 for %s\n", _th_print_exp(e));
            while (explanation) {
                fprintf(stderr, "    %s\n", _th_print_exp(explanation->e));
                explanation = explanation->next;
            }
            fprintf(stderr, "Args\n");
            for (i = 0; i < count; ++i) {
                fprintf(stderr, "    %s\n", _th_print_exp(args[i]));
            }
            _th_derive_pop(info->env);
            _th_remove_cache(info->env);
            _th_install_cache(env);
            brute_force_domain_antecedant(env,info,list,e);
            fprintf(stderr, "Correct\n");
            for (i = 0; i < n_tuple->size; ++i) {
                fprintf(stderr, "    %s\n", _th_print_exp(n_tuple->terms[i]));
            }
            exit(1);
        }
    }
    _th_derive_pop(info->env);
    for (i = 0; i < count; ++i) {
        fail = 0;
        _zone_print1("Testing position %d", i);
        _tree_indent();
        _th_derive_push(info->env);
        for (j = 0; j < count; ++j) {
            if (i != j) {
                if (_th_assert_predicate(info->env,_th_simp(info->env,args[j]))) {
                    fail = 1;
                }
            }
        }
        _th_derive_pop(info->env);
        _tree_undent();
        if (fail) {
            _zone_print1("Position %d unnecessary b", i);
            fprintf(stderr, "Position %d unnecessary b\n", i);
            for (i = 0; i < count; ++i) {
                fprintf(stderr, "    %s\n", _th_print_exp(args[i]));
            }
            exit(1);
        }
    }
    _th_derive_push(info->env);
    fail = 0;
    for (i = 0; i < count; ++i) {
        if (_th_assert_predicate(info->env,_th_simp(info->env,_th_simp(info->env,args[i])))) fail = 1;
    }
    if (!fail) {
        _zone_print0("Tuple not valid");
        fprintf(stderr, "Tuple not valid\n");
        for (i = 0; i < count; ++i) {
            fprintf(stderr, "    %s\n", _th_print_exp(args[i]));
        }
        exit(1);
    }
    _th_derive_pop(info->env);
    _th_remove_cache(info->env);
    _th_install_cache(env);
#endif
    //printf("Here d10\n");
    //fflush(stdout);
    while (list && list != info->unate_tail) {
        list->used_in_learn = 0;
        for (i = 0; i < count; ++i) {
            if (list->split==args[i]) {
                list->used_in_learn = 1;
                goto cont3;
            }
        }
cont3:
        list = list->next;
    }
    //printf("Here d11\n");
    //fflush(stdout);
    //for (i = 0; i < count; ++i) {
    //    struct _ex_intern *e = args[i];
    //    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
    //        e = e->u.appl.args[0];
    //    }
    //    _tree_print2("original %d %s", i, _th_print_exp(e->original));
    //    if (e->original && e->original != e) {
    //        if (e==args[i]) {
    //            args[i] = e->original;
    //        } else {
    //            args[i] = _ex_intern_appl1_env(env,INTERN_NOT,e->original);
    //        }
    //    }
    //}
    _zone_print0("Adding group\n");
    if (count==2 && ((args[0]->type==EXP_APPL && args[0]->u.appl.functor==INTERN_NOT && args[0]->u.appl.args[0]==args[1]) ||
                     (args[1]->type==EXP_APPL && args[1]->u.appl.functor==INTERN_NOT && args[1]->u.appl.args[0]==args[0]))) {
        if (_th_quit_on_no_antecedant) {
            fprintf(stderr, "Failed antecedant\n");
            for (i = 0; i < count; ++i) {
                fprintf(stderr, "    %s\n", _th_print_exp(args[i]));
            }
            exit(1);
        }
        return 0;
    }
    i = add_group(env,info,count,args,2);
    _tree_undent();
    return i;
}

static void find_different_terms(struct env *env, struct _ex_intern *e)
{
    int i;

    if (e->type != EXP_APPL) return;
    _tree_print_exp("Differences for", e);
    _tree_indent();
    for (i = 0; i < e->u.appl.count; ++i) {
        _tree_print1("Testing position %d", i);
        if (_th_simp(env,e->u.appl.args[i]) != e->u.appl.args[i]) {
            _tree_print0("*** DIFFERENT ***");
            find_different_terms(env,e->u.appl.args[i]);
        }
    }
    _tree_undent();
}

void valid_explanation(struct add_list *expl, struct parent_list *list)
{
    struct parent_list *l;

    while (expl) {
        l = list;
        while (l) {
            if (l->split==expl->e) goto cont;
            l = l->next;
        }
        fprintf(stderr, "Explanation term not valid %s\n", _th_print_exp(expl->e));
        exit(1);
cont:
        expl = expl->next;
    }
}

static void print_diffs(struct env *env, struct _ex_intern *e1, struct _ex_intern *e2)
{
    int i;

    if (e1==e2) {
        _tree_print_exp("*** Same ***", e1);
        return;
    }

    if (e1->type != EXP_APPL || e2->type != EXP_APPL || e1->u.appl.functor != e2->u.appl.functor ||
        e1->u.appl.count != e2->u.appl.count) {
        struct add_list *expl;
        if (e1==_ex_true) {
            expl = _th_retrieve_explanation(env,e2);
        } else if (e2==_ex_true) {
            expl = _th_retrieve_explanation(env,e1);
        } else if (e1==_ex_false) {
            if (e2->type==EXP_APPL && e2->u.appl.functor==INTERN_NOT) {
                expl = _th_retrieve_explanation(env,e2->u.appl.args[0]);
            } else {
                expl = _th_retrieve_explanation(env,_ex_intern_appl1_env(env,INTERN_NOT,e2));
            }
        } else if (e2==_ex_false) {
            if (e1->type==EXP_APPL && e1->u.appl.functor==INTERN_NOT) {
                expl = _th_retrieve_explanation(env,e1->u.appl.args[0]);
            } else {
                expl = _th_retrieve_explanation(env,_ex_intern_appl1_env(env,INTERN_NOT,e1));
            }
        } else {
            expl = _th_retrieve_explanation(env,_ex_intern_appl2_env(env,INTERN_EQUAL,e1,e2));
        }
        _tree_print0("*** Different ***");
        _tree_indent();
        while (expl) {
            _tree_print_exp("e", expl->e);
            expl = expl->next;
        }
        _tree_undent();
        _tree_print_exp("e1", e1);
        _tree_print_exp("e2", e2);
        return;
    }

    _tree_print_exp("Differences between", e1);
    _tree_print_exp("and", e2);
    for (i = 0; i < e1->u.appl.count; ++i) {
        if (e1->u.appl.args[i] != e2->u.appl.args[i]) {
            _tree_print1("Position %d", i);
            _tree_indent();
            print_diffs(env,e1->u.appl.args[i],e2->u.appl.args[i]);
            _tree_undent();
        }
    }
}

//#define BUILD_STRUCT 1

void check_explanation(struct env *env, struct learn_info *info, struct parent_list *list)
{
    struct add_list *explanation;
    struct add_list *expl;
    struct parent_list *l;
    struct _ex_intern **args;
    int count, i, j;
    struct _ex_intern *e;
#ifdef BUILD_STRUCT
    struct _ex_intern *str1, *str2;
    extern struct _ex_intern *str;
#endif
#ifdef SANITY_CHECK
    int start_count;
#endif
    struct _ex_intern *term, *diff;
    int fail = 0;
    char *mark;

    _tree_print0("check explanation");

    //printf("env = %x\n", env);
    //printf("learn env = %x\n", info->env);

    if (info->unate_tail==NULL) return;

    l = list;
    while (l && l->next != info->unate_tail) {
        l = l->next;
    }
    if (!l) {
        return;
    }
    term = l->exp;

    e = _th_simp(env,term);
#ifdef BUILD_STRUCT
    str1 = str;
#endif

    if (e==_ex_true) {
        explanation = _th_retrieve_explanation(env,term);
    } else {
        explanation = _th_retrieve_explanation(env,_ex_intern_appl2_env(env,INTERN_EQUAL,e,term));
    }
    valid_explanation(explanation,list);

    if (explanation==NULL) {
        fprintf(stderr, "No explanation 5 for %s\n", _th_print_exp(term));
        exit(1);
    }

    expl = explanation;
    while (expl) {
        expl->e->user2 = NULL;
        expl = expl->next;
    }
    l = info->unate_tail;
    while (l) {
        l->split->user2 = _ex_true;
        l = l->next;
    }
    count = 0;
    expl = explanation;
    while (expl) {
        if (!expl->e->user2) {
            ++count;
            expl->e->user2 = _ex_true;
        }
        expl = expl->next;
    }
    //printf("count(a) = %d\n", count);
    expl = explanation;
    while (expl) {
        expl->e->user2 = NULL;
        expl = expl->next;
    }
    l = info->unate_tail;
    while (l) {
        l->split->user2 = _ex_true;
        l = l->next;
    }

    //printf("Here d4 %d\n", count);
    //fflush(stdout);

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (count+1));

    //printf("Here d5\n");
    //fflush(stdout);

    count = 0;
    expl = explanation;
    while (expl) {
        if (!expl->e->user2) {
            //struct _ex_intern *orig = expl->e;
            //if (orig->type==EXP_APPL && orig->u.appl.functor==INTERN_NOT) {
            //    orig = _ex_intern_appl1_env(env,INTERN_NOT,orig->u.appl.args[0]->original);
            //} else {
            //    orig = expl->e->original;
            //}
            args[count++] = expl->e;
            expl->e->user2 = _ex_true;
        }
        expl = expl->next;
    }
    //printf("count(b) = %d\n", count);

    //printf("Here d6\n");
    //fflush(stdout);

    for (i = 0; i < count; ++i) {
        args[i]->user2 = NULL;
    }

    //printf("Here d7\n");
    //fflush(stdout);

    l = info->unate_tail;
    while (l) {
        l->split->user2 = NULL;
        l = l->next;
    }

    //printf("Starting check\n");
    _th_remove_cache(env);
    _th_install_cache(info->env);
    mark = _th_alloc_mark(LEARN_ENV_SPACE);
    _th_derive_push(info->env);
#ifdef SANITY_CHECK
    start_count = count;
    printf("Start count %d\n", count);
    //for (i = 0; i < start_count; ++i) {
    //    printf("    %s\n", _th_print_exp(args[i]));
    //}
#endif
    //printf("Here d8\n");
    //fflush(stdout);

    fail = 0;
    _zone_print0("Testing explanation");
    _tree_indent();
    _th_derive_push(info->env);
    for (j = 0; j < count; ++j) {
        _tree_print_exp("term", args[j]);
        _tree_indent();
        if (_th_assert_predicate(info->env,_th_simp(info->env,args[j]))) {
            printf("Inconsistent terms in info\n");
            _th_derive_pop(info->env);
            _th_remove_cache(info->env);
            _th_install_cache(env);
            _tree_undent();
            _tree_undent();
            return;
        }
        //if (_ex_false->find==_ex_true) {
        //    fprintf(stderr, "Inconsistent constants\n");
        //    exit(1);
        //}
        _tree_undent();
    }
    if ((diff = _th_simp(info->env,term)) == e) fail = 1;
#ifdef BUILD_STRUCT
    str2 = str;
#endif
    _th_derive_pop(info->env);
    _tree_undent();
    if (!fail) {
        fprintf(stderr, "Explanation invalid\n");
        _th_remove_cache(info->env);
        _th_install_cache(env);
        find_different_terms(env,diff);
        _tree_print0("Stack");
        _tree_indent();
        while (list) {
            _tree_print_exp("e", list->split);
            list = list->next;
        }
        _tree_undent();
        _tree_print0("Explanation");
        _tree_indent();
        while (explanation) {
            _tree_print_exp("e", explanation->e);
            explanation = explanation->next;
        }
        _tree_undent();
#ifdef BUILD_STRUCT
        print_diffs(env,str1,str2);
#endif
        exit(1);
    }
    //printf("Here d9\n");
    //fflush(stdout);
    _th_derive_pop(info->env);
    _th_alloc_release(LEARN_ENV_SPACE,mark);
    //printf("Ending check\n");
    _th_remove_cache(info->env);
    _th_install_cache(env);
}

//#define CHECK_BAD_SIMP

static int exp_antecedant(struct env *env, struct learn_info *info, struct parent_list *list, struct _ex_intern *pred)
{
    struct add_list *explanation;
    struct add_list *expl;
    struct parent_list *l;
    struct _ex_intern **args;
    int count, i, j;
    struct _ex_intern *e;
#ifdef SANITY_CHECK
    struct _ex_intern *orig;
    int start_count;
#endif
#ifdef BUILD_STRUCT
    struct _ex_intern *str1, *str2;
    extern struct _ex_intern *str;
#endif
    int fail = 0;
    char *mark;
    struct _ex_intern *term;

    n_tuple = NULL;

    _tree_print_exp("Parent antecedant", pred);
    _tree_indent();

    //pl = list;
    l = list;
    while (l && l->next != info->unate_tail) {
        l = l->next;
    }
    if (!l) {
        _tree_undent();
        return 0;
    }
    term = l->exp;
    _zone_print_exp("term", term);
#ifdef SANITY_CHECK
    orig = term;
#endif

    //printf("Domain antecedant\n");
    //printf("Here d0\n");
    //fflush(stdout);

    //printf("Here d1\n");
    //fflush(stdout);

    //printf("Retrieving explanation for %s\n", _th_print_exp(e));
    //fflush(stdout);

    if (pred) {
        _th_remove_cache(env);
        _th_install_cache(info->env);
        mark = _th_alloc_mark(LEARN_ENV_SPACE);
        _th_derive_push(info->env);
        _th_assert_predicate(info->env,_th_simp(info->env,pred));
        term = _th_simp(info->env,term);
        _zone_print0("Assertions");
        _tree_indent();
        l = list;
        while (l != info->unate_tail) {
            _th_assert_predicate(info->env,_th_simp(info->env,l->split));
            l = l->next;
        }
        _tree_undent();
        e = _th_simp(info->env,term);
        if (e != _ex_true) {
#ifdef CHECK_BAD_SIMP
            fprintf(stderr, "Incomplete simplification\ne = %s\n", _th_print_exp(e));
            l = list;
            while (l) {
                if (_th_simp(info->env,l->exp) != _ex_true) {
                    exit(1);
                }
                fprintf(stderr, "    split = %s\n", _th_print_exp(l->split));
                l = l->next;
            }
#else
            _th_derive_pop(info->env);
            _th_alloc_release(LEARN_ENV_SPACE,mark);
            _th_remove_cache(info->env);
            _th_install_cache(env);
            _tree_undent();
            return 0;
#endif
        }
        explanation = _th_retrieve_explanation(info->env,term);
        _th_derive_pop(info->env);
        //_th_remove_cache(info->env);
        //_th_install_cache(env);
        //_th_alloc_release(LEARN_ENV_SPACE, mark);
    } else {
        e = _th_simp(env,term);
        if (e != _ex_true) {
#ifdef CHECK_BAD_SIMP
            fprintf(stderr, "Incomplete simplification\ne = %s\n", _th_print_exp(e));
            l = list;
            while (l) {
                if (_th_simp(env,l->exp) != _ex_true) {
                    exit(1);
                }
                fprintf(stderr, "    split = %s\n", _th_print_exp(l->split));
                l = l->next;
            }
#else
            _tree_undent();
            return 0;
#endif
        }
        explanation = _th_retrieve_explanation(env,term);
    }
#ifdef BUILD_STRUCT
    str1 = str;
#endif

    _tree_print_exp("Retrieving explanation for", term);
    if (explanation==NULL) {
        fprintf(stderr, "No explanation 4 for %s\n", _th_print_exp(term));
        exit(1);
        return 0;
    }
    _tree_print0("Has explanation");

    //printf("Here d2\n");
    //fflush(stdout);

    //printf("Here d3\n");
    //fflush(stdout);

    expl = explanation;
    while (expl) {
        expl->e->user2 = NULL;
        expl = expl->next;
    }
    l = info->unate_tail;
    while (l) {
        l->split->user2 = _ex_true;
        l = l->next;
    }
    count = 0;
    expl = explanation;
    while (expl) {
        if (!expl->e->user2) {
            ++count;
            expl->e->user2 = _ex_true;
        }
        expl = expl->next;
    }
    //printf("count(a) = %d\n", count);
    expl = explanation;
    while (expl) {
        expl->e->user2 = NULL;
        expl = expl->next;
    }
    l = info->unate_tail;
    while (l) {
        l->split->user2 = _ex_true;
        l = l->next;
    }

    //printf("Here d4 %d\n", count);
    //fflush(stdout);

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (count+1));

    //printf("Here d5\n");
    //fflush(stdout);

    count = 0;
    expl = explanation;
    while (expl) {
        if (!expl->e->user2) {
            //struct _ex_intern *orig = expl->e;
            //if (orig->type==EXP_APPL && orig->u.appl.functor==INTERN_NOT) {
            //    orig = _ex_intern_appl1_env(env,INTERN_NOT,orig->u.appl.args[0]->original);
            //} else {
            //    orig = expl->e->original;
            //}
            args[count++] = expl->e;
            expl->e->user2 = _ex_true;
        }
        expl = expl->next;
    }
    //printf("count(b) = %d\n", count);

    //printf("Here d6\n");
    //fflush(stdout);

    for (i = 0; i < count; ++i) {
        args[i]->user2 = NULL;
    }

    //printf("Here d7\n");
    //fflush(stdout);

    l = info->unate_tail;
    while (l) {
        l->split->user2 = NULL;
        l = l->next;
    }

    if (pred==NULL) {
        _th_remove_cache(env);
        _th_install_cache(info->env);
        mark = _th_alloc_mark(LEARN_ENV_SPACE);
    }
    _th_derive_push(info->env);
#ifdef SANITY_CHECK
    start_count = count;
    printf("Start count %d\n", count);
    for (i = 0; i < start_count; ++i) {
        printf("    %s\n", _th_print_exp(args[i]));
    }
#endif
    //printf("Here d8\n");
    //fflush(stdout);

    for (i = count-1; i >= 0; --i) {
        fail = 0;
        _zone_print1("Testing position %d", i);
        _tree_indent();
        _th_derive_push(info->env);
        for (j = 0; j < count; ++j) {
            if (i != j) {
                if (_th_assert_predicate(info->env,_th_simp(info->env,args[j]))) {
                    fprintf(stderr, "Inconsistent terms in info\n");
                    exit(1);
                }
            }
        }
        if (_th_simp(info->env,term) == _ex_true) fail = 1;
        _th_derive_pop(info->env);
        _tree_undent();
        if (fail) {
            _zone_print0("Eliminating");
            for (j = i; j < count-1; ++j) {
                args[j] = args[j+1];
            }
            --count;
        }
    }
    if (pred) {
        for (i = 0; i < count; ++i) {
            if (args[i]==pred) goto skip_pred_add;
        }
        args[count++] = pred;
    }
skip_pred_add:

    //printf("Here d9\n");
    //fflush(stdout);
    _th_derive_pop(info->env);
    _th_alloc_release(LEARN_ENV_SPACE,mark);
    _th_remove_cache(info->env);
    _th_install_cache(env);

#ifdef SANITY_CHECK
    if (start_count != count) {
        l = info->unate_tail;
        while (l) {
            l->split->user2 = _ex_false;
            l = l->next;
        }
        expl = explanation;
        printf("Original explanation\n");
        while (expl) {
            if (expl->e->user2==_ex_false) {
                printf("    tail: %s\n", _th_print_exp(expl->e));
                expl->e->user2 = _ex_true;
            }
            if (!expl->e->user2) {
                printf("    %s\n", _th_print_exp(expl->e));
                expl->e->user2 = _ex_true;
            }
            expl = expl->next;
        }
        //printf("count(a) = %d\n", count);
        expl = explanation;
        while (expl) {
            expl->e->user2 = NULL;
            expl = expl->next;
        }
        l = info->unate_tail;
        while (l) {
            l->split->user2 = _ex_true;
            l = l->next;
        }
        printf("Reduced set\n");
        for (i = 0; i < count; ++i) {
            printf("    %s\n", _th_print_exp(args[i]));
        }
    }
    l = list;
    i = 0; j = 0;
    while (l) {
        //fprintf(stderr, "l->split = %s\n", _th_print_exp(l->split));
        l->split->user2 = _ex_true;
        if (!j && l != info->unate_tail) {
            ++i;
        } else {
            j = 1;
        }
        l = l->next;
    }
    printf("%d reduced to %d\n", i, count);
    expl = explanation;
    while (expl) {
        //struct _ex_intern *orig = expl->e;
        //if (orig->type==EXP_APPL && orig->u.appl.functor==INTERN_NOT) {
        //    orig = _ex_intern_appl1_env(env,INTERN_NOT,orig->u.appl.args[0]->original);
        //} else {
        //    orig = expl->e->original;
        //}
        //if (orig->user2==NULL && expl->e->user2==NULL && expl->e != e && expl->e != ne &&
        //    orig != e && orig != ne) {
        if (expl->e->user2==NULL &&
            (expl->e->type != EXP_APPL && expl->e->u.appl.functor != INTERN_NOT && expl->e->user2==NULL)) {
            fprintf(stderr, "Explanation term not in assertion list %s\n", _th_print_exp(expl->e));
            //fprintf(stderr, "Original: %s\n", _th_print_exp(orig));
            expl = explanation;
            while (expl) {
                fprintf(stderr, "    %s\n", _th_print_exp(expl->e));
                expl = expl->next;
            }
            printf("List:\n");
            while (list) {
                printf("    %s\n", _th_print_exp(list->split));
                list = list->next;
            }
            exit(1);
        }
        expl = expl->next;
    }
    l = list;
    while (l) {
        l->split->user2 = NULL;
        l = l->next;
    }
    _th_remove_cache(env);
    _th_install_cache(info->env);
    _th_derive_push(info->env);
    expl = explanation;
    //printf("\n*** RECONSTRUCTING PROOF ***\n\n");
    while (expl) {
        if (_th_assert_predicate(info->env,_th_simp(info->env,expl->e))) {
            _zone_print0("Failure");
            fail = 1;
        }
        expl = expl->next;
    }
    if (!fail && _th_simp(info->env,term) != _ex_true) {
#ifdef BUILD_STRUCT
        str2 = str;
        print_diffs(info->env,str1,str2);
#endif
        fprintf(stderr, "Explanation not valid 2 for %s\n", _th_print_exp(term));
        while (explanation) {
            fprintf(stderr, "    %s\n", _th_print_exp(explanation->e));
            explanation = explanation->next;
        }
        fprintf(stderr, "Args\n");
        for (i = 0; i < count; ++i) {
            fprintf(stderr, "    %s\n", _th_print_exp(args[i]));
        }
        exit(1);
    }
    _th_derive_pop(info->env);
    for (i = 0; i < count; ++i) {
        fail = 0;
        _zone_print1("Testing position %d", i);
        _tree_indent();
        _th_derive_push(info->env);
        for (j = 0; j < count; ++j) {
            if (i != j) {
                if (_th_assert_predicate(info->env,_th_simp(info->env,args[j]))) {
                    fail = 1;
                }
            }
        }
        _tree_undent();
        if (fail || _th_simp(info->env,orig)==_ex_true) {
            _zone_print1("Position %d unnecessary a", i);
            fprintf(stderr, "Position %d unnecessary a\n", i);
            for (i = 0; i < count; ++i) {
                fprintf(stderr, "    %s\n", _th_print_exp(args[i]));
            }
            exit(1);
        }
        _th_derive_pop(info->env);
    }
    _th_derive_push(info->env);
    fail = 0;
    for (i = 0; i < count; ++i) {
        if (_th_assert_predicate(info->env,_th_simp(info->env,args[i]))) fail = 1;
    }
    if (!fail && _th_simp(info->env,term) != _ex_true) {
        _zone_print0("Tuple not valid");
        fprintf(stderr, "Tuple not valid\n");
        for (i = 0; i < count; ++i) {
            fprintf(stderr, "    %s\n", _th_print_exp(args[i]));
        }
        exit(1);
    }
    _th_derive_pop(info->env);
    _th_remove_cache(info->env);
    _th_install_cache(env);
#endif
    //printf("Here d10\n");
    //fflush(stdout);
    while (list && list != info->unate_tail) {
        list->used_in_learn = 0;
        for (i = 0; i < count; ++i) {
            if (list->split==args[i]) {
                list->used_in_learn = 1;
                goto cont3;
            }
        }
cont3:
        list = list->next;
    }
    //printf("Here d11\n");
    //fflush(stdout);
    for (i = 0; i < count; ++i) {
        struct _ex_intern *e = args[i];
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
            e = e->u.appl.args[0];
        }
        _tree_print2("original %d %s", i, _th_print_exp(e->original));
        if (e->original && e->original != e) {
            if (e==args[i]) {
                args[i] = e->original;
            } else {
                args[i] = _ex_intern_appl1_env(env,INTERN_NOT,e->original);
            }
        }
    }
    _zone_print0("Adding group\n");
    for (i = 0; i < count; ++i) {
        if (!args[i]->in_hash) _th_simp(env,args[i]);
        //if (args[i]->type==EXP_APPL && args[i]->u.appl.functor==INTERN_NOT &&
        //    !args[i]->u.appl.args[0]->in_hash) _th_simp(env,args[i]->u.appl.args[0]);
    }
    i = add_group(env,info,count,args,2);
    _tree_undent();
    return i;
}

#ifdef XX
struct expl_list {
    struct expl_list *next;
    struct add_list *explanation;
};

struct expl_rec {
    struct expl_list *pos_expl;
    int has_true;
    struct expl_list *neg_expl;
    int has_false;
};

static struct _ex_intern *user2_trail;

static int exp_antecedant(struct env *env, struct learn_info *info, struct parent_list *list)
{
    struct parent_list *l = list;
    struct _ex_intern *e;
    struct expl_rec *rec;
    struct expl_list *expl;
    struct add_list *a;

    user2_trail = _ex_true;
    _ex_true->rewrite_next = NULL;

    while (l) {
        if (l->split->type==EXP_APPL && l->split->u.appl.functor==INTERN_NOT) {
            e = l->split->u.appl.args[0];
            if (e->rewrite_next = NULL) {
                e->rewrite_next = user2_trail;
                user2_trail = e;
                rec = (struct _ex_intern *)_th_alloc(REWRITE_SPACE,sizeof(struct expl_rec));
                e->user2 = (struct _ex_intern *)rec;
                rec->pos_expl = NULL;
                expl = rec->neg_expl = (struct expl_list *)_th_alloc(REWRITE_SPACE,sizeof(struct expl_list));
                expl->next = NULL;
                a = expl->explanation = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                a->next = NULL;
                a->e = l->split;
                rec->has_true = 1;
                rec->has_false = 1;
            }
        } else {
            e = l->split;
            if (e->rewrite_next = NULL) {
                e->rewrite_next = user2_trail;
                user2_trail = e;
                rec = (struct _ex_intern *)_th_alloc(REWRITE_SPACE,sizeof(struct expl_rec));
                e->user2 = (struct _ex_intern *)rec;
                rec->neg_expl = NULL;
                expl = rec->pos_expl = (struct expl_list *)_th_alloc(REWRITE_SPACE,sizeof(struct expl_list));
                expl->next = NULL;
                a = expl->explanation = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                a->next = NULL;
                a->e = l->split;
                rec->has_true =1;
                rec->has_false = 1;
            }
        }
        l = l->next;
    }
}
#endif

static struct tuple *find_antecedant(struct learn_info *info, struct parent_list *list, struct _ex_intern *e)
{
    struct term_info_list *ti;
    struct tuple *t;
    int i, j, ni;

    _zone_print_exp("Finding antecedant for", e);
    //printf("find_antecedant %s\n", _th_print_exp(e));
    ti = get_term_info(NULL, info, e, 1);

    t = ti->tuple;
    i = ti->index;

    _tree_indent();
    while (t) {
        _zone_print2("Testing %x %d", t, i);
        _tree_indent();
        ni = t->term_next_index[i];
        if (e==t->terms[i]) goto cont;
        for (j = 0; j < t->size; ++j) {
            _zone_print2("Pos %d %s", j, _th_print_exp(t->terms[j]));
            _zone_print_exp("val", t->term_info[j]->assignment);
            if (t->term_info[j]->passed) {
                _zone_print0("Passed");
                goto cont;
            }
            if (i != j) {
                if (t->term_info[j]->assignment==NULL) goto cont;
                if (t->term_info[j]->assignment==_ex_true &&
                    t->terms[j]->type==EXP_APPL && t->terms[j]->u.appl.functor==INTERN_NOT) goto cont;
                if (t->term_info[j]->assignment==_ex_false &&
                    (t->terms[j]->type!=EXP_APPL || t->terms[j]->u.appl.functor!=INTERN_NOT)) goto cont;
            }
        }
        _tree_undent();
        _tree_undent();
        return t;
cont:
        _tree_undent();
        t = t->term_next[i];
        i = ni;
    }
    _tree_undent();

    return NULL;
}


int learn_contradiction(struct env *env, struct learn_info *info, struct parent_list *list, int count, struct _ex_intern **args)
{
    struct tuple *t;
    struct _ex_intern **args2;
    struct _ex_intern *e;
    struct _ex_intern *test;
    struct term_info_list *ti;
    int i, j, k, l;

    //pl = list;

#ifndef FAST
    //if (_zone_active) {
        _tree_print0("Resolving");
        _tree_indent();
        for (i = 0; i < count; ++i) {
            _tree_print_exp("r", args[i]);
        }
        _tree_undent();
    //}
#endif
    while (list && list->unate) {
        list->used_in_learn = 0;
        test = list->split;
        if (test->type==EXP_APPL && test->u.appl.functor==INTERN_NOT) {
            if (test->u.appl.args[0]->original) test = _ex_intern_appl1_env(env,INTERN_NOT,test->u.appl.args[0]->original);
        } else {
            if (test->original) test = test->original;
        }
        for (i = 0; i < count; ++i) {
            if (args[i]==test) goto cont;
        }
        ti = get_term_info(env,info,test,0);
        if (ti) ti->passed = 1;
        list = list->next;
    }
    while (list) {
        list->used_in_learn = 0;
		_tree_print_exp("Processing list term %s", list->split);
        for (i = 0; i < count; ++i) {
			//_tree_print2("args[%d] = %s", i, _th_print_exp(args[i]));
            if (args[i]==list->split) {
                list->used_in_learn = 1;
                goto cont1;
            }
        }
cont1:
        list = list->next;
    }
    while (list && list != info->unate_tail) {
        list->used_in_learn = 0;
		_tree_print_exp("Processing list term %s", list->split);
        for (i = 0; i < count; ++i) {
			//_tree_print2("args[%d] = %s", i, _th_print_exp(args[i]));
            if (list->split==args[i]) {
                list->used_in_learn = 1;
                goto cont3;
            }
        }
cont3:
        list = list->next;
    }
    for (i = 0; i < count; ++i) {
        struct _ex_intern *e = args[i];
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
            e = e->u.appl.args[0];
        }
        if (e->original && e->original != e) {
            if (e==args[i]) {
                args[i] = e->original;
            } else {
                args[i] = _ex_intern_appl1_env(env,INTERN_NOT,e->original);
            }
        }
    }
    if (add_group(info->env,info,count,args,1)) {
        return 1;
    } else {
        return -1;
    }
cont:
    //no_recurse = 0;
    //printf("Find antecedant 1\n");
    t = find_antecedant(info,list->next,test);
#ifdef DOMAIN_PROPAGATE
    if (t==NULL) {
        if (list->unate==2) {
            //struct parent_list l;
            //l.next = list;
            //l.exp = _ex_true;
            //l.unate = 2;
            //l.used_in_learn = 1;
            struct _ex_intern *x;
            if (list->split->type != EXP_APPL || list->split->u.appl.functor != INTERN_NOT) {
                x = _ex_intern_appl1_env(env,INTERN_NOT,list->split);
            } else {
                x = list->split->u.appl.args[0];
            }
            exp_antecedant(env,info,list->next,x);
            if (n_tuple) {
                t = n_tuple;
            }
        } else {
            if (domain_antecedant(env,info,list->next,list->split)) {
                t = n_tuple;
            }
        }
    }
#endif
    if (t==NULL) {
        return 0;
    }
#ifndef FAST
    //if (_zone_active) {
        _tree_print0("with");
        _tree_indent();
        for (i = 0; i < t->size; ++i) {
            _tree_print_exp("r", t->terms[i]);
        }
        _tree_undent();
    //}
#endif
    args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (t->size+count));
    j = 0;
    e = list->split;
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) e = e->u.appl.args[0];

    for (i = 0; i < count; ++i) {
        if (args[i] != e && (args[i]->type != EXP_APPL || args[i]->u.appl.functor != INTERN_NOT || args[i]->u.appl.args[0] != e)) {
            args2[j++] = args[i];
        }
    }
    l = j;
    for (i = 0; i < t->size; ++i) {
        if (t->terms[i] != e && (t->terms[i]->type != EXP_APPL || t->terms[i]->u.appl.functor != INTERN_NOT || t->terms[i]->u.appl.args[0] != e)) {
            for (k = 0; k < l; ++k) {
                if (args2[k]==t->terms[i]) goto cont2;
            }
            args2[j++] = t->terms[i];
cont2:;
        }
    }
    ti = get_term_info(env,info,list->split,0);
    ti->passed = 1;
    return learn_contradiction(env, info, list->next, j, args2);
}

void check_assignments(struct learn_info *info, struct parent_list *list)
{
    int i;

    for (i = 0; i < TERM_HASH; ++i) {
        struct term_info_list *t = info->tuples_by_term[i];
        while (t) {
            struct parent_list *l;
            _zone_print_exp("Checking", t->term);
            if (t->assignment==NULL) goto cont;
            _zone_print_exp("Assignment", t->assignment);
            l = list;
            while (l) {
                struct _ex_intern *e = l->split;
                if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) e = e->u.appl.args[0];
                if (e==t->term || e->original==t->term) goto cont;
                l = l->next;
            }
            fprintf(stderr, "Extra assignment for term %s\n", _th_print_exp(t->term));
            exit(1);
cont:
            t = t->next;
        }
    }
}

void clear_passed(struct learn_info *info)
{
    int i;

    for (i = 0; i < TERM_HASH; ++i) {
        struct term_info_list *t = info->tuples_by_term[i];
        while (t) {
            t->passed = 0;
            t = t->next;
        }
    }
}

void _th_add_unate_tail(struct env *env, struct learn_info *info, struct parent_list *list)
{
    struct parent_list *l;

    if (!info->have_unate_tail) {
        l = list;
        while (l && !all_unates(l)) {
            l = l->next;
        }
        _tree_print0("Adding unate tail generalizations");
        _tree_indent();
        info->unate_tail = l;
        info->have_unate_tail = 1;
        //info->env = _th_get_learn_env();
        _th_remove_cache(env);
        _th_install_cache(info->env);
        _th_initialize_difference_table(info->env);
        if (l) {
            _th_simp(info->env,l->exp);
#ifdef SANITY_CHECK
            printf("Unate tail:\n");
#endif
            while (l) {
                if (l->split==0) {
                    printf("Error\n");
                    exit(1);
                }
                //_th_simp(info->env,l->split);
                _th_assert_predicate(info->env,_th_simp(info->env,l->split));
#ifdef SANITY_CHECK
                printf("    %s\n", _th_print_exp(l->split));
#endif
                l = l->next;
            }
        }
        _th_remove_cache(info->env);
        _th_install_cache(env);
        _tree_undent();
    }
}

static void print_me(struct _ex_intern *e)
{
	struct add_list *a = e->explanation;

    _tree_print_exp("merge", e->merge);
	_tree_indent();
	while (a) {
    	_tree_print_exp("expl", a->e);
		a = a->next;
	}
	_tree_undent();
}

static void print_merge_explanation(struct _ex_intern *e)
{
	_tree_indent();
	print_me(e);
	if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
		e = e->u.appl.args[0];
		_tree_print_exp("merge and explanation of", e);
        print_me(e);
	}
	if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL) {
		_tree_print_exp("merge and explanation of", e->u.appl.args[0]);
		print_me(e->u.appl.args[0]);
		_tree_print_exp("merge and explanation of", e->u.appl.args[1]);
		print_me(e->u.appl.args[1]);
	}
	_tree_undent();
}

void _th_print_trail(char *heading, struct parent_list *l)
{
	_tree_print0(heading);
    _tree_indent();
    _tree_print0("Top");
    while (l != NULL) {
        if (l->unate) {
            _tree_indent();
        }
        _tree_print3("t %d %d %s", l->unate, l->used_in_learn, _th_print_exp(l->split));
		print_merge_explanation(l->split);
        if (l->unate) {
            _tree_undent();
        }
        l = l->next;
    }
    _tree_undent();
}

int _th_learn(struct env *env, struct learn_info *info, struct parent_list *list, struct term_list *terms, int from_domain)
{
    int count;
    struct _ex_intern **args;
    //struct _ex_intern *fexp;
    int res;
    char *mark;
    struct tuple *t;
    struct _ex_intern *e;
    int i;
    struct parent_list *l;

    //check_assignments(info, list);

    //printf("Entering _th_learn\n");
    //fflush(stdout);

    //printf("\n*** LEARNING *** %x\n\n", info);

    if (list==NULL) return 0;

    _tree_print1("Learning %d", from_domain);
    _tree_indent();


#ifndef FAST
	_th_print_trail("Original tuple", list);
#endif

    if (has_learned_unate(info,list->split)) {
        _tree_undent();
        return 0;
    }

    //printf("Here a %x\n", info);
    //fflush(stdout);


    ++info->learns;
    if (!info->have_unate_tail) {
        if (!list || all_unates(list)) {
            _tree_print0("All unates");
            _tree_undent();
            return 0;
        }
    }
    _th_add_unate_tail(env,info,list);

    clear_passed(info);

    //printf("Here b %x\n", info);
    //fflush(stdout);
    mark = _th_alloc_mark(LEARN_ENV_SPACE);

    l = list;
    count = 0;
    while (l && l != info->unate_tail) {
        ++count;
        l = l->next;
    }

    //printf("Here c %x\n", info);
    //fflush(stdout);
    //_th_mark_original(env);
    if (list->split->type==EXP_APPL && list->split->u.appl.functor==INTERN_NOT) {
        e = list->split->u.appl.args[0];
    } else {
        e = _ex_intern_appl1_env(env,INTERN_NOT,list->split);
    }
    res = 0;
    //printf("Here cc %x\n", info);
    //fflush(stdout);
    if (from_domain==2) {
        res = exp_antecedant(env,info,list,NULL);
        if (!list->unate) {
            _tree_undent();
            _tree_print0("Done learn 0a");
            return res;
        }
    } else if (from_domain==0) {
        res = domain_antecedant(env,info,list->next,e);
        if (!list->unate) {
            struct parent_list *l = list;
            _tree_undent();
            _tree_print0("USE IN LEARN 6");
            while (list && list != info->unate_tail) {
                list->used_in_learn = 0;
                for (i = 0; i < count; ++i) {
                    if (list->split==n_tuple->terms[i] ||
                        list->split->original==n_tuple->terms[i]) {
                        list->used_in_learn = 1;
                        goto cont3;
                    }
                }
cont3:
                list = list->next;
            }
            list = l->next;
            while (list && list != info->unate_tail && !list->used_in_learn) {
                list = list->next;
            }
            if (list==info->unate_tail) {
                while (list) {
                    list->used_in_learn = 0;
                    list = list->next;
                }
            } else {
                while (list && list != info->unate_tail) {
                    list->used_in_learn = 1;
                    list = list->next;
                }
            }
            return res;
        }
    }
    //printf("Here ccc %x\n", info);
    //fflush(stdout);
    //printf("Find antecedant 2 %x\n", info);
    t = find_antecedant(info,list->next,e);
    _zone_print1("Initial antecedant %x", t);
    //printf("Here d %x\n", t);
    //fflush(stdout);
    if (t) {
#ifndef FAST
        _zone_print0("Tuple");
        for (i = 0; i < t->size; ++i) {
            _zone_print_exp("term", t->terms[i]);
        }
#endif
        if (list->unate) {
            struct _ex_intern *e1;
            if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                e1 = e->u.appl.args[0];
            } else {
                e1 = _ex_intern_appl1_env(env,INTERN_NOT,e);
            }
            l = (struct parent_list *)ALLOCA(sizeof(struct parent_list));
            l->next = list->next;
            l->split = e;
            l->unate = 1;
            l->used_in_learn = 0;
            l = (struct parent_list *)ALLOCA(sizeof(struct parent_list));
            l->next = list;
            l->split = e;
            l->unate = 1;
            l->used_in_learn = 0;
            list = l;
            goto cont;
        }
    } else {
        for (i = 0; i < TERM_HASH; ++i) {
            struct term_info_list *ti = info->tuples_by_term[i];
            while (ti) {
                //printf("Testing %s %d %d\n", _th_print_exp(ti->term), ti->false_implications, ti->true_implications);
                //if (ti->term->u.appl.functor==INTERN_EQUAL &&
                //    ti->term->u.appl.args[0]->type==EXP_VAR &&
                //    ti->term->u.appl.args[1]->type==EXP_VAR) {
                //    _tree_print_exp("Testing", ti->term);
                //    _tree_print_exp("Assignment", ti->assignment);
                //    _tree_print2("Result %d %d", ti->false_implications, ti->true_implications);
                //}
                if ((ti->false_implications && ti->true_implications) ||
                    (ti->false_implications && ti->assignment==_ex_true) ||
                    (ti->true_implications && ti->assignment==_ex_false)) {
                    struct parent_list *l = (struct parent_list *)ALLOCA(sizeof(struct parent_list));
                    _zone_print_exp("Contradictory term is", ti->term);
                    e = ti->term;
                    //_tree_print_exp("ti term", e);
                    //printf("Find antecedant 3\n");
                    t = find_antecedant(info,list,e);
                    _zone_print1("t = %x", t);
                    //printf("Result %x\n", t);
                    l->next = list;
                    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                        l->split = e->u.appl.args[0];
                    } else {
                        l->split = _ex_intern_appl1_env(env,INTERN_NOT,e);
                    }
                    list = l;
                    l->unate = 1;
                    l->used_in_learn = 0;
                    l = (struct parent_list *)ALLOCA(sizeof(struct parent_list));
                    l->next = list;
                    l->split = e;
                    l->unate = 1;
                    l->used_in_learn = 0;
                    list = l;
                    goto cont;
                }
                ti = ti->next;
            }
        }
    }
    _zone_print0("All fails");
    t = info->tuples;
    //printf("Here e %d\n", t);
    //fflush(stdout);
    while (t) {
        //printf("Testing %x\n", t);
        //fflush(stdout);
        if (t->var1==-1 && t->var2==-1) {
            //printf("Testing tuple\n");
            //fflush(stdout);
            for (i = 0; i < t->size; ++i) {
                //printf("    %s\n", _th_print_exp(t->terms[i]));
                if (t->term_info[i]->assignment==_ex_true) {
                    if (t->terms[i]->type==EXP_APPL && t->terms[i]->u.appl.functor==INTERN_NOT) goto c1;
                } else if (t->term_info[i]->assignment==_ex_false) {
                    if (t->terms[i]->type!=EXP_APPL || t->terms[i]->u.appl.functor!=INTERN_NOT) goto c1;
                } else {
                    fprintf(stderr, "Internal error: Bad tuple\n");
                    exit(1);
               }
            }
            _zone_print0("Got tuple");
            goto cont;
        }
c1:
        t = t->next;
    }
cont:
    //printf("Here f\n");
    //fflush(stdout);
    if (t) {
        int res2;
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * t->size);
        for (i = 0; i < t->size; ++i) {
            args[i] = t->terms[i];
        }
        list->used_in_learn = 1;
        //no_recurse = 1;
        res2 = learn_contradiction(env,info,list->next,t->size,args);
        _zone_print0("Done learn 1");
        if (!res) res = res2;
    }
    if (!res) {
        //fprintf(stderr, "_th_learn: learn failure\n");
        //exit(1);
        //args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
        //i = 0;
        //l = list;
        //while (l && l != info->unate_tail) {
        //    l->used_in_learn = 1;
        //    args[i++] = l->split;
        //    l = l->next;
        //}
        //res = add_group(env,info,i,args,3);
    } else {
        ++info->generalized_tuples;
    }

    //printf("Exiting _th_learn\n");
    //fflush(stdout);

    _tree_undent();

    //while (list != NULL && list->next != NULL) {
    //    list = list->next;
    //}
    //return added_unate_tuple && check_unate_contradiction(env,info,list->exp);
    //if (fexp) exit(1);

    _th_alloc_release(LEARN_ENV_SPACE,mark);

    _zone_print0("exiting learn");

    //printf("Here g\n");
    //fflush(stdout);
    l = list;
#ifdef XX
    _tree_print0("Final tuple");
    _tree_indent();
    _tree_print0("Top");
    _tree_indent();
    while (l != NULL) {
        int i, x;
        //static *xxx = NULL;
        //if (xxx==NULL) xxx = _th_parse(env, "(== (f3 c_5) c_1)");
        if (!l->unate) {
            _tree_undent();
        }
        x = 0;
        for (i = 0; i < n_tuple->size; ++i) {
            if (n_tuple->terms[i]==l->split || n_tuple->terms[i]==l->split->original) x = 1;
        }
        if (x) _tree_print0("*** TUPLE HERE ***");
        _tree_print3("t %d %d %s", l->unate, l->used_in_learn, _th_print_exp(l->split));
        if (l->split->original) {
            _tree_indent();
            _tree_print_exp("orig", l->split);
            _tree_undent();
        }
        //if (xxx==l->split && _zone_active()) exit(1);
        if (!l->unate) {
            _tree_indent();
        }
        l = l->next;
    }
    _tree_undent();
    _tree_undent();
#endif
    l = list;
	list = list->next;
    while (list && list != info->unate_tail && !list->used_in_learn) {
        list = list->next;
    }
	_tree_print1("list = %x", list);
    if (list==info->unate_tail) {
        while (list) {
            list->used_in_learn = 0;
            list = list->next;
        }
    } else {
        while (list && list != info->unate_tail) {
            list->used_in_learn = 1;
            list = list->next;
        }
    }
    //printf("Here h\n");
    //fflush(stdout);
    //check_assignments(info, l);
    _tree_print0("Done learn 2");
    //fprintf(stderr, "Finished learn\n");
    //fflush(stderr);
    //exit(1);
    if (res<=0 && _th_quit_on_no_antecedant) {
        fprintf(stderr, "Failed learn\n");
        exit(1);
    }
    return res > 0;
}

void _th_learn_increase_bump(struct learn_info *info, double factor)
{
	info->bump_size *= factor;
}

double _th_learn_pos_score(struct env *env, struct learn_info *info, struct _ex_intern *term)
{
	struct term_info_list *t = get_term_info(env,info,term,0);
	if (t) {
		return t->pos_score;
	} else {
		return 0;
	}
}

double _th_learn_neg_score(struct env *env, struct learn_info *info, struct _ex_intern *term)
{
	struct term_info_list *t = get_term_info(env,info,term,0);
	if (t) {
		return t->neg_score;
	} else {
		return 0;
	}
}

int _th_learn_score(struct env *env, struct learn_info *info, struct _ex_intern *term, struct parent_list *parents)
{
    struct term_info_list *t = get_term_info(env,info,term,0);

    if (t) {
        int count = t->count;
        struct score_list *s = t->score_list;
        _zone_print2("Score for %s is %d", _th_print_exp(term), t->count);
        while (s) {
            if (s->is_implication) {
                count += (s->term->count/2);
            } else {
                count += (s->term->count/4);
            }
            s = s->next;
        }
        return count;
    } else {
        return 0;
    }

#ifdef XX
    int hash;
    struct term_info_list *t;
    struct tuple *tuple;
    int index, count, i;
    struct parent_list *p;

    //_tree_print_exp("Learn score for", term);
    //_tree_indent();

    if (term->type==EXP_APPL && term->u.appl.functor==INTERN_NOT) term = term->u.appl.args[0];

    hash = (((int)term)/4)%TERM_HASH;
    //_tree_print1("hash = %d", hash);
    t = info->tuples_by_term[hash];
    while (t && t->term != term) {
        t = t->next;
    }
    if (t==NULL) {
        //_tree_undent();
        return 0;
    }

    tuple = t->tuple;
    index = t->index;

    count = 0;
    while (tuple) {
        int ni;
        //_tree_print("tuple");
        //_tree_indent();
        //for (i = 0; i < tuple->size; ++i) {
        //    _tree_print_exp("t", tuple->terms[i]);
        //}
        //_tree_undent();
        p = parents;
        //_tree_print("parents");
        //_tree_indent();
        while (p != NULL) {
            struct _ex_intern *test;
            int not;
            //_tree_print_exp("Checking parent", p->split);
            if (p->split->type==EXP_APPL && p->split->u.appl.functor==INTERN_NOT) {
                test = p->split->u.appl.args[0];
                not = 0;
            } else {
                test = p->split;
                not = 1;
            }
            for (i = 0; i < tuple->size; ++i) {
                if (!not && tuple->terms[i]==test) {
                    //_tree_undent();
                    //_tree_print("Skipping tuple");
                    goto cont;
                }
                if (not && tuple->terms[i]->type==EXP_APPL && tuple->terms[i]->u.appl.functor==INTERN_NOT &&
                    tuple->terms[i]->u.appl.args[0]==test) {
                    goto cont;
                }
            }
            p = p->next;
        }
        //_tree_undent();
        ++count;
cont:
        ni = tuple->term_next_index[index];
        tuple = tuple->term_next[index];
        index = ni;
    }

    //_tree_undent();
    return count;
#endif
}

struct _ex_intern *_th_learn_choose(struct env *env, struct learn_info *info, struct parent_list *parents)
{
    struct term_info_list *t;
    int score = -1, s;
    int i;
    struct _ex_intern *result = NULL;

	_tree_print0("Learn choose");
	_tree_indent();

    for (i = 0; i < TERM_HASH; ++i) {
        t = info->tuples_by_term[i];
        while (t) {
            if (!t->assignment) {
                s = _th_learn_score(env,info,t->term,parents);
                if (s > score) {
                    score = s;
                    result = t->term;
                }
            }
            t = t->next;
        }
    }

	_tree_undent();
	_tree_print_exp("result", result);

    return result;
}

struct _ex_intern *_th_learn_choose_signed(struct env *env, struct learn_info *info, struct parent_list *parents, double random_probability)
{
    struct term_info_list *t;
    double score = -1;
    int i;
    struct _ex_intern *result = NULL;

	_tree_print0("Learn choose signed");
	_tree_indent();

	if (rand() < random_probability * RAND_MAX) {
		int x;
		int total = 0;
		for (i = 0; i < TERM_HASH; ++i) {
			t = info->tuples_by_term[i];
			while (t) {
				if (!t->assignment) {
					++total;
				}
				t = t->next;
			}
		}
		if (total==0) {
			_tree_undent();
			return NULL;
		}
		x = rand()%(total*2);
		_tree_print2("Random case %d of %d", x, total*2);
		for (i = 0; i < TERM_HASH; ++i) {
			t = info->tuples_by_term[i];
			while (t) {
				if (!t->assignment) {
					x -= 2;
					if (x < 2) {
						if (x) {
    						result = t->term;
						} else {
    						result = _ex_intern_appl1_env(env,INTERN_NOT,t->term);
						}
						goto cont;
					}
				}
				t = t->next;
			}
		}
	} else {
		for (i = 0; i < TERM_HASH; ++i) {
			t = info->tuples_by_term[i];
			while (t) {
				if (!t->assignment) {
					if (t->pos_score > score || (result==NULL && t->assignment==NULL)) {
						score = t->pos_score;
						result = t->term;
					}
					if (t->neg_score > score) {
						score = t->neg_score;
						result = _ex_intern_appl1_env(env,INTERN_NOT,t->term);
					}
				}
				t = t->next;
			}
		}
	}

cont:
	_tree_print_exp("result", result);
	_tree_undent();

    return result;
}

struct _ex_intern *sublist1(int count1, struct _ex_intern **list1, int count2, struct _ex_intern **list2)
{
    int i, j;
    struct _ex_intern *ret = NULL;

    i = 0; j = 0;
    while (i < count1 && j < count2) {
        _zone_print2("i, j = %d %d", i, j);
        if (list1[i]==list2[j]) {
            ++i;
        } else if (list1[i]->type==EXP_APPL && list1[i]->u.appl.functor==INTERN_NOT &&
            list1[i]->u.appl.args[0]==list2[j]) {
            return 0;
        } else if (list2[j]->type==EXP_APPL && list2[j]->u.appl.functor==INTERN_NOT &&
            list2[j]->u.appl.args[0]==list1[i]) {
            return 0;
        } else if (cmp(&list1[i],&list2[j]) < 0) {
            if (ret) return NULL;
            ret = list1[i];
            ++i;
            --j;
        }
        ++j;
    }
    _zone_print5("finish i, j, count1, count2, ret = %d %d %d %d %d", i, j, count1, count2, ret);
    if (i==count1-1 && ret==NULL) ret = list1[i++];
    return (i==count1)?ret:NULL;
}

void _th_print_assignments(struct learn_info *info)
{
    int i;

    _tree_print0("Assignments");
    _tree_indent();
    for (i = 0; i < TERM_HASH; ++i) {
        struct term_info_list *t = info->tuples_by_term[i];
        while (t) {
            if (t->assignment==_ex_true) {
                _tree_print2("(%d) Term %s => True", t->decision_level, _th_print_exp(t->term));
            } else if (t->assignment==_ex_false) {
                _tree_print2("(%d) Term %s => False", t->decision_level, _th_print_exp(t->term));
            } else {
                _tree_print2("[%d] Term %s => Unassigned", t->decision_level, _th_print_exp(t->term));
            }
            t = t->next;
        }
    }
    _tree_undent();
}

int _th_learned_domain_case;

struct _ex_intern *_th_learned_unate_case(struct env *env, struct learn_info *info, struct parent_list *list)
{
    //int count, i;
    //struct parent_list *l;
    //struct _ex_intern **args;
    struct _ex_intern *e;
    struct tuple *tuple;

    //int hash;
    //struct term_info_list *t;
    //struct tuple *tuple;
    int index;

    //check_unates(info, list, "_th_learned_unate_case");
    //printf("Entering _th_solved_case\n");
    //fflush(stdout);

    _zone_print0("Testing learned unate");

    //if (info->have_unate_tail==0) {
    //    return NULL;
    //}

    _th_learned_domain_case = 0;
    if (!info->unates) {
#ifdef DOMAIN_PROPAGATE
        int i;
        for (i = 0; i < TERM_HASH; ++i) {
            struct term_info_list *t = info->tuples_by_term[i];
            while (t) {
                struct _ex_intern *r;
                //while (r->rewrite && r->rewrite != r) r = r->rewrite;
                //_tree_indent();
                //_tree_print_exp("Testing", t->term);
                //_tree_print_exp("Assignment", t->assignment);
                //_tree_print_exp("Rewrite", t->term->rewrite);
                //_tree_print_exp("Real rewrite", r);
                //_tree_undent();
                if (t->assignment==NULL) {
                    struct _ex_intern *orig = t->term->original;
					struct add_list *expl;
                    if (orig && orig != t->term) goto cont;
					if (t->term->in_hash) {
                        //printf("Processing %d %s\n", _tree_zone, _th_print_exp(t->term));
                        r = t->term;
                        while (r->find != r) r = r->find;
                        while (r->rewrite && r->rewrite != r) r = r->rewrite;
                    } else {
                        //fprintf(stderr, "Error (not in hash 1) %s\n", _th_print_exp(t->term));
                        //exit(1);
                        //r = _th_simp(env,t->term);
    					r = _th_check_cycle_rless(env,t->term,&expl);
						if (r==_ex_true || r==_ex_false) {
							_th_add_merge_explanation(env,t->term,r,expl);
						}
                    }
					if (r==_ex_true) {
                        _tree_undent();
                        _tree_print0("Domain true");
                        _tree_indent();
                        _th_learned_domain_case = 1;
                        return t->term;
                    } else if (r==_ex_false) {
                        _tree_undent();
                        _tree_print0("Domain false");
                        _tree_indent();
                        _th_learned_domain_case = 1;
                        return _ex_intern_appl1_env(env,INTERN_NOT,t->term);
                    }
                }
cont:
                t = t->next;
            }
        }
#endif
        return NULL;
    }

    //printf("info->unates = %x\n", info->unates);
    //fflush(stdout);

    tuple = info->unates;
    index = tuple->var1;
    if (index==-1) {
        index = tuple->var2;
    }
    if (index==-1) {
        fprintf(stderr, "Unate error %x\n", info->unates);
        exit(1);
    }
#ifndef FAST
    if (_zone_active()) {
        int i;
        _tree_print2("Returning unate based on tuple %x %d", tuple, tuple->size);
        _tree_indent();
        for (i = 0; i < tuple->size; ++i) {
            if (tuple->term_info[i]->assignment == _ex_true) {
                _tree_print_exp("TRUE", tuple->terms[i]);
            } else if (tuple->term_info[i]->assignment == _ex_false) {
                _tree_print_exp("FALSE", tuple->terms[i]);
            } else {
                _tree_print_exp("unassigned", tuple->terms[i]);
            }
        }
        _tree_undent();
    }
#endif
    e = tuple->term_info[index]->term;
    e = tuple->terms[index];
    ++info->unates->used_count;
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        return e->u.appl.args[0];
    } else {
        return _ex_intern_appl1_env(env,INTERN_NOT,e);
    }

#ifdef OLD
    _tree_indent();

#ifndef FAST
    if (_zone_active()) {
        _zone_print0("All tuples");
        tuple = info->tuples;
        _tree_indent();
        while (tuple) {
            _zone_print0("tuple");
            _tree_indent();
            for (i = 0; i< tuple->size; ++i) {
                _zone_print_exp("t", tuple->terms[i]);
            }
            _tree_undent();
            tuple = tuple->next;
        }
        _tree_undent();
    }
#endif

    l = list;
    count = 0;
    while (l && l != info->unate_tail) {
        ++count;
        l = l->next;
    }
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
    l = list;
    i = 0;

    while (l && l != info->unate_tail) {
        //_zone_print_exp("exp", l->split);
        args[i++] = l->split;
        l =l->next;
    }

    qsort(args,count,sizeof(struct _ex_intern *),cmp);

#ifndef FAST
    _zone_print0("Test args");
    _tree_indent();
    for (i = 0; i < count; ++i) {
        struct _ex_intern *t = args[i];
        if (t->type==EXP_APPL && t->u.appl.functor==INTERN_NOT) t = t->u.appl.args[0];
        _zone_print2("term %d %s", t, _th_print_exp(args[i]));
    }
    _tree_undent();
#endif

    for (i = 0; i < count; ++i) {
        _zone_print2("i = %d %s", i, _th_print_exp(args[i]));
        e = args[i];
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) e = e->u.appl.args[0];
        hash = (((int)e)/4)%TERM_HASH;
        t = info->tuples_by_term[hash];
        while (t != NULL && t->term != e) {
            t = t->next;
        }
        if (t != NULL) {
            tuple = t->tuple;
            index = t->index;
            while (tuple) {
                int nin = tuple->term_next_index[index];
                //printf("tuple, index, size = %x %d %d\n", tuple, index, tuple->size);
#ifndef FAST
                if (_zone_active()) {
                    int j;
                    _zone_print0("Checking");
                    _tree_indent();
                    for (j = 0; j < tuple->size; ++j) {
                        struct _ex_intern *t = tuple->terms[j];
                        if (t->type==EXP_APPL && t->u.appl.functor==INTERN_NOT) t = t->u.appl.args[0];
                        _zone_print2("term %d %s", t, _th_print_exp(tuple->terms[j]));
                    }
                    _tree_undent();
                }
#endif
                if (index == 0 || index==1) {
                    struct _ex_intern *ret = sublist1(tuple->size,tuple->terms,count-i,args+i);
                    _zone_print0("Testing");
                    if (ret) {
                        struct parent_list *l = list;
                        if (ret->type==EXP_APPL && ret->u.appl.functor==INTERN_NOT) {
                            ret = ret->u.appl.args[0];
                        } else {
                            ret = _ex_intern_appl1_env(env,INTERN_NOT,ret);
                        }
                        while (l != NULL && l != info->unate_tail) {
                            if (l->split==ret) goto cont;
                            l = l->next;
                        }
                        ++tuple->used_count;
                        //printf("Exiting _th_solved_case (solved)\n");
                        _zone_print_exp("unate", ret);
                        _tree_undent();
                        printf("Unate tuple basis\n");
                        for (i = 0; i < tuple->size; ++i) {
                            printf("    %s ", _th_print_exp(tuple->terms[i]));
                            printf(" (%s)\n", _th_print_exp(tuple->term_info[i]->assignment));
                        }
                        _tree_print_exp("Unate fill", ret);
                        return ret;
                    }
                }
cont:
                tuple = tuple->term_next[index];
                index = nin;
            }
        }
    }

    //printf("Exiting _th_solved_case\n");
    //fflush(stdout);

    _tree_undent();
#endif
    return NULL;
}

struct _ex_intern *_th_learned_non_domain_unate_case(struct env *env, struct learn_info *info, struct parent_list *list)
{
    struct _ex_intern *e;
    struct tuple *tuple;

    int index;

    _zone_print0("Testing learned unate");

    _th_learned_domain_case = 0;
    if (!info->unates) {
        return NULL;
    }

    tuple = info->unates;
    index = tuple->var1;
    if (index==-1) {
        index = tuple->var2;
    }
    if (index==-1) {
        fprintf(stderr, "Unate error %x\n", info->unates);
        exit(1);
    }
#ifndef FAST
    if (_zone_active()) {
        int i;
        _tree_print2("Returning unate based on tuple %x %d", tuple, tuple->size);
        _tree_indent();
        for (i = 0; i < tuple->size; ++i) {
            if (tuple->term_info[i]->assignment == _ex_true) {
                _tree_print_exp("TRUE", tuple->terms[i]);
            } else if (tuple->term_info[i]->assignment == _ex_false) {
                _tree_print_exp("FALSE", tuple->terms[i]);
            } else {
                _tree_print_exp("unassigned", tuple->terms[i]);
            }
        }
        _tree_undent();
    }
#endif
    e = tuple->term_info[index]->term;
    e = tuple->terms[index];
    ++info->unates->used_count;
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        return e->u.appl.args[0];
    } else {
        return _ex_intern_appl1_env(env,INTERN_NOT,e);
    }
}

int sublist(int count1, struct _ex_intern **list1, int count2, struct _ex_intern **list2)
{
    int i, j;

    i = 0; j = 0;
    while (i < count1 && j < count2) {
        if (list1[i]==list2[j]) {
            ++i;
        }
        ++j;
    }
    return (i==count1);
}

int _th_solved_case(struct env *env, struct learn_info *info, struct parent_list *list)
{
    int count, i;
    struct parent_list *l;
    struct _ex_intern **args;
    struct _ex_intern *e;
    int hash;
    struct term_info_list *t;
    struct tuple *tuple;
    int index;

    //printf("Entering _th_solved_case\n");
    //fflush(stdout);

    if (info->have_unate_tail==0) return 0;

    l = list;
    count = 0;
    while (l && l != info->unate_tail) {
        ++count;
        l = l->next;
    }
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
    l = list;
    i = 0;
    while (l && l != info->unate_tail) {
        args[i++] = l->split;
        l =l->next;
    }
    qsort(args,count,sizeof(struct _ex_intern *),cmp);

    for (i = 0; i < count-1; ++i) {
        e = args[i];
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) e = e->u.appl.args[0];
        hash = (((int)e)/4)%TERM_HASH;
        t = info->tuples_by_term[hash];
        while (t != NULL && t->term != e) {
            t = t->next;
        }
        if (t != NULL) {
            tuple = t->tuple;
            index = t->index;
            while (tuple) {
                int nin = tuple->term_next_index[index];
                //printf("tuple, index, size = %x %d %d\n", tuple, index, tuple->size);
                if (index == 0) {
                    if (sublist(tuple->size,tuple->terms,count-i,args+i)) {
                        ++tuple->used_count;
                        //printf("Exiting _th_solved_case (solved)\n");
#ifndef FAST
                        _tree_print0("Solve tuple");
                        for (i = 0; i < tuple->size; ++i) {
                            _tree_print_exp("t", tuple->terms[i]);
                        }
#endif
                        return 1;
                    }
                }
                tuple = tuple->term_next[index];
                index = nin;
            }
        }
    }

    //printf("Exiting _th_solved_case\n");
    //fflush(stdout);

    return 0;
}

int _th_get_learns(struct learn_info *info)
{
    return info->learns;
}

int _th_get_generalizations(struct learn_info *info)
{
    return info->generalized_tuples;
}

void _th_dump_learn(struct learn_info *info)
{
    struct tuple *t;
    int i;
    _tree_print0("Learn statistics");
    _tree_indent();
    _tree_print1("Learn calls: %d", info->learns);
    _tree_print1("Generalizations: %d", info->generalized_tuples);
    _tree_indent();
    t = info->tuples;
    while (t) {
        if (t->from_implication) {
            _tree_print2("Tuple: %d from implication (used %d times)", t->size, t->used_count);
        } else if (t->add_mode==2) {
            _tree_print2("Tuple: %d from domain (used %d times)", t->size, t->used_count);
        } else if (t->add_mode==1) {
            _tree_print2("Tuple: %d from resolution (used %d times)", t->size, t->used_count);
        } else if (t->add_mode==3) {
            _tree_print2("Tuple: %d by default (used %d times)", t->size, t->used_count);
        } else {
            _tree_print2("Tuple: %d (used %d times)", t->size, t->used_count);
        }
        _tree_indent();
        for (i = 0; i < t->size; ++i) {
            _tree_print_exp("", t->terms[i]);
        }
        _tree_undent();
        t = t->next;
    }
    _tree_undent();
    _tree_undent();
}

