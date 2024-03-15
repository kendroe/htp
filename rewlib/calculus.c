/*
 * calculus.c
 *
 * Routines for simplifying derivative and integrate expressions.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"

static struct _ex_intern *true_case, *false_case;

static int no_quant_vars(struct _ex_intern *quant, struct _ex_intern *e)
{
    int i;

    for (i = 0; i < quant->u.quant.var_count; ++i) {
        if (_th_is_free_in(e,quant->u.quant.vars[i])) return 0;
    }

    return 1;
}

static struct _ex_intern *extract_term(struct env *env, struct _ex_intern *quant, struct _ex_intern *term)
{
    int i, j, k;
    struct _ex_intern **args, *res;
    int *marks;

    //if (term->type==EXP_APPL && term->u.appl.functor==INTERN_NORMAL) term = term->u.appl.args[0];

    if (term->type != EXP_APPL) return NULL;

    if (term->u.appl.functor == INTERN_ITE) {
        if (no_quant_vars(quant,term->u.appl.args[0])) {
            true_case = term->u.appl.args[1];
            false_case = term->u.appl.args[2];
            return term->u.appl.args[0];
        }
        res = extract_term(env,quant,term->u.appl.args[0]);
        if (res) {
            false_case = _ex_intern_appl3_env(env,INTERN_ITE,
                                              false_case,
                                              term->u.appl.args[1],
                                              term->u.appl.args[2]);
            true_case = _ex_intern_appl3_env(env,INTERN_ITE,
                                             true_case,
                                             term->u.appl.args[1],
                                             term->u.appl.args[2]);
            return res;
        }
        res = extract_term(env,quant,term->u.appl.args[1]);
        if (res) {
            false_case = _ex_intern_appl3_env(env,INTERN_ITE,
                                              term->u.appl.args[0],
                                              false_case,
                                              term->u.appl.args[2]);
            true_case = _ex_intern_appl3_env(env,INTERN_ITE,
                                             term->u.appl.args[0],
                                             true_case,
                                             term->u.appl.args[2]);
            return res;
        }
        res = extract_term(env,quant,term->u.appl.args[2]);
        if (res) {
            false_case = _ex_intern_appl3_env(env,INTERN_ITE,
                                              term->u.appl.args[0],
                                              term->u.appl.args[1],
                                              false_case);
            true_case = _ex_intern_appl3_env(env,INTERN_ITE,
                                             term->u.appl.args[0],
                                             term->u.appl.args[1],
                                             true_case);
            return res;
        }
    }

    if (term->u.appl.functor != INTERN_AND && term->u.appl.functor != INTERN_OR) return NULL;

    marks = (int *)ALLOCA(sizeof(int) * term->u.appl.count);
    k = 0;

    for (i = 0; i < term->u.appl.count; ++i) {
        marks[i] = no_quant_vars(quant,term->u.appl.args[i]);
        if (marks[i]) ++k;
    }

    if (k) {
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * term->u.appl.count);
        for (i = 0, j = 0; i < term->u.appl.count; ++i) {
            if (!marks[i]) args[j++] = term->u.appl.args[i];
        }
        if (j==0) {
            if (term->u.appl.functor==INTERN_AND) {
                res = _ex_true;
            } else {
                res = _ex_false;
            }
        } else if (j==1) {
            res = args[0];
        } else {
            res = _ex_intern_appl_env(env,term->u.appl.functor,j,args);
        }

        if (term->u.appl.functor==INTERN_AND) {
            false_case = _ex_false;
            true_case = res;
        } else {
            false_case = res;
            true_case = _ex_true;
        }

        for (i = 0, j = 0; i < term->u.appl.count; ++i) {
            if (marks[i]) args[j++] = term->u.appl.args[i];
        }

        if (j==1) {
            return args[0];
        } else {
            return _ex_intern_appl_env(env,term->u.appl.functor, j, args);
        }
    }

    for (i = 0; i < term->u.appl.count; ++i) {
        res = extract_term(env,quant,term->u.appl.args[i]);
        if (res) {
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * term->u.appl.count);
            for (j = 0; j < term->u.appl.count; ++j) {
                args[j] = term->u.appl.args[j];
            }
            args[i] = true_case;
            true_case = _th_flatten(env,_ex_intern_appl_env(env,term->u.appl.functor,j,args));
            for (j = 0; j < term->u.appl.count; ++j) {
                args[j] = term->u.appl.args[j];
            }
            args[i] = false_case;
            false_case = _th_flatten(env,_ex_intern_appl_env(env,term->u.appl.functor,j,args));
            return res;
        }
    }
    return NULL;
}

struct _ex_intern *_th_remove_free_terms(struct env *env, struct _ex_intern *quant)
{
    struct _ex_intern *cond, *tset, *fset, *e;

    cond = extract_term(env,quant,quant->u.quant.cond);

    if (cond) {
        tset = _ex_intern_quant(INTERN_SETQ,quant->u.quant.var_count,quant->u.quant.vars,
                                quant->u.quant.exp,true_case);
        fset = _ex_intern_quant(INTERN_SETQ,quant->u.quant.var_count,quant->u.quant.vars,
                                quant->u.quant.exp,false_case);

        e = _th_remove_free_terms(env,tset);
        if (e) tset = e;
        e = _th_remove_free_terms(env,fset);
        if (e) fset = e;

        return _ex_intern_appl3_env(env,INTERN_ITE, cond, tset, fset);
    }

    return NULL;
}

static struct segment_list {
    struct segment_list *next;
    struct _ex_intern *low;
    struct _ex_intern *high;
};

static struct base_list {
    struct base_list *next;
    struct _ex_intern *base;
    struct segment_list *segments;
};

static struct base_list *add_not(struct env *env, struct base_list *list, struct _ex_intern *value)
{
    struct _ex_intern *base;
    struct _ex_intern *offset;
    int i, j, k;
    struct _ex_intern **args;
    struct base_list *l;
    struct segment_list *s, *ps, *ms;

    if (value->type==EXP_INTEGER) {
        offset = value;
        base = _ex_intern_small_integer(0);
    } else if (value->type==EXP_APPL && value->u.appl.functor==INTERN_NAT_PLUS) {
        for (i = 0; i < value->u.appl.count; ++i) {
            if (value->u.appl.args[i]->type==EXP_INTEGER) {
                offset = value->u.appl.args[i];
                args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * value->u.appl.count);
                for (j = 0, k = 0; j < value->u.appl.count; ++j) {
                    if (j != i) args[k++] = value->u.appl.args[j];
                }
                base = _ex_intern_appl_env(env,INTERN_NAT_PLUS,k,args);
                goto cont;
            }
        }
        offset = _ex_intern_small_integer(0);
        base = value;
    } else {
        offset = _ex_intern_small_integer(0);
        base = value;
    }
cont:
    l = list;
    while (l != NULL) {
        if (l->base==base) break;
        l = l->next;
    }
    if (!l) {
        l = (struct base_list *)_th_alloc(REWRITE_SPACE,sizeof(struct base_list));
        l->next = list;
        list = l;
        l->base = base;
        l->segments = NULL;
    }

    s = l->segments;
    while (s != NULL) {
        if (_th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,s->high,_ex_intern_small_integer(1)),1)==offset) {
            s->high = offset;
            ps = ms = s;
            s = s->next;
            while (s) {
                if (_th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,s->low,_ex_intern_small_integer(-1)),1)==offset) {
                    ps->next = s->next;
                    ms->high = s->high;
                    return list;
                }
                s = s->next;
                ps = ps->next;
            }
            return list;
        }
        if (_th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,s->low,_ex_intern_small_integer(-1)),1)==offset) {
            s->low = offset;
            ps = ms = s;
            s = s->next;
            while (s) {
                if (_th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,s->high,_ex_intern_small_integer(1)),1)==offset) {
                    ps->next = s->next;
                    ms->low = s->low;
                    return list;
                }
                s = s->next;
                ps = ps->next;
            }
            return list;
        }
        if (!_th_big_less(s->high->u.integer,offset->u.integer) && !_th_big_less(offset->u.integer,s->low->u.integer)) return list;
        s = s->next;
    }
    if (s==NULL) {
        s = (struct segment_list *)_th_alloc(REWRITE_SPACE,sizeof(struct segment_list));
        s->next = l->segments;
        l->segments = s;
        s->low = s->high = offset;
    }

    return list;
}

static struct _ex_intern *integrate_and(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *f = e->u.appl.args[0]->u.quant.exp;
    unsigned var = e->u.appl.args[0]->u.quant.vars[0];
    struct _ex_intern *g, *a;
    struct base_list *segments = NULL;
    int i, j, k;
    struct _ex_intern **args;

    if (f->type != EXP_APPL || f->u.appl.functor != INTERN_ITE) return NULL;
    if (f->u.appl.args[1] != _ex_intern_small_integer(0)) return NULL;
    g = f->u.appl.args[0];

    if (g->type != EXP_APPL || g->u.appl.functor != INTERN_AND) return NULL;

    for (i = 0; i < g->u.appl.count; ++i) {
        if (!_th_is_free_in(g->u.appl.args[i], var)) {
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * g->u.appl.count);
            for (j = 0, k = 0; j < g->u.appl.count; ++j) {
                if (i != j) args[k++] = g->u.appl.args[j];
            }
            return _ex_intern_appl3_env(env,INTERN_ITE,g->u.appl.args[i],
                       _ex_intern_appl3_env(env,INTERN_NAT_INTEGRATE,
                           _ex_intern_quant(INTERN_LAMBDA,e->u.appl.args[0]->u.quant.var_count,e->u.appl.args[0]->u.quant.vars,
                               _ex_intern_appl3_env(env,INTERN_ITE,
                                   _ex_intern_appl_env(env,INTERN_AND,k,args),
                                   f->u.appl.args[1],
                                   f->u.appl.args[2]),
                               _ex_true),
                           e->u.appl.args[1],
                           e->u.appl.args[2]),
                       _ex_intern_small_integer(0));
        }
    }

    for (i = 0; i < g->u.appl.count; ++i) {
        a = _th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_SOLVE_FOR,_ex_intern_var(var),g->u.appl.args[i]), 1);
        if (a->type==EXP_APPL && a->u.appl.functor==INTERN_SOLVE_FOR) a = g->u.appl.args[i];
        if (a->type != EXP_APPL || a->u.appl.functor != INTERN_NOT || a->u.appl.count != 1) return NULL;
        a = a->u.appl.args[0];
        if (a->u.appl.args[0]->type==EXP_VAR && a->u.appl.args[0]->u.var==var) {
            a = a->u.appl.args[1];
        } else if (a->u.appl.args[1]->type==EXP_VAR && a->u.appl.args[1]->u.var==var) {
            a = a->u.appl.args[0];
        } else {
            return NULL;
        }
        if (_th_is_free_in(a,var)) return NULL;
        segments = add_not(env, segments, a);
    }
    return NULL;
}

static struct _ex_intern *get_term(unsigned var, struct _ex_intern *eq)
{
    if (eq->type != EXP_APPL || (eq->u.appl.functor != INTERN_EQUAL && eq->u.appl.functor != INTERN_ORIENTED_RULE)) return eq;

    if (eq->u.appl.args[0]==_ex_intern_var(var)) return eq->u.appl.args[1];

    return eq->u.appl.args[0];
}

static struct _ex_intern *sum_sets(struct env *env,
                                   struct _ex_intern *min,
                                   struct _ex_intern *max,
                                   struct _ex_intern *weight,
                                   unsigned var,
                                   struct _ex_intern *equals)
{
    struct _ex_intern **args, **args2, *term;
    int i, j;

    if (equals->type != EXP_APPL) return _ex_intern_small_integer(0);

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * equals->u.appl.count);
    args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (equals->u.appl.count+2));

    for (i = 0; i < equals->u.appl.count; ++i) {
        args2[0] = _ex_intern_appl2_env(env,INTERN_NAT_LESS,min,get_term(var,equals->u.appl.args[i]));
        args2[1] = _ex_intern_appl2_env(env,INTERN_NAT_LESS,get_term(var,equals->u.appl.args[i]),max);
        for (j = 0; j < i; ++j) {
            args2[j+2] = _ex_intern_appl1_env(env,INTERN_NOT,
                           _ex_intern_appl2_env(env,INTERN_EQUAL,
                               get_term(var,equals->u.appl.args[i]),
                               get_term(var,equals->u.appl.args[j])));
        }
        if (weight->type==EXP_QUANT && weight->u.quant.quant==INTERN_LAMBDA) {
            term = _ex_intern_appl2_env(env,INTERN_APPLY,weight,_ex_intern_var(var));
        } else {
            term = weight;
        }
        args[i] = _ex_intern_appl3_env(env,INTERN_ITE,
                      _ex_intern_appl_env(env,INTERN_AND,j+2,args2),
                      term,
                      _ex_intern_small_integer(0));
    }

    return _ex_intern_appl_env(env,INTERN_NAT_PLUS,i,args);
}

int _th_not_limit = 3;
static struct _ex_intern *min_term, *max_term, *eq_term;
struct _ex_intern *_th_range_set_size(struct env *env, struct _ex_intern *set)
{
    struct add_list *min = NULL, *max = NULL, *ne = NULL, *a;
    struct _ex_intern **args;
    unsigned var;
    int i, count;
    int not_count = 0;

    if (set->type != EXP_QUANT) return NULL;
    if (set->u.quant.quant != INTERN_SETQ) return NULL;
    if (set->u.quant.var_count != 1) return NULL;
    if (set->u.quant.cond->type != EXP_APPL ||
        set->u.quant.cond->u.appl.functor != INTERN_AND) return NULL;

    var = set->u.quant.vars[0];

    //printf("here1 %d %s\n", var, _th_intern_decode(var));

    for (i = 0; i < set->u.quant.cond->u.appl.count; ++i) {
        struct _ex_intern *e = set->u.quant.cond->u.appl.args[i];
        //_tree_print_exp("Arg", e);
        if (e->type != EXP_APPL) return NULL;
        switch (e->u.appl.functor) {
            case INTERN_NAT_LESS:
                if (e->u.appl.args[0]->type==EXP_VAR && e->u.appl.args[0]->u.var==var &&
                    !_th_is_free_in(e->u.appl.args[1],var)) {
                    struct add_list *m = (struct add_list *)ALLOCA(sizeof(struct add_list));
                    m->next = max;
                    max = m;
                    m->e = e->u.appl.args[1];
                } else if (e->u.appl.args[1]->type==EXP_VAR && e->u.appl.args[1]->u.var==var &&
                    !_th_is_free_in(e->u.appl.args[0],var)) {
                    struct add_list *m = (struct add_list *)ALLOCA(sizeof(struct add_list));
                    m->next = min;
                    min = m;
                    m->e = e->u.appl.args[0];
                } else {
                    return NULL;
                }
                break;
            case INTERN_NOT:
                ++not_count;
                if (not_count > _th_not_limit) return NULL;
                e = e->u.appl.args[0];
                if (e->type != EXP_APPL) return NULL;
                switch (e->u.appl.functor) {
                    case INTERN_NAT_LESS:
                        if (e->u.appl.args[0]->type==EXP_VAR && e->u.appl.args[0]->u.var==var &&
                            !_th_is_free_in(e->u.appl.args[1],var)) {
                            struct add_list *m = (struct add_list *)ALLOCA(sizeof(struct add_list));
                            m->next = min;
                            min = m;
                            m->e = _ex_intern_appl2_env(env,INTERN_NAT_PLUS,e->u.appl.args[1],_ex_intern_small_integer(-1));
                        } else if (e->u.appl.args[1]->type==EXP_VAR && e->u.appl.args[1]->u.var==var &&
                            !_th_is_free_in(e->u.appl.args[0],var)) {
                            struct add_list *m = (struct add_list *)ALLOCA(sizeof(struct add_list));
                            m->next = max;
                            max = m;
                            m->e = _ex_intern_appl2_env(env,INTERN_NAT_PLUS,e->u.appl.args[0],_ex_intern_small_integer(1));
                        } else {
                            return NULL;
                        }
                        break;
                    case INTERN_EQUAL:
                        if (e->u.appl.args[0]->type==EXP_VAR && e->u.appl.args[0]->u.var==var &&
                            !_th_is_free_in(e->u.appl.args[1],var)) {
                            struct add_list *m = (struct add_list *)ALLOCA(sizeof(struct add_list));
                            m->next = ne;
                            ne = m;
                            m->e = e;
                        } else if (e->u.appl.args[1]->type==EXP_VAR && e->u.appl.args[1]->u.var==var &&
                            !_th_is_free_in(e->u.appl.args[0],var)) {
                            struct add_list *m = (struct add_list *)ALLOCA(sizeof(struct add_list));
                            m->next = ne;
                            ne = m;
                            m->e = e;
                        } else {
                            return NULL;
                        }
                        break;
                    case INTERN_ORIENTED_RULE:
                        //_zone_print0("Here1");
                        if (e->u.appl.args[2] != _ex_true) return NULL;
                        //_zone_print0("Here2");
                        if (e->u.appl.args[0]->type==EXP_VAR && e->u.appl.args[0]->u.var==var &&
                            !_th_is_free_in(e->u.appl.args[1],var)) {
                            struct add_list *m = (struct add_list *)ALLOCA(sizeof(struct add_list));
                            //_zone_print0("Here3");
                            m->next = ne;
                            ne = m;
                            m->e = e;
                        } else {
							return NULL;
						}
                        break;
                    default:
                        return NULL;
                }
                break;
            default:
                return NULL;
        }
    }

    if (min==NULL) return NULL;
    a = min;
    count = 0;
    while (a) {
        a = a->next;
        ++count;
    }
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
    a = min;
    for (i = 0; i < count; ++i) {
        args[i] = a->e;
        a = a->next;
    }
    min_term = _ex_intern_appl_env(env,INTERN_NAT_MAX,count,args);

    if (max==NULL) return NULL;
    a = max;
    count = 0;
    while (a) {
        a = a->next;
        ++count;
    }
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
    a = max;
    for (i = 0; i < count; ++i) {
        args[i] = a->e;
        a = a->next;
    }
    max_term = _ex_intern_appl_env(env,INTERN_NAT_MIN,count,args);

    if (ne==NULL) {
        eq_term = _ex_false;
    } else {
        a = ne;
        count = 0;
        while (a) {
            a = a->next;
            ++count;
        }
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
        a = ne;
        for (i = 0; i < count; ++i) {
            args[i] = a->e;
            a = a->next;
        }
        eq_term = _ex_intern_appl_env(env,INTERN_OR,count,args);
    }

    //printf("min_term = %s\n", _th_print_exp(min_term));
    //printf("max_term = %s\n", _th_print_exp(max_term));
    //printf("eq_term = %s\n", _th_print_exp(eq_term));
    //fflush(stdout);

    return _ex_intern_appl3_env(env,INTERN_ITE,
               _ex_intern_appl2_env(env,INTERN_NAT_LESS,min_term,max_term),
               _ex_intern_appl2_env(env,INTERN_NAT_MINUS,
                   _ex_intern_appl2_env(env,INTERN_NAT_PLUS,
                       _ex_intern_appl2_env(env,INTERN_NAT_MINUS,
                           max_term,
                           min_term),
                       _ex_intern_small_integer(-1)),
                   sum_sets(env,min_term,max_term,_ex_intern_small_integer(1),var,eq_term)),
               _ex_intern_small_integer(0));
}

struct _ex_intern *_th_simplify_nat_integrate(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *f, *h, *st;
    struct _ex_intern **args;
	int i, j, k;

	if (e->u.appl.count==3 &&
		e->u.appl.args[0]->type==EXP_QUANT &&
		e->u.appl.args[0]->u.quant.quant==INTERN_LAMBDA &&
		e->u.appl.args[0]->u.quant.var_count == 1) {
		f = e->u.appl.args[0];
		if (!_th_is_free_in(f->u.quant.exp, f->u.quant.vars[0])) {
			return _ex_intern_appl2_env(env,INTERN_NAT_TIMES,
				_ex_intern_appl2_env(env,INTERN_NAT_PLUS,
				_ex_intern_appl2_env(env,INTERN_NAT_MINUS,
				e->u.appl.args[2],
				e->u.appl.args[1]),
				_ex_intern_small_integer(1)),
				f->u.quant.exp);
		}
		h = integrate_and(env, e);
		if (h) return h;
		if (f->u.quant.exp->type==EXP_APPL && (f->u.quant.exp->u.appl.functor==
			INTERN_NAT_PLUS || f->u.quant.exp->u.appl.functor==INTERN_NAT_MINUS)) {
			args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * f->u.quant.exp->u.appl.count);
			for (i = 0; i < f->u.quant.exp->u.appl.count; ++i) {
				args[i] = _ex_intern_appl3_env(env,INTERN_NAT_INTEGRATE,
					_ex_intern_quant(INTERN_LAMBDA,
					f->u.quant.var_count,
					f->u.quant.vars,
					f->u.quant.exp->u.appl.args[i],
					f->u.quant.cond),
					e->u.appl.args[1],
					e->u.appl.args[2]);
			}
			return _ex_intern_appl_env(env,f->u.quant.exp->u.appl.functor,f->u.quant.exp->u.appl.count,args);
		}
		if (f->u.quant.exp->type==EXP_VAR && f->u.quant.exp->u.var==f->u.quant.vars[0]) {
			return _ex_intern_appl2_env(env,INTERN_NAT_DIVIDE,
				_ex_intern_appl3_env(env,INTERN_NAT_PLUS,
				_ex_intern_appl2_env(env,INTERN_NAT_MINUS,
				_ex_intern_appl2_env(env,INTERN_NAT_TIMES,
				e->u.appl.args[2],
				e->u.appl.args[2]),
				_ex_intern_appl2_env(env,INTERN_NAT_TIMES,
				e->u.appl.args[1],
				e->u.appl.args[1])),
				e->u.appl.args[1],
				e->u.appl.args[2]),
				_ex_intern_small_integer(2));
			
		}
		if (f->u.quant.exp->type==EXP_APPL && f->u.quant.exp->u.appl.functor==INTERN_NAT_TIMES) {
			h = f->u.quant.exp;
			//_zone_print2("Dividing %s %d", _th_print_exp(h), h->u.appl.count);
			for (i = 0; i < h->u.appl.count; ++i) {
				//_zone_print1("before test %d", h->u.appl.count);
				if (!_th_is_free_in(h->u.appl.args[i],f->u.quant.vars[0])) {
					//_zone_print0("allocating %d %d", i, h->u.appl.count);
					args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * h->u.appl.count);
					//_zone_print0("allocation done");
					for (j = 0, k= 0; j < h->u.appl.count; ++j) {
						if (j != i) {
							args[k++] = h->u.appl.args[j];
						}
					}
					return _ex_intern_appl2_env(env, INTERN_NAT_TIMES,
						h->u.appl.args[i],
						_ex_intern_appl3_env(env,INTERN_NAT_INTEGRATE,
						_ex_intern_quant(INTERN_LAMBDA,f->u.quant.var_count,
						f->u.quant.vars,
						_ex_intern_appl_env(env,INTERN_NAT_TIMES,
						k,args),
						f->u.quant.cond),
						e->u.appl.args[1],
						e->u.appl.args[2]));
				}
				//_zone_print2("h = %s %d\n", _th_print_exp(h), h->u.appl.count);
			}
		}
		h = f->u.quant.exp;
		if (h->type==EXP_APPL && h->u.appl.functor==INTERN_ITE &&
			h->u.appl.count==3 && h->u.appl.args[0]->type==EXP_APPL && h->u.appl.args[0]->u.appl.functor==INTERN_AND &&
			h->u.appl.args[0]->u.appl.count > 1) {
			return _ex_intern_appl3_env(env,INTERN_NAT_INTEGRATE,
				_ex_intern_quant(INTERN_LAMBDA,
				f->u.quant.var_count,
				f->u.quant.vars,
				_ex_intern_appl3_env(env,INTERN_ITE,
				h->u.appl.args[0]->u.appl.args[0],
				_ex_intern_appl3_env(env,INTERN_ITE,
				_ex_intern_appl_env(env,INTERN_AND,h->u.appl.args[0]->u.appl.count-1,h->u.appl.args[0]->u.appl.args+1),
				h->u.appl.args[1],
				h->u.appl.args[2]),
				h->u.appl.args[2]),
				f->u.quant.cond
				),
				e->u.appl.args[1],
				e->u.appl.args[2]);
		}
		if (h->type==EXP_APPL && h->u.appl.functor==INTERN_ITE &&
			h->u.appl.count==3 && h->u.appl.args[0]->type==EXP_APPL &&
			(h->u.appl.args[0]->u.appl.functor==INTERN_EQUAL ||
			h->u.appl.args[0]->u.appl.functor==INTERN_ORIENTED_RULE ||
			h->u.appl.args[0]->u.appl.functor==INTERN_NAT_LESS) &&
			(h->u.appl.args[0]->u.appl.args[0]->type != EXP_VAR ||
			h->u.appl.args[0]->u.appl.args[0]->u.var != f->u.quant.vars[0]) &&
			(h->u.appl.args[0]->u.appl.args[1]->type != EXP_VAR ||
			h->u.appl.args[0]->u.appl.args[1]->u.var != f->u.quant.vars[0])
			) {
			_zone_print2("Solving %s %s", _th_print_exp(h->u.appl.args[0]), _th_intern_decode(f->u.quant.vars[0]));
			st = _th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_SOLVE_FOR,
				_ex_intern_var(f->u.quant.vars[0]),
				h->u.appl.args[0]), 1);
			_zone_print_exp("Result", st);
			if (st->type != EXP_APPL || st->u.appl.functor != INTERN_SOLVE_FOR) {
				return _ex_intern_appl3_env(env,INTERN_NAT_INTEGRATE,
					_ex_intern_quant(INTERN_LAMBDA,
					f->u.quant.var_count,
					f->u.quant.vars,
					_ex_intern_appl3_env(env,INTERN_ITE,
					st,
					h->u.appl.args[1],
					h->u.appl.args[2]),
					f->u.quant.cond
					),
					e->u.appl.args[1],
					e->u.appl.args[2]);
			}
		}
		h = extract_term(env, f, f->u.quant.exp);
		if (h) {
			return _ex_intern_appl3_env(env,INTERN_ITE,
				h,
				_ex_intern_appl3_env(env,INTERN_NAT_INTEGRATE,
				_ex_intern_quant(f->u.quant.quant,
				f->u.quant.var_count,
				f->u.quant.vars,
				true_case,
				f->u.quant.cond),
				e->u.appl.args[1],
				e->u.appl.args[2]),
				_ex_intern_appl3_env(env,INTERN_NAT_INTEGRATE,
				_ex_intern_quant(f->u.quant.quant,
				f->u.quant.var_count,
				f->u.quant.vars,
				false_case,
				f->u.quant.cond),
				e->u.appl.args[1],
				e->u.appl.args[2]));
		}
        f = _ex_intern_appl2_env(env,INTERN_NAT_MINUS,e->u.appl.args[1],e->u.appl.args[2]);
        f = _th_int_rewrite(env,f, 1);
        if (_th_equal(env,f,_ex_intern_small_integer(1))) return _ex_intern_small_integer(0);
    }
	return NULL;
}

struct _ex_intern *_th_simplify_nat_solve_integrate(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *f, *h;

	if (e->u.appl.count==3 &&
		e->u.appl.args[0]->type==EXP_QUANT &&
		e->u.appl.args[0]->u.quant.quant==INTERN_LAMBDA &&
		e->u.appl.args[0]->u.quant.var_count == 1) {
		f = e->u.appl.args[0];
		h = extract_term(env, f, f->u.quant.exp);
		if (h) {
			return _ex_intern_appl3_env(env,INTERN_ITE,
				h,
				_ex_intern_appl3_env(env,INTERN_NAT_SOLVE_INTEGRATE,
				_ex_intern_quant(f->u.quant.quant,
				f->u.quant.var_count,
				f->u.quant.vars,
				true_case,
				f->u.quant.cond),
				e->u.appl.args[1],
				e->u.appl.args[2]),
				_ex_intern_appl3_env(env,INTERN_NAT_SOLVE_INTEGRATE,
				_ex_intern_quant(f->u.quant.quant,
				f->u.quant.var_count,
				f->u.quant.vars,
				false_case,
				f->u.quant.cond),
				e->u.appl.args[1],
				e->u.appl.args[2]));
		}
		h = f->u.quant.exp;
		if (h->type==EXP_APPL && h->u.appl.functor==INTERN_ITE &&
			h->u.appl.count==3 && h->u.appl.args[0]->type==EXP_APPL && h->u.appl.args[0]->u.appl.functor==INTERN_AND &&
			h->u.appl.args[0]->u.appl.count > 1) {
			return _ex_intern_appl3_env(env,INTERN_NAT_SOLVE_INTEGRATE,
				_ex_intern_quant(INTERN_LAMBDA,
				f->u.quant.var_count,
				f->u.quant.vars,
				_ex_intern_appl3_env(env,INTERN_ITE,
				h->u.appl.args[0]->u.appl.args[0],
				_ex_intern_appl3_env(env,INTERN_ITE,
				_ex_intern_appl_env(env,INTERN_AND,h->u.appl.args[0]->u.appl.count-1,h->u.appl.args[0]->u.appl.args+1),
				h->u.appl.args[1],
				h->u.appl.args[2]),
				h->u.appl.args[2]),
				f->u.quant.cond
				),
				e->u.appl.args[1],
				e->u.appl.args[2]);
		}
		if (h->type==EXP_INTEGER) {
			if (h->u.integer[0]==1 && h->u.integer[1]==0) return NULL;
			return _ex_intern_appl2_env(env,INTERN_NAT_PLUS,
				_ex_intern_appl2_env(env,INTERN_NAT_MINUS,e->u.appl.args[1],_ex_intern_small_integer(1)),
				_ex_intern_appl2_env(env,INTERN_NAT_DIVIDE,
				_ex_intern_appl3_env(env,INTERN_ITE,
				_ex_intern_appl2_env(env,INTERN_NAT_LESS,
				_ex_intern_small_integer(-1),
				e->u.appl.args[2]),
				e->u.appl.args[2],
				_ex_intern_appl2_env(env,INTERN_NAT_MINUS,
				e->u.appl.args[2],
				_ex_intern_appl2_env(env,INTERN_NAT_MINUS,
				h,
				_ex_intern_small_integer(1)))),
				h));    
		}
	}
	return NULL;
}

struct _ex_intern *_th_simplify_nat_integrate_set(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *f, *h;
	int i;

	if (e->u.appl.count==2 &&
		e->u.appl.args[0]->type==EXP_QUANT &&
		e->u.appl.args[0]->u.quant.quant==INTERN_LAMBDA &&
		e->u.appl.args[0]->u.quant.var_count == 1) {
		f = e->u.appl.args[0];
		if (!_th_is_free_in(f->u.quant.exp,f->u.quant.vars[0])) {
			return _ex_intern_appl2_env(env,INTERN_NAT_TIMES,
				f->u.quant.exp,
				_ex_intern_appl1_env(env,INTERN_SETSIZE,
				e->u.appl.args[1]));
		}
		h = extract_term(env, f, f->u.quant.exp);
		if (h) {
			return _ex_intern_appl3_env(env,INTERN_ITE,
				h,
				_ex_intern_appl3_env(env,INTERN_NAT_INTEGRATE_SET,
				_ex_intern_quant(f->u.quant.quant,
				f->u.quant.var_count,
				f->u.quant.vars,
				true_case,
				f->u.quant.cond),
				e->u.appl.args[1],
				e->u.appl.args[2]),
				_ex_intern_appl3_env(env,INTERN_NAT_INTEGRATE_SET,
				_ex_intern_quant(f->u.quant.quant,
				f->u.quant.var_count,
				f->u.quant.vars,
				false_case,
				f->u.quant.cond),
				e->u.appl.args[1],
				e->u.appl.args[2]));
		}
	}
	h = e->u.appl.args[1];
	if (h->type==EXP_QUANT && h->u.appl.functor==INTERN_SETQ) {
		f = _th_range_set_size(env,h);
		if (f) {
			_zone_print_exp("f =", f);
			_zone_print_exp("eq_term =", eq_term);
			if (eq_term->type==EXP_APPL && eq_term->u.appl.functor==INTERN_OR) {
#ifdef USE_EQ_TERM
				args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * eq_term->u.appl.count);
				for (i = 0; i < eq_term->u.appl.count; ++i) {
					f = eq_term->u.appl.args[i];
					if (f->u.appl.args[0]->type==INTERN_VAR &&
						f->u.appl.args[0]->u.var==h->u.quant.vars[0]) {
						f = f->u.appl.args[1];
					} else {
						f = f->u.appl.args[0];
					}
					args[i] = _ex_intern_appl2_env(env,INTERN_APPLY,
						e->u.appl.args[0],
						f);
					_zone_print2("args[%d] = %s", i, _th_print_exp(args[i]));
				}
#endif
				return NULL;
			} else {
				i = 0;
			}
#ifdef USE_EQ_TERM
			return _ex_intern_appl2_env(env,INTERN_NAT_MINUS,
				_ex_intern_appl3_env(env,INTERN_NAT_INTEGRATE,
				e->u.appl.args[0],
				_ex_intern_appl2_env(env,INTERN_NAT_PLUS,min_term,_ex_intern_small_integer(1)),
				_ex_intern_appl2_env(env,INTERN_NAT_PLUS,max_term,_ex_intern_small_integer(-1))),
				sum_sets(env,min_term,max_term,e->u.appl.args[0],e->u.appl.args[1]->u.quant.vars[0],eq_term));
#endif
			return _ex_intern_appl3_env(env,INTERN_NAT_INTEGRATE,
				e->u.appl.args[0],
				_ex_intern_appl2_env(env,INTERN_NAT_PLUS,min_term,_ex_intern_small_integer(1)),
				_ex_intern_appl2_env(env,INTERN_NAT_PLUS,max_term,_ex_intern_small_integer(-1)));
		}
	}
	return NULL;
}

void _th_add_calculus_rules(int s, struct env *env)
{
    /*_th_add_property(env,_th_parse(env, "(-> (nsolveintegrate (lambda x (ite (== x n) c e_)) l v) \
                                               (ite (|| (&& (nless n l) (not (nless v (nintegrate (lambda x e_) l n)))) (&& (not (nless  n l)) (not (nless (nintegrate (lambda x e_) l (nminus n 1)) v)))) \
                                                   (nsolveintegrate (lambda x e_) l v) \
                                                   (ite (&& (not (nless n l)) (nless v (nplus (nintegrate (lambda x e_) l (nminus n 1)) c))) \
                                                       (nminus n 1) \
                                                       (ite  (not (nless n l)) \
                                                           (nsolveintegrate (lambda x e_) (nplus n 1) (nminus v (nplus c (nintegrate(lambda x e_) l (nminus n 1))))) \
                                                           (ite (&& (nless l n) (not (nless v (nminus (nintegrate (lambda x e_) l n) c)))) \
                                                               n \
                                                               (nsolveintegrate (lambda x e_) (nminus n 1) (nplus v (nminus c (nintegrate (lambda x e_) l n)))) \
                                                           ) \
                                                       ) \
                                                   ) \
                                               ) \
                                           (True))"));

    _th_add_property(env,_th_parse(env, "(-> (nsolveintegrate (lambda x (ite (-> x n (True)) c e_)) l v) \
                                               (ite (|| (&& (nless n l) (not (nless v (nintegrate (lambda x e_) l n)))) (&& (not (nless n l)) (not (nless (nintegrate (lambda x e_) l (nminus n 1)) v)))) \
                                                   (nsolveintegrate (lambda x e_) l v) \
                                                   (ite (&& (not (nless n l)) (nless v (nplus (nintegrate (lambda x e_) l (nminus n 1)) c))) \
                                                       (nminus n 1) \
                                                       (ite (not (nless n l)) \
                                                           (nsolveintegrate (lambda x e_) (nplus n 1) (nminus v (nplus c (nintegrate(lambda x e_) l (nminus n 1))))) \
                                                           (ite (&& (nless l n) (not (nless v (nminus (nintegrate (lambda x e_) l n) c)))) \
                                                               n \
                                                               (nsolveintegrate (lambda x e_) (nminus n 1) (nplus v (nminus c (nintegrate (lambda x e_) l n)))) \
                                                           ) \
                                                       ) \
                                                   ) \
                                               ) \
                                           (True))"));

    _th_add_property(env,_th_parse(env, "(-> (nsolveintegrate (lambda x (ite (nless n x) t_ f_)) l v) \
                                               (ite (&& (not (nless n l)) (not (nless (nintegrate (lambda x f_) l n) v))) \
                                                   (nsolveintegrate (lambda x f_) l v) \
                                                   (ite (&& (nless n l) (not (nless v (nintegrate (lambda x t_) l n)))) \
                                                       (nsolveintegrate (lambda x t_) l v) \
                                                       (ite (nless n l) \
                                                           (nsolveintegrate (lambda x f_) (nplus n 1) (nminus v (nintegrate (lambda x t_) l n))) \
                                                           (nsolveintegrate (lambda x t_) (nplus n 1) (nminus v (nintegrate (lambda x f_) l n))) \
                                                       ) \
                                                   ) \
                                               ) \
                                           (True))"));

    _th_add_property(env,_th_parse(env, "(-> (nsolveintegrate (lambda x (ite (nless x n) t_ f_)) l v) \
                                               (ite (&& (not (nless l n)) (not (nless v (nintegrate (lambda x f_) l (nminus n 1))))) \
                                                   (nsolveintegrate (lambda x f_) l v) \
                                                   (ite (&& (nless l n) (not (nless (nintegrate (lambda x t_) l (nminus n 1)) v))) \
                                                       (nsolveintegrate (lambda x t_) l v) \
                                                       (ite (nless l n) \
                                                           (nsolveintegrate (lambda x f_) n (nminus v (nintegrate (lambda x t_) l (nminus n 1)))) \
                                                           (nsolveintegrate (lambda x t_) n (nminus v (nintegrate (lambda x f_) l (nminus n 1)))) \
                                                       ) \
                                                   ) \
                                               ) \
                                           (True))"));*/

    _th_add_property(env,_th_parse(env, "(-> (nintegrate (lambda x (ite (== x n) c e_)) l h) \
                                           (ite (&& (not (nless n l)) (not (nless h n))) \
                                               (nplus c \
                                                   (nintegrate (lambda x e_) l (nminus n 1)) \
                                                   (nintegrate (lambda x e_) (nplus n 1) h)) \
                                               (ite (&& (nless h n) (nless n l)) \
                                                   (nminus \
                                                       (nplus \
                                                           (nintegrate (lambda x e_) l n) \
                                                           (nintegrate (lambda x e_) n h)) \
                                                       c \
                                                   ) \
                                                   (nintegrate (lambda x e_) l h) \
                                               ) \
                                           ) \
                                           (True))"));

    _th_add_property(env,_th_parse(env, "(-> (nintegrate (lambda x (ite (nless x n) e1_ e2_)) l h) \
                                           (ite (&& (not (nless n l)) (not (nless h n))) \
                                               (nplus \
                                                   (nintegrate (lambda x e1_) l (nminus n 1)) \
                                                   (nintegrate (lambda x e2_) n h)) \
                                               (ite (&& (nless h n) (nless n l)) \
                                                   (nplus \
                                                       (nintegrate (lambda x e2_) l (nminus n 1)) \
                                                       (nintegrate (lambda x e1_) n h)) \
                                                   (ite (nless n l) \
                                                       (nintegrate (lambda x e2_) l h) \
                                                       (nintegrate (lambda x e1_) l h) \
                                                   ) \
                                               ) \
                                           ) \
                                           (True))"));

    _th_add_property(env,_th_parse(env, "(-> (nintegrate (lambda x (ite (nless n x) e1_ e2_)) l h) \
                                           (ite (&& (not (nless n l)) (not (nless h n))) \
                                               (nplus \
                                                   (nintegrate (lambda x e2_) l n) \
                                                   (nintegrate (lambda x e1_) (nplus n 1) h)) \
                                               (ite (&& (nless h n) (nless n l)) \
                                                   (nplus \
                                                       (nintegrate (lambda x e1_) l n) \
                                                       (nintegrate (lambda x e2_) (nplus n 1) h)) \
                                                   (ite (nless n l) \
                                                       (nintegrate (lambda x e1_) l h) \
                                                       (nintegrate (lambda x e2_) l h) \
                                                   ) \
                                               ) \
                                           ) \
                                           (True))"));

    _th_add_property(env,_th_parse(env, "(-> (nintegrate (lambda x (ite (-> x n (True)) c e_)) l h) \
                                           (ite (&& (not (nless n l)) (not (nless h n))) \
                                               (nplus c \
                                                   (nintegrate (lambda x e_) l (nminus n 1)) \
                                                   (nintegrate (lambda x e_) (nplus n 1) h)) \
                                               (ite (&& (nless h n) (nless n l)) \
                                                   (nminus \
                                                       (nplus \
                                                           (nintegrate (lambda x e_) l n) \
                                                           (nintegrate (lambda x e_) n h)) \
                                                       c \
                                                   ) \
                                                   (nintegrate (lambda x e_) l h) \
                                               ) \
                                           ) \
                                           (True))"));

    _th_add_property(env,_th_parse(env, "(-> (nsolveintegrate (lambda x 0) l 0) (nminus l 1) (True))"));

    _th_add_property(env,_th_parse(env, "(-> (nintegrate (lambda x 0) a b) 0 (True))"));
}
