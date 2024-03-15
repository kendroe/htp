/*
 * setsize.c
 *
 * Routines for simplifying setsize expressions
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"

struct _ex_intern *union_setsize(struct env *env,struct _ex_intern *sets)
{
    struct _ex_intern **args;
    int i;

    if (sets->u.appl.count==2) {
        return _ex_intern_appl2_env(env,INTERN_NAT_MINUS,
                   _ex_intern_appl2_env(env,INTERN_NAT_PLUS,
                       _ex_intern_appl1_env(env,INTERN_SETSIZE,sets->u.appl.args[0]),
                       _ex_intern_appl1_env(env,INTERN_SETSIZE,sets->u.appl.args[1])),
                   _ex_intern_appl1_env(env,INTERN_SETSIZE,
                       _ex_intern_appl2_env(env,INTERN_INTERSECT,
                                            sets->u.appl.args[0],
                                            sets->u.appl.args[1])));
    } else {
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (sets->u.appl.count+1));
        for (i = 0; i < sets->u.appl.count-1; ++i) {
            args[i] = _ex_intern_appl2_env(env,INTERN_INTERSECT,
                          sets->u.appl.args[0],
                          sets->u.appl.args[i+1]);
        }
        return _ex_intern_appl2_env(env,INTERN_NAT_MINUS,
                   _ex_intern_appl2_env(env,INTERN_NAT_PLUS,
                       _ex_intern_appl1_env(env,INTERN_SETSIZE,sets->u.appl.args[0]),
                       _ex_intern_appl1_env(env,INTERN_SETSIZE,
                           _ex_intern_appl_env(env,INTERN_UNION,sets->u.appl.count-1,sets->u.appl.args+1))),
                   _ex_intern_appl1_env(env,INTERN_SETSIZE,
                       _ex_intern_appl_env(env,INTERN_UNION,sets->u.appl.count-1,args)));
    }
}

static unsigned int *integer_set_size(unsigned var, struct _ex_intern *cond)
{
    int i;
    unsigned *min, *max, normalize[2];

    if (cond->type != EXP_APPL || cond->u.appl.functor != INTERN_AND) NULL;

    min = max = NULL;

    for (i = 0; i < cond->u.appl.count; ++i) {
        struct _ex_intern *e = cond->u.appl.args[i];
        if (e->type != EXP_APPL) return NULL;
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NAT_LESS) {
            if (e->u.appl.args[0]->type==EXP_VAR && e->u.appl.args[0]->u.var==var) {
                if (e->u.appl.args[1]->type==EXP_INTEGER) {
                    max = e->u.appl.args[1]->u.integer;
                } else {
                    return NULL;
                }
            } else if (e->u.appl.args[0]->type==EXP_INTEGER) {
                if (e->u.appl.args[1]->type==EXP_VAR && e->u.appl.args[1]->u.var==var) {
                    min = e->u.appl.args[0]->u.integer;
                } else {
                    return NULL;
                }
            } else {
                return NULL;
            }
        } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
            e = e->u.appl.args[0];
            if (e->type != EXP_APPL || (e->u.appl.functor != INTERN_EQUAL && e->u.appl.functor != INTERN_ORIENTED_RULE)) return NULL;
            if (e->u.appl.count==3 && e->u.appl.args[2] != _ex_true) return NULL;
            if (e->u.appl.args[0]->type==EXP_INTEGER) {
                if (e->u.appl.args[1]->type != EXP_VAR || e->u.appl.args[1]->u.var != var) return NULL;
            } else if (e->u.appl.args[0]->type==EXP_VAR && e->u.appl.args[0]->u.var == var) {
                if (e->u.appl.args[1]->type != EXP_INTEGER) return NULL;
            } else {
                return NULL;
            }
        } else {
            return NULL;
        }
    }
    if (min==NULL || max==NULL) return NULL;
    normalize[0]= 1;
    normalize[1] = cond->u.appl.count-1;
    min = _th_big_sub(max,min);
    min = _th_big_sub(min,normalize);
    return min;
}

static struct _ex_intern *shared_condition_separation(struct env *env, struct _ex_intern *set)
{
    int i, j, k, l, var_pos;
    unsigned var;
    int *in_set;
    struct _ex_intern *e, *min, *max, *f, **args, **args2;
    unsigned *vars;

    //_zone_print1("Shared separation %s", _th_print_exp(set));

    if (set->u.quant.cond->type != EXP_APPL || set->u.quant.cond->u.appl.functor != INTERN_AND) return NULL;
    if (!_th_is_constant(env, set->u.quant.exp)) return NULL;
    if (set->u.quant.var_count<=1) return NULL;

    in_set = (int *)ALLOCA(sizeof(int) * set->u.quant.cond->u.appl.count);

    for (i = 0; i < set->u.quant.var_count; ++i) {
         var = set->u.quant.vars[i];
         e = set->u.quant.cond;
         min = NULL;
         max = NULL;
         //_zone_print1("Checking %d", i);
         for (j = 0; j < e->u.appl.count; ++j) {
             f = e->u.appl.args[j];
             //_zone_print_exp("term", f);
             in_set[j] = 0;
             if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NAT_LESS) {
                 if (f->u.appl.args[0]->type==EXP_VAR && f->u.appl.args[0]->u.var==var) {
                     max = _th_trans_constant(e,1,f->u.appl.args[1], set->u.quant.var_count, set->u.quant.vars);
                     if (max) {
                         max = _ex_intern_appl2_env(env,INTERN_NAT_LESS,f->u.appl.args[0],max);
                         in_set[j] = -2;
                     }
                 }
                 if (f->u.appl.args[1]->type==EXP_VAR && f->u.appl.args[1]->u.var==var) {
                     min = _th_trans_constant(e,0,f->u.appl.args[0], set->u.quant.var_count, set->u.quant.vars);
                     if (min) {
                         min = _ex_intern_appl2_env(env,INTERN_NAT_LESS,min,f->u.appl.args[1]);
                         in_set[j] = -1;
                     }
                 }
             }
             if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NOT) {
                 f = f->u.appl.args[0];
                 if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NAT_LESS) {
                     if (f->u.appl.args[0]->type==EXP_VAR && f->u.appl.args[0]->u.var==var) {
                         min = _th_trans_constant(e,0,f->u.appl.args[1], set->u.quant.var_count, set->u.quant.vars);
                         if (min) {
                             min = _ex_intern_appl1_env(env,INTERN_NOT,
                                       _ex_intern_appl2_env(env,INTERN_NAT_LESS,
                                           f->u.appl.args[0],
                                           min));
                             in_set[j] = -1;
                         }
                     }
                     if (f->u.appl.args[1]->type==EXP_VAR && f->u.appl.args[1]->u.var==var) {
                         max = _th_trans_constant(e,1,f->u.appl.args[0], set->u.quant.var_count, set->u.quant.vars);
                         if (max) {
                             max = _ex_intern_appl1_env(env,INTERN_NOT,
                                       _ex_intern_appl2_env(env,INTERN_NAT_LESS,
                                           max,
                                           f->u.appl.args[1]));
                             in_set[j] = -2;
                         }
                     }
                 }
             }
             if (in_set[j]) {
                 for (k = 0; k < set->u.quant.var_count; ++k) {
                     if (i != k && _th_is_free_in(f,set->u.quant.vars[k])) {
                         goto cont1;
                     }
                 }
                 in_set[j] = 1;
             } else {
                 if (_th_is_free_in(f,var)) {
                     //_zone_print1("free1 %d", j);
                     in_set[j] = 1;
                     for (k = 0; k < set->u.quant.var_count; ++k) {
                         if (i != k && _th_is_free_in(f,set->u.quant.vars[k])) {
                             in_set[j] = 0;
                             goto cont1;
                         }
                     }
                 } else {
                     in_set[j] = 0;
                 }
             }
             //_zone_print2("free3 %d %d", min, max);
cont1: ;
             //_zone_print2("in_set[%d] = %d", j, in_set[j]);
         }
         if (!min || !max) {
             goto cont;
         }
         //_zone_print0("free4");
         var_pos = i;
         goto good;
cont: ;
    }
    return NULL;
good:
    //_zone_print_exp("good", e);
    //_zone_print_exp("min", min);
    //_zone_print_exp("max", max);
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
    args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
    for (i = 0, j = 0, l = 0; i < e->u.appl.count; ++i) {
        if (in_set[i] > 0) {
            args[j++] = e->u.appl.args[i];
        } else {
            args2[l++] = e->u.appl.args[i];
            if (in_set[i]==-1) {
                args[j++] = min;
            }
            if (in_set[i]==-2) {
                args[j++] = max;
            }
        }
    }
    //_zone_print3("sizes %d %d %d", i, j, l);
    vars = (unsigned *)ALLOCA(sizeof(unsigned) * set->u.quant.var_count);
    for (i = 0, k = 0; i < set->u.quant.var_count; ++i) {
        if (i != var_pos) {
            vars[k++] = set->u.quant.vars[i];
        }
    }
    return
        _ex_intern_appl2_env(env,INTERN_NAT_INTEGRATE_SET,
            _ex_intern_quant(INTERN_LAMBDA,1,&var,
                _ex_intern_appl1_env(env,INTERN_SETSIZE,
                    _ex_intern_quant(INTERN_SETQ,k,vars,set->u.quant.exp,
                        _ex_intern_appl_env(env,INTERN_AND,l,args2))),
                    _ex_true),
            _ex_intern_quant(INTERN_SETQ,1,&var,_ex_intern_var(var),
                _ex_intern_appl_env(env,INTERN_AND,j,args)));
}

static struct _ex_intern *check_and_do_separation(struct env *env, struct _ex_intern *set)
{
    unsigned *fv, *used;
    int count, i, j, k, l;
    int *in_set, *keep;
    struct _ex_intern **args;
    struct _ex_intern *exp1, *exp2, *cond1, *cond2;

    if (set->u.quant.cond->type != EXP_APPL || set->u.quant.cond->u.appl.functor != INTERN_AND) return NULL;
    //printf("Here1a\n");
    if (!_th_is_constant(env, set->u.quant.exp)) return NULL;

    fv = _th_get_free_vars_leave_marked(set->u.quant.exp,&count);
    for (i = 0; i < set->u.quant.var_count; ++i) {
        if (!_th_intern_get_data(set->u.quant.vars[i])) {
            for (i = 0; i < count; ++i) {
                _th_intern_set_data(fv[i],0);
            }
            return NULL;
        }
    }
    //printf("count = %d\n", count);
    for (i = 0; i < count; ++i) {
        _th_intern_set_data(fv[i],0);
    }
    in_set = (int *)ALLOCA(sizeof(int) * set->u.quant.var_count);
    keep = (int *)ALLOCA(sizeof(int) * set->u.quant.cond->u.appl.count);
    for (i = 0; i < set->u.quant.cond->u.appl.count; ++i) {
        keep[i] = 1;
        fv = _th_get_free_vars_leave_marked(set->u.quant.cond->u.appl.args[i], &count);
        for (j = 0; j < set->u.quant.var_count; ++j) {
            in_set[j] = _th_intern_get_data(set->u.quant.vars[j]);
        }
        for (j = 0; j < count; ++j) {
            _th_intern_set_data(fv[j],0);
        }
        for (j = 0; j < set->u.quant.cond->u.appl.count; ++j) {
            if (i != j) {
                int direction;
                direction = -1;
                //printf("Processing %d %d %s\n", i, j, _th_print_exp(set->u.quant.cond->u.appl.args[j]));
                fv = _th_get_free_vars(set->u.quant.cond->u.appl.args[j], &count);
                for (k = 0; k < set->u.quant.var_count; ++k) {
                    if (in_set[k]) _th_intern_set_data(set->u.quant.vars[k],1);
                }
                used = (unsigned *)ALLOCA(sizeof(unsigned) * count);
                for (k = 0; k < count; ++k) {
                    used[k] = 0;
                    for (l = 0; l < set->u.quant.var_count; ++l) {
                        used[k] = 1;
                    }
                }
                //printf("    count = %d\n", count);
                //fflush(stdout);
                for (k = 0; k < count; ++k) {
                    if (used[k]) {
                        if (direction==-1) {
                            direction = (_th_intern_get_data(fv[k])&1);
                            //printf("    Setting keep %d to %d\n", j, direction);
                            keep[j] = direction;
                        } else if (_th_intern_get_data(fv[k]) != (unsigned)direction) {
                            for (k = 0; k < set->u.quant.var_count; ++k) {
                                _th_intern_set_data(set->u.quant.vars[k],0);
                            }
                            return NULL;
                        }
                    }
                }
                for (k = 0; k < set->u.quant.var_count; ++k) {
                    _th_intern_set_data(set->u.quant.vars[k],0);
                }
            }
        }
        goto finish;
    }
    return NULL;
finish:
    //for (i = 0; i < set->u.quant.cond->u.appl.count; ++i) {
    //    printf("keep[%d] = %d\n", i, keep[i]);
    //}
    //for (i = 0; i < set->u.quant.var_count; ++i) {
    //    printf("in_set[%d] = %d\n", i, in_set[i]);
    //}
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * set->u.quant.var_count);
    j = 0;
    for (i = 0; i < set->u.quant.var_count; ++i) {
        if (in_set[i]) args[j++] = _ex_intern_var(set->u.quant.vars[i]);
    }
    if (i==j) return NULL;
    exp1 = _ex_intern_appl_env(env,INTERN_T,j,args);
    j = 0;
    for (i = 0; i < set->u.quant.var_count; ++i) {
        if (!in_set[i]) args[j++] = _ex_intern_var(set->u.quant.vars[i]);
    }
    exp2 = _ex_intern_appl_env(env,INTERN_T,j,args);
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * set->u.quant.cond->u.appl.count);
    j = 0;
    for (i = 0; i < set->u.quant.cond->u.appl.count; ++i) {
        if (keep[i]) args[j++] = set->u.quant.cond->u.appl.args[i];
    }
    cond1 = _ex_intern_appl_env(env,INTERN_AND,j,args);
    j = 0;
    for (i = 0; i < set->u.quant.cond->u.appl.count; ++i) {
        if (!keep[i]) args[j++] = set->u.quant.cond->u.appl.args[i];
    }
    cond2 = _ex_intern_appl_env(env,INTERN_AND,j,args);

    return _ex_intern_appl2_env(env,INTERN_NAT_TIMES,
               _ex_intern_appl1_env(env,INTERN_SETSIZE,
                   _ex_intern_quant(INTERN_SETQ,set->u.quant.var_count,set->u.quant.vars,exp1,cond1)),
               _ex_intern_appl1_env(env,INTERN_SETSIZE,
                   _ex_intern_quant(INTERN_SETQ,set->u.quant.var_count,set->u.quant.vars,exp2,cond2)));
}

struct _ex_intern *_th_simplify_setsize(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *f, *h;

	f = e->u.appl.args[0];
    if (f->type==EXP_APPL && f->u.appl.functor==INTERN_SET) {
		return _ex_intern_small_integer(f->u.appl.count);
	}
	if (f->type==EXP_APPL && f->u.appl.functor==INTERN_UNION) {
		return union_setsize(env,f);
	}
	if (f->type==EXP_QUANT && f->u.quant.quant==INTERN_SETQ) {
	    //h = free_finite_variable_expansion(env, f);
		//if (h) {
		//    return h;
		//}
		//h = finite_variable_expansion(env, f);
		//if (h) {
		//    return h;
		//}
		if (_th_is_constant(env,f->u.quant.exp) && f->u.quant.var_count==1) {
			h = _th_range_set_size(env,f);
		    if (h) {
				//printf("Range %s\n", _th_print_exp(h));
				return h;
			}
			//unsigned *res;
			//res = integer_set_size(f->u.quant.vars[0], f->u.quant.cond);
			//if (res) return _ex_intern_integer(res);
		}
#ifdef NOT_USED
		h = f->u.quant.cond;
		if (_th_is_constant(env,f->u.quant.exp) &&
		    h->type==EXP_APPL && h->u.appl.functor==INTERN_AND) {
			for (i = 0; i < h->u.appl.count; ++i) {
				if (h->u.appl.args[i]->type==EXP_APPL &&
					h->u.appl.args[i]->u.appl.functor==INTERN_OR) {
					return separate_or(env,f,h,i);
				}
			}
		}
#endif
		h = check_and_do_separation(env, f);
	    if (h) {
			//printf("Separation %s\n", _th_print_exp(h));
			return h;
		}
		h = shared_condition_separation(env, f);
		if (h) {
			return h;
		}
	}
	return NULL;
}

void _th_add_setsize_rules(int s, struct env *env)
{
    _th_add_property(env,_th_parse(env, "(-> (setsize (ite a tval fval)) (ite a (setsize tval) (setsize fval)) (True))"));
}

