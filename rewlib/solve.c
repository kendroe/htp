/*
 * solve.c
 *
 * Functions for solving an equation (involving integer or real variables)
 * for a particular variable.  This file also contains the generic routines
 * for simplifying addition and multiplication expressions.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"

static int member(struct _ex_intern *e, struct add_list *a)
{
    while (a) {
        if (e==a->e) return 1;
        a = a->next;
    }

    return 0;
}

struct add_list *_th_basic_terms(struct _ex_intern *e, struct add_list *list)
{
    int i;
    struct add_list *a;

    switch (e->type) {
        case EXP_RATIONAL:
        case EXP_INTEGER:
            return list;
        case EXP_APPL:
            if (e->u.appl.functor==INTERN_NAT_PLUS || e->u.appl.functor==INTERN_NAT_TIMES ||
                e->u.appl.functor==INTERN_RAT_PLUS || e->u.appl.functor==INTERN_RAT_TIMES ||
                e->u.appl.functor==INTERN_NAT_DIVIDE || e->u.appl.functor==INTERN_RAT_DIVIDE ||
                e->u.appl.functor==INTERN_NAT_MOD || e->u.appl.functor==INTERN_RAT_MOD ||
                e->u.appl.functor==INTERN_EQUAL || e->u.appl.functor==INTERN_NAT_LESS ||
                e->u.appl.functor==INTERN_RAT_LESS || e->u.appl.functor==INTERN_NOT ||
                e->u.appl.functor==INTERN_ORIENTED_RULE) {
                for (i = 0; i < e->u.appl.count; ++i) {
                    list = _th_basic_terms(e->u.appl.args[i],list);
                }
                return list;
            }
            break;
    }

    if (!member(e,list)) {
        a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        a->next = list;
        a->e = e;
        list = a;
    }

    return list;
}

int _th_is_variable_term(struct _ex_intern *e)
{
    switch (e->type) {
        case EXP_VAR:
        case EXP_MARKED_VAR:
            return 1;

        case EXP_APPL:
            return e->u.appl.functor!=INTERN_NAT_PLUS && e->u.appl.functor!=INTERN_NAT_TIMES &&
                   e->u.appl.functor!=INTERN_RAT_PLUS && e->u.appl.functor!=INTERN_RAT_TIMES &&
                   e->u.appl.functor!=INTERN_NAT_DIVIDE && e->u.appl.functor!=INTERN_RAT_DIVIDE &&
                   e->u.appl.functor!=INTERN_NAT_MOD && e->u.appl.functor!=INTERN_RAT_MOD &&
                   e->u.appl.functor!=INTERN_EQUAL && e->u.appl.functor!=INTERN_NAT_LESS &&
                   e->u.appl.functor!=INTERN_RAT_LESS && e->u.appl.functor!=INTERN_NOT &&
                   e->u.appl.functor!=INTERN_ORIENTED_RULE;

        default:
            return 0;
    }

}

static int contains_variable_term(struct _ex_intern *e, struct _ex_intern *var)
{
    int i;

    if (e==var) return 1;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor==INTERN_NAT_PLUS || e->u.appl.functor==INTERN_NAT_TIMES ||
                e->u.appl.functor==INTERN_RAT_PLUS || e->u.appl.functor==INTERN_RAT_TIMES ||
                e->u.appl.functor==INTERN_NAT_DIVIDE || e->u.appl.functor==INTERN_RAT_DIVIDE ||
                e->u.appl.functor==INTERN_NAT_MOD || e->u.appl.functor==INTERN_RAT_MOD ||
                e->u.appl.functor==INTERN_EQUAL || e->u.appl.functor==INTERN_NAT_LESS ||
                e->u.appl.functor==INTERN_RAT_LESS || e->u.appl.functor==INTERN_NOT ||
                e->u.appl.functor==INTERN_ORIENTED_RULE) {
                for (i = 0; i < e->u.appl.count; ++i) {
                    if (contains_variable_term(e->u.appl.args[i],var)) return 1;
                }
            }

        default:
            return 0;
    }

}

static int valid_plus_term(struct env *env, struct _ex_intern *e, unsigned var);

static int valid_divide_term(struct env *env, struct _ex_intern *e, unsigned var)
{
    if (!_th_is_free_in(e,var)) return 1;
    // For now don't handle divide
    if (e->type==EXP_VAR) return 1;
    return 0;
    if (e->type==EXP_APPL) {
        switch (e->u.appl.functor) {
            case INTERN_NAT_DIVIDE:
                if (_th_is_free_in(e->u.appl.args[1],var)) return 0;
                return valid_plus_term(env,e->u.appl.args[0],var);
            default:
                return valid_plus_term(env,e,var);
        }
    } else return (e->type==EXP_VAR);
}

static int valid_times_term(struct env *env, struct _ex_intern *e, unsigned var)
{
    int i;
    int var_term = -1;

    if (!_th_is_free_in(e,var)) return 1;
    if (e->type==EXP_APPL) {
        switch (e->u.appl.functor) {
            case INTERN_NAT_TIMES:
                for (i = 0; i < e->u.appl.count; ++i) {
                    if (_th_is_free_in(e->u.appl.args[i],var)) {
                        if (var_term==-1) {
                            var_term = i;
                        } else {
                            return 0;
                        }
                        if (!valid_divide_term(env,e->u.appl.args[i],var)) return 0;
                    }
                }
                return 1;
            default:
                return valid_divide_term(env,e,var);
        }
    } else return (e->type==EXP_VAR);
}

static int valid_plus_term(struct env *env, struct _ex_intern *e, unsigned var)
{
    int i;

    if (!_th_is_free_in(e,var)) return 1;
    if (e->type==EXP_APPL) {
        switch (e->u.appl.functor) {
            case INTERN_NAT_PLUS:
            case INTERN_NAT_MINUS:
                for (i = 0; i < e->u.appl.count; ++i) {
                    if (!valid_plus_term(env,e->u.appl.args[i],var)) return 0; 
                }
                return 1;
            default:
                return valid_times_term(env,e,var);
        }
    } else return (e->type == EXP_VAR);
}

static int r_valid_plus_term(struct env *env, struct _ex_intern *e, struct _ex_intern *var);

static int r_valid_divide_term(struct env *env, struct _ex_intern *e, struct _ex_intern *var)
{
    if (!contains_variable_term(e,var)) return 1;
    // For now don't handle divide
    if (_th_is_variable_term(e)) return 1;
    return 0;
    if (e->type==EXP_APPL) {
        switch (e->u.appl.functor) {
            case INTERN_RAT_DIVIDE:
                if (contains_variable_term(e->u.appl.args[1],var)) return 0;
                return r_valid_plus_term(env,e->u.appl.args[0],var);
            default:
                return r_valid_plus_term(env,e,var);
        }
    } else return (e->type==EXP_VAR);
}

static int r_valid_times_term(struct env *env, struct _ex_intern *e, struct _ex_intern *var)
{
    int i;
    int var_term = -1;

    if (!contains_variable_term(e,var)) return 1;
    if (e->type==EXP_APPL) {
        switch (e->u.appl.functor) {
            case INTERN_RAT_TIMES:
                for (i = 0; i < e->u.appl.count; ++i) {
                    if (contains_variable_term(e->u.appl.args[i],var)) {
                        if (var_term==-1) {
                            var_term = i;
                        } else {
                            return 0;
                        }
                        if (!r_valid_divide_term(env,e->u.appl.args[i],var)) return 0;
                    }
                }
                return 1;
            default:
                return r_valid_divide_term(env,e,var);
        }
    } else return (_th_is_variable_term(e));
}

static int r_valid_plus_term(struct env *env, struct _ex_intern *e, struct _ex_intern *var)
{
    int i;

    if (!contains_variable_term(e,var)) return 1;
    if (e->type==EXP_APPL) {
        switch (e->u.appl.functor) {
            case INTERN_RAT_PLUS:
            case INTERN_RAT_MINUS:
                for (i = 0; i < e->u.appl.count; ++i) {
                    if (!r_valid_plus_term(env,e->u.appl.args[i],var)) return 0; 
                }
                return 1;
            default:
                return r_valid_times_term(env,e,var);
        }
    } else return (_th_is_variable_term(e));
}

static int count_times_terms(struct _ex_intern *e)
{
    int i, count;

    if (e->u.appl.functor==INTERN_NAT_PLUS || e->u.appl.functor==INTERN_NAT_MINUS) {
        count = 0;
        for (i = 0; i < e->u.appl.count; ++i) {
            count += count_times_terms(e->u.appl.args[i]);
        }
        return count;
    } else {
        return 1;
    }
}

static int r_count_times_terms(struct _ex_intern *e)
{
    int i, count;

    if (e->u.appl.functor==INTERN_RAT_PLUS || e->u.appl.functor==INTERN_RAT_MINUS) {
        count = 0;
        for (i = 0; i < e->u.appl.count; ++i) {
            count += r_count_times_terms(e->u.appl.args[i]);
        }
        return count;
    } else {
        return 1;
    }
}

static struct _ex_intern **add_times_terms(struct env *env, struct _ex_intern *e, struct _ex_intern **args, int sign)
{
    int i;

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NAT_PLUS) {
        for (i = 0; i < e->u.appl.count; ++i) {
            args = add_times_terms(env, e->u.appl.args[i], args, sign);
        }
        return args;
    }
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NAT_MINUS) {
        args = add_times_terms(env, e->u.appl.args[0], args, sign);
        args = add_times_terms(env, e->u.appl.args[1], args, 1-sign);
        return args;
    }
    if (sign) {
        *args = e;
    } else {
        *args = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_NAT_TIMES,_ex_intern_small_integer(-1),e));
    }
    ++args;
    return args;
}

static struct _ex_intern **r_add_times_terms(struct env *env, struct _ex_intern *e, struct _ex_intern **args, int sign)
{
    int i;

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_PLUS) {
        for (i = 0; i < e->u.appl.count; ++i) {
            args = r_add_times_terms(env, e->u.appl.args[i], args, sign);
        }
        return args;
    }
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_MINUS) {
        args = r_add_times_terms(env, e->u.appl.args[0], args, sign);
        args = r_add_times_terms(env, e->u.appl.args[1], args, 1-sign);
        return args;
    }
    if (sign) {
        *args = e;
    } else {
        *args = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_RAT_TIMES,_ex_intern_small_rational(-1,1),e));
    }
    ++args;
    return args;
}

static struct _ex_intern *normalize_to_plus(struct env *env, struct _ex_intern *e)
{
    int c = count_times_terms(e);
    struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * c);

    add_times_terms(env, e, args, 1);

    return _ex_intern_appl_env(env,INTERN_NAT_PLUS,c,args);
}

static struct _ex_intern *r_normalize_to_plus(struct env *env, struct _ex_intern *e)
{
    int c = r_count_times_terms(e);
    struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * c);

    r_add_times_terms(env, e, args, 1);

    return _ex_intern_appl_env(env,INTERN_RAT_PLUS,c,args);
}

static struct _ex_intern *remove_term_var(struct env *env, unsigned var, struct _ex_intern *e)
{
    int i;

    if (e->type==EXP_VAR) return _ex_intern_small_integer(1);
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NAT_TIMES) {
        for (i = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type==EXP_VAR && e->u.appl.args[i]->u.var==var) {
                struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
                int j, k;
                k = 0;
                for (j = 0; j < e->u.appl.count; ++j) {
                    if (i != j) {
                        args[k++] = e->u.appl.args[j];
                    }
                }
                return _ex_intern_appl_env(env,INTERN_NAT_TIMES,e->u.appl.count-1,args);
            }
        }
    }
    fprintf(stderr, "Illegal times term %s\n", _th_print_exp(e));
    exit(1);
}

static struct _ex_intern *r_remove_term_var(struct env *env, struct _ex_intern *var, struct _ex_intern *e)
{
    int i;

    if (e==var) return _ex_intern_small_rational(1,1);
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_TIMES) {
        for (i = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]==var) {
                struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
                int j, k;
                k = 0;
                for (j = 0; j < e->u.appl.count; ++j) {
                    if (i != j) {
                        args[k++] = e->u.appl.args[j];
                    }
                }
                return _ex_intern_appl_env(env,INTERN_RAT_TIMES,e->u.appl.count-1,args);
            }
        }
    }
    fprintf(stderr, "Illegal times term %s\n", _th_print_exp(e));
    exit(1);
}

struct _ex_intern *_th_nat_equal_linear_solve(struct env *env, unsigned var, struct _ex_intern *e)
{
    int terms;
    struct _ex_intern *left, *right, *mod;
    struct _ex_intern **numerator, **denominator;
    int nc, dc;
    int i;

    if (!_th_is_free_in(e,var)) return NULL;

    if (!valid_plus_term(env,e->u.appl.args[0],var)) return NULL;
    if (!valid_plus_term(env,e->u.appl.args[1],var)) return NULL;

    left = normalize_to_plus(env, e->u.appl.args[0]);
    right = normalize_to_plus(env, e->u.appl.args[1]);

    _zone_print0("_th_nat_equal_linear_solve");
    _zone_print_exp("left =", left);
    _zone_print_exp("right =", right);

    terms = left->u.appl.count + right->u.appl.count;

    numerator = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * terms);
    denominator = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * terms);

    nc = dc = 0;

    for (i = 0; i < left->u.appl.count; ++i) {
        if (_th_is_free_in(left->u.appl.args[i],var)) {
            denominator[dc++] = remove_term_var(env,var,left->u.appl.args[i]);
        } else {
            numerator[nc++] = _ex_intern_appl2_env(env,INTERN_NAT_TIMES,_ex_intern_small_integer(-1),left->u.appl.args[i]);
        }
    }
    for (i = 0; i < right->u.appl.count; ++i) {
        if (_th_is_free_in(right->u.appl.args[i],var)) {
            denominator[dc++] = _ex_intern_appl2_env(env,INTERN_NAT_TIMES,_ex_intern_small_integer(-1),remove_term_var(env,var,right->u.appl.args[i]));
        } else {
            numerator[nc++] = right->u.appl.args[i];
        }
    }

    left = _ex_intern_appl_env(env,INTERN_NAT_PLUS,nc,numerator);
    right = _ex_intern_appl_env(env,INTERN_NAT_PLUS,dc,denominator);

    _zone_print_exp("left =", left);
    _zone_print_exp("right =", right);

    //printf("left = %s\n", _th_print_exp(left));
    //printf("right = %s\n", _th_print_exp(right));

    mod = _th_int_rewrite(env,
               _ex_intern_appl1_env(env,INTERN_NOT,
                   _ex_intern_appl2_env(env,INTERN_EQUAL,right,_ex_intern_small_integer(0))), 1);

    _zone_print_exp("mod =", mod);

    if (mod != _ex_true) return NULL;

    mod = _th_int_rewrite(env,
               _ex_intern_appl2_env(env,INTERN_EQUAL,
                   _ex_intern_small_integer(0),
                   _ex_intern_appl2_env(env,INTERN_NAT_MOD,left,right)), 1);

    _zone_print_exp("mod2 =", mod);

    if (mod == _ex_false) return _ex_false;
    if (mod != _ex_true) return NULL;

    return _ex_intern_appl2_env(env,INTERN_EQUAL,
                _ex_intern_var(var),
                _ex_intern_appl2_env(env,INTERN_NAT_DIVIDE,left,right));
}

struct _ex_intern *_th_rat_equal_linear_solve(struct env *env, struct _ex_intern *var, struct _ex_intern *e)
{
    int terms;
    struct _ex_intern *left, *right, *mod;
    struct _ex_intern **numerator, **denominator;
    int nc, dc;
    int i;

    //if (!_th_is_free_in(e,var)) return NULL;

    if (!r_valid_plus_term(env,e->u.appl.args[0],var)) return NULL;
    if (!r_valid_plus_term(env,e->u.appl.args[1],var)) return NULL;

    left = r_normalize_to_plus(env, e->u.appl.args[0]);
    right = r_normalize_to_plus(env, e->u.appl.args[1]);

    _zone_print0("_th_rat_equal_linear_solve");
    _zone_print_exp("left =", left);
    _zone_print_exp("right =", right);

    terms = left->u.appl.count + right->u.appl.count;

    numerator = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * terms);
    denominator = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * terms);

    nc = dc = 0;

    for (i = 0; i < left->u.appl.count; ++i) {
        if (contains_variable_term(left->u.appl.args[i],var)) {
            denominator[dc++] = r_remove_term_var(env,var,left->u.appl.args[i]);
        } else {
            numerator[nc++] = _ex_intern_appl2_env(env,INTERN_RAT_TIMES,_ex_intern_small_rational(-1,1),left->u.appl.args[i]);
        }
    }
    for (i = 0; i < right->u.appl.count; ++i) {
        if (contains_variable_term(right->u.appl.args[i],var)) {
            denominator[dc++] = _ex_intern_appl2_env(env,INTERN_RAT_TIMES,_ex_intern_small_rational(-1,1),r_remove_term_var(env,var,right->u.appl.args[i]));
        } else {
            numerator[nc++] = right->u.appl.args[i];
        }
    }

    if (_th_is_integer_logic() && (dc > 1 || denominator[0] != _ex_intern_small_rational(1,1))) return NULL;

    left = _ex_intern_appl_env(env,INTERN_RAT_PLUS,nc,numerator);
    right = _ex_intern_appl_env(env,INTERN_RAT_PLUS,dc,denominator);

    _zone_print_exp("left =", left);
    _zone_print_exp("right =", right);

    //printf("left = %s\n", _th_print_exp(left));
    //printf("right = %s\n", _th_print_exp(right));

    mod = _th_int_rewrite(env,
               _ex_intern_appl1_env(env,INTERN_NOT,
                   _ex_intern_equal(env,_ex_real,right,_ex_intern_small_rational(0,1))), 1);

    _zone_print_exp("mod =", mod);

    if (mod != _ex_true) return NULL;

    mod = _ex_intern_equal(env,_ex_real,
                var,
                _ex_intern_appl2_env(env,INTERN_RAT_DIVIDE,left,right));

    return mod;
}

struct _ex_intern *_th_linear_solve(struct env *env, unsigned var, struct _ex_intern *e)
{
    int terms;
    struct _ex_intern *left, *right;
    struct _ex_intern **numerator, **denominator;
    int nc, dc;
    int i;
    int have_not = 0;

    if (!_th_is_free_in(e,var)) return NULL;

	if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
		have_not = 1;
		e = e->u.appl.args[0];
	}
    if (e->u.appl.functor != INTERN_EQUAL && e->u.appl.functor != INTERN_NAT_LESS &&
		e->u.appl.functor != INTERN_ORIENTED_RULE) return NULL;

    if (!valid_plus_term(env,e->u.appl.args[0],var)) return NULL;
    if (!valid_plus_term(env,e->u.appl.args[1],var)) return NULL;

    left = normalize_to_plus(env, e->u.appl.args[0]);
    right = normalize_to_plus(env, e->u.appl.args[1]);

    _zone_print2("_th_linear_solve %s %s", _th_intern_decode(var), _th_print_exp(e));
	_tree_indent();
    _zone_print_exp("left =", left);
    _zone_print_exp("right =", right);

    terms = left->u.appl.count + right->u.appl.count;

    numerator = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * terms);
    denominator = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * terms);

    nc = dc = 0;

    for (i = 0; i < left->u.appl.count; ++i) {
        if (_th_is_free_in(left->u.appl.args[i],var)) {
            denominator[dc++] = remove_term_var(env,var,left->u.appl.args[i]);
        } else {
            numerator[nc++] = _ex_intern_appl2_env(env,INTERN_NAT_TIMES,_ex_intern_small_integer(-1),left->u.appl.args[i]);
        }
    }
    for (i = 0; i < right->u.appl.count; ++i) {
        if (_th_is_free_in(right->u.appl.args[i],var)) {
            denominator[dc++] = _ex_intern_appl2_env(env,INTERN_NAT_TIMES,_ex_intern_small_integer(-1),remove_term_var(env,var,right->u.appl.args[i]));
        } else {
            numerator[nc++] = right->u.appl.args[i];
        }
    }

    left = _ex_intern_appl_env(env,INTERN_NAT_PLUS,nc,numerator);
    right = _ex_intern_appl_env(env,INTERN_NAT_PLUS,dc,denominator);

    _zone_print_exp("left =", left);
    _zone_print_exp("right =", right);

    //printf("left = %s\n", _th_print_exp(left));
    //printf("right = %s\n", _th_print_exp(right));

	if (e->u.appl.functor==INTERN_EQUAL) {
        e = _ex_intern_appl2_env(env,INTERN_EQUAL,
                _ex_intern_var(var),
                _ex_intern_appl2_env(env,INTERN_NAT_DIVIDE,left,right));
		if (have_not) e = _ex_intern_appl1_env(env,INTERN_NOT,e);
	} else {
		if (have_not) {
			e = _ex_intern_appl2_env(env,INTERN_AND,
				    _ex_intern_appl2_env(env,INTERN_OR,
					    _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),right)),
						_ex_intern_appl1_env(env,INTERN_NOT,
						    _ex_intern_appl2_env(env,INTERN_NAT_LESS,
						        _ex_intern_var(var),
							    _ex_intern_appl2_env(env,INTERN_NAT_DIVIDE,left,right)))),
				    _ex_intern_appl2_env(env,INTERN_OR,
					    _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_NAT_LESS,right,_ex_intern_small_integer(0))),
						_ex_intern_appl1_env(env,INTERN_NOT,
						    _ex_intern_appl2_env(env,INTERN_NAT_LESS,
							    _ex_intern_appl2_env(env,INTERN_NAT_DIVIDE,left,right),
						        _ex_intern_var(var)))));
		} else {
			e = _ex_intern_appl2_env(env,INTERN_AND,
				    _ex_intern_appl2_env(env,INTERN_OR,
					    _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),right)),
						_ex_intern_appl2_env(env,INTERN_NAT_LESS,
						    _ex_intern_var(var),
							_ex_intern_appl2_env(env,INTERN_NAT_DIVIDE,left,right))),
				    _ex_intern_appl2_env(env,INTERN_OR,
					    _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_NAT_LESS,right,_ex_intern_small_integer(0))),
						_ex_intern_appl2_env(env,INTERN_NAT_LESS,
							_ex_intern_appl2_env(env,INTERN_NAT_DIVIDE,left,right),
						    _ex_intern_var(var))));
		}
	}
	_tree_undent();
	return e;
}

int _th_r_can_solve_for(struct env *env, struct _ex_intern *e, int var)
{
    int i;
    struct _ex_intern *core;

    int lf = _th_is_free_in(e->u.appl.args[0],var);
    int rf = _th_is_free_in(e->u.appl.args[1],var);

    if (lf && rf) return 0;

    if (lf) {
        e = e->u.appl.args[0];
    } else if (rf) {
        e = e->u.appl.args[1];
    } else {
        return 0;
    }

    if (e->type==EXP_VAR) return 1;

    if (e->type==EXP_APPL) {
        switch (e->u.appl.functor) {
            case INTERN_RAT_TIMES:
                e = _th_r_get_core(env,e);
                return e->type==EXP_VAR;
            case INTERN_RAT_PLUS:
                for (i = 0; i < e->u.appl.count; ++i) {
                    if (_th_is_free_in(e->u.appl.args[i],var)) {
                        core = _th_r_get_core(env,e->u.appl.args[i]);
                        if (core->type != EXP_VAR) return 0;
                    }
                }
                return 1;
        }
    } else {
        return 0;
    }
    return 0;
}

struct _ex_intern *_th_r_linear_solve(struct env *env, struct _ex_intern *var, struct _ex_intern *e)
{
    int terms;
    struct _ex_intern *left, *right;
    struct _ex_intern **numerator, **denominator;
    int nc, dc;
    int i;
    int have_not = 0;

    //if (!_th_is_free_in(e,var)) return NULL;

	if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
		have_not = 1;
		e = e->u.appl.args[0];
	}
    if (e->u.appl.functor != INTERN_EQUAL && e->u.appl.functor != INTERN_RAT_LESS &&
		e->u.appl.functor != INTERN_ORIENTED_RULE) return NULL;

    if (!r_valid_plus_term(env,e->u.appl.args[0],var)) return NULL;
    if (!r_valid_plus_term(env,e->u.appl.args[1],var)) return NULL;

    left = r_normalize_to_plus(env, e->u.appl.args[0]);
    right = r_normalize_to_plus(env, e->u.appl.args[1]);

    _zone_print_exp("_th_r_linear_solve", e);
	_tree_indent();
    _zone_print_exp("var", var);
    _zone_print_exp("left =", left);
    _zone_print_exp("right =", right);

    terms = left->u.appl.count + right->u.appl.count;

    numerator = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * terms);
    denominator = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * terms);

    nc = dc = 0;

    for (i = 0; i < left->u.appl.count; ++i) {
        if (contains_variable_term(left->u.appl.args[i],var)) {
            denominator[dc++] = r_remove_term_var(env,var,left->u.appl.args[i]);
        } else {
            numerator[nc++] = _ex_intern_appl2_env(env,INTERN_RAT_TIMES,_ex_intern_small_rational(-1,1),left->u.appl.args[i]);
        }
    }
    for (i = 0; i < right->u.appl.count; ++i) {
        if (contains_variable_term(right->u.appl.args[i],var)) {
            denominator[dc++] = _ex_intern_appl2_env(env,INTERN_RAT_TIMES,_ex_intern_small_rational(-1,1),r_remove_term_var(env,var,right->u.appl.args[i]));
        } else {
            numerator[nc++] = right->u.appl.args[i];
        }
    }

    left = _ex_intern_appl_env(env,INTERN_RAT_PLUS,nc,numerator);
    right = _ex_intern_appl_env(env,INTERN_RAT_PLUS,dc,denominator);

    _zone_print_exp("left =", left);
    _zone_print_exp("right =", right);

    //printf("left = %s\n", _th_print_exp(left));
    //printf("right = %s\n", _th_print_exp(right));

	if (e->u.appl.functor==INTERN_EQUAL) {
        e = _ex_intern_appl2_env(env,INTERN_EQUAL,
                var,
                _ex_intern_appl2_env(env,INTERN_RAT_DIVIDE,left,right));
		if (have_not) e = _ex_intern_appl1_env(env,INTERN_NOT,e);
	} else {
		if (have_not) {
			e = _ex_intern_appl2_env(env,INTERN_AND,
				    _ex_intern_appl2_env(env,INTERN_OR,
					    _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_RAT_LESS,_ex_intern_small_rational(0,1),right)),
						_ex_intern_appl1_env(env,INTERN_NOT,
						    _ex_intern_appl2_env(env,INTERN_RAT_LESS,
						        var,
							    _ex_intern_appl2_env(env,INTERN_RAT_DIVIDE,left,right)))),
				    _ex_intern_appl2_env(env,INTERN_OR,
					    _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_RAT_LESS,right,_ex_intern_small_rational(0,1))),
						_ex_intern_appl1_env(env,INTERN_NOT,
						    _ex_intern_appl2_env(env,INTERN_RAT_LESS,
							    _ex_intern_appl2_env(env,INTERN_RAT_DIVIDE,left,right),
						        var))));
		} else {
			e = _ex_intern_appl2_env(env,INTERN_AND,
				    _ex_intern_appl2_env(env,INTERN_OR,
					    _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_RAT_LESS,_ex_intern_small_rational(0,1),right)),
						_ex_intern_appl2_env(env,INTERN_RAT_LESS,
						    var,
							_ex_intern_appl2_env(env,INTERN_RAT_DIVIDE,left,right))),
				    _ex_intern_appl2_env(env,INTERN_OR,
					    _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_RAT_LESS,right,_ex_intern_small_rational(0,1))),
						_ex_intern_appl2_env(env,INTERN_NAT_LESS,
							_ex_intern_appl2_env(env,INTERN_RAT_DIVIDE,left,right),
						    var)));
		}
	}
	_tree_undent();
	return e;
}

static int is_inverse(struct _ex_intern *e1, struct _ex_intern *e2)
{
    if (e1->type==EXP_APPL && e1->u.appl.functor==INTERN_NOT &&
        e1->u.appl.args[0]==e2) return 1;
    if (e2->type==EXP_APPL && e2->u.appl.functor==INTERN_NOT &&
        e2->u.appl.args[0]==e1) return 1;

    return 0;
}

struct _ex_intern *_th_nat_less_linear_solve(struct env *env, unsigned var, struct _ex_intern *e)
{
    int terms;
    struct _ex_intern *left, *right, *cond[4], *res[4];
    struct _ex_intern **numerator, **denominator;
    int nc, dc;
    int i;

    if (!_th_is_free_in(e,var)) return NULL;

    if (!valid_plus_term(env,e->u.appl.args[0],var)) return NULL;
    if (!valid_plus_term(env,e->u.appl.args[1],var)) return NULL;

    left = normalize_to_plus(env, e->u.appl.args[0]);
    right = normalize_to_plus(env, e->u.appl.args[1]);

    terms = left->u.appl.count + right->u.appl.count;

    numerator = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * terms);
    denominator = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * terms);

    nc = dc = 0;

    _zone_print_exp("left =", left);
    _zone_print_exp("right =", right);

    for (i = 0; i < left->u.appl.count; ++i) {
        if (_th_is_free_in(left->u.appl.args[i],var)) {
            denominator[dc++] = remove_term_var(env,var,left->u.appl.args[i]);
        } else {
            numerator[nc++] = _ex_intern_appl2_env(env,INTERN_NAT_TIMES,_ex_intern_small_integer(-1),left->u.appl.args[i]);
        }
    }
    for (i = 0; i < right->u.appl.count; ++i) {
        if (_th_is_free_in(right->u.appl.args[i],var)) {
            denominator[dc++] = _ex_intern_appl2_env(env,INTERN_NAT_TIMES,_ex_intern_small_integer(-1),remove_term_var(env,var,right->u.appl.args[i]));
        } else {
            numerator[nc++] = right->u.appl.args[i];
        }
    }

    left = _ex_intern_appl_env(env,INTERN_NAT_PLUS,nc,numerator);
    right = _ex_intern_appl_env(env,INTERN_NAT_PLUS,dc,denominator);

    _zone_print_exp("left 2 =", left);
    _zone_print_exp("right 2 =", right);

    //printf("left = %s\n", _th_print_exp(left));
    //printf("right = %s\n", _th_print_exp(right));

    if (!(_th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_EQUAL,right,_ex_intern_small_integer(0)),1)==_ex_false)) {
        return NULL;
    }

    right = _th_int_rewrite(env,right,1);
    left = _th_int_rewrite(env,left,1);
    if (_th_equal(env,right,_ex_intern_small_integer(1))) {
        return _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_var(var),left);
    }
    if (_th_equal(env,right,_ex_intern_small_integer(-1))) {
        return _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_appl2_env(env,INTERN_NAT_TIMES,left,_ex_intern_small_integer(-1)),_ex_intern_var(var));
    }
    cond[0] = _th_int_rewrite(env,
                   _ex_intern_appl2_env(env,INTERN_OR,
                       _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),left)),
                       _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),right))), 1);
    res[0] = _th_int_rewrite(env,
                 _ex_intern_appl2_env(env,INTERN_NAT_LESS,
                     _ex_intern_var(var),
                     _ex_intern_appl2_env(env,INTERN_NAT_DIVIDE,
                         _th_flatten_top(env,_ex_intern_appl3_env(env,INTERN_NAT_PLUS,left,right,_ex_intern_small_integer(-1))),
                         right)), 1);
    cond[1] = _th_int_rewrite(env,
                  _ex_intern_appl2_env(env,INTERN_OR,
                      _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),left),
                      _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),right))), 1);
    res[1] = _th_int_rewrite(env,
                 _ex_intern_appl2_env(env,INTERN_NAT_LESS,
                     _ex_intern_var(var),
                     _ex_intern_appl2_env(env,INTERN_NAT_DIVIDE,
                         left,
                         right)), 1);
    cond[2] = _th_int_rewrite(env,
                  _ex_intern_appl2_env(env,INTERN_OR,
                      _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),left)),
                      _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),right)), 1);
    res[2] = _th_int_rewrite(env,
                 _ex_intern_appl2_env(env,INTERN_NAT_LESS,
                     _ex_intern_appl2_env(env,INTERN_NAT_DIVIDE,
                         _th_flatten_top(env,_ex_intern_appl3_env(env,INTERN_NAT_PLUS,left,_ex_intern_appl2_env(env,INTERN_NAT_TIMES,right,_ex_intern_small_integer(-1)),_ex_intern_small_integer(-1))),
                         right),
                     _ex_intern_var(var)), 1);
    cond[3] = _th_int_rewrite(env,
                  _ex_intern_appl2_env(env,INTERN_OR,
                      _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),left),
                      _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),right)), 1);
    res[3] = _th_int_rewrite(env,
                 _ex_intern_appl2_env(env,INTERN_NAT_LESS,
                     _ex_intern_appl2_env(env,INTERN_NAT_DIVIDE,
                         left,
                         right),
                     _ex_intern_var(var)), 1);


    if (cond[0]==_ex_false) return res[0];
    if (cond[1]==_ex_false) return res[1];
    if (cond[2]==_ex_false) return res[2];
    if (cond[3]==_ex_false) return res[3];

    if (res[0]==res[1] && is_inverse(cond[0],cond[1])) return res[0];
    if (res[0]==res[2] && is_inverse(cond[0],cond[2])) return res[0];
    if (res[1]==res[3] && is_inverse(cond[1],cond[3])) return res[1];
    if (res[2]==res[3] && is_inverse(cond[2],cond[3])) return res[2];

    return NULL;
}

struct _ex_intern *_th_solve_for_a_var(struct env *env, struct _ex_intern *e)
{
    unsigned *fv;
    int c, i;
    unsigned var = 0;
    struct _ex_intern *r;
    struct _ex_intern *args[3];

    if (_th_cond_level() > 0) return NULL;
    if (_th_has_complex_term(e,7)) return NULL;

    fv = _th_get_free_vars(e, &c);

    for (i = 0; i < c; ++i) {
        if (valid_plus_term(env,e->u.appl.args[0],fv[i]) &&
            valid_plus_term(env,e->u.appl.args[1],fv[i])) {
            if (var) return NULL;
            var = fv[i];
        }
    }
	
	if (!var) return NULL;

    r = _ex_intern_var(var);
    if (r==e->u.appl.args[0] || r==e->u.appl.args[1]) return NULL;

    if (e->u.appl.functor==INTERN_NAT_LESS) {
        _th_increment_cond_level();
        r = _th_nat_less_linear_solve(env,var,e);
        _zone_print_exp("r =", r);
        _th_decrement_cond_level();
        if (r==_ex_true || r==_ex_false) return r;
        if (r==NULL) return NULL;
        if (r->type != EXP_APPL || r->u.appl.functor != INTERN_NAT_LESS || r->u.appl.count != 2) return NULL;
        args[0] = _th_int_rewrite(env,r->u.appl.args[0],1);
        args[1] = _th_int_rewrite(env,r->u.appl.args[1],1);
        r = _ex_intern_appl2_env(env,e->u.appl.functor,args[0],args[1]);
        if (e != r) return r;
    }

    if (e->u.appl.functor==INTERN_EQUAL || e->u.appl.functor==INTERN_ORIENTED_RULE) {
        _th_increment_cond_level();
        r = _th_nat_equal_linear_solve(env,var,e);
        _zone_print_exp("r =", r);
        _th_decrement_cond_level();
        if (r==NULL) return NULL;
        if (r==_ex_true || r==_ex_false) return r;
        if (r->type != EXP_APPL || r->u.appl.count < 2 || (r->u.appl.functor != INTERN_EQUAL && r->u.appl.functor != INTERN_ORIENTED_RULE)) return NULL;
        args[0] = _th_int_rewrite(env,r->u.appl.args[0],1);
        args[1] = _th_int_rewrite(env,r->u.appl.args[1],1);
        if (e->u.appl.count > 2) args[2] = _th_int_rewrite(env,e->u.appl.args[2],1);
        r = _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
        if (e != r) return r;
    }

    return NULL;
}

struct env *cenv;

int term_cmp(struct _ex_intern **t1, struct _ex_intern **t2)
{
    return _th_term_compare(cenv, *t1, *t2);
}

struct _ex_intern *_th_r_solve_for_a_var(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern **fv;
    int c, i;
    //unsigned var = 0;
    struct _ex_intern *r;
    struct _ex_intern *args[3];
    struct add_list *terms, *t;

    _zone_print0("_th_r_solve_for_a_var");

    //if ((e->u.appl.args[0]->type==EXP_VAR && !_th_is_slack(e->u.appl.args[0])) ||
    //     (e->u.appl.args[1]->type==EXP_VAR && !_th_is_slack(e->u.appl.args[1]))) return NULL;
    if (_th_cond_level() > 0) return NULL;
    if (_th_has_complex_term(e,10)) return NULL;

    _tree_indent();

    terms = _th_basic_terms(e,NULL);
    c = 0;
    t = terms;
    while (t) {
        _zone_print_exp("var ", t->e);
        ++c;
        t = t->next;
    }

    fv = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * c);

    i = 0;
    while (terms) {
        fv[i++] = terms->e;
        terms = terms->next;
    }
    cenv = env;
    qsort(fv,c,sizeof(struct _ex_intern *),term_cmp);

    for (i = 0; i < c; ++i) {
        _zone_print_exp("Testing", fv[i]);
        _tree_indent();
        if (r_valid_plus_term(env,e->u.appl.args[0],fv[i]) &&
            r_valid_plus_term(env,e->u.appl.args[1],fv[i])) {
            if (fv[i]==e->u.appl.args[0] || fv[i]==e->u.appl.args[1]) {
                _zone_print0("Already solved");
                _tree_undent();
                _tree_undent();
                return NULL;
            }
            _tree_indent();
            _zone_print0("Can solve");
            //var = fv[i]->u.var;
            if (e->u.appl.functor==INTERN_EQUAL || e->u.appl.functor==INTERN_ORIENTED_RULE) {
                _th_increment_cond_level();
                r = _th_rat_equal_linear_solve(env,fv[i],e);
                _zone_print_exp("r =", r);
                _th_decrement_cond_level();
                if (r!=NULL) {
                    if (r==_ex_true || r==_ex_false) {
                        _tree_undent();
                        _tree_undent();
                        _tree_undent();
                        return r;
                    }
                    if (r->type != EXP_APPL || r->u.appl.count < 2 || (r->u.appl.functor != INTERN_EQUAL && r->u.appl.functor != INTERN_ORIENTED_RULE)) {
                        _tree_undent();
                        _tree_undent();
                        _tree_undent();
                        return NULL;
                    }
                    args[0] = _th_int_rewrite(env,r->u.appl.args[0],1);
                    args[1] = _th_int_rewrite(env,r->u.appl.args[1],1);
                    if (e->u.appl.count > 2) args[2] = _th_int_rewrite(env,e->u.appl.args[2],1);
                    r = _ex_intern_appl_equal_env(env,e->u.appl.functor,e->u.appl.count,args,e->type_inst);
                    if (e->u.appl.functor==INTERN_EQUAL && r->type_inst==NULL) r->type_inst = _ex_real;
                    _zone_print_exp("result", r);
                    _tree_undent();
                    _tree_undent();
                    _tree_undent();
                    if (e != r) return r;
                    return NULL;
                }
            }
            _tree_undent();
        }
        _tree_undent();
    }

    _tree_undent();
	return NULL;

    //r = _ex_intern_var(var);
    //if (r==e->u.appl.args[0] || r==e->u.appl.args[1]) return NULL;

    //if (e->u.appl.functor==INTERN_NAT_LESS) {
    //    _th_increment_cond_level();
    //    r = _th_nat_less_linear_solve(env,var,e);
    //    _zone_print_exp("r =", r);
    //    _th_decrement_cond_level();
    //    if (r==_ex_true || r==_ex_false) return r;
    //    if (r==NULL) return NULL;
    //    if (r->type != EXP_APPL || r->u.appl.functor != INTERN_NAT_LESS || r->u.appl.count != 2) return NULL;
    //    args[0] = _th_int_rewrite(env,r->u.appl.args[0],1);
    //    args[1] = _th_int_rewrite(env,r->u.appl.args[1],1);
    //    r = _ex_intern_appl2_env(env,e->u.appl.functor,args[0],args[1]);
    //    if (e != r) return r;
    //}

    //return NULL;
}

struct _ex_intern *_th_solve_term(struct env *env, int var_count, unsigned *vars, struct _ex_intern *term)
{
    int i;
    unsigned var = -1;
    struct _ex_intern *res;
    char *mark;

    //printf("Solving term %s\n", _th_print_exp(term));
    for (i = 0; i < var_count; ++i) {
        if (_th_is_free_in(term,vars[i])) {
            if (var==-1) {
                var = vars[i];
            } else {
                return NULL;
            }
        }
    }
    if (var==-1) return NULL;

    mark = _th_alloc_mark(REWRITE_SPACE) ;
    _th_push_context() ;
    for (i = 0; i < var_count; ++i) {
        _th_intern_push_quant(REWRITE_SPACE,vars[i],_th_quant_level) ;
        _th_quant_add_context_rule(vars[i],_th_quant_level) ;
    }

    res = _th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_SOLVE_FOR,_ex_intern_var(var),_ex_intern_appl1_env(env,INTERN_NORMAL,term)), 1);

    for (i = 0; i < var_count; ++i) {
        _th_intern_pop_quant(vars[i]) ;
    }
    --_th_quant_level ;
    _th_pop_context() ;
    _th_alloc_release(REWRITE_SPACE,mark) ;
    
    //printf("res = %s\n", _th_print_exp(res));
    //fflush(stdout);
    if (res->type==EXP_APPL && res->u.appl.functor==INTERN_SOLVE_FOR) return NULL;
    if (res==term) return NULL;
    return res;
}

struct _ex_intern *_th_simplify_equation(struct env *env, struct _ex_intern *exp)
{
	struct _ex_intern *l, *r;
    int i, j, k, m, n;
    struct _ex_intern **args, **args2;

	l = exp->u.appl.args[0];
	r = exp->u.appl.args[1];

    //printf("Simplify equation l %s\n", _th_print_exp(l));
    //printf("Simplify equation r %s\n", _th_print_exp(r));
    if (l->type==EXP_APPL && l->u.appl.functor==INTERN_NAT_PLUS) {
		for (i = 0; i < l->u.appl.count; ++i) {
			if (l->u.appl.args[i]->type==EXP_INTEGER) {
                //printf("Here1 %d\n", i);
				if (r->type==EXP_INTEGER) {
					args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * l->u.appl.count);
                    for (j = 0, k = 0; j < l->u.appl.count; ++j) {
						if (i != j) args[k++] = l->u.appl.args[j];
					}
					if (exp->u.appl.count==2) {
					    return _ex_intern_appl2_env(env,exp->u.appl.functor,
						           _ex_intern_appl_env(env,INTERN_NAT_PLUS,k,args),
							       _ex_intern_integer(_th_big_sub(r->u.integer,l->u.appl.args[i]->u.integer)));
					} else {
					    return _ex_intern_appl3_env(env,exp->u.appl.functor,
						           _ex_intern_appl_env(env,INTERN_NAT_PLUS,k,args),
							       _ex_intern_integer(_th_big_sub(r->u.integer,l->u.appl.args[i]->u.integer)),
								   exp->u.appl.args[2]);
					}
				} else if (r->type==EXP_APPL && r->u.appl.functor==INTERN_NAT_PLUS) {
					for (j = 0; j < r->u.appl.count; ++j) {
						if (r->u.appl.args[j]->type==EXP_INTEGER) {
        					args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * l->u.appl.count);
        					args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * r->u.appl.count);
							for (m = 0, k = 0; k < l->u.appl.count; ++k) {
								if (i != k) {
								   args[m++] = l->u.appl.args[k];
								}
							}
							for (n = 0, k = 0; k < r->u.appl.count; ++k) {
								if (j != k) {
								   args2[n++] = r->u.appl.args[k];
								}
							}
							if (_th_big_less(l->u.appl.args[i]->u.integer,r->u.appl.args[j]->u.integer)) {
								args2[n++] = _ex_intern_integer(_th_big_sub(r->u.appl.args[j]->u.integer,l->u.appl.args[i]->u.integer));
							} else {
								args[m++] = _ex_intern_integer(_th_big_sub(l->u.appl.args[i]->u.integer,r->u.appl.args[j]->u.integer));
							}
							if (exp->u.appl.count==2) {
								return _ex_intern_appl2_env(env,exp->u.appl.functor,
									       _ex_intern_appl_env(env,INTERN_NAT_PLUS,m,args),
										   _ex_intern_appl_env(env,INTERN_NAT_PLUS,n,args2));
							} else {
								return _ex_intern_appl3_env(env,exp->u.appl.functor,
									       _ex_intern_appl_env(env,INTERN_NAT_PLUS,m,args),
										   _ex_intern_appl_env(env,INTERN_NAT_PLUS,n,args2),
										   exp->u.appl.args[2]);
							}
						}
						if (_th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_EQUAL,l->u.appl.args[i],r->u.appl.args[j]),1)==_ex_true) {
        					args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * l->u.appl.count);
        					args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * l->u.appl.count);
							for (m = 0, k = 0; k < l->u.appl.count; ++k) {
								if (i != k) {
								   args[m++] = l->u.appl.args[k];
								}
							}
							for (n = 0, k = 0; k < r->u.appl.count; ++k) {
								if (j != k) {
								   args2[n++] = r->u.appl.args[k];
								}
							}
							if (exp->u.appl.count==2) {
								return _ex_intern_appl2_env(env,exp->u.appl.functor,
									       _ex_intern_appl_env(env,INTERN_NAT_PLUS,m,args),
										   _ex_intern_appl_env(env,INTERN_NAT_PLUS,n,args2));
							} else {
								return _ex_intern_appl3_env(env,exp->u.appl.functor,
									       _ex_intern_appl_env(env,INTERN_NAT_PLUS,m,args),
										   _ex_intern_appl_env(env,INTERN_NAT_PLUS,n,args2),
										   exp->u.appl.args[2]);
							}
						}
					}
				}
			}
		}
	} else if (l->type==EXP_INTEGER && r->type==EXP_APPL && r->u.appl.functor==INTERN_NAT_PLUS) {
		for (i = 0; i < r->u.appl.count; ++i) {
			if (r->u.appl.args[i]->type==EXP_INTEGER) break;
		}
		if (i < r->u.appl.count) {
			args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * r->u.appl.count);
			for (j = 0, k = 0; j < r->u.appl.count; ++j) {
				if (i != j) args[k++] = r->u.appl.args[j];
			}
			if (exp->u.appl.count==2) {
				return _ex_intern_appl2_env(env,exp->u.appl.functor,
					_ex_intern_integer(_th_big_sub(l->u.integer,r->u.appl.args[i]->u.integer)),
					_ex_intern_appl_env(env,INTERN_NAT_PLUS,k,args));
			} else {
				return _ex_intern_appl3_env(env,exp->u.appl.functor,
					_ex_intern_integer(_th_big_sub(l->u.integer,r->u.appl.args[i]->u.integer)),
					_ex_intern_appl_env(env,INTERN_NAT_PLUS,k,args),
					exp->u.appl.args[2]);
			}
		}
	}

	return NULL;
}

struct _ex_intern *_th_r_simplify_equation(struct env *env, struct _ex_intern *exp)
{
	struct _ex_intern *l, *r;
    int i, j, k, m, n;
    struct _ex_intern **args, **args2;

	l = exp->u.appl.args[0];
	r = exp->u.appl.args[1];

    //printf("Simplify equation l %s\n", _th_print_exp(l));
    //printf("Simplify equation r %s\n", _th_print_exp(r));
    if (l->type==EXP_APPL && l->u.appl.functor==INTERN_RAT_PLUS) {
		for (i = 0; i < l->u.appl.count; ++i) {
			if (l->u.appl.args[i]->type==EXP_RATIONAL) {
                //printf("Here1 %d\n", i);
				if (r->type==EXP_RATIONAL) {
					args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * l->u.appl.count);
                    for (j = 0, k = 0; j < l->u.appl.count; ++j) {
						if (i != j) args[k++] = l->u.appl.args[j];
					}
					if (exp->u.appl.count==2) {
					    return _ex_intern_appl2_env(env,exp->u.appl.functor,
						           _ex_intern_appl_env(env,INTERN_RAT_PLUS,k,args),
                				   _th_subtract_rationals(r,l->u.appl.args[i]));
					} else {
					    return _ex_intern_appl3_env(env,exp->u.appl.functor,
						           _ex_intern_appl_env(env,INTERN_RAT_PLUS,k,args),
							       _th_subtract_rationals(r,l->u.appl.args[i]),
								   exp->u.appl.args[2]);
					}
				} else if (r->type==EXP_APPL && r->u.appl.functor==INTERN_RAT_PLUS) {
					for (j = 0; j < r->u.appl.count; ++j) {
						if (r->u.appl.args[j]->type==EXP_RATIONAL) {
        					args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * l->u.appl.count);
        					args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * r->u.appl.count);
							for (m = 0, k = 0; k < l->u.appl.count; ++k) {
								if (i != k) {
								   args[m++] = l->u.appl.args[k];
								}
							}
							for (n = 0, k = 0; k < r->u.appl.count; ++k) {
								if (j != k) {
								   args2[n++] = r->u.appl.args[k];
								}
							}
							if (_th_rational_less(l->u.appl.args[i],r->u.appl.args[j])) {
								args2[n++] = _th_subtract_rationals(r->u.appl.args[j],l->u.appl.args[i]);
							} else {
								args[m++] = _th_subtract_rationals(l->u.appl.args[i],r->u.appl.args[j]);
							}
							if (exp->u.appl.count==2) {
								return _ex_intern_appl2_equal_env(env,exp->u.appl.functor,
									       _ex_intern_appl_env(env,INTERN_RAT_PLUS,m,args),
										   _ex_intern_appl_env(env,INTERN_RAT_PLUS,n,args2),_ex_real);
							} else {
								return _ex_intern_appl3_env(env,exp->u.appl.functor,
									       _ex_intern_appl_env(env,INTERN_RAT_PLUS,m,args),
										   _ex_intern_appl_env(env,INTERN_RAT_PLUS,n,args2),
										   exp->u.appl.args[2]);
							}
						}
						if (_th_int_rewrite(env,_ex_intern_appl2_equal_env(env,INTERN_EQUAL,l->u.appl.args[i],r->u.appl.args[j],_ex_real),1)==_ex_true) {
        					args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * l->u.appl.count);
        					args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * l->u.appl.count);
							for (m = 0, k = 0; k < l->u.appl.count; ++k) {
								if (i != k) {
								   args[m++] = l->u.appl.args[k];
								}
							}
							for (n = 0, k = 0; k < r->u.appl.count; ++k) {
								if (j != k) {
								   args2[n++] = r->u.appl.args[k];
								}
							}
							if (exp->u.appl.count==2) {
								return _ex_intern_appl2_env(env,exp->u.appl.functor,
									       _ex_intern_appl_env(env,INTERN_RAT_PLUS,m,args),
										   _ex_intern_appl_env(env,INTERN_RAT_PLUS,n,args2));
							} else {
								return _ex_intern_appl3_env(env,exp->u.appl.functor,
									       _ex_intern_appl_env(env,INTERN_RAT_PLUS,m,args),
										   _ex_intern_appl_env(env,INTERN_RAT_PLUS,n,args2),
										   exp->u.appl.args[2]);
							}
						}
					}
				}
			}
		}
	} else if (l->type==EXP_RATIONAL && r->type==EXP_APPL && r->u.appl.functor==INTERN_RAT_PLUS) {
		for (i = 0; i < r->u.appl.count; ++i) {
			if (r->u.appl.args[i]->type==EXP_RATIONAL) break;
		}
		if (i < r->u.appl.count) {
			args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * r->u.appl.count);
			for (j = 0, k = 0; j < r->u.appl.count; ++j) {
				if (i != j) args[k++] = r->u.appl.args[j];
			}
			if (exp->u.appl.count==2) {
				return _ex_intern_appl2_env(env,exp->u.appl.functor,
        			_th_subtract_rationals(l,r->u.appl.args[i]),
					_ex_intern_appl_env(env,INTERN_RAT_PLUS,k,args));
			} else {
				return _ex_intern_appl3_env(env,exp->u.appl.functor,
        			_th_subtract_rationals(l,r->u.appl.args[i]),
					_ex_intern_appl_env(env,INTERN_RAT_PLUS,k,args),
					exp->u.appl.args[2]);
			}
		}
	}

	return NULL;
}

static struct _ex_intern *get_coef(struct env *env, struct _ex_intern *exp)
{
	if (exp->type==EXP_APPL && exp->u.appl.functor==INTERN_NAT_TIMES) {
		int i;
		for (i = 0; i < exp->u.appl.count; ++i) {
			if (exp->u.appl.args[i]->type==EXP_INTEGER) return exp->u.appl.args[i];
		}
	}
	return _ex_intern_small_integer(1);
}

static struct _ex_intern *strip_coef(struct env *env, struct _ex_intern *exp)
{
	if (exp->type==EXP_APPL && exp->u.appl.functor==INTERN_NAT_TIMES) {
		int i;
		for (i = 0; i < exp->u.appl.count; ++i) {
			if (exp->u.appl.args[i]->type==EXP_INTEGER) {
				int j, k;
				struct _ex_intern **args;
				args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count);
				for (j = 0, k = 0; j < exp->u.appl.count; ++j) {
					if (j != i) {
						args[k++] = exp->u.appl.args[j];
					}
				}
                if (k==1) {
                    return args[0];
                } else {
				    return _ex_intern_appl_env(env,INTERN_NAT_TIMES,k,args);
                }
			}
		}
	}
	return exp;
}

struct _ex_intern *_th_simplify_nat_minus(struct env *env, struct _ex_intern *exp)
{
    if (exp->u.appl.args[0]->type == EXP_INTEGER &&
        exp->u.appl.args[1]->type == EXP_INTEGER) {
        return _ex_intern_integer(_th_big_sub(exp->u.appl.args[0]->u.integer,exp->u.appl.args[1]->u.integer)) ;
    }
    return _ex_intern_appl2_env(env,INTERN_NAT_PLUS,exp->u.appl.args[0],_ex_intern_appl2_env(env,INTERN_NAT_TIMES,_ex_intern_small_integer(-1),exp->u.appl.args[1]));
}

struct _ex_intern *_th_simplify_nat_plus(struct env *env, struct _ex_intern *exp)
{
    struct _ex_intern **coef, **args;
    int i, j, count;
    unsigned *accumulate, zero[2] = { 1, 0 };
    
    if (exp->u.appl.count==1) return exp->u.appl.args[0] ;
    if (exp->u.appl.count==0) return _ex_intern_small_integer(0);
    accumulate = zero ;
    j = 0 ;
    for (i = 0; i < exp->u.appl.count; ++i) {
        if (exp->u.appl.args[i]->type==EXP_INTEGER) {
            ++j ;
            accumulate = _th_big_add(accumulate, exp->u.appl.args[i]->u.integer) ;
        }
    }
    if (j >= 2 || (j==1 && accumulate[0]==1 && accumulate[1]==0)) {
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count);
        for (i = 0, j = 0; i < exp->u.appl.count; ++i) {
            if (exp->u.appl.args[i]->type != EXP_INTEGER) {
                args[j++] = exp->u.appl.args[i] ;
            }
        }
        if (j==0) return _ex_intern_integer(accumulate) ;
        if (accumulate[0] != 1 || accumulate[1] != 0) {
            args[j++] = _ex_intern_integer(accumulate) ;
        }
        return _ex_intern_appl_env(env, INTERN_NAT_PLUS, j, args) ;
    }
    
    coef = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count);
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count);
    
    for (i = 0; i < exp->u.appl.count; ++i) {
        coef[i] = get_coef(env,exp->u.appl.args[i]);
        args[i] = strip_coef(env,exp->u.appl.args[i]);
    }
    
    count = exp->u.appl.count;
    for (i = 0; i < count; ++i) {
        for (j = i+1; j < count; ++j) {
            if (args[i]==args[j]) {
                coef[i] = _ex_intern_integer(_th_big_add(coef[i]->u.integer,coef[j]->u.integer));
                coef[j] = coef[--count];
                args[j] = args[count];
                --j;
            }
        }
    }
    
    if (count < exp->u.appl.count) {
        for (i = 0; i < count; ++i) {
            args[i] = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_NAT_TIMES,args[i],coef[i]));
        }
        return _ex_intern_appl_env(env,INTERN_NAT_PLUS,count,args);
    }
    
    return NULL;
}

struct _ex_intern *_th_simplify_nat_times(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern **args;
	int i, j;
    unsigned *accumulate, one[2] = { 1, 1 };

	if (e->u.appl.count==1) return e->u.appl.args[0] ;
	if (e->u.appl.count==0) return _ex_intern_small_integer(1);
	accumulate = one ;
	j = 0 ;
	for (i = 0; i < e->u.appl.count; ++i) {
		if (e->u.appl.args[i]->type==EXP_INTEGER) {
            struct _ex_intern *f = e->u.appl.args[i];
			++j ;
            if (f->u.integer[0]==1 && f->u.integer[1]==0) return f;
			accumulate = _th_big_copy(REWRITE_SPACE,_th_big_multiply(accumulate, f->u.integer)) ;
		}
	}
	if (j >= 2 || (j==1 && accumulate[0]==1 && accumulate[1]==1)) {
		//check_size(e->u.appl.count) ;
		args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
		for (i = 0, j = 0; i < e->u.appl.count; ++i) {
			if (e->u.appl.args[i]->type != EXP_INTEGER) {
				args[j++] = e->u.appl.args[i] ;
			}
		}
		if (j==0) return _ex_intern_integer(accumulate) ;
        if (accumulate[0] != 1 || accumulate[1] != 1) {
		    args[j++] = _ex_intern_integer(accumulate) ;
        }
		return _ex_intern_appl_env(env, INTERN_NAT_TIMES, j, args) ;
	}
	return NULL ;
}

struct _ex_intern *_th_simplify_nat_divide(struct env *env, struct _ex_intern *e)
{
    if (e->u.appl.args[1]->type == EXP_INTEGER) {
        struct _ex_intern *f;
        if (e->u.appl.args[0]->type == EXP_INTEGER &&
            (!_th_big_is_zero(e->u.appl.args[1]->u.integer))) {
            return _ex_intern_integer(_th_big_divide(e->u.appl.args[0]->u.integer,e->u.appl.args[1]->u.integer)) ;
        }
        f = e->u.appl.args[1];
        if (f->u.integer[0]==1 && f->u.integer[1]==1) return e->u.appl.args[0];
        if (f->u.integer[0]==1 && f->u.integer[1]==0xffffffff) return _ex_intern_appl2_env(env,INTERN_NAT_TIMES,e->u.appl.args[0],f);
    }
    return NULL ;            
}

struct _ex_intern *_th_simplify_nat_rat(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *f = e->u.appl.args[0];
    if (f->type==EXP_INTEGER) {
        return _ex_intern_rational(f->u.integer,_ex_one->u.integer);
    }
    if (f->type==EXP_APPL) {
        switch (f->u.appl.functor) {
            case INTERN_ITE:
                return _ex_intern_appl3_env(env,INTERN_ITE,f->u.appl.args[0],_ex_intern_appl1_env(env,INTERN_NAT_TO_RAT,f->u.appl.args[1]),_ex_intern_appl1_env(env,INTERN_NAT_TO_RAT,f->u.appl.args[2]));
        }
    }
    return NULL;
}

struct _ex_intern *_th_simplify_nat_less(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *f, **args;
	int i, l;
	if (e->u.appl.args[0]->type == EXP_INTEGER &&
		e->u.appl.args[1]->type == EXP_INTEGER) {
		if (_th_big_less(e->u.appl.args[0]->u.integer,e->u.appl.args[1]->u.integer)) {
			return _ex_true ;
		} else {
			return _ex_false ;
		}
	}
    f = _th_simplify_equation(env,e);
    if (f) return f;
    f = _th_collect_like_terms(env,e);
    if (f) return f;
	//f = _th_solve_for_a_var(env,e);
	//if (f) return f;
	if (e->u.appl.args[1]->type==EXP_APPL) {
		f = e->u.appl.args[1];
		switch (f->u.appl.functor) {
    		case INTERN_NAT_MAX:
				for (i = 0; i < f->u.appl.count; ++i) {
					if (_th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_LESS,e->u.appl.args[0],f->u.appl.args[i]), 1)==_ex_true) return _ex_true;
				}
				return NULL;
			case INTERN_NAT_MIN:
				//check_size(f->u.appl.count);
				args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * f->u.appl.count);
				l = 0;
				for (i = 0; i < f->u.appl.count; ++i) {
					if (_th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_LESS,e->u.appl.args[0],f->u.appl.args[i]), 1)!=_ex_true) {
						args[l++] = f->u.appl.args[i];
					}
				}
				if (l==0) return _ex_true;
				if (l==i) return NULL;
				return _ex_intern_appl2_env(env,INTERN_NAT_LESS,e->u.appl.args[0],_ex_intern_appl_env(env,INTERN_NAT_MIN,l,args));
		}
	}
	if (e->u.appl.args[0]->type==EXP_APPL) {
		f = e->u.appl.args[0];
		switch (f->u.appl.functor) {
    		case INTERN_NAT_MAX:
				//check_size(f->u.appl.count);
				args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * f->u.appl.count);
				l = 0;
				for (i = 0; i < f->u.appl.count; ++i) {
					if (_th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_LESS,f->u.appl.args[i],e->u.appl.args[1]), 1)!=_ex_true) {
						args[l++] = f->u.appl.args[i];
					}
				}
				if (l==0) return _ex_true;
				if (l==i) return NULL;
				return _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_appl_env(env,INTERN_NAT_MAX,l,args),e->u.appl.args[1]);
		    case INTERN_NAT_MIN:
				for (i = 0; i < f->u.appl.count; ++i) {
					if (_th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_LESS,f->u.appl.args[i],e->u.appl.args[1]), 1)==_ex_true) return _ex_true;
				}
		}
	}
    f = _th_simplify_nless_by_range(env,e);
    if (f) return f;
    f = _th_remove_times_neg_one(env,e);
    if (f) return f;
	f = _th_bit_blast_comparison(env,e);
    if (f) return f;
    f = _th_reverse_terms(env,e);
    if (_th_use_transitive) {
        if (f) return f;
        f = _th_search_less(env,e);
    }
	return f;
}

struct _ex_intern *_th_simplify_nat_min(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern **args;
	int i, j, l;

	if (e->u.appl.count==1) return e->u.appl.args[0];
	for (i = 0; i < e->u.appl.count; ++i) {
		for (j = 0; j < e->u.appl.count; ++j) {
			if (i !=j) {
				if (_th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_LESS,e->u.appl.args[i],e->u.appl.args[j]), 1)==_ex_true) {
					l = 0;
					args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
					for (i = 0; i < e->u.appl.count; ++i) {
						if (i != j) args[l++] = e->u.appl.args[i];
					}
					return _ex_intern_appl_env(env,INTERN_NAT_MIN,l,args);
				}
			}
		}
	}
	return NULL;
}

struct _ex_intern *_th_simplify_nat_max(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern **args;
	int i, j, l;

	if (e->u.appl.count==1) return e->u.appl.args[0];
	for (i = 0; i < e->u.appl.count; ++i) {
		for (j = 0; j < e->u.appl.count; ++j) {
			if (i !=j) {
				if (_th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_LESS,e->u.appl.args[j],e->u.appl.args[i]), 1)==_ex_true) {
					l = 0;
					args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
					for (i = 0; i < e->u.appl.count; ++i) {
						if (i != j) args[l++] = e->u.appl.args[i];
					}
					return _ex_intern_appl_env(env,INTERN_NAT_MIN,l,args);
				}
			}
		}
	}
	return NULL;
}

static struct _ex_intern *get_r_coef(struct env *env, struct _ex_intern *exp)
{
	if (exp->type==EXP_APPL && exp->u.appl.functor==INTERN_RAT_TIMES) {
		int i;
		for (i = 0; i < exp->u.appl.count; ++i) {
			if (exp->u.appl.args[i]->type==EXP_RATIONAL) return exp->u.appl.args[i];
		}
	}
	return _ex_intern_small_rational(1,1) ;
}

static struct _ex_intern *strip_r_coef(struct env *env, struct _ex_intern *exp)
{
	if (exp->type==EXP_APPL && exp->u.appl.functor==INTERN_RAT_TIMES) {
		int i;
		for (i = 0; i < exp->u.appl.count; ++i) {
			if (exp->u.appl.args[i]->type==EXP_RATIONAL) {
				int j, k;
				struct _ex_intern **args;
				args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count);
				for (j = 0, k = 0; j < exp->u.appl.count; ++j) {
					if (j != i) {
						args[k++] = exp->u.appl.args[j];
					}
				}
                if (k==1) {
                    return args[0];
                } else {
				    return _ex_intern_appl_env(env,INTERN_RAT_TIMES,k,args);
                }
			}
		}
	}
	return exp;
}

static struct _ex_intern *trail = NULL;

static int has_non_unity(struct env *env, struct _ex_intern *e)
{
    int i;
    struct _ex_intern *coef;
    static struct _ex_intern *one = NULL, *none = NULL;

    if (one==NULL) {
        one = _ex_intern_small_rational(1,1);
        none = _ex_intern_small_rational(-1,1);
    }

    if (e->user2) return 0;

    e->user2 = trail;
    trail = e;

    if (e->type != EXP_APPL) return 0;

    if (e->u.appl.functor!=INTERN_RAT_TIMES) {
        for (i = 0; i < e->u.appl.count; ++i) {
            if (has_non_unity(env,e->u.appl.args[i])) return 1;
        }
    }

    coef = get_r_coef(env,e);

    return coef != one && coef != none;
}

int _th_has_non_unity(struct env *env, struct _ex_intern *e)
{
    int res;

    trail = _ex_true;

    res = has_non_unity(env,e);

    while (trail) {
        struct _ex_intern *t = trail->user2;
        trail->user2 = NULL;
        trail = t;
    }

    return res;
}

struct _ex_intern *_th_simplify_rat_plus(struct env *env, struct _ex_intern *e)
{
	unsigned one[2] = { 1, 1 };
	unsigned zero[2] = { 1, 0 };
	unsigned *tmp1, *tmp2, *accumulate;
	int i, j;
	struct _ex_intern **args, **coef;
    int count;

    //printf("Simplifying %s\n", _th_print_exp(e));

    if (e->u.appl.count==0) return _ex_intern_small_rational(0,1);
	if (e->u.appl.count==1) return e->u.appl.args[0] ;
	tmp1 = zero ;
	tmp2 = one ;
	j = 0 ;
	for (i = 0; i < e->u.appl.count; ++i) {
		if (e->u.appl.args[i]->type==EXP_RATIONAL) {
			++j ;
			//printf("simplifying rat_plus %s\n", _th_print_exp(e));
			accumulate = _th_big_copy(REWRITE_SPACE,_th_big_gcd(tmp2,e->u.appl.args[i]->u.rational.denominator)) ;
			tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_divide(_th_big_multiply(tmp1,e->u.appl.args[i]->u.rational.denominator),accumulate)) ;
			tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_add(tmp1,_th_big_divide(_th_big_multiply(e->u.appl.args[i]->u.rational.numerator,tmp2),accumulate))) ;
			tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_divide(_th_big_multiply(tmp2,e->u.appl.args[i]->u.rational.denominator),accumulate)) ;
			//printf("end simplify rat_plus\n");
		}
	}
	if (j >= 2 || (j==1 && tmp1[0]==1 && tmp1[1]==0)) {
		//check_size(e->u.appl.count) ;
		args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
		for (i = 0, j = 0; i < e->u.appl.count; ++i) {
			if (e->u.appl.args[i]->type 
                != EXP_RATIONAL) {
				args[j++] = e->u.appl.args[i] ;
			}
		}
        if (j==0) {
            struct _ex_intern *r = _ex_intern_rational(tmp1,tmp2);
            //printf("%s is reduced to ", _th_print_exp(e));
            //printf("%s\n", _th_print_exp(r));
            return _ex_intern_rational(tmp1,tmp2) ;
        }
        if (tmp1[0] != 1 || tmp1[1] != 0) {
		    args[j++] = _ex_intern_rational(tmp1,tmp2) ;
        }
        //printf("%s is reduced to ", _th_print_exp(e));
        //printf("%s\n", _th_print_exp(_ex_intern_appl_env(env,INTERN_RAT_PLUS, j, args)));
		e = _ex_intern_appl_env(env, INTERN_RAT_PLUS, j, args) ;
        //printf("Returning 1 %s\n", _th_print_exp(e));
        return e;
	}

    coef = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
    
    for (i = 0; i < e->u.appl.count; ++i) {
        coef[i] = get_r_coef(env,e->u.appl.args[i]);
        args[i] = strip_r_coef(env,e->u.appl.args[i]);
    }
    
    count = e->u.appl.count;
    for (i = 0; i < count; ++i) {
    	tmp1 = coef[i]->u.rational.numerator ;
	    tmp2 = coef[i]->u.rational.denominator ;
        for (j = i+1; j < count; ++j) {
            if (args[i]==args[j]) {
				//printf("simplify rat_plus b %s\n", _th_print_exp(e));
    			accumulate = _th_big_gcd(tmp2,coef[j]->u.rational.denominator) ;
	    		tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_divide(_th_big_multiply(tmp1,coef[j]->u.rational.denominator),accumulate)) ;
		    	tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_add(tmp1,_th_big_divide(_th_big_multiply(coef[j]->u.rational.numerator,tmp2),accumulate))) ;
			    tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_divide(_th_big_multiply(tmp2,coef[j]->u.rational.denominator),accumulate)) ;
                coef[j] = coef[--count];
                args[j] = args[count];
                --j;
				//printf("end simplify rat_plus b\n");
            }
        }
        coef[i] = _ex_intern_rational(tmp1,tmp2);
    }
    
    if (count < e->u.appl.count) {
        for (i = 0; i < count; ++i) {
            args[i] = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_RAT_TIMES,args[i],coef[i]));
        }
        //printf("%s is reduced to ", _th_print_exp(e));
        //printf("%s\n", _th_print_exp(_ex_intern_appl_env(env,INTERN_RAT_PLUS, count, args)));
        e = _ex_intern_appl_env(env,INTERN_RAT_PLUS,count,args);
        //printf("Returning 2 %s\n", _th_print_exp(e));
        return e;
    }
    
    //printf("Returning 3 NULL\n");
	return NULL ;
}

static struct _ex_intern *remove_rat_less_constants(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *l = e->u.appl.args[0];
    struct _ex_intern *r = e->u.appl.args[1];
    int i, j, k;
    struct _ex_intern *f;
    struct _ex_intern **args;

    if (l->type==EXP_RATIONAL) {
        if (r->type==EXP_APPL && r->u.appl.functor==INTERN_RAT_TIMES) {
            for (i = 0; i < r->u.appl.count; ++i) {
                f = r->u.appl.args[i];
                if (f->type==EXP_RATIONAL) {
                    struct _ex_intern *g = _th_divide_rationals(l,f);
                    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * r->u.appl.count);
                    for (j = 0, k = 0; j < e->u.appl.count; ++j) {
                        if (j != i) args[k++] = r->u.appl.args[j];
                    }
                    if (_th_big_is_negative(f->u.rational.numerator)) {
                        return _ex_intern_appl2_env(env,INTERN_RAT_LESS,
                                   _ex_intern_appl_env(env,INTERN_RAT_TIMES,k,args),g);
                    } else {
                        return _ex_intern_appl2_env(env,INTERN_RAT_LESS,
                                   g,_ex_intern_appl_env(env,INTERN_RAT_TIMES,k,args));
                    }
                }
            }
        }
        if (r->type==EXP_APPL && r->u.appl.functor==INTERN_RAT_PLUS) {
            for (i = 0; i < r->u.appl.count; ++i) {
                f = r->u.appl.args[i];
                if (f->type==EXP_RATIONAL) {
                    struct _ex_intern *g = _th_subtract_rationals(l,f);
                    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * r->u.appl.count);
                    for (j = 0, k = 0; j < r->u.appl.count; ++j) {
                        if (j != i) args[k++] = r->u.appl.args[j];
                    }
                    return _ex_intern_appl2_env(env,INTERN_RAT_LESS,
                               g,_ex_intern_appl_env(env,INTERN_RAT_PLUS,k,args));
                }
            }
        }
    }
    if (r->type==EXP_RATIONAL) {
        if (l->type==EXP_APPL && l->u.appl.functor==INTERN_RAT_TIMES) {
            for (i = 0; i < l->u.appl.count; ++i) {
                f = l->u.appl.args[i];
                if (f->type==EXP_RATIONAL) {
                    struct _ex_intern *g = _th_divide_rationals(r,f);
                    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * l->u.appl.count);
                    for (j = 0, k = 0; j < l->u.appl.count; ++j) {
                        if (j != i) args[k++] = l->u.appl.args[j];
                    }
                    if (_th_big_is_negative(f->u.rational.numerator)) {
                        return _ex_intern_appl2_env(env,INTERN_RAT_LESS,
                                   g,_ex_intern_appl_env(env,INTERN_RAT_TIMES,k,args));
                    } else {
                        return _ex_intern_appl2_env(env,INTERN_RAT_LESS,
                                   _ex_intern_appl_env(env,INTERN_RAT_TIMES,k,args),g);
                    }
                }
            }
        }
        if (l->type==EXP_APPL && l->u.appl.functor==INTERN_RAT_PLUS) {
            for (i = 0; i < l->u.appl.count; ++i) {
                f = l->u.appl.args[i];
                if (f->type==EXP_RATIONAL) {
                    struct _ex_intern *g = _th_subtract_rationals(r,f);
                    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * l->u.appl.count);
                    for (j = 0, k = 0; j < l->u.appl.count; ++j) {
                        if (j != i) args[k++] = l->u.appl.args[j];
                    }
                    return _ex_intern_appl2_env(env,INTERN_RAT_LESS,
                               _ex_intern_appl_env(env,INTERN_RAT_PLUS,k,args),g);
                }
            }
        }
    }
    return NULL;
}

struct _ex_intern *_th_simplify_rat_less(struct env *env, struct _ex_intern *e)
{
	unsigned *tmp1, *tmp2;
    struct _ex_intern *f;

    //printf("Simplifying rless %s\n", _th_print_exp(e));

	if (e->u.appl.args[0]->type == EXP_RATIONAL &&
		e->u.appl.args[1]->type == EXP_RATIONAL) {
		tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(e->u.appl.args[0]->u.rational.numerator,e->u.appl.args[1]->u.rational.denominator)) ;
		tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(e->u.appl.args[1]->u.rational.numerator,e->u.appl.args[0]->u.rational.denominator)) ;
		if (_th_big_less(tmp1,tmp2)) {
			return _ex_true ;
		} else {
			return _ex_false ;
		}
	}
    f = _th_r_simplify_equation(env,e);
    //printf("Here1 %s\n", _th_print_exp(f));
    if (f) return f;
    f = _th_r_collect_like_terms(env,e);
    //printf("Here2 %s\n", _th_print_exp(f));
    if (f) return f;
    f = _th_simplify_rless_by_range(env,e);
    //printf("Here3 %s\n", _th_print_exp(f));
    if (f) return f;
    f = _th_r_remove_times_neg_one(env,e);
    //printf("Here4 %s\n", _th_print_exp(f));
    if (f) {
        //printf("%s is reduced to ", _th_print_exp(e));
        //printf("%s\n", _th_print_exp(f));
        return f;
    }
    f = _th_r_reverse_terms(env,e);
    //printf("Here5 %s\n", _th_print_exp(f));
    if (f) return f;
    f = remove_rat_less_constants(env,e);
    //printf("Here6 %s\n", _th_print_exp(f));
    if (_th_use_transitive) {
        if (f) return f;
        f = _th_r_search_less(env,e);
    }
    //printf("Here7 %s\n", _th_print_exp(f));
    if (f) return f;
    if (_th_extract_relationship(env,e)) {
        if (_th_diff->u.rational.numerator[0]==1 && _th_diff->u.rational.numerator[1]==0) {
            f = _ex_intern_appl2_env(env,INTERN_RAT_LESS,_th_left,_th_right);
        } else if (_th_left->type==EXP_RATIONAL) {
            f = _ex_intern_appl2_env(env,INTERN_RAT_LESS,_th_add_rationals(_th_diff,_th_left),_th_right);
        } else if (_th_right->type==EXP_RATIONAL) {
            _th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(_th_diff->u.rational.numerator)),_th_diff->u.rational.denominator);
            f = _ex_intern_appl2_env(env,INTERN_RAT_LESS,_th_left,_th_diff);
            //printf("Right rational %s\n", _th_print_exp(f));
        } else {
            f = _ex_intern_appl2_env(env,INTERN_RAT_LESS,_ex_intern_appl2_env(env,INTERN_RAT_PLUS,_th_left,_th_diff),_th_right);
        }
        if (f==e) f = NULL;
    }
    //printf("Here8 %s\n", _th_print_exp(f));
    //if (f) return f;
    //f = _th_check_cycle_rless(env, e);
	return f ;
}

struct _ex_intern *_th_simplify_rat_times(struct env *env, struct _ex_intern *e)
{
	unsigned one[2] = { 1, 1 };
	unsigned *tmp1, *tmp2;
	int i, j, k;
	struct _ex_intern **args, *r;

	if (e->u.appl.count==1) return e->u.appl.args[0] ;
	tmp1 = one ;
	tmp2 = one ;
	j = 0 ;
	for (i = 0; i < e->u.appl.count; ++i) {
		if (e->u.appl.args[i]->type==EXP_RATIONAL) {
			++j ;
		    tmp1 = _th_big_copy(REWRITE_SPACE, _th_big_multiply(tmp1,e->u.appl.args[i]->u.rational.numerator)) ;
			tmp2 = _th_big_copy(REWRITE_SPACE, _th_big_multiply(tmp2,e->u.appl.args[i]->u.rational.denominator)) ;
		}
	}
    r = _ex_intern_rational(tmp1,tmp2);
    if (tmp1[0]==1 && tmp1[1]==0) return r;
    tmp1 = r->u.rational.numerator;
    tmp2 = r->u.rational.denominator;
	if (j >= 2 || (j==1 && tmp1[0]==1 && tmp1[1]==1 && tmp2[0]==1 && tmp2[1]==1)) {
		//check_size(e->u.appl.count) ;
		args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
		for (i = 0, j = 0; i < e->u.appl.count; ++i) {
			if (e->u.appl.args[i]->type != EXP_RATIONAL) {
	    		args[j++] = e->u.appl.args[i] ;
			}
		}
	    if (j==0) return r ;
        if (tmp1[0] != 1 || tmp1[1] != 1 || tmp2[0] != 1 || tmp2[1] != 1) {
            args[j++] = r ;
        }
	    return _ex_intern_appl_env(env, INTERN_RAT_TIMES, j, args) ;
	}
    for (i = 0; i < e->u.appl.count; ++i) {
        r = e->u.appl.args[i];
        if (r->type==EXP_APPL && r->u.appl.functor==INTERN_RAT_PLUS) {
            struct _ex_intern **args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * r->u.appl.count);
    		args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            for (j = 0; j < r->u.appl.count; ++j) {
                for (k = 0; k < e->u.appl.count; ++k) {
                    args[k] = e->u.appl.args[k];
                }
                args[i] = r->u.appl.args[j];
                args2[j] = _ex_intern_appl_env(env,INTERN_RAT_TIMES,e->u.appl.count,args);
            }
            return _ex_intern_appl_env(env,INTERN_RAT_PLUS,r->u.appl.count,args2);
        }
    }
	return NULL ;
}

struct _ex_intern *_th_simplify_rat_divide(struct env *env, struct _ex_intern *e)
{
	//unsigned *tmp1, *tmp2, *accumulate;
    struct _ex_intern *f;
    struct _ex_intern *r, **args;
    int i, j, k;

    if (e->u.appl.args[1]->type == EXP_RATIONAL) {
        f = e->u.appl.args[1];
        //if (f->u.rational.numerator[0]==1 && f->u.rational.numerator[1]==0) exit(1);
        if (e->u.appl.args[0]->type == EXP_RATIONAL &&
		    !_th_big_is_zero(f->u.rational.numerator)) {
            return _th_divide_rationals(e->u.appl.args[0],f);
		    //tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(e->u.appl.args[0]->u.rational.numerator,e->u.appl.args[1]->u.rational.denominator)) ;
		    //tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(e->u.appl.args[1]->u.rational.numerator,e->u.appl.args[0]->u.rational.denominator)) ;
		    //accumulate = _th_big_gcd(tmp1,tmp2) ;
		    //tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_divide(tmp1,accumulate)) ;
		    //tmp2 = _th_big_divide(tmp2,accumulate) ;
		    //return _ex_intern_rational(tmp1,tmp2) ;
        }
        if (f->u.rational.numerator[0]==1 && f->u.rational.numerator[1]==1 &&
            f->u.rational.denominator[0]==1 && f->u.rational.denominator[1]==1) return e->u.appl.args[0];
        if (f->u.rational.numerator[0]==1 && f->u.rational.numerator[1]==0xffffffff &&
            f->u.rational.denominator[0]==1 && f->u.rational.denominator[1]==1) return _ex_intern_appl2_env(env,INTERN_RAT_TIMES,e->u.appl.args[0],f);
        if (f->u.rational.numerator[0] != 1 || f->u.rational.numerator[1] != 0) {
            if (_th_big_is_negative(f->u.rational.numerator)) {
                unsigned *tmp1 = _th_big_copy(REWRITE_SPACE,f->u.rational.numerator);
                unsigned *tmp2 = _th_big_copy(REWRITE_SPACE,f->u.rational.denominator);
                return _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_RAT_TIMES,e->u.appl.args[0],_ex_intern_rational(tmp2,tmp1)));
            } else {
                return _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_RAT_TIMES,e->u.appl.args[0],_ex_intern_rational(f->u.rational.denominator,f->u.rational.numerator)));
            }
        }
    }
    for (i = 0; i < e->u.appl.count; ++i) {
        r = e->u.appl.args[i];
        if (r->type==EXP_APPL && r->u.appl.functor==INTERN_RAT_PLUS) {
            struct _ex_intern **args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * r->u.appl.count);
    		args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            for (j = 0; j < r->u.appl.count; ++j) {
                for (k = 0; k < e->u.appl.count; ++k) {
                    args[k] = e->u.appl.args[k];
                }
                args[i] = r->u.appl.args[j];
                args2[j] = _ex_intern_appl_env(env,INTERN_RAT_DIVIDE,e->u.appl.count,args);
            }
            return _ex_intern_appl_env(env,INTERN_RAT_PLUS,r->u.appl.count,args2);
        }
    }
    return NULL ;
}

struct _ex_intern *_th_simplify_rat_minus(struct env *env, struct _ex_intern *e)
{
	unsigned *tmp1, *tmp2, *accumulate;
    //printf("Simplifying %s\n", _th_print_exp(e));
    if (e->u.appl.args[0]->type == EXP_RATIONAL &&
		e->u.appl.args[1]->type == EXP_RATIONAL) {
        //printf("Doing minus\n");
	    //printf("simplify_rat_minus %s\n", _th_print_exp(e));
		tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(e->u.appl.args[0]->u.rational.numerator,e->u.appl.args[1]->u.rational.denominator)) ;
		tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(e->u.appl.args[1]->u.rational.numerator,e->u.appl.args[0]->u.rational.denominator)) ;
        //printf("tmp1 = %s\n", _th_print_exp(_ex_intern_integer(tmp1)));
        //printf("tmp2 = %s\n", _th_print_exp(_ex_intern_integer(tmp2)));
		accumulate = _th_big_copy(REWRITE_SPACE,_th_big_sub(tmp1,tmp2));
        //printf("accumulate = %s\n", _th_print_exp(_ex_intern_integer(accumulate)));
	    tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(e->u.appl.args[0]->u.rational.denominator,e->u.appl.args[1]->u.rational.denominator)) ;
		tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_gcd(tmp1,accumulate)) ;
        //printf("tmp2(b) = %s\n", _th_print_exp(_ex_intern_integer(tmp2)));
		accumulate = _th_big_copy(REWRITE_SPACE,_th_big_divide(accumulate,tmp2)) ;
        //printf("accumulate(b) = %s\n", _th_print_exp(_ex_intern_integer(accumulate)));
		tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_divide(tmp1,tmp2)) ;
        //printf("tmp1(b) = %s\n", _th_print_exp(_ex_intern_integer(tmp1)));
		e = _ex_intern_rational(accumulate,tmp1) ;
        //printf("Result = %s\n", _th_print_exp(e));
		//printf("end simplify_rat_minus\n");
        return e;
	}
    return _ex_intern_appl2_env(env,INTERN_RAT_PLUS,e->u.appl.args[0],_ex_intern_appl2_env(env,INTERN_RAT_TIMES,_ex_intern_small_rational(-1,1),e->u.appl.args[1]));
}

struct _ex_intern *_th_add_term(struct env *env, struct _ex_intern *sum, struct _ex_intern *t)
{
    if (t->type==EXP_INTEGER && t->u.integer[0]==1 && t->u.integer[1]==0) return sum;

    if (sum) {
        return _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,sum,t));
    } else {
        return t;
    }
}

struct _ex_intern *_th_remove_term(struct env *env, struct _ex_intern *sum, struct _ex_intern *t)
{
    if (sum==NULL) return NULL;

    if (sum==t) return NULL;

    if (sum->type==EXP_APPL && sum->u.appl.functor==INTERN_NAT_PLUS) {
        int i, j;
        struct _ex_intern **args;
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * sum->u.appl.count);
        for (i = 0, j = 0; i < sum->u.appl.count; ++i) {
            if (sum->u.appl.args[i] != t) {
                args[j++] = sum->u.appl.args[i];
            }
        }
        if (j==1) {
            return args[0];
        } else {
            return _ex_intern_appl_env(env,INTERN_NAT_PLUS,j,args);
        }
    }

    return sum;
}

struct _ex_intern *_th_get_coef(struct env *env, struct _ex_intern *e)
{
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NAT_TIMES) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type==EXP_INTEGER) {
                return e->u.appl.args[i];
            }
        }
    } else if (e->type==EXP_INTEGER) {
        return e;
    }
    return _ex_one;
}

struct _ex_intern *_th_get_core(struct env *env, struct _ex_intern *e)
{
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NAT_TIMES) {
        int i, j;
        struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
        for (i = 0, j = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type!=EXP_INTEGER) {
                args[j++] = e->u.appl.args[i];
            }
        }
        if (j==1) {
            return args[0];
        } else {
            return _ex_intern_appl_env(env,INTERN_NAT_TIMES,j,args);
        }
    } else if (e->type==EXP_INTEGER) {
        return NULL;
    }
	return e;
}

struct _ex_intern *_th_build_term(struct env *env, struct _ex_intern *coef, struct _ex_intern *core)
{
    if (core==NULL) {
        return coef;
    } else if (coef->u.integer[0]==1 && coef->u.integer[1]==1) {
        return core;
    } else {
        return _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_NAT_TIMES,coef,core));
    }
}

static void add_a_term(struct env *env, struct _ex_intern *t, struct _ex_intern **left_terms, struct _ex_intern **right_terms, int *change)
{
    struct _ex_intern *coef;
    struct _ex_intern *core;
    struct _ex_intern *tcoef;
    struct _ex_intern *tcore;

    tcoef = _th_get_coef(env,t);
    tcore = _th_get_core(env,t);

    //printf("    Adding term %s\n", _th_print_exp(t));
    //printf("        core: %s\n", _th_print_exp(tcore));
    //printf("        coef: %s\n", _th_print_exp(tcoef));

    if (*left_terms != NULL) {
        if ((*left_terms)->type==EXP_APPL && (*left_terms)->u.appl.functor==INTERN_NAT_PLUS) {
            int i, j;
            struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (*left_terms)->u.appl.count);
            //printf("        here 1\n");
            for (i = 0, j = 0; i < (*left_terms)->u.appl.count; ++i) {
                coef = _th_get_coef(env,(*left_terms)->u.appl.args[i]);
                core = _th_get_core(env,(*left_terms)->u.appl.args[i]);
                //printf("        check(3) coef = %s\n", _th_print_exp(coef));
                //printf("        check(3) core = %s\n", _th_print_exp(core));
                if (core==tcore) {
                    tcoef = _ex_intern_integer(_th_big_add(tcoef->u.integer,coef->u.integer));
                    //printf("        CHANGING 4\n");
                    *change = 1;
                } else {
                    args[j++] = (*left_terms)->u.appl.args[i];
                }
            }
            if (j < i) {
                if (j==0) {
                    *left_terms = NULL;
                } else if (j==1) {
                    *left_terms = args[0];
                } else {
                    *left_terms = _ex_intern_appl_env(env,INTERN_NAT_PLUS,j,args);
                }
            }
        } else {
            //printf("        here 2\n");
            coef = _th_get_coef(env,*left_terms);
            core = _th_get_core(env,*left_terms);
            //printf("        check(4) coef = %s\n", _th_print_exp(coef));
            //printf("        check(4) core = %s\n", _th_print_exp(core));
            if (core==tcore) {
                tcoef = _ex_intern_integer(_th_big_add(coef->u.integer,tcoef->u.integer));
                //printf("        CHANGING 3\n");
                *change = 1;
                *left_terms = NULL;
            }
        }
    }

    //printf("        int core: %s\n", _th_print_exp(tcore));
    //printf("        int coef: %s\n", _th_print_exp(tcoef));

    if (*right_terms != NULL) {
        if ((*right_terms)->type==EXP_APPL && (*right_terms)->u.appl.functor==INTERN_NAT_PLUS) {
            int i, j;
            struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (*right_terms)->u.appl.count);
            //printf("        here 3\n");
            for (i = 0, j = 0; i < (*right_terms)->u.appl.count; ++i) {
                coef = _th_get_coef(env,(*right_terms)->u.appl.args[i]);
                core = _th_get_core(env,(*right_terms)->u.appl.args[i]);
                //printf("        check(1) coef = %s\n", _th_print_exp(coef));
                //printf("        check(1) core = %s\n", _th_print_exp(core));
                if (core==tcore) {
                    //printf("        CHANGING 1\n");
                    tcoef = _ex_intern_integer(_th_big_sub(tcoef->u.integer,coef->u.integer));
                    *change = 1;
                } else {
                    args[j++] = (*right_terms)->u.appl.args[i];
                }
            }
            if (j < i) {
                if (j==0) {
                    *right_terms = NULL;
                } else if (j==1) {
                    *right_terms = args[0];
                } else {
                    *right_terms = _ex_intern_appl_env(env,INTERN_NAT_PLUS,j,args);
                }
            }
        } else {
            coef = _th_get_coef(env,*right_terms);
            core = _th_get_core(env,*right_terms);
            //printf("        check(2) coef = %s\n", _th_print_exp(coef));
            //printf("        check(2) core = %s\n", _th_print_exp(core));
            if (core==tcore) {
                tcoef = _ex_intern_integer(_th_big_sub(tcoef->u.integer,coef->u.integer));
                //printf("        CHANGING 2\n");
                *change = 1;
                *right_terms = NULL;
            }
        }
    }

    //printf("        done core: %s\n", _th_print_exp(tcore));
    //printf("        dene coef: %s\n", _th_print_exp(tcoef));

    if (tcoef->u.integer[0]!=1 || tcoef->u.integer[1]!=0) {
        if (_th_big_is_negative(tcoef->u.integer)) {
            tcoef = _ex_intern_integer(_th_complement(tcoef->u.integer));
            //*change = 1;
            *right_terms = _th_add_term(env,*right_terms,_th_build_term(env,tcoef,tcore));
        } else {
            *left_terms = _th_add_term(env,*left_terms,_th_build_term(env,tcoef,tcore));
        }
    }
}

struct _ex_intern *_th_collect_like_terms(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *left_terms = NULL;
    struct _ex_intern *right_terms = NULL;
    int i;
    int change;

    if ((e->u.appl.args[0]->type != EXP_APPL ||
         (e->u.appl.args[0]->u.appl.functor != INTERN_NAT_PLUS &&
          e->u.appl.args[0]->u.appl.functor != INTERN_NAT_TIMES)) &&
        (e->u.appl.args[1]->type != EXP_APPL ||
         (e->u.appl.args[1]->u.appl.functor != INTERN_NAT_PLUS &&
         e->u.appl.args[1]->u.appl.functor != INTERN_NAT_TIMES)) &&
         e->u.appl.functor==INTERN_EQUAL) {
        return NULL;
    }

    //printf("Collecting terms for %s\n", _th_print_exp(e));

    change = 0;

    if (e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_NAT_PLUS) {
        for (i = 0; i < e->u.appl.args[0]->u.appl.count; ++i) {
            add_a_term(env,e->u.appl.args[0]->u.appl.args[i],&left_terms,&right_terms, &change);
        }
    } else {
        add_a_term(env,e->u.appl.args[0],&left_terms,&right_terms, &change);
    }

    //printf("e = %s\n", _th_print_exp(e));

    if (e->u.appl.args[1]->type==EXP_APPL && e->u.appl.args[1]->u.appl.functor==INTERN_NAT_PLUS) {
        for (i = 0; i < e->u.appl.args[1]->u.appl.count; ++i) {
            add_a_term(env,e->u.appl.args[1]->u.appl.args[i],&right_terms,&left_terms,&change);
        }
    } else {
        add_a_term(env,e->u.appl.args[1],&right_terms,&left_terms,&change);
    }

    if (change) {
        if (left_terms==NULL) left_terms = _ex_intern_small_integer(0);
        if (right_terms==NULL) right_terms = _ex_intern_small_integer(0);
        //printf("    left: %s\n", _th_print_exp(left_terms));
        //printf("    right: %s\n", _th_print_exp(right_terms));
        //printf("Done\n");
        if (e->u.appl.count==2) {
            return _ex_intern_appl2_env(env,e->u.appl.functor,left_terms,right_terms);
        } else {
            return _ex_intern_appl3_env(env,e->u.appl.functor,left_terms,right_terms,e->u.appl.args[2]);
        }
    } else {
        //printf("Done %s\n", _th_print_exp(e));
        return NULL;
    }
}

struct _ex_intern *_th_r_add_term(struct env *env, struct _ex_intern *sum, struct _ex_intern *t)
{
    if (t->type==EXP_RATIONAL && t->u.rational.numerator[0]==1 && t->u.rational.numerator[1]==0) return sum;

    if (sum) {
        return _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_RAT_PLUS,sum,t));
    } else {
        return t;
    }
}

struct _ex_intern *_th_r_remove_term(struct env *env, struct _ex_intern *sum, struct _ex_intern *t)
{
    if (sum==NULL) return NULL;

    if (sum==t) return NULL;

    if (sum->type==EXP_APPL && sum->u.appl.functor==INTERN_RAT_PLUS) {
        int i, j;
        struct _ex_intern **args;
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * sum->u.appl.count);
        for (i = 0, j = 0; i < sum->u.appl.count; ++i) {
            if (sum->u.appl.args[i] != t) {
                args[j++] = sum->u.appl.args[i];
            }
        }
        if (j==1) {
            return args[0];
        } else {
            return _ex_intern_appl_env(env,INTERN_RAT_PLUS,j,args);
        }
    }

    return sum;
}

struct _ex_intern *_th_r_get_coef(struct env *env, struct _ex_intern *e)
{
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_TIMES) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type==EXP_RATIONAL) {
                return e->u.appl.args[i];
            }
        }
    } else if (e->type==EXP_RATIONAL) {
        return e;
    }
    return _ex_r_one;
}

struct _ex_intern *_th_r_get_core(struct env *env, struct _ex_intern *e)
{
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_TIMES) {
        int i, j;
        struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
        for (i = 0, j = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type!=EXP_RATIONAL) {
                args[j++] = e->u.appl.args[i];
            }
        }
        if (j==1) {
            return args[0];
        } else {
            return _ex_intern_appl_env(env,INTERN_RAT_TIMES,j,args);
        }
    } else if (e->type==EXP_RATIONAL) {
        return NULL;
    }
	return e;
}

struct _ex_intern *_th_r_build_term(struct env *env, struct _ex_intern *coef, struct _ex_intern *core)
{
    if (core==NULL) {
        return coef;
    } else if (coef->u.rational.numerator[0]==1 && coef->u.rational.numerator[1]==1 && coef->u.rational.denominator[0]==1 && coef->u.rational.denominator[1]==1) {
        return core;
    } else {
        return _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_RAT_TIMES,coef,core));
    }
}

struct _ex_intern *_th_add_rationals(struct _ex_intern *r1, struct _ex_intern *r2)
{
    if (r1->u.rational.numerator[0]==1 && r1->u.rational.numerator[1]==0) {
        return r2;
    } else if (r2->u.rational.numerator[0]==1 && r2->u.rational.numerator[1]==0) {
        return r1;
    } else {
		//printf("Enter _th_add_rationals\n");
		{
        char *mark = _th_alloc_mark(REWRITE_SPACE);
        struct _ex_intern *res;
        unsigned *accumulate = _th_big_copy(REWRITE_SPACE,_th_big_multiply(r1->u.rational.denominator,r2->u.rational.denominator));
        unsigned *tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(r1->u.rational.numerator,r2->u.rational.denominator));
        unsigned *tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(r1->u.rational.denominator,r2->u.rational.numerator));
        //_zone_print1("tmp1 %s", _th_print_exp(_ex_intern_integer(tmp1)));
        //_zone_print1("tmp2 %s", _th_print_exp(_ex_intern_integer(tmp2)));
        //_zone_print1("accumulate %s", _th_print_exp(_ex_intern_integer(accumulate)));
        tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_add(tmp1,tmp2));
        if (tmp1[0]==1 && tmp1[1]==0) {
            return _ex_intern_small_rational(0,1);
        }
        tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_gcd(tmp1,accumulate));
        tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_divide(tmp1,tmp2));
        accumulate = _th_big_copy(REWRITE_SPACE,_th_big_divide(accumulate,tmp2));
        res = _ex_intern_rational(tmp1,accumulate);
        _th_alloc_release(REWRITE_SPACE,mark);
		//printf("exit _th_add_rationals\n");
        return res;
		}
    }
}

struct _ex_intern *_th_subtract_rationals(struct _ex_intern *r1, struct _ex_intern *r2)
{
    if (r1->u.rational.numerator[0]==1 && r1->u.rational.numerator[1]==0) {
        return _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(r2->u.rational.numerator)),r2->u.rational.denominator);
    } else if (r2->u.rational.numerator[0]==1 && r2->u.rational.numerator[1]==0) {
        return r1;
    } else {
		//printf("_th_subtract_rationals\n");
		{
        unsigned *accumulate = _th_big_copy(REWRITE_SPACE,_th_big_multiply(r1->u.rational.denominator,r2->u.rational.denominator));
        unsigned *tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(r1->u.rational.numerator,r2->u.rational.denominator));
        unsigned *tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(r1->u.rational.denominator,r2->u.rational.numerator));
        tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_sub(tmp1,tmp2));
        if (tmp1[0]==1 && tmp1[1]==0) {
            return _ex_intern_small_rational(0,1);
        }
        tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_gcd(tmp1,accumulate));
        tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_divide(tmp1,tmp2));
        accumulate = _th_big_copy(REWRITE_SPACE,_th_big_divide(accumulate,tmp2));
		//printf("end _th_subtract_rationals\n");
        return _ex_intern_rational(tmp1,accumulate);
		}
    }
}

static void r_add_a_term(struct env *env, struct _ex_intern *t, struct _ex_intern **left_terms, struct _ex_intern **right_terms, int *change)
{
    struct _ex_intern *coef;
    struct _ex_intern *core;
    struct _ex_intern *tcoef;
    struct _ex_intern *tcore;

    _zone_print_exp("Adding term", t);
    _zone_print_exp("left", *left_terms);
    _zone_print_exp("right", *right_terms);

    tcoef = _th_r_get_coef(env,t);
    tcore = _th_r_get_core(env,t);

    _zone_print_exp("tcoef", tcoef);
    _zone_print_exp("tcore", tcore);

    //printf("    Adding term %s\n", _th_print_exp(t));
    //printf("        core: %s\n", _th_print_exp(tcore));
    //printf("        coef: %s\n", _th_print_exp(tcoef));

    if (*left_terms != NULL) {
        if ((*left_terms)->type==EXP_APPL && (*left_terms)->u.appl.functor==INTERN_RAT_PLUS) {
            int i, j;
            struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (*left_terms)->u.appl.count);
            //printf("        here 1\n");
            for (i = 0, j = 0; i < (*left_terms)->u.appl.count; ++i) {
                coef = _th_r_get_coef(env,(*left_terms)->u.appl.args[i]);
                core = _th_r_get_core(env,(*left_terms)->u.appl.args[i]);
                //printf("        check(3) coef = %s\n", _th_print_exp(coef));
                //printf("        check(3) core = %s\n", _th_print_exp(core));
                if (core==tcore) {
                    tcoef = _th_add_rationals(tcoef,coef);
                    //printf("        CHANGING 4\n");
                    *change = 1;
                } else {
                    args[j++] = (*left_terms)->u.appl.args[i];
                }
            }
            if (j < i) {
                if (j==0) {
                    *left_terms = NULL;
                } else if (j==1) {
                    *left_terms = args[0];
                } else {
                    *left_terms = _ex_intern_appl_env(env,INTERN_RAT_PLUS,j,args);
                }
            }
        } else {
            //printf("        here 2\n");
            coef = _th_r_get_coef(env,*left_terms);
            core = _th_r_get_core(env,*left_terms);
            //printf("        check(4) coef = %s\n", _th_print_exp(coef));
            //printf("        check(4) core = %s\n", _th_print_exp(core));
            if (core==tcore) {
                tcoef = _th_add_rationals(coef,tcoef);
                //printf("        CHANGING 3\n");
                *change = 1;
                *left_terms = NULL;
            }
        }
    }

    //printf("        int core: %s\n", _th_print_exp(tcore));
    //printf("        int coef: %s\n", _th_print_exp(tcoef));

    if (*right_terms != NULL) {
        if ((*right_terms)->type==EXP_APPL && (*right_terms)->u.appl.functor==INTERN_RAT_PLUS) {
            int i, j;
            struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (*right_terms)->u.appl.count);
            //printf("        here 3\n");
            for (i = 0, j = 0; i < (*right_terms)->u.appl.count; ++i) {
                coef = _th_r_get_coef(env,(*right_terms)->u.appl.args[i]);
                core = _th_r_get_core(env,(*right_terms)->u.appl.args[i]);
                //printf("        check(1) coef = %s\n", _th_print_exp(coef));
                //printf("        check(1) core = %s\n", _th_print_exp(core));
                if (core==tcore) {
                    //printf("        CHANGING 1\n");
                    tcoef = _th_subtract_rationals(tcoef,coef);
                    *change = 1;
                } else {
                    args[j++] = (*right_terms)->u.appl.args[i];
                }
            }
            if (j < i) {
                if (j==0) {
                    *right_terms = NULL;
                } else if (j==1) {
                    *right_terms = args[0];
                } else {
                    *right_terms = _ex_intern_appl_env(env,INTERN_RAT_PLUS,j,args);
                }
            }
        } else {
            coef = _th_r_get_coef(env,*right_terms);
            core = _th_r_get_core(env,*right_terms);
            //printf("        check(2) coef = %s\n", _th_print_exp(coef));
            //printf("        check(2) core = %s\n", _th_print_exp(core));
            if (core==tcore) {
                tcoef = _th_subtract_rationals(tcoef,coef);
                //printf("        CHANGING 2\n");
                *change = 1;
                *right_terms = NULL;
            }
        }
    }

    //printf("        done core: %s\n", _th_print_exp(tcore));
    //printf("        dene coef: %s\n", _th_print_exp(tcoef));

    if (tcoef->u.rational.numerator[0]!=1 || tcoef->u.rational.numerator[1]!=0) {
        if (_th_big_is_negative(tcoef->u.rational.numerator)) {
            tcoef = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(tcoef->u.rational.numerator)),tcoef->u.rational.denominator);
            //*change = 1;
            *right_terms = _th_r_add_term(env,*right_terms,_th_r_build_term(env,tcoef,tcore));
        } else {
            *left_terms = _th_r_add_term(env,*left_terms,_th_r_build_term(env,tcoef,tcore));
        }
    }

    _zone_print_exp("left after", *left_terms);
    _zone_print_exp("right after", *right_terms);
}

struct _ex_intern *_th_r_collect_like_terms(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *left_terms = NULL;
    struct _ex_intern *right_terms = NULL;
    int i;
    int change;

    _zone_print_exp("Collecting like terms", e);
    _tree_indent();

    if ((e->u.appl.args[0]->type != EXP_APPL ||
         (e->u.appl.args[0]->u.appl.functor != INTERN_RAT_PLUS &&
          e->u.appl.args[0]->u.appl.functor != INTERN_RAT_TIMES)) &&
        (e->u.appl.args[1]->type != EXP_APPL ||
         (e->u.appl.args[1]->u.appl.functor != INTERN_RAT_PLUS &&
         e->u.appl.args[1]->u.appl.functor != INTERN_RAT_TIMES)) &&
         e->u.appl.functor==INTERN_EQUAL) {
        _tree_undent();
        return NULL;
    }

    //printf("Collecting terms for %s\n", _th_print_exp(e));

    change = 0;

    if (e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_RAT_PLUS) {
        for (i = 0; i < e->u.appl.args[0]->u.appl.count; ++i) {
            r_add_a_term(env,e->u.appl.args[0]->u.appl.args[i],&left_terms,&right_terms, &change);
        }
    } else {
        r_add_a_term(env,e->u.appl.args[0],&left_terms,&right_terms, &change);
    }

    //printf("e = %s\n", _th_print_exp(e));

    if (e->u.appl.args[1]->type==EXP_APPL && e->u.appl.args[1]->u.appl.functor==INTERN_RAT_PLUS) {
        for (i = 0; i < e->u.appl.args[1]->u.appl.count; ++i) {
            r_add_a_term(env,e->u.appl.args[1]->u.appl.args[i],&right_terms,&left_terms,&change);
        }
    } else {
        r_add_a_term(env,e->u.appl.args[1],&right_terms,&left_terms,&change);
    }

    if (change) {
        if (left_terms==NULL) left_terms = _ex_intern_small_rational(0,1);
        if (right_terms==NULL) right_terms = _ex_intern_small_rational(0,1);
        //printf("    left: %s\n", _th_print_exp(left_terms));
        //printf("    right: %s\n", _th_print_exp(right_terms));
        //printf("Done\n");
        _zone_print1("left terms", left_terms);
        _zone_print1("right terms", right_terms);
        _zone_print0("Done");
        _tree_undent();
        if (e->u.appl.count==2) {
            return _ex_intern_appl2_equal_env(env,e->u.appl.functor,left_terms,right_terms,_ex_real);
        } else {
            return _ex_intern_appl3_env(env,e->u.appl.functor,left_terms,right_terms,e->u.appl.args[2]);
        }
    } else {
        //printf("Done %s\n", _th_print_exp(e));
        _tree_undent();
        return NULL;
    }
}

struct _ex_intern *_th_remove_times_neg_one(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *f, *g, *h, *x;

    if (e->u.appl.args[1]->type==EXP_INTEGER && e->u.appl.args[1]->u.integer[0]==1 &&
        e->u.appl.args[1]->u.integer[1]==0) {
        f = e->u.appl.args[0];
    } else if (e->u.appl.args[0]->type==EXP_INTEGER && e->u.appl.args[0]->u.integer[0]==1 &&
        e->u.appl.args[0]->u.integer[1]==0) {
        f = e->u.appl.args[1];
    } else {
        return NULL;
    }

    if (f->type != EXP_APPL || f->u.appl.functor != INTERN_NAT_PLUS ||
        f->u.appl.count != 2) return NULL;

    g = f->u.appl.args[0];
    x = f->u.appl.args[1];
    if (g->type!=EXP_APPL || g->u.appl.functor!=INTERN_NAT_TIMES || g->u.appl.count!=2) {
        g = f->u.appl.args[1];
        x = f->u.appl.args[0];
    }
    if (g->type!=EXP_APPL || g->u.appl.functor!=INTERN_NAT_TIMES || g->u.appl.count!=2) {
        return NULL;
    }

    h = g->u.appl.args[0];
    if (h->type!=EXP_INTEGER || h->u.integer[0]!=1 || h->u.integer[1]!=0xffffffff) {
        h = g->u.appl.args[1];
        if (h->type!=EXP_INTEGER || h->u.integer[0]!=1 || h->u.integer[1]!=0xffffffff) {
            return NULL;
        } else {
            h = g->u.appl.args[0];
        }
    } else {
        h = g->u.appl.args[1];
    }

    if (e->u.appl.args[0]->type==EXP_INTEGER) {
        if (e->u.appl.count==2) {
            return _ex_intern_appl2_env(env,e->u.appl.functor,h,x);
        } else {
            return _ex_intern_appl3_env(env,e->u.appl.functor,h,x,e->u.appl.args[2]);
        }
    } else {
        if (e->u.appl.count==2) {
            return _ex_intern_appl2_env(env,e->u.appl.functor,x,h);
        } else {
            return _ex_intern_appl3_env(env,e->u.appl.functor,x,h,e->u.appl.args[2]);
        }
    }
}

struct _ex_intern *_th_r_remove_times_neg_one(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *f, *g, *h, *x;

    if (e->u.appl.args[1]->type==EXP_RATIONAL && e->u.appl.args[1]->u.rational.numerator[0]==1 &&
        e->u.appl.args[1]->u.rational.numerator[1]==0) {
        f = e->u.appl.args[0];
    } else if (e->u.appl.args[0]->type==EXP_RATIONAL && e->u.appl.args[0]->u.rational.numerator[0]==1 &&
        e->u.appl.args[0]->u.rational.numerator[1]==0) {
        f = e->u.appl.args[1];
    } else {
        return NULL;
    }

    if (f->type != EXP_APPL || f->u.appl.functor != INTERN_RAT_PLUS ||
        f->u.appl.count != 2) return NULL;

    g = f->u.appl.args[0];
    x = f->u.appl.args[1];
    if (g->type!=EXP_APPL || g->u.appl.functor!=INTERN_RAT_TIMES || g->u.appl.count!=2) {
        g = f->u.appl.args[1];
        x = f->u.appl.args[0];
    }
    if (g->type!=EXP_APPL || g->u.appl.functor!=INTERN_RAT_TIMES || g->u.appl.count!=2) {
        return NULL;
    }

    h = g->u.appl.args[0];
    if (h->type!=EXP_RATIONAL || h->u.rational.numerator[0]!=1 || h->u.rational.numerator[1]!=0xffffffff ||
        h->u.rational.denominator[0]!=1 || h->u.rational.denominator[1]!=1) {
        h = g->u.appl.args[1];
        if (h->type!=EXP_RATIONAL || h->u.rational.numerator[0]!=1 || h->u.rational.numerator[1]!=0xffffffff ||
            h->u.rational.denominator[0]!=1 || h->u.rational.denominator[1]!=1) {
            return NULL;
        } else {
            h = g->u.appl.args[0];
        }
    } else {
        h = g->u.appl.args[1];
    }

    if (e->u.appl.args[0]->type==EXP_RATIONAL) {
        if (e->u.appl.count==2) {
            return _ex_intern_appl2_equal_env(env,e->u.appl.functor,h,x,_ex_real);
        } else {
            return _ex_intern_appl3_env(env,e->u.appl.functor,h,x,e->u.appl.args[2]);
        }
    } else {
        if (e->u.appl.count==2) {
            return _ex_intern_appl2_env(env,e->u.appl.functor,x,h);
        } else {
            return _ex_intern_appl3_env(env,e->u.appl.functor,x,h,e->u.appl.args[2]);
        }
    }
}

void _th_add_solve_rules(int s, struct env *env)
{
    //_th_add_property(env,_th_parse(env,"(= (== (nminus x y) z) (== x (nplus y z)) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(= (== x y) (False) (nless x y))")) ;
    _th_add_property(env,_th_parse(env,"(-> (nless x (nplus y 1)) (True) (== x y))")) ;
    //_th_add_property(env,_th_parse(env,"(= (nminus x (nplus a b)) (nminus (nminus x a) b) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(= (nplus (nminus x a) b) (nminus x (nminus a b)) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(= (nplus (nminus x b) a) (nminus (nplus x a) b) (True))")) ;

    //_th_add_property(env,_th_parse(env,"(-> (nminus (nplus x a) b) x (== a b))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (rminus (rplus x a) b) x (== a b))")) ;
    //_th_add_property(env,_th_parse(env,"(= (nminus (nplus a b) c) (nplus (nminus a c) b) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (nminus (nplus 1 x) (nplus 1 y)) (nminus x y) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (|| (nless x y) (nless y1 x1) (== x2 y2)) (True) (and (== x x1) (== x x2) (== y y1) (== y y2)))")) ;
    _th_add_property(env,_th_parse(env,"(-> (|| (rless x y) (rless y1 x1) (== x2 y2)) (True) (and (== x x1) (== x x2) (== y y1) (== y y2)))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (&& (nless x y) (nless y1 x1)) (False) (and (== x x1) (== y y1)))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (&& (== x y) (nless y1 x1)) (False) (and (== x x1) (== y y1)))")) ;
    _th_add_property(env,_th_parse(env,"(-> (nless (nplus a 1) b) (True) (&& (not (== (nplus a 1) b)) (nless a b)))")) ;
    _th_add_property(env,_th_parse(env,"(-> (ntimes x (nplus y z)) (nplus (ntimes x y) (ntimes x z)) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (== x (nplus x1 1)) (False) (and (inContext \"mainContext\") (== x x1)))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (== (nplus x y) (nplus x1 z)) (== y z) (and (inContext \"mainContext\") (== x x1)))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (nless (nplus x y) (nplus x1 z)) (nless y z) (and (inContext \"mainContext\") (== x x1)))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (nless x y) (False) (== x y))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (nminus x y) 0 (== x y))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (nminus x 0) x (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (== (nminus x a) b) (== x (nplus a b)) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (nless (nminus x a) b) (nless x (nplus a b)) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (nplus x 0) x (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (nless a (nminus b x)) (nless (nplus a x) b) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (not (nless a b)) (nless b (nplus a 1)) (q_nat a))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (not (nless a b)) (nless (nminus b 1) a) (q_nat b))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (nplus (nminus a b) c) (nplus a (nminus c b)) (and (q_nat b) (q_nat c)))")) ;
    _th_add_property(env,_th_parse(env,"(-> (== (ntimes x a) (ntimes x1 b)) (== a b) (and (== x x1) (not (== x 0))))")) ;
    _th_add_property(env,_th_parse(env,"(= (== (rminus x y) z) (== x (rplus y z)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(= (== x y) (False) (rless x y))")) ;
    _th_add_property(env,_th_parse(env,"(-> (rless x (rplus x1 y)) (True) (and (== x x1) (rless #0/1 y)))")) ;
    //_th_add_property(env,_th_parse(env,"(= (rminus x (rplus a b)) (rminus (rminus x a) b) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(= (rplus (rminus x a) b) (rminus x (rminus a b)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (rminus (rplus a x) (rplus b x1)) (rminus a b) (== x x1))")) ;
    _th_add_property(env,_th_parse(env,"(-> (|| (rless x y) (rless y1 x1) (== x2 y2)) (True) (and (== x x1) (== x x2) (== y y1) (== y y2)))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (&& (rless x y) (rless y1 x1)) (False) (and (== x x1) (== y y1)))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (&& (== x y) (rless y1 x1)) (False) (and (== x x1) (== y y1)))")) ;
    _th_add_property(env,_th_parse(env,"(-> (rtimes x (rplus y z)) (rplus (rtimes x y) (rtimes x z)) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (== x (rplus x1 y)) (== y 0) (== x x1))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (== (rplus x y) (rplus x1 z)) (== y z) (== x x1))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (rless (x y)) (False) (== x y))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (rminus x x1) #0/1 (== x x1))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (== (rminus (x a)) b) (== x (rplus a b)) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (rless (rminus (x a)) b) (rless x (rplus a b)) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (rless (b rminus (x a))) (rless (rplus a b) x) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (rplus x #0/1) x (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (rtimes x (rplus a b)) (rplus (rtimes x a) (rtimes x b)) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (nplus (ntimes a x) (ntimes b x1)) (ntimes (nplus a b) x) (and (q_nat a) (q_nat b) (== x x1)))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (nminus (nminus x a) b) (nminus x (nplus a b)) (and (q_nat a) (q_nat b)))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (rplus (rtimes a x) (rtimes b x1)) (rtimes (rplus a b) x) (and (== x x1) (q_rat a) (q_rat b)))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (nplus (ntimes a x) x1) (ntimes (nplus a 1) x) (and (q_nat a) (== x x1)))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (rplus (rtimes a x) x1) (rtimes (rplus a #1/1) x) (and (q_rat a) (== x x1)))")) ;

    //_th_add_property(env,_th_parse(env,"(-> (-> (nplus x v) y c) (-> x (nminus y v) c) (and (compatible_prec x c) (compatible_prec x (nminus y v))))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (-> (nminus x v) y c) (-> x (nplus y v) c) (and (compatible_prec x c) (compatible_prec x (nplus y v))))")) ;

    //_th_add_property(env,_th_parse(env,"(+> (nless a b) (False) (and (q_nat a) (nestingLimit 1) (nless b (nplus a 1))))")) ;

    _th_add_property(env,_th_parse(env, "(+> (-> (nmod (nplus x y) v) z (True)) (== (nmod x v) (nmod (nminus (nplus z v) y) v)) (and (q_nat v) (q_nat y) (q_nat z) (nless -1 y) (nless y v) (nless z v) (nless -1 z)))"));
    _th_add_property(env,_th_parse(env, "(+> (-> (nmod (ndivide x d) v) r (True)) (&& (nless (nmod x (ntimes v d)) (nplus (ntimes r d) d)) (nless (nminus (ntimes r d) 1) (nmod x (ntimes v d)))) (and (q_nat d) (q_nat r) (q_nat v) (nless -1 d) (nless -1 r) (nless -1 v)))"));

    _th_add_property(env,_th_parse(env, "(-> (nless (nmod x y) z) (True) (not (nless z y)))"));
    _th_add_property(env,_th_parse(env, "(-> (nless z (nmod x y)) (True) (nless z 0))"));
    _th_add_property(env,_th_parse(env, "(+> (nless (nmod (nplus x c) z) v) (|| (nless (nmod x z) (nminus v c)) (nless (nminus z (nplus c 1)) (nmod x z))) (and (q_nat z) (q_nat c) (q_nat v) (not (nless z c)) (nless -1 z) (nless -1 c) (nless -1 v))))"));
    _th_add_property(env,_th_parse(env, "(+> (nless v (nmod (nplus x c) z)) (&& (nless (nminus v c) (nmod x z)) (nless (nmod x z) (nminus z c))) (and (q_nat z) (q_nat c) (q_nat v) (not (nless z c)) (nless -1 z) (nless -1 c) (nless -1 v))))"));
    _th_add_property(env,_th_parse(env, "(+> (|| (nless a b) (nless c a)) (True) (and (q_nat b) (q_nat c) (nless c b)))"));

    //_th_add_property(env,_th_parse(env, "(priority -1 (+> (nless a b) (nless (nplus a 1) b) (and (q_nat a) (not (== (nplus a 1) b)) (notl (not (== (nplus a 2) b))))))")) ;
    //_th_add_property(env,_th_parse(env, "(priority -1 (+> (nless a b) (nless a (nminus b 1)) (and (inContext \"mainContext\") (q_nat b) (not (== (nplus a 1) b)))))")) ;

    _th_add_property(env,_th_parse(env, "(-> (ndivide a (ntimes b c)) (ndivide (ndivide a (gcd a b)) (ntimes (ndivide b (gcd a b)) c)) (and (q_nat a) (q_nat b) (nless 1 (gcd a b))))")) ;
    _th_add_property(env,_th_parse(env, "(-> (ndivide (ntimes a c) (ntimes b d)) (ndivide (ntimes (ndivide a (gcd a b)) c) (ntimes (ndivide b (gcd a b)) d)) (and (q_nat a) (q_nat b) (nless 1 (gcd a b))))")) ;
    _th_add_property(env,_th_parse(env, "(-> (ndivide (ntimes a c) b) (ndivide (ntimes (ndivide a (gcd a b)) c) (ndivide b (gcd a b))) (and (q_nat a) (q_nat b) (nless 1 (gcd a b))))")) ;

    //_th_add_property(env,_th_parse(env, "(-> (ndivide x 1) x (True))"));

    _th_add_property(env,_th_parse(env, "(+> (&& (nless x lim) (not (-> x lim1 (True)))) (nless x lim1) (and (q_nat lim) (q_nat lim1) (== (nplus lim1 1) lim)))"));
    _th_add_property(env,_th_parse(env, "(+> (&& (nless lim x) (not (-> x lim1 (True)))) (nless lim1 x) (and (q_nat lim) (q_nat lim1) (== (nplus lim 1) lim1)))"));

    _th_add_property(env,_th_parse(env, "(+> (&& (nless lim x) (nless x lim1)) (== x (nplus lim 1)) (== lim1 (nplus lim 2)))"));

    //_th_add_property(env,_th_parse(env, "(+> (nless (nplus a b) c) (nless a (nminus c b)) (and (q_nat b) (q_nat c)))"));                                                
    //_th_add_property(env,_th_parse(env, "(+> (nless c (nplus a b)) (nless (nminus c b) a) (and (q_nat b) (q_nat c)))"));                                                
    //_th_add_property(env,_th_parse(env, "(+> (nminus (nplus a b) c) (nminus a (nminus c b)) (and (q_nat b) (q_nat c)))"));
    //_th_add_property(env,_th_parse(env, "(+> (nminus a b) (nplus a (nminus 0 b)) (q_nat b))"));
    //_th_add_property(env,_th_parse(env, "(-> (ntimes x 0) 0 (True))"));
    //_th_add_property(env,_th_parse(env, "(-> (ntimes x 1) x (True))"));
    _th_add_property(env,_th_parse(env, "(-> (nplus (nminus a b) c) (nminus (nplus a c) b) (and (q_nat a) (q_nat c)))"));

    _th_add_property(env,_th_parse(env, "(-> (nminus a b) (nplus a (ntimes -1 b)) (True))"));
    _th_add_property(env,_th_parse(env, "(-> (ntimes a (ndivide b c)) (ndivide (ntimes a b) c) (== (gcd a c) 1))"));

    _th_add_property(env,_th_parse(env, "(-> (ndivide a b) (ndivide (ntimes -1 a) (ntimes -1 b)) (and (q_nat b) (nless b 0)))"));
    _th_add_property(env,_th_parse(env, "(-> (ndivide (ntimes a t) b) (nplus (ntimes (ndivide a b) t) (ndivide (ntimes (nmod a b) t) b)) (and (q_nat a) (q_nat b) (nless 0 b) (nless b a)))"));
    _th_add_property(env,_th_parse(env, "(-> (ndivide (nplus x (ntimes a t)) b) (nplus (ntimes (ndivide a b) t) (ndivide (nplus x (ntimes (nmod a b) t)) b)) (and (q_nat a) (q_nat b) (nless 0 b) (nless b a)))"));
    _th_add_property(env,_th_parse(env, "(-> (ndivide (ntimes a t) b) \
                                               (nminus \
                                                   (ndivide \
                                                       (ntimes \
                                                           (nplus a (ntimes b (ndivide (nminus (nminus b 1) a) b))) \
                                                           t) \
                                                       b) \
                                                   (ntimes (ndivide (nminus (nminus b 1) a) b) t)) \
                                               (and (q_nat a) (q_nat b) (nless 0 b) (nless a 0)))"));
    _th_add_property(env,_th_parse(env, "(-> (ndivide (nplus x (ntimes a t)) b) \
                                               (nminus \
                                                   (ndivide \
                                                       (nplus x \
                                                           (ntimes \
                                                               (nplus a (ntimes b (ndivide (nminus (nminus b 1) a) b))) \
                                                               t) \
                                                           ) \
                                                       b) \
                                                   (ntimes (ndivide (nminus (nminus b 1) a) b) t)) \
                                               (and (q_nat a) (q_nat b) (nless 0 b) (nless a 0)))"));


    _th_add_property(env,_th_parse(env, "(-> (nmod x 1) 0 (True))"));
    _th_add_property(env,_th_parse(env, "(+> (nmod x y) (nmod x (nminus 0 y)) (and (q_nat y) (nless y 0)))"));
    //_th_add_property(env,_th_parse(env, "(-> (-> (nplus x c) x (True)) (== c 0) (True))"));
	//_th_add_property(env,_th_parse(env, "(-> (== (nplus a b) (nplus c d)) (== a (nplus c (nminus d b))) (and (q_nat b) (q_nat d) (nless b d)))"));
	//_th_add_property(env,_th_parse(env, "(-> (-> (nplus a b) (nplus c d) (True)) (== a (nplus c (nminus d b))) (and (q_nat b) (q_nat d) (nless b d)))"));
	//_th_add_property(env,_th_parse(env, "(-> (-> (nplus c d) (nplus a b) (True)) (== a (nplus c (nminus d b))) (and (q_nat b) (q_nat d) (nless b d)))"));
    //_th_add_property(env,_th_parse(env, "(-> (== (nplus a (ntimes b c)) (nplus d (ntimes e c))) (== a (nplus d (ntimes (nminus e b) c))) (and (q_nat e) (q_nat b) (nless b e)))"));
    //_th_add_property(env,_th_parse(env, "(-> (-> (nplus a (ntimes b c)) (nplus d (ntimes e c)) (True)) (-> a (nplus d (ntimes (nminus e b) c)) (True)) (and (q_nat e) (q_nat b) (nless b e)))"));
    //_th_add_property(env,_th_parse(env, "(-> (-> (nplus d (ntimes e c)) (nplus a (ntimes b c)) (True)) (-> (nplus d (ntimes (nminus e b) c)) a (True)) (and (q_nat e) (q_nat b) (nless b e)))"));
    //_th_add_property(env,_th_parse(env, "(-> (-> (ntimes n x) x (True)) (== (ntimes (nminus n 1) x) 0) (q_nat n))"));
    //_th_add_property(env,_th_parse(env, "(-> (-> (nplus (ntimes n x) c) x (True)) (== (nplus (ntimes (nminus n 1) x) c) 0) (q_nat n))"));
	//_th_add_property(env,_th_parse(env, "(-> (-> (ntimes n x) (nplus x y) (True)) (== (ntimes (nminus n 1) x) y) (True))"));
    _th_add_property(env,_th_parse(env, "(-> (-> (ntimes n x) 0 (True)) (== x 0) (and (q_nat n) (not (== n 0))))"));
    _th_add_property(env,_th_parse(env, "(-> (-> (ntimes n x) m (True)) (False) (and (q_nat n) (q_nat m) (not (== (nmod m n) 0))))"));
    //_th_add_property(env,_th_parse(env, "(+> (nplus x x) (ntimes 2 x) (True))"));
}

struct _ex_intern *_th_reverse_terms(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *l = e->u.appl.args[0];
    struct _ex_intern *r = e->u.appl.args[1];
    struct _ex_intern *nl, *nr;
    struct _ex_intern *c, *t;
    int i;

    if (l->type==EXP_APPL && l->u.appl.functor==INTERN_NAT_PLUS) {
        for (i = 0; i < l->u.appl.count; ++i) {
            if (l->u.appl.args[i]->type != EXP_INTEGER) {
                c = _th_get_coef(env,l->u.appl.args[i]);
                if (!_th_big_is_negative(c->u.integer)) {
                    return NULL;
                }
            }
        }
    } else {
        if (l->type != EXP_INTEGER) {
            c = _th_get_coef(env,l);
            if (!_th_big_is_negative(c->u.integer)) {
                return NULL;
            }
        }
    }

    if (r->type==EXP_APPL && r->u.appl.functor==INTERN_NAT_PLUS) {
        for (i = 0; i < r->u.appl.count; ++i) {
            if (r->u.appl.args[i]->type != EXP_INTEGER) {
                c = _th_get_coef(env,r->u.appl.args[i]);
                if (!_th_big_is_negative(c->u.integer)) {
                    return NULL;
                }
            }
        }
    } else {
        if (r->type != EXP_INTEGER) {
            c = _th_get_coef(env,r);
            if (!_th_big_is_negative(c->u.integer)) {
                return NULL;
            }
        }
    }

    if (l->type==EXP_APPL && l->u.appl.functor==INTERN_NAT_PLUS) {
        nl = NULL;
        for (i = 0; i < l->u.appl.count; ++i) {
            c = _th_get_coef(env,l->u.appl.args[i]);
            t = _th_get_core(env,l->u.appl.args[i]);
            nl = _th_add_term(env,nl,_th_build_term(env,_ex_intern_integer(_th_complement(c->u.integer)),t));
        }
    } else {
        c = _th_get_coef(env,l);
        t = _th_get_core(env,l);
        nl = _th_build_term(env,_ex_intern_integer(_th_complement(c->u.integer)),t);
    }

    if (r->type==EXP_APPL && r->u.appl.functor==INTERN_NAT_PLUS) {
        nr = NULL;
        for (i = 0; i < r->u.appl.count; ++i) {
            c = _th_get_coef(env,r->u.appl.args[i]);
            t = _th_get_core(env,r->u.appl.args[i]);
            nr = _th_add_term(env,nr,_th_build_term(env,_ex_intern_integer(_th_complement(c->u.integer)),t));
        }
    } else {
        c = _th_get_coef(env,r);
        t = _th_get_core(env,r);
        nr = _th_build_term(env,_ex_intern_integer(_th_complement(c->u.integer)),t);
    }

    if (e->u.appl.count==2) {
        return _ex_intern_appl2_env(env,e->u.appl.functor,nr,nl);
    } else {
        return _ex_intern_appl3_env(env,e->u.appl.functor,nr,nl,e->u.appl.args[2]);
    }
}

struct _ex_intern *_th_r_reverse_terms(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *l = e->u.appl.args[0];
    struct _ex_intern *r = e->u.appl.args[1];
    struct _ex_intern *nl, *nr;
    struct _ex_intern *c, *t;
    int i;

    if (l->type==EXP_APPL && l->u.appl.functor==INTERN_RAT_PLUS) {
        for (i = 0; i < l->u.appl.count; ++i) {
            if (l->u.appl.args[i]->type != EXP_RATIONAL) {
                c = _th_r_get_coef(env,l->u.appl.args[i]);
                if (!_th_big_is_negative(c->u.rational.numerator)) {
                    return NULL;
                }
            }
        }
    } else {
        if (l->type != EXP_RATIONAL) {
            c = _th_r_get_coef(env,l);
            if (!_th_big_is_negative(c->u.rational.numerator)) {
                return NULL;
            }
        }
    }

    if (r->type==EXP_APPL && r->u.appl.functor==INTERN_RAT_PLUS) {
        for (i = 0; i < r->u.appl.count; ++i) {
            if (r->u.appl.args[i]->type != EXP_RATIONAL) {
                c = _th_r_get_coef(env,r->u.appl.args[i]);
                if (!_th_big_is_negative(c->u.rational.numerator)) {
                    return NULL;
                }
            }
        }
    } else {
        if (r->type != EXP_RATIONAL) {
            c = _th_r_get_coef(env,r);
            if (!_th_big_is_negative(c->u.rational.numerator)) {
                return NULL;
            }
        }
    }

    if (l->type==EXP_APPL && l->u.appl.functor==INTERN_RAT_PLUS) {
        nl = NULL;
        for (i = 0; i < l->u.appl.count; ++i) {
            c = _th_r_get_coef(env,l->u.appl.args[i]);
            t = _th_r_get_core(env,l->u.appl.args[i]);
            nl = _th_r_add_term(env,nl,_th_r_build_term(env,_ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(c->u.rational.numerator)),c->u.rational.denominator),t));
        }
    } else {
        c = _th_r_get_coef(env,l);
        t = _th_r_get_core(env,l);
        nl = _th_r_build_term(env,_ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(c->u.rational.numerator)),c->u.rational.denominator),t);
    }

    if (r->type==EXP_APPL && r->u.appl.functor==INTERN_RAT_PLUS) {
        nr = NULL;
        for (i = 0; i < r->u.appl.count; ++i) {
            c = _th_r_get_coef(env,r->u.appl.args[i]);
            t = _th_r_get_core(env,r->u.appl.args[i]);
            nr = _th_r_add_term(env,nr,_th_r_build_term(env,_ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(c->u.rational.numerator)),c->u.rational.denominator),t));
        }
    } else {
        c = _th_r_get_coef(env,r);
        t = _th_r_get_core(env,r);
        nr = _th_r_build_term(env,_ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(c->u.rational.numerator)),c->u.rational.denominator),t);
    }

    if (e->u.appl.count==2) {
        return _ex_intern_appl2_env(env,e->u.appl.functor,nr,nl);
    } else {
        return _ex_intern_appl3_env(env,e->u.appl.functor,nr,nl,e->u.appl.args[2]);
    }
}

static struct _ex_intern *diff_except(struct env *env, struct _ex_intern *left, struct _ex_intern *right, struct _ex_intern *term)
{
    struct _ex_intern *result = NULL;
    struct _ex_intern *t, *c;
    int i;

    if (left->type==EXP_APPL && left->u.appl.functor==INTERN_NAT_PLUS) {
        for (i = 0; i < left->u.appl.count; ++i) {
            if (left->u.appl.args[i] != term) {
                if (left->u.appl.args[i]->type != EXP_INTEGER ||
                    left->u.appl.args[i]->u.integer[0] != 1 ||
                    left->u.appl.args[i]->u.integer[1] != 0) {
                    result = _th_add_term(env,result,left->u.appl.args[i]);
                }
            }
        }
    } else {
        if (left->type != EXP_INTEGER ||
            left->u.integer[0] != 1 ||
            left->u.integer[1] != 0) {
            if (left != term) result = left;
        }
    }

    if (right->type==EXP_APPL && right->u.appl.functor==INTERN_NAT_PLUS) {
        for (i = 0; i < right->u.appl.count; ++i) {
            if (right->u.appl.args[i] != term) {
                if (right->u.appl.args[i]->type != EXP_INTEGER ||
                    right->u.appl.args[i]->u.integer[0] != 1 ||
                    right->u.appl.args[i]->u.integer[1] != 0) {

                    c = _th_get_coef(env,right->u.appl.args[i]);
                    t = _th_get_core(env,right->u.appl.args[i]);
                    result = _th_add_term(env,result,_th_build_term(env,_ex_intern_integer(_th_complement(c->u.integer)),t));
                }
            }
        }
    } else {
        if (right != term) {
            if (right->type != EXP_INTEGER ||
                right->u.integer[0] != 1 ||
                right->u.integer[1] != 0) {
                c = _th_get_coef(env,right);
                t = _th_get_core(env,right);
                result = _th_add_term(env,result,_th_build_term(env,_ex_intern_integer(_th_complement(c->u.integer)),t));
            }
        }
    }

    return result;
}

static struct add_list *make_variant(struct env *env, struct _ex_intern *e, struct _ex_intern *left, struct _ex_intern *right, struct add_list *al)
{
    struct add_list *a;
    struct _ex_intern *res;
    int not_mode = 0;

    if (e->u.appl.functor==INTERN_NOT) {
        not_mode = 1;
        e = e->u.appl.args[0];
    }

    if (left==NULL) {
        left = _ex_intern_small_integer(0);
    }
    if (right==NULL) {
        right = _ex_intern_small_integer(0);
    }

    if (e->u.appl.count==2) {
        res = _ex_intern_appl2_env(env,e->u.appl.functor,left,right);
    } else {
        res = _ex_intern_appl3_env(env,e->u.appl.functor,left,right,e->u.appl.args[2]);
    }
    if (res==e) return al;
    if (not_mode) {
        res = _ex_intern_appl1_env(env,INTERN_NOT,res);
    }
    a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
    a->next = al;
    a->e = res;
    //printf("    variant %s\n", _th_print_exp(res));
    //fflush(stdout);
    return a;
}

struct add_list *_th_get_transpositions(struct env *env, struct _ex_intern *e, struct add_list *al)
{
    int i;
    struct _ex_intern *rest;
    struct _ex_intern *t, *c;
    struct _ex_intern *left, *right;
    struct add_list *l;

    //printf("e = %s\n", _th_print_exp(e));
    //fflush(stdout);

    _zone_print_exp("transpositions of", e);
    _tree_indent();

    if (e->type != EXP_APPL) {
        _tree_undent();
        return al;
    }
    if (e->u.appl.functor != INTERN_NOT && e->u.appl.functor != INTERN_EQUAL && e->u.appl.functor != INTERN_NAT_LESS) {
        _tree_undent();
        return al;
    }
    if (e->u.appl.functor==INTERN_NOT) {
        struct _ex_intern *f = e->u.appl.args[0];
        if (f->type != EXP_APPL) {
            _tree_undent();
            return al;
        }
        if (f->u.appl.functor != INTERN_EQUAL && f->u.appl.functor != INTERN_NAT_LESS) {
            _tree_undent();
            return al;
        }
        left = f->u.appl.args[0];
        right = f->u.appl.args[1];
    } else {
        left = e->u.appl.args[0];
        right = e->u.appl.args[1];
    }
    if (left->type==EXP_APPL && left->u.appl.functor==INTERN_NAT_PLUS) {
        for (i = 0; i < left->u.appl.count; ++i) {
            c = _th_get_coef(env,left->u.appl.args[i]);
            if (_th_big_is_negative(c->u.integer)) {
                t = _th_get_core(env,left->u.appl.args[i]);
                rest = diff_except(env,left,right,left->u.appl.args[i]);
                t = _th_build_term(env,_ex_intern_integer(_th_complement(c->u.integer)),t);
                if (rest==NULL) rest = _ex_intern_small_integer(0);
                if (t->type != EXP_INTEGER) al = make_variant(env,e,rest,t,al);
            } else {
                rest = diff_except(env,right,left,left->u.appl.args[i]);
                if (left->u.appl.args[i]->type != EXP_INTEGER) al = make_variant(env,e,left->u.appl.args[i],rest,al);
            }
        }
    } else {
        c = _th_get_coef(env,left);
        if (_th_big_is_negative(c->u.integer)) {
            t = _th_get_core(env,left);
            rest = diff_except(env,left,right,left);
            t = _th_build_term(env,_ex_intern_integer(_th_complement(c->u.integer)),t);
            if (rest==NULL) rest = _ex_intern_small_integer(0);
            if (t->type != EXP_INTEGER) al = make_variant(env,e,rest,t,al);
        } else {
            rest = diff_except(env,right,left,left);
            if (left->type != EXP_INTEGER) al = make_variant(env,e,left,rest,al);
        }
    }

    if (right->type==EXP_APPL && right->u.appl.functor==INTERN_NAT_PLUS) {
        for (i = 0; i < right->u.appl.count; ++i) {
            c = _th_get_coef(env,right->u.appl.args[i]);
            if (_th_big_is_negative(c->u.integer)) {
                t = _th_get_core(env,right->u.appl.args[i]);
                rest = diff_except(env,right,left,right->u.appl.args[i]);
                t = _th_build_term(env,_ex_intern_integer(_th_complement(c->u.integer)),t);
                if (rest==NULL) rest = _ex_intern_small_integer(0);
                if (t->type != EXP_INTEGER) al = make_variant(env,e,t,rest,al);
            } else {
                rest = diff_except(env,left,right,right->u.appl.args[i]);
                if (right->u.appl.args[i]->type != EXP_INTEGER) al = make_variant(env,e,rest,right->u.appl.args[i],al);
            }
        }
    } else {
        c = _th_get_coef(env,right);
        if (_th_big_is_negative(c->u.integer)) {
            t = _th_get_core(env,right);
            rest = diff_except(env,right,left,right);
            t = _th_build_term(env,_ex_intern_integer(_th_complement(c->u.integer)),t);
            if (rest==NULL) rest = _ex_intern_small_integer(0);
            if (t->type != EXP_INTEGER) al = make_variant(env,e,t,rest,al);
        } else {
            rest = diff_except(env,left,right,right);
            if (right->type != EXP_INTEGER) al = make_variant(env,e,rest,right,al);
        }
    }

    l = al;
    while (l != NULL) {
        _zone_print_exp("trans", l->e);
        l = l->next;
    }
    
    _tree_undent();
    return al;
}

#ifdef XX
int has_var;

int can_solve_for(struct env *env, struct _ex_intern *var, struct _ex_intern *rhs)
{
}

int _th_can_solve_for(struct env *env, struct _ex_intern *var, struct _ex_intern *rhs)
{
    if (rhs->type!=EXP_APPL || (rhs->u.appl.functor!=INTERN_NAT_PLUS &&
        rhs->u.appl.functor!=INTERN_RAT_PLUS && rhs->u.appl.functor!=INTERN_NAT_TIMES &&
        rhs->u.appl.functor!=INTERN_RAT_TIMES && rhs->u.appl.functor!=INTERN_NAT_DIVIDE &&
        rhs->u.appl.functor!=INTERN_RAT_DIVIDE) {
        return 0;
    }
    if (var->type==EXP_APPL || (rhs->u.appl.functor!=INTERN_NAT_PLUS &&
        var->u.appl.functor!=INTERN_RAT_PLUS && rhs->u.appl.functor!=INTERN_NAT_TIMES &&
        var->u.appl.functor!=INTERN_RAT_TIMES && rhs->u.appl.functor!=INTERN_NAT_DIVIDE &&
        var->u.appl.functor!=INTERN_RAT_DIVIDE) {
        return 0;
    }

    has_var = 0;
    return can_solve_for(env, var, rhs) && has_var;
}
#endif
