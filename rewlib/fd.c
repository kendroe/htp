/*
 * fd.c
 *
 * Implementation of an FD constraint solver (similar to what is in gprolog).
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>

#include "Intern.h"
#include "Globals.h"

struct range_list {
	struct range_list *next;
	struct _ex_intern *low, *high;
};

#define RANGE_MIN_MAX   1
#define RANGE_BITS      2
#define RANGE_FRAGMENTS 3
#define RANGE_FILLED    4
#define RANGE_NONE      5

struct variable_info {
	unsigned var;
	int effects_count;
	int *effects_var;
	int *effects_constraint;
	int range_type;
	union {
        struct r {
			struct _ex_intern *min;
			struct _ex_intern *max;
		} range;
		struct b {
			struct _ex_intern *base;
			unsigned bits;
		} bits;
		struct range_list *fragments;

	} u;
};

struct constraint_info {
	struct _ex_intern *constraint;
	int is_delayed;
	int needs_propagation;
	unsigned assign_var;
	int assign_index;
	int var_count;
	int *vars;
};

struct fd_handle {
	struct fd_handle *next;
	int var_count;
	struct variable_info *vars;
	int constraint_count;
	struct constraint_info *constraints;
};

static struct _ex_intern *new_na;
static struct _ex_intern *subexps;
static struct _ex_intern *reduce_one_var(struct env *env, struct _ex_intern *na, struct _ex_intern *exp)
{
	struct _ex_intern **args, *e, *v;
	unsigned *used, var1, var2;
	int i, j, count;
	unsigned *fv;

	//printf("Reduce one var %s\n", _th_print_exp(exp));
	//printf("na = %s\n", _th_print_exp(na));
    //fflush(stdout);

	used = (int *)ALLOCA(sizeof(int) * exp->u.appl.count);
	args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count);
	for (i =0; i < exp->u.appl.count; ++i) {
		used[i] = 0;
	}
	var1 = var2 = 0;
	for (i = 0, j = 0; i < exp->u.appl.count; ++i) {
		fv = _th_get_free_vars(exp->u.appl.args[i], &count);
		if (count > 0) {
		    if (fv[0]==var1 || fv[0]==var2) {
			    args[j++] = exp->u.appl.args[i];
				used[i] = 1;
			} else if (var1==0) {
				args[j++] = exp->u.appl.args[i];
				used[i] = 1;
				var1 = fv[0];
			} else if (var2==0) {
				args[j++] = exp->u.appl.args[i];
				used[i] = 1;
				var2 = fv[0];
			}
		}
	}
	e = _ex_intern_appl_env(env,exp->u.appl.functor,j,args);
	v = _ex_intern_var(_th_name_away(na,INTERN_V));
	for (i = 0, j = 0; i < exp->u.appl.count; ++i) {
		if (!used[i]) {
			args[j++] = exp->u.appl.args[i];
		}
	}
	args[j++] = v;
	new_na = _ex_intern_appl2_env(env, INTERN_TUPLE,v,na);
	e = _ex_intern_appl2_env(env,INTERN_EQUAL,e,v);
	_zone_print_exp("New variable introduction", e);
	if (subexps) {
		subexps = _th_flatten(env,_ex_intern_appl2_env(env,INTERN_AND,e,subexps));
	} else {
		subexps = e;
	}
	return _ex_intern_appl_env(env,exp->u.appl.functor,j,args);
}

static struct _ex_intern *split_side(struct env *env, struct _ex_intern *na, struct _ex_intern *exp)
{
	unsigned *fv;
	int i, count;
    struct _ex_intern **args, *e, *f;

	fv = _th_get_free_vars(exp, &count);
	if (count < 2) return exp;

	if (exp->type==EXP_APPL && _th_is_ac(env,exp->u.appl.functor)) {
		args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count);
		for (i = 0; i < exp->u.appl.count; ++i) {
            e = exp->u.appl.args[i];
			f = split_side(env,na,e);
			na = new_na;
			args[i] = f;
		}
		exp = _ex_intern_appl_env(env,exp->u.appl.functor,exp->u.appl.count,args);
		fv = _th_get_free_vars(exp, &count);
		//na = exp;
		while (count > 2) {
		    exp = reduce_one_var(env,na,exp);
     		fv = _th_get_free_vars(exp, &count);
			na = new_na;
		}
		return exp;
	} else {
		new_na = na;
		return exp;
	}
}

static struct _ex_intern *break_equation(struct env *env, struct _ex_intern *na, struct _ex_intern *exp)
{
	unsigned *fv;
	int count;
    struct _ex_intern *lhs, *rhs, *o;

	//printf("break_equation: %s\n", _th_print_exp(exp));
    //fflush(stdout);

	new_na = na;
	fv = _th_get_free_vars(exp, &count);
	if (count < 4) return exp;

	if (exp->type==EXP_APPL) {
		switch (exp->u.appl.functor) {
		    case INTERN_EQUAL:
			case INTERN_NAT_LESS:
				lhs = exp->u.appl.args[0];
				rhs = exp->u.appl.args[1];
				break;
			case INTERN_NOT:
				if (exp->u.appl.args[0]->type==EXP_APPL) {
					switch (exp->u.appl.args[0]->u.appl.functor) {
					    case INTERN_EQUAL:
                        case INTERN_NAT_LESS:
							lhs = exp->u.appl.args[0]->u.appl.args[0];
							rhs = exp->u.appl.args[0]->u.appl.args[1];
							break;
						default:
							return exp;
					}
				} else {
					return exp;
				}
				break;
			default:
				return exp;
		}
	} else {
		return exp;
	}
	o = subexps;
	lhs = split_side(env,na,lhs);
	rhs = split_side(env,new_na,rhs);
    if (subexps==o) return exp;

	switch (exp->u.appl.functor) {
	    case INTERN_EQUAL:
		case INTERN_NAT_LESS:
			return _ex_intern_appl2_env(env,exp->u.appl.functor,lhs,rhs);
		case INTERN_NOT:
			return _ex_intern_appl1_env(env,INTERN_NOT,
				       _ex_intern_appl2_env(env,exp->u.appl.args[0]->u.appl.functor,lhs,rhs));
		default:
			fprintf(stderr, "break_equation: internal error\n");
			exit(1);
	}
}

static int min_max_times(struct env *env, struct _ex_intern *e)
{
	unsigned var;
	int i;
    struct _ex_intern *f;

	printf("min_max_times %s\n", _th_print_exp(e));

	var = 0;
	for (i = 0; i < e->u.appl.count; ++i) {
		f = e->u.appl.args[i];
		if (f->type != EXP_INTEGER) {
			if (f->type==EXP_VAR) {
				if (var==0) {
					var = f->u.var;
				} else if (f->u.var != var) {
					return 0;
				}
			} else {
				return 0;
			}
		}
	}

	printf("good\n");

	return 1;
}

static int min_max_mvar_times(struct env *env, struct _ex_intern *e)
{
	int i;
    struct _ex_intern *f;

	for (i = 0; i < e->u.appl.count; ++i) {
		f = e->u.appl.args[i];
		if (f->type != EXP_INTEGER && f->type != EXP_VAR) {
			return 0;
		}
	}

	return 1;
}

static int min_max_divide(struct env *env, struct _ex_intern *e);

static int min_max_plus(struct env *env, struct _ex_intern *e)
{
    int i;
	printf("Checking min_max_plus %s\n", _th_print_exp(e));
	for (i = 0; i < e->u.appl.count; ++i) {
		struct _ex_intern *f = e->u.appl.args[i];
	    if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NAT_TIMES) {
			if (!min_max_times(env, f)) return 0;
		} else if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NAT_DIVIDE) {
			if (!min_max_divide(env, f)) return 0;
		} else if (f->type!=EXP_VAR && f->type!=EXP_INTEGER) {
			return 0;
		}
	}
	printf("Good\n");
    return 1;
}

static int min_max_divide(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *n = e->u.appl.args[0];
	struct _ex_intern *d = e->u.appl.args[1];

	if (n->type==EXP_APPL && n->u.appl.functor==INTERN_NAT_PLUS) {
		return min_max_plus(env, n);
	} else if (n->type==EXP_APPL && n->u.appl.functor==INTERN_NAT_TIMES) {
		return min_max_mvar_times(env, d);
	} else if (n->type != EXP_VAR && n->type != EXP_INTEGER) {
		return 0;
	}

	if (d->type==EXP_APPL && d->u.appl.functor==INTERN_NAT_PLUS) {
		return min_max_plus(env, d);
	} else if (d->type==EXP_APPL && d->u.appl.functor==INTERN_NAT_TIMES) {
		return min_max_mvar_times(env, d);
	} else if (d->type != EXP_VAR && d->type != EXP_INTEGER) {
		return 0;
	}

	return 1;
}

static int min_max_form(struct env *env, unsigned var, struct _ex_intern *e)
{
	struct _ex_intern *rhs;

	printf("Checking form %s\n", _th_print_exp(e));
	printf("var = %s\n", _th_intern_decode(var));

	if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT && e->u.appl.args[0]->type==EXP_APPL &&
		e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_NAT_LESS) {
		e = e->u.appl.args[0];
	}

	if (e->type != EXP_APPL ||
		(e->u.appl.functor != INTERN_EQUAL && e->u.appl.functor != INTERN_NAT_LESS &&
		 e->u.appl.functor != INTERN_ORIENTED_RULE)) return 0;

	if (e->u.appl.args[0]->type==EXP_VAR && e->u.appl.args[0]->u.var==var) {
		rhs = e->u.appl.args[1];
		if (_th_is_free_in(rhs,var)) return 0;
	} else if (e->u.appl.args[1]->type==EXP_VAR && e->u.appl.args[1]->u.var==var) {
		rhs = e->u.appl.args[0];
		if (_th_is_free_in(rhs,var)) return 0;
	} else {
		return 0;
	}

	printf("rhs = %s\n", _th_print_exp(rhs));

	if (rhs->type==EXP_APPL && rhs->u.appl.functor==INTERN_NAT_PLUS) {
		return min_max_plus(env, rhs);
	} else if (rhs->type==EXP_APPL && rhs->u.appl.functor==INTERN_NAT_TIMES) {
		return min_max_mvar_times(env, rhs);
	} else if (rhs->type==EXP_APPL && rhs->u.appl.functor==INTERN_NAT_DIVIDE) {
		return min_max_divide(env, rhs);
	} else if (rhs->type != EXP_VAR && rhs->type != EXP_INTEGER) {
		return 0;
	} else {
		return 1;
	}
}

static struct _ex_intern *generate_constraint_for_var(struct env *env,
													  unsigned var,
													  struct _ex_intern *e)
{
	struct _ex_intern *f;
	f = _th_linear_solve(env,var,e);
	if (f != NULL) {
        e = _th_rewrite(env,f);
	}
	return e;
}

struct _ex_intern *_th_get_min(struct env *env, struct _ex_intern *context_rules, struct _ex_intern *exp, unsigned var)
{
    struct _ex_intern *f, *min;
    int i;

    min = NULL;

    for (i = 0; i < context_rules->u.appl.count; ++i) {
        f = context_rules->u.appl.args[i];
        //_zone_print2("Free finite %s %s", _th_intern_decode(var), _th_print_exp(context_rules->u.appl.args[i]));
        //_zone_print_exp("term", f);
        if (f->u.appl.args[2]==_ex_true) {
            if (f->u.appl.args[1]==_ex_true) {
                f = f->u.appl.args[0];
                if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NAT_LESS) {
                    if (f->u.appl.args[1]->type==EXP_MARKED_VAR && f->u.appl.args[1]->u.var==var && min==NULL) {
                        min = f->u.appl.args[0];
                        if (min->type==EXP_INTEGER) {
                            min = _th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,min,_ex_intern_small_integer(1)),1);
                        } else {
                            min = NULL;
                        }
                    }
                }
            }
            if (f->u.appl.args[1]==_ex_false) {
                f = f->u.appl.args[0];
                if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NAT_LESS) {
                    if (f->u.appl.args[0]->type==EXP_MARKED_VAR && f->u.appl.args[0]->u.var==var && min==NULL) {
                        min = f->u.appl.args[1];
                        if (min->type != EXP_INTEGER) min = NULL;
                    }
                }
            }
        }
    }

    if (min || exp->type != EXP_APPL || exp->u.appl.functor != INTERN_AND) return min;

    for (i = 0; i < exp->u.appl.count; ++i) {
        f = exp->u.appl.args[i];
        //_zone_print_exp("term", f);
        if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NAT_LESS) {
            if (f->u.appl.args[1]->type==EXP_VAR && f->u.appl.args[1]->u.var==var && min==NULL) {
                min = _th_trans_constant(exp,0,f->u.appl.args[0], 0, NULL);
				if (min) {
                    min = _th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,min,_ex_intern_small_integer(1)),1);
                    if (min->type != EXP_INTEGER) min = NULL;
				}
            }
        }
        if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NOT) {
            f = f->u.appl.args[0];
            if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NAT_LESS) {
                if (f->u.appl.args[0]->type==EXP_VAR && f->u.appl.args[0]->u.var==var && min==NULL) {
                    min = _th_trans_constant(exp,0,f->u.appl.args[1], 0, NULL);
                    if (min && min->type != EXP_INTEGER) min = NULL;
                }
            }
        }
        //_zone_print2("free3 %d %d", min, max);
        //_zone_print2("in_set[%d] = %d", j, in_set[j]);
    }

    return min;
}

struct _ex_intern *_th_get_max(struct env *env, struct _ex_intern *context_rules, struct _ex_intern *exp, unsigned var)
{
    struct _ex_intern *f, *max;
    int i;

    max = NULL;

    for (i = 0; i < context_rules->u.appl.count; ++i) {
        f = context_rules->u.appl.args[i];
        //_zone_print2("Free finite %s %s", _th_intern_decode(var), _th_print_exp(context_rules->u.appl.args[i]));
        //_zone_print_exp("term", f);
        if (f->u.appl.args[2]==_ex_true) {
            if (f->u.appl.args[1]==_ex_true) {
                f = f->u.appl.args[0];
                if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NAT_LESS) {
                    if (f->u.appl.args[0]->type==EXP_MARKED_VAR && f->u.appl.args[0]->u.var==var && max==NULL) {
                        max = f->u.appl.args[1];
                        if (max->type==EXP_INTEGER) {
                            max = _th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_MINUS,max,_ex_intern_small_integer(1)),1);
                        } else {
                            max = NULL;
                        }
                    }
                }
            }
            if (f->u.appl.args[1]==_ex_false) {
                f = f->u.appl.args[0];
                if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NAT_LESS) {
                    if (f->u.appl.args[1]->type==EXP_MARKED_VAR && f->u.appl.args[1]->u.var==var && max==NULL) {
                        max = f->u.appl.args[0];
                        if (max->type != EXP_INTEGER) max = NULL;
                    }
                }
            }
        }
        //_zone_print2("free3 %d %d", min, max);
        //_zone_print2("in_set[%d] = %d", j, in_set[j]);
    }

    if (max || exp->type != EXP_APPL || exp->u.appl.functor != INTERN_AND) return max;

    for (i = 0; i < exp->u.appl.count; ++i) {
        f = exp->u.appl.args[i];
        //_zone_print_exp("term", f);
        if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NAT_LESS) {
            if (f->u.appl.args[0]->type==EXP_VAR && f->u.appl.args[0]->u.var==var && max==NULL) {
                max = _th_trans_constant(exp,1,f->u.appl.args[1], 0, NULL);
				if (max) {
                    max = _th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_MINUS,max,_ex_intern_small_integer(1)),1);
                    if (max->type != EXP_INTEGER) max = NULL;
				}
            }
        }
        if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NOT) {
            f = f->u.appl.args[0];
            if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NAT_LESS) {
                if (f->u.appl.args[1]->type==EXP_VAR && f->u.appl.args[1]->u.var==var && max==NULL) {
                    max = _th_trans_constant(exp,1,f->u.appl.args[0], 0, NULL);
                    if (max && max->type != EXP_INTEGER) max = NULL;
                }
            }
        }
        //_zone_print2("free3 %d %d", min, max);
        //_zone_print2("in_set[%d] = %d", j, in_set[j]);
    }

    return max;
}

static struct _ex_intern *add_small(struct _ex_intern *e, int offset)
{
	unsigned n[2];

	n[0] = 1;
	n[1] = (unsigned)offset;

    return _ex_intern_integer(_th_big_add(n,e->u.integer));
}

static int small_bit(unsigned n)
{
	int count;

	if (n==0) {
		printf("Internal error: small_bit: illegal value\n");
		exit(1);
	}

	count = 0;

	while (n&1==0) {
		n = (n>>1);
		++count;
	}

	return count;
}

static int large_bit(unsigned n)
{
	int count;

	if (n==0) {
		printf("Internal error: large_bit: illegal value\n");
		exit(1);
	}

	count = 0;

	while (n) {
		n = (n>>1);
		++count;
	}

	return --count;
}

static struct _ex_intern *min_value(struct fd_handle *fd, unsigned var)
{
	int i;

	for (i = 0; i < fd->var_count; ++i) {
		if (fd->vars[i].var==var) {
			switch (fd->vars[i].range_type) {
			    case RANGE_MIN_MAX:
				case RANGE_FILLED:
					return fd->vars[i].u.range.min;
				case RANGE_BITS:
					return add_small(fd->vars[i].u.bits.base,small_bit(fd->vars[i].u.bits.bits));
				case RANGE_FRAGMENTS:
					return fd->vars[i].u.fragments->low;
				case RANGE_NONE:
					return NULL;
				default:
					fprintf(stderr, "Internal error: min_value: Illegal range type\n");
					exit(1);
			}
		}
	}
	fprintf(stderr, "Internal error: min_value: variable not found\n");
	exit(1);
}

static struct _ex_intern *max_value(struct fd_handle *fd, unsigned var)
{
	int i;
    struct range_list *r;

	for (i = 0; i < fd->var_count; ++i) {
		if (fd->vars[i].var==var) {
			switch (fd->vars[i].range_type) {
     			case RANGE_NONE:
	     			return NULL;
			    case RANGE_MIN_MAX:
					return fd->vars[i].u.range.max;
				case RANGE_FILLED:
					return fd->vars[i].u.range.min;
				case RANGE_BITS:
					return add_small(fd->vars[i].u.bits.base,large_bit(fd->vars[i].u.bits.bits));
				case RANGE_FRAGMENTS:
					r = fd->vars[i].u.fragments;
					while (r->next != NULL) {
						r = r->next;
					}
					return r->high;
				default:
					fprintf(stderr, "Internal error: max_value: Illegal range type\n");
					exit(1);
			}
		}
	}
	fprintf(stderr, "Internal error: min_value: variable not found\n");
	exit(1);
}

static struct _ex_intern *add_values(struct _ex_intern *a, struct _ex_intern *b)
{
	return _ex_intern_integer(_th_big_add(a->u.integer,b->u.integer));
}

static struct _ex_intern *res_min, *res_max;
static void multiply_ranges(struct env *env, struct _ex_intern *min1, struct _ex_intern *min2, struct _ex_intern *max1, struct _ex_intern *max2)
{
	static struct _ex_intern *zero = NULL;

	if (zero==NULL) zero = _ex_intern_small_integer(0);

	_zone_print0("multiply ranges");
	_tree_indent();
	_zone_print_exp("min1 =", min1);
	_zone_print_exp("max1 =", max1);
	_zone_print_exp("min2 =", min2);
	_zone_print_exp("max2 =", max2);
    _tree_undent();

	if ((min1==zero && max1==zero) || (min2==zero && max2==zero)) {
		res_min = res_max = zero;
	} else if (min2==NULL && max2==NULL) {
		res_min = res_max = NULL;
	} else if (min1==NULL) {
		if (max1==NULL) {
			res_min = res_max = NULL;
		} else if (_th_big_is_negative(max1->u.integer)) {
			if (min2==NULL) {
				if (_th_big_is_negative(max2->u.integer)) {
					res_max = NULL;
					res_min = _ex_intern_integer(_th_big_multiply(max1->u.integer,max2->u.integer));
				} else {
					res_min = res_max = NULL;
				}
			} else if (_th_big_is_negative(min2->u.integer)) {
				if (max2==zero || _th_big_is_negative(max2->u.integer)) {
					res_max = NULL;
					res_min = _ex_intern_integer(_th_big_multiply(max1->u.integer,max2->u.integer));
				} else {
					res_min = res_max = NULL;
				}
			}
		} else {
			if (min2==NULL || max2==NULL) {
				res_min = res_max = NULL;
			} else if (_th_big_is_negative(min2->u.integer) && _th_big_is_negative(max2->u.integer)) {
				res_max = NULL;
				res_min = _ex_intern_integer(_th_big_multiply(min2->u.integer,max1->u.integer));
			} else if (!_th_big_is_negative(min2->u.integer) && !_th_big_is_negative(max2->u.integer)) {
				res_min = NULL;
				res_max = _ex_intern_integer(_th_big_multiply(max1->u.integer,max2->u.integer));
			} else {
				res_min = res_max = NULL;
			}
		}
	} else if (_th_big_is_negative(min1->u.integer)) {
		if (max1==NULL) {
			if (min2==NULL || max2==NULL) {
				res_min = res_max = NULL;
			} else if (_th_big_is_negative(min2->u.integer) && _th_big_is_negative(max2->u.integer)) {
				res_min = NULL;
				res_max = _ex_intern_integer(_th_big_multiply(min2->u.integer,min1->u.integer));
			} else if (!_th_big_is_negative(min2->u.integer) && !_th_big_is_negative(max2->u.integer)) {
				res_max = NULL;
				res_min = _ex_intern_integer(_th_big_multiply(min1->u.integer,max2->u.integer));
			} else {
				res_min = res_max = NULL;
			}
		} else if (_th_big_is_negative(max1->u.integer)) {
			if (min2 != NULL) {
				if (_th_big_is_negative(min2->u.integer)) {
					res_max = _ex_intern_integer(_th_big_multiply(min2->u.integer,max1->u.integer));
				} else {
					res_max = _ex_intern_integer(_th_big_multiply(min2->u.integer,min1->u.integer));
				}
			} else {
				res_max = NULL;
			}
			if (max2 != NULL) {
				if (_th_big_is_negative(max2->u.integer)) {
					res_min = _ex_intern_integer(_th_big_multiply(max2->u.integer,min1->u.integer));
				} else {
					res_min = _ex_intern_integer(_th_big_multiply(max2->u.integer,max1->u.integer));
				}
			} else {
				res_min = NULL;
			}
		} else {
			if (min2==NULL || max2==NULL) {
				res_min = res_max = NULL;
			} else {
				if (_th_big_is_negative(min2->u.integer)) {
					if (_th_big_is_negative(max2->u.integer)) {
						res_min = _ex_intern_integer(_th_big_multiply(max1->u.integer,min2->u.integer));
						res_max = _ex_intern_integer(_th_big_multiply(min1->u.integer,min2->u.integer));
					} else {
						struct _ex_intern *c1, *c2;
						c1 = _ex_intern_integer(_th_big_multiply(max1->u.integer,max2->u.integer));
						c2 = _ex_intern_integer(_th_big_multiply(min1->u.integer,min2->u.integer));
						if (_th_big_less(c1->u.integer,c2->u.integer)) {
							res_max = c2;
						} else {
							res_max = c1;
						}
						c1 = _ex_intern_integer(_th_big_multiply(max1->u.integer,min2->u.integer));
						c2 = _ex_intern_integer(_th_big_multiply(min1->u.integer,max2->u.integer));
						if (_th_big_less(c1->u.integer,c2->u.integer)) {
							res_min = c1;
						} else {
							res_min = c2;
						}
					}
				} else {
					res_min = _ex_intern_integer(_th_big_multiply(min1->u.integer,max2->u.integer));
					res_max = _ex_intern_integer(_th_big_multiply(max1->u.integer,max2->u.integer));
				}
			}
		}
	} else {
		if (max1==NULL) {
			if (min2 != NULL) {
				if (max2 != NULL) {
					if (_th_big_is_negative(min2->u.integer) && _th_big_is_negative(max2->u.integer)) {
						res_max = _ex_intern_integer(_th_big_multiply(min2->u.integer,min1->u.integer));
						res_min = NULL;
					} else if (!_th_big_is_negative(min2->u.integer) && !_th_big_is_negative(max2->u.integer)) {
						res_max = NULL;
						res_min = _ex_intern_integer(_th_big_multiply(min2->u.integer,min1->u.integer));
					} else {
						res_min = res_max = NULL;
					}
				} else {
					if (_th_big_is_negative(min2->u.integer)) {
						res_min = res_max = NULL;
					} else {
					    res_min = _ex_intern_integer(_th_big_multiply(min2->u.integer,min1->u.integer));
                        res_max = NULL;
					}
				}
			} else {
				if (!_th_big_is_negative(max2->u.integer)) {
					res_min = res_max = NULL;
				} else {
				    res_max = _ex_intern_integer(_th_big_multiply(max2->u.integer,min1->u.integer));
					res_min = NULL;
				}
			}
		} else {
			if (min2 != NULL) {
				if (_th_big_is_negative(min2->u.integer)) {
					res_min = _ex_intern_integer(_th_big_multiply(min2->u.integer,max1->u.integer));
				} else {
					res_min = _ex_intern_integer(_th_big_multiply(min2->u.integer,min1->u.integer));
				}
			}
			if (max2 != NULL) {
				if (_th_big_is_negative(max2->u.integer)) {
					res_max = _ex_intern_integer(_th_big_multiply(max2->u.integer,min1->u.integer));
				} else {
					res_max = _ex_intern_integer(_th_big_multiply(max2->u.integer,max1->u.integer));
				}
			}
		}
	}
}

static void divide_ranges(struct env *env, struct _ex_intern *min1, struct _ex_intern *max1, struct _ex_intern *min2, struct _ex_intern *max2)
{
	static struct _ex_intern *zero = NULL;

	if (zero==NULL) zero = _ex_intern_small_integer(0);

	_zone_print_exp("divide min1", min1);
	_zone_print_exp("divide max1", max1);
	_zone_print_exp("divide min2", min2);
	_zone_print_exp("divide max2", max2);

    if (max2 != NULL && _th_big_is_negative(max2->u.integer) && (min2==NULL || _th_big_is_negative(min2->u.integer))) {
		if (min1==NULL) {
			res_max = NULL;
		} else {
		    res_max = _ex_intern_integer(_th_big_divide(min1->u.integer, max2->u.integer));
		}
		if (max1==NULL) {
			res_min = NULL;
		} else {
		    res_min = _ex_intern_integer(_th_big_divide(max1->u.integer, max2->u.integer));
		}
	} else if (min2 != NULL && !_th_big_is_negative(min2->u.integer) && min2 != zero) {
		if (min1==NULL) {
			res_min = NULL;
		} else {
		    res_min = _ex_intern_integer(_th_big_divide(min1->u.integer, min2->u.integer));
		}
		if (max1==NULL) {
			res_max = NULL;
		} else {
		    res_max = _ex_intern_integer(_th_big_divide(max1->u.integer, min2->u.integer));
		}
	} else {
		res_min = min1;
		res_max = max1;
	}
}

static struct _ex_intern *compute_max(struct env *env, struct fd_handle *fd, struct _ex_intern *e);

static struct _ex_intern *compute_min(struct env *env, struct fd_handle *fd, struct _ex_intern *e)
{
	struct _ex_intern *total, *r, *rm, *total_max;
	int i;

	switch (e->type) {
	    case EXP_INTEGER:
			return e;
		case EXP_VAR:
			return min_value(fd, e->u.var);
		case EXP_APPL:
			switch (e->u.appl.functor) {
			    case INTERN_NAT_PLUS:
					_zone_print0("plus min");
					_tree_indent();
					total = compute_min(env,fd,e->u.appl.args[0]);
					_tree_undent();
					_zone_print1("total =", total);
					if (total==NULL) return NULL;
					for (i = 1; i < e->u.appl.count; ++i) {
						_tree_indent();
						r = compute_min(env,fd,e->u.appl.args[i]);
						_tree_undent();
						_zone_print_exp("r =", r);
						if (r==NULL) return NULL;
						total = add_values(total, r);
					}
					return total;
				case INTERN_NAT_TIMES:
					_zone_print0("times min");
					_tree_indent();
					total = compute_min(env,fd,e->u.appl.args[0]);
					total_max = compute_max(env,fd,e->u.appl.args[0]);
					_tree_undent();
					_zone_print_exp("total =", total);
					_zone_print_exp("total_max =", total_max);
					for (i = 1; i < e->u.appl.count; ++i) {
						if (total==NULL && total_max==NULL) return NULL;
						_tree_indent();
						r = compute_min(env,fd,e->u.appl.args[i]);
						rm = compute_max(env,fd,e->u.appl.args[i]);
						_tree_undent();
						_zone_print_exp("r =", r);
						_zone_print_exp("rm =", rm);
						multiply_ranges(env,r,total,rm,total_max);
						_zone_print_exp("res_min =", res_min);
						_zone_print_exp("res_max =", res_max);
						total = res_min;
						total_max = res_max;
					}
					return total;
				case INTERN_NAT_DIVIDE:
					_zone_print0("divide");
					_tree_indent();
					divide_ranges(env,compute_min(env,fd,e->u.appl.args[0]),
						              compute_max(env,fd,e->u.appl.args[0]),
						              compute_min(env,fd,e->u.appl.args[1]),
						              compute_max(env,fd,e->u.appl.args[1]));
					_tree_undent();
					return res_min;
				default:
					return NULL;
			}
		default:
			return NULL;
	}
}

static struct _ex_intern *compute_max(struct env *env, struct fd_handle *fd, struct _ex_intern *e)
{
	struct _ex_intern *total, *r, *rm, *total_max;
	int i;

	switch (e->type) {
	    case EXP_INTEGER:
			return e;
		case EXP_VAR:
			return max_value(fd, e->u.var);
		case EXP_APPL:
			switch (e->u.appl.functor) {
			    case INTERN_NAT_PLUS:
					_zone_print0("plus max");
					_tree_indent();
					total = compute_max(env,fd,e->u.appl.args[0]);
					_tree_undent();
					_zone_print_exp("total =", total);
					if (total==NULL) return NULL;
					for (i = 1; i < e->u.appl.count; ++i) {
						_tree_indent();
						r = compute_max(env,fd,e->u.appl.args[i]);
						_tree_undent();
						_zone_print_exp("r =", r);
						if (r==NULL) return NULL;
						total = add_values(total, r);
					}
					return total;
				case INTERN_NAT_TIMES:
					_zone_print0("compute times max");
					_tree_indent();
					total = compute_min(env,fd,e->u.appl.args[0]);
					total_max = compute_max(env,fd,e->u.appl.args[0]);
					_tree_undent();
					_zone_print_exp("total =", total);
					_zone_print_exp("total_max =", total_max);
					for (i = 1; i < e->u.appl.count; ++i) {
						if (total==NULL && total_max==NULL) return NULL;
						_tree_indent();
						r = compute_min(env,fd,e->u.appl.args[i]);
						rm = compute_max(env,fd,e->u.appl.args[i]);
						_tree_undent();
						_zone_print_exp("r =", r);
						_zone_print_exp("rm ", rm);
						multiply_ranges(env,r,total,rm,total_max);
						_zone_print_exp("res_min =", res_min);
						_zone_print_exp("res_max =", res_max);
						total = res_min;
						total_max = res_max;
					}
					return total_max;
				case INTERN_NAT_DIVIDE:
					_zone_print0("divide_ranges max");
					_tree_indent();
					divide_ranges(env,compute_min(env,fd,e->u.appl.args[0]),
						              compute_max(env,fd,e->u.appl.args[0]),
						              compute_min(env,fd,e->u.appl.args[1]),
						              compute_max(env,fd,e->u.appl.args[1]));
					_tree_undent();
					return res_max;
				default:
					return NULL;
			}
		default:
			return NULL;
	}
}

static unsigned bit_mask[33] = {
    0x1, 0x3, 0x7, 0xf, 0x1f, 0x3f, 0x7f, 0xff,
    0x1ff, 0x3ff, 0x7ff, 0xfff, 0x1fff, 0x3fff, 0x7fff, 0xffff,
	0x1ffff, 0x3ffff, 0x7ffff, 0xfffff, 0x1fffff, 0x3fffff, 0x7fffff, 0xffffff,
	0x1ffffff, 0x3ffffff, 0x7ffffff, 0xfffffff, 0x1fffffff, 0x3fffffff, 0x7fffffff,0xffffffff };

static int restrict_range(struct variable_info *info, struct _ex_intern *min, struct _ex_intern *max)
{
	struct range_list *f;
    static unsigned increment[2] = { 1, 32 };
    int range_changed = 0;
	unsigned *diff;

	switch (info->range_type) {
	    case RANGE_NONE:
			return 0;
	    case RANGE_FILLED:
			if ((min==NULL || (info->u.range.min != NULL && !_th_big_less(info->u.range.min->u.integer,min->u.integer))) &&
				(max==NULL || (info->u.range.max != NULL && !_th_big_less(max->u.integer,info->u.range.min->u.integer)))) {
				return 0;
			} else {
				info->range_type = RANGE_NONE;
				return 1;
			}
		case RANGE_MIN_MAX:
			if ((max != NULL && info->u.range.min != NULL && _th_big_less(max->u.integer,info->u.range.min->u.integer)) ||
				(min != NULL && info->u.range.max != NULL && _th_big_less(info->u.range.max->u.integer,min->u.integer))) {
				info->range_type = RANGE_NONE;
				return 1;
			} else {
				if (min != NULL && (info->u.range.min==NULL || _th_big_less(info->u.range.min->u.integer,min->u.integer))) {
					info->u.range.min = min;
					range_changed = 1;
				}
				if (max != NULL && (info->u.range.max==NULL || _th_big_less(max->u.integer,info->u.range.max->u.integer))) {
					info->u.range.max = max;
					range_changed = 1;
				}
				if (info->u.range.min != NULL && info->u.range.min==info->u.range.max) {
					info->range_type = RANGE_FILLED;
				}
				return range_changed;
			}
		case RANGE_FRAGMENTS:
            f = info->u.fragments;
			while (f != NULL && min != NULL && f->high != NULL && _th_big_less(f->high->u.integer,min->u.integer)) {
				range_changed = 1;
			    f = f->next;
			}
			if (f==NULL) {
				info->range_type = RANGE_NONE;
				return range_changed;
			}
			if (max==NULL || !_th_big_less(f->high->u.integer,max->u.integer)) {
				info->range_type = RANGE_MIN_MAX;
				info->u.range.min = f->low;
				info->u.range.max = max;
				return 1;
			}
			if (f->next==NULL || (max != NULL && _th_big_less(max->u.integer,f->next->low->u.integer))) {
				info->range_type = RANGE_MIN_MAX;
				info->u.range.min = f->low;
				info->u.range.max = f->high;
				return 1;
			}
			while (f->next != NULL && max != NULL && !_th_big_less(max->u.integer,f->next->low->u.integer)) {
				f = f->next;
			}
			if (f->next) range_changed = 1;
			f->next = NULL;
			if (max != NULL && (f->high==NULL || _th_big_less(max->u.integer,f->high->u.integer))) {
				range_changed = 1;
				f->high = max;
			}
			return range_changed;
		case RANGE_BITS:
			if (max != NULL && _th_big_less(max->u.integer,info->u.bits.base->u.integer)) {
				info->range_type = RANGE_NONE;
				return 1;
			}
			increment[1] = 32;
			if (min != NULL && !_th_big_less(min->u.integer,_th_big_add(info->u.bits.base->u.integer,increment))) {
				info->range_type = RANGE_NONE;
				return 1;
			}
			if (min!= NULL && !_th_big_less(min->u.integer,info->u.bits.base->u.integer)) {
				unsigned *r = _th_big_sub(min->u.integer,info->u.bits.base->u.integer);
                info->u.bits.bits >>= r[1];
				if (info->u.bits.bits==0) {
					info->range_type = RANGE_NONE;
					return 1;
				}
				range_changed = 1;
				increment[1] = 0;
				while ((info->u.bits.bits & 1)==0) {
					info->u.bits.bits >>= 1;
					++increment[1];
				}
			    info->u.bits.base = _ex_intern_integer(_th_big_add(info->u.bits.base->u.integer,increment));
			}
			if (max != NULL) {
				diff = _th_big_sub(max->u.integer,info->u.bits.base->u.integer);
			    if (diff[1]==1 && diff[2] < 31) {
				    unsigned m = info->u.bits.bits & bit_mask[diff[1]];
				    if (m != info->u.bits.bits) range_changed = 1;
				    info->u.bits.bits = m;
				}
			}
			return range_changed;
		default:
			fprintf(stderr, "Internal error: range_changed: Illegal range_type\n");
			exit(1);
	}
}

static int contains_value(struct variable_info *info, struct _ex_intern *value)
{
	struct range_list *f;

	switch (info->range_type) {
	    case RANGE_FILLED:
			return (info->u.range.min==value);
		case RANGE_NONE:
			return 0;
		case RANGE_MIN_MAX:
			return (info->u.range.min==NULL || !_th_big_less(value->u.integer,info->u.range.min->u.integer)) &&
				   (info->u.range.max==NULL || !_th_big_less(info->u.range.max->u.integer,value->u.integer));
		case RANGE_FRAGMENTS:
			f = info->u.fragments;
			while (f != NULL) {
			if ((f->low==NULL || !_th_big_less(value->u.integer,f->low->u.integer)) &&
				(f->high==NULL || !_th_big_less(f->high->u.integer,value->u.integer))) return 1;
                f = f->next;
			}
			return 0;
		case RANGE_BITS:
			if (_th_big_less(value->u.integer,info->u.bits.base->u.integer)) {
				return 0;
			} else {
				unsigned *d = _th_big_sub(value->u.integer,info->u.bits.base->u.integer);
				//_zone_print_exp("Contains", value);
				//_zone_print3("testing bits %x %d %x\n", info->u.bits.bits, d[1], (info->u.bits.bits>>d[1]));
				return d[0]==1 && d[1] < 32 && ((info->u.bits.bits>>d[1])&1);
			}
		default:
			fprintf(stderr, "contains_value: Internal error: Illegal range_type\n");
			exit(1);
	}
}

static int restrict_bits(struct variable_info *info, struct _ex_intern *base, unsigned bits)
{
	struct range_list *f;
    static unsigned increment[2] = { 1, 32 };
    int range_changed = 0;
	unsigned *d;
    unsigned disjunct, fbits;
	unsigned n;

	switch (info->range_type) {
	    case RANGE_FILLED:
			if (_th_big_less(info->u.range.min->u.integer,base->u.integer)) {
				info->range_type = RANGE_NONE;
				return 1;
			}
            d = _th_big_sub(info->u.range.min->u.integer,base->u.integer);
			if (d[0] != 1 || ((bits>>d[1])&1)==0) {
				info->range_type = RANGE_NONE;
				return 1;
			}
			return 0;
		case RANGE_NONE:
			return 0;
		case RANGE_MIN_MAX:
			if (info->u.range.max != NULL && _th_big_less(info->u.range.max->u.integer,base->u.integer)) {
				info->range_type = RANGE_NONE;
				return 1;
			}
			increment[1] = 32;
			if (info->u.range.min != NULL && !_th_big_less(info->u.range.min->u.integer,_th_big_add(base->u.integer,increment))) {
				info->range_type = RANGE_NONE;
				return 1;
			}
			if (info->u.range.min != NULL && !_th_big_less(info->u.range.min->u.integer,base->u.integer)) {
				unsigned *r = _th_big_sub(info->u.range.min->u.integer,base->u.integer);
                bits >>= r[1];
				if (bits==0) {
					info->range_type = RANGE_NONE;
					return 1;
				}
				increment[1] = 0;
				while ((bits & 1)==0) {
					bits >>= 1;
					++increment[1];
				}
			    base = _ex_intern_integer(_th_big_add(base->u.integer,increment));
			}
			if (info->u.range.max != NULL) {
			    d = _th_big_sub(info->u.range.max->u.integer,info->u.bits.base->u.integer);
			    if (d[1]==1 && d[2] < 31) {
				    bits = bits & bit_mask[d[1]];
				}
			}
			info->range_type = RANGE_BITS;
			info->u.bits.base = base;
			info->u.bits.bits = bits;
			if (info->u.bits.bits==0) {
				info->range_type = RANGE_NONE;
			}
			return 1;
		case RANGE_FRAGMENTS:
			f = info->u.fragments;
			disjunct = 0;
			while (f != NULL) {
				increment[1] = 32;
				if (f->high != NULL && _th_big_less(f->high->u.integer,base->u.integer)) {
					fbits = 0;
				} else if (f->low != NULL && !_th_big_less(f->low->u.integer,_th_big_add(base->u.integer,increment))) {
					fbits = 0;
				} else {
					fbits = bits;
					if (f->low != NULL && !_th_big_less(f->low->u.integer,base->u.integer)) {
						unsigned *r = _th_big_sub(f->low->u.integer,base->u.integer);
						fbits >>= r[1];
						fbits <<= r[1];
					}
					if (f->high != NULL) {
						d = _th_big_sub(f->high->u.integer,base->u.integer);
						if (d[1]==1 && d[2] < 31) {
							fbits = fbits & bit_mask[d[1]];
						}
					}
				}
				disjunct |= fbits;
				f = f->next;
			}
			if (disjunct==0) {
				info->range_type = RANGE_NONE;
				return 1;
			} else if (bits != disjunct) {
				range_changed = 1;
			}
			bits = disjunct;
			increment[1] = 0;
			while ((bits & 1)==0) {
				bits >>= 1;
				++increment[1];
			}
			base = _ex_intern_integer(_th_big_add(base->u.integer,increment));
			return range_changed;
		case RANGE_BITS:
			increment[0] = 31;
			if (_th_big_less(_th_big_add(info->u.bits.base->u.integer,increment),base->u.integer)) {
				info->range_type = RANGE_NONE;
				return 1;
			}
			if (_th_big_less(_th_big_add(base->u.integer,increment),info->u.bits.base->u.integer)) {
				info->range_type = RANGE_NONE;
				return 1;
			}
			if (_th_big_less(base->u.integer,info->u.bits.base->u.integer)) {
				unsigned *u = _th_big_sub(info->u.bits.base->u.integer,base->u.integer);
				n = info->u.bits.bits & (bits >> u[1]);
			} else {
				unsigned *u = _th_big_sub(base->u.integer,info->u.bits.base->u.integer);
				n = info->u.bits.bits & (bits << u[1]);
			}
            range_changed = (n != info->u.bits.bits);
			if (n==0) {
				info->range_type = RANGE_NONE;
				return 1;
			}
			info->u.bits.bits = n;
			increment[1] = 0;
			while ((info->u.bits.bits & 1)==0) {
				info->u.bits.bits >>= 1;
				++increment[1];
			}
	        info->u.bits.base = _ex_intern_integer(_th_big_add(info->u.bits.base->u.integer,increment));
			return range_changed;
		default:
			fprintf(stderr, "restrict_bits: Internal error: Illegal range_type\n");
			exit(1);
	}
}

static int restrict_range_list(struct variable_info *info, struct range_list *list, struct _ex_intern *offset)
{
	struct range_list *f, *fn, *fs, *fp;
    static unsigned increment[2] = { 1, 32 };
    int range_changed = 0;
	unsigned *d;
    unsigned disjunct, fbits;
	//unsigned n;

	switch (info->range_type) {
	    case RANGE_NONE:
			return 0;
		case RANGE_FILLED:
			while (list != NULL) {
				if ((list->low==NULL || !_th_big_less(info->u.range.min->u.integer,_th_big_add(list->low->u.integer,offset->u.integer))) &&
					(list->high==NULL || !_th_big_less(_th_big_add(list->high->u.integer,offset->u.integer),info->u.range.min->u.integer))) {
					return 0;
				}
				list = list->next;
			}
			info->range_type = RANGE_NONE;
			return 1;
		case RANGE_MIN_MAX:
			while (list && list->high != NULL && info->u.range.min != NULL &&
				   _th_big_less(_th_big_add(offset->u.integer,list->high->u.integer),info->u.range.min->u.integer)) {
				list = list->next;
			}
			if (list==NULL ||
				(info->u.range.max != NULL && _th_big_less(info->u.range.max->u.integer,_th_big_add(offset->u.integer,list->low->u.integer)))) {
				info->range_type = RANGE_NONE;
				return 1;
			}
			if (list->next==NULL || _th_big_less(info->u.range.max->u.integer,_th_big_add(list->next->low->u.integer,offset->u.integer))) {
                if (list->low && _th_big_less(info->u.range.min->u.integer,(d = _th_big_add(list->low->u.integer,offset->u.integer)))) {
					range_changed = 1;
					info->u.range.min = _ex_intern_integer(d);
				}
				if (list->high != NULL && _th_big_less((d = _th_big_add(list->high->u.integer,offset->u.integer)),info->u.range.max->u.integer)) {
					range_changed = 1;
					info->u.range.max = _ex_intern_integer(d);
				}
				return range_changed;
			}
			info->range_type = RANGE_FRAGMENTS;
			fs = f = (struct range_list *)_th_alloc(REWRITE_SPACE,sizeof(struct range_list));
			if (list->low && _th_big_less(info->u.range.min->u.integer,(d = _th_big_add(list->low->u.integer,offset->u.integer)))) {
				f->low = _ex_intern_integer(d);
			} else {
				f->low = info->u.range.min;
			}
			f->high = _ex_intern_integer(_th_big_add(list->high->u.integer,offset->u.integer));
			list = list->next;
			while (list != NULL) {
				if (info->u.range.max != NULL && _th_big_less(info->u.range.max->u.integer,_th_big_add(list->low->u.integer,offset->u.integer))) break;
  			    fn = (struct range_list *)_th_alloc(REWRITE_SPACE,sizeof(struct range_list));
                f->next = fn;
				f = fn;
				fn->low = _ex_intern_integer(_th_big_add(list->low->u.integer,offset->u.integer));
				if (info->u.range.max && _th_big_less((d = _th_big_add(list->high->u.integer,offset->u.integer)), info->u.range.max->u.integer)) {
					fn->high = _ex_intern_integer(d);
				} else {
					fn->high = info->u.range.max;
					break;
				}
				list = list->next;
			}
			info->u.fragments = fs;
			return 1;

		case RANGE_BITS:
			disjunct = 0;
			while (list != NULL) {
				increment[1] = 32;
				if (list->high != NULL && _th_big_less(_th_big_add(list->high->u.integer,offset->u.integer),info->u.bits.base->u.integer)) {
					fbits = 0;
				} else if (list->low != NULL && !_th_big_less(_th_big_add(offset->u.integer,list->low->u.integer),_th_big_copy(REWRITE_SPACE,_th_big_add(info->u.bits.base->u.integer,increment)))) {
					fbits = 0;
				} else {
					fbits = info->u.bits.bits;
					if (list->low != NULL && !_th_big_less(_th_big_add(offset->u.integer,list->low->u.integer),info->u.bits.base->u.integer)) {
						unsigned *r = _th_big_sub(_th_big_copy(REWRITE_SPACE,_th_big_copy(REWRITE_SPACE,_th_big_add(offset->u.integer,list->low->u.integer))),info->u.bits.base->u.integer);
						fbits >>= r[1];
						fbits <<= r[1];
					}
					if (list->high != NULL) {
						d = _th_big_sub(_th_big_copy(REWRITE_SPACE,_th_big_add(offset->u.integer,list->high->u.integer)),info->u.bits.base->u.integer);
						if (d[1]==1 && d[2] < 31) {
							fbits = fbits & bit_mask[d[1]];
						}
					}
				}
				disjunct |= fbits;
				list = list->next;
			}
			if (disjunct==0) {
				info->range_type = RANGE_NONE;
				return 1;
			} else if (info->u.bits.bits != disjunct) {
				range_changed = 1;
			}
			info->u.bits.bits = disjunct;
			increment[1] = 0;
			while ((info->u.bits.bits & 1)==0) {
				info->u.bits.bits >>= 1;
				++increment[1];
			}
			info->u.bits.base = _ex_intern_integer(_th_big_add(info->u.bits.base->u.integer,increment));
			return range_changed;
		case RANGE_FRAGMENTS:
			f = info->u.fragments;
			fs = fp = NULL;
			while (f && list) {
			    if (list->high != NULL && f->low != NULL &&
				       _th_big_less(_th_big_add(offset->u.integer,list->high->u.integer),f->low->u.integer)) {
				    list = list->next;
				} else if (list->low != NULL && f->high != NULL &&
					_th_big_less(f->high->u.integer,_th_big_add(offset->u.integer,list->low->u.integer))) {
					f = f->next;
				} else {
					if (fp = NULL) {
						fs = fp = (struct range_list *)_th_alloc(REWRITE_SPACE,sizeof(struct range_list));
					} else {
						fp->next = (struct range_list *)_th_alloc(REWRITE_SPACE,sizeof(struct range_list));
						fp = fp->next;
					}

					if (list->low==NULL || (f->low != NULL && _th_big_less(_th_big_add(list->low->u.integer,offset->u.integer),f->low->u.integer))) {
						fp->low = f->low;
					} else {
						fp->low = _ex_intern_integer(_th_big_add(offset->u.integer,list->low->u.integer));
					}

					if (list->high==NULL || (f->high != NULL && _th_big_less(f->high->u.integer,_th_big_add(offset->u.integer,list->low->u.integer)))) {
						fp->high = f->high;
						f = f->next;
					} else {
						fp->high = _ex_intern_integer(_th_big_add(offset->u.integer,list->high->u.integer));
						list = list->next;
					}
				}
			}
			if (fs==NULL) {
				info->range_type = RANGE_NONE;
				return 1;
			} else if (fs->next==NULL) {
				info->range_type = RANGE_MIN_MAX;
				info->u.range.min = fs->low;
				info->u.range.max = fs->high;
				return 1;
			} else {
				fp->next = NULL;
				fp = fs;
				f = info->u.fragments;
				while (f != NULL && fp != NULL) {
					if (f->low != fp->low || f->high != fp->high) {
						info->u.fragments = fs;
						return 1;
					}
					f = f->next;
					fp = fp->next;
				}
				if (f || fp) {
					info->u.fragments = fs;
					return 1;
				}
				return 0;
			}

		default:
			fprintf(stderr, "restrict_range_list: Internal error: illegal range type\n");
			exit(1);
	}
}

static int exclude_value(struct variable_info *info, struct _ex_intern *value)
{
	struct range_list *f, *f2;
    static unsigned increment[2] = { 1, 32 };
    int range_changed = 0;
	unsigned *d, *diff, u;

	switch (info->range_type) {
	    case RANGE_NONE:
			return 0;
		case RANGE_FILLED:
			if (info->u.range.min != value) {
				return 0;
			} else {
				info->range_type = RANGE_NONE;
				return 1;
			}
		case RANGE_MIN_MAX:
			if (info->u.range.min != NULL && _th_big_less(value->u.integer,info->u.range.min->u.integer)) return 0;
			if (info->u.range.max != NULL && _th_big_less(info->u.range.max->u.integer,value->u.integer)) return 0;
			increment[1] = 1;
			if (value==info->u.range.min) {
				info->u.range.min = _ex_intern_integer(_th_big_add(info->u.range.min->u.integer,increment));
				if (info->u.range.min==info->u.range.max) {
					info->range_type = RANGE_FILLED;
				}
				return 1;
			}
			if (value==info->u.range.max) {
				info->u.range.max = _ex_intern_integer(_th_big_sub(info->u.range.min->u.integer,increment));
				if (info->u.range.min==info->u.range.max) {
					info->range_type = RANGE_FILLED;
				}
				return 1;
			}
			if (info->u.range.min != NULL && info->u.range.max != NULL) {
                d = _th_big_sub(info->u.range.max->u.integer,info->u.range.min->u.integer);
				if (d[0]==1 && d[1] < 32) {
					u = d[1];
					info->range_type = RANGE_BITS;
					diff = _th_big_sub(value->u.integer,info->u.range.min->u.integer);
					info->u.bits.base = info->u.range.min;
					info->u.bits.bits = bit_mask[u] - (1<<diff[1]);
					if (info->u.bits.bits==0) {
						info->range_type = RANGE_NONE;
					}
					return 1;
				}
			}
			f = (struct range_list *)_th_alloc(REWRITE_SPACE,sizeof(struct range_list));
			f->next = NULL;
			f->high = info->u.range.max;
			f->low = _ex_intern_integer(_th_big_add(value->u.integer,increment));
            f2 = (struct range_list *)_th_alloc(REWRITE_SPACE,sizeof(struct range_list));
			f2->next = f;
			f2->low = info->u.range.min;
			f2->high = _ex_intern_integer(_th_big_sub(value->u.integer,increment));
			info->range_type = RANGE_FRAGMENTS;
			info->u.fragments = f2;
			return 1;

		case RANGE_BITS:
			if (_th_big_less(value->u.integer,info->u.bits.base->u.integer)) return 0;
			increment[1] = 31;
			if (_th_big_less(_th_big_add(info->u.bits.base->u.integer,increment),value->u.integer)) return 0;
			d = _th_big_sub(value->u.integer,info->u.bits.base->u.integer);
			if (info->u.bits.bits & (1<<d[1])) {
				info->u.bits.bits -= (1<<d[1]);
				if (info->u.bits.bits==0) {
					info->range_type = RANGE_NONE;
				}
				return 1;
			} else {
				return 0;
			}

		case RANGE_FRAGMENTS:
			f = info->u.fragments;
			f2 = NULL;
			while (f != NULL) {
				if ((f->low==NULL || !_th_big_less(value->u.integer,f->low->u.integer)) &&
					(f->high==NULL || !_th_big_less(f->high->u.integer,value->u.integer))) {
					increment[1] = 1;
					if (f->low==f->high) {
						if (f2) {
							f2->next = f->next;
						} else if (f->next) {
							info->u.fragments = f->next;
						} else {
							info->range_type = RANGE_NONE;
						}
					} else if (f->low==value) {
						f->low = _ex_intern_integer(_th_big_add(f->low->u.integer,increment));
					} else if (f->high==value) {
						f->high = _ex_intern_integer(_th_big_sub(f->high->u.integer,increment));
					} else {
						f2 = (struct range_list *)_th_alloc(REWRITE_SPACE,sizeof(struct range_list));
						f2->next = f->next;
						f->next = f2;
						f2->high = f->high;
						f->high= _ex_intern_integer(_th_big_sub(value->u.integer,increment));
						f2->low = _ex_intern_integer(_th_big_add(value->u.integer,increment));
					}
					return 1;
				}
				f2 = f;
				f = f->next;
			}
			return 0;
		default:
			fprintf(stderr, "restrict_range_list: Internal error: illegal range type\n");
			exit(1);
	}
}

static int restrict_variable(struct variable_info *var, struct variable_info *vi, struct _ex_intern *offset)
{
	struct _ex_intern *min, *max;
	switch (vi->range_type) {
	    case RANGE_NONE:
			return 0;
		case RANGE_FILLED:
			if (contains_value(var,vi->u.range.min)) {
				return 0;
			} else {
				var->range_type = RANGE_NONE;
				return 1;
			}
		case RANGE_BITS:
			return restrict_bits(var,
				       _ex_intern_integer(_th_big_add(vi->u.bits.base->u.integer,offset->u.integer)),
					   vi->u.bits.bits);
		case RANGE_MIN_MAX:
			if (vi->u.range.min==NULL) {
				min = NULL;
			} else {
				min = _ex_intern_integer(_th_big_add(vi->u.range.min->u.integer,offset->u.integer));
			}
			if (vi->u.range.max==NULL) {
				max = NULL;
			} else {
				max = _ex_intern_integer(_th_big_add(vi->u.range.max->u.integer,offset->u.integer));
			}
			return restrict_range(var,min,max);
		case RANGE_FRAGMENTS:
			return restrict_range_list(var,vi->u.fragments,offset);
		default:
			fprintf(stderr, "Internal error: restrict_vairable: Illegal range type\n");
			exit(1);
	}
}

void _print_range(struct variable_info *var)
{
	struct range_list *rl;

	_tree_print1("range: (%d) ", var->range_type);
	switch (var->range_type) {
	    case RANGE_MIN_MAX:
		    _tree_print_exp("", var->u.range.min);
		    _tree_print_exp("", var->u.range.max);
		    break;
	    case RANGE_BITS:
		    _tree_print2("%s (%x)", _th_print_exp(var->u.bits.base), var->u.bits.bits);
		    break;
	    case RANGE_FRAGMENTS:
		    rl = var->u.fragments;
		    while (rl != NULL) {
			    _tree_print0("Fragment");
			    _tree_indent();
			    _tree_print_exp("", rl->low);
			    _tree_print_exp("", rl->high);
			    _tree_undent();
			    rl = rl->next;
			}
		    break;
	    case RANGE_FILLED:
		    _tree_print_exp("exact value", var->u.range.min);
		    break;
		case RANGE_NONE:
			_tree_print0("No legal value");
			break;
	    default:
		    _tree_print0("**ERROR**\n");
	}
}

struct _ex_intern *_fd_get_value_count(struct env *env, struct fd_handle *fd, unsigned var)
{
	int i;
    struct variable_info *v;
    unsigned increment[2] = { 1, 1 };
    unsigned *acc, *tmp, bits;
    struct range_list *f;

	for (i = 0; i < fd->var_count; ++i) {
		if (fd->vars[i].var==var) {
			v = &fd->vars[i];
			break;
		}
	}

	switch (v->range_type) {
	    case RANGE_FILLED:
			return _ex_intern_small_integer(1);
		case RANGE_NONE:
			return _ex_intern_small_integer(0);
		case RANGE_MIN_MAX:
			if (v->u.range.min==NULL || v->u.range.max==NULL) return 0;
            tmp = _th_big_copy(REWRITE_SPACE,_th_big_sub(v->u.range.max->u.integer,v->u.range.min->u.integer));
			tmp = _th_big_add(increment,tmp);
			return _ex_intern_integer(tmp);

		case RANGE_FRAGMENTS:
			f = v->u.fragments;
            acc = NULL;
			while (f) {
				if (f->low && f->high) {
                    tmp = _th_big_copy(REWRITE_SPACE,_th_big_sub(f->high->u.integer,f->low->u.integer));
		        	tmp = _th_big_add(increment,tmp);
					if (acc) {
						acc = _th_big_copy(REWRITE_SPACE,_th_big_add(acc,tmp));
					} else {
						acc = tmp;
					}
				}
				f = f->next;
			}
			return _ex_intern_integer(acc);
		case RANGE_BITS:
			bits = v->u.bits.bits;
			i = 0;
			while (bits) {
				if (bits&1) {
					++i;
				}
				bits >>= 1;
			}
			return _ex_intern_small_integer(i);
		default:
			fprintf(stderr, "Internal error: _fd_get_value_count: Illegal range type\n");
			exit(1);
	}
}

static int equal_ranges(struct variable_info *var1, struct variable_info *var2)
{
	struct range_list *f1, *f2;

	if (var1->range_type != var2->range_type) return 0;

	switch (var1->range_type) {
	    case RANGE_NONE:
			return 1;
		case RANGE_FILLED:
			return var1->u.range.min==var2->u.range.min;
		case RANGE_MIN_MAX:
			return var1->u.range.min==var2->u.range.min &&
				   var1->u.range.max==var2->u.range.max;
		case RANGE_BITS:
			return var1->u.bits.base==var2->u.bits.base &&
				   var1->u.bits.bits==var2->u.bits.bits;
		case RANGE_FRAGMENTS:
			f1 = var1->u.fragments;
			f2 = var2->u.fragments;
			while (f1 && f2) {
				if (f1->low != f2->low || f1->high != f2->high) return 0;
				f1 = f1->next;
				f2 = f2->next;
			}
			if (f1 || f2) return 0;
			return 1;
		default:
			return 0;
	}
}

static void add_value(struct variable_info *var, struct _ex_intern *value)
{
	unsigned increment[2] = { 1, 1 };
	unsigned *d;
    struct _ex_intern *e, *g;
    unsigned bits, n;
    struct range_list *f, *pf, *nf;

	if (contains_value(var, value)) return;

	switch (var->range_type) {
	    case RANGE_NONE:
			var->range_type = RANGE_FILLED;
			var->u.range.min = value;
			return;
		case RANGE_FILLED:
			if (var->u.range.min==value) return;
			e = _ex_intern_integer(_th_big_add(value->u.integer,increment));
			if (e==var->u.range.min) {
				var->u.range.max = var->u.range.min;
				var->u.range.min = value;
				var->range_type = RANGE_MIN_MAX;
			}
			e = _ex_intern_integer(_th_big_sub(value->u.integer,increment));
			if (e==var->u.range.min) {
				var->u.range.max = value;
				var->range_type = RANGE_MIN_MAX;
			}
            if (_th_big_less(var->u.range.min->u.integer,value->u.integer)) {
				d = _th_big_sub(value->u.integer,var->u.range.min->u.integer);
				if (d[0]==1 && d[1] < 32) {
					bits = (1<<d[1]);
					bits |= 1;
					var->u.bits.base = var->u.range.min;
					var->u.bits.bits = bits;
					var->range_type = RANGE_BITS;
					return;
				} else {
					f = (struct range_list *)_th_alloc(REWRITE_SPACE, sizeof(struct range_list));
					f->low = var->u.range.min;
					f->high = var->u.range.min;
					f->next = (struct range_list *)_th_alloc(REWRITE_SPACE, sizeof(struct range_list));
					f->next->low = f->next->high = value;
					f->next->next = NULL;
					var->u.fragments = f;
					var->range_type = RANGE_FRAGMENTS;
					return;
				}
			} else {
			    d = _th_big_sub(var->u.range.min->u.integer, value->u.integer);
				if (d != NULL && d[0]==1 && d[1] < 32) {
					bits = 1;
					bits <<= d[1];
					bits += 1;
					var->u.bits.base = value;
					var->u.bits.bits = bits;
					var->range_type = RANGE_BITS;
					return;
				} else {
					f = (struct range_list *)_th_alloc(REWRITE_SPACE, sizeof(struct range_list));
					f->low = f->high = value;
					f->next = (struct range_list *)_th_alloc(REWRITE_SPACE, sizeof(struct range_list));
					f->next->low = var->u.range.min;
					f->next->high = var->u.range.min;
					f->next->next = NULL;
					var->u.fragments = f;
					var->range_type = RANGE_FRAGMENTS;
					return;
				}
			}
		case RANGE_MIN_MAX:
			e = _ex_intern_integer(_th_big_add(value->u.integer,increment));
			if (e==var->u.range.min) {
				var->u.range.min = value;
				return;
			}
			e = _ex_intern_integer(_th_big_sub(value->u.integer,increment));
			if (e==var->u.range.max) {
				var->u.range.max = value;
				return;
			}
            if (var->u.range.max != NULL && _th_big_less(var->u.range.max->u.integer,value->u.integer)) {
				d = _th_big_sub(value->u.integer,var->u.range.min->u.integer);
				if (d[0]==1 && d[1] < 32) {
					bits = (1<<d[1]);
					d = _th_big_sub(var->u.range.max->u.integer,var->u.range.min->u.integer);
					bits |= bit_mask[d[1]];
					var->u.bits.base = var->u.range.min;
					var->u.bits.bits = bits;
					var->range_type = RANGE_BITS;
					return;
				} else {
					f = (struct range_list *)_th_alloc(REWRITE_SPACE, sizeof(struct range_list));
					f->low = var->u.range.min;
					f->high = var->u.range.max;
					f->next = (struct range_list *)_th_alloc(REWRITE_SPACE, sizeof(struct range_list));
					f->next->low = f->next->high = value;
					f->next->next = NULL;
					var->u.fragments = f;
					var->range_type = RANGE_FRAGMENTS;
					return;
				}
			} else {
				if (var->u.range.max != NULL) {
					d = _th_big_sub(var->u.range.max->u.integer, value->u.integer);
				} else {
					d = NULL;
				}
				if (d != NULL && d[0]==1 && d[1] < 32) {
					d = _th_big_sub(var->u.range.max->u.integer,var->u.range.min->u.integer);
					bits = bit_mask[d[1]];
					d = _th_big_sub(var->u.range.min->u.integer,value->u.integer);
					bits <<= d[1];
					bits += 1;
					var->u.bits.base = value;
					var->u.bits.bits = bits;
					var->range_type = RANGE_BITS;
					return;
				} else {
					f = (struct range_list *)_th_alloc(REWRITE_SPACE, sizeof(struct range_list));
					f->low = f->high = value;
					f->next = (struct range_list *)_th_alloc(REWRITE_SPACE, sizeof(struct range_list));
					f->next->low = var->u.range.min;
					f->next->high = var->u.range.max;
					f->next->next = NULL;
					var->u.fragments = f;
					var->range_type = RANGE_FRAGMENTS;
					return;
				}
			}
		case RANGE_BITS:
			increment[1] = 31;
			g = _ex_intern_integer(_th_big_add(var->u.bits.base->u.integer,increment));
			if (_th_big_less(g->u.integer,value->u.integer)) goto convert_to_fragments;
			if (_th_big_less(var->u.bits.base->u.integer,value->u.integer)) {
				d = _th_big_sub(value->u.integer,var->u.bits.base->u.integer);
				var->u.bits.bits |= (1<<d[1]);
				return;
			}
			d = _th_big_sub(var->u.bits.base->u.integer,value->u.integer);
			if (d[0] > 1 || d[1] > 31) goto convert_to_fragments;
			bits = var->u.bits.bits;
			n = d[1];
			while (n--) {
				if (bits & 0x80000000) goto convert_to_fragments;
				bits <<= 1;
			}
            var->u.bits.bits = (bits | 1);
			var->u.bits.base = value;
			return;
convert_to_fragments:
			bits = var->u.bits.bits;
			nf = pf = f = NULL;
			e = var->u.bits.base;
			n = 0;
#ifdef XX
			printf("pre bits %x\n", bits);
			while ((bits&1)==0) {
				++n;
				bits >>= 1;
			}
			printf("post bits %x\n", bits);
			increment[1] = n;
			e = _ex_intern_integer(_th_big_add(e->u.integer,increment));
#endif
			while (bits) {
  			    //printf("Bits = %x\n", bits);
				n = 0;
				while (bits&1) {
					++n;
					bits >>= 1;
				}
				//printf("    1) %x\n", bits);
				increment[1] = n-1;
				f = (struct range_list *)_th_alloc(REWRITE_SPACE,sizeof(struct range_list));
				f->next = NULL;
				if (pf) {
					pf->next = f;
				} else {
					var->u.fragments = f;
				}
				f->low = e;
				f->high = _ex_intern_integer(_th_big_add(e->u.integer,increment));
				pf = f;
				if (bits) {
					while ((bits&1)==0) {
						++n;
						bits >>= 1;
					}
				}
				//printf("    2) %x\n", bits);
				increment[1] = n;
				e = _ex_intern_integer(_th_big_add(e->u.integer,increment));
     			//exit(1);
			}
			var->range_type = RANGE_FRAGMENTS;
		case RANGE_FRAGMENTS:
			f = var->u.fragments;
			pf = NULL;
			e = _ex_intern_integer(_th_big_sub(value->u.integer,increment));
			g = _ex_intern_integer(_th_big_add(value->u.integer,increment));
			while (f != NULL) {
				if (f->low==g) {
					f->low = value;
					return;
				}
				if (f->high==e) {
					f->high = value;
					return;
				}
				if (f->low && _th_big_less(value->u.integer,f->low->u.integer)) {
					nf = (struct range_list *)_th_alloc(REWRITE_SPACE,sizeof(struct range_list));
					nf->low = nf->high = value;
					nf->next = f;
					if (pf) {
						pf->next = nf;
					} else {
						var->u.fragments = nf;
					}
					return;
				}
				pf = f;
				f = f->next;
			}
			nf = (struct range_list *)_th_alloc(REWRITE_SPACE,sizeof(struct range_list));
			nf->low = nf->high = value;
			nf->next = NULL;
			if (pf) {
				pf->next = nf;
			} else {
				var->u.fragments = nf;
			}
			return;
		default:
			fprintf(stderr, "Internal error: add_value: Illegal range_type\n");
			exit(1);
	}
}

static struct _ex_intern *evaluate_expression(struct env *env, struct _ex_intern *exp)
{
	struct _ex_intern *acc, *e;
    int i;

	if (exp->type==EXP_INTEGER) return exp;

	if (exp->type != EXP_APPL) {
		e = _th_rewrite(env,exp);
		if (e->type != EXP_INTEGER) return NULL;
		return e;
	}

	switch (exp->u.appl.functor) {
	    case INTERN_NAT_PLUS:
			acc = evaluate_expression(env,exp->u.appl.args[0]);
			if (acc==NULL) return NULL;
			for (i = 1; i < exp->u.appl.count; ++i) {
				e = evaluate_expression(env,exp->u.appl.args[i]);
				if (e==NULL) return NULL;
				acc = _ex_intern_integer(_th_big_add(acc->u.integer,e->u.integer));
			}
			return acc;
	    case INTERN_NAT_TIMES:
			acc = evaluate_expression(env,exp->u.appl.args[0]);
			e = evaluate_expression(env,exp->u.appl.args[1]);
			if (acc==NULL || e==NULL) return NULL;
			return _ex_intern_integer(_th_big_multiply(acc->u.integer,e->u.integer));
		case INTERN_NAT_DIVIDE:
			acc = evaluate_expression(env,exp->u.appl.args[0]);
			e = evaluate_expression(env,exp->u.appl.args[1]);
			if (acc==NULL || e==NULL) return NULL;
			return _ex_intern_integer(_th_big_divide(acc->u.integer,e->u.integer));
	    default:
			e = _th_rewrite(env,exp);
			if (e->type != EXP_INTEGER) return NULL;
			return e;
	}
}

static int exact_restriction(struct fd_handle *fd, struct env *env, struct constraint_info *ci)
{
	struct variable_info *var, old_var;
	int *indices, i;
    char *mark;
    struct _ex_intern *r;
	mark = _th_alloc_mark(MATCH_SPACE);

	_zone_print0("Exact restriction");
	_tree_indent();

	var = &fd->vars[ci->assign_index];
	indices = (int *)ALLOCA(sizeof(int) * ci->var_count);
	for (i = 0; i < ci->var_count; ++i) {
		indices[i] = 0;
	}

	old_var = *var;
	var->range_type = RANGE_NONE;
	i = 0;
	while (i < ci->var_count) {
		struct _ex_unifier *u = _th_new_unifier(MATCH_SPACE);
		_zone_print0("Checking combination");
		_tree_indent();
		for (i = 0; i < ci->var_count; ++i) {
			_zone_print2("%s = %s", _th_intern_decode(fd->vars[ci->vars[i]].var),_th_print_exp(_fd_get_value_n(env,fd,fd->vars[ci->vars[i]].var,indices[i])));
			_th_add_pair(MATCH_SPACE,u,fd->vars[ci->vars[i]].var,
				         _fd_get_value_n(env,fd,fd->vars[ci->vars[i]].var,indices[i]));
		}
		_tree_undent();
		r = ci->constraint;
		if (r->u.appl.args[0]->type==EXP_VAR && r->u.appl.args[0]->u.var==ci->assign_var) {
			r = r->u.appl.args[1];
		} else {
			r = r->u.appl.args[0];
		}
        r = evaluate_expression(env,_th_subst(env,u,r));
		if (r==NULL) {
			*var = old_var;
			_zone_print0("Failure");
			_tree_undent();
			return 0;
		}
		if (contains_value(&old_var,r)) {
			_zone_print_exp("Adding value", r);
			add_value(var,r);
#ifndef FAST
            if (_zone_active() && !strcmp(_th_intern_decode(var->var),"d")) {
			    _tree_indent();
		        _print_range(var);
			    _tree_undent();
			}
#endif
		}
		for (i = 0; i < ci->var_count; ++i) {
			if (_th_is_free_in(ci->constraint,fd->vars[ci->vars[i]].var)) {
			    struct _ex_intern *v = _fd_get_value_count(env,fd,fd->vars[ci->vars[i]].var);
			    ++indices[i];
			    if (indices[i]==(int)v->u.integer[1]) {
				    indices[i] = 0;
				} else {
				    break;
				}
			}
		}
	}

	_th_alloc_release(MATCH_SPACE, mark);

	_tree_undent();
	return !equal_ranges(var,&old_var);
}

static int combination_count(struct fd_handle *fd, struct env *env, struct constraint_info *ci)
{
	int prod = 1;
	int i;

	for (i = 0; i < ci->var_count; ++i) {
		struct _ex_intern *v = _fd_get_value_count(env,fd,fd->vars[ci->vars[i]].var);

		if (v==NULL || v->u.integer[0] != 1) {
			return 0x7fffffff;
		}

		prod *= v->u.integer[1];
	}

	return prod;
}

int _fd_combination_limit = 10000;

static int propagate_constraint(struct fd_handle *fd, struct env *env, struct constraint_info *ci)
{
	struct _ex_intern *e = ci->constraint, *rhs, *min, *max;
    int change;
    struct variable_info *var;
    static unsigned increment[2] = { 1, 1 };
	unsigned v;
    int vindex, i, count;

	ci->needs_propagation = 0;
    if (ci->is_delayed) {
		return 0;
	}

	_zone_print_exp("Propagating constraint", ci->constraint);
	_tree_indent();

	if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
		e = e->u.appl.args[0];
	}
	if (e->u.appl.args[0]->type==EXP_VAR && e->u.appl.args[0]->u.var==ci->assign_var) {
		rhs = e->u.appl.args[1];
	} else {
		rhs = e->u.appl.args[0];
	}
	var = &fd->vars[ci->assign_index];
#ifndef FAST
    if (_zone_active()) _print_range(var);
#endif
	switch (ci->constraint->u.appl.functor) {
	    case INTERN_NOT:
		    switch (e->u.appl.functor) {
		        case INTERN_NAT_LESS:
		 		    if (rhs==e->u.appl.args[1]) {
					    e = compute_min(env,fd,rhs);
					    change = restrict_range(var,e,NULL);
					} else {
					    e = compute_max(env,fd,rhs);
					    change = restrict_range(var,NULL,e);
					}
				    break;
			    case INTERN_EQUAL:
				case INTERN_ORIENTED_RULE:
				    if (rhs->type==EXP_INTEGER) {
					    change = exclude_value(var,rhs);
					} else {
				 	    change = 0;
					}
				    break;
			}
		    break;
	    case INTERN_EQUAL:
		case INTERN_ORIENTED_RULE:
			if (combination_count(fd,env,ci) <= _fd_combination_limit) {
				//printf("Combination count %d\n", combination_count(fd,env,ci));
				change = exact_restriction(fd,env,ci);
				goto cont;
			} else if (rhs->u.appl.functor==INTERN_NAT_PLUS &&
				rhs->u.appl.count==2) {
				if (rhs->u.appl.args[0]->type==EXP_INTEGER && rhs->u.appl.args[1]->type==EXP_VAR) {
					v = rhs->u.appl.args[1]->u.var;
					for (i = 0; i < ci->var_count; ++i) {
						if (fd->vars[ci->vars[i]].var==v) {
							vindex = ci->vars[i];
							break;
						}
					}
                    change = restrict_variable(var,&fd->vars[vindex],rhs->u.appl.args[0]);
					goto cont;
				} else if (rhs->u.appl.args[1]->type==EXP_INTEGER && rhs->u.appl.args[0]->type==EXP_VAR) {
					v = rhs->u.appl.args[0]->u.var;
					for (i = 0; i < ci->var_count; ++i) {
						if (fd->vars[ci->vars[i]].var==v) {
							vindex = ci->vars[i];
							break;
						}
					}
                    change = restrict_variable(var,&fd->vars[vindex],rhs->u.appl.args[1]);
					goto cont;
				}
			}
			min = compute_min(env,fd,rhs);
			max = compute_max(env,fd,rhs);
			_zone_print_exp("min =", min);
			_zone_print_exp("max =", max);
			change = restrict_range(var,min,max);
			break;
	    case INTERN_NAT_LESS:
			if (rhs==e->u.appl.args[1]) {
				e = compute_max(env,fd,rhs);
				e = _ex_intern_integer(_th_big_sub(e->u.integer,increment));
				change = restrict_range(var,NULL,e);
			} else {
				e = compute_min(env,fd,rhs);
				e = _ex_intern_integer(_th_big_add(e->u.integer,increment));
				change = restrict_range(var,e,NULL);
			}
			break;
		default:
			fprintf(stderr, "Internal error: propagate_constraint: Illegal constraint form:\n%s\n",
				    _th_print_exp(ci->constraint));
			exit(1);
	}
cont:
	if (change) {
		if (var->range_type==RANGE_NONE) {
			_zone_print0("Eliminates all solutions");
			_tree_undent();
			return 1;
		}
		_zone_print_exp("Restricts range of", ci->assign_var);
#ifndef FAST
        if (_zone_active()) {
			_print_range(var);
		}
#endif
		for (i = 0; i < var->effects_count; ++i) {
			fd->constraints[var->effects_constraint[i]].needs_propagation = 1;
		}
		if (var->range_type==RANGE_FILLED) {
		    struct _ex_unifier *u = _th_new_unifier(REWRITE_SPACE);
			u = _th_add_pair(REWRITE_SPACE,u,var->var,var->u.range.min);
  		    for (i = 0; i < var->effects_count; ++i) {
				struct constraint_info *ci = &fd->constraints[var->effects_constraint[i]];
				ci->constraint = _th_rewrite(env, _th_subst(env,u,ci->constraint));
         		_th_get_free_vars(ci->constraint, &count);
		        if (count < 2) {
			        ci->is_delayed = 0;
				}
			}
		}
	}
	_tree_undent();
	return 0;
}

static int propagate_constraints(struct env *env, struct fd_handle *fd)
{
	int i, changed;

	changed = 1;
	while (changed) {
		changed = 0;
		for (i = 0; i < fd->constraint_count; ++i) {
			if (fd->constraints[i].needs_propagation) {
				if (propagate_constraint(fd,env,&fd->constraints[i])) return 1;
				changed = 1;
			}
		}
	}
	return 0;
}

void _fd_print(struct env *env, struct fd_handle *fd)
{
	int i, j;

    _tree_print0("FD info");
	_tree_indent();

	_tree_print0("Variables");
	_tree_indent();
    for (i = 0; i < fd->var_count; ++i) {
		_tree_print1("%s", _th_intern_decode(fd->vars[i].var));
		_tree_indent();
		_print_range(&fd->vars[i]);
        for (j = 0; j < fd->vars[i].effects_count; ++j) {
			_tree_print3("Effects %s through constraint %d (%s)\n",
				_th_intern_decode(fd->vars[i].effects_var[j]),
				fd->vars[i].effects_constraint[j],
				_th_print_exp(fd->constraints[fd->vars[i].effects_constraint[j]].constraint));
		}
		_tree_undent();
	}
	_tree_undent();

	_tree_print0("Constraints");
	_tree_indent();
	for (i = 0; i < fd->constraint_count; ++i) {
		_tree_print2("Constraint #%d: %s\n", i, _th_print_exp(fd->constraints[i].constraint));
		_tree_indent();
		if (fd->constraints[i].is_delayed) {
			_tree_print0("*** DELAYED ***");
		}
		_tree_print2("Assigns to %s with index %d\n",
			   _th_intern_decode(fd->constraints[i].assign_var),
			   fd->constraints[i].assign_index);
		_tree_print0("Uses:\n");
		_tree_indent();
		for (j = 0; j < fd->constraints[i].var_count; ++j) {
			_tree_print1("%s", _th_intern_decode(fd->vars[fd->constraints[i].vars[j]].var));
		}
		_tree_undent();
		_tree_undent();
	}
    _tree_undent();

	_tree_undent();
}

struct fd_handle *_fd_solve(struct env *env, struct _ex_intern *exp)
{
	unsigned *fv, *vars;
    int count, i, j, k, ccount, l, m;
    struct fd_handle *fd;
    struct _ex_intern **args, *na, *e;
    struct _ex_intern *context_rules = _th_get_context_rule_set(env);

	_zone_print0("fd solve");
	_tree_indent();

	subexps = NULL;
	args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (exp->u.appl.count + 1));
	na = exp;
    for (i = 0; i < exp->u.appl.count; ++i) {
		args[i] = break_equation(env,na,exp->u.appl.args[i]);
		na = new_na;
	}
	if (subexps==NULL) subexps = _ex_true;
	args[i++] = subexps;
	exp = _th_flatten(env,_ex_intern_appl_env(env,INTERN_AND,i,args));

	fv = _th_get_free_vars(exp, &count);

	fd = (struct fd_handle *)_th_alloc(REWRITE_SPACE,sizeof(struct fd_handle));
	fd->var_count = count;
	fd->vars = (struct variable_info *)_th_alloc(REWRITE_SPACE,sizeof(struct variable_info) * count);

	for (i = 0; i < count; ++i) {
		fd->vars[i].var = fv[i];
	}

	ccount = 0;
	for (i = 0; i < exp->u.appl.count; ++i) {
		fv = _th_get_free_vars(exp->u.appl.args[i], &j);
		ccount += j;
	}

	printf("Total count = %d\n", ccount);

	fd->constraints = (struct constraint_info *)_th_alloc(REWRITE_SPACE,sizeof(struct constraint_info) * ccount);
    fd->next = NULL;

	args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count);

	ccount = 0;
	for (i = 0; i < exp->u.appl.count; ++i) {
		fv = _th_get_free_vars(exp->u.appl.args[i],&count);
		vars = (unsigned *)ALLOCA(sizeof(unsigned) * count);
		for (j = 0; j < count; ++j) {
			vars[j] = fv[j];
		}
		for (j = 0; j < count; ++j) {
			e = generate_constraint_for_var(env, vars[j], exp->u.appl.args[i]);
			fd->constraints[ccount].constraint = e;
			fd->constraints[ccount].assign_var = vars[j];
			fd->constraints[ccount].needs_propagation = 1;
			fd->constraints[ccount].is_delayed = (!min_max_form(env,vars[j],e));
			for (k = 0; k < fd->var_count; ++k) {
				if (vars[j]==fd->vars[k].var) {
					fd->constraints[ccount].assign_index = k;
					break;
				}
			}
			fd->constraints[ccount].var_count = count - 1;
			fd->constraints[ccount].vars = (unsigned *)_th_alloc(REWRITE_SPACE,sizeof(unsigned) * (count - 1));
			for (k = 0, l = 0; k < count; ++k) {
				if (k != j) {
					for (m = 0; m < fd->var_count; ++m) {
						if (fd->vars[m].var==vars[k]) {
        					fd->constraints[ccount].vars[l++] = m;
							break;
						}
					}
				}
			}
			++ccount;
		}
	}

	fd->constraint_count = ccount;

	for (i = 0; i < fd->var_count; ++i) {
		k = 0;
		for (j = 0; j < fd->constraint_count; ++j) {
			for (l = 0; l < fd->constraints[j].var_count; ++l) {
				if (i==fd->constraints[j].vars[l]) {
					++k;
					goto cont;
				}
			}
cont:;
		}
		fd->vars[i].effects_constraint = (int *)_th_alloc(REWRITE_SPACE,sizeof(int) * k);
		fd->vars[i].effects_var = (int *)_th_alloc(REWRITE_SPACE,sizeof(int) * k);
		k = 0;
		for (j = 0; j < fd->constraint_count; ++j) {
			for (l = 0; l < fd->constraints[j].var_count; ++l) {
				if (i==fd->constraints[j].vars[l]) {
					fd->vars[i].effects_constraint[k] = j;
					fd->vars[i].effects_var[k++] = fd->constraints[j].assign_var;
					goto cont2;
				}
			}
cont2:;
		}
        fd->vars[i].effects_count = k;
		fd->vars[i].range_type = RANGE_MIN_MAX;
		fd->vars[i].u.range.min = _th_get_min(env,context_rules,exp,fd->vars[i].var);
		fd->vars[i].u.range.max = _th_get_max(env,context_rules,exp,fd->vars[i].var);
	}

#ifndef FAST
    if (_zone_active()) _fd_print(env,fd);
#endif
	_zone_print0("Constraint propagations");
	_tree_indent();
	i = propagate_constraints(env, fd);
    _tree_undent();
#ifndef FAST
    if (_zone_active()) _fd_print(env,fd);
#endif

	if (i) fd = NULL;

	_tree_undent();
	return fd;
}

static struct range_list *copy_fragments(struct range_list *rl)
{
	struct range_list *np, *n, *ret;

	ret = np = NULL;
	while (rl) {
		n = (struct range_list *)_th_alloc(REWRITE_SPACE, sizeof(struct range_list));
		if (np) {
			np->next = n;
		} else {
			ret = n;
		}
		n->low = rl->low;
		n->high = rl->high;
		n->next = NULL;
		np = n;
		rl = rl->next;
	}

	return ret;
}

void _fd_push(struct fd_handle *fd)
{
	int i;
	struct fd_handle *n =(struct fd_handle *)_th_alloc(REWRITE_SPACE, sizeof(struct fd_handle));

	memcpy(n,fd,sizeof(struct fd_handle));
	fd->vars = (struct variable_info *)_th_alloc(REWRITE_SPACE,sizeof(struct variable_info) * n->var_count);
	memcpy(fd->vars,n->vars,sizeof(struct variable_info) * n->var_count);
	fd->constraints = (struct constraint_info *)_th_alloc(REWRITE_SPACE,sizeof(struct constraint_info) * n->constraint_count);
	memcpy(fd->constraints,n->constraints,sizeof(struct constraint_info) * n->constraint_count);
	fd->next = n;

	for (i = 0; i < fd->var_count; ++i) {
		if (fd->vars[i].range_type==RANGE_FRAGMENTS) {
			fd->vars[i].u.fragments = copy_fragments(fd->vars[i].u.fragments);
		}
	}
}

void _fd_pop(struct fd_handle *fd)
{
	memcpy(fd,fd->next,sizeof(struct fd_handle));
}

void _fd_revert(struct fd_handle *fd)
{
	int i;

	struct fd_handle *n = fd->next;
	memcpy(fd,fd->next,sizeof(struct fd_handle));
	fd->vars = (struct variable_info *)_th_alloc(REWRITE_SPACE,sizeof(struct variable_info) * n->var_count);
	memcpy(fd->vars,n->vars,sizeof(struct variable_info) * n->var_count);
	fd->constraints = (struct constraint_info *)_th_alloc(REWRITE_SPACE,sizeof(struct constraint_info) * n->constraint_count);
	memcpy(fd->constraints,n->constraints,sizeof(struct constraint_info) * n->constraint_count);
	for (i = 0; i < fd->var_count; ++i) {
		if (fd->vars[i].range_type==RANGE_FRAGMENTS) {
			fd->vars[i].u.fragments = copy_fragments(fd->vars[i].u.fragments);
		}
	}
	fd->next = n;
}

struct _ex_intern *_fd_get_value_n(struct env *env, struct fd_handle *fd, unsigned var, int n)
{
	int i;
    struct variable_info *v;
    unsigned increment[2] = { 1, 1 };
    unsigned *acc, *tmp, bits;
    struct range_list *f;

	if (n < 0) return NULL;

	for (i = 0; i < fd->var_count; ++i) {
		if (fd->vars[i].var==var) {
			v = &fd->vars[i];
			break;
		}
	}

	switch (v->range_type) {
	    case RANGE_FILLED:
			if (n==0) {
				return v->u.range.min;
			} else {
				return NULL;
			}
		case RANGE_NONE:
			return NULL;
		case RANGE_MIN_MAX:
			if (v->u.range.min==NULL || v->u.range.max==NULL) return NULL;
			increment[1] = n;
			return _ex_intern_integer(_th_big_add(v->u.range.min->u.integer,increment));
		case RANGE_FRAGMENTS:
			f = v->u.fragments;
            acc = NULL;
			while (f) {
				if (f->low && f->high) {
                    tmp = _th_big_sub(f->high->u.integer,f->low->u.integer);
					if (tmp[0] > 1 || ((unsigned)n) <= tmp[1]) {
						increment[1] = n;
						return _ex_intern_integer(_th_big_add(f->low->u.integer,increment));
					}
					n -= (tmp[1]+1);
				}
				f = f->next;
			}
			return NULL;
		case RANGE_BITS:
			bits = v->u.bits.bits;
			i = -1;
			while (bits && n >= 0) {
				++i;
				if (bits&1) {
					--n;
				}
				bits >>= 1;
			}
			increment[1] = i;
			return _ex_intern_integer(_th_big_add(v->u.bits.base->u.integer,increment));
		default:
			fprintf(stderr, "Internal error: _fd_get_value_count: Illegal range type\n");
			exit(1);
	}
}

int _fd_instantiate(struct env *env, struct fd_handle *fd, unsigned var, struct _ex_intern *value)
{
	int i, count;
    struct variable_info *v;
    struct _ex_unifier *u = _th_new_unifier(REWRITE_SPACE);

	_zone_print2("fd_instantiate %s %s\n", _th_intern_decode(var), _th_print_exp(value));
	_tree_indent();

	for (i = 0; i < fd->var_count; ++i) {
		if (fd->vars[i].var==var) {
			v = &fd->vars[i];
			break;
		}
	}

	u = _th_add_pair(REWRITE_SPACE,u,v->var,v->u.range.min);
	for (i = 0; i < v->effects_count; ++i) {
		struct constraint_info *ci = &fd->constraints[v->effects_constraint[i]];
		ci->constraint = _th_rewrite(env, _th_subst(env,u,ci->constraint));
		_th_get_free_vars(ci->constraint, &count);
		if (count < 2) {
			ci->is_delayed = 0;
		}
	}

	v->range_type = RANGE_FILLED;
	v->u.range.min = value;

#ifndef FAST
    if (_zone_active()) _fd_print(env,fd);
#endif

	for (i = 0; i < v->effects_count; ++i) {
		fd->constraints[v->effects_constraint[i]].needs_propagation = 1;
	}

	i = propagate_constraints(env,fd);

#ifndef FAST
    if (_zone_active()) _fd_print(env,fd);
#endif
	_tree_undent();
	return i;
}

struct _ex_intern *_fd_get_min_value(struct env *env, struct fd_handle *fd, unsigned var)
{
	int i;
    struct variable_info *v;

	for (i = 0; i < fd->var_count; ++i) {
		if (fd->vars[i].var==var) {
			v = &fd->vars[i];
			break;
		}
	}

	switch (v->range_type) {
	    case RANGE_FILLED:
		case RANGE_MIN_MAX:
			return v->u.range.min;
		case RANGE_NONE:
			return NULL;
		case RANGE_FRAGMENTS:
			return v->u.fragments->low;
		case RANGE_BITS:
			return v->u.bits.base;
		default:
			fprintf(stderr, "Internal error: fd_get_min_value: Illegal range type\n");
			exit(1);
	}
}

struct _ex_intern *_fd_get_max_value(struct env *env, struct fd_handle *fd, unsigned var)
{
	int i;
    struct variable_info *v;
    struct range_list *f;
    unsigned bits;
	unsigned increment[2] = { 1, 1 };

	for (i = 0; i < fd->var_count; ++i) {
		if (fd->vars[i].var==var) {
			v = &fd->vars[i];
			break;
		}
	}

	switch (v->range_type) {
	    case RANGE_FILLED:
			return v->u.range.min;
		case RANGE_MIN_MAX:
			return v->u.range.max;
		case RANGE_NONE:
			return NULL;
		case RANGE_FRAGMENTS:
			f = v->u.fragments;
			while (f->next) {
				f = f->next;
			}
			return f->high;
		case RANGE_BITS:
			bits = v->u.bits.bits;
			i = -1;
			while (bits) {
				++i;
				bits >>= 1;
			}
			increment[1] = (unsigned)i;
			return _ex_intern_integer(_th_big_add(v->u.bits.base->u.integer,increment));
		default:
			fprintf(stderr, "Internal error: fd_get_max_value: Illegal range type\n");
			exit(1);
	}
}

struct _ex_intern *_fd_get_min_open(struct env *env, struct fd_handle *fd, unsigned var)
{
	int i;
    struct variable_info *v;

	for (i = 0; i < fd->var_count; ++i) {
		if (fd->vars[i].var==var) {
			v = &fd->vars[i];
			break;
		}
	}

	switch (v->range_type) {
	    case RANGE_FILLED:
		case RANGE_NONE:
		case RANGE_BITS:
			return NULL;
		case RANGE_MIN_MAX:
			if (v->u.range.min==NULL) {
				return v->u.range.max;
			} else {
				return NULL;
			}
		case RANGE_FRAGMENTS:
			if (v->u.fragments->low==NULL) {
				return v->u.fragments->high;
			} else {
				return NULL;
			}
		default:
			fprintf(stderr, "Internal error: fd_get_min_open: Illegal range type\n");
			exit(1);
	}
}

struct _ex_intern *_fd_get_max_open(struct env *env, struct fd_handle *fd, unsigned var)
{
	int i;
    struct variable_info *v;
    struct range_list *f;

	for (i = 0; i < fd->var_count; ++i) {
		if (fd->vars[i].var==var) {
			v = &fd->vars[i];
			break;
		}
	}

	switch (v->range_type) {
	    case RANGE_FILLED:
		case RANGE_NONE:
		case RANGE_BITS:
			return NULL;
		case RANGE_MIN_MAX:
			if (v->u.range.max==NULL) {
				return v->u.range.min;
			} else {
				return NULL;
			}
		case RANGE_FRAGMENTS:
			f = v->u.fragments;
			while (f->next) {
				f = f->next;
			}
			if (f->high==NULL) {
				return f->low;
			} else {
				return NULL;
			}
		default:
			fprintf(stderr, "Internal error: fd_get_max_open: Illegal range type\n");
			exit(1);
	}
}

