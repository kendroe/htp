/*
 * bitblast.c
 *
 * Routines to split up modulo variables.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */

#include <stdio.h>
#include <stdlib.h>
#include "Globals.h"
#include "Intern.h"

struct int_list {
	struct int_list *next;
	struct _ex_intern *factor;
};

struct variable_divisions {
	struct variable_divisions *next;
	unsigned var;
	struct int_list *list;
};

struct variable_divisions *insert_divisions(struct variable_divisions *divisions, unsigned var, struct int_list *parent_divisions)
{
    struct variable_divisions *d;
    struct int_list *p, *c, *n;

	//printf("*************** Inserting divisions %s\n", _th_intern_decode(var));
	d = divisions;
	while (d && d->var != var) {
		d = d->next;
	}
	if (!d) {
		//printf("DEFAULT CASE %x\n", parent_divisions);
		if (parent_divisions==NULL) return divisions;
		d = (struct variable_divisions *)_th_alloc(REWRITE_SPACE,sizeof(struct variable_divisions));
		d->next = divisions;
		d->list = parent_divisions;
		d->var = var;
		return d;
	}

	p = NULL;
	c = d->list;

	while (parent_divisions) {
		while (c && _th_big_less(c->factor->u.integer,parent_divisions->factor->u.integer)) {
			//printf("* Passing %s\n", _th_print_exp(c->factor));
			p = c;
			c = c->next;
		}
		if (!c || parent_divisions->factor != c->factor) {
		    n = (struct int_list *)_th_alloc(REWRITE_SPACE,sizeof(struct int_list));
		    n->next = c;
		    if (p) {
			    p->next = n;
			} else {
			    d->list = n;
			}
		    p = n;
			//printf("* Inserting %s\n", _th_print_exp(parent_divisions->factor));
		    n->factor = parent_divisions->factor;
		}

		parent_divisions = parent_divisions->next;
	}

	return divisions;
}

struct int_list *divide_parent_division(struct int_list *divisions, struct _ex_intern *e)
{
	struct int_list *ret, *p, *n;

	p = ret = NULL;

    if (_th_big_is_negative(e->u.integer)) {
        e = _ex_intern_integer(_th_complement(e->u.integer));
    }

	while (divisions != NULL) {
		unsigned *x = _th_big_mod(divisions->factor->u.integer,e->u.integer);
		if (x[0] != 1 || x[1] != 0) {
			x = _th_big_divide(divisions->factor->u.integer,e->u.integer);
			if (x[0] != 1 || x[1] != 0) {
			    n = (struct int_list *)_th_alloc(REWRITE_SPACE,sizeof(struct int_list));
			    n->factor = _ex_intern_integer(x);
			    n->next = NULL;
			    if (p) {
				    p->next = n;
				} else {
				    ret = n;
				}
			}
		}
		divisions = divisions->next;
	}

	return ret;
}

struct int_list *multiply_parent_division(struct int_list *divisions, struct _ex_intern *e)
{
	struct int_list *ret, *p, *n;

	p = ret = NULL;

    if (_th_big_is_negative(e->u.integer)) {
        e = _ex_intern_integer(_th_complement(e->u.integer));
    }

	while (divisions != NULL) {
		unsigned *x = _th_big_multiply(divisions->factor->u.integer,e->u.integer);
		n = (struct int_list *)_th_alloc(REWRITE_SPACE,sizeof(struct int_list));
		n->factor = _ex_intern_integer(x);
		n->next = NULL;
		if (p) {
			p->next = n;
		} else {
			ret = n;
		}
		p = n;
		divisions = divisions->next;
	}
	n = (struct int_list *)_th_alloc(REWRITE_SPACE,sizeof(struct int_list));
	n->next = ret;
	n->factor = e;

	return n;
}

struct int_list *insert_parent_division(struct int_list *divisions, struct _ex_intern *e)
{
	struct int_list *ret, *d, *p, *n;
    unsigned *x;

	//printf("ADDING %s\n", _th_print_exp(e));

	p = ret = NULL;
    d = divisions;
	//if (d != NULL) printf("head = %s\n", _th_print_exp(d->factor));
	while (d != NULL && _th_big_less(d->factor->u.integer,e->u.integer)) {
		//printf("    passing %s\n", _th_print_exp(d->factor));
		d = d->next;
	}
	if (d) {
		if (d->factor==e) return divisions;
		x = _th_big_mod(d->factor->u.integer,e->u.integer);
		if (x[0] != 1 || x[1] != 0) return divisions;
	}
	if (p) {
		x = _th_big_mod(e->u.integer,p->factor->u.integer);
		if (x[0] != 1 || x[1] != 0) return divisions;
	}

	//printf("    really inserting\n");
	n = (struct int_list *)_th_alloc(REWRITE_SPACE,sizeof(struct int_list));

	if (p) {
		p->next = n;
	} else {
		ret = n;
	}
	n->next = d;
	n->factor = e;

	return ret;
}

static struct _ex_intern *the_coef(struct _ex_intern *e)
{
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NAT_TIMES) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type==EXP_INTEGER) {
                return e->u.appl.args[i];
            }
        }
    } if (e->type==EXP_INTEGER) {
		return e;
	}
	return NULL;
}

struct int_list *insert_term_divisions(struct env *env, struct _ex_intern *e, struct int_list *list)
{
	struct _ex_intern *coef;
    int i;

	if (e->type != EXP_APPL) return list;

	switch (e->u.appl.functor) {
	    case INTERN_NAT_PLUS:
			for (i = 0; i < e->u.appl.count; ++i) {
				coef = the_coef(e->u.appl.args[i]);
				if (coef) {
                    if (_th_big_is_negative(coef->u.integer)) {
                        coef = _ex_intern_integer(_th_complement(coef->u.integer));
                    }
					list = insert_parent_division(list,coef);
				}
			}
			return list;
		case INTERN_NAT_TIMES:
			coef = the_coef(e);
			if (coef) {
                if (_th_big_is_negative(coef->u.integer)) {
                    coef = _ex_intern_integer(_th_complement(coef->u.integer));
                }
				return insert_parent_division(list, coef);
			}
	    default:
			return list;
	}
}

static int has_m_var(struct _ex_intern *e)
{
    int i;
    char *c;

    switch (e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                if (has_m_var(e->u.appl.args[i])) return 1;
            }
            return 0;
        case EXP_VAR:
            c = _th_intern_decode(e->u.var);
            if (c[0]=='m' && c[1]=='i') return 1;
        default:
            return 0;
    }
}

struct variable_divisions *compute_divisions(struct env *env, struct _ex_intern *e, struct int_list *parent_division, struct variable_divisions *divisions)
{
    int i;
    struct int_list *l = parent_division;

    //if (has_m_var(e)) {
    //    _tree_print_exp("computing divisions", e);
    //    _tree_indent();
    //    while (l != NULL) {
    //        _tree_print_exp("factor", l->factor);
    //        l = l->next;
    //    }
    //    _tree_undent();
    //}
	//printf("computing divisions %s\n", _th_print_exp(e));
	//printf("divisions = %x\n", divisions);
	//if (divisions) {
	//	printf("    %s %x\n", _th_intern_decode(divisions->var), divisions->list);
	//}
    //while (l != NULL) {
	//	printf("l = %s\n", _th_print_exp(l->factor));
	//	l = l->next;
	//}

	switch (e->type) {
	    case EXP_APPL:
			switch (e->u.appl.functor) {
			    case INTERN_NAT_PLUS:
				case INTERN_NAT_MINUS:
					for (i = 0; i < e->u.appl.count; ++i) {
						divisions = compute_divisions(env, e->u.appl.args[i], parent_division, divisions);
					}
					return divisions;
				case INTERN_NAT_TIMES:
					if (e->u.appl.count==2) {
						if (e->u.appl.args[0]->type==EXP_INTEGER) {
							return compute_divisions(env,e->u.appl.args[1],divide_parent_division(parent_division,e->u.appl.args[0]),divisions);
						} else if (e->u.appl.args[1]->type==EXP_INTEGER) {
							return compute_divisions(env,e->u.appl.args[0],divide_parent_division(parent_division,e->u.appl.args[1]),divisions);
						} else {
							goto def;
						}
					} else {
						goto def;
					}
				case INTERN_NAT_DIVIDE:
					if (e->u.appl.args[1]->type==EXP_INTEGER) {
						return compute_divisions(env,e->u.appl.args[0],multiply_parent_division(parent_division,e->u.appl.args[1]),divisions);
					} else if (e->u.appl.args[0]->type==EXP_INTEGER) {
						return compute_divisions(env,e->u.appl.args[1],multiply_parent_division(parent_division,e->u.appl.args[0]),divisions);
					} else {
						goto def;
					}
				case INTERN_NAT_MOD:
					if (e->u.appl.args[1]->type==EXP_INTEGER) {
						return compute_divisions(env,e->u.appl.args[0],insert_parent_division(parent_division,e->u.appl.args[1]),divisions);
					}
				case INTERN_NAT_LESS:
				case INTERN_EQUAL:
					parent_division = NULL;
					parent_division = insert_term_divisions(env,e->u.appl.args[0],parent_division);
					parent_division = insert_term_divisions(env,e->u.appl.args[1],parent_division);
					divisions = compute_divisions(env, e->u.appl.args[0],parent_division, divisions);
					divisions = compute_divisions(env, e->u.appl.args[1],parent_division, divisions);
					return divisions;
				case INTERN_ITE:
					divisions = compute_divisions(env, e->u.appl.args[0], NULL, divisions);
					divisions = compute_divisions(env, e->u.appl.args[1], parent_division, divisions);
					divisions = compute_divisions(env, e->u.appl.args[2], parent_division, divisions);
					return divisions;
				default:
def:
					for (i = 0; i < e->u.appl.count; ++i) {
						divisions = compute_divisions(env, e->u.appl.args[i], NULL, divisions);
					}
					return divisions;
			}
		case EXP_VAR:
			return insert_divisions(divisions, e->u.var, parent_division);
		default:
			return divisions;
	}
}

struct add_list *_th_get_not_equals(struct env *env, struct _ex_intern *var)
{
	struct rule *cr;
	struct _ex_intern *r = _th_get_first_context_rule(env, &cr);
    struct add_list *al = NULL, *a;

	var = _th_mark_vars(env, var);

	while (r) {
		if (r->type==EXP_APPL && r->u.appl.functor==INTERN_ORIENTED_RULE &&
			r->u.appl.args[1]==_ex_true && r->u.appl.args[2]==_ex_true) {
			r = r->u.appl.args[0];
			if (r->type==EXP_APPL && r->u.appl.functor==INTERN_NOT) {
				r = r->u.appl.args[0];
				if (r->type==EXP_APPL && r->u.appl.functor==INTERN_EQUAL ||
					r->u.appl.functor==INTERN_ORIENTED_RULE) {
					if (r->u.appl.args[0]==var &&
					    r->u.appl.args[1]->type==EXP_INTEGER) {
						a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
						a->next = al;
						al = a;
						a->e = r->u.appl.args[1];
					} else if (r->u.appl.args[1]==var && r->u.appl.args[0]->type==EXP_INTEGER) {
						a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
						a->next = al;
						al = a;
						a->e = r->u.appl.args[0];
					}
				}
			}
		}
		r = _th_get_next_rule(env, &cr);
	}

	return al;
}

struct _ex_intern *_th_bit_blast(struct env *env, struct _ex_intern *e)
{
	struct variable_divisions *divisions = compute_divisions(env,e,NULL,NULL);
    struct _ex_unifier *u = _th_new_unifier(REWRITE_SPACE);
    struct _ex_intern *na = e;
	struct _ex_intern *t, *l, *h, *up;
    struct int_list *f;
    unsigned v;
    unsigned one[2] = { 1, 1 };

	_tree_print_exp("Bit blasting", e);
    _tree_indent();

	while (divisions != NULL) {
		v = divisions->var;
		//printf("Var %s\n", _th_intern_decode(v));
		_tree_print1("var %s", _th_intern_decode(v));
		_tree_indent();
		l = _th_get_lower_bound(env,_ex_intern_var(v));
		h = _th_get_upper_bound(env,_ex_intern_var(v));
		if (h) h = _ex_intern_integer(_th_big_add(h->u.integer,one));
		//printf("lb = %s\n", _th_print_exp(l));
		//printf("ub = %s\n", _th_print_exp(h));
		//if (h != NULL) h = _ex_intern_integer(_th_big_sub(h->u.integer,one));
		_tree_print_exp("l", l);
		_tree_print_exp("h", h);
  		f = divisions->list;
		if (f->factor->u.integer[0]==1 && f->factor->u.integer[1]==1) {
			f = f->next;
		}
		if (f != NULL && l != NULL &&
			l->u.integer[0]==1 &&
			(l->u.integer[1]==0 || (l->u.integer[1] & 0x80000000)==0) &&
			(h==NULL || _th_big_less(f->factor->u.integer,h->u.integer))) {
			v = _th_name_away(na,divisions->var);
    		t = _ex_intern_var(v);
			na = _ex_intern_appl2_env(env,INTERN_TUPLE,_ex_intern_var(v),na);
			_th_derive_add_prepared(env,_th_derive_prepare(env,_ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(-1),_ex_intern_var(v))));
			if (h && _th_big_less(h->u.integer,f->factor->u.integer)) {
				_th_derive_add_prepared(env,_th_derive_prepare(env,_ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_var(v),h)));
			} else {
				_th_derive_add_prepared(env,_th_derive_prepare(env,_ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_var(v),f->factor)));
			}
    		while (f != NULL) {
				_tree_print_exp("Factor", f->factor);
				//printf("Factor %s\n", _th_print_exp(f->factor));
				if (f->next && (h==NULL || _th_big_less(f->next->factor->u.integer,h->u.integer))) {
					up = _ex_intern_integer(
						     _th_big_divide(f->next->factor->u.integer,f->factor->u.integer));
				} else {
					if (h==NULL) {
						up = NULL;
					} else {
						up = _ex_intern_integer(
						         _th_big_divide(h->u.integer,f->factor->u.integer));
					}
					//up = _ex_intern_integer(
					//	     _th_big_add(up->u.integer,one));
				}
				if ((up==NULL || _th_big_less(one,up->u.integer)) &&
					(h==NULL || _th_big_less(f->factor->u.integer,h->u.integer))) {
	    		    v = _th_name_away(na,divisions->var);
				    na = _ex_intern_appl2_env(env,INTERN_TUPLE,_ex_intern_var(v),na);
				    _th_derive_add_prepared(env,_th_derive_prepare(env,_ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(-1),_ex_intern_var(v))));
				    if (up) _th_derive_add_prepared(env,_th_derive_prepare(env,_ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_var(v),up)));
		    	    t = _ex_intern_appl2_env(env,INTERN_NAT_PLUS,t,_ex_intern_appl2_env(env,INTERN_NAT_TIMES,_ex_intern_var(v),f->factor));
				    //printf("t = %s\n", _th_print_exp(t));
				}
			    f = f->next;
			}
		    t = _th_flatten(env,t);
			_tree_print2("Substituting %s with %s", _th_intern_decode(divisions->var), _th_print_exp(t));
		    u = _th_add_pair(REWRITE_SPACE,u,divisions->var,t);
		}

		_tree_undent();
		divisions = divisions->next;
	}

	e = _th_subst(env,u,e);

	_tree_print_exp("Result", e);
	_tree_undent();

	return e;
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

static struct _ex_intern *_th_compute_max(struct env *env, struct _ex_intern *e);

static unsigned zero[2] = { 1, 0 }, one[2]  = { 1, 1 };

static struct _ex_intern *_th_compute_min(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *total, *r, *rm, *total_max, *lb;
	int i;

	if (e->type==EXP_INTEGER) {
		return e;
	} else {
        lb = _th_get_lower_bound(env,e);
	}

	switch (e->type) {
		case EXP_APPL:
			switch (e->u.appl.functor) {
			    case INTERN_NAT_PLUS:
					_zone_print0("plus min");
					_tree_indent();
					total = _th_compute_min(env,e->u.appl.args[0]);
					_tree_undent();
					_zone_print_exp("total =", total);
					if (total==NULL) return NULL;
					for (i = 1; i < e->u.appl.count; ++i) {
						_tree_indent();
						r = _th_compute_min(env,e->u.appl.args[i]);
						_tree_undent();
						_zone_print_exp("r =", r);
						if (r==NULL) return NULL;
						total = add_values(total, r);
					}
					if (total==NULL || (lb != NULL && _th_big_less(total->u.integer, lb->u.integer))) {
						return lb;
					} else {
					    return total;
					}
				case INTERN_NAT_TIMES:
					_zone_print0("times min");
					_tree_indent();
					total = _th_compute_min(env,e->u.appl.args[0]);
					total_max = _th_compute_max(env,e->u.appl.args[0]);
					_tree_undent();
					_zone_print_exp("total =", total);
					_zone_print_exp("total_max =", total_max);
					for (i = 1; i < e->u.appl.count; ++i) {
						if (total==NULL && total_max==NULL) return NULL;
						_tree_indent();
						r = _th_compute_min(env,e->u.appl.args[i]);
						rm = _th_compute_max(env,e->u.appl.args[i]);
						_tree_undent();
						_zone_print_exp("r =", r);
						_zone_print_exp("rm =", rm);
						multiply_ranges(env,r,total,rm,total_max);
						_zone_print_exp("res_min =", res_min);
						_zone_print_exp("res_max =", res_max);
						total = res_min;
						total_max = res_max;
					}
					if (total==NULL || (lb != NULL && _th_big_less(total->u.integer, lb->u.integer))) {
						return lb;
					} else {
					    return total;
					}
				case INTERN_NAT_MOD:
					if (e->u.appl.args[1]->type==EXP_INTEGER) {
						total = _th_compute_max(env,e->u.appl.args[0]);
						r = e->u.appl.args[1];
						if (_th_big_less(r->u.integer,one)) return lb;
						if (r==NULL || (total != NULL && _th_big_less(r->u.integer,total->u.integer))) {
							if (lb==NULL || (total != NULL && _th_big_less(lb->u.integer,total->u.integer))) {
								return total;
							} else {
								return lb;
							}
						} else {
							if (lb==NULL || (r != NULL && _th_big_less(lb->u.integer,r->u.integer))) {
								return r;
							} else {
								return lb;
							}
						}
					} else {
						return lb;
					}
				case INTERN_NAT_DIVIDE:
					_zone_print0("divide");
					_tree_indent();
					divide_ranges(env,_th_compute_min(env,e->u.appl.args[0]),
						              _th_compute_max(env,e->u.appl.args[0]),
						              _th_compute_min(env,e->u.appl.args[1]),
						              _th_compute_max(env,e->u.appl.args[1]));
					_tree_undent();
					if (res_min == NULL || (lb != NULL && _th_big_less(res_min->u.integer,lb->u.integer))) {
						return lb;
					} else {
					    return res_min;
					}
				default:
					return lb;
			}
		default:
			return lb;
	}
}

static struct _ex_intern *_th_compute_max(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *total, *r, *rm, *total_max, *ub;
	int i;

	if (e->type==EXP_INTEGER) {
		return e;
	} else {
        ub = _th_get_upper_bound(env,e);
	}

	switch (e->type) {
		case EXP_APPL:
			switch (e->u.appl.functor) {
			    case INTERN_NAT_PLUS:
					_zone_print0("plus max");
					_tree_indent();
					total = _th_compute_max(env,e->u.appl.args[0]);
					_tree_undent();
					_zone_print_exp("total =", total);
					if (total==NULL) return NULL;
					for (i = 1; i < e->u.appl.count; ++i) {
						_tree_indent();
						r = _th_compute_max(env,e->u.appl.args[i]);
						_tree_undent();
						_zone_print_exp("r =", r);
						if (r==NULL) return NULL;
						total = add_values(total, r);
					}
					if (total==NULL || (ub != NULL && _th_big_less(ub->u.integer,total->u.integer))) {
						return ub;
					} else {
					    return total;
					}
				case INTERN_NAT_TIMES:
					_zone_print0("compute times max");
					_tree_indent();
					total = _th_compute_min(env,e->u.appl.args[0]);
					total_max = _th_compute_max(env,e->u.appl.args[0]);
					_tree_undent();
					_zone_print_exp("total =", total);
					_zone_print_exp("total_max =", total_max);
					for (i = 1; i < e->u.appl.count; ++i) {
						if (total==NULL && total_max==NULL) return NULL;
						_tree_indent();
						r = _th_compute_min(env,e->u.appl.args[i]);
						rm = _th_compute_max(env,e->u.appl.args[i]);
						_tree_undent();
						_zone_print_exp("r =", r);
						_zone_print_exp("rm ", rm);
						multiply_ranges(env,r,total,rm,total_max);
						_zone_print_exp("res_min =", res_min);
						_zone_print_exp("res_max =", res_max);
						total = res_min;
						total_max = res_max;
					}
					if (total_max==NULL || (ub != NULL && _th_big_less(ub->u.integer,total_max->u.integer))) {
						return ub;
					} else {
					    return total_max;
					}
				case INTERN_NAT_MOD:
					if (e->u.appl.args[1]->type==EXP_INTEGER) {
						total = _th_compute_max(env,e->u.appl.args[0]);
						r = e->u.appl.args[1];
						if (_th_big_less(r->u.integer,one)) return ub;
						if (r==NULL || (total != NULL && _th_big_less(total->u.integer,r->u.integer))) {
							if (ub==NULL || (total != NULL && _th_big_less(total->u.integer,ub->u.integer))) {
								return total;
							} else {
								return ub;
							}
						} else {
							if (ub==NULL || (r != NULL && _th_big_less(r->u.integer,ub->u.integer))) {
								return r;
							} else {
								return ub;
							}
						}
					} else {
						return ub;
					}
				case INTERN_NAT_DIVIDE:
					_zone_print0("divide_ranges max");
					_tree_indent();
					divide_ranges(env,_th_compute_min(env,e->u.appl.args[0]),
						              _th_compute_max(env,e->u.appl.args[0]),
						              _th_compute_min(env,e->u.appl.args[1]),
						              _th_compute_max(env,e->u.appl.args[1]));
					_tree_undent();
					if (res_max==NULL || (ub != NULL && _th_big_less(ub->u.integer,res_max->u.integer))) {
						return ub;
					} else {
					    return res_max;
					}
				default:
					return ub;
			}
		default:
			return ub;
	}
}

int _th_rational_less(struct _ex_intern *a, struct _ex_intern *b)
{
    unsigned *tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(a->u.rational.numerator,b->u.rational.denominator));
    unsigned *tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(b->u.rational.numerator,a->u.rational.denominator));
    return _th_big_less(tmp1,tmp2);
}

struct _ex_intern *_th_divide_rationals(struct _ex_intern *a, struct _ex_intern *b)
{
	unsigned *tmp1, *tmp2, *accumulate;
    if (a->u.rational.numerator[0]==1 && a->u.rational.numerator[1]==0) {
        return a;
    }
    tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(a->u.rational.numerator,b->u.rational.denominator)) ;
    tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(b->u.rational.numerator,a->u.rational.denominator)) ;
    accumulate = _th_big_gcd(tmp1,tmp2) ;
    tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_divide(tmp1,accumulate)) ;
    tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_divide(tmp2,accumulate)) ;
    return _ex_intern_rational(tmp1,tmp2) ;
}

struct _ex_intern *_th_multiply_rationals(struct _ex_intern *a, struct _ex_intern *b)
{
	unsigned *tmp1, *tmp2, *accumulate;
    if (a->u.rational.numerator[0]==1 && a->u.rational.numerator[1]==0) {
        return a;
    }
    if (b->u.rational.numerator[0]==1 && b->u.rational.numerator[1]==0) {
        return b;
    }
    //_zone_print2("a %d %d", a->u.rational.numerator[0], a->u.rational.numerator[1]);
    //_zone_print2("b %d %d", b->u.rational.numerator[0], b->u.rational.numerator[1]);
    tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(a->u.rational.numerator,b->u.rational.numerator)) ;
    tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(b->u.rational.denominator,a->u.rational.denominator)) ;
    accumulate = _th_big_gcd(tmp1,tmp2) ;
    //_zone_print2("tmp1 %d %d", tmp1[0], tmp1[1]);
    //_zone_print2("tmp2 %d %d", tmp2[0], tmp2[1]);
    //_zone_print2("accumulate %d %d", accumulate[0], accumulate[1]);
    tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_divide(tmp1,accumulate)) ;
    tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_divide(tmp2,accumulate)) ;
    //_zone_print2("tmp1 %d %d", tmp1[0], tmp1[1]);
    //_zone_print2("tmp2 %d %d", tmp2[0], tmp2[1]);
    return _ex_intern_rational(tmp1,tmp2) ;
}

static int min_incl, max_incl;
static void r_multiply_ranges(struct env *env, struct _ex_intern *min1, struct _ex_intern *min2, struct _ex_intern *max1, struct _ex_intern *max2, int min1_incl, int min2_incl, int max1_incl, int max2_incl)
{
	_zone_print0("r_multiply ranges");
	_tree_indent();
	_zone_print_exp("min1 =", min1);
    _zone_print_exp("max1 =", max1);
	_zone_print_exp("min2 =", min2);
	_zone_print_exp("max2 =", max2);
    _tree_undent();

	if (min1 != NULL && max1 != NULL &&
        min1->u.rational.numerator[0]==1 && min1->u.rational.numerator[1]==0 &&
        max1->u.rational.numerator[0]==1 && max1->u.rational.numerator[1]==0) {
		res_min = res_max = _ex_intern_small_rational(0,1);
        min_incl = max_incl = (min1_incl & max1_incl);
    } else if (min2 != NULL && max2 != NULL &&
               min2->u.rational.numerator[0]==1 && min2->u.rational.numerator[1]==0 &&
               max2->u.rational.numerator[0]==1 && max2->u.rational.numerator[1]==0) {
		res_min = res_max = _ex_intern_small_rational(0,1);
        min_incl = max_incl = (min2_incl & max2_incl);
	} else if (min2==NULL && max2==NULL) {
		res_min = res_max = NULL;
	} else if (min1==NULL) {
		if (max1==NULL) {
			res_min = res_max = NULL;
		} else if (_th_big_is_negative(max1->u.rational.numerator)) {
			if (min2==NULL) {
				if (_th_big_is_negative(max2->u.rational.numerator)) {
					res_max = NULL;
					res_min = _th_multiply_rationals(max1,max2);
                    min_incl = (max1_incl && max2_incl);
				} else {
					res_min = res_max = NULL;
				}
			} else if (_th_big_is_negative(min2->u.rational.numerator)) {
				if ((max2 && max2->u.rational.numerator[0]==1 && max2->u.rational.numerator[1]==0) || _th_big_is_negative(max2->u.rational.numerator)) {
					res_max = NULL;
					res_min = _th_multiply_rationals(max1,max2);
                    min_incl = (max1_incl && max2_incl);
				} else {
					res_min = res_max = NULL;
				}
			}
		} else {
			if (min2==NULL || max2==NULL) {
				res_min = res_max = NULL;
			} else if (_th_big_is_negative(min2->u.rational.numerator) && _th_big_is_negative(max2->u.rational.numerator)) {
				res_max = NULL;
				res_min = _th_multiply_rationals(min2,max1);
                min_incl = (min2_incl && max1_incl);
			} else if (!_th_big_is_negative(min2->u.rational.numerator) && !_th_big_is_negative(max2->u.rational.numerator)) {
				res_min = NULL;
				res_max = _th_multiply_rationals(max1,max2);
                max_incl =(max1_incl && max2_incl);
			} else {
				res_min = res_max = NULL;
			}
		}
	} else if (_th_big_is_negative(min1->u.rational.numerator)) {
		if (max1==NULL) {
			if (min2==NULL || max2==NULL) {
				res_min = res_max = NULL;
			} else if (_th_big_is_negative(min2->u.rational.numerator) && _th_big_is_negative(max2->u.rational.numerator)) {
				res_min = NULL;
				res_max = _th_multiply_rationals(min2,min1);
                max_incl =(min1_incl && min2_incl);
			} else if (!_th_big_is_negative(min2->u.rational.numerator) && !_th_big_is_negative(max2->u.rational.numerator)) {
				res_max = NULL;
				res_min = _th_multiply_rationals(min1,max2);
                min_incl =(min1_incl && max2_incl);
			} else {
				res_min = res_max = NULL;
			}
		} else if (_th_big_is_negative(max1->u.rational.numerator)) {
			if (min2 != NULL) {
				if (_th_big_is_negative(min2->u.rational.numerator)) {
					res_max = _th_multiply_rationals(min2,max1);
                    max_incl =(min2_incl && max1_incl);
				} else {
					res_max = _th_multiply_rationals(min2,min1);
                    max_incl =(min2_incl && min1_incl);
				}
			} else {
				res_max = NULL;
			}
			if (max2 != NULL) {
				if (_th_big_is_negative(max2->u.rational.numerator)) {
					res_min = _th_multiply_rationals(max2,min1);
                    min_incl =(max2_incl && min1_incl);
				} else {
					res_min = _th_multiply_rationals(max2,max1);
                    min_incl =(max2_incl && max1_incl);
				}
			} else {
				res_min = NULL;
			}
		} else {
			if (min2==NULL || max2==NULL) {
				res_min = res_max = NULL;
			} else {
				if (_th_big_is_negative(min2->u.rational.numerator)) {
					if (_th_big_is_negative(max2->u.rational.numerator)) {
						res_min = _th_multiply_rationals(max1,min2);
						res_max = _th_multiply_rationals(min1,min2);
                        min_incl = (max1_incl && min2_incl);
                        max_incl = (min_incl && min2_incl);
					} else {
						struct _ex_intern *c1, *c2;
						c1 = _th_multiply_rationals(max1,max2);
						c2 = _th_multiply_rationals(min1,min2);
						if (_th_rational_less(c1,c2)) {
							res_max = c2;
                            max_incl = (min1_incl && min2_incl);
						} else {
							res_max = c1;
                            max_incl = (max1_incl && max2_incl);
						}
						c1 = _th_multiply_rationals(max1,min2);
						c2 = _th_multiply_rationals(min1,max2);
						if (_th_rational_less(c1,c2)) {
							res_min = c1;
                            min_incl = (max1_incl && min2_incl);
						} else {
							res_min = c2;
                            min_incl = (min1_incl && max2_incl);
						}
					}
				} else {
					res_min = _th_multiply_rationals(min1,max2);
					res_max = _th_multiply_rationals(max1,max2);
                    min_incl = (min1_incl && max2_incl);
                    max_incl = (max1_incl && max2_incl);
				}
			}
		}
	} else {
		if (max1==NULL) {
			if (min2 != NULL) {
				if (max2 != NULL) {
					if (_th_big_is_negative(min2->u.rational.numerator) && _th_big_is_negative(max2->u.rational.numerator)) {
						res_max = _th_multiply_rationals(min2,min1);
                        max_incl = (min2_incl && min1_incl);
						res_min = NULL;
					} else if (!_th_big_is_negative(min2->u.rational.numerator) && !_th_big_is_negative(max2->u.rational.numerator)) {
						res_max = NULL;
						res_min = _th_multiply_rationals(min2,min1);
                        min_incl = (min2_incl && min1_incl);
					} else {
						res_min = res_max = NULL;
					}
				} else {
					if (_th_big_is_negative(min2->u.rational.numerator)) {
						res_min = res_max = NULL;
					} else {
					    res_min = _th_multiply_rationals(min2,min1);
                        min_incl = (min2_incl && min1_incl);
                        res_max = NULL;
					}
				}
			} else {
				if (!_th_big_is_negative(max2->u.rational.numerator)) {
					res_min = res_max = NULL;
				} else {
				    res_max = _th_multiply_rationals(max2,min1);
                    max_incl = (max2_incl && min1_incl);
					res_min = NULL;
				}
			}
		} else {
			if (min2 != NULL) {
				if (_th_big_is_negative(min2->u.rational.numerator)) {
					res_min = _th_multiply_rationals(min2,max1);
                    min_incl = (min2_incl && max1_incl);
				} else {
					res_min = _th_multiply_rationals(min2,min1);
                    min_incl = (min2_incl && min1_incl);
				}
			}
			if (max2 != NULL) {
				if (_th_big_is_negative(max2->u.rational.numerator)) {
					res_max = _th_multiply_rationals(max2,min1);
                    max_incl = (max2_incl && min1_incl);
				} else {
					res_max = _th_multiply_rationals(max2,max1);
                    max_incl = (max2_incl & max1_incl);
				}
			}
		}
	}
}

static void r_divide_ranges(struct env *env, struct _ex_intern *min1, struct _ex_intern *max1, struct _ex_intern *min2, struct _ex_intern *max2, int min1_incl, int min2_incl, int max1_incl, int max2_incl)
{
    _zone_print_exp("divide min1", min1);
	_zone_print_exp("divide max1", max1);
	_zone_print_exp("divide min2", min2);
	_zone_print_exp("divide max2", max2);

    if (max2 != NULL && _th_big_is_negative(max2->u.rational.numerator) && (min2==NULL || _th_big_is_negative(min2->u.rational.numerator))) {
		if (min1==NULL) {
			res_max = NULL;
		} else {
		    res_max = _th_divide_rationals(min1, max2);
            max_incl = (min1_incl && max2_incl);
		}
		if (max1==NULL) {
			res_min = NULL;
		} else {
		    res_min = _th_divide_rationals(max1, max2);
            min_incl = (max1_incl && max2_incl);

		}
	} else if (min2 != NULL && !_th_big_is_negative(min2->u.rational.numerator) && (min2->u.rational.numerator[0] != 1 || min2->u.rational.numerator[1] != 0)) {
		if (min1==NULL) {
			res_min = NULL;
		} else {
		    res_min = _th_divide_rationals(min1, min2);
            min_incl = (min1_incl && min2_incl);
		}
		if (max1==NULL) {
			res_max = NULL;
		} else {
		    res_max = _th_divide_rationals(max1, min2);
            max_incl = (max1_incl && min2_incl);
		}
	} else {
		res_min = min1;
		res_max = max1;
	}
}

static struct _ex_intern *_th_compute_rmax(struct env *env, struct _ex_intern *e);

static struct _ex_intern *_th_compute_rmin(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *total, *r, *rm, *total_max, *lb;
    int mini, maxi, minii, maxii, min_inclusive;
	int i;

    if (e->type==EXP_RATIONAL) {
		return e;
	} else {
        lb = _th_get_lower_bound(env,e);
        min_inclusive = _th_inclusive;
	}

	switch (e->type) {
		case EXP_APPL:
			switch (e->u.appl.functor) {
			    case INTERN_RAT_PLUS:
					_zone_print0("plus min");
					_tree_indent();
					total = _th_compute_rmin(env,e->u.appl.args[0]);
                    mini = min_incl;
					_tree_undent();
					_zone_print_exp("total =", total);
					if (total==NULL) return NULL;
					for (i = 1; i < e->u.appl.count; ++i) {
						_tree_indent();
						r = _th_compute_rmin(env,e->u.appl.args[i]);
                        mini = (mini && min_incl);
						_tree_undent();
						_zone_print_exp("r =", r);
						if (r==NULL) return NULL;
						total = _th_add_rationals(total, r);
					}
                    min_incl = mini;
                    if (total==lb) {
                        min_incl = (min_incl && min_inclusive);
                        return lb;
                    } else if (total==NULL || (lb != NULL && _th_rational_less(total, lb))) {
                        min_incl = min_inclusive;
						return lb;
					} else {
					    return total;
					}
				case INTERN_RAT_TIMES:
					_zone_print0("times min");
					_tree_indent();
					total = _th_compute_rmin(env,e->u.appl.args[0]);
                    mini = min_incl;
					total_max = _th_compute_rmax(env,e->u.appl.args[0]);
                    maxi = max_incl;
					_tree_undent();
					_zone_print_exp("total =", total);
					_zone_print_exp("total_max =", total_max);
					for (i = 1; i < e->u.appl.count; ++i) {
						if (total==NULL && total_max==NULL) return NULL;
						_tree_indent();
						r = _th_compute_rmin(env,e->u.appl.args[i]);
                        minii = min_incl;
						rm = _th_compute_rmax(env,e->u.appl.args[i]);
                        maxii = max_incl;
						_tree_undent();
						_zone_print_exp("r =", r);
						_zone_print_exp("rm =", rm);
						r_multiply_ranges(env,r,total,rm,total_max,mini,maxi,minii,maxii);
                        mini = min_incl;
                        maxi = max_incl;
						_zone_print_exp("res_min =", res_min);
						_zone_print_exp("res_max =", res_max);
						total = res_min;
						total_max = res_max;
					}
                    min_incl = mini;
                    max_incl = maxi;
                    if (total==lb) {
                        min_incl = (min_incl && min_inclusive);
                        return lb;
                    } else if (total==NULL || (lb != NULL && _th_rational_less(total, lb))) {
                        min_incl = min_inclusive;
						return lb;
					} else {
					    return total;
					}
				case INTERN_RAT_DIVIDE:
					_zone_print0("divide");
					_tree_indent();
					total = _th_compute_rmin(env,e->u.appl.args[0]);
                    mini = min_incl;
					total_max = _th_compute_rmax(env,e->u.appl.args[0]);
                    maxi = max_incl;
				    r = _th_compute_rmin(env,e->u.appl.args[1]);
                    minii = min_incl;
				    rm = _th_compute_rmax(env,e->u.appl.args[1]);
                    maxii = max_incl;
					r_divide_ranges(env,total,total_max,r,rm,mini,maxi,minii,maxii);
					_tree_undent();
                    if (res_min==lb) {
                        min_incl = (min_incl && min_inclusive);
                        return lb;
                    } else if (res_min == NULL || (lb != NULL && _th_rational_less(res_min,lb))) {
                        min_incl = min_inclusive;
						return lb;
					} else {
					    return res_min;
					}
				default:
                    min_incl = min_inclusive;
					return lb;
			}
		default:
            min_incl = min_inclusive;
			return lb;
	}
}

static struct _ex_intern *_th_compute_rmax(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *total, *r, *rm, *total_max, *ub;
    int mini, maxi, minii, maxii, max_inclusive;
	int i;

	if (e->type==EXP_RATIONAL) {
		return e;
	} else {
        ub = _th_get_upper_bound(env,e);
        max_inclusive = _th_inclusive;
	}

	switch (e->type) {
		case EXP_APPL:
			switch (e->u.appl.functor) {
			    case INTERN_RAT_PLUS:
					_zone_print0("plus max");
					_tree_indent();
					total = _th_compute_rmax(env,e->u.appl.args[0]);
                    maxi = max_incl;
					_tree_undent();
					_zone_print_exp("total =", total);
					if (total==NULL) return NULL;
					for (i = 1; i < e->u.appl.count; ++i) {
						_tree_indent();
						r = _th_compute_rmax(env,e->u.appl.args[i]);
                        maxi = (maxi && max_incl);
						_tree_undent();
						_zone_print_exp("r =", r);
						if (r==NULL) return NULL;
						total = _th_add_rationals(total, r);
                    }
                    max_incl = maxi;
                    if (total==ub) {
                        max_incl = (max_incl && max_inclusive);
                        return ub;
                    } else if (total==NULL || (ub != NULL && _th_rational_less(ub,total))) {
                        max_incl = _th_inclusive;
						return ub;
					} else {
					    return total;
					}
				case INTERN_RAT_TIMES:
					_zone_print0("compute times max");
					_tree_indent();
					total = _th_compute_rmin(env,e->u.appl.args[0]);
                    mini = min_incl;
					total_max = _th_compute_rmax(env,e->u.appl.args[0]);
                    maxi = max_incl;
					_tree_undent();
					_zone_print_exp("total =", total);
					_zone_print_exp("total_max =", total_max);
					for (i = 1; i < e->u.appl.count; ++i) {
						if (total==NULL && total_max==NULL) return NULL;
						_tree_indent();
						r = _th_compute_rmin(env,e->u.appl.args[i]);
                        minii = min_incl;
						rm = _th_compute_rmax(env,e->u.appl.args[i]);
                        maxii = max_incl;
						_tree_undent();
						_zone_print_exp("r =", r);
						_zone_print_exp("rm ", rm);
						r_multiply_ranges(env,r,total,rm,total_max,mini,maxi,minii,maxii);
                        mini = min_incl;
                        maxi = max_incl;
						_zone_print_exp("res_min =", res_min);
						_zone_print_exp("res_max =", res_max);
						total = res_min;
						total_max = res_max;
					}
                    max_incl = maxi;
                    if (total_max==ub) {
                        max_incl = (max_incl && max_inclusive);
                        return ub;
                    } else if (total_max==NULL || (ub != NULL && _th_rational_less(ub,total_max))) {
                        max_incl = _th_inclusive;
						return ub;
					} else {
					    return total_max;
					}
				case INTERN_RAT_DIVIDE:
					_zone_print0("divide_ranges max");
					_tree_indent();
					total = _th_compute_rmin(env,e->u.appl.args[0]);
                    mini = min_incl;
			        total_max = _th_compute_rmax(env,e->u.appl.args[0]);
                    maxi = max_incl;
			        r = _th_compute_rmin(env,e->u.appl.args[1]);
                    minii = min_incl;
				    rm = _th_compute_rmax(env,e->u.appl.args[1]);
                    maxii = max_incl;
					r_divide_ranges(env,total,total_max,r,rm,mini,maxi,minii,maxii);
					_tree_undent();
                    if (res_max==ub) {
                        max_incl = (max_incl && max_inclusive);
                        return ub;
                    } else if (res_max==NULL || (ub != NULL && _th_rational_less(ub,res_max))) {
                        max_incl = _th_inclusive;
						return ub;
					} else {
					    return res_max;
					}
				default:
                    max_incl = _th_inclusive;
					return ub;
			}
		default:
            max_incl = _th_inclusive;
			return ub;
	}
}

struct _ex_intern *_th_process_mod(struct env *env, struct _ex_intern *e)
{
	int i, j, k;
    struct _ex_intern *f, *g;
    struct _ex_intern **args;
    struct _ex_intern *min, *max;

	if (e->u.appl.count != 2) return NULL;

	if (e->u.appl.args[1]->type != EXP_INTEGER) return NULL;

    f = e->u.appl.args[0];
	if (f->type==EXP_APPL) {
		switch (f->u.appl.functor) {
		    case INTERN_NAT_PLUS:
				args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * f->u.appl.count);
				j = 0;
				for (i = 0; i < f->u.appl.count; ++i) {
					if (f->u.appl.args[i]->type==EXP_INTEGER) {
						unsigned *r = _th_big_mod(f->u.appl.args[i]->u.integer,e->u.appl.args[1]->u.integer);
						if (r[0]==1 && r[1]==0) goto cont;
					} else if (f->u.appl.args[i]->type==EXP_APPL && f->u.appl.args[i]->u.appl.functor==INTERN_NAT_TIMES) {
						g = f->u.appl.args[i];
						for (k = 0; k < g->u.appl.count; ++k) {
							if (g->u.appl.args[k]->type==EXP_INTEGER) {
    						    unsigned *r = _th_big_mod(g->u.appl.args[k]->u.integer,e->u.appl.args[1]->u.integer);
	    				        if (r[0]==1 && r[1]==0) goto cont;
							}
						}
					}
					args[j++] = f->u.appl.args[i];
cont:;
				}
				if (j < i) return _ex_intern_appl2_env(env,INTERN_NAT_MOD,
					                  _ex_intern_appl_env(env,INTERN_NAT_PLUS,j,args),e->u.appl.args[1]);
				break;

			case INTERN_NAT_TIMES:
				for (i = 0; i < f->u.appl.count; ++i) {
					if (f->u.appl.args[i]->type==EXP_INTEGER) {
						unsigned *r = _th_big_mod(f->u.appl.args[i]->u.integer,e->u.appl.args[1]->u.integer);
						if (r[0]==1 && r[1]==0) return _ex_intern_small_integer(0);
					}
				}
				break;
		}
	}

	_zone_print_exp("Checking elimination of", e);
	_tree_indent();
	min = _th_compute_min(env,e->u.appl.args[0]);
	max = _th_compute_max(env,e->u.appl.args[0]);
	_zone_print_exp("min", min);
	_zone_print_exp("max =", max);
	_tree_undent();
	if (min != NULL && max != NULL && !_th_big_less(min->u.integer,zero) &&
		_th_big_less(max->u.integer,e->u.appl.args[1]->u.integer)) {
		return e->u.appl.args[0];
	}
	return NULL;
}

static struct _ex_intern *smallest_coef(struct _ex_intern *e)
{
	if (e==NULL) return NULL;
	if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NAT_PLUS) {
		int i;
		struct _ex_intern *s = NULL, *c;
		for (i = 0; i < e->u.appl.count; ++i) {
			c = the_coef(e->u.appl.args[i]);
			if (s==NULL ||_th_big_less(c->u.integer,s->u.integer)) {
				s = c;
			}
		}
		return s;
	} else {
		return the_coef(e);
	}
}

static int is_zero(unsigned *n)
{
	return n[0]==1 && n[1]==0;
}

static int all_divisible_by(struct _ex_intern *n, struct _ex_intern *e)
{
	if (e==NULL) return 1;
	if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NAT_PLUS) {
		int i;
		for (i = 0; i < e->u.appl.count; ++i) {
			struct _ex_intern *x = the_coef(e->u.appl.args[i]);
			if (!is_zero(_th_big_mod(x->u.integer,n->u.integer))) return 0;
		}
		return 1;
	}
	e = the_coef(e);
	return is_zero(_th_big_mod(e->u.integer,n->u.integer));
}

static struct _ex_intern *divide_by(struct env *env, struct _ex_intern *n, struct _ex_intern *e)
{
	struct _ex_intern *c;
	int i;
	struct _ex_intern **args;
	if (e==NULL) return NULL;
	if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NAT_PLUS) {
		args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
		for (i = 0; i < e->u.appl.count; ++i) {
			args[i] = divide_by(env,n,e->u.appl.args[i]);
			if (args[i]==NULL) return NULL;
		}
		return _ex_intern_appl_env(env,INTERN_NAT_PLUS,e->u.appl.count,args);
	}
	c = the_coef(e);
	if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NAT_TIMES) {
		args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
		for (i = 0; i < e->u.appl.count; ++i) {
			if (e->u.appl.args[i]->type==EXP_INTEGER) {
				args[i] = _ex_intern_integer(_th_big_divide(e->u.appl.args[i]->u.integer,n->u.integer));
			} else {
				args[i] = e->u.appl.args[i];
			}
		}
		return _ex_intern_appl_env(env,INTERN_NAT_TIMES,e->u.appl.count,args);
	} else if (e->type==EXP_INTEGER) {
		return _ex_intern_integer(_th_big_divide(e->u.integer,n->u.integer));
	} else {
		return NULL;
	}
}

struct _ex_intern *_th_equality_false_by_range(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *minl, *maxl, *minr, *maxr;

    if (_th_get_block_rule(env)) return NULL;

    minl = _th_compute_min(env,e->u.appl.args[0]);
	if (minl) {
		maxr = _th_compute_max(env,e->u.appl.args[1]);
		if (maxr && _th_big_less(maxr->u.integer,minl->u.integer)) return _ex_false;
	}

	minr = _th_compute_min(env,e->u.appl.args[1]);
	if (minr) {
		maxl = _th_compute_max(env,e->u.appl.args[0]);
		if (maxl && _th_big_less(maxl->u.integer,minr->u.integer)) return _ex_false;
	}

	return NULL;
}

struct _ex_intern *_th_r_equality_false_by_range(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *minl, *maxl, *minr, *maxr;
    int i1, i2;

    if (_th_get_block_rule(env)) return NULL;

    _zone_print0("_th_r_equality_false_by_range");
    _tree_indent();

	minl = _th_compute_rmin(env,e->u.appl.args[0]);
    _zone_print2("left min %d %s", min_incl, _th_print_exp(minl));
    i1 = min_incl;
	if (minl) {
		maxr = _th_compute_rmax(env,e->u.appl.args[1]);
        _zone_print2("right max %d %s", max_incl, _th_print_exp(maxr));
        i2 = max_incl;
        if (maxr && _th_rational_less(maxr,minl)) {
            _tree_undent();
            return _ex_false;
        }
        if (maxr==minl && (!i1 || !i2)) {
            _tree_undent();
            return _ex_false;
        }
	}

	minr = _th_compute_rmin(env,e->u.appl.args[1]);
    _zone_print2("right min %d %s", min_incl, _th_print_exp(minr));
    i1 = min_incl;
	if (minr) {
		maxl = _th_compute_rmax(env,e->u.appl.args[0]);
        i2 = max_incl;
        _zone_print2("left max %d %s", max_incl, _th_print_exp(maxl));
        if (maxl && _th_rational_less(maxl,minr)) {
            _tree_undent();
            return _ex_false;
        }
        if (maxl==minr && (!i1 || !i2)) {
            _tree_undent();
            return _ex_false;
        }
	}

    _tree_undent();
	return NULL;
}

struct _ex_intern *_th_simplify_nless_by_range(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *minl, *maxl, *minr, *maxr;

    if (_th_get_block_rule(env)) return NULL;

	minl = _th_compute_min(env,e->u.appl.args[0]);
	if (minl) {
		maxr = _th_compute_max(env,e->u.appl.args[1]);
		if (maxr && (maxr==minl || _th_big_less(maxr->u.integer,minl->u.integer))) return _ex_false;
	}

	minr = _th_compute_min(env,e->u.appl.args[1]);
	if (minr) {
		maxl = _th_compute_max(env,e->u.appl.args[0]);
        if (minr==maxl) return _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0],e->u.appl.args[1]));
		if (maxl && _th_big_less(maxl->u.integer,minr->u.integer)) return _ex_true;
	}

	return NULL;
}

struct _ex_intern *_th_simplify_rless_by_range(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *minl, *maxl, *minr, *maxr;
    int i1, i2;

    if (_th_get_block_rule(env)) return NULL;

    _zone_print_exp("_th_simplify_rless_by_range", e);
    _tree_indent();

	minl = _th_compute_rmin(env,e->u.appl.args[0]);
    _zone_print_exp("minl", minl);
    i1 = min_incl;
	if (minl) {
		maxr = _th_compute_rmax(env,e->u.appl.args[1]);
        _zone_print_exp("maxr", maxr);
        i2 = max_incl;
        _zone_print2("inclusives %d %d", i1, i2);
        if (maxr) {
            unsigned *tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(maxr->u.rational.numerator,minl->u.rational.denominator));
            unsigned *tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(minl->u.rational.numerator,maxr->u.rational.denominator));
            if (_th_big_less(tmp1,tmp2)) {
                _zone_print0("false");
                _tree_undent();
                return _ex_false;
            }
            if (minl==maxr) {
                _zone_print0("false");
                _tree_undent();
                return _ex_false;
            }
            //if (minl==maxr && i1 && i2) {
            //    struct _ex_intern *r = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0],e->u.appl.args[1]));
            //    _zone_print_exp("r", r);
            //    _tree_undent();
            //    return r;
            //}
        }
	}

	minr = _th_compute_rmin(env,e->u.appl.args[1]);
    _zone_print_exp("minr", minr);
    i1 = min_incl;
	if (minr) {
		maxl = _th_compute_rmax(env,e->u.appl.args[0]);
        _zone_print_exp("maxl", maxl);
        i2 = max_incl;
        if (maxl) {
            unsigned *tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(maxl->u.rational.numerator,minr->u.rational.denominator));
            unsigned *tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(minr->u.rational.numerator,maxl->u.rational.denominator));
            if (_th_big_less(tmp1,tmp2)) {
                _zone_print0("true");
                _tree_undent();
                return _ex_true;
            }
            if (minr==maxl && (!i1 || !i2)) {
                _zone_print0("true");
                _tree_undent();
                return _ex_true;
            }
            if (minr==maxl && i1 && i2) {
                struct _ex_intern *r = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0],e->u.appl.args[1]));
                _zone_print_exp("r", r);
                _tree_undent();
                return r;
            }
        }
	}

    _zone_print0("NULL");
    _tree_undent();
	return NULL;
}

struct _ex_intern *_th_pos_test_rless_by_range(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *minl, *maxl, *minr, *maxr;
    int i1, i2;

    if (_th_get_block_rule(env)) return NULL;

    _zone_print_exp("_th_pos_test_rless_by_range", e);
    _tree_indent();

	minr = _th_compute_rmin(env,e->u.appl.args[1]);
    _zone_print_exp("minr", minr);
    i1 = min_incl;
	if (minr) {
		maxl = _th_compute_rmax(env,e->u.appl.args[0]);
        _zone_print_exp("maxl", maxl);
        i2 = max_incl;
        if (maxl) {
            unsigned *tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(maxl->u.rational.numerator,minr->u.rational.denominator));
            unsigned *tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(minr->u.rational.numerator,maxl->u.rational.denominator));
            if (_th_big_less(tmp1,tmp2)) {
                _zone_print0("true");
                _tree_undent();
                return _ex_true;
            }
            if (minr==maxl && (!i1 || !i2)) {
                _zone_print0("true");
                _tree_undent();
                return _ex_true;
            }
            if (minr==maxl && i1 && i2) {
                struct _ex_intern *r = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0],e->u.appl.args[1]));
                _zone_print_exp("r", r);
                _tree_undent();
                return r;
            }
        }
	}

	minl = _th_compute_rmin(env,e->u.appl.args[0]);
    _zone_print_exp("minl", minl);
    i1 = min_incl;
	if (minl) {
		maxr = _th_compute_rmax(env,e->u.appl.args[1]);
        _zone_print_exp("maxr", maxr);
        i2 = max_incl;
        if (maxr) {
            unsigned *tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(maxr->u.rational.numerator,minl->u.rational.denominator));
            unsigned *tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(minl->u.rational.numerator,maxr->u.rational.denominator));
            if (_th_big_less(tmp1,tmp2)) {
                _zone_print0("false");
                _tree_undent();
                return _ex_false;
            }
            if (minl==maxr) {
                _zone_print0("false");
                _tree_undent();
                return _ex_false;
            }
            //if (minl==maxr && i1 && i2) {
            //    struct _ex_intern *r = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0],e->u.appl.args[1]));
            //    _zone_print_exp("r", r);
            //    _tree_undent();
            //    return r;
            //}
        }
	}

    _zone_print0("NULL");
    _tree_undent();
	return NULL;
}

static struct _ex_intern *replace_coef(struct env *env, struct _ex_intern *e, struct _ex_intern *coef)
{
    int i;
    struct _ex_intern **args;
    int c;

    if (e->type != EXP_APPL || e->u.appl.functor != INTERN_NAT_TIMES) {
        return _ex_intern_appl2_env(env,INTERN_NAT_TIMES,e,coef);
    }

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
    c = 0;
    for (i = 0; i < e->u.appl.count; ++i) {
        if (e->u.appl.args[i]->type==EXP_INTEGER) {
            args[i] = coef;
            c = 1;
        } else {
            args[i] = e->u.appl.args[i];
        }
    }
    if (c) {
        return _ex_intern_appl_env(env,INTERN_NAT_TIMES,e->u.appl.count,args);
    } else {
        return _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_NAT_TIMES,coef,e));
    }
}

static struct _ex_intern *delete_coef(struct env *env, struct _ex_intern *e)
{
    int i, j;
    struct _ex_intern **args;
    int c;

    if (e->type != EXP_APPL || e->u.appl.functor != INTERN_NAT_TIMES) {
        return e;
    }

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
    c = 0;
    for (i = 0, j = 0; i < e->u.appl.count; ++i) {
        if (e->u.appl.args[i]->type!=EXP_INTEGER) {
            args[j++] = e->u.appl.args[i];
        }
    }
    if (c) {
        return _ex_intern_appl_env(env,INTERN_NAT_TIMES,j,args);
    } else {
        return e;
    }
}

struct _ex_intern *_th_bit_blast_comparison(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *left, *leftb, *right, *rightb, *side, *l, *r;
    int i;
    //int attempt = 0;

	//_tree_core = 1;
	_zone_print_exp("bit_blast_comparison", e);
    _tree_indent();

	//if (e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_NAT_PLUS ||
	//	e->u.appl.args[1]->type==EXP_APPL && e->u.appl.args[1]->u.appl.functor==INTERN_NAT_PLUS) {
	//	printf("Attempting to simplify %s\n", _th_print_exp(e));
	//	attempt = 1;
	//}

    left = NULL;
    leftb = NULL;
    right = NULL;
    rightb = NULL;
	side = e->u.appl.args[0];
	if (side->type==EXP_APPL) {
		switch (side->u.appl.functor) {
		    case INTERN_NAT_PLUS:
				for (i = 0; i < side->u.appl.count; ++i) {
					_zone_print2("side->u.appl.args[%d] = %s", i, _th_print_exp(side->u.appl.args[i]));
					_zone_print_exp("coef", the_coef(side->u.appl.args[i]));
					if (l = the_coef(side->u.appl.args[i])) {
                        if (_th_big_is_negative(l->u.integer)) {
                            r = replace_coef(env,side->u.appl.args[i],_ex_intern_integer(_th_complement(l->u.integer)));
							rightb = _th_add_term(env,rightb,r);
                        } else {
                            leftb = _th_add_term(env,leftb,side->u.appl.args[i]);
                        }
					} else {
                        left = _th_add_term(env,left,side->u.appl.args[i]);
					}
					_zone_print_exp("leftb", leftb);
				}
				break;
			default:
				if ((l = the_coef(side))==NULL) {
					left = _th_add_term(env,NULL,side);
                } else if (_th_big_is_negative(l->u.integer)) {
                    l = _ex_intern_integer(_th_complement(l->u.integer));
                    if (l->u.integer[0]==1 && l->u.integer[1]==1) {
                        rightb = delete_coef(env,side);
                    } else {
                        rightb = replace_coef(env,side,l);
                    }
                } else {
					leftb = _th_add_term(env,NULL,side);
				}
		}
	} else if (side->type==EXP_INTEGER) {
		if (side->u.integer[0]==1 && (side->u.integer[1]==0 || side->u.integer[1]==1)) {
			left = _th_add_term(env,NULL,side);
		} else if (_th_big_is_negative(side->u.integer)) {
            side = _ex_intern_integer(_th_complement(side->u.integer));
            if (side->u.integer[0]==1 && side->u.integer[1]==1) {
                right = _th_add_term(env,NULL,side);
            } else {
                rightb = _th_add_term(env,NULL,side);
            }
        } else {
			leftb = _th_add_term(env,NULL,side);
		}
	} else {
		left = _th_add_term(env,NULL,side);
	}

	side = e->u.appl.args[1];
	if (side->type==EXP_APPL) {
		switch (side->u.appl.functor) {
		    case INTERN_NAT_PLUS:
				for (i = 0; i < side->u.appl.count; ++i) {
					if (l = the_coef(side->u.appl.args[i])) {
                        if (_th_big_is_negative(side->u.appl.args[i]->u.integer)) {
                            l = _ex_intern_integer(_th_complement(l->u.integer));
                            if (l->u.integer[0]==1 && l->u.integer[1]==1) {
                                r = delete_coef(env,side->u.appl.args[i]);
                                left = _th_add_term(env,left,r);
                            } else {
                                r = replace_coef(env,side->u.appl.args[i],l);
                                leftb = _th_add_term(env,leftb,r);
                            }
                        } else {
                            rightb = _th_add_term(env,rightb,side->u.appl.args[i]);
						}
					} else {
						if (right) {
							right = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,right,side->u.appl.args[i]));
						} else {
							right = side->u.appl.args[i];
						}
					}
				}
				break;
			default:
				if ((l = the_coef(side))==NULL) {
					right = _th_add_term(env,right,side);
				} else if (_th_big_is_negative(l->u.integer)) {
                    l = _ex_intern_integer(_th_complement(l->u.integer));
                    if (l->u.integer[0]==1 && l->u.integer[1]==1) {
                        side = delete_coef(env,side);
                        left = _th_add_term(env,left,side);
                    } else {
                        side = replace_coef(env,side,l);
                        leftb = _th_add_term(env,leftb,side);
                    }
                } else {
					rightb = _th_add_term(env,rightb,side);
				}
		}
	} else if (side->type==EXP_INTEGER) {
		if (side->u.integer[0]==1 && (side->u.integer[1]==0 || side->u.integer[1]==1)) {
			right = _th_add_term(env,right,side);
		} else if (_th_big_is_negative(side->u.integer)) {
            side = _ex_intern_integer(_th_complement(side->u.integer));
            if (side->u.integer[0]==1 && side->u.integer[1]==1) {
                left = _th_add_term(env,left,side);
            } else {
                leftb = _th_add_term(env,leftb,side);
            }
        } else {
			rightb = _th_add_term(env,rightb,side);
		}
	} else {
		right = _th_add_term(env,right,side);
	}

	_zone_print_exp("left", left);
	_zone_print_exp("leftb", leftb);
	_zone_print_exp("right", right);
	_zone_print_exp("rightb", rightb);

	while (leftb || rightb) {
		_zone_print_exp("left", left);
		_zone_print_exp("leftb", leftb);
		_zone_print_exp("right", right);
		_zone_print_exp("rightb", rightb);
		l = smallest_coef(leftb);
		r = smallest_coef(rightb);
		if (r && (l==NULL || _th_big_less(r->u.integer,l->u.integer))) {
			l = r;
		}
		if (all_divisible_by(l,leftb) && all_divisible_by(l,rightb)) {
			struct _ex_intern *minl, *maxl, *minr, *maxr;
			unsigned zero[2] = { 1, 0 };
			if (left != NULL) {
				minl = _th_compute_min(env,left);
				maxl = _th_compute_max(env,left);
			} else {
				minl = maxl = _ex_intern_small_integer(0);
			}
			if (right != NULL) {
				minr = _th_compute_min(env,right);
				maxr = _th_compute_max(env,right);
			} else {
				minr = maxr = _ex_intern_small_integer(0);
			}
			if (minl != NULL && maxl != NULL && minr != NULL && maxr != NULL &&
				!_th_big_less(minl->u.integer,zero) && !_th_big_less(minr->u.integer,zero) &&
				_th_big_less(maxl->u.integer,l->u.integer) &&
				_th_big_less(maxr->u.integer,l->u.integer)) {
				//printf("    leftb before = %s\n", _th_print_exp(leftb));
				//printf("    rightb before = %s\n", _th_print_exp(rightb));
				leftb = divide_by(env,l,leftb);
				rightb = divide_by(env,l,rightb);
				if (left==NULL) {
					left = _ex_intern_small_integer(0);
				}
				if (right==NULL) {
					right = _ex_intern_small_integer(0);
				}
				if (leftb==NULL) {
					leftb = _ex_intern_small_integer(0);
				}
				if (rightb==NULL) {
					rightb = _ex_intern_small_integer(0);
				}
				//printf("    Returning a value for %s\n", _th_print_exp(e));
				//printf("    left = %s\n", _th_print_exp(left));
				//printf("    leftb = %s\n", _th_print_exp(leftb));
				//printf("    right = %s\n", _th_print_exp(right));
				//printf("    rightb = %s\n", _th_print_exp(rightb));
				if (e->u.appl.functor==INTERN_NAT_LESS) {
					e = _ex_intern_appl2_env(env,INTERN_OR,
						       _ex_intern_appl2_env(env,INTERN_NAT_LESS,leftb,rightb),
							   _ex_intern_appl2_env(env,INTERN_AND,
							       _ex_intern_appl2_env(env,INTERN_EQUAL,leftb,rightb),
								   _ex_intern_appl2_env(env,INTERN_NAT_LESS,left,right)));
					_zone_print_exp("result", e);
					_tree_undent();
					return e;
				} else {
					e = _ex_intern_appl2_env(env,INTERN_AND,
						       _ex_intern_appl2_env(env,INTERN_EQUAL,left,right),
							   _ex_intern_appl2_env(env,INTERN_EQUAL,leftb,rightb));
					_zone_print_exp("result", e);
					_tree_undent();
					return e;
				}

			}
		}

		_zone_print_exp("l", l);
		
		if (leftb) {
			r = NULL;
			if (leftb->type==EXP_APPL && leftb->u.appl.functor==INTERN_NAT_PLUS) {
				for (i = 0; i < leftb->u.appl.count; ++i) {
					if (the_coef(leftb->u.appl.args[i])==l) {
						if (left) {
							left = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,left,leftb->u.appl.args[i]));
						} else {
							left = leftb->u.appl.args[i];
						}
					} else {
						if (r) {
							r = _th_flatten(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,r,leftb->u.appl.args[i]));
						} else {
							r = leftb->u.appl.args[i];
						}
					}
				}
				leftb = r;
			} else {
				if (the_coef(leftb)==l) {
					if (left) {
						left = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,left,leftb));
					} else {
						left = leftb;
					}
					leftb = NULL;
				} else {
					if (r) {
						r = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,r,leftb));
					} else {
						r = leftb;
					}
				}
			}
			leftb = r;
		}
		if (rightb) {
			r = NULL;
			if (rightb->type==EXP_APPL && rightb->u.appl.functor==INTERN_NAT_PLUS) {
				for (i = 0; i < rightb->u.appl.count; ++i) {
					if (the_coef(rightb->u.appl.args[i])==l) {
						if (right) {
							right = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,right,rightb->u.appl.args[i]));
						} else {
							right = rightb->u.appl.args[i];
						}
					} else {
						if (r) {
							r = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,r,rightb->u.appl.args[i]));
						} else {
							r = rightb->u.appl.args[i];
						}
					}
				}
				rightb = r;
			} else {
				if (the_coef(rightb)==l) {
					if (right) {
						right = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,right,rightb));
					} else {
						right = rightb;
					}
					rightb = NULL;
				} else {
					if (r) {
						r = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,r,rightb));
					} else {
						r = rightb;
					}
				}
			}
			rightb = r;
		}
	}

	//if (attempt && _tree_zone==324) exit(1);

	_zone_print0("No simplification");
	_tree_undent();
	return NULL;
}
