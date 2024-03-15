/*
 * crewrite.c
 *
 * Routines for maintaining the rewrite cache.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */

#include <stdio.h>
#include <stdlib.h>
#include "Globals.h"
#include "Intern.h"

struct rule_info {
	struct rule_info *next;
	struct _ex_intern *parent1;
	struct _ex_intern *parent2;
	struct add_list *rules;
} ;

#define RULE_HASH_SIZE 4001

struct rule_info *unary_rule_table[RULE_HASH_SIZE], *binary_rule_table[RULE_HASH_SIZE];

struct context_data {
	struct context_data *next;
	int count;
	struct _ex_intern **rules;
};

static struct env *benv;

void _th_crewrite_init()
{
    if (benv==NULL) {
        benv = _th_default_env(HEURISTIC_SPACE);
    }
}

static struct _ex_intern *prepare_rule(struct env *env, struct _ex_intern *rule)
{
	int i, j;
	struct _ex_intern **args;
	struct _ex_intern *r;
	struct _ex_intern *p = _th_derive_prepare(env,rule);

	if (p==NULL) return NULL;

	if (p->type==EXP_APPL && p->u.appl.functor==INTERN_AND) {
		args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * p->u.appl.count);
		for (i = 0, j = 0; i < p->u.appl.count; ++i) {
			args[j] = _th_augment_finite_rule(env,p->u.appl.args[i]);
			if (args[j] != p->u.appl.args[i]) {
				args[++j] = p->u.appl.args[i];
			}
			++j;
		}
		r = _ex_intern_appl_env(env,INTERN_AND,j,args);
	} else {
		r = _th_augment_finite_rule(env,p);
		if (r != p) r = _ex_intern_appl2_env(env,INTERN_AND,r,p);
	}

	//if (p != r) {
	//	_zone_print1("Rule: %s", _th_print_exp(rule));
	//	_zone_print1("changed to: %s", _th_print_exp(r));
	//	fprintf(stderr, "Rule changed: %s\n", _th_print_exp(p));
	//	fprintf(stderr, "          To: %s\n", _th_print_exp(r));
	//}

	return r;
}

static struct add_list *recursive_descendents(struct env *env, struct _ex_intern *rule, struct add_list *tail)
{
	struct add_list *adds = _th_unary_descendents(env,rule);
	struct add_list *a, *l, *p;
	struct _ex_intern *e;
    int i;

	if (rule->type==EXP_APPL && rule->u.appl.functor==INTERN_AND) {
		for (i = 0; i < rule->u.appl.count; ++i) {
    		e = _th_augment_finite_rule(env,rule->u.appl.args[i]);
	    	if (e != rule->u.appl.args[i]) {
		    	p = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
			    p->next = tail;
			    p->e = e;
			    tail = p;
			}
		}
	} else {
		e = _th_augment_finite_rule(env,rule);
		if (e != rule) {
			p = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
			p->next = tail;
			p->e = e;
			tail = p;
		}
	}
    a = adds;
	p = NULL;
	while (a != NULL) {
		l = tail;
		while (l != NULL) {
			if (l->e == a->e) break;
			l = l->next;
		}
		if (l) {
			if (p==NULL) {
				adds = a->next;
			} else {
				p->next = a->next;
			}
		} else {
		    p = a;
		}
		a = a->next;
	}

	a = adds;
	l = tail;
	while (a != NULL) {
		a->e = _th_derive_prepare(env,a->e);
		if (a->e) {
		    if (a->e->type==EXP_APPL && a->e->u.appl.functor==INTERN_AND) {
			    for (i = 0; i < a->e->u.appl.count; ++i) {
  				    l = recursive_descendents(env,a->e->u.appl.args[i],l);
				}
			} else {
		        l = recursive_descendents(env,a->e,l);
			}
		}
		a = a->next;
	}

	return l;
}

static int unary_cached = 1;

static struct add_list *generate_unary_descendents(struct env *env, struct _ex_intern *rule, struct add_list *tail)
{
	int hash = (((int)rule)/4)%RULE_HASH_SIZE;
    struct rule_info *r = unary_rule_table[hash];
    struct add_list *adds, *a, *ret, *ap;
    int i;

    unary_cached = 1;

	while (r != NULL) {
		if (r->parent1==rule) {
			break;
		}
		r = r->next;
	}

	if (r==NULL) {
		if (rule->type==EXP_APPL && rule->u.appl.functor==INTERN_AND) {
			adds = NULL;
			for (i = 0; i < rule->u.appl.count; ++i) {
			    adds = recursive_descendents(env,rule->u.appl.args[i],adds);
			}
		} else {
		    adds = recursive_descendents(env,rule,NULL);
		}
	    a = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
		a->next = adds;
		a->e = rule;
		adds = a;
		r = (struct rule_info *)_th_alloc(CACHE_SPACE,sizeof(struct rule_info));
		r->next = unary_rule_table[hash];
		unary_rule_table[hash] = r;
		r->parent1 = rule;
		r->parent2 = NULL;
		r->rules = adds;
		unary_cached = 0;
	}

	if (r->rules==NULL) {
        ret = tail;
	} else {
		adds = r->rules;
		ap = NULL;
		while (adds) {
			a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
			a->e = adds->e;
			if (ap) {
				ap->next = a;
			} else {
				ret = a;
			}
			adds = adds->next;
			ap = a;
		}
		a->next = tail;
	}

	return ret;
}


static struct add_list *binary_descendents(struct env *env, struct _ex_intern *rule1, struct _ex_intern *rule2)
{
	//_zone_print0("Binary descendents of %s", _th_print_exp(rule1));
	//_zone_print0("and %s", _th_print_exp(rule2));
	return _th_binary_descendents(env,rule1,rule2,NULL);
}

int rule_in_list(struct _ex_intern *r, struct add_list *l)
{
	while (l != NULL) {
		if (l->e==r) return 1;
		l = l->next;
	}
	return 0;
}

static struct add_list *recursive_binary_descendents(struct env *env, struct add_list *tail)
{
	struct add_list *new_list, *n, *l, *generated;
    struct _ex_intern *r;

	new_list = NULL;
	while (tail != NULL) {
		r = tail->e;
		//_zone_print0("Picking off %s", _th_print_exp(r));
		tail = tail->next;
		if (!rule_in_list(r,new_list)) {
			n = new_list;
			while (n != NULL) {
				generated = binary_descendents(env,r,n->e);
				l = generated;
				while (l != NULL) {
					struct _ex_intern *prep;
					if (l->e==_ex_false) {
                        _zone_print0("False in context");
						return NULL;
					}
					prep = _th_derive_prepare(env,l->e);
					//_zone_print_exp("before prepare", l->e);
					//_zone_print1("unary %s", _th_derive_prepare(env,l->e));
					if (prep) {
					    tail = generate_unary_descendents(env,prep,tail);
					}
					l = l->next;
				}
				//if (generated != NULL) {
				//	l = generated;
				//	while (l->next != NULL) {
				//		l = l->next;
				//	}
				//	l->next = tail;
				//	tail = generated;
				//}
				n = n->next;
			}
			l = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
			l->next = new_list;
			l->e = r;
			new_list = l;
		}
		n = new_list;
	}

	return new_list;
}

static struct add_list fail;

static struct add_list *generate_binary_descendents(struct env *env, struct _ex_intern *rule1, struct _ex_intern *rule2, struct add_list *tail)
{
	int hash = (((int)rule1)/4+((int)rule2)/4)%RULE_HASH_SIZE;
    struct rule_info *r = binary_rule_table[hash];
    struct add_list *adds, *a, *ret, *ap;
    int i;

	//_zone_print0("generate_binary_descendents of %s", _th_print_exp(rule1));
	//_zone_print0("and %s", _th_print_exp(rule2));

	//fprintf(stderr, "binary descendents of\n");
	//fprintf(stderr, "    %s\n", _th_print_exp(rule1));
	//fprintf(stderr, "    %s\n", _th_print_exp(rule2));
	while (r != NULL) {
		if ((r->parent1==rule1 && r->parent2==rule2) ||
			(r->parent1==rule2 && r->parent2==rule1)) {
			goto cont;
		}
		r = r->next;
	}

cont:
	if (r==NULL) {
		if (rule1->type==EXP_APPL && rule1->u.appl.functor==INTERN_AND) {
			adds = NULL;
			for (i = 0; i < rule1->u.appl.count; ++i) {
				a = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
				a->next = adds;
				a->e = rule1->u.appl.args[i];
				adds = a;
			}
		} else {
		    adds = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
			adds->next = NULL;
			adds->e = rule1;
		}
		if (rule2->type==EXP_APPL && rule2->u.appl.functor==INTERN_AND) {
			for (i = 0; i < rule2->u.appl.count; ++i) {
				a = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
				a->next = adds;
				a->e = rule2->u.appl.args[i];
				adds = a;
			}
		} else {
		    a = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
			a->next = adds;
			a->e = rule2;
			adds = a;
		}
		//_zone_print0("Initial recursive descent");
		adds = recursive_binary_descendents(env,adds);
		r = (struct rule_info *)_th_alloc(CACHE_SPACE,sizeof(struct rule_info));
		r->next = binary_rule_table[hash];
		binary_rule_table[hash] = r;
		r->parent1 = rule1;
		r->parent2 = rule2;
		r->rules = adds;
	//} else {
	//	fprintf(stderr, "    cache hit\n");
	}
	//fflush(stderr);

	if (r->rules==NULL) {
        return &fail;
	} else {
		adds = r->rules;
		ap = NULL;
		while (adds) {
			if (!rule_in_list(adds->e,tail)) {
			    a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
			    a->e = adds->e;
			    if (ap) {
				    ap->next = a;
				} else {
				    ret = a;
				}
    			ap = a;
			}
			adds = adds->next;
		}
		if (ap) {
		    a->next = tail;
		} else {
			ret = tail;
		}
	}

	return ret;
}

static int not_smaller_sym(struct env *env, unsigned functor, struct _ex_intern *exp)
{
	int i;
	switch (exp->type) {
	    case EXP_APPL:
			if (_th_has_equal_precedence(env,functor,exp->u.appl.functor)) return 0;
			if (_th_has_smaller_precedence(env,functor,exp->u.appl.functor)) return 0;
			for (i = 0; i < exp->u.appl.count; ++i) {
				if (!not_smaller_sym(env,functor,exp->u.appl.args[i])) return 0;
			}
			return 1;
	    default:
			return 1;
	}
}

static int has_not_smaller_precedence(struct env *env, struct _ex_intern *rule, struct _ex_intern *exp)
{
	int i;
	switch (rule->type) {
	    case EXP_APPL:
			if (not_smaller_sym(env, rule->u.appl.functor, exp)) return 1;
			for (i = 0; i < rule->u.appl.count; ++i) {
				if (has_not_smaller_precedence(env, rule->u.appl.args[i], exp)) return 1;
			}
			return 0;
	    case EXP_VAR:
		case EXP_INTEGER:
		case EXP_RATIONAL:
		case EXP_STRING:
		case EXP_MARKED_VAR:
			return 0;
		default:
			return 1;
	}
}

int _th_has_complex_term(struct _ex_intern *exp, int level)
{
    int i;

    if (level==0) return 1;

    switch (exp->type) {
        case EXP_APPL:
            switch (exp->u.appl.functor) {
                case INTERN_ITE:
                //case INTERN_NOT:
                case INTERN_AND:
                case INTERN_OR:
                case INTERN_XOR:
                    return 1;
            }
            for (i = 0; i < exp->u.appl.count; ++i) {
                if (_th_has_complex_term(exp->u.appl.args[i],level-1)) return 1;
            }
            return 0;
        case EXP_QUANT:
            switch (exp->u.quant.quant) {
                case INTERN_EXISTS:
                case INTERN_ALL:
                    return 1;
                default:
                    return _th_has_complex_term(exp->u.quant.exp,level-1) ||
                           _th_has_complex_term(exp->u.quant.cond,level-1);
            }
        default:
            return level<=1;
    }
}

struct _ex_intern *_th_eliminate_var(struct env *env, struct _ex_intern *exp)
{
    struct _ex_intern *r;
    unsigned *fv, *fvar;
    int count, i, v, c;
    struct _ex_unifier *u;
    struct var_solve_list *cr;
    
    if (_th_get_block_rule(env) != NULL) return NULL;

    _zone_print_exp("Eliminating var from", exp);
    if (exp->type==EXP_APPL &&
        (exp->u.appl.functor==INTERN_ITE || exp->u.appl.functor==INTERN_AND || exp->u.appl.functor==INTERN_OR ||
         exp->u.appl.functor==INTERN_NOT)) return NULL;
    if (_th_has_complex_term(exp,7)) return NULL;

    fv = _th_get_free_vars(exp,&count);
    fvar = (unsigned *)ALLOCA(sizeof(unsigned) * count);
    for (i = 0; i < count; ++i) fvar[i] = fv[i];
    for (v = 0; v < count; ++v) {
        r = _th_get_first_rule_by_var_solve(env, fvar[v], &cr);
        _tree_indent();
        while (r != NULL) {
            _zone_print_exp("Really testing rule", r);
            r = _th_unmark_vars(env,r);
            fv  = _th_get_free_vars(r,&c);
            //_zone_print0("Here4");
            for (i = 0; i < c; ++i) {
                if (!_th_is_free_in(exp,fv[i])) goto cont;
            }
            //_zone_print0("Here5");
            if (has_not_smaller_precedence(env,r,exp)) goto cont;
            //_zone_print0("Here6");
            u = _th_new_unifier(REWRITE_SPACE);
            u = _th_add_pair(REWRITE_SPACE,u,fvar[v],r);
            exp = _th_subst(env,u,exp);
            _zone_print_exp("Good", exp);
            _tree_undent();
            return exp;
cont:
            r = _th_get_next_rule_by_var_solve(fvar[v], &cr);
        }
        _tree_undent();
    }
    _zone_print0("None");
    return NULL;
}

struct _ex_intern *_th_strengthen_in_context(struct env *env, struct _ex_intern *e)
{
    if (_th_is_binary_term(env,e) && _th_get_block_rule(env)==NULL) {
        struct rule_double_operand_list *cr;
        struct _ex_intern *left;
        struct _ex_intern *right;
        struct _ex_intern *r;
        struct _ex_intern *res;
        struct _ex_intern *exp;
        _zone_print_exp("Testing strengthen", e);
        _tree_indent();
        exp = NULL;
        left = _th_get_left_operand(env,e);
        right = _th_get_right_operand(env,e);
        _zone_print_exp("left", left);
        _zone_print_exp("right", right);
        r = _th_get_first_rule_by_operands(env, left, right, &cr);
        while (r) {
            _zone_print_exp("Testing", r);
            if (!exp) exp = _th_mark_vars(env,e);
            r = _th_extract_relation(env,r);
            res = _th_strengthen_term(env,r,exp);
            if (res) {
                _tree_undent();
                _zone_print_exp("res", res);
                _zone_print_exp("strengthened with", r);
                return _th_unmark_vars(env,res);
            }
            r = _th_get_next_rule_by_operands(left, right, &cr);
        }
        _tree_undent();
    }
    return _th_eliminate_var(env,e);
}

static void after_check(struct env *env);

static int has_subterm(struct _ex_intern *e, struct _ex_intern *s)
{
    int i;

    if (e==s) return 1;

    switch (e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                if (has_subterm(e->u.appl.args[i],s)) return 1;
            }
            return 0;
        default:
            return 0;
    }
}

static struct _ex_intern *check_for_reduction(struct env *env, struct _ex_intern *e, struct _ex_intern *left, struct _ex_intern *right)
{
    struct _ex_intern **args, *c, *d;
    int r;
    int i;

    //_zone_print_exp("Check for reduction", e);
    //_tree_indent();
    //_zone_print_exp("left", left);
    //_zone_print_exp("right", right);

    if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_NAT_LESS || e->u.appl.functor==INTERN_RAT_LESS) &&
        left->type==EXP_APPL && left->u.appl.functor==e->u.appl.functor) {
        if (right==_ex_true) {
            if (e->u.appl.args[0]==left->u.appl.args[1]) {
                if (e->u.appl.args[1]->type==EXP_RATIONAL && left->u.appl.args[0]->type==EXP_RATIONAL &&
                    (e->u.appl.args[1]==left->u.appl.args[0] || _th_rational_less(e->u.appl.args[1],left->u.appl.args[0]))) {
                    return _ex_false;
                } else if (e->u.appl.args[1]->type==EXP_INTEGER && left->u.appl.args[0]->type==EXP_INTEGER &&
                    (e->u.appl.args[1]==left->u.appl.args[0] || _th_big_less(e->u.appl.args[1]->u.integer,left->u.appl.args[0]->u.integer))) {
                    return _ex_false;
                }
            } else if (e->u.appl.args[1]==left->u.appl.args[0]) {
                if (e->u.appl.args[0]->type==EXP_RATIONAL && left->u.appl.args[1]->type==EXP_RATIONAL &&
                    (e->u.appl.args[0]==left->u.appl.args[1] || _th_rational_less(left->u.appl.args[1],e->u.appl.args[0]))) {
                    return _ex_false;
                } else if (e->u.appl.args[0]->type==EXP_INTEGER && left->u.appl.args[1]->type==EXP_INTEGER &&
                    (e->u.appl.args[0]==left->u.appl.args[1] || _th_big_less(left->u.appl.args[1]->u.integer,e->u.appl.args[0]->u.integer))) {
                    return _ex_false;
                }
            }
        } else if (right==_ex_false) {
            if (e->u.appl.args[0]==left->u.appl.args[0]) {
                if (e->u.appl.args[1]->type==EXP_RATIONAL && left->u.appl.args[1]->type==EXP_RATIONAL &&
                    _th_rational_less(e->u.appl.args[1],left->u.appl.args[1])) {
                    return _ex_false;
                } else if (e->u.appl.args[1]->type==EXP_INTEGER && left->u.appl.args[1]->type==EXP_INTEGER &&
                    _th_big_less(e->u.appl.args[1]->u.integer,left->u.appl.args[1]->u.integer)) {
                    return _ex_false;
                }
            } else if (e->u.appl.args[1]==left->u.appl.args[1]) {
                if (e->u.appl.args[0]->type==EXP_RATIONAL && left->u.appl.args[0]->type==EXP_RATIONAL &&
                    _th_rational_less(left->u.appl.args[0],e->u.appl.args[0])) {
                    return _ex_false;
                } else if (e->u.appl.args[0]->type==EXP_INTEGER && left->u.appl.args[0]->type==EXP_INTEGER &&
                    _th_big_less(left->u.appl.args[0]->u.integer,e->u.appl.args[0]->u.integer)) {
                    return _ex_false;
                }
            }
        }
    }

    if ((right==_ex_true || right==_ex_false) && (left->u.appl.functor==INTERN_NAT_LESS || left->u.appl.functor==INTERN_RAT_LESS)) {
        if (left->u.appl.args[0]->type==EXP_INTEGER || left->u.appl.args[0]->type==EXP_RATIONAL &&
            e==left->u.appl.args[1]) {
            return NULL;
        } else if (left->u.appl.args[1]->type==EXP_INTEGER || left->u.appl.args[1]->type==EXP_RATIONAL &&
            e==left->u.appl.args[0]) {
            return NULL;
        }
    }

    if (right==_ex_false && left->type==EXP_APPL && left->u.appl.functor==INTERN_EQUAL) {
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_SELECT) {
            struct _ex_intern *f = e->u.appl.args[0];
            if (f->type==EXP_APPL && f->u.appl.functor==INTERN_STORE) {
                if ((left->u.appl.args[0]==e->u.appl.args[1] && left->u.appl.args[1]==f->u.appl.args[1]) ||
                    (left->u.appl.args[0]==f->u.appl.args[1] && left->u.appl.args[1]==e->u.appl.args[1])) {
                    //_zone_print0("Reduced");
                    //_tree_undent();
                    return _ex_intern_appl2_env(env,INTERN_SELECT,f->u.appl.args[0],e->u.appl.args[1]);
                }
            }
        }
    }

    if (e==left) {
        //_zone_print0("Reduced");
        //_tree_undent();
        return right;
    }

    switch (e->type) {
        case EXP_APPL:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            r = 0;
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = check_for_reduction(env,e->u.appl.args[i],left,right);
                if (args[i]==NULL) return NULL;
                if (args[i]!=e->u.appl.args[i]) r = 1;
            }
            if (r) {
                struct _ex_intern *e1 = _ex_intern_appl_equal_env(env,e->u.appl.functor,e->u.appl.count,args, e->type_inst);
                //if (e1->type_inst==NULL) e1->type_inst = e->type_inst;
                e1 = _th_flatten_top(env,e1);
                e = e1;
            }
            //_tree_undent();
            return e;
        case EXP_QUANT:
            c = check_for_reduction(env,e->u.quant.cond,left,right);
            if (c==NULL) return NULL;
            d = check_for_reduction(env,e->u.quant.exp,left,right);
            if (d==NULL) return NULL;
            if (c != e->u.quant.cond || d != e->u.quant.exp) e = _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,e->u.quant.vars,d,c);
            //_tree_undent();
            return e;
        default:
            //_tree_undent();
            return e;
    }
}

int has_free_vars(struct _ex_intern *e)
{
    // int c;

    return e != _ex_true && e != _ex_false && e->type != EXP_INTEGER && e->type != EXP_RATIONAL;

    //_th_get_free_vars(e, &c);
    //return c > 0;
}

struct _ex_intern *_th_can_impact(struct env *env, struct _ex_intern *e1, struct _ex_intern *e2)
{
    struct _ex_intern *r, *e, *e2o;
    int i;

    //printf("Checking impact %s\n", _th_print_exp(e1));
    //printf("and %s\n", _th_print_exp(e2));
    //fflush(stdout);

    _zone_print_exp("Checking impact", e1);
    _zone_print_exp("on", e2);
    _tree_indent();

    if (e1->type==EXP_VAR) {
        _tree_undent();
        return 0;
    }
    if (e2->type==EXP_VAR) {
        _tree_undent();
        return 0;
    }

    //_zone_print_exp("can_impact e1", e1);
    //_zone_print_exp("can_impact e2", e2);

    r = NULL;
    if (e1->type==EXP_APPL && e1->u.appl.functor==INTERN_EQUAL) {
        r = _th_derive_prepare(env,_th_mark_vars(env,e1));
        //if (e1->type==EXP_APPL && e1->u.appl.functor==INTERN_EQUAL) {
        //    _tree_print_exp("e1",e1);
        //    _tree_print_exp("r", r);
        //    _tree_print_exp("e2", e2);
        //}
        e2o = e2;
        e2 = _th_mark_vars(env,e2);
        
        if (r->u.appl.functor==INTERN_AND) {
            for (i = 0; i < r->u.appl.count; ++i) {
                if (r->u.appl.args[i]->u.appl.args[2]==_ex_true) {
                    e = check_for_reduction(env,e2,r->u.appl.args[i]->u.appl.args[0],r->u.appl.args[i]->u.appl.args[1]);
                    if (e != e2) {
                        if (e==NULL) e = e2;
                        //_zone_print0("ret1");
                        _tree_undent();
                        _zone_print_exp("impact 1", e);
                        return _th_unmark_vars(env,e);
                    }
                }
            }
        } else if (r->u.appl.args[2]==_ex_true) {
            e = check_for_reduction(env,e2,r->u.appl.args[0],r->u.appl.args[1]);
            if (e != e2) {
                if (e==NULL) e = e2;
                //_zone_print0("ret2");
                _tree_undent();
                _zone_print_exp("impact 2", e);
                return _th_unmark_vars(env,e);
            }
        }
        e2 = e2o;
    }    

    if (e1->type==EXP_APPL && (e1->u.appl.functor==INTERN_RAT_LESS || e1->u.appl.functor==INTERN_NAT_LESS)) {
        int count;
        unsigned *f = _th_get_free_vars(e1,&count);
        if (count > 0) {
            struct _ex_intern **fv = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
            for (i = 0; i < count; ++i) {
                fv[i] = _ex_intern_var(f[i]);
            }
            qsort(fv,count,sizeof(struct _ex_intern *),_th_term_cmp);
            if (_th_is_free_in(e2,fv[0]->u.var)) {
                _tree_undent();
                _zone_print_exp("impact 3", e2);
                return e2;
            }
        }
    }

    if (_th_is_binary_term(env,e1) && _th_is_binary_term(env,e2)) {
        struct _ex_intern *l1 = _th_get_left_operand(env,e1);
        struct _ex_intern *l2 = _th_get_left_operand(env,e2);
        struct _ex_intern *r1 = _th_get_right_operand(env,e1);
        struct _ex_intern *r2 = _th_get_right_operand(env,e2);
        if ((l1==l2 && has_free_vars(l1)) || (r1==l2 && has_free_vars(r1)) || (l1==r2 && has_free_vars(l1)) || (r1==r2 && has_free_vars(r1))) {
            if (((l1==l2 || (l1->type==EXP_INTEGER && l2->type==EXP_INTEGER) || (l1->type==EXP_RATIONAL && l2->type==EXP_RATIONAL)) &&
                 (r1==r2 || (r1->type==EXP_INTEGER && r2->type==EXP_INTEGER) || (r1->type==EXP_RATIONAL && r2->type==EXP_RATIONAL))) ||
                ((l1==r2 || (l1->type==EXP_INTEGER && r2->type==EXP_INTEGER) || (l1->type==EXP_RATIONAL && r2->type==EXP_RATIONAL)) &&
                 (r1==l2 || (r1->type==EXP_INTEGER && l2->type==EXP_INTEGER) || (r1->type==EXP_RATIONAL && l2->type==EXP_RATIONAL)))) {
                _zone_print0("Both sides equal");
                _th_derive_push(env);
                if (r==NULL) r = _th_derive_prepare(env,_th_mark_vars(env,e1));
                _th_derive_add_prepared(env,r);
                e = _th_nc_rewrite(env,_th_unmark_vars(env,e2));
                _th_derive_pop(env);
                //_zone_print0("ret3");
                _tree_undent();
                _zone_print_exp("impact 3", e);
                return e;
            } else {
                //_zone_print0("ret4");
                _tree_undent();
                _zone_print_exp("impact 4", e2);
                return NULL;
            }
        }
    }

    _tree_undent();
    _zone_print0("no impact");
    return NULL;
}

static struct _ex_intern *done_list;

void check_x43(struct _ex_intern *e, int pos)
{
    _zone_print_exp("Checking x43", e);
    _zone_print1("pos %d", pos);
#ifndef FAST
    //printf("Checking %d %d %s\n", pos, _tree_zone, _th_print_exp(e));
#endif
    //if (e->type != EXP_APPL || e->u.appl.functor != INTERN_EQUAL) return;

    //if (e->u.appl.args[1]->type != EXP_INTEGER || e->u.appl.args[1]->u.integer[0] != 1 ||
    //    e->u.appl.args[1]->u.integer[1] != 1) return;

    //if (e->u.appl.args[0]->type != EXP_VAR || strcmp(_th_intern_decode(e->u.var),"x_43")) return;

    //printf("Marking x_43\n");
    //exit(1);
}

static struct _ex_intern *slack1, *slack2;
static int add_slack(struct env *env, struct _ex_intern *e)
{
    //fprintf(stderr, "Adding slack to %s\n", _th_print_exp(e));
    //fflush(stderr);

    struct add_list *l = _th_basic_terms(e,NULL);

    while (l) {
        if (!_th_is_slack(l->e)) goto cont;
        l = l->next;
    }
    return 0;

    //fv = _th_get_free_vars(e,&count);
    //for (i = 0; i < count; ++i) {
    //    if (!_th_is_slack(_ex_intern_var(fv[i]))) goto cont;
    //}
    //fv = _th_get_marked_vars(e,&count);
    //for (i = 0; i < count; ++i) {
    //    if (!_th_is_slack(_ex_intern_var(fv[i]))) goto cont;
    //}
    //return 0;

cont:
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_ORIENTED_RULE) {
        if (e->u.appl.args[1]==_ex_true && e->u.appl.args[2]==_ex_true) {
            e = e->u.appl.args[0];
        } else if (e->u.appl.args[1]==_ex_false && e->u.appl.args[2]==_ex_false) {
            e = _ex_intern_appl1_env(env,INTERN_NOT,e->u.appl.args[0]);
        } else {
            return 0;
        }
    }

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_LESS) {
        struct _ex_intern *l = e->u.appl.args[0];
        struct _ex_intern *r = e->u.appl.args[1];
        struct _ex_intern *sv;
        if ((_th_is_variable_term(l) && r->type==EXP_RATIONAL) ||
            (l->type==EXP_RATIONAL && _th_is_variable_term(r))) {
            return 0;
        }
        sv = _ex_intern_marked_var(_th_new_slack(env),0);
        slack1 = _ex_intern_appl2_env(env,INTERN_RAT_LESS,_ex_intern_small_rational(0,1),sv);
        slack1 = _th_mark_vars(env,_th_nc_rewrite(benv,_th_unmark_vars(env,slack1)));
        slack2 = _ex_intern_equal(env,_ex_real,_th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_RAT_PLUS,l,sv)),r);
        slack2 = _th_mark_vars(env,_th_nc_rewrite(benv,_th_unmark_vars(env,slack2)));
        return 1;
    } if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        e = e->u.appl.args[0];
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_LESS) {
            struct _ex_intern *l = e->u.appl.args[0];
            struct _ex_intern *r = e->u.appl.args[1];
            struct _ex_intern *sv;
            if ((_th_is_variable_term(l) && r->type==EXP_RATIONAL) ||
                (l->type==EXP_RATIONAL && _th_is_variable_term(r))) {
                return 0;
            }
            sv = _ex_intern_marked_var(_th_new_slack(env),0);
            slack1 = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_RAT_LESS,sv,_ex_intern_small_rational(0,1)));
            slack1 = _th_mark_vars(env,_th_nc_rewrite(benv,_th_unmark_vars(env,slack1)));
            slack2 = _ex_intern_equal(env,_ex_real,_th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_RAT_PLUS,sv,r)),l);
            slack2 = _th_mark_vars(env,_th_nc_rewrite(benv,_th_unmark_vars(env,slack2)));
            return 1;
        }
    }
    return 0;
}

static struct _ex_intern *lhs_reduce(struct env *env, struct _ex_intern *l, struct _ex_intern *rhs)
{
    struct rule *cr;
    struct _ex_intern *r;

    _zone_print_exp("lhs_reduce", l);
    _tree_indent();
    _zone_print_exp("rhs", rhs);
    l = _th_unmark_vars(env,l);
    r = _th_get_first_context_rule(env,&cr);
    while (r) {
        if (!r->rule_simplified &&
            r->u.appl.args[0]->type==EXP_MARKED_VAR && r->u.appl.args[2]==_ex_true &&
            r->u.appl.args[0]->u.marked_var.var==l->u.var) {
            struct _ex_intern *e = _th_unmark_vars(env,r->u.appl.args[1]);
            if (rhs==e) goto cont;
            _zone_print_exp("reduced to", e);
            _tree_undent();
            return e;
        }
cont:
        r = _th_get_next_rule(env,&cr);
    }

    _tree_undent();
    return l;
}

#ifdef OLD_REW_RULE
static struct _ex_intern *rew_rule(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *res, *l, *r;

    _zone_print_exp("rew_rule", e);
    _tree_indent();

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL) {
        if (e->u.appl.args[0]->type==EXP_MARKED_VAR ||
            e->u.appl.args[0]->type==EXP_VAR) {
            r = _th_nc_rewrite(env,e->u.appl.args[1]);
            l = lhs_reduce(env,e->u.appl.args[0],e->u.appl.args[1]);
cont:
            res = _ex_intern_appl2_env(env,INTERN_EQUAL,l,r);
            res->type_inst = e->type_inst;
            e = res;
            res = _th_nc_rewrite(benv,e);
            if (res) e = res;
            _zone_print_exp("case 3", e);
            _tree_undent();
            return e;
        } else if (e->u.appl.args[1]->type==EXP_MARKED_VAR ||
                   e->u.appl.args[1]->type==EXP_VAR) {
            r = _th_nc_rewrite(env,e->u.appl.args[0]);
            l = lhs_reduce(env,e->u.appl.args[1],e->u.appl.args[0]);
            goto cont;
        } else {
            l = _th_nc_rewrite(env,e->u.appl.args[0]);
            r = _th_nc_rewrite(env,e->u.appl.args[1]);
            res = _ex_intern_appl2_env(env,INTERN_EQUAL,l,r);
            res->type_inst = e->type_inst;
            res = _th_nc_rewrite(benv,res);
            _zone_print_exp("case 5", res);
            _tree_undent();
            return res;
        }
    }

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_LESS) {
        l = _th_nc_rewrite(env,e->u.appl.args[0]);
        r = _th_nc_rewrite(env,e->u.appl.args[1]);
        res = _ex_intern_appl2_env(env,INTERN_RAT_LESS,l,r);
        res->type_inst = e->type_inst;
        res = _th_nc_rewrite(env,res);
        _zone_print_exp("case 6", res);
        _tree_undent();
        return res;
    }

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        struct _ex_intern *e1 = e->u.appl.args[0];
        if (e1->type==EXP_APPL && (e1->u.appl.functor==INTERN_EQUAL || e1->u.appl.functor==INTERN_RAT_LESS)) {
            struct _ex_intern *l = _th_nc_rewrite(env,e1->u.appl.args[0]);
            struct _ex_intern *r = _th_nc_rewrite(env,e1->u.appl.args[1]);
            res = _ex_intern_appl2_env(env,e1->u.appl.functor,l,r);
            if (!res->type_inst) res->type_inst = e1->type_inst;
            res = _th_nc_rewrite(env,_ex_intern_appl1_env(env,INTERN_NOT,res));
            _zone_print_exp("case 7", res);
            _tree_undent();
            return res;
        }
    }

    if (e->type != EXP_APPL || e->u.appl.functor != INTERN_ORIENTED_RULE || e->u.appl.args[2] != _ex_true) {
        _zone_print0("No simplification");
        _tree_undent();
        return e;
    }

    if (e->u.appl.args[0]->type==EXP_MARKED_VAR) {
        _zone_print0("Case 1");
        _tree_undent();
        r = _th_nc_rewrite(env,e->u.appl.args[1]);
        l = lhs_reduce(env,e->u.appl.args[0],r);
        _ex_intern_appl2_env(env,INTERN_EQUAL,l,r);
        l->type_inst = e->type_inst;
        l = _th_nc_rewrite(env,l);
        _tree_undent();
        return _th_derive_prepare(env,l);
    }
    if (e->u.appl.args[1]==_ex_true || e->u.appl.args[1]==_ex_false) {
        if (e->u.appl.args[0]->type==EXP_APPL &&
            (e->u.appl.args[0]->u.appl.functor==INTERN_EQUAL || e->u.appl.args[0]->u.appl.functor==INTERN_RAT_LESS)) {
            res = _ex_intern_appl2_env(env,e->u.appl.args[0]->u.appl.functor,
                      _th_nc_rewrite(env,e->u.appl.args[0]->u.appl.args[0]),
                      _th_nc_rewrite(env,e->u.appl.args[0]->u.appl.args[1]));
            if (res->type_inst==NULL) res->type_inst = e->type_inst;
            res = _th_nc_rewrite(benv,res);
            _zone_print0("Case 2");
            _tree_undent();
            return _ex_intern_appl3_env(env,
                e->u.appl.functor,
                res,
                e->u.appl.args[1],
                e->u.appl.args[2]);
        }
    }

    _zone_print0("No simplification");
    _tree_undent();

    return e;
}
#endif

static int has_slack3(struct _ex_intern *e)
{
    int i;

    if (_th_is_slack(e)==4) return 1;

    if (e->type != EXP_APPL) return 0;

    for (i = 0; i < e->u.appl.count; ++i) {
        if (has_slack3(e->u.appl.args[i])) return 1;
    }

    return 0;
}

static struct _ex_intern *rew_rule(struct env *env, struct _ex_intern *e, struct _ex_intern *r)
{
    //struct rule *cr;
    struct _ex_intern *f;
    //struct _ex_intern *g, *h, *rule;

    _zone_print_exp("rew_rule", e);
    _tree_indent();
    _zone_print_exp("r", r);

    //if (has_slack3(e)) {
    //    printf("slack3 used %d\n", _tree_zone);
    //}
cont:
#ifdef OLD
    h = g = e = _th_nc_rewrite(benv,e);
cont1:
    rule = _th_get_first_context_rule(env, &cr);
    while (rule) {
        if (!rule->rule_simplified &&
            rule != r && rule->u.appl.args[2]==_ex_true && rule->u.appl.functor==INTERN_ORIENTED_RULE) {
            rule = _th_unmark_vars(env,rule);
            f = check_for_reduction(env,e,rule->u.appl.args[0],rule->u.appl.args[1]);
            if (f != NULL && f != e) {
                e = f;
                _zone_print_exp("reduced with", rule);
            }
        }
        rule = _th_get_next_rule(env,&cr);
    }
    if (e != g) {
        g = e;
        goto cont1;
    }
    if (e != h) {
        goto cont;
    }
#endif
    //_th_set_block_rule(env,r,0);
    //_th_mark_original(env);
    if (r->u.appl.args[0]->type==EXP_MARKED_VAR && e->u.appl.functor==INTERN_EQUAL) {
        unsigned var = r->u.appl.args[0]->u.marked_var.var;
        if (e->u.appl.args[0]->type==EXP_VAR && var == e->u.appl.args[0]->u.var) {
            e = _ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0],_th_nc_rewrite(env,e->u.appl.args[1]));
        } else if (e->u.appl.args[1]->type==EXP_VAR && var == e->u.appl.args[1]->u.var) {
            e = _ex_intern_appl2_env(env,INTERN_EQUAL,_th_nc_rewrite(env,e->u.appl.args[0]),e->u.appl.args[1]);
        } else {
            e = _th_nc_rewrite(env,e);
        }
    } else {
        e = _th_nc_rewrite(env,e);
    }
    //_th_clear_original(env);
    //_th_set_block_rule(env,NULL,0);

    if (e->type==EXP_APPL) {
        switch (e->u.appl.functor) {
            case INTERN_EQUAL:
                if (e->type_inst==_ex_real) {
                    f = _th_r_equality_false_by_range(env,e);
                } else {
                    f = NULL;
                }
                break;
            case INTERN_RAT_LESS:
                f = _th_simplify_rless_by_range(env,e);
                if (f && f->type==EXP_APPL && f->u.appl.functor==INTERN_NOT) {
                    e = f;
                    goto cont;
                }
                break;
            case INTERN_NOT:
                if (e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_RAT_LESS) {
                    f = _th_pos_test_rless_by_range(env,e->u.appl.args[0]);
                    if (f && f->type==EXP_APPL && f->u.appl.functor==INTERN_NOT) {
                        e = f->u.appl.args[0];
                        goto cont;
                    } else if (f==_ex_true) {
                        f = _ex_false;
                    } else if (f==_ex_false) {
                        f = _ex_true;
                    }
                } else {
                    f = NULL;
                }
                break;
            default:
                f = NULL;
        }
    }
    if (f==_ex_false) e = f;
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT &&
        e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_NOT) {
        e = e->u.appl.args[0]->u.appl.args[0];
    }
    _zone_print_exp("returning", e);
    _tree_undent();

    //if (has_slack3(e) && e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_LESS) {
    //    printf("*** slack3 done %d\n", _tree_zone);
    //}

    return e;
}

static struct add_list *props;

static struct add_list *propagate_inequalities(struct env *env, struct _ex_intern *p,struct add_list *props);

int add_context_rule(struct env *env, struct _ex_intern *rule)
{
    //struct add_list *a;
    struct rule *cr;
    struct _ex_intern *left, *right;
    struct _ex_intern *r, *rule2, *r3;
    int oriented = 0;

#ifdef PROPAGATE
    props = propagate_inequalities(env,rule,props);
#endif

    if (rule==NULL) return 0;
    //printf("Adding rule %s\n", _th_print_exp(rule));

    if (rule->type==EXP_APPL && rule->u.appl.functor==INTERN_AND) {
        int i;
        for (i = 0; i < rule->u.appl.count; ++i) {
            if (add_context_rule(env,rule->u.appl.args[i])) return 1;
        }
        return 0;
    }
    _zone_print_exp("Prepared rule being added", rule);
    _tree_indent();

    if (rule->u.appl.args[0]->type==EXP_APPL && rule->u.appl.args[0]->u.appl.functor==INTERN_RAT_LESS &&
        rule->u.appl.args[2]==_ex_true) {
        if (rule->u.appl.args[1]==_ex_true && _th_simplify_rless_by_range(env,_th_unmark_vars(env,rule->u.appl.args[0]))==_ex_false) {
            _tree_undent();
            return 1;
        }
        if (rule->u.appl.args[1]==_ex_false && _th_pos_test_rless_by_range(env,_th_unmark_vars(env,rule->u.appl.args[0]))==_ex_true) {
            _tree_undent();
            return 1;
        }
    }
    if (_th_equal(env,rule->u.appl.args[0],rule->u.appl.args[1])) {
        _zone_print0("Equal sides");
        _tree_undent();
        return 0;
    }
    if (rule->type==EXP_APPL && rule->u.appl.count==3 && rule->u.appl.functor==INTERN_ORIENTED_RULE) {
        rule2 = _ex_intern_appl3_env(env,rule->u.appl.functor,rule->u.appl.args[0],_th_unmark_vars(env,rule->u.appl.args[1]),_th_unmark_vars(env,rule->u.appl.args[2]));
    } else {
        rule2 = rule;
    }
    if (_th_rule_in_context(env,rule2)) {
        _tree_undent();
        return 0;
    }

    _th_derive_add_prepared(env,rule);

#ifdef UNARY
    a = _th_unary_descendents(env,rule);

    while (a) {
        //printf("Unary descendent %s\n", _th_print_exp(a->e));
        _zone_print_exp("Unary add", a->e);
        if (!a->e->user1) {
            //check_x43(a->e,2);
            a->e->user1 = done_list;
            done_list = a->e;
            if (a->e==_ex_false || add_context_rule(env,_th_derive_prepare(env,a->e))) {
                _tree_undent();
                return 1;
            }
        }
        a = a->next;
    }
#endif

    left = right = NULL;
    if (rule->u.appl.args[1]==_ex_true && rule->u.appl.args[2]==_ex_true &&
        rule->u.appl.args[0]->type==EXP_APPL &&
        rule->u.appl.args[0]->u.appl.functor==INTERN_EQUAL) {
        left = rule->u.appl.args[0]->u.appl.args[0];
        right = rule->u.appl.args[0]->u.appl.args[1];
        //_zone_print_exp("Here1", rule);
    } else if (rule->u.appl.args[1] != _ex_true && rule->u.appl.args[1] != _ex_false &&
               rule->u.appl.args[2] == _ex_true) {
        left = rule->u.appl.args[0];
        right = rule->u.appl.args[1];
        oriented = (rule->u.appl.functor==INTERN_ORIENTED_RULE);
        //_zone_print_exp("Here2", rule);
    } else {
        oriented = (rule->u.appl.functor==INTERN_ORIENTED_RULE);
        //_zone_print_exp("Here3", rule);
    }

    if (oriented) {
        //struct add_list *radd, *rl = NULL;
        struct _ex_intern *r_orig;
        r_orig = r = _th_get_first_context_rule(env, &cr);
        _zone_print_exp("Testing for reductions with", rule);
        _tree_indent();
        while (r != NULL) {
            if (r->is_marked_term) {
                r = _ex_intern_appl3_env(env,r->u.appl.functor,
                        r->u.appl.args[0],
                        _th_mark_vars(env,r->u.appl.args[1]),
                        _th_mark_vars(env,r->u.appl.args[2]));
            }
            if (_th_mark_vars(env,r) != _th_mark_vars(env,rule)) {
                //extern int in_list(struct env *env, struct _ex_intern *rule);
                //_zone_print_exp("Testing for reduction on", r);
                //if (r->rule_simplified && !in_list(env,r)) exit(1);
                if (!r->rule_simplified) {
                    struct _ex_intern *r2 = check_for_reduction(env,_th_mark_vars(env,r),rule->u.appl.args[0],rule->u.appl.args[1]);
                    _zone_print_exp("Testing for reduction on", r);
                    _tree_indent();
                    if (r2 != r) {
                        if (r2==NULL) r2 = _th_mark_vars(env,r);
                    //if (r2 != r && (r2->u.appl.args[0]->type != EXP_MARKED_VAR ||
                        //r2->u.appl.args[1]->type != EXP_MARKED_VAR ||
                        //r2->u.appl.args[2] != _ex_true)) {
                        //if (r->u.appl.args[0]->type==EXP_MARKED_VAR && !strcmp(_th_intern_decode(r->u.appl.args[0]->u.marked_var.var),"_slack4")) exit(1);
                        _zone_print_exp("Not simplified", r2);
                        //r2->user1 = done_list;
                        //done_list = r2;
                        //check_x43(r2,3);
                        //printf("%s is reduced to\n", _th_print_exp(r));
                        //printf("%s\n", _th_print_exp(r2));
                        _zone_print_exp("Reduced", r2);
                        r2 = _th_unmark_vars(env,r2);
                        if (r2->u.appl.args[2]==_ex_true) {
                            if (r2->u.appl.args[1]==_ex_true) {
                                r2 = r2->u.appl.args[0];
                            } else if (r2->u.appl.args[1]==_ex_false) {
                                r2 = _ex_intern_appl1_env(env,INTERN_NOT,r2->u.appl.args[0]);
                            } else {
                                r2 = _ex_intern_equal(env,r->type_inst,r2->u.appl.args[0],r2->u.appl.args[1]);
                            }
                        }
                        r2 = rew_rule(env,r2,r_orig);
                        if (r2==_ex_false) {
                            _tree_undent();
                            _tree_undent();
                            _tree_undent();
                            return 1;
                        }
                        r3 = _th_derive_prepare(env,r2);
                        if (r3 != r && r3 != r_orig) {
                            r->rule_simplified = r_orig->rule_simplified = 1;
                            _th_add_simplified_rule(env,r);
                            _th_add_simplified_rule(env,r_orig);
                            if (r2 != _ex_true) {
                                if (r2==_ex_false || add_context_rule(env,r3)) {
                                    _tree_undent();
                                    _tree_undent();
                                    _tree_undent();
                                    return 1;
                                }
                            }
                        }
                        //if (r2 != _ex_true) {
                        //    _zone_print_exp("Will add", r2);
                        //    radd = ALLOCA(sizeof(struct add_list));
                        //    radd->next = rl;
                        //    rl = radd;
                        //    radd->e = r2;
                        //}
                    }
                    _tree_undent();
                }
            }
            r_orig = r = _th_get_next_rule(env,&cr);
        }
        //after_check(env);
        //while (rl != NULL) {
            //_zone_print_exp("Processing", rl->e);
            //_tree_indent();
            //rl->e = rew_rule(env,rl->e);
            //rl->e = _th_mark_vars(env,rl->e);
            //if (add_slack(env,rl->e)) {
            //    struct _ex_intern *s1 = slack1;
            //    struct _ex_intern *s2 = slack2;
            //    if (add_context_rule(env,_th_derive_prepare(env,s1))) {
            //        _tree_undent();
            //        _tree_undent();
            //        return 1;
            //    }
            //    if (add_context_rule(env,_th_derive_prepare(env,s2))) {
            //        _tree_undent();
            //        _tree_undent();
            //        return 1;
            //    }
            //} else {
            //    if (rl->e != _ex_true) {
            //        if (rl->e==_ex_false || add_context_rule(env,_th_derive_prepare(env,rl->e))) {
            //            _tree_undent();
            //            _tree_undent();
            //            _tree_undent();
            //            return 1;
            //        }
            //    }
            //}
            //_tree_undent();
            //rl = rl->next;
        //}
        _tree_undent();
    }

#ifdef XX
    r = _th_get_first_context_rule(env, &cr);
	while (r != NULL) {
        if (!r->rule_simplified) {
            _zone_print_exp("Binary descendents of", r);
            _tree_indent();
            a = _th_binary_descendents(env,r,rule,&done_list);
            while (a != NULL) {
                //printf("Binary descendent %s\n", _th_print_exp(a->e));
                _zone_print0("Binary add");
                if (a->e==_ex_false || add_context_rule(env,_th_derive_prepare(env,a->e))) {
                    _tree_undent();
                    _tree_undent();
                    return 1;
                }
                a = a->next;
            }
            _tree_undent();
        }
        r = _th_get_next_rule(env,&cr);
    }
#endif

    _tree_undent();
    return 0;
}

static int _th_add_transitive_derivatives(struct env *env, struct _ex_intern *e)
{
	struct add_list *a = _th_implied_descendents(env, e);

	while (a) {
        _zone_print_exp("Checking transitive", a->e);
        _zone_print1("user1 %d", a->e->user1);
        if (!a->e->user1) {
            a->e->user1 = done_list;
            done_list = a->e;
            //check_x43(a->e,4);
		    if (a->e==_ex_false || add_context_rule(env, _th_derive_prepare(env,a->e))) return 1;
        }
		a = a->next;
	}

	return 0;
}

static void after_check(struct env *env)
{
    struct rule *cr1, *cr2;
    struct _ex_intern *r1, *r2, *s;

    r1 = _th_get_first_context_rule(env,&cr1);
    while (r1) {
        if (r1->u.appl.args[0]->type==EXP_APPL && r1->u.appl.args[0]->u.appl.functor==INTERN_EQUAL &&
            r1->u.appl.args[1]==_ex_true) {
            fprintf(stderr, "Illegal rule, %s\n", _th_print_exp(r1));
            exit(1);
        }

        r2 = _th_get_first_context_rule(env,&cr2);
        while (r2) {
            if (r1 != r2 && !r1->rule_simplified && !r2->rule_simplified) {
                if ((s = check_for_reduction(env,r1,r2->u.appl.args[0],r2->u.appl.args[1])) != r1) {
                    printf("Failure: %s\n", _th_print_exp(r1));
                    printf("and %s\n", _th_print_exp(r2));
                    printf("simp %s\n", _th_print_exp(s));
                    exit(1);
                }
            }
            r2 = _th_get_next_rule(env,&cr2);
        }
        r1 = _th_get_next_rule(env,&cr1);
    }
}

int _th_uninterpreted_functor(int functor)
{
    return functor != INTERN_NAT_PLUS && functor != INTERN_NAT_TIMES && functor != INTERN_RAT_PLUS &&
           functor != INTERN_RAT_TIMES && functor != INTERN_NAT_LESS && functor != INTERN_RAT_LESS &&
           functor != INTERN_NAT_DIVIDE && functor != INTERN_RAT_DIVIDE && functor != INTERN_AND &&
           functor != INTERN_OR && functor != INTERN_XOR && functor != INTERN_NAT_MOD &&
           functor != INTERN_RAT_MOD && functor != INTERN_EQUAL && functor != INTERN_NOT;
}

static int is_a_constant(struct _ex_intern *e)
{
    if (e==_ex_true ||
        e==_ex_false ||
        e->type==EXP_INTEGER ||
        e->type==EXP_RATIONAL ||
        e->type==EXP_STRING) return 1;
    return 0;
}

static struct add_list *collect_n_equivalent_terms(struct env *env, struct _ex_intern *functor, struct _ex_intern *val)
{
    struct rule *cr;
    struct _ex_intern *r;
    struct add_list *list, *a;

    list = NULL;
    r = _th_get_first_context_rule(env,&cr);
    while (r) {
        if (r->u.appl.args[0]->type==EXP_APPL &&
            r->u.appl.args[0]->u.appl.functor==functor->u.appl.functor &&
            r->u.appl.args[1]!=val && is_a_constant(r->u.appl.args[1]) &&
            _th_uninterpreted_functor(r->u.appl.args[0]->u.appl.functor)) {
            a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            a->next = list;
            a->e = r->u.appl.args[0];
            list = a;
        } else if (r->u.appl.args[1]->type==EXP_APPL &&
                   r->u.appl.args[1]->u.appl.functor==functor->u.appl.functor &&
                   r->u.appl.args[0]!=val && is_a_constant(r->u.appl.args[0]) &&
                   _th_uninterpreted_functor(r->u.appl.args[1]->u.appl.functor)) {
            a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            a->next = list;
            a->e = r->u.appl.args[1];
            list = a;
        }
        r = _th_get_next_rule(env,&cr);
    }

    return list;
}

static struct add_list *collect_equivalent_terms(struct env *env, struct _ex_intern *functor, struct _ex_intern *val)
{
    struct rule *cr;
    struct _ex_intern *r;
    struct add_list *list, *a;

    list = NULL;
    r = _th_get_first_context_rule(env,&cr);
    while (r) {
        if (r->u.appl.args[0]->type==EXP_APPL &&
            r->u.appl.args[0]->u.appl.functor==functor->u.appl.functor &&
            r->u.appl.args[1]==val &&
            _th_uninterpreted_functor(r->u.appl.args[0]->u.appl.functor)) {
            a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            a->next = list;
            a->e = r->u.appl.args[0];
            list = a;
        } else if (r->u.appl.args[1]->type==EXP_APPL &&
                   r->u.appl.args[1]->u.appl.functor==functor->u.appl.functor &&
                   r->u.appl.args[0]==val &&
                   _th_uninterpreted_functor(r->u.appl.args[1]->u.appl.functor)) {
            a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            a->next = list;
            a->e = r->u.appl.args[1];
            list = a;
        }
        r = _th_get_next_rule(env,&cr);
    }

    return list;
}

static int is_characteristic(struct _ex_intern *e)
{
    return e->type==EXP_INTEGER || e->type==EXP_RATIONAL || e->type==EXP_MARKED_VAR ||
           (e->type==EXP_APPL && !_th_uninterpreted_functor(e->u.appl.functor));
}

static struct add_list *collect_all_functors(struct env *env, struct _ex_intern *val)
{
    struct rule *cr;
    struct _ex_intern *r;
    struct add_list *list, *a;

    if (!is_characteristic(val)) {
        r = _th_get_first_context_rule(env,&cr);
        while (r) {
            if (r->u.appl.args[0]==val) {
                val = r->u.appl.args[1];
                break;
            }
            if (r->u.appl.args[1]==val) {
                val = r->u.appl.args[0];
                break;
            }
            r = _th_get_next_rule(env,&cr);
        }
    }

    if (!is_characteristic(val)) {
        if (val->type==EXP_APPL && _th_uninterpreted_functor(val->u.appl.functor)) {
            a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            a->next = NULL;
            a->e = val;
            return a;
        } else {
            return NULL;
        }
    }

    list = NULL;
    r = _th_get_first_context_rule(env,&cr);
    while (r) {
        if (r->u.appl.args[0]->type==EXP_APPL &&
            r->u.appl.args[1]==val && _th_uninterpreted_functor(r->u.appl.args[0]->u.appl.functor)) {
            a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            a->next = list;
            a->e = r->u.appl.args[0];
            list = a;
        } else if (r->u.appl.args[1]->type==EXP_APPL &&
                   r->u.appl.args[0]==val &&
                   _th_uninterpreted_functor(r->u.appl.args[1]->u.appl.functor)) {
            a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            a->next = list;
            a->e = r->u.appl.args[1];
            list = a;
        }
        r = _th_get_next_rule(env,&cr);
    }

    return list;
}

static struct _ex_intern *disjoint_functor_rule(struct env *env, struct _ex_intern *f1, struct _ex_intern *f2)
{
    int i;
    struct _ex_intern **args;
    struct _ex_intern *r;

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * f1->u.appl.count);
    for (i = 0; i < f1->u.appl.count; ++i) {
        args[i] = _ex_intern_appl1_env(env,INTERN_NOT,
            _ex_intern_appl2_env(env,INTERN_EQUAL,
                f1->u.appl.args[i],
                f2->u.appl.args[i]));
    }

    //printf("Disjoint\n");
    //printf("    f1 = %s\n", _th_print_exp(f1));
    //printf("    f2 = %s\n", _th_print_exp(f2));

    r = _ex_intern_appl_env(env,INTERN_OR,f1->u.appl.count,args);
    r = _th_mark_vars(env,_th_nc_rewrite(env,_th_unmark_vars(env,r)));
    //printf("    r = %s\n", _th_print_exp(r));

    return r;
}

static struct add_list *augment_store(struct env *env, struct _ex_intern *l, struct _ex_intern *r, struct add_list *list)
{
    struct add_list *a;

    a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
    a->next = list;
    list = a;
    a->e = _ex_intern_appl2_env(env,INTERN_EQUAL,
           _ex_intern_appl2_env(env,INTERN_SELECT,r,l->u.appl.args[1]),
           l->u.appl.args[2]);
    a->e = _th_mark_vars(env,_th_nc_rewrite(env,_th_unmark_vars(env,a->e)));

    a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
    a->next = list;
    list = a;
    a->e = _ex_intern_appl3_env(env,INTERN_EE,l->u.appl.args[0],r,l->u.appl.args[1]);
    a->e = _th_mark_vars(env,_th_nc_rewrite(env,_th_unmark_vars(env,a->e)));

    return a;
}

static struct add_list *augment_neg_store(struct env *env, struct _ex_intern *l, struct _ex_intern *r, struct add_list *list)
{
    struct add_list *a;

    a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
    a->next = list;
    list = a;
    a->e = _ex_intern_appl1_env(env,INTERN_NOT,
               _ex_intern_appl2_env(env,INTERN_EQUAL,
                   _ex_intern_appl2_env(env,INTERN_SELECT,r,l->u.appl.args[1]),
                   l->u.appl.args[2]));
    a->e = _ex_intern_appl2_env(env,INTERN_OR,a->e,
               _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl3_env(env,INTERN_EE,l->u.appl.args[0],r,l->u.appl.args[1])));
    a->e = _th_mark_vars(env,_th_nc_rewrite(env,_th_unmark_vars(env,a->e)));

    return a;
}

struct _ex_intern *_th_add_to_ee(struct env *env, struct _ex_intern *ee, struct _ex_intern *t)
{
    struct _ex_intern **args = ALLOCA(sizeof(ee->u.appl.count+1));
    int i, j;
    int done;

    for (i = 2; i < ee->u.appl.count; ++i){
        if (ee->u.appl.args[i]==t) return ee;
    }

    args[0] = ee->u.appl.args[0];
    args[1] = ee->u.appl.args[1];

    done = 0;
    for (j = 2, i = 2; i < ee->u.appl.count; ++i) {
        if (!done && ((int)ee->u.appl.args[i]) > ((int)t)) {
            args[j++] = t;
            done = 1;
        }
        args[j++] = ee->u.appl.args[i];
    }
    if (!done) args[j++] = t;

    return _ex_intern_appl_env(env,INTERN_EE,j,args);
}

static struct add_list *augment_ee_store(struct env *env, struct _ex_intern *l, struct _ex_intern *r, struct _ex_intern *term, struct add_list *list)
{
    struct add_list *a;
    struct _ex_intern **args = ALLOCA(sizeof(term->u.appl.count+1));
    int i;

    a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
    a->next = list;
    list = a;
    for (i = 0; i < term->u.appl.count-2; ++i) {
        args[i] = _ex_intern_appl2_env(env,INTERN_EQUAL,term->u.appl.args[i+2],l->u.appl.args[1]);
    }
    args[i++] = _ex_intern_appl2_env(env,INTERN_EQUAL,
                _ex_intern_appl2_env(env,INTERN_SELECT,r,l->u.appl.args[1]),
                l->u.appl.args[2]);
    a->e = _ex_intern_appl_env(env,INTERN_OR,i,args);
    a->e = _th_mark_vars(env,_th_nc_rewrite(env,_th_unmark_vars(env,a->e)));


    args[0] = l->u.appl.args[0];
    args[1] = r;
    for (i = 2; i < term->u.appl.count; ++i) {
        args[i] = term->u.appl.args[i];
    }
    if (((int)args[1]) < ((int)args[0])) {
        struct _ex_intern *e = args[0];
        args[0] = args[1];
        args[1] = e;
    }
    a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
    a->next = list;
    a->e = _th_add_to_ee(env,_ex_intern_appl_env(env,INTERN_EE,i,args),l->u.appl.args[1]);

    return a;
}

static struct add_list *intersect_ee_store(struct env *env, struct _ex_intern *ee1, struct _ex_intern *ee2, struct add_list *l)
{
    struct add_list *a;
    struct _ex_intern **args = ALLOCA(sizeof(ee1->u.appl.count+1));
    int i, j, k;
    struct _ex_intern *e;

    args[0] = ee1->u.appl.args[0];
    args[1] = ee1->u.appl.args[1];

    for (i = 2, j = 2; i < ee1->u.appl.count; ++i) {
        for (k = 2; k < ee2->u.appl.count; ++k) {
            if (ee1->u.appl.args[i]==ee2->u.appl.args[k]) {
                args[j++] = ee1->u.appl.args[i];
                goto cont;
            }
        }
cont:;
    }

    if (((int)args[1]) < ((int)args[0])) {
        struct _ex_intern *e = args[0];
        args[0] = args[1];
        args[1] = e;
    }

    e = _ex_intern_appl_env(env,INTERN_EE,j,args);

    if (e != ee1 && e != ee2) {
        a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        a->next = l;
        l = a;
        a->e = e;
    }

    return l;
}

static struct add_list *remove_from_ee(struct env *env, struct _ex_intern *ee, struct _ex_intern *p, struct add_list *l)
{
    struct add_list *a;
    struct _ex_intern **args = ALLOCA(sizeof(ee->u.appl.count));
    int i, j;

    args[0] = ee->u.appl.args[0];
    args[1] = ee->u.appl.args[1];
    for (i = 2, j = 2; i < ee->u.appl.count; ++i) {
        if (ee->u.appl.args[i] != p) args[j++] = ee->u.appl.args[i];
    }

    if (j < i) {
        a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        a->next = l;
        l = a;
        if (j==2) {
            a->e = _ex_intern_appl_env(env,INTERN_EQUAL,2,args);
        } else {
            a->e = _ex_intern_appl_env(env,INTERN_EE,j,args);
        }
    }

    return l;
}

static struct add_list *remove_from_ee_neg(struct env *env, struct _ex_intern *ee, struct _ex_intern *p, struct add_list *l)
{
    struct add_list *a;
    struct _ex_intern **args = ALLOCA(sizeof(ee->u.appl.count));
    int i, j;

    args[0] = ee->u.appl.args[0];
    args[1] = ee->u.appl.args[1];
    for (i = 2, j = 2; i < ee->u.appl.count; ++i) {
        if (ee->u.appl.args[i] != p) args[j++] = ee->u.appl.args[i];
    }

    if (j < i) {
        a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        a->next = l;
        l = a;
        if (j==2) {
            a->e = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl_env(env,INTERN_EQUAL,j,args));
        } else {
            a->e = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl_env(env,INTERN_EE,j,args));
        }
    }

    return l;
}

static struct add_list *intersect_ee_nee(struct env *env, struct _ex_intern *ee, struct _ex_intern *nee, struct add_list *l)
{
    struct add_list *a;
    struct _ex_intern **args = ALLOCA(sizeof(ee->u.appl.count+nee->u.appl.count));
    int i, j, k;

    for (i = 0; i < ee->u.appl.count-2; ++i) {
        for (j = 0; j < nee->u.appl.count-2; ++j) {
            if (ee->u.appl.args[i+2]==nee->u.appl.args[j+2]) goto cont;
        }
        args[i] = _ex_intern_appl1_env(env,INTERN_NOT,
                       _ex_intern_appl2_env(env,INTERN_EQUAL,
                           _ex_intern_appl2_env(env,INTERN_SELECT,ee->u.appl.args[0],ee->u.appl.args[i+2]),
                           _ex_intern_appl2_env(env,INTERN_SELECT,ee->u.appl.args[1],ee->u.appl.args[i+2])));
cont:;
    }

    a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
    a->next = l;
    a->e = _ex_intern_appl_env(env,INTERN_OR,i,args);
    a->e = _th_mark_vars(env,_th_nc_rewrite(env,_th_unmark_vars(env,a->e)));

    args[0] = nee->u.appl.args[0];
    args[1] = nee->u.appl.args[1];
    k = 2;
    for (i = 0; i < nee->u.appl.count-2; ++i) {
        for (j = 0; j < ee->u.appl.count-2; ++j) {
            if (ee->u.appl.args[i+2]==nee->u.appl.args[j+2]) {
                args[k++] = nee->u.appl.args[i];
                goto cont2;
            }
        }
cont2:;
    }

    a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
    a->next = l;
    a->e = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl_env(env,INTERN_EE,k,args));
    a->e = _th_mark_vars(env,_th_nc_rewrite(env,_th_unmark_vars(env,a->e)));

    return a;
}

static struct add_list *intersect_ee_ne(struct env *env, struct _ex_intern *ee, struct add_list *l)
{
    struct add_list *a;
    struct _ex_intern **args = ALLOCA(sizeof(ee->u.appl.count));
    int i;

    for (i = 0; i < ee->u.appl.count-2; ++i) {
        args[i] = _ex_intern_appl1_env(env,INTERN_NOT,
                       _ex_intern_appl2_env(env,INTERN_EQUAL,
                           _ex_intern_appl2_env(env,INTERN_SELECT,ee->u.appl.args[0],ee->u.appl.args[i+2]),
                           _ex_intern_appl2_env(env,INTERN_SELECT,ee->u.appl.args[1],ee->u.appl.args[i+2])));
    }

    a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
    a->next = l;
    a->e = _ex_intern_appl_env(env,INTERN_OR,i,args);
    a->e = _th_mark_vars(env,_th_nc_rewrite(env,_th_unmark_vars(env,a->e)));

    return a;
}

static struct add_list *transitive_ee(struct env *env, struct _ex_intern *ee1, struct _ex_intern *ee2, struct add_list *list)
{
    struct _ex_intern *nee = NULL;
    struct add_list *a;
    int i;

    if (ee1->u.appl.args[0] != ee2->u.appl.args[0] ||
        ee1->u.appl.args[1] != ee2->u.appl.args[1]) {

        if (ee1->u.appl.args[0]==ee2->u.appl.args[1]) {
            nee = _ex_intern_appl2_env(env,INTERN_EE,ee2->u.appl.args[0],ee1->u.appl.args[1]);
        }
        if (ee2->u.appl.args[0]==ee1->u.appl.args[1]) {
            nee = _ex_intern_appl2_env(env,INTERN_EE,ee1->u.appl.args[0],ee2->u.appl.args[1]);
        }
    }

    if (nee) {
        for (i = 2; i < ee1->u.appl.count; ++i) {
            nee = _th_add_to_ee(env,nee,ee1->u.appl.args[i]);
        }
        for (i = 2; i < ee2->u.appl.count; ++i) {
            nee = _th_add_to_ee(env,nee,ee2->u.appl.args[i]);
        }
        nee = _th_mark_vars(env,_th_nc_rewrite(env,_th_unmark_vars(env,nee)));
        a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        a->next = list;
        a->e = nee;
        list = a;
    }

    return list;
}

static struct add_list *collect_ee_pos(struct env *env, struct _ex_intern *left, struct _ex_intern *right)
{
    struct rule *cr;
    struct _ex_intern *r;
    struct add_list *list, *a;

    list = NULL;
    r = _th_get_first_context_rule(env,&cr);
    while (r) {
        if (r->u.appl.args[0]->type==EXP_APPL &&
            r->u.appl.args[1]==_ex_true && r->u.appl.args[0]->u.appl.functor==INTERN_EE &&
            ((r->u.appl.args[0]->u.appl.args[0]==left && r->u.appl.args[0]->u.appl.args[1]==right) ||
             (r->u.appl.args[0]->u.appl.args[0]==right && r->u.appl.args[0]->u.appl.args[1]==left))) {
            a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            a->next = list;
            a->e = r->u.appl.args[0];
            list = a;
        }
        r = _th_get_next_rule(env,&cr);
    }

    return list;
}

static struct add_list *collect_ee_all_pos(struct env *env)
{
    struct rule *cr;
    struct _ex_intern *r;
    struct add_list *list, *a;

    list = NULL;
    r = _th_get_first_context_rule(env,&cr);
    while (r) {
        if (r->u.appl.args[0]->type==EXP_APPL &&
            r->u.appl.args[1]==_ex_true && r->u.appl.args[0]->u.appl.functor==INTERN_EE) {
            a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            a->next = list;
            a->e = r->u.appl.args[0];
            list = a;
        }
        r = _th_get_next_rule(env,&cr);
    }

    return list;
}

static struct add_list *collect_ss_pos(struct env *env, struct _ex_intern *left, struct _ex_intern *right)
{
    struct rule *cr;
    struct _ex_intern *r;
    struct add_list *list, *a;

    list = NULL;
    r = _th_get_first_context_rule(env,&cr);
    while (r) {
        if (r->u.appl.args[0]->type==EXP_APPL &&
            r->u.appl.args[1]==_ex_true && r->u.appl.args[0]->u.appl.functor==INTERN_EQUAL) {
            struct _ex_intern *le = r->u.appl.args[0]->u.appl.args[0];
            struct _ex_intern *ri = r->u.appl.args[0]->u.appl.args[1];
            if (le->type==EXP_APPL && ri->type==EXP_APPL && le->u.appl.functor==INTERN_SELECT &&
                ri->u.appl.functor==INTERN_SELECT && le->u.appl.args[1]==ri->u.appl.args[1] &&
                ((le->u.appl.args[0]==left && ri->u.appl.args[0]==right) ||
                 (ri->u.appl.args[0]==right && le->u.appl.args[0]==left))) {
                a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                a->next = list;
                a->e = r->u.appl.args[0];
                list = a;
            }
        }
        r = _th_get_next_rule(env,&cr);
    }

    return list;
}

static struct add_list *collect_ss_neg(struct env *env)
{
    struct rule *cr;
    struct _ex_intern *r;
    struct add_list *list, *a;

    list = NULL;
    r = _th_get_first_context_rule(env,&cr);
    while (r) {
        if (r->u.appl.args[0]->type==EXP_APPL &&
            r->u.appl.args[1]==_ex_false && r->u.appl.args[0]->u.appl.functor==INTERN_EQUAL) {
            struct _ex_intern *l = r->u.appl.args[0]->u.appl.args[0];
            struct _ex_intern *r = r->u.appl.args[0]->u.appl.args[1];
            if (l->type==EXP_APPL && r->type==EXP_APPL && l->u.appl.functor==INTERN_SELECT &&
                r->u.appl.functor==INTERN_SELECT && l->u.appl.args[1]==r->u.appl.args[1]) {
                a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                a->next = list;
                a->e = r->u.appl.args[0];
                list = a;
            }
        }
        r = _th_get_next_rule(env,&cr);
    }

    return list;
}

static struct add_list *collect_ee_neg(struct env *env)
{
    struct rule *cr;
    struct _ex_intern *r;
    struct add_list *list, *a;

    list = NULL;
    r = _th_get_first_context_rule(env,&cr);
    while (r) {
        if (r->u.appl.args[0]->type==EXP_APPL &&
            r->u.appl.args[1]==_ex_false && r->u.appl.args[0]->u.appl.functor==INTERN_EE) {
            a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            a->next = list;
            a->e = r->u.appl.args[0];
            list = a;
        }
        r = _th_get_next_rule(env,&cr);
    }

    return list;
}

static struct add_list *propagate_inequalities(struct env *env, struct _ex_intern *new_rule, struct add_list *back)
{
    struct add_list *flist, *a, *glist, *l, *rl;
    int functor;
    struct _ex_intern *left, *right;

    _zone_print_exp("Propagating", new_rule);

    if (new_rule->u.appl.args[0]->type != EXP_APPL) return back;

    _tree_indent();

    if (new_rule->u.appl.args[0]->u.appl.functor==INTERN_EE) {
        struct _ex_intern *ee = new_rule->u.appl.args[0];
        if (new_rule->u.appl.args[1]==_ex_true) {
            flist = collect_ss_pos(env,ee->u.appl.args[0],ee->u.appl.args[1]);
            rl = back;
            while (flist) {
                rl = remove_from_ee(env,ee,flist->e->u.appl.args[0]->u.appl.args[1],rl);
                flist = flist->next;
            }
            flist = collect_ee_all_pos(env);
            while (flist) {
                rl = transitive_ee(env,ee,flist->e,rl);
                flist = flist->next;
            }
            _zone_print_exp("ee prop", ee);
            if (ee->u.appl.args[0]->type==EXP_APPL && ee->u.appl.args[0]->u.appl.functor==INTERN_STORE) {
                rl = augment_ee_store(env,ee->u.appl.args[0],ee->u.appl.args[1],ee,rl);
            } else if (ee->u.appl.args[1]->type==EXP_APPL && ee->u.appl.args[1]->u.appl.functor==INTERN_STORE) {
                rl = augment_ee_store(env,ee->u.appl.args[1],ee->u.appl.args[0],ee,rl);
            }
            _tree_undent();
            return rl;
        }
        _tree_undent();
        return back;
    }

    if (new_rule->u.appl.args[0]->u.appl.functor==INTERN_EQUAL) {
        if (new_rule->u.appl.args[1]==_ex_true) {
            struct _ex_intern *l = new_rule->u.appl.args[0]->u.appl.args[0];
            struct _ex_intern *r = new_rule->u.appl.args[0]->u.appl.args[1];
            rl = back;
            if (l->type==EXP_APPL && l->u.appl.functor==INTERN_STORE) {
                rl = augment_store(env,l,r,rl);
            }
            if (r->type==EXP_APPL && r->u.appl.functor==INTERN_STORE) {
                rl = augment_store(env,r,l,rl);
            }
            if (l->type==EXP_APPL && l->u.appl.functor==INTERN_SELECT &&
                r->type==EXP_APPL && r->u.appl.functor==INTERN_SELECT &&
                l->u.appl.args[1]==r->u.appl.args[1]) {
                flist = collect_ee_pos(env,l->u.appl.args[0],r->u.appl.args[0]);
                while (flist) {
                    rl = remove_from_ee(env,flist->e,l->u.appl.args[1],rl);
                    flist = flist->next;
                }
            }
            _tree_undent();
            return rl;
        }
        if (new_rule->u.appl.args[1]==_ex_false) {
            struct _ex_intern *eq = new_rule->u.appl.args[0];
            flist = collect_all_functors(env,eq->u.appl.args[0]);
            glist = collect_all_functors(env,eq->u.appl.args[1]);
            rl = back;
            while (flist) {
                l = glist;
                while (l) {
                    if (flist->e->u.appl.functor==l->e->u.appl.functor) {
                        _zone_print_exp("Pair", flist->e);
                        _zone_print_exp("and", l->e);
                        a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                        a->next = rl;
                        rl = a;
                        a->e = disjoint_functor_rule(env,flist->e,l->e);
                    }
                    l = l->next;
                }
                flist = flist->next;
            }
            _tree_undent();
            if (new_rule->u.appl.args[0]->u.appl.args[0]->type==EXP_APPL && new_rule->u.appl.args[0]->u.appl.args[0]->u.appl.functor==INTERN_STORE) {
                rl = augment_neg_store(env,new_rule->u.appl.args[0]->u.appl.args[0],new_rule->u.appl.args[0]->u.appl.args[1],rl);
            }
            if (new_rule->u.appl.args[0]->u.appl.args[1]->type==EXP_APPL && new_rule->u.appl.args[0]->u.appl.args[1]->u.appl.functor==INTERN_STORE) {
                rl = augment_neg_store(env,new_rule->u.appl.args[0]->u.appl.args[1],new_rule->u.appl.args[0]->u.appl.args[0],rl);
            }
            return rl;
        }
        _tree_undent();
        return back;
    }

    functor = new_rule->u.appl.args[0]->u.appl.functor;

    //_tree_print1("Here3 %s", _th_intern_decode(functor));

    flist = back;
    if (_th_uninterpreted_functor(functor) && is_a_constant(new_rule->u.appl.args[1])) {
        flist = collect_n_equivalent_terms(env,new_rule->u.appl.args[0],new_rule->u.appl.args[1]);
        a = flist;
        _tree_indent();
        while(a) {
            //_tree_print_exp("Processing", a->e);
            a->e = disjoint_functor_rule(env,new_rule->u.appl.args[0],a->e);
            //_tree_print_exp("Result", a->e);
            a = a->next;
        }
        _tree_undent();
    }

    left = new_rule->u.appl.args[0];
    right = new_rule->u.appl.args[1];

    if (left->type==EXP_APPL && left->u.appl.functor==INTERN_STORE) {
        flist = augment_store(env,left,right,flist);
    }
    if (right->type==EXP_APPL && right->u.appl.functor==INTERN_STORE) {
        flist = augment_store(env,right,left,flist);
    }

    _tree_undent();
    return flist;
}

int _th_do_abstraction = 0;

int _th_add_rule_and_implications(struct env *env, struct _ex_intern *e)
{
	int x;
    struct add_list *al = NULL;

    //unsigned *fv;
    //int count;

	_zone_print_exp("Adding rule and implications", e);
	_tree_indent();
    //e = abstract_condition(env,e,PARENT_NONE);
    //_zone_print_exp("abstracted to", e);

    if (add_slack(env,e)) {
        struct _ex_intern *s1 = slack1;
        struct _ex_intern *s2 = slack2;
        _tree_undent();
        if (_th_add_rule_and_implications(env,s1)) return 1;
        if (_th_add_rule_and_implications(env,s2)) return 1;
        return 0;
    }

    _th_mark_simplified(env);
    //done_list = _ex_true;
    //_ex_true->user1 = _ex_true;

    //fv = _th_get_free_vars(e,&count);
    //if (count) {
    //    int i = 0;
    //    printf("Free vars in rule %s\n", _th_print_exp(e));
    //    i = 1 / i;
    //    exit(1);
    //}

    e = _th_unmark_vars(env,e);
    e = _th_nc_rewrite(env,e);
    e = _th_mark_vars(env,e);
    _zone_print_exp("Simplified to", e);
    //_zone_print1("e->user1 = %d", e->user1);
    //_zone_print_exp("e->user1", e->user1);
#ifdef UNARY
    if (_th_add_transitive_derivatives(env, e)) {
        //_zone_print0("Here1");
        while (done_list && (done_list != _ex_true)) {
            struct _ex_intern *n = done_list->user1;
            //_zone_print_exp("Removing", done_list);
            done_list->user1 = NULL;
            done_list = n;
        }
        _th_clear_simplified(env);
        _tree_undent();
        return 1;
    }
    _zone_print1("e->user1 = %d", e->user1);
#endif
    props = NULL;
    if (e->user1) {
        x = 0;
    } else if (e==_ex_false) {
        x = 1;
    } else {
        struct _ex_intern *p;
        p = _th_derive_prepare(env,e);
        if (p) {
            _tree_undent();
            //e->user1 = done_list;
            //done_list = e;
            //check_x43(e,5);
            _th_add_original_rule(env,p);
	        x = add_context_rule(env,p);
            _zone_print0("Disjoint propagation");
            _tree_indent();
            if (p->type==EXP_APPL && p->u.appl.functor==INTERN_ORIENTED_RULE) {
                p = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,p->u.appl.args[0],
                    _th_unmark_vars(env,p->u.appl.args[1]),
                    _th_unmark_vars(env,p->u.appl.args[2]));
            }
        } else {
            x = 0;
        }
    }
    //while (done_list && (done_list != _ex_true)) {
    //    struct _ex_intern *n = done_list->user1;
        //_zone_print_exp("Removing", done_list);
    //    done_list->user1 = NULL;
    //    done_list = n;
    //}

#ifdef PROPAGATE
    al = props;
    _zone_print0("PROPAGATIONS");
    _tree_indent();
    while (al != NULL && !x) {
        //fprintf(stderr, "Propagating %s\n", _th_print_exp(al->e));
        //exit(1);
        if (_th_add_rule_and_implications(env,al->e)) {
            x = 1;
        }
        al = al->next;
    }
    _tree_undent();
#endif

	_tree_undent();

    _ex_true->user1 = NULL;

    //after_check(env);

    _th_clear_simplified(env);

	return x;
}

static void invalidate_term(struct env *env, struct _ex_intern *term)
{
    struct add_list *parents;
    struct _ex_intern *r = term;

    while (r->rewrite && r->rewrite != r) r = r->rewrite;

    if (r==_ex_true || r==_ex_false || r->type==EXP_INTEGER || r->type==EXP_RATIONAL || r->type==EXP_STRING) return;

    if (term->cache_bad) return;
    //printf("Marking bad %s\n", _th_print_exp(term));
    //check_cycle(env, "before");
    _th_mark_bad(env,term);
    //check_cycle(env, "after");

    parents = term->used_in;
    while (parents) {
        invalidate_term(env, parents->e);
        parents = parents->next;
    }
    parents = term->cached_in;
    while (parents) {
        invalidate_term(env, parents->e);
        parents = parents->next;
    }
}

static struct _ex_intern *rewrite_n;

//static struct _ex_intern *eqtest;

static struct add_list *copy_list(int space, struct add_list *list)
{
    struct add_list *p, *l, *ret, *n;

    p = NULL;

    l = list;
    while (l) {
        n = (struct add_list *)_th_alloc(space,sizeof(struct add_list));
        if (p==NULL) {
            ret = n;
        } else {
            p->next = n;
        }
        n->e = l->e;
        p = n;
        l = l->next;
    }
    if (p) {
        p->next = NULL;
    } else {
        ret = NULL;
    }

    return ret;
}

static int merge(struct env *env, struct _ex_intern *left, struct _ex_intern *right, struct _ex_intern *lspot, struct _ex_intern *rspot, struct add_list *explanation, int disallow_const);

static int process_term(struct env *env, struct _ex_intern *e)
{
    _zone_print_exp("Processing term", e);
    _tree_indent();

    //printf("Processing %s\n", _th_print_exp(e));

    if (e->type==EXP_APPL) {
        if (e->u.appl.functor==INTERN_AND || e->u.appl.functor==INTERN_OR || e->u.appl.functor==INTERN_NOT ||
            e->u.appl.functor==INTERN_ITE || e->u.appl.functor==INTERN_ORIENTED_RULE ||
            e->u.appl.functor==INTERN_UNORIENTED_RULE) {
            invalidate_term(env,e);
        } else if (e->u.appl.functor==INTERN_EQUAL) {
            struct _ex_intern *f = e;
            while (f->rewrite != NULL && f->rewrite != f) {
                f = f->rewrite;
            }
            //if (e->u.appl.args[0]->type==EXP_VAR && e->u.appl.args[1]->type==EXP_VAR) {
            //fprintf(stderr, "Processing %s\n", _th_print_exp(e));
            //fprintf(stderr, "Result: %s\n", _th_print_exp(f));
            //}
            if (f==_ex_true) {
                struct _ex_intern *l, *r;
true_case:
                _zone_print0("is true");
                l = e->u.appl.args[0];
                while (l) {
                    r = e->u.appl.args[1];
                    while (r) {
                        struct _ex_intern *eq = _ex_intern_appl2_env(env,INTERN_EQUAL,l,r);
                        struct _ex_intern *x = eq;
                        _zone_print_exp("Handling", eq);
                        _zone_print_exp("l", l);
                        _zone_print_exp("r", r);
                        while (x->rewrite && x->rewrite != x) {
                            x = x->rewrite;
                        }
                        _zone_print_exp("which rewrites to", x);
                        if (x==_ex_false) {
                            _zone_print0("equality contradiction");
                            _tree_undent();
                            return 1;
                        } else if (x != _ex_true) {
                            _th_add_cache_assignment(env,x,_ex_true);
                        }
                        if (r==r->rewrite) {
                            r = NULL;
                        } else {
                            r = r->rewrite;
                        }
                    }
                    if (l==l->rewrite) {
                        l = NULL;
                    } else {
                        l = l->rewrite;
                    }
                }
            } else if (f==_ex_false) {
                struct _ex_intern *l, *r;
false_case:
                _zone_print0("is false");
                l = e->u.appl.args[0];
                while (l) {
                    r = e->u.appl.args[1];
                    while (r) {
                        struct _ex_intern *eq = _ex_intern_appl2_env(env,INTERN_EQUAL,l,r);
                        struct _ex_intern *x = eq;
                        _zone_print_exp("Handling", eq);
                        _zone_print_exp("l", l);
                        _zone_print_exp("r", r);
                        if (l==r) {
                            _zone_print0("equality contradiction");
                            _tree_undent();
                            return 1;
                        }
                        while (x->rewrite && x->rewrite != x) {
                            x = x->rewrite;
                        }
                        _zone_print_exp("which rewrites to", x);
                        if (x==_ex_true) {
                            _zone_print0("equality contradiction");
                            _tree_undent();
                            return 1;
                        } else if (x != _ex_false) {
                            _th_add_cache_assignment(env,x,_ex_false);
                        }
                        if (r==r->rewrite) {
                            r = NULL;
                        } else {
                            r = r->rewrite;
                        }
                    }
                    if (l==l->rewrite) {
                        l = NULL;
                    } else {
                        l = l->rewrite;
                    }
                }
#ifdef XX
                l = e->u.appl.args[0];
                r = e->u.appl.args[1];
                if (l->type==EXP_APPL && r->type==EXP_APPL &&
                    l->u.appl.functor==r->u.appl.functor &&
                    l->u.appl.count==r->u.appl.count) {
                    int i;
                    f = NULL;
                    for (i = 0; i < l->u.appl.count; ++i) {
                        if (l->u.appl.args[i] != r->u.appl.args[i]) {
                            if (f) goto cont;
                            f = _ex_intern_appl2_env(env,INTERN_EQUAL,l->u.appl.args[i],r->u.appl.args[i]);
                        }
                    }
                    if (f) {
                        struct _ex_intern *g = f;
                        while (f->rewrite != NULL && f != f->rewrite) {
                            f = f->rewrite;
                        }
                        if (f==_ex_true) {
                            _zone_print0("Equality contradiction");
                            _tree_undent();
                            return 1;
                        }
                        _th_add_cache_assignment(env,f,_ex_false);
                        _zone_print_exp("Adding to queue", g);
                        //printf("Processing parent %s\n", _th_print_exp(e));
                        _tree_indent();
                        if (g->user2) {
                            _zone_print0("Already in queue");
                        } else {
                            g->user2 = _ex_true;
                            g->next_cache = rewrite_n;
                            invalidate_term(env,g);
                            rewrite_n = g;
                        }
                        _tree_undent();
                     }
                }
cont:
                //l = e->u.appl.args[0];
                //r = e->u.appl.args[1];
                while (l->rewrite && l->rewrite != l) {
                    l = l->rewrite;
                }
                while (r->rewrite && r->rewrite != r) {
                    r = r->rewrite;
                }
                if (l==r) {
                    _zone_print0("ne contradiction");
                    _tree_undent();
                    return 1;
                }
                f = _ex_intern_appl2_env(env,INTERN_EQUAL,l,r);
                _zone_print_exp("Making false", f);
                _zone_print_exp("rewrite", f->rewrite);
                while (f->rewrite && f->rewrite != f) {
                    f = f->rewrite;
                }
                
                if (f==_ex_true) {
                    _zone_print0("Equality contradiction 2");
                    _tree_undent();
                    return 1;
                }
                
                //invalidate_term(env,f);
                _th_add_cache_assignment(env,f,_ex_false);
                if (l->type==EXP_APPL && r->type==EXP_APPL &&
                    l->u.appl.functor==r->u.appl.functor &&
                    l->u.appl.count==r->u.appl.count) {
                    int i;
                    f = NULL;
                    for (i = 0; i < l->u.appl.count; ++i) {
                        if (l->u.appl.args[i] != r->u.appl.args[i]) {
                            if (f) goto end;
                            f = _ex_intern_appl2_env(env,INTERN_EQUAL,l->u.appl.args[i],r->u.appl.args[i]);
                        }
                    }
                    if (f) {
                        struct _ex_intern *g = f;
                        while (f->rewrite != NULL && f != f->rewrite) {
                            f = f->rewrite;
                        }
                        if (f==_ex_true) {
                            _zone_print0("Equality contradiction");
                            _tree_undent();
                            return 1;
                        }
                        _th_add_cache_assignment(env,f,_ex_false);
                        _zone_print_exp("Adding to queue", g);
                        //printf("Processing parent %s\n", _th_print_exp(e));
                        _tree_indent();
                        if (g->user2) {
                            _zone_print0("Already in queue");
                        } else {
                            g->user2 = _ex_true;
                            g->next_cache = rewrite_n;
                            invalidate_term(env,g);
                            rewrite_n = g;
                        }
                        _tree_undent();
                     }
                }
#endif
            } else if (e->rewrite==NULL) {
                struct _ex_intern *r;
                _th_int_rewrite(env,e,0);
                _zone_print_exp("rewrite", e->rewrite);
                r = e;
                while (r->rewrite != NULL && r != r->rewrite) r = r->rewrite;
                if (r==_ex_true) goto true_case;
                if (r==_ex_false) goto false_case;
            } else {
                struct _ex_intern *l, *r;
                _zone_print_exp("Old reduction", e->rewrite);
                l = e->u.appl.args[0];
                while (l) {
                    r = e->u.appl.args[1];
                    while (r) {
                        struct _ex_intern *eq = _ex_intern_appl2_env(env,INTERN_EQUAL,l,r);
                        struct _ex_intern *x = eq;
                        _zone_print_exp("Handling", eq);
                        _zone_print_exp("l", l);
                        _zone_print_exp("r", r);
                        while (x->rewrite && x->rewrite != x) {
                            x = x->rewrite;
                        }
                        _zone_print_exp("which rewrites to", x);
                        if (x==_ex_false) {
                            goto false_case;
                        } else if (x == _ex_true) {
                            goto true_case;
                        }
                        if (r==r->rewrite) {
                            r = NULL;
                        } else {
                            r = r->rewrite;
                        }
                    }
                    if (l==l->rewrite) {
                        l = NULL;
                    } else {
                        l = l->rewrite;
                    }
                }
                l = e->u.appl.args[0];
                r = e->u.appl.args[1];
                while (l->rewrite && l->rewrite != l) {
                    l = l->rewrite;
                }
                while (r->rewrite && r->rewrite != r) {
                    r = r->rewrite;
                }
                if (l==r) goto true_case;
                _th_add_cache_assignment(env,e,_ex_intern_appl2_env(env,INTERN_EQUAL,l,r));
            }
        } else if (e->rewrite==NULL) {
            struct add_list *parents;

            _th_int_rewrite(env,e,0);

            parents = e->used_in;
            
            while (parents) {
                struct _ex_intern *e = parents->e;
                _zone_print_exp("Adding to queue", e);
                //printf("Processing parent %s\n", _th_print_exp(e));
                _tree_indent();
                if (e->user2) {
                    _zone_print_exp("Already in queue", e->user2);
                } else {
                    e->user2 = _ex_true;
                    e->next_cache = rewrite_n;
                    invalidate_term(env,e);
                    rewrite_n = e;
                }
                _tree_undent();
                parents = parents->next;
            }
        } else {
            struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            struct _ex_intern *g = e, *f;
            struct _ex_intern *eq;
            int i;
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = e->u.appl.args[i];
                while (args[i]->rewrite && args[i]->rewrite != args[i]) {
                    args[i] = args[i]->rewrite;
                }
            }
            f = _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
            f = _th_int_rewrite(env,f,0);
            _zone_print_exp("initial g", g);
            while (g->rewrite && g->rewrite != g) {
                g = g->rewrite;
                _zone_print_exp("g", g);
            }
            _zone_print_exp("final g", g);
            if (g==f && g != e) {
                struct add_list *parents = e->used_in;
                while (parents) {
                    struct _ex_intern *e = parents->e;
                    _zone_print_exp("Adding to queue", e);
                    //printf("Processing parent %s\n", _th_print_exp(e));
                    _tree_indent();
                    if (e->user2) {
                        _zone_print_exp("Already in queue", e->user2);
                    } else {
                        e->user2 = _ex_true;
                        e->next_cache = rewrite_n;
                        invalidate_term(env,e);
                        rewrite_n = e;
                    }
                    _tree_undent();
                    parents = parents->next;
                }
            }
            if ((f->type==EXP_APPL && (f->u.appl.functor==INTERN_NAT_PLUS ||
                 f->u.appl.functor==INTERN_NAT_TIMES || f->u.appl.functor==INTERN_NAT_DIVIDE ||
                 f->u.appl.functor==INTERN_RAT_PLUS || f->u.appl.functor==INTERN_RAT_TIMES ||
                 f->u.appl.functor==INTERN_RAT_DIVIDE)) ||
                (g->type==EXP_APPL && (g->u.appl.functor==INTERN_NAT_PLUS ||
                 g->u.appl.functor==INTERN_NAT_TIMES || g->u.appl.functor==INTERN_NAT_DIVIDE ||
                 g->u.appl.functor==INTERN_RAT_PLUS || g->u.appl.functor==INTERN_RAT_TIMES ||
                 g->u.appl.functor==INTERN_RAT_DIVIDE))) {
                eq = _ex_intern_appl2_env(env,INTERN_EQUAL,f,g);
                eq = _th_int_rewrite(env,eq,0);
                if (eq->type==EXP_APPL && eq->u.appl.functor==INTERN_EQUAL) {
                    _zone_print_exp("Replacing", f);
                    _zone_print_exp("and", g);
                    f = eq->u.appl.args[0];
                    g = eq->u.appl.args[1];
                    _zone_print_exp("with", f);
                    _zone_print_exp("and", g);
                }
            }
            //printf("start merge: process term\n");
            if (merge(env,g,f,g,f,NULL,1)) {
                _tree_undent();
                return 1;
            }
            //while (f->rewrite != NULL && f->rewrite != f) {
            //    f = f->rewrite;
            //}
            //if (propagate_pred(env,e,f)) {
            //    _tree_undent();
            //    _tree_undent();
            //    --level;
            //    return 1;
            //}
        }
    }

    _tree_undent();
    return 0;
}

static void recursive_initialize(struct env *env, struct _ex_intern *e)
{
    if (e->in_hash) return;

    _th_add_signature(env,e,e);

    _th_mark_inhash(env,e);

    if (e->type==EXP_APPL) {
        int i;
        _ex_add_used_in(e);
        for (i = 0; i < e->u.appl.count; ++i) {
            recursive_initialize(env,e->u.appl.args[i]);
        }
    }
}

static struct _ex_intern *new_expr(struct env *env, struct _ex_intern *e, struct add_list **expl)
{
    struct _ex_intern *f;
    struct add_list *ee;
    //static struct _ex_intern *teste = NULL;
    static int stop = 0;

    //printf("new_expr %d %x %s\n", (env == _th_get_learn_env()), env, _th_print_exp(e));
    _zone_print_exp("new_expr", e);
    _tree_indent();

    _th_mark_bad(env,e);

    e = _th_int_rewrite(env,e,0);
    if (e->in_hash) {
        if (expl) *expl = NULL;
        _zone_print_exp("result (already in hash)", e);
        _tree_undent();
        return e;
    }

    //printf("%d: New expr %x %s\n", _tree_zone, env, _th_print_exp(e));
    //if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_LESS) printf("e = %s\n", _th_print_exp(e));
#ifndef FAST
	if (_zone_active()) _th_print_difference_table(env);
#endif
	f = _th_check_cycle_rless(env,e,&ee);
    //printf("    reduction %s\n", _th_print_exp(f));

    if (f) {
        recursive_initialize(env,e);
        //printf("f = %s\n", _th_print_exp(e));
        //if (e->find==NULL || e->find==e) {
        //    _th_add_find(env,e,f);
        //}
        f = _th_int_rewrite(env,f,0);
        //printf("start merge: new_expr\n");
		if (merge(env,e,f,e,f,ee,1)) {
			int i = 0;
			fprintf(stderr, "Merge error %s\n", _th_print_exp(e));
			fprintf(stderr, "and %s\n", _th_print_exp(f));
			i = 1 / i;
		}
        if (expl) *expl = ee;
        recursive_initialize(env,f);
        e = f;
        //printf("e = %s\n", _th_print_exp(e));
        //printf("f = %s\n", _th_print_exp(f));
    } else if (expl) {
        *expl = NULL;
        recursive_initialize(env,e);
        //printf("No cycle simplify\n");
    }

    //if (teste==NULL) {
    //    teste = _th_parse(env,"(rless #2/1 (rplus (rtimes #-1/1 x_22) x_61))");
    //}
    //if (_tree_zone >= 131744 && e==teste && _th_get_learn_env()!=env) {
    //    fprintf(stderr, "Stopping point\n");
    //    exit(1);
    //}
    //printf("Done rewriting\n");

    if (_th_is_boolean_term(env,e) && (e->type != EXP_APPL ||
        (e->u.appl.functor!=INTERN_AND && e->u.appl.functor != INTERN_OR &&
        e->u.appl.functor!=INTERN_ITE && e->u.appl.functor != INTERN_NOT &&
        (e->u.appl.functor!=INTERN_EQUAL || !_th_is_boolean_term(env,e->u.appl.args[0])))) &&
        e != _ex_true && e != _ex_false) {
        //printf("New term 3 %d %s\n", e->in_hash, _th_print_exp(e));
        _th_new_term(e);
    }

    _zone_print_exp("result", e);
    _tree_undent();
    return e;
}

static struct _ex_intern *new_expr1(struct env *env, struct _ex_intern *e, struct add_list **expl)
{
    //struct _ex_intern *f;
    //struct add_list *ee;
    //static struct _ex_intern *teste = NULL;
    static int stop = 0;

    //printf("new_expr %d %x %s\n", (env == _th_get_learn_env()), env, _th_print_exp(e));
    _zone_print_exp("new_expr1", e);
    _tree_indent();

    _th_mark_bad(env,e);

    e = _th_int_rewrite(env,e,0);
    if (e->in_hash) {
        if (expl) *expl = NULL;
        _zone_print_exp("result (already in hash)", e);
        _tree_undent();
        return e;
    }

    if (expl) {
        *expl = NULL;
        recursive_initialize(env,e);
        //printf("No cycle simplify\n");
    }

    //if (teste==NULL) {
    //    teste = _th_parse(env,"(rless #2/1 (rplus (rtimes #-1/1 x_22) x_61))");
    //}
    //if (_tree_zone >= 131744 && e==teste && _th_get_learn_env()!=env) {
    //    fprintf(stderr, "Stopping point\n");
    //    exit(1);
    //}
    //printf("Done rewriting\n");

    if (_th_is_boolean_term(env,e) && (e->type != EXP_APPL ||
        (e->u.appl.functor!=INTERN_AND && e->u.appl.functor != INTERN_OR &&
        e->u.appl.functor!=INTERN_ITE && e->u.appl.functor != INTERN_NOT &&
        (e->u.appl.functor!=INTERN_EQUAL || !_th_is_boolean_term(env,e->u.appl.args[0])))) &&
        e != _ex_true && e != _ex_false) {
        //printf("New term 3 %d %s\n", e->in_hash, _th_print_exp(e));
        _th_new_term(e);
    }

    _zone_print_exp("result", e);
    _tree_undent();
    return e;
}

static struct _ex_intern *signature(struct env *env, struct _ex_intern *e);

static struct _ex_intern *simp(struct env *env, struct _ex_intern *e)
{
    //printf("simp %s\n", _th_print_exp(e));

    _zone_print_exp("simp", e);
    _tree_indent();

    if (e->type==EXP_APPL) {
        _tree_indent();
        e = signature(env,e);
        _tree_undent();
    }
    while (e->find && e != e->find) e = e->find;

    if (!e->in_hash) {
        _th_mark_inhash(env,e);
        if (e->type==EXP_APPL) _ex_add_used_in(e);
        if (e->type != EXP_APPL && _th_is_boolean_term(env,e) && (e->type != EXP_APPL ||
            (e->u.appl.functor!=INTERN_AND && e->u.appl.functor != INTERN_OR &&
            e->u.appl.functor!=INTERN_ITE && e->u.appl.functor != INTERN_NOT)) &&
            e != _ex_true && e != _ex_false) {
            //printf("New term 4 %s\n", _th_print_exp(e));
            _th_new_term(e);
        }
    }

    _tree_undent();
    _zone_print_exp("return", e);

    return e;
}

static struct _ex_intern *signature(struct env *env, struct _ex_intern *e)
{
    int i;
    struct _ex_intern *x;
    struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
    _zone_print_exp("Signature", e);
    for (i = 0; i < e->u.appl.count; ++i) {
        args[i] = simp(env,e->u.appl.args[i]);
        _zone_print2("args[%d] = %s", i, _th_print_exp(args[i]));
    }
    x = _ex_intern_appl_equal_env(env,e->u.appl.functor,e->u.appl.count,args,e->type_inst);
    //if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL && x->type_inst==NULL) {
    //    x->type_inst = e->type_inst;
    //}
    return new_expr(env,x,NULL);
}

static struct add_list *ret_expl;

static struct add_list *quick_explanation(struct env *env, struct _ex_intern *left, struct _ex_intern *right, struct add_list *explanation);

static struct _ex_intern *signature_expl(struct env *env, struct _ex_intern *e, struct add_list *expl);

static struct _ex_intern *simp_expl(struct env *env, struct _ex_intern *e, struct add_list *expl)
{
    //printf("simp %s\n", _th_print_exp(e));
    struct _ex_intern *f;

    //printf("Simplifying %s\n", _th_print_exp(e));

    _zone_print_exp("simp_expl", e);
    _tree_indent();
    //if (_zone_active() && _ex_false->find==_ex_true) {
    //    fprintf(stderr, "false rewrites to true\n");
    //    exit(1);
    //}

    if (e->type==EXP_APPL) {
        e = signature_expl(env,e,expl);
        expl = ret_expl;
    }
    f = e;
    _zone_print_exp("f", f);
    while (e->find && e != e->find) {
        e = e->find;
        _zone_print_exp("Find", e);
    }
    expl = quick_explanation(env,e,f,expl);

    if (!e->in_hash) {
        _th_mark_inhash(env,e);
        if (e->type==EXP_APPL) _ex_add_used_in(e);
        if (e->type != EXP_APPL && _th_is_boolean_term(env,e) && (e->type != EXP_APPL ||
            (e->u.appl.functor!=INTERN_AND && e->u.appl.functor != INTERN_OR &&
            e->u.appl.functor!=INTERN_ITE && e->u.appl.functor != INTERN_NOT)) &&
            e != _ex_true && e != _ex_false) {
            //printf("New term 5 %s\n", _th_print_exp(e));
            _th_new_term(e);
        }
    }

    ret_expl = expl;

#ifndef FAST
    if (_zone_active()) {
        _tree_print("Explanation");
        _tree_indent();
        while (expl) {
            _tree_print_exp("e", expl->e);
            expl = expl->next;
        }
        _tree_undent();
    }
#endif
    _tree_undent();
    _zone_print_exp("result", e);
    return e;
}

static int in_assert = 0;

static struct _ex_intern *signature_expl(struct env *env, struct _ex_intern *e, struct add_list *expl)
{
    int i;
    struct _ex_intern *x;
    struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
    struct add_list *a;

    _zone_print_exp("Signature", e);
	_tree_indent();
    for (i = 0; i < e->u.appl.count; ++i) {
        args[i] = simp_expl(env,e->u.appl.args[i], expl);
        expl = ret_expl;
        _zone_print2("args[%d] = %s", i, _th_print_exp(args[i]));
    }
    x = _ex_intern_appl_equal_env(env,e->u.appl.functor,e->u.appl.count,args,e->type_inst);
    //if (e->u.appl.functor==INTERN_EQUAL && x->type_inst==NULL) x->type_inst = e->type_inst;
    //if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL && x->type_inst==NULL) {
    //    x->type_inst = e->type_inst;
    //}

    ret_expl = expl;
    //if (in_assert) {
    //    x = new_expr1(env,x, &ret_expl);
    //} else {
        x = new_expr(env,x, &ret_expl);
    //}
    if (ret_expl==NULL) {
        ret_expl = expl;
    } else {
        a = ret_expl;
        while (a->next) {
            a = a->next;
        }
        a->next = expl;
    }
	_tree_undent();
    return x;
}

//#define BUILD_STRUCT

#ifdef BUILD_STRUCT
struct _ex_intern *str;
#endif

static struct _ex_intern *trail;

struct _ex_intern *int_simp(struct env *env, struct _ex_intern *e, int need_expl)
{
#ifndef FAST
    struct _ex_intern *orig = e;
#endif
    struct _ex_intern *res;

    _zone_print_exp("int_simp", e);
    _zone_print1("tree_zone %d", _tree_zone);
    _tree_indent();

    if (e->type==EXP_APPL) {
        if (e->u.appl.functor==INTERN_AND || e->u.appl.functor==INTERN_OR ||
            e->u.appl.functor==INTERN_NOT ||
            e->u.appl.functor==INTERN_ITE) {
            int i;
            struct _ex_intern **args;
special:
            if (e->find) {
                _zone_print_exp("From cache", e->find);
                _tree_undent();
                return e->find;
            }
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            //printf("Processing term\n");
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = int_simp(env,e->u.appl.args[i],need_expl);
            }
            res = _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
            e->merge = res;
            e->explanation = (struct add_list *)trail;
            trail = e;
            //printf("Done processing term\n");
            _tree_undent();
            return res;
        } else if (e->u.appl.functor==INTERN_EQUAL) {
            if (_th_is_boolean_term(env,e->u.appl.args[0]) || _th_is_boolean_term(env,e->u.appl.args[1])) goto special;
            if (_th_my_contains_ite(e)) goto special;
        } else if (_th_my_contains_ite(e)) goto special;
    } else {
        struct _ex_intern *e1 = e;
        //printf("Core simp %s\n", _th_print_exp(e));
        //_tree_print_exp("int_simp 1", e);
        e = _th_int_rewrite(env,e,0);
        if (e->in_hash) {
            while (e->find != e) e = e->find;
            _zone_print_exp("find", e);
            _tree_undent();
            _zone_print_exp("Result", e);
#ifndef FAST
            if (_zone_active() && e != orig) _tree_print0("*** Different ***");
#endif
            return e;
        }
    }

    //printf("Core simp 2 %s\n", _th_print_exp(e));
    //_tree_print_exp("int_simp 2", e);
    if (need_expl || !e->in_hash) {
        struct _ex_intern *f;
        //_tree_print0("Here x");
        //_tree_print_exp("int_simp 2", e);
        f = simp_expl(env,e, NULL);
        //_tree_print0("Here a");
        if (f != e) {
            //printf("start merge: int_simp\n");
            if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL && f==_ex_true) {
                merge(env,e->u.appl.args[0],e->u.appl.args[1],e->u.appl.args[0],e->u.appl.args[1],copy_list(_th_get_space(env),ret_expl),1);
            } else {
                merge(env,e,f,e,f,copy_list(_th_get_space(env),ret_expl),1);
            }
            //printf("Merged %s\n", _th_print_exp(e));
            //printf("   and %s\n", _th_print_exp(f));
            e = f;
        }
        //_tree_print0("Here b");
    } else {
        //_tree_print_exp("int_simp 3", e);
#ifdef FAST
        e = simp(env,e);
#else
        if (_zone_active()) {
            e = simp_expl(env,e,NULL);
        } else {
            e = simp(env,e);
        }
#endif
    }

    _tree_undent();
    _zone_print_exp("Result", e);
#ifndef FAST
    if (_zone_active() && e != orig) _tree_print0("*** Different ***");
#endif
    return e;
}

struct _ex_intern *_th_simp(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *res;
    char *mark = _th_alloc_mark(REWRITE_SPACE);
    _zone_print_exp("_th_simp", e);
    //printf("*** _th_simp *** %s\n\n", _th_print_exp(e));
#ifndef FAST
    if (_zone_active()) _th_print_difference_table(env);
#endif
    trail = NULL;
    res = int_simp(env,e,0);
    while (trail) {
        e = trail;
        trail = (struct _ex_intern *)e->explanation;
        e->merge = NULL;
        e->explanation = NULL;
        e = (struct _ex_intern *)e->explanation;
    }
    _th_alloc_release(REWRITE_SPACE,mark);
    return res;
}

static int is_integer(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *t;

    switch (e->type) {
        case EXP_APPL:
            t = _th_get_type(env,e->u.appl.functor);
            //if (t==NULL) return 0;
            return (t && t->u.appl.args[1]==_ex_int);
        case EXP_VAR:
            return (_th_get_var_type(env,e->u.var)==_ex_int);
        case EXP_INTEGER:
            return 1;
        default:
            return 0;
    }
}

static int is_bool(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *t;

    switch (e->type) {
        case EXP_APPL:
            t = _th_get_type(env,e->u.appl.functor);
            if (t && t->u.appl.args[1]==_ex_bool) return 1;
            return (e->u.appl.functor==INTERN_AND || e->u.appl.functor==INTERN_OR || e->u.appl.functor==INTERN_NOT || e->u.appl.functor==INTERN_TRUE || e->u.appl.functor==INTERN_FALSE);
        case EXP_VAR:
            return (_th_get_var_type(env,e->u.var)==_ex_bool);
        default:
            return 0;
    }
}

static int is_real(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *t;

    switch (e->type) {
        case EXP_APPL:
            t = _th_get_type(env,e->u.appl.functor);
            //if (t==NULL) return 0;
            return (t && t->u.appl.args[1]==_ex_real);
        case EXP_VAR:
            return (_th_get_var_type(env,e->u.var)==_ex_real);
        case EXP_RATIONAL:
            return 1;
        default:
            return 0;
    }
}

static struct add_list *quick_explanation(struct env *env, struct _ex_intern *left, struct _ex_intern *right, struct add_list *explanation)
{
    struct _ex_intern *l, *ancestor;
    struct add_list *expl;

    l = left;

    while (l->merge) {
        _zone_print_exp("l", l);
        _zone_print_exp("l->merge", l->merge);
        //if (_zone_active()) {
        //    printf("l = %s\n", _th_print_exp(l));
        //    fflush(stdout);
        //}
        l->user2 = _ex_true;
        l = l->merge;
        if (l==l->merge) {
            //int i = 0;
            fprintf(stderr, "Quick explanation failure\n");
            fprintf(stderr, "left = %s\n", _th_print_exp(left));
            fprintf(stderr, "right = %s\n", _th_print_exp(right));
            //i = 1/i;
            exit(1);
        }
    }

    ancestor = right;
    while (ancestor->user2==NULL && ancestor->merge) {
        ancestor = ancestor->merge;
    }
#ifndef FAST
    if (!ancestor->merge && l != ancestor) {
        fprintf(stderr, "Explanation error, terms not merged 1\n");
        fprintf(stderr, "    left = %s\n", _th_print_exp(left));
        while (left->merge) {
            left = left->merge;
            fprintf(stderr,"        %s\n", _th_print_exp(left));
        }
        fprintf(stderr, "    right = %s\n", _th_print_exp(right));
        while (right->merge) {
            right = right->merge;
            fprintf(stderr,"        %s\n", _th_print_exp(right));
        }
        exit(1);
    }
#endif
    l = left;
    while (l->merge) {
        l->user2 = NULL;
        l = l->merge;
    }

    l = left;
    while (l != ancestor) {
        expl = (struct add_list *)_th_alloc(_th_get_space(env),sizeof(struct add_list));
        expl->next = explanation;
        if (l->merge==_ex_true) {
            expl->e = l;
        } else if (l->merge==_ex_false) {
            expl->e = _ex_intern_appl1_env(env,INTERN_NOT,l);
        } else {
			if (is_bool(env,l) || is_bool(env,l->merge)) {
                expl->e = _ex_intern_equal(env,_ex_bool,l,l->merge);
			} else if (is_integer(env,l) || is_integer(env,l->merge)) {
                expl->e = _ex_intern_equal(env,_ex_int,l,l->merge);
			} else if (is_real(env,l) || is_real(env,l->merge)) {
                expl->e = _ex_intern_equal(env,_ex_real,l,l->merge);
			} else {
				fprintf(stderr, "Illegal equal terms 1 %s", _th_print_exp(l));
				fprintf(stderr, " and %s\n", _th_print_exp(l->merge));
				exit(1);
			}
        }
        l = l->merge;
        explanation = expl;
    }
    l = right;
    while (l != ancestor) {
        expl = (struct add_list *)_th_alloc(_th_get_space(env),sizeof(struct add_list));
        expl->next = explanation;
        if (l->merge==_ex_true) {
            expl->e = l;
        } else if (l->merge==_ex_false) {
            expl->e = _ex_intern_appl1_env(env,INTERN_NOT,l);
        } else {
			if (is_bool(env,l) || is_bool(env,l->merge)) {
                expl->e = _ex_intern_equal(env,_ex_bool,l,l->merge);
			} else if (is_integer(env,l) || is_integer(env,l->merge)) {
                expl->e = _ex_intern_equal(env,_ex_int,l,l->merge);
			} else if (is_real(env,l) || is_real(env,l->merge)) {
                expl->e = _ex_intern_equal(env,_ex_real,l,l->merge);
			} else {
				int i = 0;
				fprintf(stderr, "Illegal equal terms 2 %s", _th_print_exp(l));
				fprintf(stderr, " and %s\n", _th_print_exp(l->merge));
				fprintf(stderr, "type l = %s\n", _th_print_exp(_th_get_var_type(env,l->u.var)));
				i = 1 / i;
				exit(1);
			}
        }
        l = l->merge;
        explanation = expl;
    }

    return explanation;
}

static int do_assert(struct env *env, struct _ex_intern *pred, struct _ex_intern *orig, struct add_list *explanation);

struct add_list *contradiction;

void print_explanation_list(struct env *env, struct add_list *elist);

void print_explanation(struct env *env, struct _ex_intern *left, struct _ex_intern *right)
{
    struct _ex_intern *l, *ancestor;

    l = left;

    _tree_print_exp("Explanation of", left);
    _tree_print_exp("and", right);
    _tree_indent();

    while (l->merge) {
        l->user2 = _ex_true;
        l = l->merge;
        _zone_print_exp("Left merge", l);
    }

    ancestor = right;
    while (ancestor->user2==NULL && ancestor->merge) {
        ancestor = ancestor->merge;
        _zone_print_exp("right merge", ancestor->merge);
    }
    _zone_print_exp("Ancestor", ancestor);
#ifndef FAST
    if (!ancestor->merge && l != ancestor) {
        fprintf(stderr, "Explanation error, terms not merged 2\n");
        fprintf(stderr, "    left = %s\n", _th_print_exp(left));
        while (left->merge) {
            left = left->merge;
            fprintf(stderr,"        %s\n", _th_print_exp(left));
        }
        fprintf(stderr, "    right = %s\n", _th_print_exp(right));
        while (right->merge) {
            right = right->merge;
            fprintf(stderr,"        %s\n", _th_print_exp(right));
        }
        exit(1);
    }
#endif
    l = left;
    while (l->merge) {
        l->user2 = NULL;
        l = l->merge;
    }

    l = left;
    while (l != ancestor) {
        _tree_print_exp("Left link", l);
        _tree_print_exp("to", l->merge);
        _tree_indent();
        print_explanation_list(env, l->explanation);
        _tree_undent();
        l = l->merge;
    }
    l = right;
    while (l != ancestor) {
        _tree_print_exp("Right link", l);
        _tree_print_exp("to", l->merge);
        _tree_indent();
        print_explanation_list(env, l->explanation);
        _tree_undent();
        l = l->merge;
    }

    _tree_undent();
}

void print_explanation_list(struct env *env, struct add_list *elist)
{
    struct _ex_intern *left, *right;

    while (elist) {
        _zone_print_exp("Term", elist->e);
        _tree_indent();
        if (elist->e->type==EXP_APPL) {
            if (elist->e->u.appl.functor==INTERN_NOT) {
                left = elist->e->u.appl.args[0];
                right = _ex_false;
            } else if (elist->e->u.appl.functor==INTERN_EQUAL) {
                left = elist->e->u.appl.args[0];
                right = elist->e->u.appl.args[1];
            } else {
                left = elist->e;
                right = _ex_true;
            }
        } else {
            left = elist->e;
            right = _ex_true;
        }
        print_explanation(env,left,right);
        _tree_undent();
        elist = elist->next;
    }
}

static struct _ex_intern *test = NULL, *testl = NULL, *testr = NULL;

static int add_implications(struct env *env, struct _ex_intern *e);

static struct _ex_intern *get_type(struct env *env, struct _ex_intern *exp)
{
    struct _ex_intern *t;

    switch (exp->type) {
        case EXP_INTEGER:
            return _ex_int;
            break;
        case EXP_RATIONAL:
            return _ex_real;
            break;
        case EXP_VAR:
            return _th_get_var_type(env,exp->u.var);
            break;
        case EXP_APPL:
            if (exp->u.appl.functor==INTERN_ITE) {
                t = get_type(env,exp->u.appl.args[1]);
                return t;
            } else {
                t = _th_get_type(env,exp->u.appl.functor);
                return t->u.appl.args[1];
            }
            break;
        default:
            return NULL;
    }
}

static int merge(struct env *env, struct _ex_intern *left, struct _ex_intern *right, struct _ex_intern *lspot, struct _ex_intern *rspot, struct add_list *explanation, int disallow_const)
{
    struct add_list *parents;
    struct _ex_intern *l, *r;
    int repeated = 0;
    struct add_list *expl;
    struct _ex_intern *m;
    char *mark = _th_alloc_mark(REWRITE_SPACE);

    //if (test==NULL) {
    //    test = _th_parse(env,"(rless x_8 x_7)");
    //}

    //if ((left==test && right==_ex_true) || (right==test && left==_ex_true)) {
    //    printf("%d: TEST MERGE %s ", _tree_zone, _th_print_exp(left));
    //    printf("AND %s\n", _th_print_exp(right));
    //}
    //if (testl==NULL) {
    //    testl = _th_parse(env, "(f5 c_0 c_0)");
    //    testr = _th_parse(env, "c_3");
    //    test = _th_parse(env, "(== (f5 c_0 c_0) c_3)");
    //}

#ifdef EXTENDED_CHECK2
    expl = explanation;
	while (expl) {
		struct _ex_intern *f1, *f2;
		if (expl->e->type==EXP_APPL && expl->e->u.appl.functor==INTERN_EQUAL) {
			f1 = expl->e->u.appl.args[0];
			f2 = expl->e->u.appl.args[1];
		} else if (expl->e->type==EXP_APPL && expl->e->u.appl.functor==INTERN_NOT) {
			f1 = expl->e->u.appl.args[0];
			f2 = _ex_false;
		} else {
			f1 = expl->e;
			f2 = _ex_true;
		}
    	while (f1->find != NULL && f1->find != f1) f1 = f1->find;
    	while (f2->find != NULL && f2->find != f2) f2 = f2->find;
		if (f1 != f2) {
			int i = 0;
			fprintf(stderr, "Illegal explanation being added %s\n", _th_print_exp(expl->e));
			fprintf(stderr, "    %s\n", _th_print_exp(f1));
			fprintf(stderr, "    %s\n", _th_print_exp(f2));
			fprintf(stderr, "for %s to", _th_print_exp(left));
			fprintf(stderr, " %s\n", _th_print_exp(right));
			i = 1/i;
		}
		expl = expl->next;
	}
#endif

#ifdef EXTENDED_CHECK
	if (left->type==EXP_APPL && left->u.appl.functor==INTERN_RAT_LESS &&
		left->u.appl.args[0]==left->u.appl.args[1]) {
		int i = 0;
		printf("Illegal rless merge 1\n");
		printf("left = %s\n", _th_print_exp(left));
		printf("right = %s\n", _th_print_exp(right));
		i = 1 / i;
	}
	if (right->type==EXP_APPL && right->u.appl.functor==INTERN_RAT_LESS &&
		right->u.appl.args[0]==right->u.appl.args[1]) {
		int i = 0;
		printf("Illegal rless merge 2\n");
		printf("left = %s\n", _th_print_exp(left));
		printf("right = %s\n", _th_print_exp(right));
		i = 1 / i;
	}
	if (left->type==EXP_APPL && left->u.appl.functor==INTERN_EQUAL && right==_ex_true) {
		l = left->u.appl.args[0];
		r = left->u.appl.args[1];
		while (l->merge) l = l->merge;
		while (r->merge) r = r->merge;
		if (l != r) {
			int i = 0;
			printf("Illegal equal merge\n");
			printf("left = %s\n", _th_print_exp(left));
			printf("right = %s\n", _th_print_exp(right));
			i = 1 / i;
		}
	}
	if (right->type==EXP_APPL && right->u.appl.functor==INTERN_EQUAL && left==_ex_true) {
		l = right->u.appl.args[0];
		r = right->u.appl.args[1];
		while (l->merge) l = l->merge;
		while (r->merge) r = r->merge;
		if (l != r) {
			int i = 0;
			printf("Illegal equal merge\n");
			printf("left = %s\n", _th_print_exp(left));
			printf("right = %s\n", _th_print_exp(right));
			i = 1 / i;
		}
	}
#endif

    _zone_print_exp("Merging", left);
    _zone_print_exp("and", right);
    _zone_print_exp("Connecting", lspot);
    _zone_print_exp("and", rspot);
    _tree_indent();

#ifndef FAST
    if (_zone_active()) {
        struct add_list *e = explanation;
        while (e) {
            _tree_print_exp("expl", e->e);
            e = e->next;
        }
    }
#endif
#ifdef XX
    //printf("Propagating %d %s\n", _tree_zone, _th_print_exp(left));
    //printf("    to %s\n", _th_print_exp(right));
    expl = explanation;
    while (expl) {
        //printf("e: %s\n", _th_print_exp(expl->e));
        expl = expl->next;
    }
#endif
    l = left;
    while (l->find && l != l->find) {
        l = l->find;
        //_zone_print_exp("l->find", l->find);
	}
    r = right;
    while (r->find && r != r->find) r = r->find;

    if (l==r) {
#ifndef FAST
        if (_zone_active()) {
            struct _ex_intern *e;
            l = left;
            r = right;
            if (l==_ex_true) {
                //_tree_print("Case 1");
                e = r;
            } else if (l==_ex_false) {
                if (r->type==EXP_APPL && r->u.appl.functor==INTERN_NOT) {
                    //_tree_print("Case 2");
                    e = r->u.appl.args[0];
                } else {
                    //_tree_print("Case 3");
                    e = _ex_intern_appl1_env(env,INTERN_NOT,r);
                }
            } else if (r==_ex_true) {
                //_tree_print("Case 4");
                e = l;
            } else if (r==_ex_false) {
                if (l->type==EXP_APPL && l->u.appl.functor==INTERN_NOT) {
                    //_tree_print("Case 5");
                    e = l->u.appl.args[0];
                } else {
                    //_tree_print_exp("Case 6", l);
                    e = _ex_intern_appl1_env(env,INTERN_NOT,l);
                }
            } else {
                //_tree_print("Case 7");
				if (is_real(env,l) || is_real(env,r)) {
                    e = _ex_intern_equal(env,_ex_real,l,r);
				} else if (is_integer(env,l) || is_integer(env,r)) {
                    e = _ex_intern_equal(env,_ex_int,l,r);
				} else if (is_bool(env,l) || is_bool(env,r)) {
                    e = _ex_intern_equal(env,_ex_bool,l,r);
				} else {
					fprintf(stderr, "Illegal equals %s", _th_print_exp(l));
					fprintf(stderr, " and %s\n", _th_print_exp(r));
					exit(1);
				}
            }
            _tree_print0("Equal terms");
            expl = _th_retrieve_explanation(env,e);
            //_tree_print("Here c");
            _tree_indent();
            while (expl) {
                //_tree_print("Here d");
                _tree_print_exp("e", expl->e);
                //_tree_print("Here e");
                expl = expl->next;
            }
            _tree_undent();
        }
#endif
        _tree_undent();
        //printf("Equal terms\n");
        _th_alloc_release(REWRITE_SPACE,mark);
        return 0;
    }

    if ((l==_ex_true || l==_ex_false || l->type==EXP_INTEGER || l->type==EXP_RATIONAL || l->type==EXP_STRING) &&
        (r==_ex_true || r==_ex_false || r->type==EXP_INTEGER || r->type==EXP_RATIONAL || r->type==EXP_STRING) &&
        disallow_const) {
        //printf("Constant contradiction\n");
        _zone_print0("Constant contradiction");
        _zone_print_exp("l", l);
        _zone_print_exp("r", r);
        explanation = quick_explanation(env,left,l,explanation);
        explanation = quick_explanation(env,right,r,explanation);
        contradiction = explanation;
        _tree_undent();
        //_th_alloc_release(REWRITE_SPACE,mark);
        return 1;
    }
    //printf("Doing merge\n");

    _zone_print_exp("l", l);
    _zone_print_exp("r", r);
    if (_th_term_compare(env,l,r) > 0) {
        struct _ex_intern *x = left;
        left = right;
        right = x;
        _zone_print0("Switch");
    }
    expl = lspot->explanation;
    m = lspot->merge;
    _zone_print_exp("Initial merge", lspot->merge);
    _th_add_merge_explanation(env,lspot,rspot,explanation);
    //if (left==testl && right==testr) exit(1);
    //if (left==testr && right==testl) exit(1);
    //if (left==test && right==_ex_true) exit(1);
    //if (left==_ex_true && right==test) exit(1);
    //if (left==test && explanation==NULL) exit(1);
    //if (right==test && explanation==NULL) exit(1);
    //if (l==test || r==test ||
    //    (l==testl && r==testr) ||
    //    (l==testr && r==testl)) {
    //    printf("    left = %s\n", _th_print_exp(l));
    //    printf("    right = %s\n", _th_print_exp(r));
    //}
    //fprintf(stderr, "Merging %s\n", _th_print_exp(left));
    //fprintf(stderr, "    and %s\n", _th_print_exp(right));
    l = lspot;
    while (m) {
        r = m;
        m = r->merge;
        explanation = expl;
        expl = r->explanation;
        _zone_print_exp("New merge", m);
        _zone_print_exp("Adding sub merge", r);
        _zone_print_exp("to", l);
        _th_add_merge_explanation(env,r,l,explanation);
        l = r;
        //if (l==testl && r==testr) exit(1);
        //if (l==testr && r==testl) exit(1);
        //if (l==test && r==_ex_true) exit(1);
        //if (r==test && l==_ex_true) exit(1);
        //if (l==test && explanation==NULL) exit(1);
        //if (r==test && explanation==NULL) exit(1);
    }
    //has_false_cycle();

    r = right;
    while (r->find && r->find != r) r = r->find;
    //l = left;
    //while (l->find && l->find != l) {
    //    l = l->find;
    //}
    //if (l==r) {
    //    _zone_print0("Equal");
    //    _tree_undent();
    //    return 0;
    //}

    l = left;
    while (l->find != NULL && l->find != l) {
        struct _ex_intern *x = l->find;
        _zone_print_exp("assign", l);
        _th_add_find(env,l,r);
        l = x;
    }

    _zone_print_exp("assign2", l);
    _zone_print_exp("left", left);
    _zone_print_exp("right", r);
    _th_add_find(env,l,r);

	if (get_type(env,l)==_ex_real || get_type(env,r)==_ex_real) {
		if (_th_add_reduction(env,_ex_intern_equal(env,_ex_real,l,r),l,r, NULL, &contradiction)) {
            return 1;
		}
    }
    if (_th_do_implications) {
        struct _ex_intern *x;
        struct _ex_intern *test;
        //if (r==_ex_true) {
        //    x = left;
        //} else if (r==_ex_false) {
        //    x = _ex_intern_appl1_env(env,INTERN_NOT,l);
        //} else {
            x = _ex_intern_equal(env,get_type(env,l),l,r);
            x = _th_nc_rewrite(env,x);
        //}
        test = _th_check_cycle_rless(env,x,&contradiction);
        _zone_print_exp("test", test);
        _th_prepare_node_implications(env, x);
        if (test==_ex_false || add_implications(env,x)) {
            _zone_print0("add implication contradiction");
            _tree_undent();
            //_th_alloc_release(REWRITE_SPACE,mark);
            return 1;
        }
    }
    //has_false_cycle();

    parents = l->used_in;

    while (parents) {
        struct _ex_intern *e = parents->e;
        _zone_print_exp("Processing parent", e);
        //if (!e->in_hash) new_expr(env,e,NULL);
        //printf("Processing parent %s\n", _th_print_exp(e));
        //printf("    of %s\n", _th_print_exp(left));
        _tree_indent();
        _zone_print_exp("Signature", e->sig);
        if (e->sig==e) {
            _th_add_signature(env,e,signature_expl(env,e,NULL));
            _zone_print_exp("Computed signature", e->sig);
            l = e;
            //while (l->rewrite && l->rewrite != l) l = l->rewrite;
            while (l->find && l->find != l) l = l->find;
            _zone_print_exp("find", l);
            r = e->sig;
            while (r->find && r->find != r) r = r->find;
            _zone_print_exp("find(signature)", r);
            if (l!=r) {
                struct add_list *ex, *ee;
                //expl = (struct add_list *)_th_alloc(_th_get_space(env),sizeof(struct add_list));
                //expl->next = ret_expl;
                //expl->e = _ex_intern_appl2_env(env,INTERN_EQUAL,left,right);
                expl = ret_expl;
                if (e==l) {
                    if (merge(env,e,e->sig,e,e->sig,expl,disallow_const)) {
                        _zone_print0("Contradiction");
                        _tree_undent();
                        _tree_undent();
                        if (contradiction) {
                            ex = contradiction;
                            while (ex->next) {
                                ex = ex->next;
                            }
                            ex->next = expl;
                        } else {
                            contradiction = expl;
                        }
                        //_th_alloc_release(REWRITE_SPACE,mark);
                        return 1;
                    }
                } else {
                    struct _ex_intern *x;
                    struct _ex_intern *ce;
                    if (is_integer(env,l) || is_integer(env,r)) {
                        x = _ex_intern_equal(env,_ex_int,l,r);
                    } else if (is_real(env,l) || is_real(env,r)) {
                        x = _ex_intern_equal(env,_ex_real,l,r);
					} else if (is_bool(env,l) || is_bool(env,r)) {
						x = _ex_intern_equal(env,_ex_bool,l,r);
					} else {
						fprintf(stderr, "Illegal equality %s", _th_print_exp(l));
						fprintf(stderr, " %s\n", _th_print_exp(r));
						exit(1);
					}
					ce = x;
                    x = new_expr(env,x,&ex);
                    if (expl==NULL) {
                        expl = ex;
                    } else {
                        ee = expl;
                        while (ee->next != NULL) {
                            ee = ee->next;
                        }
                        ee->next = ex;
                    }
                    expl = quick_explanation(env,l,e,expl);
                    expl = quick_explanation(env,r,e->sig,expl);
#ifndef FAST
                    if (_zone_active()) {
                        _tree_print0("Explanation");
                        _tree_indent();
                        print_explanation_list(env,expl);
                        _tree_undent();
                    }
#endif
                    if (do_assert(env,x,x,expl)) {
                        struct add_list *c;
                        _zone_print_exp("Contradiction", x);
                        //c = contradiction;
                        //while (c && c->next) {
                        //    c = c->next;
                        //}
                        //if (c) {
                        //    c->next = expl;
                        //    c = contradiction;
                        //} else {
                        //    c = expl;
                        //}
                        c = contradiction;
                        contradiction = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                        contradiction->next = c;
                        if (x->type==EXP_APPL && x->u.appl.functor==INTERN_NOT) {
                            contradiction->e = x->u.appl.args[0];
                        } else {
                            contradiction->e = _ex_intern_appl1_env(env,INTERN_NOT,x);
                        }
                        //merge(env,ce,_ex_false,ce,false,copy_list(_th_get_space(env),contradiction->next),0);
                        if (contradiction->e->type==EXP_APPL && contradiction->e->u.appl.functor==INTERN_NOT) {
                            merge(env,contradiction->e->u.appl.args[0],_ex_true,contradiction->e->u.appl.args[0],_ex_true,copy_list(_th_get_space(env),contradiction->next),0);
                        } else {
                            merge(env,contradiction->e,_ex_false,contradiction->e,_ex_false,copy_list(_th_get_space(env),contradiction->next),0);
                        }
                        //_th_alloc_release(REWRITE_SPACE,mark);
#ifndef FAST
                        if (_zone_active()) {
                            _tree_print0("Contradiction explanation");
                            _tree_indent();
                            print_explanation_list(env,contradiction);
                            _tree_undent();
                        }
#endif
                        _tree_undent();
                        _tree_undent();
                        return 1;
                    }
                }
            }
        } else {
            _zone_print_exp("Sig different", e->sig);
        }
        _tree_undent();
        parents = parents->next;
    }

    _tree_undent();
    _th_alloc_release(REWRITE_SPACE,mark);
    return 0;
}

//static struct _ex_intern *tt = NULL;

struct implication_list  {
    struct implication_list *next;
    struct _ex_intern *e, *r;
    struct add_list *expl;
};

static int add_implications(struct env *env, struct _ex_intern *e)
{
    struct add_list *parents, *expl;
    struct _ex_intern *l;
    struct implication_list *list, *n;
    //char *mark;

    //mark = _th_alloc_mark(REWRITE_SPACE);

    //printf("Adding implications for %s\n", _th_print_exp(e));

    if ((e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL) ||
        (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_LESS) ||
        (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT &&
         e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_RAT_LESS)) {
        _zone_print_exp("Adding implications for", e);
        _tree_indent();
        parents = _th_collect_impacted_terms(env,e);
        if (e->u.appl.functor!=INTERN_EQUAL) _th_prepare_quick_implications(env,e);
        //check_missed_term(env,parents);
        list = NULL;
        while (parents) {
            struct _ex_intern *e = parents->e;
            _zone_print_exp("Processing impact parent", e);
            _tree_indent();
            _zone_print_exp("Signature", e->sig);
            if (e->sig==e) {
                _zone_print_exp("Computed signature", e->sig);
                l = e;
                while (l->find && l->find !=l) {
                    l = l->find;
                }
                _zone_print_exp("l",l);
                _zone_print_exp("e",e);
                if (l==e) {
                    l = _th_get_quick_implication(env,e,&expl);
                    if (l) {
						_zone_print_exp("l implication", l);
                        n = (struct implication_list *)ALLOCA(sizeof(struct implication_list));
                        n->next = list;
                        list = n;
						if (l==_ex_true && e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL) {
							l = e->u.appl.args[0];
							e = e->u.appl.args[1];
							if (_th_term_compare(env,e,l) > 0) {
								struct _ex_intern *x = e;
								e = l;
								l = x;
							}
						}
                        list->e = e;
                        list->r = l;
                        list->expl = expl;
                    }
                }
            } else {
                _zone_print_exp("Sig different", e->sig);
            }
            _tree_undent();
            parents = parents->next;
        }
        //printf("%d: Adding implications for %x %s\n", _tree_zone, env, _th_print_exp(e));
        while (list) {
            struct _ex_intern *e = list->e;
            l = list->r;
#ifndef FAST
            if (_zone_active()) {
                struct add_list *ex = list->expl;
                _tree_print("Before explanation");
                _tree_indent();
                while (ex) {
                    _tree_print_exp("before expl", ex->e);
                    ex = ex->next;
                }
                _tree_undent();

            }
#endif
            if (!l->in_hash) {
                //_zone_print("Case 1");
                l = simp_expl(env,l,list->expl);
                list->expl = ret_expl;
            } else {
                _zone_print_exp("Case 2", l);
                while (l->find != l) l = l->find;
                list->expl = quick_explanation(env,l,list->r,list->expl);
            }
            //printf("    %s reduces to", _th_print_exp(e));
            //printf(" %s\n", _th_print_exp(l));
            _zone_print_exp("Merging", e);
            _zone_print_exp("and", l);
            _tree_indent();
            _th_add_signature(env,e,signature_expl(env,e,NULL));
            _tree_undent();
            _zone_print_exp("Reducing", e);
            _zone_print_exp("to", l);
            _tree_indent();
            //struct add_list *ee = expl;
            //printf("    Merging %s and", _th_print_exp(e));
            //printf(" %s\n", _th_print_exp(l));
            //while (ee) {
            //    printf("        %s\n", _th_print_exp(ee->e));
            //    ee = ee->next;
            //}
            //printf("start merge: add_implications\n");
            if (merge(env,e,l,e,l,copy_list(_th_get_space(env),list->expl),1)) {
                //_th_alloc_release(REWRITE_SPACE, mark);
                _tree_undent();
                _tree_undent();
                return 1;
            }
            _tree_undent();
            list = list->next;
        }
        _tree_undent();
    }
    //_th_alloc_release(REWRITE_SPACE, mark);

    return 0;
}

static int same_val(struct _ex_intern *e1, struct _ex_intern *e2)
{
    while (e1->find && e1->find != e1) e1 = e1->find;
    while (e2->find && e2->find != e2) e2 = e2->find;

    return e1==e2;
}

static int do_assert(struct env *env, struct _ex_intern *pred, struct _ex_intern *orig, struct add_list *explanation)
{
    struct _ex_intern *left, *right, *x, *oleft, *oright;
    char *mark = _th_alloc_mark(REWRITE_SPACE);

    //++in_assert;

    _zone_increment();
    //printf("DO ASSERT %s\n", _th_print_exp(pred));

    //eqtest = _ex_intern_appl2_env(env,INTERN_EQUAL,_ex_intern_var(_th_intern("c_0")),_ex_intern_var(_th_intern("c_1")));

    //if (tt==NULL) tt = _th_parse(env,"c13");

    _zone_print_exp("do_assert", pred);

    //if (pred==tt || (pred->type==EXP_APPL && pred->u.appl.functor==INTERN_EQUAL &&
        //(pred->u.appl.args[0]==tt || pred->u.appl.args[1]==tt))) {
        //printf("Asserting %d %s\n", _tree_zone, _th_print_exp(pred));
        //while (explanation !=  NULL) {
        //    printf("    %s\n", _th_print_exp(explanation->e));
        //    explanation = explanation->next;
        //}
        //exit(1);
    //}

    //if (explanation==NULL && (pred==tt || pred->original==tt)) {
    //    printf("Asserting at %d %s\n", _tree_zone, _th_print_exp(pred->original));
    //}

    if (pred==orig) {
        if (pred->type==EXP_APPL && pred->u.appl.functor==INTERN_NOT) {
            oleft = left = pred->u.appl.args[0];
            oright = right = _ex_false;
        } else if (pred->type==EXP_APPL && pred->u.appl.functor==INTERN_EQUAL) {
            oleft = left = pred->u.appl.args[0];
            oright = right = pred->u.appl.args[1];
        } else {
            oleft = left = pred;
            oright = right = _ex_true;
        }
    } else {        
        if (orig->type==EXP_APPL && orig->u.appl.functor==INTERN_NOT) {
            oleft = orig->u.appl.args[0];
            left = simp_expl(env,oleft,NULL);
			if (left != oleft) {
				if (merge(env,left,oleft,left,oleft,copy_list(_th_get_space(env),ret_expl),0)) {
					return 1;
				}
			}
            right = oright = _ex_false;
        } else if (orig->type==EXP_APPL && orig->u.appl.functor==INTERN_EQUAL) {
            oleft = orig->u.appl.args[0];
            left = simp_expl(env,oleft,NULL);
			if (left != oleft) {
				if (merge(env,left,oleft,left,oleft,copy_list(_th_get_space(env),ret_expl),0)) {
					return 1;
				}
			}
            oright = orig->u.appl.args[1];
            right = simp_expl(env,oright,NULL);
			if (right != oright) {
				if (merge(env,right,oright,right,oright,copy_list(_th_get_space(env),ret_expl),0)) {
					return 1;
				}
			}
        } else {
            oleft = orig;
            left = simp_expl(env,oleft,NULL);
			if (left != oleft) {
				if (merge(env,left,oleft,left,oleft,copy_list(_th_get_space(env),ret_expl),0)) {
					return 1;
				}
			}
            right = oright = _ex_true;
        }
        
        if ((!same_val(left,oleft) && !same_val(left,oright)) ||
            (!same_val(right,oleft) && !same_val(right,oright))) {
            fprintf(stderr, "Equality of subterms error\n");
            exit(1);
        }
    }
    rewrite_n = NULL;

    //while (left->find != NULL && left->find != left) {
    //    left = left->find;
    //}
    //while (right->find != NULL && right->find != right) {
    //    right = right->find;
    //}

    //printf("start merge: do_assert\n");
    if (merge(env,left,right,oleft,oright,explanation,1)) {
        //printf("Failed\n");
        //_th_alloc_release(REWRITE_SPACE,mark);
        //--in_assert;
        return 1;
    }
    if (right==_ex_true && (x = _th_check_cycle_rless(env,left,&contradiction))) {
        if (x == _ex_false || add_implications(env,left)) {
            //--in_assert;
            return 1;
        }
    } else if (right==_ex_false && (x = _th_check_cycle_rless(env,left,&contradiction))) {
        if (x == _ex_true || add_implications(env,_ex_intern_appl1_env(env,INTERN_NOT,left))) {
            //--in_assert;
            return 1;
        }
    }
    //while (rewrite_n) {
    //    left = rewrite_n;
    //    rewrite_n->user2 = NULL;
    //    rewrite_n = rewrite_n->next_cache;
    //    if (process_term(env,left)) {
    //        while (rewrite_n) {
    //            rewrite_n->user2 = NULL;
    //            rewrite_n = rewrite_n->next_cache;
    //        }
    //        return 1;
    //    }
    //}
    //_th_collect_and_print_classes(env,0);

    _th_alloc_release(REWRITE_SPACE,mark);
    //--in_assert;
    return 0;
}

static void check_failure(struct _ex_intern *e)
{
    if (e->type==EXP_APPL) {
        int i;
        if (e->u.appl.functor==INTERN_EQUAL) {
            if (e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_RAT_PLUS) {
                for (i = 0; i < e->u.appl.args[0]->u.appl.count; ++i) {
                    if (e->u.appl.args[0]->u.appl.args[i]==e->u.appl.args[1]) exit(1);
                }
            }
            if (e->u.appl.args[1]->type==EXP_APPL && e->u.appl.args[1]->u.appl.functor==INTERN_RAT_PLUS) {
                for (i = 0; i < e->u.appl.args[1]->u.appl.count; ++i) {
                    if (e->u.appl.args[1]->u.appl.args[i]==e->u.appl.args[0]) exit(1);
                }
            }
        }
        for (i = 0; i < e->u.appl.count; ++i) {
            check_failure(e->u.appl.args[i]);
        }
    }
}

//extern int has_positive_cycle(struct env *env);

//static struct _ex_intern *v1 = NULL, *v2, *v3;

#define TEST_SPRED

int _th_assert_predicate(struct env *env, struct _ex_intern *pred)
{
    int x;
    struct add_list *expl;
    //static struct _ex_intern *test = NULL;
    char *mark = _th_alloc_mark(REWRITE_SPACE);
    struct _ex_intern *spred;
    //void *merge_mark;

    //if (test==NULL) test = _th_parse(env,"(== x_6 x_8)");
    //if (pred==test) exit(1);
    //if (pred->type==EXP_APPL && (pred->u.appl.functor==INTERN_RAT_LESS || pred->u.appl.functor==INTERN_EQUAL)) {
    //    if (v1==NULL) v1 = _th_parse(env,"x_92");
    //    if (v2==NULL) v2 = _th_parse(env,"x_88");
    //    if (v3==NULL) v3 = _th_parse(env,"x_89");
    //    if (pred->u.appl.args[0]==v1 || pred->u.appl.args[0]==v2 || pred->u.appl.args[0]==v3 ||
    //        pred->u.appl.args[1]==v1 || pred->u.appl.args[1]==v2 || pred->u.appl.args[1]==v3) {
    //        printf("%d %d %s\n", _tree_zone, _th_get_indent(), _th_print_exp(pred));
    //        printf("    v1->find = %s\n", _th_print_exp(v1->find));
    //        printf("    v2->find = %s\n", _th_print_exp(v2->find));
    //        printf("    v3->find = %s\n", _th_print_exp(v3->find));
    //    }
    //}
#ifndef FAST
    if (_zone_active()) _th_print_difference_table(env);
#endif

    //struct _ex_intern *original = pred;

    _zone_print2("Asserting predicate %d %s", _tree_zone, _th_print_exp(pred));
    _tree_indent();
    _zone_print_exp("rewrite", pred->rewrite);

    if (pred != _ex_true && pred->type==EXP_APPL && pred->u.appl.functor != INTERN_NOT && (!pred->in_hash || pred->find != pred)) {
//#ifdef TEST_SPRED
//        struct _ex_intern *s1, *p1;
//#endif
        //_tree_print("Here1");
        spred = simp_expl(env,pred,NULL);
//#ifdef TEST_SPRED
//        s1 = spred;
//        p1 = pred;
//        while (s1->merge) s1 = s1->merge;
//        while (p1->merge) p1 = p1->merge;
//        if (s1 != p1) {
//            fprintf(stderr, "Terms different\n");
//            exit(1);
//        }
//#endif
        //fprintf(stderr, "Predicate %s being asserted is not simplified\n", _th_print_exp(pred));
        //exit(1);
        if (spred==_ex_false) {
            //merge(env,pred,_ex_false,pred,_ex_false,copy_list(_th_get_space(env),ret_expl),0);
            _tree_undent();
            _th_alloc_release(REWRITE_SPACE,mark);
            return 1;
        }
    } else {
        spred = pred;
    }
#ifdef PRINT1
	if (pred->type != EXP_APPL && pred->u.appl.functor!=INTERN_NOT) {
		struct _ex_intern *spred = _th_check_cycle_rless(env,pred,&expl);
		if (spred==_ex_false && spred != NULL) {
			fprintf(stderr, "assert bug %s\n", _th_print_exp(pred));
			fprintf(stderr, "spred %s\n", _th_print_exp(spred));
			fprintf(stderr, "env %x\n", env);
			exit(1);
		}
	}
	if (spred->type != EXP_APPL && spred->u.appl.functor!=INTERN_NOT) {
		struct _ex_intern *pred = _th_check_cycle_rless(env,spred,&expl);
		if (pred==_ex_false && pred != NULL) {
			fprintf(stderr, "assert bug 2 %s\n", _th_print_exp(pred));
			fprintf(stderr, "spred %s\n", _th_print_exp(spred));
			exit(1);
		}
	}
#endif

    //check_failure(pred);

    //printf("ASSERTING %s\n", _th_print_exp(pred));

    //check_env(env, "a");
    //check_cycle(env, "assert 1");
    if (pred->type==EXP_APPL && pred->u.appl.functor==INTERN_NOT) {
        _tree_undent();
        _th_alloc_release(REWRITE_SPACE,mark);
        return _th_deny_predicate(env,pred->u.appl.args[0]);
    }

    //if (_th_incomplete_decision_procedure(env,spred)) _th_unknown = 1;

    if (pred->type==EXP_APPL && pred->u.appl.functor==INTERN_EQUAL) {
        if (pred->u.appl.args[0]==_ex_false) {
            _tree_undent();
            _th_alloc_release(REWRITE_SPACE,mark);
            return _th_deny_predicate(env,pred->u.appl.args[1]);
        } else if (pred->u.appl.args[1]==_ex_false) {
            _tree_undent();
            _th_alloc_release(REWRITE_SPACE,mark);
            return _th_deny_predicate(env,pred->u.appl.args[0]);
        }
    }
#ifdef XX
    if ((pred->cache_bad || pred->rewrite==NULL || pred->rewrite != pred ||
        pred->find != pred)) {
        _zone_print1("pred->cache_bad %d", pred->cache_bad);
        _zone_print_exp("before rewrite", pred->rewrite);
        pred = _th_simp(env,pred);
    }
    if (pred==_ex_false) {
        _tree_undent();
        _th_alloc_release(REWRITE_SPACE,mark);
        return 1;
    }
#endif

    //r = _th_check_cycle_rless(env,pred,&expl);
    //if (r==_ex_false) {
    //    //printf("Failed check\n");
    //    merge(env,pred,_ex_false,expl);
    //    x = 1;
    //    goto end;
    //if (r != NULL && r->type==EXP_APPL && r->u.appl.functor==INTERN_EQUAL) {
    //    //printf("Adding equalities for %s\n", _th_print_exp(pred));
    //    cl = _th_get_equal_cycle_info(env,r);
    //    while (cl) {
    //        if (do_assert(env,_th_int_rewrite(env,cl->e,0),cl->explanation)) {
    //            merge(env,pred,_ex_false,contradiction);
    //            x = 1;
    //            goto end;
    //        }
    //        cl = cl->next;
    //    }
    //}
    //_th_add_original(env,pred,original);
	//merge_mark = _th_quick_mark(env);
#ifdef PRINT1
	if (pred != spred) {
		fprintf(stderr, "pred = %s\n", _th_print_exp(pred));
		fprintf(stderr, "spred = %s\n", _th_print_exp(spred));
	}
#endif
	if (_th_add_predicate(env,pred, &expl)) {
        //printf("start merge: deny merge 1\n");
        merge(env,pred,_ex_false,pred,_ex_false,copy_list(_th_get_space(env),expl),0);
        x = 1;
    } else {
        x = do_assert(env,spred,pred,NULL);
        //if (!x) _th_derive_add_prepared(env,rule);
        if (x) {
            //fprintf(stderr, "predicate %s\n", _th_print_exp(pred));
            //fprintf(stderr, "CONTRADICTION %x\n", contradiction);
            //printf("start merge: deny merge 2\n");
            merge(env,pred,_ex_false,pred,_ex_false,copy_list(_th_get_space(env),contradiction),0);
            //while (contradiction) {
                //fprintf(stderr, "    contr %s\n", _th_print_exp(contradiction->e));
                //contradiction = contradiction->next;
            //}
        }
    }
    //check_cycle(env, "assert 7");
    //check_env(env, "e");
    _tree_undent();
#ifndef FAST
    //if (!x) _th_collect_and_print_classes(env,1);
#endif
    //if (has_positive_cycle(env)) {
    //    fprintf(stderr, "Undetected cycle\n");
    //    exit(1);
    //}
	//if (x) {
	//	_th_quick_pop(env,merge_mark);
	//}
    _th_alloc_release(REWRITE_SPACE,mark);
    return x;
}

int _th_deny_predicate(struct env *env, struct _ex_intern *pred)
{
    //struct _ex_intern *rule;
    int x;
    struct add_list *expl;
    char *mark = _th_alloc_mark(REWRITE_SPACE);
    struct _ex_intern *spred;
    //void *merge_mark;

#ifndef FAST
    if (_zone_active()) _th_print_difference_table(env);
#endif
    //struct _ex_intern *original = pred;

    _zone_print_exp("Denying predicate", pred);
    _tree_indent();

    if (pred->type==EXP_APPL && pred->u.appl.functor != INTERN_NOT && (!pred->in_hash || pred->find != pred)) {
        spred = simp_expl(env,pred,NULL);
        //fprintf(stderr, "Predicate %s being denied is not simplified\n", _th_print_exp(pred));
        //fprintf(stderr, "find: %s\n", _th_print_exp(pred->find));
        //exit(1);
        if (spred==_ex_true) {
            //merge(env,pred,_ex_false,copy_list(_th_get_space(env),ret_expl),0);
            _tree_undent();
			//printf("Simplified %s to true\n", _th_print_exp(pred));
            _th_alloc_release(REWRITE_SPACE,mark);
            return 1;
        }
    } else {
        spred = pred;
    }
    //printf("DENYING %s\n", _th_print_exp(pred));

    //check_failure(pred);
#ifdef PRINT1
	if (pred->type != EXP_APPL && pred->u.appl.functor!=INTERN_NOT) {
		struct _ex_intern *spred = _th_check_cycle_rless(env,pred,&expl);
		if (spred==_ex_true && spred != NULL) {
			fprintf(stderr, "deny bug %s\n", _th_print_exp(pred));
			fprintf(stderr, "spred %s\n", _th_print_exp(spred));
			exit(1);
		}
	}
	if (spred->type != EXP_APPL && spred->u.appl.functor!=INTERN_NOT) {
		struct _ex_intern *pred = _th_check_cycle_rless(env,spred,&expl);
		if (pred==_ex_true && pred != NULL) {
			fprintf(stderr, "deny bug 2 %s\n", _th_print_exp(pred));
			fprintf(stderr, "spred %s\n", _th_print_exp(spred));
			exit(1);
		}
	}
#endif

    _zone_print_exp("rewrite", pred->rewrite);
    //rule = pred;
    //while (rule->rewrite && rule->rewrite != rule) rule = rule->rewrite;
    //_zone_print_exp("rule", rule);

    //check_cycle(env, "deny 1");
    if (pred->type==EXP_APPL && pred->u.appl.functor==INTERN_NOT) {
        _tree_undent();
        _th_alloc_release(REWRITE_SPACE,mark);
        return _th_assert_predicate(env,pred->u.appl.args[0]);
    }

    //if (_th_incomplete_decision_procedure(env,spred)) _th_unknown = 1;

    if (pred->type==EXP_APPL && pred->u.appl.functor==INTERN_EQUAL) {
        if (pred->u.appl.args[0]==_ex_false) {
            _tree_undent();
            _th_alloc_release(REWRITE_SPACE,mark);
            return _th_assert_predicate(env,pred->u.appl.args[1]);
        } else if (pred->u.appl.args[1]==_ex_false) {
            _tree_undent();
            _th_alloc_release(REWRITE_SPACE,mark);
            return _th_assert_predicate(env,pred->u.appl.args[0]);
        }
    }
#ifdef XX
    if ((pred->cache_bad || pred->rewrite==NULL || pred->rewrite != pred ||
         pred->find != pred)) {
        pred = _th_simp(env,pred);
    }
    if (pred==_ex_true) {
        _tree_undent();
        _th_alloc_release(REWRITE_SPACE,mark);
        return 1;
    }
#endif

    //_th_add_original(env,pred,original);
    pred = _ex_intern_appl1_env(env,INTERN_NOT,pred);
    spred = _ex_intern_appl1_env(env,INTERN_NOT,spred);
    //check_cycle(env, "deny 2");
    //rule = _th_derive_prepare(env, _th_mark_vars(env, pred));
    //check_cycle(env, "deny 3");
    //if (!pred->in_hash) pred = _th_simp(env,pred);
    //r = _th_check_cycle_rless(env,pred,&expl);
    //printf("r = %s\n", _th_print_exp(r));
    //if (r==_ex_false) {
    //    //printf("Failed check\n");
    //    merge(env,pred->u.appl.args[0],_ex_true,expl);
    //    x = 1;
    //    goto end;
    //if (r != NULL && r->type==EXP_APPL && r->u.appl.functor==INTERN_EQUAL) {
    //    //printf("Adding equalities for %s\n", _th_print_exp(pred));
    //    cl = _th_get_equal_cycle_info(env,r);
    //    while (cl) {
    //        if (do_assert(env,_th_int_rewrite(env,cl->e,0),cl->explanation)) {
    //            merge(env,pred->u.appl.args[0],_ex_true,contradiction);
    //            x = 1;
    //            goto end;
    //        }
    //        cl = cl->next;
    //    }
    //}
    //merge_mark = _th_quick_mark(env);
	if (_th_add_predicate(env,pred, &expl)) {
        //printf("start merge: deny merge 3\n");
        x = 1;
		contradiction = expl;
		goto fail_merge;
//      merge(env,pred->u.appl.args[0],_ex_true,pred->u.appl.args[0],_ex_true,copy_list(_th_get_space(env),expl),0);
    } else {
        x = do_assert(env,spred,pred,NULL);
        //if (!x) _th_derive_add_prepared(env,rule);
        if (x) {
			struct _ex_intern *e;
            //fprintf(stderr, "Adding contradiction %x\n", contradiction);
            //fprintf(stderr, "    Pred %s\n", _th_print_exp(pred));
            //printf("start merge: deny merge 4\n");
fail_merge:
			e = pred->u.appl.args[0];
			if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL) {
			    merge(env,e->u.appl.args[0],e->u.appl.args[1],e->u.appl.args[0],e->u.appl.args[1],copy_list(_th_get_space(env),contradiction),0);
			} else {
			    merge(env,e,_ex_true,e,_ex_true,copy_list(_th_get_space(env),contradiction),0);
			}
        }
    }
    //check_cycle(env, "deny 4");

    _tree_undent();
#ifndef FAST
    //if (!x && rec_entry==0) _th_collect_and_print_classes(env,1);
#endif
    //if (has_positive_cycle(env)) {
    //    fprintf(stderr, "Undetected cycle\n");
    //    exit(1);
    //}

	//if (x) _th_quick_pop(env,merge_mark);
    _th_alloc_release(REWRITE_SPACE,mark);
    return x;

    //if (_th_add_rule_and_implications(env,_th_mark_vars(env,_ex_intern_appl1_env(env,INTERN_NOT,pred)))) return 1;
    //if (pred->type==EXP_APPL && pred->u.appl.functor==INTERN_EQUAL) {
    //    if (_th_add_inequality(ENVIRONMENT_SPACE,env,pred->u.appl.args[0],pred->u.appl.args[1])) return 1;
    //} else {
    //    if (_th_add_equality(ENVIRONMENT_SPACE,env,pred,_ex_false)) return 1;
    //}
    //return 0;
}

void _th_block_predicate(struct env *env, struct _ex_intern *pred)
{
    struct _ex_intern *rule = _th_derive_prepare(env, _th_mark_vars(env, pred));
    _th_set_block_rule(ENVIRONMENT_SPACE,env,rule);
}

int _th_reassert_unblocked_rules(struct env *env)
{
    struct rule *cr;
    struct _ex_intern *r;

    _zone_print0("reassert");
    _tree_indent();
    r = _th_get_first_context_rule(env,&cr);
    while (r) {
        if (!r->rule_blocked) {
            struct _ex_intern *e = _th_unmark_vars(env,r);
            if (e->u.appl.args[2]==_ex_true) {
                if (e->u.appl.args[1]==_ex_true) {
                    e = e->u.appl.args[0];
                } else if (e->u.appl.args[1]==_ex_false) {
                    e = _ex_intern_appl1_env(env,INTERN_NOT,e->u.appl.args[0]);
                } else {
                    e = _ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0],e->u.appl.args[1]);
                }
                _zone_print_exp("e", e);
                _zone_print_exp("e->rewrite", e->rewrite);
                _zone_print1("e->cache_bad %d", e->cache_bad);
                if (do_assert(env,e,e,NULL)) {
                    _zone_print0("contradiction");
                    _tree_undent();
                    return 1;
                }
            }
        } else {
            _zone_print_exp("Skipping rule", r);
        }
        r = _th_get_next_rule(env,&cr);
    }

    _tree_undent();

    return 0;
}

static struct _ex_intern *trail;

#ifndef FAST
static void check_term(struct _ex_intern *e)
{
    struct _ex_intern *t = trail;

    while (t && t != _ex_true) {
        if (t==e) return;
        t = t->user2;
    }

    if (!t) {
        fprintf(stderr, "Illegal trail\n");
        while (trail) {
            fprintf(stderr, "    %s\n", _th_print_exp(trail));
            trail = trail->user2;
        }
        exit(1);
    }

    fprintf(stderr, "Illegal user2 setting for %s", _th_print_exp(e));
    fprintf(stderr, " (%x:%s)\n", e->user2, _th_print_exp(e->user2));
    exit(1);
}
#endif

struct add_list *add_explanation_list(struct env *env, struct add_list *elist, struct add_list *tail);

struct add_list *merge_explanation(struct env *env, struct _ex_intern *left, struct _ex_intern *right, struct add_list *explanation)
{
    struct _ex_intern *l, *ancestor;
    struct add_list *expl;

    l = left;

    _zone_print_exp("Getting merge explanation", left);
    _zone_print_exp("and", right);

    if (left==right) return explanation;

    _tree_indent();

    while (l->merge) {
        l->user2 = (((int)l->user2) | 1);
        l = l->merge;
        _zone_print_exp("Left merge", l);
    }

    ancestor = right;
    while ((((int)ancestor->user2)&1)==0 && ancestor->merge) {
        ancestor = ancestor->merge;
        _zone_print_exp("right merge", ancestor->merge);
    }
    _zone_print_exp("Ancestor", ancestor);
    if (!ancestor->merge && l != ancestor) {
        l = left;
        while (l->merge) {
            l->user2 = (((int)l->user2) & 0xfffffffe);
            l = l->merge;
        }
        _tree_undent();
        //printf("No common root\n");
        //printf("    %s\n", _th_print_exp(left));
        //printf("    %s\n", _th_print_exp(right));
        return NULL;
        //fprintf(stderr, "Explanation error, terms not merged\n");
        //fprintf(stderr, "    left = %s\n", _th_print_exp(left));
        //while (left->merge) {
        //    left = left->merge;
        //    fprintf(stderr,"        %s\n", _th_print_exp(left));
        //}
        //fprintf(stderr, "    right = %s\n", _th_print_exp(right));
        //while (right->merge) {
        //    right = right->merge;
        //    fprintf(stderr,"        %s\n", _th_print_exp(right));
        //}
        //exit(1);
    }
    l = left;
    while (l->merge) {
        l->user2 = (((int)l->user2) & 0xfffffffe);
        l = l->merge;
    }

    l = left;
    while (l != ancestor) {
#ifndef FAST
        if (_zone_active()) {
            struct add_list *expl = l->explanation;
            _zone_print_exp("Left term explanation", l);
            _tree_indent();
            while (expl) {
                _zone_print_exp("expl", expl->e);
                expl = expl->next;
            }
            _tree_undent();
        }
#endif
        //if (l==NULL) exit(1);
        if (l->explanation==NULL) {
            if (l->merge) {
                expl = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                expl->next = explanation;
                if (l->merge==_ex_true) {
                    expl->e = l;
                } else if (l->merge==_ex_false) {
                    expl->e = _ex_intern_appl1_env(env,INTERN_NOT,l);
                } else {
					if (is_bool(env,l) || is_bool(env,l->merge)) {
                        expl->e = _ex_intern_equal(env,_ex_bool,l,l->merge);
					} else if (is_real(env,l) || is_real(env,l->merge)) {
						expl->e = _ex_intern_equal(env,_ex_real,l,l->merge);
					} else if (is_integer(env,l) || is_integer(env,l->merge)) {
						expl->e = _ex_intern_equal(env,_ex_int,l,l->merge);
					} else {
						fprintf(stderr, "Illegal merge equal 1 %s", _th_print_exp(l));
						fprintf(stderr, " and %s\n", _th_print_exp(l->merge));
					}
                }
                explanation = expl;
            }
        } else {
            //printf("l = %s\n", _th_print_exp(l));
            //fflush(stdout);
            explanation = add_explanation_list(env, l->explanation, explanation);
            //if (explanation==NULL) {
            //    _tree_undent();
            //    return NULL;
            //}
        }
        l = l->merge;
    }
    l = right;
    while (l != ancestor) {
#ifndef FAST
        if (_zone_active()) {
            struct add_list *expl = l->explanation;
            _zone_print_exp("Right term explanation", l);
            _zone_print1("expl %x", expl);
            _tree_indent();
            while (expl) {
                //_zone_print_exp("expl", expl->e);
                _zone_print1("expl %x", expl);
                _zone_print1("expl->e %x", expl->e);
                expl = expl->next;
            }
            _tree_undent();
        }
#endif
        if (l->explanation==NULL) {
            expl = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            expl->next = explanation;
            if (l->merge==_ex_true) {
                expl->e = l;
            } else if (l->merge==_ex_false) {
                expl->e = _ex_intern_appl1_env(env,INTERN_NOT,l);
            } else {
				if (is_bool(env,l) || is_bool(env,l->merge)) {
					expl->e = _ex_intern_equal(env,_ex_bool,l,l->merge);
				} else if (is_real(env,l) || is_real(env,l->merge)) {
					expl->e = _ex_intern_equal(env,_ex_real,l,l->merge);
				} else if (is_integer(env,l) || is_integer(env,l->merge)) {
					expl->e = _ex_intern_equal(env,_ex_int,l,l->merge);
				} else {
					fprintf(stderr, "Illegal merge equal 2 %s", _th_print_exp(l));
					fprintf(stderr, " and %s\n", _th_print_exp(l->merge));
				}
            }
            explanation = expl;
        } else {
            explanation = add_explanation_list(env, l->explanation, explanation);
            //if (explanation==NULL) {
            //    _tree_undent();
            //    return NULL;
            //}
        }
        l = l->merge;
    }

    _tree_undent();
    return explanation;
}

struct add_list *add_explanation_list(struct env *env, struct add_list *elist, struct add_list *tail)
{
    struct _ex_intern *left, *right;

    while (elist) {
#ifndef FAST
        if (elist->e->user2) check_term(elist->e);
#endif
        if (!elist->e->user2) {
            elist->e->user2 = trail;
            trail = elist->e;
            if (elist->e->type==EXP_APPL) {
                if (elist->e->u.appl.functor==INTERN_NOT) {
                    left = elist->e->u.appl.args[0];
                    right = _ex_false;
                } else if (elist->e->u.appl.functor==INTERN_EQUAL) {
                    left = elist->e->u.appl.args[0];
                    right = elist->e->u.appl.args[1];
                } else {
                    left = elist->e;
                    right = _ex_true;
                }
            } else {
                left = elist->e;
                right = _ex_true;
            }
            tail = merge_explanation(env,left,right,tail);
        }
        //if (tail==NULL) return NULL;
        elist = elist->next;
    }

    return tail;
}

struct add_list *_th_retrieve_explanation(struct env *env, struct _ex_intern *pred)
{
    struct _ex_intern *left, *right;
    struct add_list *ret;

    //_tree_print("Here xx");
    _zone_print_exp("Retrieving explanation for", pred);
    //_tree_print("Here yy");
    _tree_indent();

    trail = pred;
    trail->user2 = _ex_true;

    if (pred->type==EXP_APPL) {
        if (pred->u.appl.functor==INTERN_NOT) {
            left = pred->u.appl.args[0];
            right = _ex_false;
        } else if (pred->u.appl.functor==INTERN_EQUAL) {
            left = pred->u.appl.args[0];
            right = pred->u.appl.args[1];
        } else {
            left = pred;
            right = _ex_true;
        }
    } else {
        left = pred;
        right = _ex_true;
    }

    _tree_undent();
    //printf("Entering merge_explanation with %s\n", _th_print_exp(left));
    //printf("    and %s\n", _th_print_exp(right));
    //fflush(stdout);
    ret = merge_explanation(env, left, right, NULL);

    while (trail != _ex_true) {
        left = trail->user2;
        trail->user2 = NULL;
        trail = left;
    }

    return ret;
}

static int add_context_rules(struct env *env, struct context_data *data)
{
	int i;

	_zone_print0("Adding context rules");
	_tree_indent();

	_th_derive_push(env);

	if (data==NULL) {
		_tree_undent();
		return 0;
	}

	//while (data) {
		for (i = 0; i < data->count; ++i) {
			_zone_print_exp("Adding", data->rules[i]);
			if (data->rules[i]) {
				if (add_context_rule(env,data->rules[i])) {
					_tree_undent();
					_th_derive_pop(env);
					//_zone_print0("level a %d", _th_get_stack_level(env));
					//if (_th_get_stack_level(env)==0) exit(1);
					return 1;
				}
			}
		}
		//data = data->next;
	//}

	_tree_undent();

	return 0;
}

static int data_count(struct context_data *d)
{
	int c = 0;

	while (d) {
		c += d->count;
		d = d->next;
	}

	return c;
}

static void filter_data(struct context_data *old,
						struct context_data *n,
						int var_count,
						unsigned *vars)
{
	int pos;
	int i, j;

	pos = 0;

	while (old) {
		for (i = 0; i < old->count; ++i) {
			for (j = 0; j < var_count; ++j) {
				if (_th_is_free_in(old->rules[i],vars[j])) goto next;
			}
			n->rules[pos++] = old->rules[i];
next:;
		}
		old = old->next;
	}
}

int _th_rewriting_context = 0;

static int has_context_construct(struct env *env, struct _ex_intern *e)
{
	int i;

	switch (e->type) {
	    case EXP_APPL:
			switch (e->u.appl.functor) {
			    case INTERN_AND:
			    case INTERN_OR:
                case INTERN_ORIENTED_RULE:
                case INTERN_UNORIENTED_RULE:
                case INTERN_FORCE_ORIENTED:
                case INTERN_DOUBLE_ARROW:
                case INTERN_INFERENCE:
                case INTERN_MACRO_ARROW:
					return 1;
			    case INTERN_ITE:
					if (_th_is_constant(env,e->u.appl.args[1]) && _th_is_constant(env,e->u.appl.args[2])) {
						return has_context_construct(env,e->u.appl.args[0]);
					} else {
						return 1;
					}
                case INTERN_FILTER_SET:
                case INTERN_MAP_SET:
                    if (e->u.appl.count==2 && e->u.appl.args[0]->type==EXP_QUANT &&
                        e->u.appl.args[0]->u.quant.quant==INTERN_LAMBDA &&
                        e->u.appl.args[0]->u.quant.vars[0] &&
                        e->u.appl.args[0]->u.quant.var_count==1) {
						return 1;
					}
			    default:
			        for (i = 0; i < e->u.appl.count; ++i) {
						if (has_context_construct(env, e->u.appl.args[i])) return 1;
					}
					return 0;
			}
		case EXP_QUANT:
			if (e->u.quant.cond != _ex_true) return 1;
			return has_context_construct(env, e->u.quant.exp);
	    default:
			return 0;
	}
}

static struct _ex_intern *int_context_rewrite(struct env *env, struct _ex_intern *e, struct context_data *parent)
{
	struct context_data data, *d;
    struct _ex_intern **args;
	int i, change;
    struct _ex_intern *f, *g;
    //int push;

	data.next = parent;

	_zone_print_exp("Context rewrite", e);
	_tree_indent();

	switch (e->type) {
	    case EXP_APPL:
			switch (e->u.appl.functor) {
			    case INTERN_AND:
					data.count = e->u.appl.count-1;
					data.rules = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
					for (i = 0; i < e->u.appl.count; ++i) {
					    data.rules[i] = _th_derive_prepare(env,e->u.appl.args[i]);
					}
					args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
					//for (i = 0; i < e->u.appl.count; ++i) {
					//	f = data.rules[i];
					//	data.rules[i] = data.rules[data.count];
					//	args[i] = int_context_rewrite(env,e->u.appl.args[i],&data);
					//	data.rules[i] = f;
					//}
					change = 1;
					for (i = 0; i < e->u.appl.count; ++i) args[i] = e->u.appl.args[i];
					while (change) {
						change = 0;
     					for (i = 0; i < e->u.appl.count; ++i) {
	     					f = data.rules[i];
		    				data.rules[i] = data.rules[data.count];
							if (!_th_is_constant(env,args[i])) {
							    if (add_context_rules(env,&data)) {
				                	//_zone_print0("level b %d", _th_get_stack_level(env));
                 					//if (_th_get_stack_level(env)==0) exit(1);
								    _tree_undent();
								    return _ex_false;
								}
							    _th_add_transitive_derivatives(env,args[i]);
                                _th_clear_cache() ;
			    			    g = int_context_rewrite(env,args[i],&data);
							    if (g != args[i]) change = 1;
    							args[i] = g;
    				            //_zone_print0("level c %d", _th_get_stack_level(env));
                     		    //if (_th_get_stack_level(env)==0) exit(1);
		    					_th_derive_pop(env);
							}
				    		data.rules[i] = f;
						}
                    }
					++data.count;
					if (add_context_rules(env,&data)) {
						_tree_undent();
				        //_zone_print0("level d %d", _th_get_stack_level(env));
                 		//if (_th_get_stack_level(env)==0) exit(1);
						return _ex_false;
					} else {
						_th_derive_pop(env);
             		    //_zone_print0("level e %d", _th_get_stack_level(env));
                        //if (_th_get_stack_level(env)==0) exit(1);
					}
					f = _ex_intern_appl_env(env,INTERN_AND,e->u.appl.count,args);
					_tree_undent();
					_zone_print_exp("result", f);
             		//_zone_print0("level f %d", _th_get_stack_level(env));
                    //if (_th_get_stack_level(env)==0) exit(1);
					return f;
			    case INTERN_OR:
					data.count = e->u.appl.count-1;
					data.rules = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
					for (i = 0; i < e->u.appl.count; ++i) {
					    data.rules[i] = _th_derive_prepare(env,_ex_intern_appl1_env(env,INTERN_NOT,e->u.appl.args[i]));
					}
					args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
					//for (i = 0; i < e->u.appl.count; ++i) {
					//	f = data.rules[i];
					//	data.rules[i] = data.rules[data.count];
					//	args[i] = int_context_rewrite(env,e->u.appl.args[i],&data);
					//	data.rules[i] = f;
					//}
					for (i = 0; i < e->u.appl.count; ++i) args[i] = e->u.appl.args[i];
					change = 1;
					while (change) {
						change = 0;
     					for (i = 0; i < e->u.appl.count; ++i) {
	     					f = data.rules[i];
		    				data.rules[i] = data.rules[data.count];
							if (!_th_is_constant(env,args[i])) {
							    if (add_context_rules(env,&data)) {
								    _tree_undent();
             				        //_zone_print0("level g %d", _th_get_stack_level(env));
                            		//if (_th_get_stack_level(env)==0) exit(1);
								    return _ex_true;
								}
							    _th_add_transitive_derivatives(env,args[i]);
                                _th_clear_cache() ;
			    			    g = int_context_rewrite(env,args[i],&data);
							    if (g != args[i]) change = 1;
							    args[i] = g;
     							_th_derive_pop(env);
                 				//_zone_print0("level h %d", _th_get_stack_level(env));
                                //if (_th_get_stack_level(env)==0) exit(1);
							}
				    		data.rules[i] = f;
						}
                    }
					++data.count;
					if (add_context_rules(env,&data)) {
						_tree_undent();
             		    //_zone_print0("level i %d", _th_get_stack_level(env));
                        //if (_th_get_stack_level(env)==0) exit(1);
						return _ex_true;
					} else {
						_th_derive_pop(env);
             		    //_zone_print0("level j %d", _th_get_stack_level(env));
                        //if (_th_get_stack_level(env)==0) exit(1);
					}
					f = _ex_intern_appl_env(env,INTERN_OR,e->u.appl.count,args);
					_zone_print_exp("result", f);
					_tree_undent();
             		//_zone_print0("level k %d", _th_get_stack_level(env));
                    //if (_th_get_stack_level(env)==0) exit(1);
					return f;
			    case INTERN_ITE:
					data.count = 1;
					data.rules = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *));
					args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * 3);
					args[0] = int_context_rewrite(env,e->u.appl.args[0],parent);
					if (_th_is_constant(env,e->u.appl.args[1])) {
						args[1] = e->u.appl.args[1];
					} else {
    					data.rules[0] = _th_derive_prepare(env,e->u.appl.args[0]);
					    if (add_context_rules(env,&data)) {
						    _tree_undent();
						    return e->u.appl.args[2];
						}
					    _th_add_transitive_derivatives(env,e->u.appl.args[1]);
                        _th_clear_cache() ;
					    //args[1] = _th_int_rewrite(env,args[1],1);
					    args[1] = int_context_rewrite(env,e->u.appl.args[1],&data);
					    _th_derive_pop(env);
					}
					if (_th_is_constant(env,e->u.appl.args[2])) {
						args[2] = e->u.appl.args[2];
					} else {
					    data.rules[0] = _th_derive_prepare(env,_ex_intern_appl1_env(env,INTERN_NOT,e->u.appl.args[0]));
					    if (add_context_rules(env,&data)) {
						    _tree_undent();
						    return args[1];
						}
					    _th_add_transitive_derivatives(env,e->u.appl.args[2]);
                        _th_clear_cache() ;
					    //args[2] = _th_int_rewrite(env,args[2],1);
					    args[2] = int_context_rewrite(env,e->u.appl.args[2],&data);
					    _th_derive_pop(env);
					}
					f = _ex_intern_appl_env(env,INTERN_ITE,3,args);
					_zone_print_exp("result", f);
					_tree_undent();
					return f;
                case INTERN_ORIENTED_RULE:
                case INTERN_UNORIENTED_RULE:
                case INTERN_FORCE_ORIENTED:
                case INTERN_DOUBLE_ARROW:
                case INTERN_INFERENCE:
                case INTERN_MACRO_ARROW:
					data.count = 1;
					data.rules = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *));
					data.rules[0] = _th_derive_prepare(env,e->u.appl.args[2]);
					args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * 3);
					args[2] = int_context_rewrite(env,e->u.appl.args[2],parent);
					//args[0] = int_context_rewrite(env,e->u.appl.args[0],&data);
					//args[1] = int_context_rewrite(env,e->u.appl.args[1],&data);
					if (add_context_rules(env,&data)) {
						_tree_undent();
             			//if (push) _th_derive_pop(env);
						return _ex_true;
					}
					_th_add_transitive_derivatives(env,e->u.appl.args[0]);
					_th_add_transitive_derivatives(env,e->u.appl.args[1]);
                    _th_clear_cache() ;
					args[0] = int_context_rewrite(env,e->u.appl.args[0],&data);
					args[1] = int_context_rewrite(env,e->u.appl.args[1],&data);
					_th_derive_pop(env);
					f = _ex_intern_appl_env(env,e->u.appl.functor,3,args);
					_zone_print_exp("Result", f);
					_tree_undent();
           			//if (push) _th_derive_pop(env);
					return f;
                case INTERN_FILTER_SET:
                case INTERN_MAP_SET:
                    if (e->u.appl.count==2 && e->u.appl.args[0]->type==EXP_QUANT &&
                        e->u.appl.args[0]->u.quant.quant==INTERN_LAMBDA &&
                        e->u.appl.args[0]->u.quant.vars[0] &&
                        e->u.appl.args[0]->u.quant.var_count==1) {
						struct _ex_intern *g, *h ;
						if (_th_is_free_in(e->u.appl.args[1],e->u.appl.args[0]->u.quant.vars[0])) break ;
						g = e->u.appl.args[1];
						d = (struct context_data *)ALLOCA(sizeof(struct context_data));
						d->rules = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (data_count(&data)+1));
                        filter_data(&data, d, e->u.appl.args[0]->u.quant.var_count,e->u.appl.args[0]->u.quant.vars);
						d->rules[d->count++] = _th_derive_prepare(env,_th_mark_vars(env,_th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_MEMBER,_ex_intern_var(e->u.appl.args[0]->u.quant.vars[0]),g),1)));
						if (add_context_rules(env,d)) {
							_tree_undent();
                			//if (push) _th_derive_pop(env);
							return _ex_intern_appl_env(env,INTERN_SET,0,NULL);
						}
     					_th_add_transitive_derivatives(env,e->u.appl.args[0]->u.quant.exp);
						_th_clear_cache();
						h = _th_int_rewrite(env,e->u.appl.args[0]->u.quant.exp, 1) ;
						_th_derive_pop(env) ;
						e = _ex_intern_appl2_env(env,e->u.appl.functor,_ex_intern_quant(INTERN_LAMBDA,1,e->u.appl.args[0]->u.quant.vars,h,_ex_true),g) ;
					}
			    default:
					//push = has_context_construct(env,e);
					//if (push) {
					//	if (add_context_rules(env,&data)) {
					//		return _ex_false;
					//	}
					//}
					e = _th_int_rewrite(env,e,1);
					if (has_context_construct(env,e)) {
        			    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
			            for (i = 0; i < e->u.appl.count; ++i) {
			                args[i] = int_context_rewrite(env,e->u.appl.args[i],parent);
						}
     			        f = _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
					} else f = e;
					_zone_print_exp("Result", f);
					_tree_undent();
                	//if (push) _th_derive_pop(env);
					return f;
			}
		case EXP_QUANT:
			d = (struct context_data *)ALLOCA(sizeof(struct context_data));
			d->rules = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (data_count(&data)+1));
            filter_data(&data, d, e->u.appl.args[0]->u.quant.var_count,e->u.appl.args[0]->u.quant.vars);
			if (_th_is_constant(env,e->u.quant.exp)) {
				f = e->u.quant.exp;
			} else {
    			d->rules[d->count++] = _th_derive_prepare(env,_th_mark_vars(env,e->u.quant.cond));
				if (add_context_rules(env,d)) {
					_tree_undent();
                	//if (push) _th_derive_pop(env);
					switch (e->u.quant.quant) {
					    case INTERN_ALL:
							return _ex_true;
						case INTERN_SETQ:
							return _ex_intern_appl_env(env,INTERN_SET,0,NULL);
						default:
							fprintf(stderr, "Error: Ill formed quantifier %s\n", _th_print_exp(e));
							exit(1);
					}
				}
     			_th_add_transitive_derivatives(env,e->u.quant.exp);
                _th_clear_cache() ;
		    	f = _th_int_rewrite(env,e->u.quant.exp,1);
			    _th_derive_pop(env);
			    f = int_context_rewrite(env,f,d);
			    --d->count;
			}
	        g = int_context_rewrite(env,e->u.quant.cond,d);
			f = _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,e->u.quant.vars,f,g);
			_zone_print_exp("Result", f);
			_tree_undent();
           	//if (push) _th_derive_pop(env);
			return f;
	    default:
			_zone_print0("No context rewrite");
			_tree_undent();
           	//if (push) _th_derive_pop(env);
			return e;
	}
}

struct _ex_intern *_th_context_rewrite(struct env *env, struct _ex_intern *e)
{
	_th_rewriting_context = 1;
	return int_context_rewrite(env,e,NULL);
	_th_rewriting_context = 0;
}
