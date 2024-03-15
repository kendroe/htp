/*
 * unate.c
 *
 * Heuristic routines to identify unate case splits.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdio.h>
#include <stdlib.h>
#include "Globals.h"
#include "Intern.h"

struct term_lookup {
    struct term_lookup *next;
    int position;
    struct _ex_intern *term;
};

#define TERM_HASH 2047

struct term_info {
    int vector_length;
    unsigned *deny_makes_false;
    unsigned *deny_makes_true;
    unsigned *assert_makes_false;
    unsigned *assert_makes_true;
};

static struct _ex_intern *term_trail;

static int has_term(struct env *env, struct _ex_intern *e, struct _ex_intern *term)
{
    int i;
    
    if (e->user2) return 0;

    e->user2 = e;
    e->next_cache = term_trail;
    term_trail = e;

    if (e==term) return 1;
    
    switch (e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                if (has_term(env,e->u.appl.args[i],term)) return 1;
            }
            return 0;
            
        case EXP_QUANT:
            return has_term(env,e->u.quant.exp,term) ||
                   has_term(env,e->u.quant.cond,term);
            
        default:
            return 0;
    }
}

int _th_has_term(struct env *env, struct _ex_intern *e, struct _ex_intern *term)
{
    int i;
    
    if (e==term) return 1;
    
    term_trail = NULL;

    i = has_term(env,e,term);

    while (term_trail) {
        term_trail->user2 = NULL;
        term_trail = term_trail->next_cache;
    }

    return i;
}

int _th_another_cond_as_subterm(struct env *env, struct _ex_intern *e, struct term_list *list)
{
    if (e->type==EXP_APPL) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            if (_th_has_a_term(e->u.appl.args[i])) {
                return 1;
            }
        }
        return 0;
    } else {
        return 0;
    }
    //while (list != NULL) {
    //    if (e != list->e && _th_has_term(env,e,list->e)) return 1;
    //    list = list->next;
    //}
    //return 0;
}

struct term_list *_th_eliminate_composite_conds(struct env *env, struct term_list *list)
{
    struct term_list *nl, *l, *ll;

    nl = NULL;

    l = list;
    while (l != NULL) {
        if (!_th_another_cond_as_subterm(env,l->e,list)) {
            ll = (struct term_list *)_th_alloc(REWRITE_SPACE,sizeof(struct term_list));
            ll->next = nl;
            nl = ll;
            nl->e = l->e;
            nl->dependencies = nl->neg_dependencies = NULL;
            nl->count = l->count;
            nl->total_count = 0;
        }
        l = l->next;
    }

    return nl;
}

static int _my_contains_ite(struct _ex_intern *e)
{
    int i;

    if (e->user2) return 0;

    e->next_cache = term_trail;
    term_trail = e;
    e->user2 = _ex_true;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor==INTERN_ITE) return 1;
            for (i = 0; i < e->u.appl.count; ++i) {
                if (_my_contains_ite(e->u.appl.args[i])) return 1;
            }
            return 0;
        case EXP_QUANT:
            return _my_contains_ite(e->u.quant.cond) || _my_contains_ite(e->u.quant.exp);
        default:
            return 0;
    }
}

int _th_my_contains_ite(struct _ex_intern *e)
{
    int res;

    _th_clear_cache();

    term_trail = NULL;

    res = _my_contains_ite(e);

    while (term_trail) {
        term_trail->user2 = NULL;
        term_trail = term_trail->next_cache;
    }

    return res;
}

int _th_is_boolean_term(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *t;

	switch (e->type) {
	    case EXP_APPL:
			switch (e->u.appl.functor) {
			    case INTERN_AND:
				case INTERN_OR:
				case INTERN_NOT:
				case INTERN_NC_AND:
				case INTERN_NC_OR:
                case INTERN_BICONDITIONAL:
				case INTERN_XOR:
				case INTERN_EQUAL:
				case INTERN_NAT_LESS:
				case INTERN_RAT_LESS:
				case INTERN_ORIENTED_RULE:
				case INTERN_UNORIENTED_RULE:
					return 1;
				case INTERN_ITE:
					if (_th_is_boolean_term(env,e->u.appl.args[1]) ||
						_th_is_boolean_term(env,e->u.appl.args[2])) return 1;
					return 0;
				default:
					t = _th_get_type(env,e->u.appl.functor);
					return t != NULL && t->u.appl.args[1]==_ex_bool;
			}
		case EXP_QUANT:
			switch (e->u.quant.quant) {
			    case INTERN_EXISTS:
				case INTERN_ALL:
					return 1;
				case INTERN_SETQ:
					return 0;
				case INTERN_LAMBDA:
					return _th_is_boolean_term(env,e->u.quant.exp);
				default:
					return 0;
			}
		case EXP_VAR:
			return _th_get_var_type(env,e->u.var)==_ex_bool;
		default:
			return 0;
	}
}

static int member(struct _ex_intern *e, struct term_list *l)
{
    while (l != NULL) {
		if (l->e==e) {
			return 1;
		}
		l = l->next;
	}

	return 0;
}

static struct term_list *get_terms(struct env *env, struct _ex_intern *e, struct term_list *rest);

static struct term_list *extract_terms(struct env *env, struct _ex_intern *e, struct term_list *rest)
{
    int i;

    //printf("e->user2 = %s\n", _th_print_exp(e->user2));
    //printf("e->user1 = %d %s\n", e->user1, _th_print_exp(e->user1));
    if (e->user2) return rest;

    e->user2 = e;
    e->next_cache = term_trail;
    term_trail = e;

    switch(e->type) {
        case EXP_APPL:
            switch (e->u.appl.functor) {
                case INTERN_ITE:
                    term_trail = term_trail->next_cache;
                    e->user2 = NULL;
                    rest = get_terms(env,e,rest);
                default:
                    for (i = 0; i < e->u.appl.count; ++i) {
                        rest = extract_terms(env,e->u.appl.args[i],rest);
                    }
                    return rest;
            }
        case EXP_QUANT:
            rest = get_terms(env,e->u.quant.exp,rest);
            rest = get_terms(env,e->u.quant.cond,rest);
            return rest;
        default:
            return rest;
    }
}

static struct term_list *get_terms(struct env *env, struct _ex_intern *e, struct term_list *rest)
{
    int i;
    struct term_list *a;
    
    //printf("e->user2 2 = %s\n", _th_print_exp(e->user2));
    //printf("e->user1 = %d %s\n", e->user1, _th_print_exp(e->user1));
    if (e->user2) return rest;

    e->user2 = e;
    e->next_cache = term_trail;
    term_trail = e;

    switch(e->type) {
        case EXP_APPL:
            switch (e->u.appl.functor) {
                case INTERN_AND:
                case INTERN_OR:
                case INTERN_NOT:
                case INTERN_NC_AND:
                case INTERN_NC_OR:
                case INTERN_BICONDITIONAL:
                case INTERN_XOR:
                    for (i = 0; i < e->u.appl.count; ++i) {
                        rest = get_terms(env,e->u.appl.args[i],rest);
                    }
                    return rest;
                case INTERN_ORIENTED_RULE:
                case INTERN_UNORIENTED_RULE:
                    rest = get_terms(env,e->u.appl.args[2],rest);
                case INTERN_EQUAL:
                    //_tree_print_exp("e", e);
                    //_tree_print_exp("e", e->type_inst);
                    if (e->type_inst==_ex_bool ||
                        _th_is_boolean_term(env,e->u.appl.args[0]) ||
                        _th_is_boolean_term(env,e->u.appl.args[1])) {
                        rest = get_terms(env,e->u.appl.args[0],rest);
                        rest = get_terms(env,e->u.appl.args[1],rest);
                        return rest;
                    } else {
                        goto def;
                    }
                case INTERN_TRUE:
                case INTERN_FALSE:
                    return rest;
                case INTERN_ITE:
                    rest = get_terms(env,e->u.appl.args[0],rest);
                    if (_th_is_boolean_term(env,e->u.appl.args[1]) ||
                        _th_is_boolean_term(env,e->u.appl.args[2])) {
                        rest = get_terms(env,e->u.appl.args[2],rest);
                        rest = get_terms(env,e->u.appl.args[1],rest);
                        return rest;
                    } else {
                        if (!member(e,rest)) {
                            rest = extract_terms(env,e->u.appl.args[1],rest);
                            rest = extract_terms(env,e->u.appl.args[2],rest);
                            //printf("Adding term %s\n", _th_print_exp(e));
                            a = (struct term_list *)_th_alloc(REWRITE_SPACE,sizeof(struct term_list));
                            a->next = rest;
                            a->e = e;
                            rest = a;
                        }
                        return get_terms(env,e->u.appl.args[0],rest);
                    }
                default:
                    goto def;
            }
            case EXP_QUANT:
                rest = get_terms(env,e->u.quant.cond,rest);
                rest = get_terms(env,e->u.quant.exp,rest);
                return rest;
            default:
def:
                if (member(e,rest)) {
                    return  rest;
                } else {
                    term_trail = term_trail->next_cache;
                    e->user2 = NULL;
                    rest = extract_terms(env,e,rest);
                    a = (struct term_list *)_th_alloc(HEURISTIC_SPACE,sizeof(struct term_list));
                    a->next = rest;
                    a->e = e;
                    //printf("Adding term 2 %s\n", _th_print_exp(e));
                    return a;
                }
    }
}

static int my_term_count(struct env *env, struct _ex_intern *e, struct _ex_intern *term)
{
    int i, count;
    struct term_data *data = _th_get_term_data_holder(e, term);

    //if (data->term_count >= 0) {
    //    return data->term_count;
    //}

    if (e==term) {
        //data->term_count = 1;
        return 1;
    }
    
    switch (e->type) {
        case EXP_APPL:
            count = 0;
            for (i = 0; i < e->u.appl.count; ++i) {
                count += my_term_count(env,e->u.appl.args[i],term);
            }
            //data->term_count = count;
            return count;
        
        case EXP_QUANT:
            count = my_term_count(env,e->u.quant.exp,term)+
                    my_term_count(env,e->u.quant.cond,term);
            //data->term_count = count+1;
            return count;
        
        default:
            //data->term_count = 0;
            return 0;
    }
}

int _th_term_count(struct env *env, struct _ex_intern *e, struct _ex_intern *term)
{
    int count;
    
    count = my_term_count(env,e,term);

    return count;
}

static int elimination_score(struct term_list *all, struct _ex_intern *e)
{
    struct term_list *tl;
    int i, c;

    i = _th_get_elimination_score(e);
    if (i>=0) return i;

    tl = all;

    while (tl != NULL) {
        if (e==tl->e) {
            _th_set_elimination_score(e,2);
            return 2;
        }
        tl = tl->next;
    }

    switch (e->type) {
        case EXP_APPL:
            c = 0;
            for (i = 0; i < e->u.appl.count; ++i) {
                c += elimination_score(all,e->u.appl.args[i]);
                if (c < 0) c = 0x7fffffff;
            }
            _th_set_elimination_score(e,c);
            return c;
        case EXP_QUANT:
            c = elimination_score(all,e->u.quant.exp);
            c += elimination_score(all,e->u.quant.cond);
            if (c < 0) c = 0x7fffffff;
            _th_set_elimination_score(e,c);
            return c;
        default:
            _th_set_elimination_score(e,0);
            return 0;
    }
}

static int is_const(struct _ex_intern *e)
{
    if (e->type==EXP_INTEGER) return 1;
    if (e==_ex_true || e==_ex_false) return 1;
    return 0;
}

static struct _ex_intern *pos_exp, *neg_exp;
static int pos_score, neg_score;
static void reduction_score(struct env *env, struct term_list *all, struct term_list *tl, int pos, struct _ex_intern *e)
{
    int s, i, j, k, l;
    struct dependencies *d;
    struct _ex_intern *exp, *cond, *nexp, *ncond;
    struct _ex_intern **p_args, **n_args;
    int p_change, n_change;
    struct term_data *td;
    int p_skip, n_skip, p_score, n_score;

    _zone_print_exp("reduction_score", e);
    _tree_indent();

    //fprintf(stderr, "reduction score with %s\n", _th_print_exp(tl->e));
    //fprintf(stderr, "pos = %d\n", pos);

    if (!_th_check_term(e,pos)) {
        pos_exp = neg_exp = e;
        pos_score = neg_score = 0;
        _zone_print0("term not present");
        _tree_undent();
        return;
    }

    td = _th_get_term_data_holder(e,tl->e);

    if (td->pos_term) {
        pos_score = td->pos_score;
        neg_score = td->neg_score;
        pos_exp = td->pos_term;
        neg_exp = td->neg_term;
        _zone_print2("cache %d %d", td->pos_score, td->neg_score);
        //fprintf(stderr, "Cache %s\n", _th_print_exp(e));
        //fprintf(stderr, "terms %d %d\n", td->pos_term, td->pos_score);
        _tree_undent();
        return;
    }

    if (e==tl->e) {
        pos_score = td->pos_score = 2;
        neg_score = td->neg_score = 2;
        pos_exp = td->pos_term = _ex_true;
        neg_exp = td->neg_term = _ex_false;
        _zone_print_exp("true_reduction", _ex_true);
        _tree_undent();
        return;
    }


    pos_score = 0;
    d = tl->dependencies;
    while (d) {
        if (e==d->term->e) {
            if (d->reduction==_ex_true || d->reduction==_ex_false) {
                pos_score = td->pos_score = 2;
            } else {
                pos_score = td->pos_score = 1;
            }
            pos_exp = td->pos_term = d->reduction;
            _zone_print_exp("p reduction", d->reduction);
            goto cont_a;
        }
        d = d->next;
    }
cont_a:
    d = tl->neg_dependencies;
    while (d) {
        if (e==d->term->e) {
            if (d->reduction==_ex_true || d->reduction==_ex_false) {
                neg_score = td->neg_score = 2;
            } else {
                neg_score = td->neg_score = 1;
            }
            neg_exp = td->neg_term = d->reduction;
            _zone_print_exp("n reduction", d->reduction);
            if (pos_score==0) {
                td->pos_score = 0;
                pos_exp = td->pos_term = e;
            }
            _tree_undent();
            return;
        }
        d = d->next;
    }
    if (pos_score) {
        neg_score = td->neg_score = 0;
        neg_exp = td->neg_term = e;
        _tree_undent();
        return;
    }

    switch (e->type) {
        case EXP_APPL:
            switch (e->u.appl.functor) {
                case INTERN_AND:
                    n_skip = p_skip = p_score = n_score = 0;
                    for (i = 0, j = 0, k = 0; i < e->u.appl.count; ++i) {
                        reduction_score(env,all,tl,pos,e->u.appl.args[i]);
                        //fprintf(stderr, "orig = %s\n", _th_print_exp(e->u.appl.args[i]));
                        //fprintf(stderr, "args[%d] = %x\n", j, args[j]);
                        //fflush(stderr);
                        if (neg_exp==_ex_false) {
                            td->neg_term = _ex_false;
                            if (p_skip) {
                                td->neg_score = s;
                                pos_exp = neg_exp = _ex_false;
                                neg_score = pos_score = s;
                                _zone_print_exp("and false (both)", _ex_false);
                                _tree_undent();
                                return;
                            } else {
                                n_skip = 1;
                                s  = neg_score;
                                for (l = 0; l < e->u.appl.count; ++l) {
                                    if (i != l) {
                                        s += elimination_score(all,e->u.appl.args[l]);
                                        if (s < 0) s = 0x7fffffff;
                                    }
                                }
                                _zone_print_exp("and false (neg)", _ex_false);
                                //_tree_undent();
                                td->neg_score = s;
                            }
                        }
                        if (pos_exp==_ex_false) {
                            td->pos_term = _ex_false;
                            if (n_skip) {
                                td->pos_score = s;
                                pos_exp = neg_exp = _ex_false;
                                neg_score = pos_score = s;
                                _zone_print_exp("and false (both)", _ex_false);
                                _tree_undent();
                                return;
                            } else {
                                p_skip = 1;
                                s  = pos_score;
                                for (l = 0; l < e->u.appl.count; ++l) {
                                    if (i != l) {
                                        s += elimination_score(all,e->u.appl.args[l]);
                                        if (s < 0) s = 0x7fffffff;
                                    }
                                }
                                _zone_print_exp("and false (pos)", _ex_false);
                                //_tree_undent();
                                td->pos_score = s;
                            }
                        }

                        p_score += pos_score;
                        n_score += neg_score;
                        if (p_score < 0) p_score = 0x7fffffff;
                        if (n_score < 0) p_score = 0x7fffffff;

                        if (pos_exp != _ex_true) {
                            ++j;
                            exp = pos_exp;
                        }

                        if (neg_exp != _ex_true) {
                            ++k;
                            nexp = neg_exp;
                        }
                    }
                    if (p_skip) {
                        td->pos_score = s;
                        pos_exp = td->pos_term = _ex_false;
                    } else {
                        td->pos_score = p_score;
                        if (j==0) {
                            pos_exp = td->pos_term = _ex_true;
                        } else if (j==1) {
                            pos_exp = td->pos_term = exp;
                        } else {
                            pos_exp = td->pos_term = e;
                        }
                    }
                    if (n_skip) {
                        td->neg_score = s;
                        neg_exp = td->neg_term = _ex_false;
                    } else {
                        td->neg_score = n_score;
                        if (k==0) {
                            neg_exp = td->neg_term = _ex_true;
                        } else if (k==1) {
                            neg_exp = td->neg_term = nexp;
                        } else {
                            neg_exp = td->neg_term = e;
                        }
                    }
                    neg_score = td->neg_score;
                    pos_score = td->pos_score;
                    _zone_print_exp("and reduction", td->pos_term);
                    _zone_print2("scores %d %d", pos_score, neg_score);
                    _tree_undent();
                    return;
                case INTERN_OR:
                    n_skip = p_skip = p_score = n_score = 0;
                    for (i = 0, j = 0, k = 0; i < e->u.appl.count; ++i) {
                        reduction_score(env,all,tl,pos,e->u.appl.args[i]);
                        //fprintf(stderr, "orig = %s\n", _th_print_exp(e->u.appl.args[i]));
                        //fprintf(stderr, "args[%d] = %x\n", j, args[j]);
                        //fflush(stderr);
                        if (neg_exp==_ex_true) {
                            td->neg_term = _ex_true;
                            if (p_skip) {
                                td->neg_score = s;
                                pos_exp = neg_exp = _ex_true;
                                neg_score = pos_score = s;
                                _zone_print_exp("or true (both)", _ex_true);
                                _tree_undent();
                                return;
                            } else {
                                n_skip = 1;
                                s  = neg_score;
                                for (l = 0; l < e->u.appl.count; ++l) {
                                    if (i != l) {
                                        s += elimination_score(all,e->u.appl.args[l]);
                                        if (s < 0) s = 0x7fffffff;
                                    }
                                }
                                _zone_print_exp("or true (neg)", _ex_true);
                                //_tree_undent();
                                td->neg_score = s;
                            }
                        }
                        if (pos_exp==_ex_true) {
                            td->pos_term = _ex_true;
                            if (n_skip) {
                                td->pos_score = s;
                                pos_exp = neg_exp = _ex_true;
                                neg_score = pos_score = s;
                                _zone_print_exp("or true (both)", _ex_true);
                                _tree_undent();
                                return;
                            } else {
                                p_skip = 1;
                                s  = pos_score;
                                for (l = 0; l < e->u.appl.count; ++l) {
                                    if (i != l) {
                                        s += elimination_score(all,e->u.appl.args[l]);
                                        if (s < 0) s = 0x7fffffff;
                                    }
                                }
                                _zone_print_exp("or true (pos)", _ex_true);
                                //_tree_undent();
                                td->pos_score = s;
                            }
                        }

                        p_score += pos_score;
                        n_score += neg_score;
                        if (p_score < 0) p_score = 0x7fffffff;
                        if (n_score < 0) p_score = 0x7fffffff;

                        if (pos_exp != _ex_false) {
                            ++j;
                            exp = pos_exp;
                        }

                        if (neg_exp != _ex_false) {
                            ++k;
                            nexp = neg_exp;
                        }
                    }
                    if (p_skip) {
                        td->pos_score = s;
                        pos_exp = td->pos_term = _ex_true;
                    } else {
                        td->pos_score = p_score;
                        if (j==0) {
                            pos_exp = td->pos_term = _ex_false;
                        } else if (j==1) {
                            pos_exp = td->pos_term = exp;
                        } else {
                            pos_exp = td->pos_term = e;
                        }
                    }
                    if (n_skip) {
                        td->neg_score = s;
                        neg_exp = td->neg_term = _ex_true;
                    } else {
                        td->neg_score = n_score;
                        if (k==0) {
                            neg_exp = td->neg_term = _ex_false;
                        } else if (k==1) {
                            neg_exp = td->neg_term = nexp;
                        } else {
                            neg_exp = td->neg_term = e;
                        }
                    }
                    neg_score = td->neg_score;
                    pos_score = td->pos_score;
                    _zone_print_exp("or reduction", td->pos_term);
                    _zone_print2("scores %d %d", pos_score, neg_score);
                    _tree_undent();
                    return;
                case INTERN_ITE:
                    reduction_score(env,all,tl,pos,e->u.appl.args[0]);
                    cond = pos_exp;
                    ncond = neg_exp;
                    p_score = pos_score;
                    n_score = neg_score;
                    if (cond==_ex_true) {
                        reduction_score(env,all,tl,pos,e->u.appl.args[1]);
                        td->pos_term = pos_exp;
                        i = elimination_score(all,e->u.appl.args[2]);
                        p_score += pos_score;
                        if (p_score < 0) p_score = 0x7fffffff;
                        p_score += i;
                        if (p_score < 0) p_score = 0x7fffffff;
                        td->pos_score = p_score;
                        if (ncond==_ex_true) {
                            neg_score += n_score;
                            if (neg_score < 0) neg_score = 0x7fffffff;
                            neg_score += i;
                            if (neg_score < 0) neg_score = 0x7fffffff;
                            td->neg_score = neg_score;
                            pos_score = p_score;
                            td->pos_term = pos_exp;
                            td->neg_term = neg_exp;
                            _zone_print0("ite pos true neg true");
                            _tree_undent();
                            return;
                        } else if (ncond==_ex_false) {
                            n_score += elimination_score(all,e->u.appl.args[1]);
                            if (n_score < 0) n_score = 0x7fffffff;
                            reduction_score(env,all,tl,pos,e->u.appl.args[2]);
                            n_score += neg_score;
                            if (n_score < 0) n_score = 0x7fffffff;
                            td->neg_score = n_score;
                            td->neg_term = neg_exp;
                            neg_score = n_score;
                            pos_score = p_score;
                            pos_exp = td->pos_term;
                            _zone_print0("ite pos true neg false");
                            _tree_undent();
                            return;
                        } else {
                            n_score += neg_score;
                            if (n_score < 0) n_score = 0x7fffffff;
                            reduction_score(env,all,tl,pos,e->u.appl.args[2]);
                            n_score += neg_score;
                            if (n_score < 0) n_score = 0x7fffffff;
                            td->neg_score = n_score;
                            neg_exp = td->neg_term = e;
                            neg_score = n_score;
                            pos_score = p_score;
                            pos_exp = td->pos_term;
                            _zone_print0("ite pos true neg other");
                            _tree_undent();
                            return;
                        }
                    } else if (cond==_ex_false) {
                        reduction_score(env,all,tl,pos,e->u.appl.args[2]);
                        td->pos_term = pos_exp;
                        i = elimination_score(all,e->u.appl.args[1]);
                        p_score += pos_score;
                        if (p_score < 0) p_score = 0x7fffffff;
                        p_score += i;
                        if (p_score < 0) p_score = 0x7fffffff;
                        td->pos_score = p_score;
                        if (ncond==_ex_false) {
                            neg_score += n_score;
                            if (neg_score < 0) neg_score = 0x7fffffff;
                            neg_score += i;
                            if (neg_score < 0) neg_score = 0x7fffffff;
                            td->neg_score = neg_score;
                            pos_score = p_score;
                            td->neg_term = neg_exp;
                            _zone_print0("ite pos false neg false");
                            _tree_undent();
                            return;
                        } else if (ncond==_ex_true) {
                            n_score += elimination_score(all,e->u.appl.args[2]);
                            if (n_score < 0) n_score = 0x7fffffff;
                            reduction_score(env,all,tl,pos,e->u.appl.args[1]);
                            n_score += neg_score;
                            if (n_score < 0) n_score = 0x7fffffff;
                            td->neg_score = n_score;
                            td->neg_term = neg_exp;
                            neg_score = n_score;
                            pos_score = p_score;
                            pos_exp = td->pos_term;
                            _zone_print0("ite pos false neg true");
                            _tree_undent();
                            return;
                        } else {
                            n_score += neg_score;
                            if (n_score < 0) n_score = 0x7fffffff;
                            reduction_score(env,all,tl,pos,e->u.appl.args[1]);
                            n_score += neg_score;
                            if (n_score < 0) n_score = 0x7fffffff;
                            td->neg_score = n_score;
                            neg_exp = td->neg_term = e;
                            neg_score = n_score;
                            pos_score = p_score;
                            pos_exp = td->pos_term;
                            _zone_print0("ite pos false neg other");
                            _tree_undent();
                            return;
                        }
                    } else {
                        reduction_score(env,all,tl,pos,e->u.appl.args[1]);
                        nexp = neg_exp;
                        p_score += pos_score;
                        if (p_score < 0) p_score = 0x7fffffff;
                        s = neg_score;
                        reduction_score(env,all,tl,pos,e->u.appl.args[2]);
                        p_score += pos_score;
                        if (p_score < 0) p_score = 0x7fffffff;
                        pos_score = td->pos_score = p_score;
                        pos_exp = td->pos_term = e;
                        if (ncond==_ex_true) {
                            n_score += s;
                            if (n_score < 0) n_score = 0x7fffffff;
                            n_score += elimination_score(all,e->u.appl.args[2]);
                            if (n_score < 0) n_score = 0x7fffffff;
                            neg_exp = td->neg_term = nexp;
                            neg_score = n_score;
                            _zone_print0("ite pos other neg other");
                            _tree_undent();
                            return;
                        } else if (ncond==_ex_false) {
                            n_score += elimination_score(all,e->u.appl.args[1]);
                            if (n_score < 0) n_score = 0x7fffffff;
                            neg_score += n_score;
                            if (neg_score < 0) neg_score = 0x7fffffff;
                            td->neg_term = neg_exp;
                            _zone_print0("ite pos other neg other");
                            _tree_undent();
                            return;
                        } else {
                            neg_score += s;
                            if (neg_score < 0) neg_score = 0x7fffffff;
                            neg_score += n_score;
                            if (neg_score < 0) neg_score = 0x7fffffff;
                            neg_exp = td->neg_term = e;
                            _zone_print0("ite pos other neg other");
                            _tree_undent();
                            return;
                        }
                    }
                default:
                    p_args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
                    n_args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
                    p_score = n_score = 0;
                    p_change = n_change = 0;
                    for (i = 0; i < e->u.appl.count; ++i) {
                        reduction_score(env,all,tl,pos,e->u.appl.args[i]);
                        p_args[i] = pos_exp;
                        n_args[i] = neg_exp;
                        if (p_args[i] != e->u.appl.args[i]) p_change = 1;
                        if (n_args[i] != e->u.appl.args[i]) n_change = 1;
                        p_score += pos_score;
                        if (p_score < 0) p_score = 0x7fffffff;
                        n_score += neg_score;
                        if (n_score < 0) n_score = 0x7fffffff;
                    }
                    exp = _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,p_args);
                    nexp = _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,n_args);
                    if (p_change) {
                        cond = exp;
                        switch (exp->u.appl.functor) {
                            case INTERN_NOT:
                                if (exp->u.appl.args[0]==_ex_true) {
                                    exp = _ex_false;
                                } else if (exp->u.appl.args[0]==_ex_false) {
                                    exp = _ex_true;
                                }
                                break;
                            case INTERN_EQUAL:
                                if (exp->u.appl.args[0]==exp->u.appl.args[1]) {
                                    exp = _ex_true;
                                } else if (is_const(exp->u.appl.args[0]) &&
                                           is_const(exp->u.appl.args[1]) &&
                                           exp->u.appl.args[0] != exp->u.appl.args[1]) {
                                    exp = _ex_false;
                                }
                                break;
                        }
                        if (exp==NULL) exp = cond;
                        if (exp != cond) ++p_score;
                        if (exp==_ex_true || exp==_ex_false) ++p_score;
                        if (p_score < 0) p_score = 0x7fffffff;
                    }
                    if (n_change) {
                        cond = nexp;
                        switch (nexp->u.appl.functor) {
                            case INTERN_NOT:
                                if (nexp->u.appl.args[0]==_ex_true) {
                                    nexp = _ex_false;
                                } else if (nexp->u.appl.args[0]==_ex_false) {
                                    nexp = _ex_true;
                                }
                                break;
                            case INTERN_EQUAL:
                                if (nexp->u.appl.args[0]==nexp->u.appl.args[1]) {
                                    nexp = _ex_true;
                                } else if (is_const(nexp->u.appl.args[0]) &&
                                           is_const(nexp->u.appl.args[1]) &&
                                           nexp->u.appl.args[0] != nexp->u.appl.args[1]) {
                                    nexp = _ex_false;
                                }
                                break;
                        }
                        if (nexp==NULL) nexp = cond;
                        if (nexp != cond) ++n_score;
                        if (nexp==_ex_true || nexp==_ex_false) ++n_score;
                        if (n_score < 0) n_score = 0x7fffffff;
                    }
                    pos_exp = td->pos_term = exp;
                    neg_exp = td->neg_term = nexp;
                    pos_score = td->pos_score = p_score;
                    neg_score = td->neg_score = n_score;
                    _zone_print_exp("appl pos", exp);
                    _zone_print_exp("appl neg", nexp);
                    _zone_print2("scores %d %d", pos_score, neg_score);
                    _tree_undent();
                    return;
            }
        case EXP_QUANT:
            reduction_score(env,all,tl,pos,e->u.quant.exp);
            p_score = pos_score;
            n_score = neg_score;
            exp = pos_exp;
            nexp = neg_exp;
            reduction_score(env,all,tl,pos,e->u.quant.cond);
            p_score += pos_score;
            n_score += neg_score;
            cond = pos_exp;
            ncond = neg_exp;
            if (p_score < 0) p_score = 0x7fffffff;
            if (n_score < 0) n_score = 0x7fffffff;
            td->pos_score = p_score;
            td->neg_score = n_score;
            td->pos_term = _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,e->u.quant.vars,exp,cond);
            td->neg_term = _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,e->u.quant.vars,nexp,ncond);
            _zone_print_exp("quant", td->pos_term);
            _zone_print_exp("quant", td->neg_term);
            _tree_undent();
            return;
        default:
            pos_score = neg_score = td->pos_score = td->neg_score = 0;
            td->pos_term = td->neg_term = pos_exp = neg_exp = e;
            _zone_print_exp("default", e);
            _tree_undent();
            return;
    }
}

struct _ex_intern *_th_reduction_score(struct env *env, struct term_list *all, struct term_list *tl, struct _ex_intern *e)
{
    int s;

    //fprintf(stderr, "_th_reduction score %s\n", _th_print_exp(e));
    //fprintf(stderr, "    term %s\n", _th_print_exp(tl->e));

    _zone_print_exp("Score for", tl->e);
    _tree_indent();

    reduction_score(env,all,tl,_th_get_term_position(tl->e),e);
    s = pos_score + neg_score;
    if (s < 0) s = 0x7fffffff;

    _zone_print_exp("true", pos_exp);
    _zone_print_exp("false", neg_exp);

    if (pos_exp==_ex_true || neg_exp==_ex_true ||
        pos_exp==_ex_false || neg_exp==_ex_false) {
        _tree_undent();
        return _ex_intern_appl3_env(env,INTERN_T,_ex_intern_small_integer(-1),pos_exp,neg_exp);
    }

    _tree_undent();
    return _ex_intern_appl3_env(env,INTERN_T,_ex_intern_small_integer(s),pos_exp,neg_exp);
}

static struct term_list *_get_terms(struct env *env, struct _ex_intern *e, struct term_list *list)
{
    struct term_list *ret; 

    _th_clear_cache();

    term_trail = 0;

    ret = get_terms(env,e,list);

    while (term_trail != NULL) {
        term_trail->user2 = NULL;
        term_trail = term_trail->next_cache;
    }

    return ret;
}

static void _fill_term_list(struct env *env, struct _ex_intern *e, struct term_list *r)
{
    //_tree_print0("Adding terms");
    //_tree_indent();
    while (r) {
        if (_th_get_term_position(r->e) < 0) {
            //_tree_print_exp("t", r->e);
            _th_new_term(r->e);
        }
        r->count = 1;
        //_th_term_count(env,e,r->e);
        r = r->next;
    }
    //_tree_undent();
    _th_update_dependency_table(env,1);
}

struct term_list *filter_composites(struct term_list *ret)
{
    while (ret && _th_my_contains_ite(ret->e)) {
        ret = ret->next;
    }
    if (ret) {
        ret->next = filter_composites(ret->next);
    }
    return ret;
}

struct term_list *_th_get_terms(struct env *env, struct _ex_intern *e,struct term_list *list)
{
    struct term_list *ret; 

    ret = _get_terms(env,e,list);
    if (!_th_use_composite_conds) ret = filter_composites(ret);

    _fill_term_list(env,e,ret);

    return ret;
}

#ifdef XX
static int get_term_position(struct term_lookup **table, struct _ex_intern *e)
{
    int hash = (((int)e)/4)%TERM_HASH;
    struct term_lookup *t = table[hash];
    //_tree_print2("hash = %d, table = %x", hash, table);

    while (t) {
        //_tree_print2("cycle %s %d\n", _th_print_exp(t->term), t->position);
        if (t->term==e) {
            //_tree_print1("Found position %d", t->position);
            return t->position;
        }
        t = t->next;
    }

    return -1;
}

static struct _ex_intern *lookup_term(struct term_lookup **table, int index)
{
    int i;

    //_tree_print1("Looking up %d\n", index);
    for (i = 0; i < TERM_HASH; ++i) {
        struct term_lookup *t = table[i];
        while (t != NULL) {
            //_tree_print2("Testing %d %s", t->position, _th_print_exp(t->term));
            if (t->position==index) return t->term;
            t = t->next;
        }
    }
    return NULL;
}

static int table_size;
#endif

#ifdef XX
static struct term_lookup **get_leaf_terms(struct env *env, struct _ex_intern *e)
{
    struct term_list *terms = _get_terms(env,e,NULL), *tl;
    struct term_lookup **table = (struct term_lookup **)_th_alloc(REWRITE_SPACE,sizeof(struct term_lookup *) * TERM_HASH);
    int i, hash;
    struct term_lookup *t;

    _zone_print0("Obtaining leaf terms");
    _tree_indent();

    for (i = 0; i < TERM_HASH; ++i) {
        table[i] = NULL;
    }

    tl = terms;
    i = 0;

    while (tl != NULL) {
        //printf("Testing %s\n", _th_print_exp(tl->e));
        if (!_th_my_contains_ite(tl->e)) {
            //printf("    Adding\n");
        //if (!_th_another_cond_as_subterm(env,tl->e,terms)) {
            hash = (((int)tl->e)/4)%TERM_HASH;
            t = (struct term_lookup *)_th_alloc(REWRITE_SPACE,sizeof(struct term_lookup));
            t->next = table[hash];
            table[hash] = t;
            t->position = i;
            t->term = tl->e;
            _zone_print2("%d => %s", i, _th_print_exp(tl->e));
            //_tree_print3("Adding leaf %d: %s (%d)\n", i, _th_print_exp(tl->e), hash);
            ++i;
        }
        tl = tl->next;
    }

    table_size = (i+31)/32;
    //_tree_print1("Total leaf terms %d", i);

    _tree_undent();
    return table;
}
#endif

static int is_dependent(struct term_list *parent, struct term_list *child)
{
    struct dependencies *d = parent->dependencies;

    while (d) {
        if (d->term==child) return 1;
        d = d->next;
    }

    return 0;
}

struct dtable {
    struct dtable *next;
    unsigned mask;
    unsigned *false_false_implications;
    unsigned *true_false_implications;
    unsigned *false_true_implications;
    unsigned *true_true_implications;
};

#define FALSE_FALSE 1
#define TRUE_FALSE  2
#define FALSE_TRUE  3
#define TRUE_TRUE   4

static void add_item(struct dtable **dtable, int size, int mode, unsigned parent, unsigned child)
{
    unsigned pbase, pmask, cbase, cmask;
    struct dtable *d;
    unsigned *mask;
    int i;

    pbase = parent/32;
    pmask = 1<<(parent%32);
    cbase = child/32;
    cmask = 1<<(child%32);

    d = dtable[cbase];
    while (d) {
        if (d->mask==cmask) break;
        d = d->next;
    }
    if (d==NULL) {
        d = (struct dtable *)_th_alloc(REWRITE_SPACE,sizeof(struct dtable));
        d->next = dtable[cbase];
        dtable[cbase] = d;
        d->false_false_implications = NULL;
        d->false_true_implications = NULL;
        d->true_false_implications = NULL;
        d->true_true_implications = NULL;
        d->mask = cmask;
    }

    switch (mode) {
        case FALSE_FALSE:
            if (d->false_false_implications==NULL) {
                d->false_false_implications = (unsigned *)_th_alloc(REWRITE_SPACE,sizeof(unsigned) * size);
                for (i = 0; i < size; ++i) {
                    d->false_false_implications[i] = 0;
                }
            }
            mask = d->false_false_implications;
            break;
        case FALSE_TRUE:
            if (d->false_true_implications==NULL) {
                d->false_true_implications = (unsigned *)_th_alloc(REWRITE_SPACE,sizeof(unsigned) * size);
                for (i = 0; i < size; ++i) {
                    d->false_true_implications[i] = 0;
                }
            }
            mask = d->false_true_implications;
            break;
        case TRUE_TRUE:
            if (d->true_true_implications==NULL) {
                d->true_true_implications = (unsigned *)_th_alloc(REWRITE_SPACE,sizeof(unsigned) * size);
                for (i = 0; i < size; ++i) {
                    d->true_true_implications[i] = 0;
                }
            }
            mask = d->true_true_implications;
            break;
        case TRUE_FALSE:
            if (d->true_false_implications==NULL) {
                d->true_false_implications = (unsigned *)_th_alloc(REWRITE_SPACE,sizeof(unsigned) * size);
                for (i = 0; i < size; ++i) {
                    d->true_false_implications[i] = 0;
                }
            }
            mask = d->true_false_implications;
            break;
    }

    mask[pbase] |= pmask;
}

static struct dtable **build_dependency_table(struct term_list *list)
{
    int i;
    int size = (_th_get_table_size()+31)/32;
    struct dtable **dtable = (struct dtable **)_th_alloc(REWRITE_SPACE,sizeof(struct dtable *) * size);
    struct dependencies *d;

    _zone_print0("Building dependency table");
    _tree_indent();
    for (i = 0; i < size; ++i) {
        dtable[i] = NULL;
    }

    //check_valid_list(list);

    while (list != NULL) {
        _zone_print_exp("Adding", list->e);
        d = list->dependencies;
        _tree_indent();
        while (d != NULL) {
            int t1, t2;
            t1 = _th_get_term_position(list->e);
            t2 = _th_get_term_position(d->term->e);
            _zone_print_exp("dependency", d->term->e);
            _zone_print2("terms %d %d", t1, t2);
            if (t1 >= 0 && t2 >= 0) {
                //printf("Adding offset %d %s\n", t1, _th_print_exp(list->e));
                //printf("and %d %s\n", t2, _th_print_exp(d->term->e));
                //fflush(stdout);
                if (d->reduction==_ex_true) {
                    _tree_undent();
                    _zone_print_exp("true_true", d->term->e);
                    _tree_indent();
                    add_item(dtable, size, TRUE_TRUE, t1, t2);
                    add_item(dtable, size, FALSE_FALSE, t2, t1);
                } else if (d->reduction==_ex_false) {
                    _tree_undent();
                    _zone_print_exp("true_false", d->term->e);
                    _tree_indent();
                    add_item(dtable, size, TRUE_FALSE, t1, t2);
                    add_item(dtable, size, TRUE_FALSE, t2, t1);
                }
            }
            d = d->next;
        }
        _tree_undent();
        list = list->next;
    }

    _tree_undent();
    return dtable;
}

static void add_dependencies(struct dtable **dtable, struct term_info *info, int size)
{
    int added = 1;
    int i, j;

    //_zone_print0("add_dependencies");
    //_tree_indent();
    while (added) {
        added = 0;
        for (i = 0; i < size; ++i) {
            struct dtable *d = dtable[i];
            while (d != NULL) {
                if (info->assert_makes_true[i] & d->mask) {
                    //_zone_print2("assert_makes_true[%d] has %x", i, d->mask);
                    //_tree_indent();
                    for (j = 0; j < size; ++j) {
                        unsigned c = ((d->true_true_implications?d->true_true_implications[j]:0) | info->assert_makes_true[j]);
                        if (c != info->assert_makes_true[j]) {
                            //_zone_print3("assert_makes_true[%d]: %x => %x", j, info->assert_makes_true[j], c);
                            added = 1;
                        }
                        info->assert_makes_true[j] = c;
                        c = ((d->false_true_implications?d->false_true_implications[j]:0) | info->deny_makes_true[j]);
                        if (c != info->deny_makes_true[j]) {
                            //_zone_print3("deny_makes_true[%d]: %x => %x", j, info->deny_makes_true[j], c);
                            added = 1;
                        }
                        info->deny_makes_true[j] = c;
                    }
                    //_tree_undent();
                }
                if (info->assert_makes_false[i] & d->mask) {
                    //_zone_print2("assert_makes_false[%d] has %x", i, d->mask);
                    //_tree_indent();
                    for (j = 0; j < size; ++j) {
                        unsigned c = ((d->true_true_implications?d->true_true_implications[j]:0) | info->assert_makes_false[j]);
                        if (c != info->assert_makes_false[j]) {
                            //_zone_print3("assert_makes_false[%d]: %x => %x", j, info->assert_makes_false[j], c);
                            added = 1;
                        }
                        info->assert_makes_false[j] = c;
                        c = ((d->false_true_implications?d->false_true_implications[j]:0) | info->deny_makes_false[j]);
                        if (c != info->deny_makes_false[j]) {
                            //_zone_print3("deny_makes_false[%d]: %x => %x", j, info->deny_makes_false[j], c);
                            added = 1;
                        }
                        info->deny_makes_false[j] = c;
                    }
                    //_tree_undent();
                }
                if (info->deny_makes_true[i] & d->mask) {
                    //_zone_print2("deny_makes_true[%d] has %x", i, d->mask);
                    //_tree_indent();
                    for (j = 0; j < size; ++j) {
                        unsigned c = ((d->true_false_implications?d->true_false_implications[j]:0) | info->assert_makes_true[j]);
                        if (c != info->assert_makes_true[j]) {
                            //_zone_print3("assert_makes_true[%d]: %x => %x", j, info->assert_makes_true[j], c);
                            added = 1;
                        }
                        info->assert_makes_true[j] = c;
                        c = ((d->false_false_implications?d->false_false_implications[j]:0) | info->deny_makes_true[j]);
                        if (c != info->deny_makes_true[j]) {
                            //_zone_print3("deny_makes_true[%d]: %x => %x", j, info->deny_makes_true[j], c);
                            added = 1;
                        }
                        info->deny_makes_true[j] = c;
                    }
                    //_tree_undent();
                }
                if (info->deny_makes_false[i] & d->mask) {
                    //_zone_print2("deny_makes_false[%d] has %x", i, d->mask);
                    //_tree_indent();
                    for (j = 0; j < size; ++j) {
                        unsigned c = ((d->true_false_implications?d->true_false_implications[j]:0) | info->assert_makes_false[j]);
                        if (c != info->assert_makes_false[j]) {
                            //_zone_print3("assert_makes_false[%d]: %x => %x", j, info->assert_makes_false[j], c);
                            added = 1;
                        }
                        info->assert_makes_false[j] = c;
                        c = ((d->false_false_implications?d->false_false_implications[j]:0) | info->deny_makes_false[j]);
                        if (c != info->deny_makes_false[j]) {
                            //_zone_print3("deny_makes_false[%d]: %x => %x", j, info->deny_makes_false[j], c);
                            added = 1;
                        }
                        info->deny_makes_false[j] = c;
                    }
                    //_tree_undent();
                }
                d = d->next;
            }
        }
    }
    //_tree_undent();
}

static struct term_info *_find_unate(struct env *env, struct dtable **dtable, struct _ex_intern *e)
{
    int pos, i, j;
    struct term_info *info;
    struct term_info *cinfo, *dinfo, *einfo;
    int size = (_th_get_table_size() + 31)/32;

#ifdef DEBUG
    _tree_print1("Finding unate for %s\n", _th_print_exp(e));
#endif
    if (e->user2) {
        //fprintf(stderr, "Cached\n");
        //fprintf(stderr, "user1 = %x\n", e->user1);
        //if (e->user1) {
        //    fprintf(stderr, "%d %d\n", ((struct score_rec *)e->user1)->elim_count,
        //            ((struct score_rec *)e->user1)->score);
        //}
        //fprintf(stderr, "rewrite %s\n", _th_print_exp(e->user2));
        //fprintf(stderr, "cache_next %s\n", _th_print_exp(e->next_cache));
        //_tree_print0("Cached");
        //fprintf(stderr, "Cached %s\n", _th_print_exp(e));
        //fprintf(stderr, "e->user2 = %s\n", _th_print_exp(e->user2));
        //fflush(stderr);
        return (struct term_info *)e->user2;
    }
#ifdef DEBUG
    _tree_indent();
#endif
    //fprintf(stderr, "Finding unate for %s\n", _th_print_exp(e));
    //fflush(stderr);

    info = (struct term_info *)_th_alloc(REWRITE_SPACE,sizeof(struct term_info));
    info->assert_makes_false = (unsigned *)_th_alloc(REWRITE_SPACE,sizeof(unsigned) * size * 4);
    info->assert_makes_true = info->assert_makes_false + size;
    info->deny_makes_true = info->assert_makes_true + size;
    info->deny_makes_false = info->deny_makes_true + size;
    info->vector_length = size;
    e->user2 = (struct _ex_intern *)info;

    e->next_cache = term_trail;
    term_trail = e;

    if (e->type==EXP_APPL) {
        switch (e->u.appl.functor) {
            case INTERN_TRUE:
                for (i = 0; i < size; ++i) {
                    info->assert_makes_false[i] = 0;
                    info->assert_makes_true[i] = 0xffffffff;
                    info->deny_makes_false[i] = 0;
                    info->deny_makes_true[i] = 0xffffffff;
                }
                break;
            case INTERN_FALSE:
                for (i = 0; i < size; ++i) {
                    info->assert_makes_false[i] = 0xffffffff;
                    info->assert_makes_true[i] = 0;
                    info->deny_makes_false[i] = 0xffffffff;
                    info->deny_makes_true[i] = 0;
                }
                break;
            case INTERN_NOT:
                cinfo = _find_unate(env,dtable,e->u.appl.args[0]);
                for (i = 0; i < size; ++i) {
                    info->assert_makes_false[i] = ((i<cinfo->vector_length)?cinfo->assert_makes_true[i]:0);
                    info->assert_makes_true[i] = ((i<cinfo->vector_length)?cinfo->assert_makes_false[i]:0);
                    info->deny_makes_false[i] = ((i<cinfo->vector_length)?cinfo->deny_makes_true[i]:0);
                    info->deny_makes_true[i] = ((i<cinfo->vector_length)?cinfo->deny_makes_false[i]:0);
                }
                break;
            case INTERN_AND:
                for (i = 0; i < size; ++i) {
                    info->assert_makes_true[i] =
                    info->deny_makes_true[i] = 0xffffffff;
                    info->assert_makes_false[i] =
                    info->deny_makes_false[i] = 0;
                }
                for (j = 0; j < e->u.appl.count; ++j) {
                    cinfo = _find_unate(env,dtable,e->u.appl.args[j]);
                    //fprintf(stderr,"Returning from _find_unate of %s\n", _th_print_exp(e->u.appl.args[j]));
                    //fflush(stderr);
                    for (i = 0; i < size; ++i) {
                        info->assert_makes_true[i] &= ((i<cinfo->vector_length)?cinfo->assert_makes_true[i]:0);
                        info->deny_makes_true[i] &= ((i<cinfo->vector_length)?cinfo->deny_makes_true[i]:0);
                        info->assert_makes_false[i] |= ((i<cinfo->vector_length)?cinfo->assert_makes_false[i]:0);
                        info->deny_makes_false[i] |= ((i<cinfo->vector_length)?cinfo->deny_makes_false[i]:0);
                    }
                }
                break;
            case INTERN_OR:
                for (i = 0; i < size; ++i) {
                    info->assert_makes_false[i] =
                    info->deny_makes_false[i] = 0xffffffff;
                    info->assert_makes_true[i] =
                    info->deny_makes_true[i] = 0;
                }
                for (j = 0; j < e->u.appl.count; ++j) {
                    cinfo = _find_unate(env,dtable,e->u.appl.args[j]);
                    for (i = 0; i < size; ++i) {
                        info->assert_makes_false[i] &= ((i<cinfo->vector_length)?cinfo->assert_makes_false[i]:0);
                        info->deny_makes_false[i] &= ((i<cinfo->vector_length)?cinfo->deny_makes_false[i]:0);
                        info->assert_makes_true[i] |= ((i<cinfo->vector_length)?cinfo->assert_makes_true[i]:0);
                        info->deny_makes_true[i] |= ((i<cinfo->vector_length)?cinfo->deny_makes_true[i]:0);
                    }
                }
                break;
            case INTERN_ITE:
                cinfo = _find_unate(env,dtable,e->u.appl.args[0]);
                dinfo = _find_unate(env,dtable,e->u.appl.args[1]);
                einfo = _find_unate(env,dtable,e->u.appl.args[2]);
                //printf("e, size = %s %d\n", _th_print_exp(e), size);
                //fflush(stdout);
                for (i = 0; i < size; ++i) {
                    info->assert_makes_true[i] =
                        (((i<cinfo->vector_length)?cinfo->assert_makes_true[i]:0) & ((i<dinfo->vector_length)?dinfo->assert_makes_true[i]:0)) |
                        (((i<cinfo->vector_length)?cinfo->assert_makes_false[i]:0) & ((i<einfo->vector_length)?einfo->assert_makes_true[i]:0)) |
                        (((i<dinfo->vector_length)?dinfo->assert_makes_true[i]:0) &((i<einfo->vector_length)?einfo->assert_makes_true[i]:0));
                    info->assert_makes_false[i] =
                        (((i<cinfo->vector_length)?cinfo->assert_makes_true[i]:0) & ((i<dinfo->vector_length)?dinfo->assert_makes_false[i]:0)) |
                        (((i<cinfo->vector_length)?cinfo->assert_makes_false[i]:0) & ((i<einfo->vector_length)?einfo->assert_makes_false[i]:0)) |
                        (((i<dinfo->vector_length)?dinfo->assert_makes_false[i]:0) & ((i<einfo->vector_length)?einfo->assert_makes_false[i]:0));
                    info->deny_makes_true[i] =
                        (((i<cinfo->vector_length)?cinfo->deny_makes_true[i]:0) & ((i<dinfo->vector_length)?dinfo->deny_makes_true[i]:0)) |
                        (((i<cinfo->vector_length)?cinfo->deny_makes_false[i]:0) & ((i<einfo->vector_length)?einfo->deny_makes_true[i]:0)) |
                        (((i<dinfo->vector_length)?dinfo->deny_makes_true[i]:0) & ((i<einfo->vector_length)?einfo->deny_makes_true[i]:0));
                    info->deny_makes_false[i] =
                        (((i<cinfo->vector_length)?cinfo->deny_makes_true[i]:0) & ((i<dinfo->vector_length)?dinfo->deny_makes_false[i]:0)) |
                        (((i<cinfo->vector_length)?cinfo->deny_makes_false[i]:0) & ((i<einfo->vector_length)?einfo->deny_makes_false[i]:0)) |
                        (((i<dinfo->vector_length)?dinfo->deny_makes_false[i]:0) & ((i<einfo->vector_length)?einfo->deny_makes_false[i]:0));
                }
                break;
            //case INTERN_XOR:
            case INTERN_EQUAL:
                if (_th_is_boolean_term(env,e->u.appl.args[0]) ||
                    _th_is_boolean_term(env,e->u.appl.args[1])) {
                    cinfo = _find_unate(env,dtable,e->u.appl.args[0]);
                    dinfo = _find_unate(env,dtable,e->u.appl.args[1]);
                    for (i =0; i < size; ++i) {
                        info->assert_makes_true[i] =
                            ((((i<cinfo->vector_length)?cinfo->assert_makes_true[i]:0) & ((i<dinfo->vector_length)?dinfo->assert_makes_true[i]:0)) |
                            (((i<cinfo->vector_length)?cinfo->assert_makes_false[i]:0) & ((i<dinfo->vector_length)?dinfo->assert_makes_false[i]:0)));
                        info->assert_makes_false[i] =
                            ((((i<cinfo->vector_length)?cinfo->assert_makes_true[i]:0) & ((i<dinfo->vector_length)?dinfo->assert_makes_false[i]:0)) |
                            (((i<cinfo->vector_length)?cinfo->assert_makes_false[i]:0) & ((i<dinfo->vector_length)?dinfo->assert_makes_true[i]:0)));
                        info->deny_makes_true[i] =
                            ((((i<cinfo->vector_length)?cinfo->deny_makes_true[i]:0) & ((i<dinfo->vector_length)?dinfo->deny_makes_true[i]:0)) |
                            (((i<cinfo->vector_length)?cinfo->deny_makes_false[i]:0) & ((i<dinfo->vector_length)?dinfo->deny_makes_false[i]:0)));
                        info->deny_makes_false[i] =
                            ((((i<cinfo->vector_length)?cinfo->deny_makes_true[i]:0) & ((i<dinfo->vector_length)?dinfo->deny_makes_false[i]:0)) |
                            (((i<cinfo->vector_length)?cinfo->deny_makes_false[i]:0) & ((i<dinfo->vector_length)?dinfo->deny_makes_true[i]:0)));
                    }
                    break;
                }
            default:
                for (i = 0; i < size; ++i) {
                    info->assert_makes_false[i] = info->assert_makes_true[i] = info->deny_makes_false[i] =
                        info->deny_makes_true[i] = 0;
                }
        }
    } else {
        for (i = 0; i < size; ++i) {
            info->assert_makes_false[i] = info->assert_makes_true[i] = info->deny_makes_false[i] =
                info->deny_makes_true[i] = 0;
        }
    }

    pos = _th_get_term_position(e);
    if (pos >= 0) {
        unsigned bit = 1<<(pos%32);
        unsigned offset = pos/32;
        //_tree_print2("Pos of %s is %d\n", _th_print_exp(e), pos);
        info->assert_makes_true[offset] |= bit;
        info->deny_makes_false[offset] |= bit;
    }

    //_zone_print_exp("exp", e);
    //fprintf(stderr, "exp %s\n", _th_print_exp(e));
    //fprintf(stderr, "info %d %d %d %d\n", info->assert_makes_false, info->assert_makes_true, info->deny_makes_false, info->deny_makes_true);
    add_dependencies(dtable,info,size);
    //fprintf(stderr, "after info %d %d %d %d\n", info->assert_makes_false, info->assert_makes_true, info->deny_makes_false, info->deny_makes_true);
    //fflush(stderr);

#ifdef DEBUG
    _tree_print0("Result");
    _tree_indent();
    _tree_print0("Assert makes true");
    _tree_indent();
    for (i = 0; i < size; ++i) {
        _tree_print1("%x", info->assert_makes_true[i]);
    }
    _tree_undent();
    _tree_print0("Deny makes true");
    _tree_indent();
    for (i = 0; i < size; ++i) {
        _tree_print1("%x", info->deny_makes_true[i]);
    }
    _tree_undent();
    _tree_print0("Assert makes false");
    _tree_indent();
    for (i = 0; i < size; ++i) {
        _tree_print1("%x", info->assert_makes_false[i]);
    }
    _tree_undent();
    _tree_print0("Deny makes false");
    _tree_indent();
    for (i = 0; i < size; ++i) {
        _tree_print1("%x", info->deny_makes_false[i]);
    }
    _tree_undent();
    _tree_undent();

    _tree_undent();
#endif

    return info;
}

static struct _ex_intern *transform_exp(struct env *env, struct _ex_intern *e)
{
    int i, j;
    struct _ex_intern **args;
    struct _ex_intern *f, *g, *h;

    if (e->user2) return e->user2;
    e->next_cache = term_trail;
    term_trail = e;

    _zone_print_exp("transforming", e);
    _tree_indent();

    if (e->type != EXP_APPL) {
        e->user2 = e;
        _tree_undent();
        return e;
    }

    switch (e->u.appl.functor) {
        case INTERN_NOT:
            f = e->u.appl.args[0];
            g = transform_exp(env,f);
            if (g->type==EXP_APPL && g->u.appl.functor==INTERN_NOT) {
                e->user2 = g->u.appl.args[0];
                _tree_undent();
                return e->user2;
            } else if (f==g) {
                e->user2 = e;
                _tree_undent();
                return e;
            } else if (g==_ex_false) {
                e->user2 = _ex_true;
                _tree_undent();
                return _ex_true;
            } else if (g==_ex_true) {
                e->user2 = _ex_false;
                _tree_undent();
                return _ex_false;
            } else {
                f = e->user2 = _ex_intern_appl1_env(env,INTERN_NOT,g);
                _tree_undent();
                return f;
            }
        case INTERN_EQUAL:
            g = transform_exp(env,e->u.appl.args[0]);
            h = transform_exp(env,e->u.appl.args[1]);
            if (g==_ex_true) {
                e->user2 = h;
                _tree_undent();
                return h;
            } else if (h==_ex_true) {
                e->user2 = g;
                _tree_undent();
                return g;
            } else if (g==_ex_false) {
                e->user2 = transform_exp(env,_ex_intern_appl1_env(env,INTERN_NOT,h));
                _tree_undent();
                return e->user2;
            } else if (h==_ex_false) {
                e->user2 = transform_exp(env,_ex_intern_appl1_env(env,INTERN_NOT,g));
                _tree_undent();
                return e->user2;
            } else if (g==h) {
                e->user2 = _ex_true;
                _tree_undent();
                return _ex_true;
            } else if ((g->type==EXP_INTEGER || g->type==EXP_RATIONAL || g==_ex_true || g==_ex_false) &&
                       (h->type==EXP_INTEGER || h->type==EXP_RATIONAL || h==_ex_true || h==_ex_false)) {
                e->user2 = _ex_false;
                _tree_undent();
                return _ex_false;
            } else if (g==e->u.appl.args[0] && h==e->u.appl.args[1]) {
                e->user2 = e;
                _tree_undent();
                return e;
            } else {
                e->user2 = _ex_intern_appl2_env(env,INTERN_EQUAL,g,h);
                _tree_undent();
                return e->user2;
            }
        case INTERN_OR:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            for (i = 0, j = 0; i < e->u.appl.count; ++i) {
                f = transform_exp(env,e->u.appl.args[i]);
#ifndef FAST
                if (f != e->u.appl.args[i]) {
                    _zone_print1("*** change %d ***", i);
                    _zone_print_exp("res", f);
                }
#endif
                if (f==_ex_true) {
                    e->user2 = _ex_true;
                    _tree_undent();
                    return _ex_true;
                } else if (f != _ex_false) {
                    args[j++] = f;
                }
            }
            if (j==0) {
                e->user2=_ex_false;
                _tree_undent();
                return _ex_false;
            } else if (j==1) {
                e->user2 = args[0];
                _tree_undent();
                return args[0];
            } else {
                f = _ex_intern_appl_env(env,INTERN_OR,j,args);
                g = _th_flatten_top(env,f);
                if (f==g) {
                    e->user2 = f;
                    _tree_undent();
                    return f;
                } else {
                    e->user2 = transform_exp(env,g);
                    _tree_undent();
                    return e->user2;
                }
            }
        case INTERN_AND:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            for (i = 0, j = 0; i < e->u.appl.count; ++i) {
                f = transform_exp(env,e->u.appl.args[i]);
#ifndef FAST
                if (f != e->u.appl.args[i]) {
                    _zone_print1("*** change %d ***", i);
                    _zone_print_exp("res", f);
                }
#endif
                if (f==_ex_false) {
                    e->user2 = _ex_false;
                    _tree_undent();
                    return _ex_false;
                } else if (f != _ex_true) {
                    args[j++] = f;
                }
            }
            if (j==0) {
                e->user2=_ex_true;
                _tree_undent();
                return _ex_true;
            } else if (j==1) {
                e->user2 = args[0];
                _tree_undent();
                return args[0];
            } else {
                f = e->user2 = _ex_intern_appl_env(env,INTERN_AND,j,args);
                g = _th_flatten_top(env,f);
                if (f==g) {
                    e->user2 = f;
                    _tree_undent();
                    return f;
                } else {
                    e->user2 = transform_exp(env,g);
                    _tree_undent();
                    return e->user2;
                }
            }
        case INTERN_ITE:
            f = transform_exp(env,e->u.appl.args[0]);
            g = transform_exp(env,e->u.appl.args[1]);
            h = transform_exp(env,e->u.appl.args[2]);
            if (f==_ex_true) {
                e->user2 = g;
                _tree_undent();
                return g;
            } else if (f==_ex_false) {
                e->user2 = h;
                _tree_undent();
                return h;
            } else if (g==h) {
                e->user2 = g;
                _tree_undent();
                return g;
            } else {
                f = e->user2 = _ex_intern_appl3_env(env,INTERN_ITE,f,g,h);
                _tree_undent();
                return f;
            }
/*        case INTERN_EQUAL:
            f = transform_exp(env,e->u.appl.args[0]);
            g = transform_exp(env,e->u.appl.args[1]);
            if (f==g) {
                e->user2 = _ex_true;
                return _ex_true;
            } else if ((f==_ex_true && g==_ex_false) || (f==_ex_false && g==_ex_true)) {
                e->user2 = _ex_false;
                return _ex_false;
            } else {
                f = e->user2 = _ex_intern_appl2_env(env,INTERN_EQUAL,f,g);
                return f;
            }*/
        default:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = transform_exp(env,e->u.appl.args[i]);
            }
            f = e->user2 = _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
            _tree_undent();
            return f;
    }
}

struct _ex_intern *_th_reduced_exp;
struct add_list *eliminate_unates(struct env *env, struct _ex_intern *e, struct term_list *list, struct add_list *al)
{
    struct term_info *info;
    int i;
    struct _ex_intern *t;
    struct add_list *a, *al_orig = al;
    int added;
    struct dtable **dependencies = build_dependency_table(list);
    int table_size = (_th_get_table_size()+31)/32;
    //struct dependencies *d;

    //fprintf(stderr, "eliminate_unates %s\n",_th_print_exp(e));
    //fflush(stderr);

    if (e==_ex_true || e==_ex_false) {
        return al;
    }
    _zone_print_exp("Eliminate unates", e);
    _tree_indent();
    _th_clear_cache();
    term_trail = NULL;

    //_tree_print1("table_size = %d", table_size);
    info = _find_unate(env,dependencies,e);

    while (term_trail) {
        term_trail->user2 = NULL;
        term_trail = term_trail->next_cache;
    }

#ifdef DEBUG
    _tree_print0("Result");
    _tree_indent();
    _tree_print0("Assert makes true");
    _tree_indent();
    for (i = 0; i < table_size; ++i) {
        _tree_print1("%x", info->assert_makes_true[i]);
    }
    _tree_undent();
    _tree_print0("Deny makes true");
    _tree_indent();
    for (i = 0; i < table_size; ++i) {
        _tree_print1("%x", info->deny_makes_true[i]);
    }
    _tree_undent();
    _tree_print0("Assert makes false");
    _tree_indent();
    for (i = 0; i < table_size; ++i) {
        _tree_print1("%x", info->assert_makes_false[i]);
    }
    _tree_undent();
    _tree_print0("Deny makes false");
    _tree_indent();
    for (i = 0; i < table_size; ++i) {
        _tree_print1("%x", info->deny_makes_false[i]);
    }
    _tree_undent();
    _tree_undent();
#endif

    for (i = 0; i < table_size; ++i) {
        if (info->assert_makes_true[i] & info->deny_makes_true[i]) {
            int j = 0;
            unsigned x = info->assert_makes_true[i] & info->deny_makes_true[i];
            while ((x&1)==0) {
                x = (x>>1);
                ++j;
            }
            _th_reduced_exp = _ex_true;
            //_tree_print0("Got assert makes false at %d %s\n", i*32+j);
            a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            a->next = al;
            a->e = _th_lookup_term(i*32+j);
            _tree_undent();
            return a;
        }
    }
#ifdef XX
    for (i = 0; i < table_size; ++i) {
        if (info->assert_makes_false[i]) {
            int j = 0;
            unsigned x = info->assert_makes_false[i];
            while ((x&1)==0) {
                x = (x>>1);
                ++j;
            }
            _th_reduced_exp = _ex_false;
            //_tree_print2("Got assert makes false at %d %s\n", i*32+j);
            a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            a->next = al;
            a->e = _th_lookup_term(i*32+j);
            _tree_undent();
            return a;
        }
        if (info->deny_makes_false[i]) {
            int j = 0;
            unsigned x = info->deny_makes_false[i];
            while ((x&1)==0) {
                x = (x>>1);
                ++j;
            }
            //_tree_print1("Got deny makes false at %d\n", i*32+j);
            _th_reduced_exp = _ex_false;
            a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            a->next = al;
            a->e = _ex_intern_appl1_env(env,INTERN_NOT,_th_lookup_term(i*32+j));
            _tree_undent();
            return a;
        }
    }
#endif
    added = 0;
    //fprintf(stderr, "e = %s\n", _th_print_exp(e));
    for (i = 0; i < table_size; ++i) {
        if (info->assert_makes_true[i]) {
            int j = 0;
            unsigned x = info->assert_makes_true[i];
            while (x) {
                while ((x&1)==0) {
                    x = (x>>1);
                    ++j;
                }
                added = 1;
                //_tree_print1("Got assert makes true at %d\n", i*32+j);
                t = _th_lookup_term(i*32+j);
                if (t) {
                    if (!t->user2) {
                        _tree_print_exp("Adding (f)", t);
                        t->next_cache = term_trail;
                        term_trail = t;
                        t->user2 = _ex_false;
                    }
                    //d = _th_get_neg_dependencies(t);
                    //_tree_indent();
                    //while (d != NULL) {
                    //    _tree_print_exp("dep", d->term->e);
                    //    if (d->term->e->user2 == NULL && (d->reduction==_ex_true || d->reduction==_ex_false)) {
                    //        d->term->e->user2 = d->reduction;
                    //        d->term->e->next_cache = term_trail;
                    //        term_trail = t;
                    //        _tree_print_exp("adding", d->term->e);
                    //    }
                    //    d = d->next;
                    //}
                    //_tree_undent();
                    a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                    a->next = al;
                    a->e = _ex_intern_appl1_env(env,INTERN_NOT,t);
                    //fprintf(stderr, "Neg adding %s\n", _th_print_exp(t));
                    al = a;
                }
                x = (x>>1);
                ++j;
            }
        }
        if (info->deny_makes_true[i]) {
            int j = 0;
            unsigned x = info->deny_makes_true[i];
            while (x) {
                while ((x&1)==0) {
                    x = (x>>1);
                    ++j;
                }
                added = 1;
                //_tree_print1("Got deny makes true at %d\n", i*32+j);
                t = _th_lookup_term(i*32+j);
                if (t) {
                    a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                    a->next = al;
                    a->e = t;
                    al = a;
                    //fprintf(stderr, "Adding (f) %s\n", _th_print_exp(t));
                    if (!t->user2) {
                        _tree_print_exp("Adding (t)", t);
                        t->next_cache = term_trail;
                        term_trail = t;
                        t->user2 = _ex_true;
                    }
                    //d = _th_get_dependencies(t);
                    //_tree_indent();
                    //while (d != NULL) {
                    //    _tree_print_exp("dep", d->term->e);
                    //    if (d->term->e->user2 == NULL && (d->reduction==_ex_true || d->reduction==_ex_false)) {
                    //        d->term->e->user2 = d->reduction;
                    //        d->term->e->next_cache = term_trail;
                    //        term_trail = t;
                    //        _tree_print_exp("adding", d->term->e);
                    //    }
                    //    d = d->next;
                    //}
                    //_tree_undent();
                }
                x = (x>>1);
                ++j;
            }
        }
    }

    if (al) _th_reduced_exp = transform_exp(env,e);
    //_tree_print_exp("_th_reduced_exp", _th_reduced_exp);

    while (term_trail != NULL) {
        term_trail->user2 = NULL;
        term_trail = term_trail->next_cache;
    }

    _tree_undent();
    if (_th_reduced_exp==e) {
        return al_orig;
    }
    if (added) {
        //return al;
        return eliminate_unates(env,_th_reduced_exp,list,al);
    } else {
        return al;
    }
}

struct add_list *_th_eliminate_unates(struct env *env, struct _ex_intern *e, struct term_list *list)
{
    struct add_list *res;
    struct add_list *a, *n;

    if (e==_ex_true || e==_ex_false) return NULL;

    res = eliminate_unates(env, e, list, NULL);

    a = NULL;

    while (res) {
        n = res->next;
        res->next = a;
        a = res;
        res = n;
    }

    return a;
}

struct _ex_intern *_th_find_unate(struct env *env, struct _ex_intern *e)
{
    struct term_info *info;
    int i;
    int max_tc;
    struct _ex_intern *term, *t;
    int table_size = (_th_get_table_size()+31)/32;

    _th_clear_cache();
    term_trail = NULL;

    //fprintf(stderr, "Find unate %s\n", _th_print_exp(e));
    //fflush(stderr);

    //_tree_print1("table_size = %d", table_size);
    info = _find_unate(env,NULL,e);

    while (term_trail) {
        term_trail->user2 = NULL;
        term_trail = term_trail->next_cache;
    }

#ifdef DEBUG
    _tree_print0("Result");
    _tree_indent();
    _tree_print0("Assert makes true");
    _tree_indent();
    for (i = 0; i < table_size; ++i) {
        _tree_print1("%x", info->assert_makes_true[i]);
    }
    _tree_undent();
    _tree_print0("Deny makes true");
    _tree_indent();
    for (i = 0; i < table_size; ++i) {
        _tree_print1("%x", info->deny_makes_true[i]);
    }
    _tree_undent();
    _tree_print0("Assert makes false");
    _tree_indent();
    for (i = 0; i < table_size; ++i) {
        _tree_print1("%x", info->assert_makes_false[i]);
    }
    _tree_undent();
    _tree_print0("Deny makes false");
    _tree_indent();
    for (i = 0; i < table_size; ++i) {
        _tree_print1("%x", info->deny_makes_false[i]);
    }
    _tree_undent();
    _tree_undent();
#endif

    max_tc = 0;
    term = NULL;
    for (i = 0; i < table_size; ++i) {
        if (info->assert_makes_false[i]) {
            int j = 0;
            unsigned x = info->assert_makes_false[i];
            while (x) {
                while ((x&1)==0) {
                    x = (x>>1);
                    ++j;
                }
                //_tree_print1("Got assert makes false at %d\n", i*32+j);
                t = _th_lookup_term(i*32+j);
                //tc = _th_term_count(env,e,t);
                //if (tc > max_tc) {
                //    max_tc = tc;
                //    term = t;
                //}
                term = t;
                x = (x>>1);
                ++j;
            }
        }
        if (info->deny_makes_false[i]) {
            int j = 0;
            unsigned x = info->deny_makes_false[i];
            while (x) {
                while ((x&1)==0) {
                    x = (x>>1);
                    ++j;
                }
                t = _th_lookup_term(i*32+j);
                //tc = _th_term_count(env,e,t);
                //if (tc > max_tc) {
                //    max_tc = tc;
                //    term = t;
                //}
                term = t;
                x = (x>>1);
                ++j;
            }
        }
    }
    if (term) return term;
    for (i = 0; i < table_size; ++i) {
        if (info->assert_makes_true[i]) {
            int j = 0;
            unsigned x = info->assert_makes_true[i];
            while ((x&1)==0) {
                x = (x>>1);
                ++j;
            }
            //_tree_print1("Got assert makes true at %d\n", i*32+j);
            return _th_lookup_term(i*32+j);
        }
        if (info->deny_makes_true[i]) {
            int j = 0;
            unsigned x = info->deny_makes_true[i];
            while ((x&1)==0) {
                x = (x>>1);
                ++j;
            }
            //_tree_print1("Got deny makes true at %d\n", i*32+j);
            return _th_lookup_term(i*32+j);
        }
    }

    return NULL;
}
