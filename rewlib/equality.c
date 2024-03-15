/*
 * equality.c
 *
 * Routines for testing the equality of two terms
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"

static struct _ex_intern *test_simplifications(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *f, *h, **args;
	int i, j, k, c;

    c = e->u.appl.functor ;
    f = e->u.appl.args[1] ;
	if (e->u.appl.count > 2) h = e->u.appl.args[2];
    e = e->u.appl.args[0] ;
    if (_th_equal(env,e,f)) return _ex_true ;
    if (e==_ex_true) return f;
    if (f==_ex_true) return e;
    if (e==_ex_false) return _ex_intern_appl1_env(env,INTERN_NOT,f);
    if (f==_ex_false) return _ex_intern_appl1_env(env,INTERN_NOT,e);
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_QUOTE &&
        f->type==EXP_APPL && f->u.appl.functor==INTERN_QUOTE) return NULL;
    switch (e->type) {
    	case EXP_VAR:
			if (f->type==EXP_APPL && _th_is_constructor(env,f->u.appl.functor) &&
				_th_is_free_in(f,e->u.var)) {
				if (c==INTERN_EQUAL) {
					return _ex_false;
				} else {
					return _ex_intern_appl1_env(env,INTERN_NOT,e->u.appl.args[2]) ;
				}
			}
			break;
		case EXP_APPL:
			if (e->u.appl.functor==INTERN_SET) {
				if (f->type==EXP_APPL && f->u.appl.functor==INTERN_SET) {
					if (e->u.appl.count == 0 && f->u.appl.count != 0) return _ex_false ;
					if (f->u.appl.count == 0 && e->u.appl.count != 0) return _ex_false ;
				} else if (f->type==EXP_APPL && f->u.appl.functor==INTERN_INTERSECT) {
					struct _ex_intern *set, *intersect ;
					args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * f->u.appl.count) ;
set_intersect:
					for (i = 0; i < f->u.appl.count; ++i) {
						if (f->u.appl.args[i]->type==EXP_APPL && f->u.appl.args[i]->u.appl.functor==INTERN_SET) goto set_intersect_cont ;
					}
					return NULL ;
set_intersect_cont:
					k = 0 ;
					for (j = 0; j < f->u.appl.count; ++j) {
						if (i != j) args[k++] = f->u.appl.args[j] ;
					}
					if (k > 1) {
						intersect = _ex_intern_appl_env(env,INTERN_INTERSECT,k,args) ;
					} else {
						intersect = args[0] ;
					}
					set = f->u.appl.args[i] ;
					for (i = 0; i < e->u.appl.count; ++i) {
						for (j = 0; j < set->u.appl.count; ++j) {
							if (_th_equal(env,e->u.appl.args[i],set->u.appl.args[j])) {
								goto set_intersect_cont2 ;
							}
						}
						return _ex_false ;
set_intersect_cont2: ;
					}
					for (i = 0; i < set->u.appl.count; ++i) {
						int mem = 0 ;
						for (j = 0; j < e->u.appl.count; ++j) {
							if (_th_equal(env,set->u.appl.args[i], e->u.appl.args[j])) {
								mem = 1 ;
								goto set_intersect_cont3 ;
							}
						}
set_intersect_cont3:
						args[i] = _ex_intern_appl2_env(env,INTERN_MEMBER,set->u.appl.args[i],intersect) ;
						if (!mem) {
							args[i] = _ex_intern_appl1_env(env,INTERN_NOT,args[i]) ;
						}
					}
					return _ex_intern_appl_env(env,INTERN_AND,i,args) ;
				}
				return NULL ;
			} else if (f->type==EXP_APPL &&
				       f->u.appl.functor==INTERN_SET && e->u.appl.functor==INTERN_INTERSECT) {
				struct _ex_intern *g = f ;
				f = e ;
				e = g ;
				goto set_intersect ;
			} else if (_th_is_constructor(env,e->u.appl.functor) &&
				f->type==EXP_APPL &&
				_th_is_constructor(env,f->u.appl.functor)) {
				if (e->u.appl.functor != f->u.appl.functor ||
					e->u.appl.count != f->u.appl.count) {
					if (c==INTERN_EQUAL) {
						return _ex_false ;
					} else {
						return _ex_intern_appl1_env(env,INTERN_NOT,h) ;
					}
				}
				args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
				for (i = 0; i < e->u.appl.count; ++i) {
					if (c==INTERN_EQUAL) {
						args[i] = _ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[i],f->u.appl.args[i]) ;
					} else {
						args[i] = _ex_intern_appl3_env(env,c,e->u.appl.args[i],f->u.appl.args[i],h) ;
					}
				}
				return _ex_intern_appl_env(env,INTERN_AND,e->u.appl.count,args) ;
			} else if (f->type==EXP_APPL && e->u.appl.functor==f->u.appl.functor &&
				e->u.appl.count==f->u.appl.count && _th_is_constructor(env,e->u.appl.functor)) {
                //_zone_print("Here a");
				for (i = 0; i < e->u.appl.count; ++i) {
                    struct _ex_intern *x = _ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[i],f->u.appl.args[i]);
					if (_th_int_rewrite(env,x,1)!=_ex_true) return NULL;
				}
				return _ex_true ;
#ifdef BUGGY
			} else if (_th_is_constructor(env,e->u.appl.functor) &&
                f->type==EXP_VAR && _th_is_free_in(e,f->u.var)) {
                return _ex_false;
#endif
			}
			break ;			
		case EXP_STRING:
			if (f->type==EXP_STRING) {
				if (strcmp(e->u.string,f->u.string)) {
					if (c==INTERN_EQUAL) {
						return _ex_false ;
					} else {
						return _ex_intern_appl1_env(env,INTERN_NOT,h) ;
					}
				} else {
					return _ex_true ;
				}
			}
			break ;
	    case EXP_INTEGER:
			if (f->type==EXP_INTEGER) {
				if (_th_big_equal(e->u.integer,f->u.integer)) {
					return _ex_true ;
				} else {
					if (c==INTERN_EQUAL) {
						return _ex_false ;
					} else {
						return _ex_intern_appl1_env(env,INTERN_NOT,h) ;
					}
				}
			}
			break ;
		case EXP_RATIONAL:
			if (f->type==EXP_RATIONAL) {
				if (_th_big_equal(e->u.rational.numerator,f->u.rational.numerator) &&
					_th_big_equal(e->u.rational.denominator,f->u.rational.denominator)) {
					return _ex_true ;
				} else {
					if (c==INTERN_EQUAL) {
						return _ex_false ;
					} else {
						return _ex_intern_appl1_env(env,INTERN_NOT,h) ;
					}
				}
			}
			break ;
	}
	return NULL;
}

static int prec_compare(struct env *env, struct _ex_intern *e, struct _ex_intern *f)
{
    _zone_print0("comparison");
    _tree_indent();
    if (((unsigned)e)<((unsigned)f)) {
        struct _ex_intern *cmp = _ex_intern_appl2_env(env,INTERN_ORDER_CACHE,e,f) ;
        if (cmp->rewrite) {
            _tree_undent();
            return (int)cmp->rewrite ;
        } else {
            if (_th_smaller(env,e,f) && !_th_smaller(env,f,e)) {
                _th_add_cache(cmp,(struct _ex_intern *)1) ;
                _zone_print0("returning 1");
                _tree_undent();
                return 1 ;
            } else if (_th_smaller(env,f,e) && !_th_smaller(env,e,f)) {
                _th_add_cache(cmp,(struct _ex_intern *)3) ;
                _zone_print0("returning 3");
                _tree_undent();
                return 3 ;
            } else {
                _zone_print0("returning 2");
                _tree_undent();
                return 2 ;
            }
        }
    } else {
        struct _ex_intern *cmp = _ex_intern_appl2_env(env,INTERN_ORDER_CACHE,f,e) ;
        if (cmp->rewrite) {
            _tree_undent();
            return 4-((int)cmp->rewrite) ;
        } else {
            if (_th_smaller(env,e,f) && !_th_smaller(env,f,e)) {
                _th_add_cache(cmp,(struct _ex_intern *)3) ;
                _zone_print0("returning 1");
                _tree_undent();
                return 1 ;
            } else if (_th_smaller(env,f,e) && !_th_smaller(env,e,f)) {
                _th_add_cache(cmp,(struct _ex_intern *)1) ;
                _zone_print0("returning 3");
                _tree_undent();
                return 3 ;
            } else {
                _zone_print0("returning 2");
                _tree_undent();
                return 2 ;
            }
        }
    }
}

struct _ex_intern *_th_normalize_equality(struct env *env,struct _ex_intern *e)
{
	int c = e->u.appl.functor;
    struct _ex_intern *f, *h;
    int i, j;

	f = e->u.appl.args[1];
	if (e->u.appl.count==3) {
		h = e->u.appl.args[2];
	}
	e = e->u.appl.args[0];

    switch (c) {
        case INTERN_EQUAL:
			i = prec_compare(env,e,f) ;
			switch (i) {
			case 1:
				return _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE, f, e, _ex_true) ;
			case 2:
				return NULL;
			case 3:
				return _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE, e, f, _ex_true) ;
			}
		case INTERN_ORIENTED_RULE:
			j = prec_compare(env,e,h) ;
			if (j == 3 || h == _ex_true) {
				i = prec_compare(env,e,f) ;
				switch (i) {
				case 1:
					if (prec_compare(env,f,h)==3) {
						return _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE, f, e, h) ;
					} else if (h==_ex_true) {
						return NULL;
						//return _ex_intern_appl2_env(env, INTERN_EQUAL, e, f) ;
					} else {
						return NULL;
						//return _ex_intern_appl3_env(env, INTERN_UNORIENTED_RULE, f, e, h) ;
					}
				case 2:
					return NULL;
					//return _ex_intern_appl3_env(env, INTERN_UNORIENTED_RULE, e, f, h) ;
				case 3:
					return NULL;
				}
			} else {
				if (prec_compare(env,f,e)==3 && prec_compare(env,f,h)==3) {
					return _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE, f, e, h) ;
					//} else if (h==_ex_true) {
					//goto cont_eq ;
					//return _ex_intern_appl2_env(env, INTERN_EQUAL, e, f) ;
				} else {
					//goto cont_eq ;
					return _ex_intern_appl3_env(env, INTERN_UNORIENTED_RULE, e, f, h) ;
				}
			}
		case INTERN_UNORIENTED_RULE:
			j = prec_compare(env,e,h) ;
			if (j == 3) {
				i = prec_compare(env,e,f) ;
				switch (i) {
				case 1:
					if (prec_compare(env,f,h)==3) {
						return _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE, f, e, h) ;
					} else if (h==_ex_true) {
						return _ex_intern_appl2_env(env, INTERN_EQUAL, e, f) ;
					} else {
					    return NULL;
					}
				case 2:
					if (h==_ex_true) {
						return _ex_intern_appl2_env(env, INTERN_EQUAL, e, f) ;
					} else {
						return NULL; 
					}
				case 3:
					return _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE, e, f, h) ;
				}
			} else {
				if (prec_compare(env,f,e)==3 && prec_compare(env,f,h)==3) {
					return _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE, f, e, h) ;
				} else if (h==_ex_true) {
					return _ex_intern_appl2_env(env, INTERN_EQUAL, e, f) ;
				} else {
					return NULL;
				}
			}
		default:
			return NULL;
	}
}

int _th_use_transitive = 0;

struct _ex_intern *_th_simplify_equality(struct env *env, struct _ex_intern *e)
{
    int x;
	struct _ex_intern *f;
//#ifdef TMP
    if (e->type_inst==_ex_real) {
        f = _th_r_simplify_equation(env,e);
    } else {
	    f = _th_simplify_equation(env,e);
    }
    if (f) {
        //f->type_inst = e->type_inst;
        return f;
    }
//#endif
    //f = _th_solve_for_a_var(env,e);
    //if (f) return f;
	f = test_simplifications(env,e);
    //_zone_print("Here2");
    if (f) {
        if (f->type==EXP_APPL && f->u.appl.functor==e->u.appl.functor) f->type_inst = e->type_inst;
        return f;
    }
    //_zone_print("Here3");
//#ifdef TMP
    if (e->type_inst==_ex_real) {
        f = _th_r_collect_like_terms(env,e);
    } else if (e->type_inst==_ex_int) {
        f = _th_collect_like_terms(env,e);
    }
    //_zone_print("Here4");
    if (f) {
        //f->type_inst = e->type_inst;
        return f;
    }
    //_zone_print("Here5");
//#ifdef DO_SOLVE
    if (e->type_inst==_ex_real) {
        f = _th_r_solve_for_a_var(env,e);
        if (f) {
            //printf("solve %s\n", _th_print_exp(e));
            //printf("to %s\n", _th_print_exp(f));
            return f;
        }
    } else if (e->type_inst==_ex_int) {
        f = _th_solve_for_a_var(env,e);
        if (f) return f;
    }
//#endif
    //_zone_print("Here6");
    //if (e->type_inst==_ex_real) {
	//    f = _th_r_equality_false_by_range(env,e);
    //} else if (e->type_inst==_ex_int) {
	//    f = _th_equality_false_by_range(env,e);
    //}
	//if (f) return f;
    //_zone_print("Here7");
	f = _th_bit_blast_comparison(env,e);
	if (f) return f;
    if (e->type_inst==_ex_real) {
        f = _th_r_remove_times_neg_one(env,e);
    } else if (e->type_inst==_ex_int) {
        f = _th_remove_times_neg_one(env,e);
    }
    //_zone_print("Here8");
    if (f) {
        //f->type_inst = e->type_inst;
        return f;
    }
    //_zone_print("Here9");
    if (e->type_inst==_ex_real) {
        f = _th_r_reverse_terms(env,e);
    } else if (e->type_inst==_ex_int) {
        f = _th_reverse_terms(env,e);
    }
    if (f) {
        //f->type_inst = e->type_inst;
        return f;
    }
    //_zone_print("Here10");
    f = _th_simplify_equal_ite(env,e);
    if (f) return f;
//#endif
    if (_th_use_transitive) {
        if (e->type_inst==_ex_real) {
            f = _th_r_search_equality(env,e);
        } else {
            f = _th_search_equality(env,e);
        }
	    //f = _th_normalize_equality(env,e);
	    if (f) return f;
    }
    //x = _th_equality_status(ENVIRONMENT_SPACE,env,e->u.appl.args[0],e->u.appl.args[1]);
    //if (x) {
    //    if (x==1) {
    //        return _ex_true;
    //    } else {
    //        return _ex_false;
    //    }
    //}
    f = _th_simplify_array_equality(env,e);

	return f;
}

struct _ex_intern *_th_fast_simplify_equality(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *f;
	f = _th_simplify_equation(env,e);
	if (f) return f;
	f = test_simplifications(env,e);
	if (f) return f;
    f = _th_collect_like_terms(env,e);
    if (f) return f;
	f = _th_equality_false_by_range(env,e);
	if (f) return f;
    f = _th_remove_times_neg_one(env,e);
    if (f) return f;
    f = _th_reverse_terms(env,e);
	//f = _th_normalize_equality(env,e);
	//if (f) return f;
	return f;
}

void _th_add_equality_rules(int s, struct env *env)
{
    _th_add_property(env,_th_parse(env,"(-> (-> e f g) (-> g (False) (True)) (and (inContext \"mainContext\") (compatible_prec g (True)) (not (-> e f (True)))))")) ;
    _th_add_property(env,_th_parse(env,"(-> (= e f g) (-> g (False) (True)) (and (compatible_prec g (True)) (not (== e f)))))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (-> a a1 b) (True) (== a a1))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (-> a b (False)) (True) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (-> a (True) (True)) a (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (-> a (False) (True)) (not a) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (-> a b (False)) (True) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (= a b c) (-> a b c) (and (applyContext \"mainContext\") (compatible_prec a b) (compatible_prec a c)))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (= b a c) (-> a b c) (and (applyContext \"mainContext\") (compatible_prec a b) (compatible_prec a c)))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (-> b a c) (-> a b c) (and (normal_condition c) (compatible_prec (QUOTE a) (QUOTE b)) (compatible_prec (QUOTE a) (QUOTE c))))")) ;
    //_th_add_property(env,_th_parse(env,"(--> (ALL (x) (-> b_ a_ c_)) (change (unquote (quantify (-> b_ a_ c_))) (unquote (quantify (-> a_ b_ c_)))) (and (compatible_prec (QUOTE a_) (QUOTE b_)) (compatible_prec (QUOTE a_) (QUOTE c_))))")) ;
    //_th_add_property(env,_th_parse(env,"(--> (ALL (x,y) (-> b_ a_ c_)) (change (unquote (quantify (-> b_ a_ c_))) (unquote (quantify (-> a_ b_ c_)))) (and (compatible_prec (QUOTE a_) (QUOTE b_)) (compatible_prec (QUOTE a_) (QUOTE c_))))")) ;
    _th_add_property(env,_th_parse(env,"(-> (-> a b (|| c d)) (&& (-> a b c) (-> a b d)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (+> a b (|| c d)) (&& (+> a b c) (+> a b d)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(+> (+> (== a b) (False) c) (not (subst b a (removeAnd c))) (q_var a))")) ;
    _th_add_property(env,_th_parse(env,"(+> (+> (== a b) (True) c) (subst b a (removeAnd c)) (q_var a))")) ;
}

