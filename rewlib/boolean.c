/*
 * boolean.c
 *
 * Routines for simplifying boolean expressions
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"

int _th_ite_simplification_level = 2;
int _th_ite_simplification_depth = 4;

static int duplicatable_term(struct env *env, struct _ex_intern *e, int depth)
{
    int is_bool;
    int i;
    if (e->type != EXP_APPL) return 1;

    if (_th_ite_simplification_level==2) return 1;
    if (_th_ite_simplification_level==1 && _th_uninterpreted_functor(e->u.appl.functor)) return 1;

    is_bool = (e->u.appl.functor==INTERN_ITE || e->u.appl.functor==INTERN_NOT ||
               e->u.appl.functor==INTERN_AND || e->u.appl.functor==INTERN_OR ||
               e->u.appl.functor==INTERN_XOR);

    if (is_bool) {
        if (depth==0) return 0;
        --depth;
    }

    for (i = 0; i < e->u.appl.count; ++i) {
        if (!duplicatable_term(env,e->u.appl.args[i],depth)) return 0;
    }

    return 1;
}

int _th_duplicatable_term(struct env *env, struct _ex_intern *e)
{
    return duplicatable_term(env,e,_th_ite_simplification_depth);
}

struct _ex_intern *_th_simplify_equal_ite(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *l, *r;

    l = e->u.appl.args[0];
    r = e->u.appl.args[1];

    if (e->u.appl.count==3 && !_th_is_constant(env,e->u.appl.args[2])) return NULL;

    if (l->type==EXP_APPL && l->u.appl.functor==INTERN_ITE && _th_duplicatable_term(env,r)) {
        if (e->u.appl.count==2) {
            r = _ex_intern_appl3_env(env,INTERN_ITE,l->u.appl.args[0],
                       _ex_intern_equal(env,e->type_inst,l->u.appl.args[1],r),
                       _ex_intern_equal(env,e->type_inst,l->u.appl.args[2],r));
            return r;
        } else {
            r = _ex_intern_appl3_env(env,INTERN_ITE,l->u.appl.args[0],
                       _ex_intern_appl3_env(env,e->u.appl.functor,l->u.appl.args[1],r,e->u.appl.args[2]),
                       _ex_intern_appl3_env(env,e->u.appl.functor,l->u.appl.args[2],r,e->u.appl.args[2]));
            return r;
        }
    }

    if (r->type==EXP_APPL && r->u.appl.functor==INTERN_ITE && _th_duplicatable_term(env,l)) {
        if (e->u.appl.count==2) {
            r = _ex_intern_appl3_env(env,INTERN_ITE,r->u.appl.args[0],
                       _ex_intern_equal(env,e->type_inst,l,r->u.appl.args[1]),
                       _ex_intern_equal(env,e->type_inst,l,r->u.appl.args[2]));
            return r;
        } else {
            r = _ex_intern_appl3_env(env,INTERN_ITE,r->u.appl.args[0],
                       _ex_intern_appl3_env(env,e->u.appl.functor,l,r->u.appl.args[1],e->u.appl.args[2]),
                       _ex_intern_appl3_env(env,e->u.appl.functor,l,r->u.appl.args[2],e->u.appl.args[2]));
            return r;
        }
    }

    return NULL;
}

struct _ex_intern *_th_simplify_ite(struct env *env, struct _ex_intern *e)
{
	if (e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_NOT) {
		return _ex_intern_appl3_env(env,INTERN_ITE,
			e->u.appl.args[0]->u.appl.args[0],
			e->u.appl.args[2],
			e->u.appl.args[1]);
	}
    if (e->u.appl.args[0]==e->u.appl.args[1]) return _ex_intern_appl3_env(env,INTERN_ITE,e->u.appl.args[0],_ex_true,e->u.appl.args[2]);
    if (e->u.appl.args[0]==e->u.appl.args[2]) return _ex_intern_appl3_env(env,INTERN_ITE,e->u.appl.args[0],e->u.appl.args[1],_ex_false);
	if (e->u.appl.args[1]==e->u.appl.args[2]) return e->u.appl.args[1];
	if (e->u.appl.args[1]==_ex_true && e->u.appl.args[2]==_ex_false) return e->u.appl.args[0];
	if (e->u.appl.args[1]==_ex_false && e->u.appl.args[2]==_ex_true) return _ex_intern_appl1_env(env,INTERN_NOT,e->u.appl.args[0]);
    if (e->u.appl.args[1]==_ex_true) {
        return _ex_intern_appl2_env(env,INTERN_OR,e->u.appl.args[0],e->u.appl.args[2]);
    }
    if (e->u.appl.args[1]==_ex_false) {
        return _ex_intern_appl2_env(env,INTERN_AND,_ex_intern_appl1_env(env,INTERN_NOT,e->u.appl.args[0]),e->u.appl.args[2]);
    }
    if (e->u.appl.args[2]==_ex_true) {
        return _ex_intern_appl2_env(env,INTERN_OR,_ex_intern_appl1_env(env,INTERN_NOT,e->u.appl.args[0]),e->u.appl.args[1]);
    }
    if (e->u.appl.args[2]==_ex_false) {
        return _ex_intern_appl2_env(env,INTERN_AND,e->u.appl.args[0],e->u.appl.args[1]);
    }
#ifdef NEEDS_CONTEXT
	if (e->u.appl.args[1]->type==EXP_APPL && e->u.appl.args[1]->u.appl.functor==INTERN_ITE &&
		_th_smaller(env,e->u.appl.args[1]->u.appl.args[0],e->u.appl.args[0]) &&
		!_th_smaller(env,e->u.appl.args[0],e->u.appl.args[1]->u.appl.args[0])) {
		f = e->u.appl.args[1];
		_th_derive_push(env);
		_th_derive_and_add(env,_th_mark_vars(env,f->u.appl.args[0]));
		h = _th_int_rewrite(env,e->u.appl.args[0], 1);
		_th_derive_pop(env);
		if (h==_ex_true) {
			return _ex_intern_appl3_env(env,INTERN_ITE,
				f->u.appl.args[0],
				f->u.appl.args[1],
				_ex_intern_appl3_env(env,INTERN_ITE,
				e->u.appl.args[0],
				f->u.appl.args[2],
				e->u.appl.args[2]));
		}
	}
	if (e->u.appl.args[2]->type==EXP_APPL && e->u.appl.args[2]->u.appl.functor==INTERN_ITE &&
		_th_smaller(env,e->u.appl.args[2]->u.appl.args[0],e->u.appl.args[0]) &&
		!_th_smaller(env,e->u.appl.args[0],e->u.appl.args[2]->u.appl.args[0])) {
		f = e->u.appl.args[2];
		_th_derive_push(env);
		_th_derive_and_add(env,_th_mark_vars(env,_th_negate_term(env,f->u.appl.args[0])));
		h = _th_int_rewrite(env,e->u.appl.args[0], 1);
		_th_derive_pop(env);
		if (h==_ex_false) {
			return _ex_intern_appl3_env(env,INTERN_ITE,
				f->u.appl.args[0],
				_ex_intern_appl3_env(env,INTERN_ITE,
				e->u.appl.args[0],
				e->u.appl.args[1],
				f->u.appl.args[1]),
				f->u.appl.args[2]);
		}
	}
#endif
	return NULL;
}

struct _ex_intern *_th_simplify_xor(struct env *env, struct _ex_intern *e)
{
	int i, j, k;
	struct _ex_intern **args;

	if (e->u.appl.count==0) return _ex_false;
	if (e->u.appl.count==1) return e->u.appl.args[0];
	j = 0;
	k = 0;
	args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
	for (i = 0; i < e->u.appl.count; ++i) {
		if (e->u.appl.args[i] != _ex_false) {
			if (e->u.appl.args[i]==_ex_true) {
				++k;
			} else {
				args[j++] = e->u.appl.args[i];
			}
		}
	}
	if (i==j) return NULL;
	if (k&1) {
		args[j++] = _ex_true;
	}
	return _ex_intern_appl_env(env,INTERN_XOR,j,args);
}

static int has_exp(struct _ex_intern *exp, struct _ex_intern *e)
{
    int i ;

    for (i = 0; i < e->u.appl.count; ++i) {
        if (e->u.appl.args[i]==exp) return 1 ;
    }

    return 0 ;
}

int _th_do_and_context = 1, _th_do_or_context = 1;

struct _ex_intern *_th_simplify_and(struct env *env, struct _ex_intern *e)
{
	int i, j, k, c;
    int count;
    struct _ex_intern **args;

	struct _ex_intern **targs, *f;

    if (_th_do_and_context==0) return NULL;

	if (e->u.appl.count==0) return _ex_true ;
	if (e->u.appl.count==1) return e->u.appl.args[0] ;
	if (has_exp(_ex_false,e)) return _ex_false;
	
	targs = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
	for (i = 0, k = 0, c = 0; i < e->u.appl.count; ++i) {
		if (e->u.appl.args[i] != _ex_true) {
			for (j = 0; j < c; ++j) {
				//printf("i, j = %d %d %x %x\n", i, j, e->u.appl.args[i], targs[j]) ;
				//fflush(stdout) ;
				if (_th_equal(env,e->u.appl.args[i],targs[j])) goto cont_and ;
			}
			//if (e->u.appl.args[i]->type==EXP_APPL && e->u.appl.args[i]->u.appl.functor==INTERN_OR) {
			//	f = _th_invert_or_equations(env,e->u.appl.args[i]);
			//	if (f==NULL) {
			//		f = e->u.appl.args[i];
			//	}
			//} else {
				f = e->u.appl.args[i];
			//}
			if (f != e->u.appl.args[i]) k = 1;
			targs[c++] = f ;
cont_and: ;
		}
	}
	if (k || c != i) return _th_flatten_top(env,_ex_intern_appl_env(env,e->u.appl.functor,c,targs)) ;
    if (_th_do_and_context) {
        count = e->u.appl.count;
        for (i = 0; i < count; ++i) {
            if (e->u.appl.args[i]->type==EXP_APPL && e->u.appl.args[i]->u.appl.functor != INTERN_AND &&
                e->u.appl.args[i]->u.appl.functor!=INTERN_ITE && _th_is_binary_term(env,e->u.appl.args[i])) {
                for (j = i+1; j < count; ++j) {
                    if (e->u.appl.args[j]->type==EXP_APPL && e->u.appl.args[j]->u.appl.functor != INTERN_AND &&
                        e->u.appl.args[j]->u.appl.functor!=INTERN_ITE) {
                        struct _ex_intern *f = _th_and_terms(env,e->u.appl.args[i],e->u.appl.args[j]);
                        if (f) {
                            _zone_print2("And reduce %d %d", i, j);
                            _zone_print_exp("i", e->u.appl.args[i]);
                            _zone_print_exp("j", e->u.appl.args[j]);
                            //printf("and reduce\n");
                            //printf("    %s\n", _th_print_exp(e->u.appl.args[i]));
                            //printf("    %s\n", _th_print_exp(e->u.appl.args[j]));
                            //printf("    %s\n", _th_print_exp(f));
                            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
                            for (k = 0, c = 0; k < e->u.appl.count; ++k) {
                                if (k != i && k != j) args[c++] = e->u.appl.args[k];
                            }
                            args[c++] = f;
                            f = _ex_intern_appl_env(env,e->u.appl.functor,c,args);
                            e = _th_simplify_and(env,f);
                            if (e) f = e;
                            return f;
                        }
                    }
                }
            }
        }
    }
	return NULL ;
}

struct _ex_intern *_th_simplify_or(struct env *env, struct _ex_intern *e)
{
    int i, j, c, k;
    struct _ex_intern **args;
    
    if (_th_do_or_context==0) return NULL;

    if (e->u.appl.count==0) return _ex_false ;
    if (e->u.appl.count==1) return e->u.appl.args[0] ;
    if (has_exp(_ex_true,e)) return _ex_true ;
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
    for (i = 0, c=0; i < e->u.appl.count; ++i) {
        if (e->u.appl.args[i] != _ex_false) {
            for (j = 0; j < c; ++j) {
                if (e->u.appl.args[i]==e->u.appl.args[j]) goto cont_or;
            }
            args[c++] = e->u.appl.args[i] ;
cont_or: ;
        }
    }
    if (c != i) {
        return _ex_intern_appl_env(env,e->u.appl.functor,c,args) ;
    }
    if (_th_do_or_context) {
        for (i = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type==EXP_APPL && e->u.appl.args[i]->u.appl.functor != INTERN_AND &&
                e->u.appl.args[i]->u.appl.functor!=INTERN_ITE && _th_is_binary_term(env,e->u.appl.args[i])) {
                for (j = i+1; j < e->u.appl.count; ++j) {
                    if (e->u.appl.args[j]->type==EXP_APPL && e->u.appl.args[j]->u.appl.functor != INTERN_AND &&
                        e->u.appl.args[j]->u.appl.functor!=INTERN_ITE) {
                        struct _ex_intern *f = _th_or_terms(env,e->u.appl.args[i],e->u.appl.args[j]);
                        if (f) {
                            //printf("Or reduce\n");
                            //printf("    %s\n", _th_print_exp(e->u.appl.args[i]));
                            //printf("    %s\n", _th_print_exp(e->u.appl.args[j]));
                            //printf("    %s\n", _th_print_exp(f));
                            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
                            for (k = 0, c = 0; k < e->u.appl.count; ++k) {
                                if (k != i && k != j) args[c++] = e->u.appl.args[k];
                            }
                            args[c++] = f;
                            f =  _ex_intern_appl_env(env,e->u.appl.functor,c,args);
                            e = _th_simplify_or(env,f);
                            if (e) f = e;
                            return f;
                        }
                    }
                }
            }
        }
    }
    return NULL ;
}

struct _ex_intern *_th_simplify_not(struct env *env, struct _ex_intern *e)
{
	int i;
	struct _ex_intern **args;

	e = e->u.appl.args[0] ;
	switch (e->type) {
	case EXP_APPL:
		switch(e->u.appl.functor) {
		case INTERN_TRUE:
			return _ex_false ;
		case INTERN_FALSE:
			return _ex_true ;
		case INTERN_NOT:
			return e->u.appl.args[0] ;
		case INTERN_AND:
			//check_size(e->u.appl.count) ;
			args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
			for (i = 0; i < e->u.appl.count; ++i) {
				args[i] = _ex_intern_appl_env(env,INTERN_NOT,1,e->u.appl.args+i) ;
			}
			return _ex_intern_appl_env(env,INTERN_OR,e->u.appl.count,args) ;
		case INTERN_OR:
			//check_size(e->u.appl.count) ;
			args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
			for (i = 0; i < e->u.appl.count; ++i) {
				args[i] = _ex_intern_appl_env(env,INTERN_NOT,1,e->u.appl.args+i) ;
			}
			return _ex_intern_appl_env(env,INTERN_AND,e->u.appl.count,args) ;
        case INTERN_ITE:
            return _ex_intern_appl3_env(env,INTERN_ITE,e->u.appl.args[0],
                       _ex_intern_appl1_env(env,INTERN_NOT,e->u.appl.args[1]),
                       _ex_intern_appl1_env(env,INTERN_NOT,e->u.appl.args[2]));
		default:
			return NULL ;
		}
	}
	return NULL ;
}

void _th_add_boolean_rules(int s, struct env *env)
{
    _th_add_property(env,_th_parse(env,"(-> (-> (not x) (True) g) (-> x (False) g) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (-> (not x) (False) g) (-> x (True) g) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (= (not x) (True) g) (-> x (False) g) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (= (not x) (False) g) (-> x (True) g) (True))")) ;

    _th_add_property(env,_th_parse(env,"(-> (-> (&& a b) (True) c) (&& (-> a (True) c) (-> b (True) c)) (and (compatible_prec a (True)) (compatible_prec a c) (compatible_prec b (True)) (compatible_prec b c)))")) ;
    _th_add_property(env,_th_parse(env,"(-> (-> (&& a b) (False) c) (-> a (False) (&& b c)) (and (compatible_prec a (False)) (compatible_prec a (&& b c))))")) ;
    _th_add_property(env,_th_parse(env,"(-> (-> (|| a b) (False) c) (&& (-> a (False) c) (-> b (False) c)) (and (compatible_prec a (False)) (compatible_prec a c) (compatible_prec b (False)) (compatible_prec b c)))")) ;
    _th_add_property(env,_th_parse(env,"(-> (-> (|| a b) (True) c) (-> a (True) (&& (not b) c)) (and (compatible_prec a (True)) (compatible_prec a (&& (not b) c))))")) ;
    _th_add_property(env,_th_parse(env,"(-> (-> (and a b) (True) c) (&& (-> a (True) c) (-> b (True) c)) (and (applyContext \"mainContext\") (compatible_prec a (True)) (compatible_prec a c) (compatible_prec b (True)) (compatible_prec b c)))")) ;
    _th_add_property(env,_th_parse(env,"(-> (-> (and a b) (False) c) (-> a (False) (&& b c)) (and (applyContext \"mainContext\") (compatible_prec a (False)) (compatible_prec a (&& b c))))")) ;
    _th_add_property(env,_th_parse(env,"(-> (-> (or a b) (False) c) (&& (-> a (False) c) (-> b (False) c)) (and (applyContext \"mainContext\") (compatible_prec a (False)) (compatible_prec a c) (compatible_prec b (False)) (compatible_prec b c)))")) ;
    _th_add_property(env,_th_parse(env,"(-> (-> (or a b) (True) c) (-> a (True) (&& (not b) c)) (and (applyContext \"mainContext\") (compatible_prec a (True)) (compatible_prec a (&& (not b) c))))")) ;
    _th_add_property(env,_th_parse(env,"(-> (-> (not a) (True) c) (-> a (False) c) (and (applyContext \"mainContext\") (compatible_prec a (False)) (compatible_prec a c)))")) ;
    _th_add_property(env,_th_parse(env,"(-> (-> (not a) (False) c) (-> a (True) c) (and (applyContext \"mainContext\") (compatible_prec a (True)) (compatible_prec a c)))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (== a b) (-> a b (True)) (and (applyContext \"mainContext\") (compatible_prec a b) (compatible_prec a (True))))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (= a b (True)) (== a b) (and (or (not (compatible_prec a b)) (not (compatible_prec a (True)))) (or (not (compatible_prec b a)) (not (compatible_prec b (True))))))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (-> a b (True)) (== a b) (and (or (not (compatible_prec a b)) (not (compatible_prec a (True)))) (or (not (compatible_prec b a)) (not (compatible_prec b (True))))))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (not (-> a (True) (True))) (-> a (False) (True)) (True)))")) ;
    //_th_add_property(env,_th_parse(env,"(--> (-> a b c) (change (-> a b c) (= a b c)) (and (notl (compatible_prec (QUOTE a) (QUOTE b))) (notl (compatible_prec (QUOTE b) (QUOTE a)))))")) ;
    //_th_add_property(env,_th_parse(env,"(--> (-> a b c) (change (-> a b c) (= a b c)) (and (notl (compatible_prec (QUOTE a) (QUOTE c))) (notl (compatible_prec (QUOTE b) (QUOTE c)))))")) ;
    _th_add_property(env,_th_parse(env,"(--> (= a b (-> c d (True))) (= a b newc) (and (applyContext \"mainContext\") (notl (illegalTerm a)) (notl (illegalTerm b)) (or (illegalTerm c) (illegalTerm d)) (choose nr (getTerms)) (match nr (-> c d newc))))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (== a (True)) a (True))")) ;

    //_th_add_property(env,_th_parse(env,"(=> (= a b (True)) (-> (== a b) (True) (True)) (True))")) ;
    //_th_add_property(env,_th_parse(env, "(-> (ite (True) tval fval) tval (True))"));
    //_th_add_property(env,_th_parse(env, "(-> (ite (False) tval fval) fval (True))"));
    //_th_add_property(env,_th_parse(env, "(-> (ite a tval fval) tval (== (QUOTE tval) (QUOTE fval)))"));
    //_th_add_property(env,_th_parse(env, "(-> (ite (not a) tval fval) (ite a fval tval) (True))"));

    _th_add_property(env,_th_parse(env, "(-> (ite (nless (nplus a -1) b) t f) (ite (nless b a) f t) (True))"));
}

