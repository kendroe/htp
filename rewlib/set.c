/*
/*
 * set.c
 *
 * Routines for simplifying set expressions
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"

int possibly_equal(struct env *env, struct _ex_intern *e, struct _ex_intern *s)
{
    int i ;
    int eq ;

    if (_th_equal(env,e,s)) return 1 ;

    switch (e->type) {
    case EXP_APPL:
        if (_th_is_constructor(env,e->u.appl.functor)) {
            switch (s->type) {
            case EXP_APPL:
                if (_th_is_constructor(env,s->u.appl.functor)) {
                    if (e->u.appl.functor != s->u.appl.functor) return -1 ;
                    if (e->u.appl.count != s->u.appl.count) return -1 ;
                    eq = 1 ;
                    for (i = 0; i < e->u.appl.count; ++i) {
                        int x = possibly_equal(env,e->u.appl.args[i],s->u.appl.args[i]) ;
                        if (x==1) return -1 ;
                        if (x==0) eq = 0 ;
                    }
                    return eq ;
                }
                return 0 ;
            case EXP_STRING:
            case EXP_INTEGER:
            case EXP_RATIONAL:
                return -1 ;
            default:
                return 0 ;
            }
        }
        return 0 ;
    case EXP_STRING:
    case EXP_INTEGER:
    case EXP_RATIONAL:
        switch(s->type) {
        case EXP_APPL:
            if (_th_is_constructor(env,e->u.appl.functor)) return -1 ;
            return 0 ;
        case EXP_STRING:
        case EXP_RATIONAL:
        case EXP_INTEGER:
            return -1 ;
        }
    default:
        return 0 ;
    }
}

struct _ex_intern *_th_simplify_difference(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *f;
    int i, j;

	if (e->u.appl.count==2 && e->u.appl.args[0]->type==EXP_APPL &&
		e->u.appl.args[0]->u.appl.functor==INTERN_SET &&
		e->u.appl.args[1]->type==EXP_APPL &&
		e->u.appl.args[1]->u.appl.functor==INTERN_SET) {
		
		struct _ex_intern **left, **right, **out ;
		int lc = 0, oc = 0, rc = 0;
		
		f = e->u.appl.args[1] ;
		e = e->u.appl.args[0] ;
		
		left = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
		right = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * f->u.appl.count) ;
		out = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
		
		for (j = 0; j < f->u.appl.count; ++j) right[j] = 0 ;
		
		for (i = 0; i < e->u.appl.count; ++i) {
			int mo = 0 ;
			for (j = 0; j < f->u.appl.count; ++j) {
				switch (possibly_equal(env,e->u.appl.args[i],f->u.appl.args[j])) {
				case 1:
					goto cont_i ;
				case 0:
					mo = 1 ;
					right[j] = (struct _ex_intern *)1 ;
				}
			}
			if (mo) {
				left[lc++] = e->u.appl.args[i] ;
			} else {
				out[oc++] = e->u.appl.args[i] ;
			}
cont_i: ;
		}
		
		for (i = 0; i < f->u.appl.count; ++i) {
			if (right[i]) right[rc++] = f->u.appl.args[i] ;
		}
		
		if (rc==f->u.appl.count && lc==e->u.appl.count) return NULL ;
		if (rc && lc) {
			e = _ex_intern_appl2_env(env,INTERN_DIFFERENCE,
				_ex_intern_appl_env(env,INTERN_SET,lc,left),
				_ex_intern_appl_env(env,INTERN_SET,rc,right)) ;
		} else {
			e = _ex_intern_appl_env(env,INTERN_SET,lc,left) ;
		}
		if (oc) {
			return _ex_intern_appl2_env(env,INTERN_UNION,
				_ex_intern_appl_env(env,INTERN_SET,oc,out),e) ;
		} else {
			return e ;
		}
		
	}
	return NULL ;
}

struct _ex_intern *_th_simplify_union(struct env *env, struct _ex_intern *e)
{
	int i, j, k, l, n;
    struct _ex_intern *f, *h, **args, **args2;

	if (e->u.appl.count==1) return e->u.appl.args[0] ;
	for (i = 0; i < e->u.appl.count; ++i) {
		if (e->u.appl.args[i]->type == EXP_APPL &&
			e->u.appl.args[i]->u.appl.functor==INTERN_SET) break ;
	}
	if (i==e->u.appl.count) goto cont_union ;
	for (j = i+1; j < e->u.appl.count; ++j) {
		if (e->u.appl.args[j]->type == EXP_APPL &&
			e->u.appl.args[j]->u.appl.functor==INTERN_SET) break ;
	}
	if (j==e->u.appl.count) goto cont_union ;
	f = e->u.appl.args[i] ;
	h = e->u.appl.args[j] ;
	k = l = n = 0 ;
	args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern **) * (f->u.appl.count + h->u.appl.count));
	while(k < f->u.appl.count || n < h->u.appl.count) {
		if (n==h->u.appl.count || (k < f->u.appl.count && ((unsigned)f->u.appl.args[k])>((unsigned)h->u.appl.args[n]))) {
			if (n < h->u.appl.count && h->u.appl.args[n]==f->u.appl.args[k]) ++n ;
			//check_size(l+1) ;
			args[l++] = f->u.appl.args[k++] ;
		} else {
			if (k < f->u.appl.count && h->u.appl.args[n]==f->u.appl.args[k]) ++k ;
			//check_size(l+1) ;
			args[l++] = h->u.appl.args[n++] ;
		}
	}
	args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (e->u.appl.count+1));
	args2[0] = _ex_intern_appl_env(env,INTERN_SET,l,args) ;
	n = 1 ;
	//check_size(e->u.appl.count+1) ;
	for (k = 0; k < e->u.appl.count; ++k) {
		if (k!=i&&k!=j) args2[n++] = e->u.appl.args[k] ;
	}
	return _ex_intern_appl_env(env,INTERN_UNION,n,args2) ;
cont_union:
	for (i = 0; i < e->u.appl.count; ++i) {
		for (j = 0; j < e->u.appl.count; ++j) {
			if (i != j) {
				if (_th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_SUBSET,e->u.appl.args[i],e->u.appl.args[j]),1)==_ex_true) {
					args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern **) * e->u.appl.count);
					for (j = 0, k = 0; i < e->u.appl.count; ++i) {
						if (i != j) {
							args[k++] = e->u.appl.args[j];
						}
					}
					return _ex_intern_appl_env(env,INTERN_UNION,k,args);
				}
			}
		}
	}
	return NULL;
}

struct _ex_intern *_th_simplify_subset(struct env *env, struct _ex_intern *e)
{
	int i;
    struct _ex_intern *f;

	if (e->type==EXP_APPL && e->u.appl.count==2 &&
		e->u.appl.args[0]->type==EXP_APPL &&
		e->u.appl.args[0]->u.appl.functor==INTERN_SET) {
		
		struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.args[0]->u.appl.count) ;
		f = e->u.appl.args[0] ;
		for (i = 0; i < f->u.appl.count; ++i) {
			args[i] = _ex_intern_appl2_env(env, INTERN_MEMBER, f->u.appl.args[i], e->u.appl.args[1]) ;
		}
		return _ex_intern_appl_env(env, INTERN_AND, f->u.appl.count, args) ;
	}
	return NULL ;
}

struct _ex_intern *_th_simplify_separate(struct env *env, struct _ex_intern *e)
{
	int i;
    struct _ex_intern *f;

	if (e->type==EXP_APPL && e->u.appl.count==2 &&
		e->u.appl.args[0]->type==EXP_APPL &&
		e->u.appl.args[0]->u.appl.functor==INTERN_SET) {
		
		struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.args[0]->u.appl.count) ;
		f = e->u.appl.args[0] ;
		for (i = 0; i < f->u.appl.count; ++i) {
			args[i] = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env, INTERN_MEMBER, f->u.appl.args[i], e->u.appl.args[1])) ;
		}
		return _ex_intern_appl_env(env, INTERN_AND, f->u.appl.count, args) ;
	} else if (e->type==EXP_APPL && e->u.appl.count==2 &&
		e->u.appl.args[1]->type==EXP_APPL &&
		e->u.appl.args[1]->u.appl.functor==INTERN_SET) {
		
		struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.args[1]->u.appl.count) ;
		f = e->u.appl.args[1] ;
		for (i = 0; i < f->u.appl.count; ++i) {
			args[i] = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env, INTERN_MEMBER, f->u.appl.args[i], e->u.appl.args[0])) ;
		}
		return _ex_intern_appl_env(env, INTERN_AND, f->u.appl.count, args) ;
	}
	return NULL ;	
}

static int compatible_constant(struct env *env, struct _ex_intern *e, struct _ex_intern *p)
{
    int i, m, r ;

    switch (p->type) {
        case EXP_APPL:
            if (!_th_is_constructor(env,e->u.appl.functor)) return 0 ;
            if (e->type != EXP_APPL || e->u.appl.functor != p->u.appl.functor) {
                if (e->type==EXP_APPL && _th_is_constructor(env,e->u.appl.functor)) return -1 ;
                if (e->type==EXP_STRING || e->type==EXP_INTEGER || e->type==EXP_RATIONAL) return -1 ;
                return 0 ;
            }
            m = 1 ;
            for (i = 0; i < e->u.appl.count; ++i) {
                r = _th_is_constant(env,e->u.appl.args[i]) ;
                if (r==-1) return -1 ;
                if (r < m) m = r ;
            }
            return m ;
        case EXP_STRING:
        case EXP_INTEGER:
        case EXP_RATIONAL:
            if (e==p) return 1 ;
            if (e->type==EXP_APPL && _th_is_constructor(env,e->u.appl.functor)) return -1 ;
            if (e->type==EXP_STRING || e->type==EXP_INTEGER || e->type==EXP_RATIONAL) return -1 ;
            return 0 ;
        case EXP_VAR:
            return 1 ;
        default:
            return 0 ;
    }
}

struct _ex_intern *_th_simplify_member(struct env *env, struct _ex_intern *e)
{
	int i, j, c;
	struct match_return *m;
	char *mark;
	struct _ex_intern *f;
	unsigned *tmp1, *vars;

	f = e->u.appl.args[1] ;
	if (f->type==EXP_APPL &&
		f->u.appl.functor==INTERN_SET) {
		
		struct _ex_intern **args = ALLOCA(sizeof(struct _ex_intern *) * f->u.appl.count) ;
		
		for (i = 0; i < f->u.appl.count; ++i) {
			args[i] = _ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0],f->u.appl.args[i]) ;
		}
		return _ex_intern_appl_env(env,INTERN_OR,f->u.appl.count,args) ;
	} else if (f->type==EXP_QUANT && f->u.quant.quant==INTERN_SETQ &&
		_th_is_constant(env,f->u.quant.exp)) {
		switch (compatible_constant(env,e->u.appl.args[0],f->u.quant.exp)) {
		case -1:
			return _ex_false ;
		case 0:
			return NULL ;
		case 1:
			mark = _th_alloc_mark(MATCH_SPACE) ;
			m = _th_match(env,f->u.quant.exp,e->u.appl.args[0]) ;
			_th_alloc_release(MATCH_SPACE,mark) ;
			if (m==NULL) return NULL ;
			tmp1 = ALLOCA(sizeof(unsigned) * f->u.quant.var_count) ;
			vars = _th_get_free_vars_leave_marked(f->u.quant.exp,&c) ;
			for (i = 0, j = 0; i < f->u.quant.var_count; ++i) {
				if (!_th_intern_get_data(f->u.quant.vars[i])) {
					tmp1[j++] = f->u.quant.vars[i] ;
				}
			}
			for (i = 0; i < c; ++i) {
				_th_intern_set_data(vars[i], 0) ;
			}
			f = _th_subst(env,m->theta,f->u.quant.cond) ;
			if (j > 0) {
				return _ex_intern_quant(INTERN_EXISTS, j, tmp1, f, _ex_true) ;
			} else {
				return f ;
			}
		}
	}
	return NULL ;
}

static struct _ex_intern *intersect_sets(struct env *env, struct _ex_intern *e, struct _ex_intern *f)
{
    int i, g, n, c, l;
    struct _ex_intern **args;
    struct _ex_intern *exp;

    //printf("Intersect sets %s ", _th_print_exp(e));
    //printf("and %s\n", _th_print_exp(f));

    if (e->type==EXP_APPL && f->type==EXP_APPL) {
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * sizeof(struct _ex_intern *) * f->u.appl.count);
        
        i = 0 ; l = 0;
        for (i = 0; i < f->u.appl.count; ++i) {
            c = 0 ; n = e->u.appl.count-1 ;
            while(c < n-1 && n > 0) {
                g = (c + n) / 2 ;
                if (((unsigned)e->u.appl.args[g])<((unsigned)f->u.appl.args[i])) {
                    n = g ;
                } else {
                    c = g ;
                }
            }
            if (f->u.appl.args[i] != e->u.appl.args[n] &&
                f->u.appl.args[i] != e->u.appl.args[c]) continue ;
            args[l++] = f->u.appl.args[i] ;
        }
        return _ex_intern_appl_env(env,INTERN_SET,l,args) ;
    } else if (e->type==EXP_APPL) {
        char *mark;
cont:
        mark = _th_alloc_mark(MATCH_SPACE);
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * sizeof(struct _ex_intern *) * e->u.appl.count);
        l = 0;
        for (i = 0; i < e->u.appl.count; ++i) {
            struct match_return *mr = _th_match(env,f->u.quant.exp,e->u.appl.args[i]);
            if (mr != NULL && _th_int_rewrite(env,_th_subst(env,mr->theta,f->u.quant.cond),1)==_ex_true) {
                args[l++] = e->u.appl.args[i];
            }
        }
        _th_alloc_release(MATCH_SPACE,mark);
        return _ex_intern_appl_env(env,INTERN_SET,l,args);
    } else if (f->type==EXP_APPL) {
        struct _ex_intern *h = e;
        e = f;
        f = h;
        goto cont;
    } else {
        char *mark = _th_alloc_mark(MATCH_SPACE);
        struct _ex_intern *h;
        unsigned *vars = (unsigned *)ALLOCA(sizeof(unsigned) * (e->u.quant.var_count + f->u.quant.var_count));
        struct match_return *mr;
        struct _ex_intern *used_vars = _ex_intern_appl2_env(env,INTERN_TUPLE,e,f);
        struct _ex_unifier *u = _th_new_unifier(MATCH_SPACE);
        for (i = 0; i < e->u.quant.var_count; ++i) {
            vars[i] = e->u.quant.vars[i];
            used_vars = _ex_intern_appl2_env(env,INTERN_TUPLE,used_vars,_ex_intern_var(vars[i]));
        }
        n = i;
        for (i = 0; i < f->u.quant.var_count; ++i) {
            vars[n+i] = _th_name_away(used_vars,f->u.quant.vars[i]);
            used_vars = _ex_intern_appl2_env(env,INTERN_TUPLE,used_vars,_ex_intern_var(vars[n+i]));
            u = _th_add_pair(MATCH_SPACE,u,f->u.quant.vars[i],_ex_intern_var(vars[n+i]));
        }
        mr = _th_unify(env,e->u.quant.exp,_th_subst(env,u,f->u.quant.exp));
        if (mr==NULL) return _ex_intern_appl_env(env,INTERN_SET,0,NULL);
        h = _ex_intern_appl2_env(env,INTERN_AND,
            _th_subst(env,mr->theta,e->u.quant.cond),
            _th_subst(env,mr->theta,_th_subst(env,u,f->u.quant.cond)));
        h = _th_flatten_top(env,h);
        exp = _th_subst(env,mr->theta,e->u.quant.exp);
        _th_alloc_release(MATCH_SPACE,mark);
        return _ex_intern_quant(INTERN_SETQ,e->u.quant.var_count+f->u.quant.var_count,vars,exp,h);
    }
}

struct _ex_intern *_th_simplify_intersect(struct env *env, struct _ex_intern *e)
{
	int i, j, k, n;
	struct _ex_intern *f, *h, **args;

	if (e->u.appl.count==1) return e->u.appl.args[0] ;
	for (i = 0; i < e->u.appl.count; ++i) {
		if (e->u.appl.args[i]->type == EXP_APPL &&
			e->u.appl.args[i]->u.appl.functor==INTERN_SET) break ;
		if (e->u.appl.args[i]->type == EXP_QUANT &&
			e->u.appl.args[i]->u.quant.quant == INTERN_SETQ &&
			_th_is_constant(env,e->u.appl.args[i]->u.quant.exp)) break;
	}
	if (i==e->u.appl.count) return NULL ;
	for (j = i+1; j < e->u.appl.count; ++j) {
		if (e->u.appl.args[j]->type == EXP_APPL &&
			e->u.appl.args[j]->u.appl.functor==INTERN_SET) break ;
		if (e->u.appl.args[j]->type == EXP_QUANT &&
			e->u.appl.args[j]->u.quant.quant == INTERN_SETQ &&
			_th_is_constant(env,e->u.appl.args[j]->u.quant.exp)) break;
	}
	if (j==e->u.appl.count) return NULL ;
	f = e->u.appl.args[i] ;
	h = e->u.appl.args[j] ;
	n = 1 ;
	//check_size(e->u.appl.count+1) ;
	args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (e->u.appl.count+1));
	args[0] = intersect_sets(env, f, h);
	for (k = 0; k < e->u.appl.count; ++k) {
		if (k!=i&&k!=j) args[n++] = e->u.appl.args[k] ;
	}
	return _ex_intern_appl_env(env,INTERN_INTERSECT,n,args) ;
}

static unsigned find_equal_var;
static int find_equal_term;
static struct _ex_unifier *find_equal(int var_count, unsigned *vars, int count, struct _ex_intern *args[])
{
    int i ;
    struct _ex_unifier *r ;

    for (i = 0; i < var_count; ++i) {
        _th_intern_set_data(vars[i],1) ;
    }

    r = NULL ;
    for (i = 0; i < count; ++i) {
        if (args[i]->type==EXP_APPL && args[i]->u.appl.functor==INTERN_EQUAL) {
            if (args[i]->u.appl.args[0]->type==EXP_VAR &&
                _th_intern_get_data(args[i]->u.appl.args[0]->u.var)) {
                r = _th_new_unifier(REWRITE_SPACE) ;
                find_equal_var = args[i]->u.appl.args[0]->u.var;
                find_equal_term = i;
                r = _th_add_pair(REWRITE_SPACE,r,args[i]->u.appl.args[0]->u.var,
                                 args[i]->u.appl.args[1]) ;
                break ;
            }
            if (args[i]->u.appl.args[1]->type==EXP_VAR &&
                _th_intern_get_data(args[i]->u.appl.args[1]->u.var)) {
                r = _th_new_unifier(REWRITE_SPACE) ;
                find_equal_var = args[i]->u.appl.args[1]->u.var;
                find_equal_term = i;
                r = _th_add_pair(REWRITE_SPACE,r,args[i]->u.appl.args[1]->u.var,
                                 args[i]->u.appl.args[0]);
                break ;
            }
        }
        if (args[i]->type==EXP_APPL && args[i]->u.appl.functor==INTERN_ORIENTED_RULE &&
            args[i]->u.appl.args[2]==_ex_true && args[i]->u.appl.args[0]->type==EXP_VAR &&
            _th_intern_get_data(args[i]->u.appl.args[0]->u.var)) {
            r = _th_new_unifier(REWRITE_SPACE) ;
            find_equal_var = args[i]->u.appl.args[0]->u.var;
            find_equal_term = i;
            r = _th_add_pair(REWRITE_SPACE,r,args[i]->u.appl.args[0]->u.var,
                             args[i]->u.appl.args[1]) ;
            break;
        }
    }

    for (i = 0; i < var_count; ++i) {
        _th_intern_set_data(vars[i],0) ;
    }

    return r ;
}

struct _ex_intern *_th_remove_equal_bound(struct env *env, struct _ex_intern *quant)
{
    struct _ex_unifier *u;
    int i, j;
    unsigned *vars;
    struct _ex_intern **args;

    if (quant->type != EXP_QUANT || quant->u.quant.cond->type != EXP_APPL ||
        (quant->u.quant.cond->u.appl.functor != INTERN_AND &&
         quant->u.quant.cond->u.appl.functor != INTERN_NC_AND)) return NULL;

    u = find_equal(quant->u.quant.var_count,
                   quant->u.quant.vars,
                   quant->u.quant.cond->u.appl.count,
                   quant->u.quant.cond->u.appl.args);

    if (u==NULL) return NULL;

    vars = (unsigned *)ALLOCA(sizeof(unsigned) * quant->u.quant.var_count);
    for (i = 0, j = 0; i < quant->u.quant.var_count; ++i) {
        if (quant->u.quant.vars[i] != find_equal_var) {
            vars[j++] = quant->u.quant.vars[i];
        }
    }

    for (i = 0; i < quant->u.quant.cond->u.appl.count; ++i) {
        if (i != find_equal_term && _th_is_free_in(quant->u.quant.cond->u.appl.args[i],find_equal_var)) {
            return _ex_intern_quant(quant->u.quant.quant,
                                    quant->u.quant.var_count-1,
                                    vars,
                                    _th_subst(env,u,quant->u.quant.exp),
                                    _th_subst(env,u,quant->u.quant.cond));
        }
    }

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * quant->u.quant.cond->u.appl.count);

    for (i = 0, j = 0; i < quant->u.quant.cond->u.appl.count; ++i) {
        if (i != find_equal_term) {
            args[j++] = quant->u.quant.cond->u.appl.args[i];
        }
    }

    if (j==1) {
        return _ex_intern_quant(quant->u.quant.quant,
                                quant->u.quant.var_count-1,
                                vars,
                                _th_subst(env,u,quant->u.quant.exp),
                                _ex_intern_appl1_env(env,INTERN_NORMAL,args[0]));
    } else {
        return _ex_intern_quant(quant->u.quant.quant,
                                quant->u.quant.var_count-1,
                                vars,
                                _th_subst(env,u,quant->u.quant.exp),
                                _ex_intern_appl1_env(env,INTERN_NORMAL,_ex_intern_appl_env(env,INTERN_AND,j,args)));
    }
}

static int is_quant_var(unsigned var, struct _ex_intern *quant)
{
    int i;

    for (i = 0; i < quant->u.quant.var_count; ++i) {
        if (var==quant->u.quant.vars[i]) return 1;
    }
    return 0;
}

static struct _ex_intern *distribute_or_quant(struct env *env, struct _ex_intern *quant)
{
    struct _ex_intern **args, *cond, *t, *acc, *val, **args2 ;
    unsigned var, *vars ;
    int i, j, term ;
    struct _ex_unifier *u;

    if (quant->u.quant.cond->type==EXP_APPL &&
        (quant->u.quant.cond->u.appl.functor==INTERN_AND ||
         quant->u.quant.cond->u.appl.functor==INTERN_NC_AND)) {
        //_zone_print0("Here1");
        cond = quant->u.quant.cond ;
        t = NULL ;
        for (i = 0; i < cond->u.appl.count; ++i) {
            if (cond->u.appl.args[i]->type==EXP_APPL && cond->u.appl.args[i]->u.appl.functor==INTERN_OR) {
                term = i ;
                t = cond->u.appl.args[i] ;
                if (t->u.appl.count == 2) {
                    if (t->u.appl.args[0]->type==EXP_APPL &&
                        t->u.appl.args[0]->u.appl.functor==INTERN_NOT &&
                        t->u.appl.args[0]->u.appl.args[0]->type==EXP_APPL &&
                        (t->u.appl.args[0]->u.appl.args[0]->u.appl.functor==INTERN_EQUAL ||
                         t->u.appl.args[0]->u.appl.args[0]->u.appl.functor==INTERN_ORIENTED_RULE)) {
                        acc = t->u.appl.args[0]->u.appl.args[0];
                        if (acc->u.appl.args[0]->type==EXP_VAR &&
                            is_quant_var(acc->u.appl.args[0]->u.var,quant) &&
                            !_th_is_free_in(acc->u.appl.args[1],t->u.appl.args[0]->u.var)) {
                            var = acc->u.appl.args[0]->u.var;
                            val = acc->u.appl.args[1];
                            acc = t->u.appl.args[1];
                            break;
                        }
                        if (acc->u.appl.args[1]->type==EXP_VAR &&
                            is_quant_var(acc->u.appl.args[1]->u.var,quant) &&
                            !_th_is_free_in(acc->u.appl.args[0],t->u.appl.args[1]->u.var)) {
                            var = acc->u.appl.args[1]->u.var;
                            val = acc->u.appl.args[0];
                            acc = t->u.appl.args[1];
                            break;
                        }
                    }
                    if (t->u.appl.args[1]->type==EXP_APPL &&
                        t->u.appl.args[1]->u.appl.functor==INTERN_NOT &&
                        t->u.appl.args[1]->u.appl.args[0]->type==EXP_APPL &&
                        (t->u.appl.args[1]->u.appl.args[0]->u.appl.functor==INTERN_EQUAL ||
                         t->u.appl.args[1]->u.appl.args[0]->u.appl.functor==INTERN_ORIENTED_RULE)) {
                        acc = t->u.appl.args[1]->u.appl.args[0];
                        if (acc->u.appl.args[0]->type==EXP_VAR &&
                            is_quant_var(acc->u.appl.args[0]->u.var,quant) &&
                            !_th_is_free_in(acc->u.appl.args[1],t->u.appl.args[0]->u.var)) {
                            var = acc->u.appl.args[0]->u.var;
                            val = acc->u.appl.args[1];
                            acc = t->u.appl.args[0];
                            break;
                        }
                        if (acc->u.appl.args[1]->type==EXP_VAR &&
                            is_quant_var(acc->u.appl.args[1]->u.var,quant) &&
                            !_th_is_free_in(acc->u.appl.args[0],t->u.appl.args[1]->u.var)) {
                            var = acc->u.appl.args[1]->u.var;
                            val = acc->u.appl.args[0];
                            acc = t->u.appl.args[0];
                            break;
                        }
                    }
                }
            }
        }
        //_zone_print1("Here2 %d", t);
        if (i==cond->u.appl.count) return NULL ;
        args = ALLOCA(sizeof(struct _ex_intern *) * (cond->u.appl.count + 1)) ;
        args2 = ALLOCA(sizeof(struct _ex_intern *) * (cond->u.appl.count + 1)) ;
        for (i = 0; i < cond->u.appl.count; ++i) {
            args2[i] =  args[i] = cond->u.appl.args[i] ;
        }
        args[term] = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_EQUAL,_ex_intern_var(var),val));
        t = _ex_intern_quant(INTERN_SETQ,quant->u.quant.var_count,quant->u.quant.vars,quant->u.quant.exp,
                _ex_intern_appl_env(env,INTERN_AND,i,args));

        args2[term] = acc;
        vars = (unsigned *)ALLOCA(sizeof(unsigned) * t->u.quant.var_count);
        for (i = 0, j = 0; i < quant->u.quant.var_count; ++i) {
            if (quant->u.quant.vars[i] != var) {
                vars[j++] = quant->u.quant.vars[i];
            }
        }
        u = _th_new_unifier(REWRITE_SPACE);
        u = _th_add_pair(REWRITE_SPACE,u,var,val);
        acc = _ex_intern_appl2_env(env,INTERN_UNION,t,
                   _ex_intern_quant(INTERN_SETQ,quant->u.quant.var_count-1,vars,
                       _th_subst(env,u,quant->u.quant.exp),
                       _th_subst(env,u,_ex_intern_appl_env(env,INTERN_AND,cond->u.appl.count,args2))));
        return acc;
    }
    return NULL ;
}

struct _ex_intern *_th_simplify_setq(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *f, **args, *h;
	struct _ex_unifier *u;
	char *mark;
    int i, j, c, count;
    unsigned *vars, *qvars, *fv;

	//_zone_print1("Processing set %s\n", _th_print_exp(e)) ;
	if (e->u.quant.var_count==0) {
		//_zone_print0("case 1");
		return _ex_intern_appl3_env(env,INTERN_ITE,
			e->u.quant.cond,
			_ex_intern_appl1_env(env,INTERN_SET,e->u.quant.exp),
			_ex_intern_appl_env(env,INTERN_SET,0,NULL));
	}
	if (e->u.quant.cond==_ex_false) {
		return _ex_intern_appl_env(env,INTERN_SET,0,NULL);
	}
	f = distribute_or_quant(env,e) ;
	if (f != NULL) {
		return f ;
	}
	f = _th_remove_free_terms(env,e) ;
	if (f != NULL) {
		return f ;
	}
	f = _th_solve_term(env,e->u.quant.var_count,e->u.quant.vars,e->u.quant.cond);
	if (f) {
		//_zone_print0("case 4");
		return _ex_intern_quant(INTERN_SETQ,e->u.quant.var_count,e->u.quant.vars,e->u.quant.exp,f);
	}
	if (e->u.quant.cond->type==EXP_APPL) {
		switch (e->u.quant.cond->u.appl.functor) {
    		case INTERN_NC_AND:
	    		//_zone_print0("case 5");
		    	return _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,e->u.quant.vars,e->u.quant.exp,
			    	_ex_intern_appl_env(env,INTERN_AND,e->u.quant.cond->u.appl.count,e->u.quant.cond->u.appl.args)) ;
		    case INTERN_AND:
#ifdef XX
				mark = _th_alloc_mark(REWRITE_SPACE) ;
				u = find_equal(e->u.quant.var_count, e->u.quant.vars,
					e->u.quant.cond->u.appl.count,e->u.quant.cond->u.appl.args) ;
				if (u != NULL) {
					f = _th_subst(env,u,e->u.quant.cond) ;
					e = _ex_intern_quant(INTERN_SETQ,e->u.quant.var_count,e->u.quant.vars,_th_subst(env,u,e->u.quant.exp),f) ;
					_th_alloc_release(REWRITE_SPACE,mark) ;
					//_zone_print0("case 6");
					return e ;
				}
#endif
				f = _th_remove_equal_bound(env,e);
				if (f) return f;
				for (i = 0; i < e->u.quant.cond->u.appl.count; ++i) {
					f = _th_solve_term(env,e->u.quant.var_count,e->u.quant.vars,e->u.quant.cond->u.appl.args[i]);
					if (f != NULL) {
						//check_size(e->u.quant.cond->u.appl.count);
						args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.quant.cond->u.appl.count);
						for (j = 0; j < e->u.quant.cond->u.appl.count; ++j) {
							args[j] = e->u.quant.cond->u.appl.args[j];
						}
						args[i] = f;
						//_th_alloc_release(REWRITE_SPACE,mark) ;
						//_zone_print0("case 7");
						return _ex_intern_quant(INTERN_SETQ,e->u.quant.var_count,e->u.quant.vars,e->u.quant.exp, _th_flatten_top(env,_ex_intern_appl_env(env,INTERN_AND,e->u.quant.cond->u.appl.count,args)));
					}
				}
				//_th_alloc_release(REWRITE_SPACE,mark) ;
				break ;
		    case INTERN_OR:
			    //check_size(e->u.quant.cond->u.appl.count) ;
			    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.quant.cond->u.appl.count);
			    for (i = 0; i < e->u.quant.cond->u.appl.count; ++i) {
				    args[i] = _ex_intern_quant(INTERN_SETQ,e->u.quant.var_count,e->u.quant.vars,e->u.quant.exp,e->u.quant.cond->u.appl.args[i]) ;
				}
			    //_zone_print0("case 8");
		    	return _ex_intern_appl_env(env,INTERN_UNION,e->u.quant.cond->u.appl.count,args) ;
    		case INTERN_ORIENTED_RULE:
	    	case INTERN_EQUAL:
				if (e->u.quant.cond->u.appl.args[0]->type==EXP_VAR &&
					(e->u.quant.cond->u.appl.functor==INTERN_EQUAL ||
					e->u.quant.cond->u.appl.args[2]==_ex_true)) {
					for (i = 0; i < e->u.quant.var_count; ++i) {
						if (e->u.quant.cond->u.appl.args[0]->u.var==e->u.quant.vars[i]) {
							vars = _th_get_free_vars_leave_marked(e->u.quant.cond->u.appl.args[1],&c) ;
							if (_th_intern_get_data(e->u.quant.cond->u.appl.args[0]->u.var)) {
								for (i = 0; i < c; ++i) {
									_th_intern_set_data(vars[i],0) ;
								}
								goto cont_set ;
							}
							for (i = 0; i < c; ++i) {
								_th_intern_set_data(vars[i],0) ;
							}
							mark = _th_alloc_mark(REWRITE_SPACE) ;
							u = _th_new_unifier(REWRITE_SPACE) ;
							u = _th_add_pair(REWRITE_SPACE,u,e->u.quant.cond->u.appl.args[0]->u.var,
								e->u.quant.cond->u.appl.args[1]);
							e = _ex_intern_quant(INTERN_SETQ,e->u.quant.var_count,e->u.quant.vars,
								_th_subst(env,u,e->u.quant.exp), _ex_true) ;
							_th_alloc_release(REWRITE_SPACE,mark) ;
							//_zone_print0("case 9");
							return e ;
						}
					}
				} else if (e->u.quant.cond->u.appl.args[1]->type==EXP_VAR &&
					(e->u.quant.cond->u.appl.functor==INTERN_EQUAL ||
					e->u.quant.cond->u.appl.args[2]==_ex_true)) {
					for (i = 0; i < e->u.quant.var_count; ++i) {
						if (e->u.quant.cond->u.appl.args[1]->u.var==e->u.quant.vars[i]) {
							vars = _th_get_free_vars_leave_marked(e->u.quant.cond->u.appl.args[0],&c) ;
							if (_th_intern_get_data(e->u.quant.cond->u.appl.args[1]->u.var)) {
								for (i = 0; i < c; ++i) {
									_th_intern_set_data(vars[i],0) ;
								}
								goto cont_set ;
							}
							for (i = 0; i < c; ++i) {
								_th_intern_set_data(vars[i],0) ;
							}
							mark = _th_alloc_mark(REWRITE_SPACE) ;
							u = _th_new_unifier(REWRITE_SPACE) ;
							u = _th_add_pair(REWRITE_SPACE,u,e->u.quant.cond->u.appl.args[1]->u.var,
								e->u.quant.cond->u.appl.args[0]);
							e = _ex_intern_quant(INTERN_SETQ,e->u.quant.var_count,e->u.quant.vars,
								_th_subst(env,u,e->u.quant.exp), _ex_true) ;
							_th_alloc_release(REWRITE_SPACE,mark) ;
							return e ;
						}
					}
				}
				break ;
        }
   }
cont_set:
   vars = _th_get_free_vars_leave_marked(_ex_intern_appl2_env(env,INTERN_AND,e->u.quant.exp,e->u.quant.cond),&c) ;
   qvars = (unsigned *)ALLOCA(sizeof(unsigned) * e->u.quant.var_count);
   for (i = 0, j = 0; i < e->u.quant.var_count; ++i) {
	   if (_th_intern_get_data(e->u.quant.vars[i])) {
		   qvars[j++] = e->u.quant.vars[i] ;
	   }
   }
   for (i = 0; i < c; ++i) {
	   _th_intern_set_data(vars[i],0) ;
   }
   if (e->u.quant.var_count==j) {
	   f = NULL ;
   } else {
	   f = _ex_intern_quant(INTERN_SETQ,j,qvars,e->u.quant.exp,e->u.quant.cond) ;
   }
   if (f==NULL) {
	   for (i = 0; i < c; ++i) {
		   _th_intern_set_data(vars[i], 0);
	   }
	   if (e->u.quant.cond->type==EXP_APPL && e->u.quant.cond->u.appl.functor==INTERN_AND) {
		   for (i = 0; i < e->u.quant.cond->u.appl.count; ++i) {
			   vars = _th_get_free_vars_leave_marked(e->u.quant.cond->u.appl.args[i],&c);
			   for (j = 0; j < e->u.quant.var_count; ++j) {
				   goto cont_set5;
			   }
			   for (i = 0; i < c; ++i) {
				   _th_intern_set_data(vars[i], 0);
			   }
		   }
		   return _ex_intern_appl3_env(env,INTERN_ITE,
			   e->u.quant.cond->u.appl.args[i],
			   e,
			   _ex_intern_appl_env(env,INTERN_SET,0,NULL));
cont_set5:;
		  for (i = 0; i < c; ++i) {
			  _th_intern_set_data(vars[i], 0);
		  }
      }
	   if (e->u.quant.cond->type==EXP_APPL && e->u.quant.cond->u.appl.functor==INTERN_MEMBER &&
		   e->u.quant.cond->u.appl.args[0]->type==EXP_VAR && e->u.quant.cond->u.appl.args[0]->u.var==e->u.quant.vars[0] &&
		   e->u.quant.var_count==1) {
		   if (e->u.quant.exp->type==EXP_VAR && e->u.quant.exp->u.var==e->u.quant.vars[0]) {
			   return e->u.quant.cond->u.appl.args[1] ;
		   } else if (_th_is_free_in(e->u.quant.exp,e->u.quant.vars[0]) &&
			   !_th_is_free_in(e->u.quant.cond->u.appl.args[1],e->u.quant.vars[0])) {
			   return _ex_intern_appl2_env(env,INTERN_MAP_SET,
				   _ex_intern_quant(INTERN_LAMBDA,1,e->u.quant.vars,e->u.quant.exp,_ex_true),
				   e->u.quant.cond->u.appl.args[1]);
		   } else {
			   goto cont_set2 ;
		   }
	   } else if (e->u.quant.cond->type==EXP_APPL && e->u.quant.cond->u.appl.functor==INTERN_AND) {
		   struct _ex_intern **args ;
		   struct _ex_intern *f ;
		   int member_term = -1 ;
		   int member_var = -1 ;
		   for (i = 0; i < e->u.quant.cond->u.appl.count; ++i) {
			   f = e->u.quant.cond->u.appl.args[i] ;
			   if (f->type==EXP_APPL && f->u.appl.functor==INTERN_MEMBER && f->u.appl.args[0]->type==EXP_VAR) {
				   //_zone_print0("Found_member") ;
				   for (j = 0; j < e->u.quant.var_count; ++j) {
					   if (f->u.appl.args[0]->u.var==e->u.quant.vars[j]) {
						   member_var = j ;
						   break ;
					   }
				   }
				   if (member_var != -1) {
					   int count ;
					   unsigned *fv = _th_get_free_vars(f->u.appl.args[1], &count) ;
					   for (j = 0; j < count; ++j) {
						   if (fv[j] != e->u.quant.vars[member_var]) {
							   int k ;
							   for (k = 0; k < e->u.quant.var_count; ++k) {
								   if (fv[j]==e->u.quant.vars[k]) {
									   goto cont_set3 ;
								   }
							   }
						   }
					   }
					   member_term = i ;
					   break ;
cont_set3: ;
				   }
			   }
		   }
		   fv = _th_get_free_vars(e->u.quant.exp, &count) ;
		   for (j = 0; j < count; ++j) {
			   if (fv[j] != e->u.quant.vars[member_var]) {
				   int k ;
				   for (k = 0; k < e->u.quant.var_count; ++k) {
					   if (fv[j]==e->u.quant.vars[k]) {
						   goto cont_set2 ;
					   }
				   }
			   }
		   }
		   if (member_term==-1) goto cont_set2 ;
		   args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (e->u.quant.cond->u.appl.count - 1)) ;
		   for (i = 0, j = 0; i < e->u.quant.cond->u.appl.count; ++i) {
			   if (i != member_term) args[j++] = e->u.quant.cond->u.appl.args[i] ;
		   }
		   fv = (unsigned *)ALLOCA(sizeof(unsigned) * (e->u.quant.var_count - 1)) ;
		   for (i = 0, j = 0; i < e->u.quant.var_count; ++i) {
			   if (i != member_var) fv[j++] = e->u.quant.vars[i] ;
		   }
		   h = _ex_intern_quant(INTERN_LAMBDA,1,&e->u.quant.vars[member_var],_ex_intern_quant(INTERN_EXISTS,e->u.quant.var_count-1,fv,_ex_intern_appl_env(env,INTERN_AND,e->u.quant.cond->u.appl.count-1,args),_ex_true),_ex_true) ;
		   h = _ex_intern_appl2_env(env,INTERN_FILTER_SET,h,e->u.quant.cond->u.appl.args[member_term]->u.appl.args[1]) ;
		   if (e->u.quant.exp->type==EXP_VAR && e->u.quant.exp->u.var== e->u.quant.vars[member_var]) {
			   //_zone_print0("case 15");
			   return h ;
		   } else {
			   //_zone_print0("case 16");
			   return _ex_intern_appl2_env(env,INTERN_MAP_SET,_ex_intern_quant(INTERN_LAMBDA,1,e->u.quant.vars+member_var,e->u.quant.exp,_ex_true),h) ;
		   }
	   }
	   f = e ;
   }
cont_set2:
   return f ;
}

void _th_add_set_rules(int s, struct env *env)
{
    _th_add_property(env,_th_parse(env,"(+> (-> s (Set) (True)) (False) (and (chooseContextRule (QUOTE (-> (not (-> (filterSet f s) (Set) (True))) (True) (True))))))")) ;
    _th_add_property(env,_th_parse(env,"(=> (-> (mapSet f s) r c) (-> (-> s (Set) (True)) (-> r (Set) (True)) (True)) (and (compatible_prec  s r) (compatible_prec s c)))")) ;
    _th_add_property(env,_th_parse(env,"(=> (-> (-> (filterSet f s) (Set) (True)) (False) (True)) (+> (subset s b) (False) (and (nestingLimit 1) (== (filterSet f b) (Set)))) (True))")) ;
    _th_add_property(env,_th_parse(env,"(=> (-> (not (-> (filterSet f s) (Set) (True))) (True) (True)) (+> (subset s b) (False) (and (nestingLimit 1) (== (filterSet f b) (Set)))) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (ALL (x) (|| (not (member x a)) (not (member x b)))) (separate a b) (True))")) ;
    _th_add_property(env,_th_parse(env,"(+> (not (subset (Set a) b)) (separate (Set a) b) (True))")) ;

    _th_add_property(env,_th_parse(env,"(-> (member a (union b c)) (|| (member a b) (member a c)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (member a (intersect b c)) (&& (member a b) (member a c)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (member a (difference b c)) (&& (member a b) (not (member a c))) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (subset a (intersect b c)) (&& (subset a b) (subset a c)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (subset a (difference b c)) (&& (subset a b) (== (intersect a c) (Set))) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (intersect a (union b c)) (union (intersect a b) (intersect a c)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (difference a (union b c)) (intersect (difference a b) (difference a c)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (difference (union a b) c) (union (difference a c) (difference b c)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (difference a (intersect b c)) (union (difference a b) (difference a c)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (difference (intersect a b) c) (intersect (difference a c) b) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (intersect a (difference b c)) (Set) (subset a c))")) ;
    _th_add_property(env,_th_parse(env,"(-> (union (difference a b) (difference b1 c)) (difference a c) (and (== b b1) (subset c b) (subset b a)))")) ;
    _th_add_property(env,_th_parse(env,"(-> (difference a b) (Set) (subset a b))")) ;
    _th_add_property(env,_th_parse(env,"(-> (intersect a b) a (subset a b))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (union a b) b (andq (useContext \"unionSubset\") (blockContext \"unionSubset\") (notl (match a (union x y))) (subset a b)))")) ;
    _th_add_property(env,_th_parse(env,"(-> (difference a b) a (separate a b))")) ;
    _th_add_property(env,_th_parse(env,"(-> (intersect a b) (Set) (separate a b))")) ;
    _th_add_property(env,_th_parse(env,"(-> (subset (intersect a b) a1) (True) (== a a1))")) ;
    _th_add_property(env,_th_parse(env,"(-> (subset a (union a1 b)) (True) (== a a1))")) ;
    _th_add_property(env,_th_parse(env,"(-> (subset a a1) (True) (== (normal a) (normal a1)))")) ;
    _th_add_property(env,_th_parse(env,"(-> (subset (difference a b) a1) (True) (== (normal a) (normal a1)))")) ;
    _th_add_property(env,_th_parse(env,"(-> (difference a a1) (Set) (== (normal a) (normal a1)))")) ;
    _th_add_property(env,_th_parse(env,"(= (intersect a (difference b c)) (intersect (difference a c) b) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (difference (difference a b) c) (difference a (union b c)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (difference a (difference b c)) (union (difference a b) (intersect a b c)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (union a (difference b c)) (union a b) (subset c a))")) ;
    _th_add_property(env,_th_parse(env,"(-> (union a (intersect (difference b c) d)) (union a (intersect b d)) (subset c a))")) ;
    _th_add_property(env,_th_parse(env,"(-> (subset (union a b) c) (&& (subset a c) (subset b c)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (subset a (union b c)) (True) (subset a b))")) ;
    _th_add_property(env,_th_parse(env,"(-> (subset (difference a b) (difference a1 c)) (True) (and (== a a1) (subset c a)))")) ;
    _th_add_property(env,_th_parse(env,"(-> (subset (difference a b) c) (True) (subset a c))")) ;
    _th_add_property(env,_th_parse(env,"(-> (subset (intersect a b) c) (True) (subset a c))")) ;
    _th_add_property(env,_th_parse(env,"(-> (== (union (Set a1) b) (union (Set a) c)) (== c b) (and (excludeSet \"unionEqual\") (== a a1) (not (member a b)) (not (member a c))))")) ;
    _th_add_property(env,_th_parse(env,"(-> (&& (= a b c) (= b1 a1 c1) d) (&& (= a b c) d) (and (== a a1) (b b1) (c c1)))")) ;
    _th_add_property(env,_th_parse(env,"(-> (priority x (priority y r)) (priority y r) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (&& (|| a b) c) (|| (&& a c) (&& b c)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (listset (Cons a b)) (union (Set a) b) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (listset (Nil)) (Set) (True))")) ;

    _th_add_property(env,_th_parse(env,"(--> (== (union a b) c) (&& (subset a c) (subset b c)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(--> (-> (union a b) c (True)) (&& (subset a c) (subset b c)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(--> (-> (union a (Set b)) c (True)) (-> a (difference c (Set b)) (True)) (andq (compatible_prec a c) (== (intersect a (Set b)) (Set))))")) ;
    //_th_add_property(env,_th_parse(env,"(--> (-> c (union a b) (True)) (&& (subset a b) (subset a c)) (True))")) ;

    //_th_add_property(env,_th_parse(env,"(=> (-> (member a b) (True) (True)) (-> (member a d) (True) (True)) (andq (choose r (getContextRules)) (match r (-> (subset b d) (True) (True)))))")) ;
    _th_add_property(env,_th_parse(env,"(+> (member a b) (False) (andq (inContext \"mainContext\") (useContext \"backchain\") (not (member a b))))")) ;
    _th_add_property(env,_th_parse(env,"(+> (member a b) (True) (andq (inContext \"mainContext\") (useContext \"backchain\") (member a b)))")) ;
    //_th_add_property(env,_th_parse(env,"(--> (-> (member a b) (True) (True)) (-> (member a d) (True) (True)) (fireOnChange (QUOTE (subset b xxx)) (andq (choose r (getContextRules)) (match r (-> (subset b d) (True) (True))))))")) ;
    //_th_add_property(env,_th_parse(env,"(--> (-> (member a d) (False) (True)) (-> (member a b) (False) (True)) (fireOnChange (QUOTE (subset xxx b)) (andq (choose r (getContextRules)) (match r (-> (subset b d) (True) (True))))))")) ;
    _th_add_property(env,_th_parse(env,"(--> (-> (member a b) (True) (True)) (-> (member a d) (True) (True)) (fireOnChange (QUOTE (subset b xxx)) (andq (chooseContextRule (-> (subset b d) (True) (True))))))")) ;
    _th_add_property(env,_th_parse(env,"(--> (-> (member a d) (False) (True)) (-> (member a b) (False) (True)) (fireOnChange (QUOTE (subset xxx b)) (andq (chooseContextRule (-> (subset b d) (True) (True))))))")) ;
    //_th_add_property(env,_th_parse(env,"(--> (member a b) (member a d) (fireOnChange (QUOTE (subset b xxx)) (andq (choose r (getContextRules)) (match r (-> (subset b d) (True) (True))))))")) ;
    //_th_add_property(env,_th_parse(env,"(--> (not (member a d)) (not (member a b)) (fireOnChange (QUOTE (subset xxx b)) (andq (choose r (getContextRules)) (match r (-> (subset b d) (True) (True))))))")) ;
    _th_add_property(env,_th_parse(env,"(--> (member a b) (member a d) (fireOnChange (QUOTE (subset b xxx)) (andq (chooseContextRule (-> (subset b d) (True) (True))))))")) ;
    _th_add_property(env,_th_parse(env,"(--> (not (member a d)) (not (member a b)) (fireOnChange (QUOTE (subset xxx b)) (andq (chooseContextRule (-> (subset b d) (True) (True))))))")) ;
    _th_add_property(env,_th_parse(env,"(--> (member a b) (member a d) (fireOnChange (QUOTE (subset b xxx)) (andq (choose r (getTerms)) (match r (subset b d)))))")) ;
    _th_add_property(env,_th_parse(env,"(--> (not (member a d)) (not (member a b)) (fireOnChange (QUOTE (subset xxx b)) (andq (choose r (getTerms)) (match r (subset b d)))))")) ;
    //_th_add_property(env,_th_parse(env,"(= (member a d) (True) (andq (choose r (getContextRules)) (match r (-> (subset b d) (True) (True))) (member a b)))")) ;
    //_th_add_property(env,_th_parse(env,"(= (member a b) (False) (andq (choose r (getContextRules)) (match r (-> (subset b d) (True) (True))) (not (member a d))))")) ;
    _th_add_property(env,_th_parse(env,"(= (member a d) (True) (andq (chooseContextRule (-> (subset b d) (True) (True))) (member a b)))")) ;
    _th_add_property(env,_th_parse(env,"(= (member a b) (False) (andq (chooseContextRule (-> (subset b d) (True) (True))) (not (member a d))))")) ;
    _th_add_property(env,_th_parse(env,"(= (member a d) (True) (andq (chooseContextRule (-> (union b d) c (True))) (not (member a b)) (member a c)))")) ;
    //_th_add_property(env,_th_parse(env,"(= (member a d) (True) (andq (choose r (getContextRules)) (match r (= (union b c) d (True))) (member a b)))")) ;
    //_th_add_property(env,_th_parse(env,"(= (member a d) (True) (andq (choose r (getContextRules)) (match r (= d (union b c) (True))) (member a b)))")) ;
    //_th_add_property(env,_th_parse(env,"(= (member a d) (True) (andq (choose r (getContextRules)) (match r (== (union b c) d)) (member a b)))")) ;
    //_th_add_property(env,_th_parse(env,"(= (member a d) (True) (andq (choose r (getContextRules)) (match r (-> (union b c) d)) (member a b)))")) ;
    //_th_add_property(env,_th_parse(env,"(= (member a d) (True) (andq (choose r (getContextRules)) (match r (-> d (union b c))) (member a b)))")) ;
    //_th_add_property(env,_th_parse(env,"(= (member a d) (True) (andq (choose r (getContextRules)) (match r (== d b)) (member a b)))")) ;
    //_th_add_property(env,_th_parse(env,"(= (member a d) (True) (andq (choose r (getContextRules)) (match r (-> d b (True))) (member a b)))")) ;
    //_th_add_property(env,_th_parse(env,"(= (member a d) (True) (andq (choose r (getContextRules)) (match r (-> b d (True))) (member a b)))")) ;
    //_th_add_property(env,_th_parse(env,"(= (member a d) (True) (andq (choose r (getContextRules)) (match r (-> d b c)) (== b d) (member a b)))")) ;
    //_th_add_property(env,_th_parse(env,"(= (member a d) (True) (andq (choose r (getContextRules)) (match r (-> b d c)) (== b d) (member a b)))")) ;

    _th_add_property(env,_th_parse(env,"(-> (-> (mapSet f s) (Set) (True)) (-> s (Set) (True)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(=> (-> (member x s) (True) c) (-> (== s (Set)) (False) c) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(=> (-> (member x s) (True) c) (+> (== (filterSet f s) (Set)) (False) (and (apply f x) c)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(=> (-> (mapSet f x) y c) (+> (-> (filterSet h x) (Set) (True)) (-> (filterSet (uncompose h f) y) (Set) (True)) (and (rewritable (QUOTE (uncompose h f))) c)) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(=> (-> (subset a b) (True) c) (= (member x b) (True) (andq (choose xx (Set (markVars x))) (chooseContextRule (-> (member xx a) (True) (True))) c)) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(=> (-> (subset a b) (True) c) (= (member x b) (True) (andq (choose xx (Set (markVars x))) (choose r (getContextRules)) (match r (-> (member xx a) (True) (True))) c)) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(=> (-> (subset a b) (True) c) (-> (== (filterSet f b) (Set)) (False) (and c (not (== (filterSet f a) (Set))))) (compatible_prec b a))")) ;
    _th_add_property(env,_th_parse(env,"(-> (filterSet f (filterSet g s)) (filterSet (lambda x (&& (apply f x) (apply g x))) s) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (filterSet f (difference a b)) (difference (filterSet f a) (filterSet f b)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (filterSet f (union a b)) (union (filterSet f a) (filterSet f b)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (filterSet f (intersect a b)) (intersect (filterSet f a) (filterSet f b)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (mapSet f (difference a b)) (difference (mapSet f a) (mapSet f b)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (mapSet f (union a b)) (union (mapSet f a) (mapSet f b)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (mapSet f (intersect a b)) (intersect (mapSet f a) (mapSet f b)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (-> (union a b) (Set) (True)) (&& (== a (Set)) (== b (Set))) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (== (union a b) (Set)) (&& (== a (Set)) (== b (Set))) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (-> (intersect a b) (Set) (True)) (separate a b) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (== (intersect a b) (Set)) (separate a b) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (-> (difference a b) (Set) (True)) (subset a b) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (== (difference a b) (Set)) (subset a b) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (separate a (union b c)) (&& (separate a b) (separate a c)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (separate a (intersect b c)) (|| (separate a b) (separate a c)) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (separate a (difference b c)) (True) (subset a c))")) ;
    _th_add_property(env,_th_parse(env,"(-> (filterSet (lambda x (== x c)) s) (case (member c s) (True) (Set c) (False) (Set)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (filterSet (lambda x (True)) s) s (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (filterSet (lambda x (False)) s) (Set) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (filterSet (lambda x (|| a_ b_)) s) (union (filterSet (lambda x a_) s) (filterSet (lambda x b_) s)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (filterSet (lambda x (&& a_ b_)) s) (intersect (filterSet (lambda x a_) s) (filterSet (lambda x b_) s)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (filterSet (lambda x (not a_)) s) (difference s (filterSet (lambda x a_) s)) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (mapSet (lambda x c) s) (Set c) (True))")) ;
    _th_add_property(env,_th_parse(env,"(-> (mapSet (lambda x x) s) x (True))")) ;
}

