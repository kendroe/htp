/*
 * quant.c
 *
 * Routines for simplifying quantifier expressions (all and exists)
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"

static int find_rewrite(int var_count, unsigned *vars, int count, struct _ex_intern *args[])
{
    int i ;
    int r;

    for (i = 0; i < var_count; ++i) {
        _th_intern_set_data(vars[i],1) ;
    }

    r = 0 ;
    for (i = 0; i < count; ++i) {
        if (args[i]->type==EXP_APPL && args[i]->u.appl.functor==INTERN_ORIENTED_RULE) {
            if (args[i]->u.appl.args[0]->type==EXP_VAR &&
                _th_intern_get_data(args[i]->u.appl.args[0]->u.var)) {
                r = i+1 ;
                break ;
            }
        }
    }

    for (i = 0; i < var_count; ++i) {
        _th_intern_set_data(vars[i],0) ;
    }

    return r ;
}

struct _ex_intern *_th_simplify_exists(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *f, **args;
    int i, j, c;
    unsigned *vars;
    unsigned *qvars;

	if (e->u.quant.var_count==0) return e->u.quant.exp ;
	if (e->u.quant.exp==_ex_true) return _ex_true ;
	if (e->u.quant.exp->type==EXP_APPL) {
		switch (e->u.quant.exp->u.appl.functor) {
		case INTERN_AND:
#ifdef XX
			mark = _th_alloc_mark(REWRITE_SPACE) ;
			u = find_equal(e->u.quant.var_count, e->u.quant.vars,
				e->u.quant.exp->u.appl.count,e->u.quant.exp->u.appl.args) ;
			if (u != NULL) {
				f = _th_subst(env,u,e->u.quant.exp) ;
				e = _ex_intern_quant(INTERN_EXISTS,e->u.quant.var_count,e->u.quant.vars,f,e->u.quant.cond) ;
				_th_alloc_release(REWRITE_SPACE,mark) ;
				return e ;
			}
#endif
			f = _th_remove_equal_bound(env,e);
			if (f) return f;
			j = find_rewrite(e->u.quant.var_count, e->u.quant.vars,
				e->u.quant.exp->u.appl.count,e->u.quant.exp->u.appl.args) ;
			if (j) {
				struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.quant.exp->u.appl.count) ;
				for (i = 0; i < e->u.quant.exp->u.appl.count; ++i) {
					args[i] = e->u.quant.exp->u.appl.args[i] ;
				}
				args[j-1] = _ex_true ;
				e = _ex_intern_quant(INTERN_EXISTS,e->u.quant.var_count,e->u.quant.vars,
					_ex_intern_appl_env(env,INTERN_AND,i,args),e->u.quant.cond) ;
				//_th_alloc_release(REWRITE_SPACE,mark) ;
				return e ;
			}
			goto cont_exists ;
		case INTERN_NOT:
			//check_size(1) ;
			return _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_quant(INTERN_ALL,e->u.quant.var_count,e->u.quant.vars,e->u.quant.exp->u.appl.args[0],_ex_true));
			//return _ex_intern_appl_env(env,INTERN_NOT,1,args) ;
		case INTERN_OR:
			//check_size(e->u.quant.exp->u.appl.count) ;
			args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
			for (i = 0; i < e->u.quant.exp->u.appl.count; ++i) {
				args[i] = _ex_intern_quant(INTERN_EXISTS,e->u.quant.var_count,e->u.quant.vars,e->u.quant.exp->u.appl.args[i],e->u.quant.cond) ;
			}
			return _ex_intern_appl_env(env,INTERN_OR,e->u.quant.exp->u.appl.count,args) ;
			
		}
	}
cont_exists:
	vars = _th_get_free_vars_leave_marked(e->u.quant.exp,&c) ;
	qvars = (unsigned *)ALLOCA(sizeof(unsigned) * e->u.quant.var_count);
	for (i = 0, j = 0; i < e->u.quant.var_count; ++i) {
		if (_th_intern_get_data(e->u.quant.vars[i])) {
			qvars[j++] = e->u.quant.vars[i] ;
		}
	}
	if (e->u.quant.var_count==j) {
		f = NULL ;
	} else {
		f = _ex_intern_quant(INTERN_EXISTS,j,qvars,e->u.quant.exp,e->u.quant.cond) ;
	}
	for (i = 0; i < c; ++i) {
		_th_intern_set_data(vars[i],0) ;
	}
#ifdef SET_CONV
	if (f==NULL) {
		struct _ex_intern **args ;
		args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.quant.var_count) ;
		for (i = 0; i < e->u.quant.var_count; ++i) {
			args[i] = _ex_intern_var(e->u.quant.vars[i]) ;
		}
		e = _ex_intern_quant(INTERN_SETQ,e->u.quant.var_count,e->u.quant.vars,_ex_intern_appl_env(env,INTERN_T,e->u.quant.var_count,args),e->u.quant.exp) ;
		e = _ex_intern_appl2_env(env,INTERN_EQUAL,e,_ex_intern_appl_env(env,INTERN_SET,0,0)) ;
		f = _ex_intern_appl1_env(env,INTERN_NOT,e) ;
	}
#endif
	return f ;
}

struct _ex_intern *_th_simplify_all(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern **args;
	int i, j, c;
	struct _ex_unifier *u;
    unsigned *vars, *qvars;
	char *mark;

	if (e->u.quant.exp==_ex_true) {
		return _ex_true ;
	} else if (e->u.quant.cond==_ex_false) {
		return _ex_false ;
	} else if (e->u.quant.var_count==0) {
		//check_size(2) ;
		args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * 2);
		args[0] = e->u.quant.cond ;
		args[0] = _ex_intern_appl_env(env,INTERN_NOT,1,args) ;
		args[1] = e->u.quant.exp ;
		return _ex_intern_appl_env(env,INTERN_OR,2,args) ;
	}
	if (e->u.quant.exp->type==EXP_APPL) {
		if (e->u.quant.exp->u.appl.functor==INTERN_NOT) {
			//check_size(2) ;
			args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * 2);
			args[0] = e->u.quant.cond ;
			args[0] = _ex_intern_appl_env(env,INTERN_NOT,1,args) ;
			args[1] = e->u.quant.exp->u.appl.args[0] ;
			args[0] = _ex_intern_quant(INTERN_EXISTS,e->u.quant.var_count,e->u.quant.vars,_ex_intern_appl_env(env,INTERN_OR,2,args),_ex_true) ;
			return _ex_intern_appl_env(env,INTERN_NOT,1,args) ;
		} else if (e->u.quant.exp->u.appl.functor==INTERN_AND) {
			//check_size(e->u.quant.exp->u.appl.count) ;
			args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
			for (i = 0; i < e->u.quant.exp->u.appl.count; ++i) {
				args[i] = _ex_intern_quant(INTERN_ALL,e->u.quant.var_count,e->u.quant.vars,e->u.quant.exp->u.appl.args[i],e->u.quant.cond) ;
			}
			return _ex_intern_appl_env(env,INTERN_AND,e->u.quant.exp->u.appl.count,args) ;
		}
	}
	if (e->u.quant.cond->type==EXP_APPL) {
		switch (e->u.quant.cond->u.appl.functor) {
		case INTERN_AND:
#ifdef XX
			mark = _th_alloc_mark(REWRITE_SPACE) ;
			u = find_equal(e->u.quant.var_count, e->u.quant.vars,
				e->u.quant.cond->u.appl.count,e->u.quant.cond->u.appl.args) ;
			if (u != NULL) {
				f = _th_subst(env,u,e->u.quant.exp) ;
				e = _ex_intern_quant(INTERN_ALL,e->u.quant.var_count,e->u.quant.vars,f,_th_subst(env,u,e->u.quant.cond)) ;
				_th_alloc_release(REWRITE_SPACE,mark) ;
				return e ;
			}
#endif
			return _th_remove_equal_bound(env,e);
		case INTERN_EQUAL:
			if (e->u.quant.cond->u.appl.args[0]->type==EXP_VAR) {
				for (i = 0; i < e->u.quant.var_count; ++i) {
					if (e->u.quant.cond->u.appl.args[0]->u.var==e->u.quant.vars[i]) {
						vars = _th_get_free_vars_leave_marked(e->u.quant.cond->u.appl.args[1],&c) ;
						if (_th_intern_get_data(e->u.quant.cond->u.appl.args[0]->u.var)) {
							for (i = 0; i < c; ++i) {
								_th_intern_set_data(vars[i],0) ;
							}
							goto cont;
						}
						for (i = 0; i < c; ++i) {
							_th_intern_set_data(vars[i],0) ;
						}
						mark = _th_alloc_mark(REWRITE_SPACE) ;
						u = _th_new_unifier(REWRITE_SPACE) ;
						u = _th_add_pair(REWRITE_SPACE,u,e->u.quant.cond->u.appl.args[0]->u.var,
							e->u.quant.cond->u.appl.args[1]);
						e = _ex_intern_quant(INTERN_ALL,e->u.quant.var_count,e->u.quant.vars,
							_th_subst(env,u,e->u.quant.exp), _ex_true) ;
						_th_alloc_release(REWRITE_SPACE,mark) ;
						return e ;
					}
				}
			} else if (e->u.quant.cond->u.appl.args[1]->type==EXP_VAR) {
				for (i = 0; i < e->u.quant.var_count; ++i) {
					if (e->u.quant.cond->u.appl.args[1]->u.var==e->u.quant.vars[i]) {
						vars = _th_get_free_vars_leave_marked(e->u.quant.cond->u.appl.args[0],&c) ;
						if (_th_intern_get_data(e->u.quant.cond->u.appl.args[1]->u.var)) {
							for (i = 0; i < c; ++i) {
								_th_intern_set_data(vars[i],0) ;
							}
							goto cont ;
						}
						for (i = 0; i < c; ++i) {
							_th_intern_set_data(vars[i],0) ;
						}
						mark = _th_alloc_mark(REWRITE_SPACE) ;
						u = _th_new_unifier(REWRITE_SPACE) ;
						u = _th_add_pair(REWRITE_SPACE,u,e->u.quant.cond->u.appl.args[1]->u.var,
							e->u.quant.cond->u.appl.args[0]);
						e = _ex_intern_quant(INTERN_ALL,e->u.quant.var_count,e->u.quant.vars,
							_th_subst(env,u,e->u.quant.exp), _ex_true) ;
						_th_alloc_release(REWRITE_SPACE,mark) ;
						return e ;
					}
				}
			}
			break ;
		}
	}
cont:
	_th_get_free_vars_leave_marked(e->u.quant.exp,&c) ;
	vars = _th_cont_free_vars_leave_marked(e->u.quant.cond,&c) ;
	qvars = (unsigned *)ALLOCA(sizeof(unsigned) * e->u.quant.var_count);
	for (i = 0, j = 0; i < e->u.quant.var_count; ++i) {
		if (_th_intern_get_data(e->u.quant.vars[i])) {
			qvars[j++] = e->u.quant.vars[i] ;
		}
	}
	if (e->u.quant.var_count==j) {
		e = NULL ;
	} else {
		e = _ex_intern_quant(INTERN_ALL,j,qvars,e->u.quant.exp,e->u.quant.cond) ;
	}
	for (i = 0; i < c; ++i) {
		_th_intern_set_data(vars[i],0) ;
	}
	return e ;
}
