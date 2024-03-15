/*
 * lambda.c
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

struct _ex_intern *_th_simplify_apply(struct env *env, struct _ex_intern *e)
{
	char *mark;
	struct _ex_unifier *u;

	if (e->u.appl.args[0]->type==EXP_QUANT &&
		e->u.appl.args[0]->u.quant.quant==INTERN_LAMBDA) {
		mark = _th_alloc_mark(REWRITE_SPACE) ;
		u = _th_new_unifier(REWRITE_SPACE) ;
		u = _th_add_pair(REWRITE_SPACE,u,e->u.appl.args[0]->u.quant.vars[0],e->u.appl.args[1]) ;
		e = _th_subst(env,u,e->u.appl.args[0]->u.quant.exp) ;
		_th_alloc_release(REWRITE_SPACE,mark) ;
		return e ;
	}
	return NULL ;
}

struct _ex_intern *_th_simplify_lambda(struct env *env, struct _ex_intern *e)
{
	unsigned *vars;
	int c, i;

	if (e->u.quant.exp->type==EXP_APPL &&
		e->u.quant.exp->u.appl.functor==INTERN_APPLY &&
		e->u.quant.exp->u.appl.args[1]->type==EXP_VAR &&
		e->u.quant.exp->u.appl.args[1]->u.var==e->u.quant.vars[0]) {
		vars = _th_get_free_vars_leave_marked(e->u.quant.exp->u.appl.args[0],&c) ;
		if (_th_intern_get_data(e->u.quant.vars[0])) {
			e = NULL ;
		} else {
			e = e->u.quant.exp->u.appl.args[0] ;
		}
		for (i = 0; i < c; ++i) {
			_th_intern_set_data(vars[i],0) ;
		}
		return e ;
	}
	return NULL;
}

