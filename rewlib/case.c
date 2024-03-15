/*
 * case.c
 *
 * Routines for simplifying case expressions
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"

static struct _ex_unifier *name_away_from_marks(struct _ex_unifier *u, struct _ex_intern *e)
{
    char name[20], *d ;
    int i ;
    unsigned v, c ;

    switch (e->type) {
        case EXP_VAR:
            if (_th_intern_get_data(e->u.var)==0) return u ;
            d = _th_intern_decode(e->u.var) ;
            i = 0 ;
            do {
                sprintf(name,"%s%d", d, i) ;
                v = _th_intern(name) ;
                c = _th_intern_get_data(v) ;
                ++i ;
            } while (c != 0) ;
            u = _th_add_pair(REWRITE_SPACE,u,e->u.var,_ex_intern_var(v)) ;
            _th_intern_set_data(v,1) ;
            break ;
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                u = name_away_from_marks(u,e->u.appl.args[i]) ;
            }
            break ;
    }
    return u ;
}

static int find_smallest(struct env *env, struct _ex_intern *e)
{
    int i;
    int index ;
    struct _ex_intern *f ;
    unsigned v ;

    index = -1;
    for (i = 0; i < e->u.case_stmt.count; ++i) {
        f = e->u.case_stmt.args[i*2+1] ;
        if (f->type==EXP_CASE &&
            f->u.case_stmt.args[0]->type==EXP_APPL &&
            _th_is_constructor(env,f->u.case_stmt.args[0]->u.appl.functor)) {
            if (((unsigned)f->u.case_stmt.exp) < ((unsigned)e->u.case_stmt.exp)) {
                if (index==-1 || ((unsigned)f->u.case_stmt.exp) < v) {
                    v = ((unsigned)f->u.case_stmt.exp) ;
                    index = i ;
                }
            }
        }
    }
    return index ;
}

static struct _ex_intern *back[MAX_ARGS] ;
static struct _ex_intern *back_exp ;

static void process_back(struct env *env, struct _ex_intern *back, struct _ex_intern *pat)
{
    char *mark ;
    struct _ex_unifier *u ;
    int i ;
    struct _ex_intern *args[2] ;

    /*printf("Processing back %s\n", _th_print_exp(back)) ;
    //printf("    pat: %s\n", _th_print_exp(pat)) ;
    //printf("    back_exp: %s\n", _th_print_exp(back_exp)) ;*/
    switch(pat->type) {
        case EXP_VAR:
            mark = _th_alloc_mark(REWRITE_SPACE) ;
            u = _th_new_unifier(REWRITE_SPACE) ;
            u = _th_add_pair(REWRITE_SPACE,u,pat->u.var,back) ;
            back_exp = _th_subst(env,u,back_exp) ;
            _th_alloc_release(REWRITE_SPACE,mark) ;
            break;
        case EXP_APPL:
            switch (back->type) {
                case EXP_VAR:
                    args[0] = pat ;
                    args[1] = back_exp ;
                    /*printf("pat: %s\n", _th_print_exp(pat)) ;
                    //printf("back_exp: %s\n", _th_print_exp(back_exp)) ;*/
                    back_exp = _ex_intern_case(back,1,args) ;
                    /*printf("case: %s\n", _th_print_exp(back_exp)) ;*/
                    break ;
                case EXP_APPL:
                    for (i = 0; i < back->u.appl.count; ++i) {
                        process_back(env,back->u.appl.args[i],pat->u.appl.args[i]) ;
                    }
                    break;
            }
    }
}

static struct _ex_intern *build_case(struct env *env,int pos,struct _ex_intern *e,int count, struct _ex_intern *args[])
{
    int i, j, k ;
    struct _ex_intern *args2[MAX_ARGS], *args3[MAX_ARGS] ;
    int count3 ;

    /*printf("Building %d\n", pos) ;*/
    if (pos==args[0]->u.appl.count) {
        back_exp = args[1] ;
        for (i = 0; i < pos-1; ++i) {
            /*printf("i = %d\n", i) ;*/
            process_back(env,back[i],args[0]->u.appl.args[i]) ;
        }
        /*printf("Done\n") ;*/
        return back_exp ;
    }

    count3 = 0 ;
    back[pos] = args[0]->u.appl.args[pos] ;
    for (i = 0; i < count; ++i) {
        for (j = 0; j < i; ++j) {
            /*printf("%d: Testing %s and ", pos, _th_print_exp(args[i*2]->u.appl.args[pos])) ;
             printf("%s\n", _th_print_exp(args[j*2]->u.appl.args[pos])) ;*/
             if (_th_more_general(args[j*2]->u.appl.args[pos],args[i*2]->u.appl.args[pos])) goto cont ;
             /*printf("Good\n") ;*/
        }
        /*printf("    %d: Processing %d\n", pos, i) ;*/
        args2[0] = args[i*2] ;
        args2[1] = args[i*2+1] ;
        k = 2 ;
        for (j = i+1; j<count; ++j) {
            if (_th_has_unifier(args2[i*2]->u.appl.args[pos],args[j*2]->u.appl.args[pos])) {
                /*printf("    %d: Adding %d as %d\n", pos, j, k/2) ;*/
                args2[k++] = args[j*2] ;
                args2[k++] = args[j*2+1] ;
            }
        }
        /*printf("pos = %d\n", pos) ;*/
        args3[count3*2] = args[i*2]->u.appl.args[pos] ;
        /*printf("args[%d] = %s\n", i*2, _th_print_exp(args[i*2])) ;
        printf("%d,%d: args3[%d*2] = %s\n", pos, i,count3,_th_print_exp(args3[i*2]->u.appl.args[pos])) ;
        printf("sub\n") ;*/
        args3[count3*2+1] = build_case(env,pos+1,e,k/2,args2) ;
        /*printf("endsub\n") ;*/
        ++count3;
cont: ;
    }
    return _ex_intern_case(e->u.appl.args[pos],count3,args3) ;
}

static struct _ex_intern *invert_case(struct _ex_intern *e, int c)
{
    struct _ex_intern *args[MAX_ARGS] ;
    struct _ex_intern *args2[MAX_ARGS] ;
    struct _ex_intern *f ;

    int i, j ;

    f = e->u.case_stmt.args[c*2+1] ;
    for (i = 0; i < f->u.case_stmt.count; ++i) {
        args[i*2] = f->u.case_stmt.args[i*2] ;
        for (j = 0; j < e->u.case_stmt.count; ++j) {
            args2[j*2] = e->u.case_stmt.args[j*2] ;
            if (j==c) {
                args2[j*2+1] = f->u.case_stmt.args[i*2+1] ;
            } else {
                args2[j*2+1] = e->u.case_stmt.args[j*2+1] ;
            }
        }
        args[i*2+1] = _ex_intern_case(e->u.case_stmt.exp,j,args2) ;
    }
    return _ex_intern_case(f->u.case_stmt.exp,i,args) ;
}

struct _ex_intern *_th_simplify_case(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern **args, **args2, *f;
	struct _ex_unifier *u, **unifiers;
	char *mark;
    int i, j, k;
    char var_name[20];

	if (e->u.case_stmt.exp->type==EXP_CASE) {
		//check_size(e->u.case_stmt.exp->u.case_stmt.count*2) ;
		args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.case_stmt.exp->u.case_stmt.count*2);
		for (i = 0; i < e->u.case_stmt.exp->u.case_stmt.count; ++i) {
			args[i*2] = e->u.case_stmt.exp->u.case_stmt.args[i*2] ;
			args[i*2+1] = _ex_intern_case(e->u.case_stmt.exp->u.case_stmt.args[i*2+1],
				e->u.case_stmt.count,
				e->u.case_stmt.args) ;
		}
		return _ex_intern_case(e->u.case_stmt.exp->u.case_stmt.exp,
			e->u.case_stmt.exp->u.case_stmt.count,
			args) ;
	}
	if (e->u.case_stmt.exp->type==EXP_APPL &&
		_th_is_constructor(env,e->u.case_stmt.exp->u.appl.functor) &&
		e->u.case_stmt.exp->u.appl.functor != INTERN_SET) {
		//check_size(e->u.case_stmt.count*2) ;
		args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.case_stmt.count*2);
		args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.case_stmt.count*2);
		if (e->u.case_stmt.exp->u.appl.count==0) {
			for (i = 0; i < e->u.case_stmt.count; ++i) {
				switch (e->u.case_stmt.args[i*2]->type) {
				case EXP_VAR:
					mark = _th_alloc_mark(REWRITE_SPACE) ;
					u = _th_new_unifier(REWRITE_SPACE) ;
					u = _th_add_pair(REWRITE_SPACE,u,e->u.case_stmt.args[i*2]->u.var,e->u.case_stmt.exp) ;
					f = _th_subst(env,u,e->u.case_stmt.args[i*2+1]) ;
					_th_alloc_release(REWRITE_SPACE,mark) ;
					return f ;
				case EXP_APPL:
					if (_th_equal(env,e->u.case_stmt.args[i*2],e->u.case_stmt.exp)) {
						return e->u.case_stmt.args[i*2+1] ;
					}
				}
			}
			return NULL ;
		}
		for (i = 0, j = 0; i < e->u.case_stmt.count; ++i) {
			switch (e->u.case_stmt.args[i*2]->type) {
			case EXP_VAR:
				for (k = 0; k < e->u.case_stmt.exp->u.appl.count; ++k) {
					sprintf(var_name, "v%d", k+1) ;
					args2[k] = _ex_intern_var(_th_intern(var_name)) ;
				}
				f = _ex_intern_appl_env(env,e->u.case_stmt.exp->u.appl.functor,k,args2) ;
				args[j++] = f ;
				mark = _th_alloc_mark(REWRITE_SPACE) ;
				u = _th_new_unifier(REWRITE_SPACE) ;
				u = _th_add_pair(REWRITE_SPACE,u,e->u.case_stmt.args[i*2]->u.var,f) ;
				args[j++] = _th_subst(env,u,e->u.case_stmt.args[i*2+1]) ;
				_th_alloc_release(REWRITE_SPACE,mark) ;
				break ;
			case EXP_APPL:
				if (e->u.case_stmt.args[i*2]->u.appl.functor==e->u.case_stmt.exp->u.appl.functor) {
					args[j++] = e->u.case_stmt.args[i*2] ;
					args[j++] = e->u.case_stmt.args[i*2+1] ;
				}
			}
		}
		mark = _th_alloc_mark(REWRITE_SPACE) ;
		for (i = 0; i < j; i+=2) {
			_th_increment_var_data(args[i+1]) ;
		}
		unifiers = (struct _ex_unifier **)ALLOCA(sizeof(struct _ex_unifier *) * e->u.case_stmt.count * 2);
		for (i = 0; i < j; i+=2) {
			unifiers[i] = name_away_from_marks(_th_new_unifier(REWRITE_SPACE),args[i]) ;
			unifiers[i+1] = unifiers[i] ;
		}
		for (i = 0; i < j; ++i) {
			_th_clear_var_data(args[i]) ;
		}
		for (i = 0; i < j; ++i) {
			args[i] = _th_subst(env,unifiers[i],args[i]) ;
		}
		for (i = 0; i < j; ++i) {
			_th_clear_var_data(args[i]) ;
		}
		_th_alloc_release(REWRITE_SPACE,mark) ;
		return build_case(env,0,e->u.case_stmt.exp,j/2,args) ;
	}
	if (e->u.case_stmt.args[0]->type==EXP_VAR) {
		mark = _th_alloc_mark(REWRITE_SPACE) ;
		u = _th_new_unifier(REWRITE_SPACE) ;
		u = _th_add_pair(REWRITE_SPACE,u,e->u.case_stmt.args[0]->u.var,e->u.case_stmt.exp) ;
		f = _th_subst(env,u,e->u.case_stmt.args[1]);
		_th_alloc_release(REWRITE_SPACE,mark) ;
		return f ;
	}
	if (e->u.case_stmt.count > 0 &&
		e->u.case_stmt.args[0]->type == EXP_APPL &&
		_th_is_finite_constructor(env,e->u.case_stmt.args[0]->u.appl.functor)) {
		i = find_smallest(env,e) ;
		if (i != 0xffffffff) {
			return invert_case(e,i) ;
		}
	}
	return NULL ;
}
