/*
 * type.c
 *
 * Routines for type checking expressions.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */

#include <stdio.h>
#include <stdlib.h>
#include "Globals.h"
#include "Intern.h"

struct index_var {
        struct index_var *next ;
        unsigned name ;
        struct index_var *parent ;
        unsigned variable ;
        int index_count ;
        int index[1] ;
    } ;

#define DEPTH_INCREMENT 4000

static int height ;
static int current_size ;
static int *stack ;

static void check_depth(int size)
{
   if (size > current_size) {
       current_size += DEPTH_INCREMENT ;
       stack = (int *)REALLOC(stack, sizeof(int) * DEPTH_INCREMENT) ;
   }
}

static void _push_index(int index)
{
    check_depth(height+1) ;
    stack[height++] = index ;
}

static void _pop_index()
{
    --height ;
}

static struct index_var *index_root = NULL;

static struct index_var *_create(unsigned name, struct index_var *parent, unsigned var)
{
    struct index_var *v = (struct index_var *)_th_alloc(TYPE_SPACE,sizeof(struct index_var) + height * sizeof(int)) ;
    int i ;
    v->next = index_root ;
    index_root = v ;
    v->name = name ;
    v->parent = parent ;
    v->index_count = height ;
    v->variable = var ;
    for (i = 0; i < height; ++i) v->index[i] = stack[i] ;

    return v ;
}

static int _print_errors = 0 ;

static void _print_error(struct env *env, struct _ex_intern *e1, struct _ex_intern *e2, struct _ex_intern *term)
{
    int i ;

    if (_print_errors) {
        printf("Error: Type checking at:") ;
        for (i = 0; i < height; ++i) {
            printf(" %d", stack[i]) ;
        }
        printf("\n") ;
        if (term != NULL) printf("term:\n%s\n", _th_pp_print(env,INTERN_DEFAULT,80,term)) ;
        printf("Cannot match types %s", _th_pp_print(env,INTERN_DEFAULT,80,e1)) ;
        printf(" and %s\n", _th_pp_print(env,INTERN_DEFAULT,80,e2)) ;
    }
}

static struct _ex_unifier *_unify(struct env *env,struct _ex_unifier *u, struct _ex_intern *e1, struct _ex_intern *e2, struct _ex_intern *eterm)
{
    struct _ex_intern *e ;
    int i ;

    switch (e1->type) {

        case EXP_VAR:
            e = _th_apply(u,e1->u.var) ;
            if (e != NULL) return _unify(env,u,e,e2,eterm) ;
            switch (e2->type) {
                case EXP_VAR:
                    e = _th_apply(u,e2->u.var) ;
                    if (e != NULL) return _unify(env,u,e1,e,eterm) ;
                    if (e1->u.var==e2->u.var) return u ;
                    _th_update_unifier(env,e1->u.var,e2,u) ;
                    _th_add_pair(TYPE_SPACE,u,e1->u.var,e2) ;
                    return u ;

                case EXP_APPL:
                    if (_th_is_free_in(e2,e1->u.var)) {
                        _print_error(env,e1,e2,eterm) ;
                        return NULL ;
                    }
                    _th_update_unifier(env,e1->u.var,e2,u) ;
                    _th_add_pair(TYPE_SPACE,u,e1->u.var,e2) ;
                    return u ;

                default:
                    _print_error(env,e1,e2,eterm) ;
                    return NULL ;
            }

        case EXP_APPL:
            if (e1->u.appl.functor==INTERN_ANY_TYPE) return u ;
            switch (e2->type) {
                case EXP_APPL:
                    if (e1->u.appl.functor != e2->u.appl.functor ||
                        e1->u.appl.count != e2->u.appl.count) {
                        _print_error(env,e1,e2,eterm) ;
                        return NULL ;
                    }
                    for (i = 0; i < (int)e1->u.appl.count; ++i) {
                        u = _unify(env,u,e1->u.appl.args[i],e2->u.appl.args[i],eterm) ;
                        if (u==NULL) return NULL ;
                    }
                    return u ;

                case EXP_VAR:
                    e = _th_apply(u,e2->u.var) ;
                    if (e != NULL) return _unify(env,u,e1,e,eterm) ;
                    if (_th_is_free_in(e1,e2->u.var)) {
                        _print_error(env,e1,e2,eterm) ;
                        return NULL ;
                    }
                    _th_update_unifier(env,e2->u.var,e1,u) ;
                    _th_add_pair(TYPE_SPACE,u,e2->u.var,e1) ;
                    return u ;
                default:
                    _print_error(env,e1,e2,eterm) ;
                    return NULL ;
            }

        default:
            return NULL;
    }
}

static int count ;

static struct _ex_unifier *_create_mapping(struct _ex_unifier *u, struct _ex_intern *e)
{
    int i ;
    unsigned nvar ;
    char name[10] ;

    switch(e->type) {
        case EXP_VAR:
            if (_th_apply(u,e->u.var) != NULL) return u ;
            sprintf(name, "v%d", count++) ;
            nvar = _th_intern(name) ;
            u = _th_add_pair(TYPE_SPACE,u,e->u.var,_ex_intern_var(nvar)) ;
            return u ;

        case EXP_APPL:
            for (i = 0; i < (int)e->u.appl.count; ++i) {
                u = _create_mapping(u,e->u.appl.args[i]) ;
            }
            return u ;

        default:
            printf("Illegal type\n") ;
            exit(1) ;
    }
}

static struct _ex_intern *_type_subst(struct env *env,struct _ex_unifier *u,struct _ex_intern *e)
{
    struct _ex_intern **args ;
    struct _ex_intern *e1 ;
    int i ;

    switch(e->type) {

        case EXP_VAR:
            e1 = _th_apply(u,e->u.var) ;
            if (e1 == NULL) {
                return e ;
            } else {
                return e1 ;
            }
        case EXP_APPL:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            for (i = 0; i < (int)e->u.appl.count; ++i) {
                 args[i] = _type_subst(env,u,e->u.appl.args[i]) ;
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args) ;
        default:
            printf("Illegal type\n") ;
            exit(1) ;
    }
}

static struct _ex_intern *_instantiate(struct env *env, struct _ex_intern *e)
{
    char *mark ;
    struct _ex_unifier *u ;

    mark = _th_alloc_mark(TYPE_SPACE) ;

    u = _create_mapping(_th_new_unifier(TYPE_SPACE),e) ;
    e = _type_subst(env,u,e) ;

    _th_alloc_release(TYPE_SPACE,mark) ;

    return e ;
}

static struct _ex_intern *integerType ;
static struct _ex_intern *stringType ;
static struct _ex_intern *rationalType ;
static struct _ex_intern *boolType ;
static struct _ex_intern *setType ;
static struct _ex_intern *lambdaType ;

void _th_type_init()
{
    integerType = _ex_intern_appl(INTERN_INT,0,NULL) ;
    stringType = _ex_intern_appl(INTERN_STRING,0,NULL) ;
    rationalType = _ex_intern_appl(INTERN_REAL,0,NULL) ;
    boolType = _ex_intern_appl(INTERN_BOOL,0,NULL) ;
    setType = _th_parse(NULL,"(F (P a) (Set a))") ;
    lambdaType = _th_parse(NULL, "(=> a b)") ;
}

struct _ex_intern *_get_var_type(int v)
{
    struct index_var *iv = (struct index_var *)_th_intern_get_data(v) ;
    char name[10] ;

    sprintf(name, "v%d", iv->variable) ;
    return _ex_intern_var(_th_intern(name)) ;
}

struct _ex_intern *_get_marked_var_type(int v)
{
    struct index_var *iv = (struct index_var *)_th_intern_get_data(v) ;
    char name[10] ;

    sprintf(name, "_%s", _th_intern_decode(v)) ;
    v = _th_intern(name) ;
    iv = (struct index_var *)_th_intern_get_data(v) ;
    sprintf(name, "v%d", iv->variable) ;
    return _ex_intern_var(_th_intern(name)) ;
}

static struct _ex_intern **args ;
static int arg_count ;

check_size(int x)
{
    if (x > arg_count) {
        arg_count = x ;
        args = (struct _ex_intern **)REALLOC(args,sizeof(struct _ex_intern *) * arg_count) ;
    }
}

static struct _ex_intern *_mk_product(int x)
{
    int i ;
    char name[10] ;

    check_size(x) ;
    check_size(2) ;
    for (i = 0; i < x; ++i) {
         sprintf(name, "v%d", count++) ;
         args[i] = _ex_intern_var(_th_intern(name)) ;
    }
    args[1] = args[0] = _ex_intern_appl(INTERN_TUPLE,x,args) ;
    return _ex_intern_appl(INTERN_FUNCTION,2,args) ;
}

static void _push_case_vars(struct _ex_intern *e)
{
    int i ;

    switch(e->type) {

        case EXP_APPL:
            for (i = 0; i < (int)e->u.appl.count; ++i) {
                _push_case_vars(e->u.appl.args[i]) ;
            }
            break ;

        case EXP_VAR:
            _th_intern_set_data(e->u.var,
                ((int)_create(e->u.var,
                        (struct index_var *)_th_intern_get_data(e->u.var),
                        count++))) ;
            break ;
    }
}

static void _pop_case_vars(struct _ex_intern *e)
{
    int i ;

    switch(e->type) {

        case EXP_APPL:
            for (i = 0; i < (int)e->u.appl.count; ++i) {
                _pop_case_vars(e->u.appl.args[i]) ;
            }
            break ;

        case EXP_VAR:
            _th_intern_set_data(e->u.var,((int)((struct index_var *)_th_intern_get_data(e->u.var))->parent)) ;
            break ;
    }
}

static struct _ex_intern *is_a_type(struct env *env, unsigned sym)
{
    struct _ex_intern *f = _th_get_type_functor(env,sym);
    int i;

    if (f==NULL) {
        //if (sym==INTERN_INT || sym==INTERN_REAL || sym==INTERN_BOOL ||
        //     sym==INTERN_BOOL) {
        //    return _ex_intern_appl2_env(env,INTERN_FUNCTION,
        //               _ex_intern_appl_env(env,INTERN_TUPLE,0,NULL),
        //               _ex_intern_appl_env(env,INTERN_TYPE,0,NULL)) ;
        //}
        return NULL;
    }


    if (f != NULL) check_size(f->u.appl.count);
    check_size(2);
    for (i = 0; i < f->u.appl.count; ++i) {
         //sprintf(name, "v%d", count++);
         args[i] = _ex_intern_appl_env(env,INTERN_TYPE,0,NULL);
    }
    args[1] = _ex_intern_appl_env(env,INTERN_TYPE,0,NULL);
    args[0] = _ex_intern_appl(INTERN_TUPLE,f->u.appl.count,args);

    return _ex_intern_appl(INTERN_FUNCTION,2,args);
}

static struct _ex_intern *get_special_type(struct env *env, struct _ex_intern *term)
{
    struct disc *d = _th_get_all_rules(env) ;
    struct match_return *mr ;
    struct _ex_intern *r, *sub, *res ;
    struct disc_iterator di ;
    char *mark ;

    term = _ex_intern_appl1_env(env, INTERN_SPECIAL_TYPE, term) ;

    mark = _th_alloc_mark(MATCH_SPACE) ;

    _th_init_find(&di, d, term) ;

    while(r = _th_next_find(&di,NULL)) {
        if (r->u.appl.args[0]->type != EXP_VAR) {
            r = _th_augment_expression(env,r,term) ;
            mr = _th_match(env, r->u.appl.args[0], term) ;
            while (mr != NULL) {
                sub = r->u.appl.args[1] ;
                res = _th_subst(env,mr->theta,sub) ;
                _th_alloc_release(MATCH_SPACE,mark) ;
                return res ;
            }
        }
    }

    _th_alloc_release(MATCH_SPACE,mark) ;

    return NULL ;
}

static struct _ex_unifier *_checkTyping(struct env *env, struct _ex_unifier *u, struct _ex_intern *t, struct _ex_intern *e)
{
    struct _ex_intern *test, *test2 ;
    struct _ex_intern *vt ;
    int i, a ;
    
    //printf("Checking %s\n", _th_pp_print(env,INTERN_DEFAULT,80,e)) ;
    //printf("Type %s\n", _th_print_exp(t)) ;
    //fflush(stdout) ;

    switch (e->type) {
        
    case EXP_INTEGER:
        return _unify(env,u,t,integerType,e) ;
        
    case EXP_RATIONAL:
        return _unify(env,u,t,rationalType,e) ;
        
    case EXP_STRING:
        return _unify(env,u,t,stringType,e) ;
        
    case EXP_VAR:
        if (t->u.appl.functor==INTERN_TYPE) return u ;
        vt = _get_var_type(e->u.var);
        //if (((struct index_var *)_th_intern_get_data(e->u.var))->next==NULL) {
        //    struct _ex_intern *vt2 = _th_get_var_type(env,e->u.var);
        //    //printf("vt2 = %s\n", _th_print_exp(vt2));
        //    vt2 = _instantiate(env,vt2);
        //    if (vt2) {
        //        u = _unify(env,u,t,vt2,e);
        //    }
        //}
        return _unify(env,u,t,vt,e) ;
        
    case EXP_MARKED_VAR:
        return _unify(env,u,t,_get_marked_var_type(e->u.var),e) ;
        
    case EXP_APPL:
        if (e->u.appl.functor==INTERN_T) {
            test = _mk_product(e->u.appl.count) ;
            //printf("    Case1 %s\n", _th_print_exp(test)) ;
            //fflush(stdout) ;
        } else {
            test = get_special_type(env,e) ;
            if (test==NULL) test = is_a_type(env,e->u.appl.functor) ;
            if (test==NULL) test = _th_get_type(env,e->u.appl.functor) ;
            if (test==NULL) {
                if (_print_errors) {
                    printf("Undefined symbol %s\n", _th_intern_decode(e->u.appl.functor)) ;
                }
                return NULL ;
            }
            test = _instantiate(env,test) ;
            //printf("    Case2 %s\n", _th_print_exp(test)) ;
            //fflush(stdout) ;
        }
        u = _unify(env,u,t,test->u.appl.args[1],e) ;
        //printf("Unifying %s ", _th_print_exp(test->u.appl.args[1])) ;
        //printf(" and %s\n", _th_print_exp(e)) ;
        if (u==NULL) return NULL ;
        test = _th_subst(env,u,test) ;
        if (test->u.appl.args[0]->u.appl.functor==INTERN_ANY_TYPE) {
            ;
        } else if (e->u.appl.functor==INTERN_SET || _th_is_ac(env,e->u.appl.functor) || _th_is_a(env,e->u.appl.functor)) {
            a = _th_ac_arity(env,e->u.appl.functor) ;
            if (test->u.appl.args[0]->u.appl.functor != INTERN_TUPLE ||
                test->u.appl.args[0]->u.appl.count != 2+a) {
                if (_print_errors) {
                    printf("Illegal type %s for functor %s\n",_th_print_exp(test),_th_intern_decode(e->u.appl.functor)) ;
                }
                return NULL ;
            }
            for (i = 0; i < a; ++i) {
                _push_index(i) ;
                u = _checkTyping(env,u,test->u.appl.args[0]->u.appl.args[i],e->u.appl.args[i]) ;
                if (u == NULL) return NULL ;
                _pop_index() ;
            }
            for (; i < (int)e->u.appl.count; ++i) {
                _push_index(i) ;
                u = _checkTyping(env,u,test->u.appl.args[0]->u.appl.args[a],e->u.appl.args[i]) ;
                if (u == NULL) return NULL ;
                _pop_index() ;
            }
        } else {
            if (e->u.appl.count==1) {
                struct _ex_intern *t ;
                if (test->u.appl.args[0]->type == EXP_APPL && test->u.appl.args[0]->u.appl.functor == INTERN_TUPLE &&
                    test->u.appl.args[0]->u.appl.count != 1) {
                    if (_print_errors) {
                        printf("%s\n",_th_print_exp(e)) ;
                        printf("%s\n",_th_print_exp(test)) ;
                        printf("(a) Illegal # parameters for functor %s\n",_th_intern_decode(e->u.appl.functor)) ;
                    }
                    return NULL ;
                }
                _push_index(0) ;
                t = test->u.appl.args[0] ;
                if (t->type==EXP_APPL && t->u.appl.functor==INTERN_TUPLE) t = t->u.appl.args[0] ;
                u = _checkTyping(env,u,t,e->u.appl.args[0]) ;
                if (u == NULL) return NULL ;
                _pop_index() ;
            } else {
                if (test->u.appl.args[0]->type != EXP_APPL || test->u.appl.args[0]->u.appl.functor != INTERN_TUPLE ||
                    test->u.appl.args[0]->u.appl.count != e->u.appl.count) {
                    if (_print_errors) {
                        printf("%s\n",_th_print_exp(e)) ;
                        printf("%s\n",_th_print_exp(test)) ;
                        printf("(b) Illegal # parameters for functor %s\n",_th_intern_decode(e->u.appl.functor)) ;
                    }
                    return NULL ;
                }
                for (i = 0; i < (int)e->u.appl.count; ++i) {
                    _push_index(i) ;
                    u = _checkTyping(env,u,test->u.appl.args[0]->u.appl.args[i],e->u.appl.args[i]) ;
                    if (u == NULL) return NULL ;
                    _pop_index() ;
                }
            }
        }
        return u ;
        
    case EXP_QUANT:
        for (i = 0; i < (int)e->u.quant.var_count; ++i) {
            _th_intern_set_data(e->u.quant.vars[i],
                ((int)_create(e->u.quant.vars[i],
                (struct index_var *)_th_intern_get_data(e->u.quant.vars[i]),
                count++))) ;
        }
        switch (e->u.quant.quant) {
            
        case INTERN_ALL:
            _push_index(0) ;
            u = _checkTyping(env,u,boolType,e->u.quant.exp) ;
            if (u==NULL) return NULL ;
            _pop_index() ;
            _push_index(1) ;
            u = _checkTyping(env,u,boolType,e->u.quant.cond) ;
            if (u==NULL) return NULL ;
            _pop_index() ;
            u = _unify(env,u,t,boolType,e) ;
            break ;
            
        case INTERN_EXISTS:
            _push_index(0) ;
            u = _checkTyping(env,u,boolType,e->u.quant.exp) ;
            if (u==NULL) return NULL ;
            _pop_index() ;
            u = _unify(env,u,t,boolType,e) ;
            break ;
            
        case INTERN_SETQ:
            test = _instantiate(env,setType) ;
            _push_index(0) ;
            u = _checkTyping(env,u,test->u.appl.args[0]->u.appl.args[0],e->u.quant.exp) ;
            if (u == NULL) return NULL ;
            _pop_index() ;
            _push_index(1) ;
            u = _checkTyping(env,u,boolType,e->u.quant.cond) ;
            if (u == NULL) return NULL ;
            _pop_index() ;
            u = _unify(env,u,test->u.appl.args[1],t,e) ;
            break ;
            
        case INTERN_LAMBDA:
            if (e->u.quant.var_count > 1) return NULL ;
            test = _instantiate(env,lambdaType) ;
            u = _checkTyping(env,u,test->u.appl.args[0],_ex_intern_var(e->u.quant.vars[0])) ;
            _push_index(0) ;
            u = _checkTyping(env,u,test->u.appl.args[1],e->u.quant.exp) ;
            if (u == NULL) return NULL ;
            _pop_index() ;
            _push_index(1) ;
            u = _checkTyping(env,u,boolType,e->u.quant.cond) ;
            if (u == NULL) return NULL ;
            _pop_index() ;
            u = _unify(env,u,test,t,e) ;
            break ;
            
        default:
            return NULL ;
        }
        for (i = 0; i < (int)e->u.quant.var_count; ++i) {
            _th_intern_set_data(e->u.quant.vars[i],((int)((struct index_var *)_th_intern_get_data(e->u.quant.vars[i]))->parent)) ;
        }
        return u ;
        
        case EXP_CASE:
            test = _instantiate(env,_ex_intern_var(1)) ;
            test2 = _instantiate(env,_ex_intern_var(1)) ;
            _push_index(0) ;
            u = _checkTyping(env,u,test,e->u.case_stmt.exp) ;
            if (u == NULL) return NULL ;
            _pop_index() ;
            for (i = 0; i < (int)e->u.case_stmt.count; ++i) {
                _push_index(i*2+1) ;
                _push_case_vars(e->u.case_stmt.args[i*2]) ;
                u = _checkTyping(env,u,test,e->u.case_stmt.args[i*2]) ;
                if (u == NULL) return NULL ;
                _pop_index() ;
                _push_index(i*2+2) ;
                u = _checkTyping(env,u,t,e->u.case_stmt.args[i*2+1]) ;
                _pop_case_vars(e->u.case_stmt.args[i*2]) ;
                if (u == NULL) return NULL ;
                _pop_index() ;
            }
            return u ;
        default:
            return NULL;
    }
}

static char *mark ;
struct _ex_unifier *_th_checkTyping(struct env *env, struct _ex_intern *t, struct _ex_intern *e)
{
    int c ;
    unsigned *fv = _th_get_free_vars(e, &c) ;
    int i ;
    struct _ex_unifier *u ;
    mark = _th_alloc_mark(TYPE_SPACE) ;

    height = count = 0 ;

    index_root = NULL;

    u = _th_new_unifier(TYPE_SPACE) ;
    for (i = 0; i < c; ++i) {
        _th_intern_set_data(fv[i], ((int)_create(fv[i],0,count++))) ;
    }
    u = _checkTyping(env,u,t,e) ;
    for (i = 0; i < c; ++i) {
        _th_intern_set_data(fv[i],0) ;
    }

    return u ;
}

void _th_check(struct env *env, struct _ex_intern *t, struct _ex_intern *e)
{
    int res ;
    _print_errors = 1 ;
    //printf("Checking %s\n", _th_pp_print(env,INTERN_DEFAULT,80,e)) ;
    //printf("Type %s\n", _th_pp_print(env,INTERN_DEFAULT,80,t)) ;
    //fflush(stdout) ;
    res = (_th_checkTyping(env,t,e) != NULL) ;
    _print_errors = 0 ;
    if (!res) {
        printf("Error: Type checking in %s\n", _th_pp_print(env,INTERN_DEFAULT,80,e)) ;
        exit(1) ;
    }
    _th_clearTypeInfo() ;
}

struct _ex_intern *_th_return_type(struct env *env, struct _ex_intern *e)
{
    struct _ex_unifier *res ;
    struct _ex_intern *t = _ex_intern_var(_th_intern("vv")) ;
    _print_errors = 1 ;
    //printf("Checking %s\n", _th_pp_print(env,INTERN_DEFAULT,80,e)) ;
    //printf("Type %s\n", _th_pp_print(env,INTERN_DEFAULT,80,t)) ;
    //fflush(stdout) ;
    res = _th_checkTyping(env,t,e) ;
    _print_errors = 0 ;
    _th_clearTypeInfo() ;
    if (!res) return NULL ;
    return _th_apply(res,_th_intern("vv")) ;
}

void _th_clearTypeInfo()
{
    _th_alloc_release(TYPE_SPACE,mark) ;
}

struct _ex_intern *_th_exp_var_type(struct _ex_unifier *u, unsigned v, int count, int *index)
{
    struct index_var *iv = index_root ;
    struct index_var *current = NULL ;
    char name[20] ;
    int i ;

    while (iv != NULL) {
        if (v != iv->name) goto next ;
        if (iv->index_count > count) goto next ;
        for (i = 0; i < iv->index_count; ++i) {
            if (index[i] != iv->index[i]) goto next ;
        }
        if (current==NULL || iv->index_count > current->index_count) {
            current = iv ;
        }
next:
        iv = iv->next ;
    }
    if (current==NULL) return NULL ;

    sprintf(name, "v%d", current->variable) ;
    return _th_apply(u,_th_intern(name)) ;
}

