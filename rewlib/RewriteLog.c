/*
 * RewriteLog.c
 *
 * Code for logging rewrite commands
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Globals.h"

#include "RewriteLog.h"

#ifdef MAKE_LOG

struct _ex_intern *_th_log_rewrite(struct env *env, struct _ex_intern *exp)
{
    fprintf(rewrite_log, "rewrite %s\n", _th_print_exp(exp)) ;
    exp = _th_rewrite(env,exp) ;
    fprintf(rewrite_log, "result %s\n", _th_print_exp(exp)) ;
    return exp ;
}

struct _ex_intern *_th_log_int_rewrite(struct env *env, struct _ex_intern *exp, int flag)
{
    fprintf(rewrite_log, "int_rewrite %s %d\n", _th_print_exp(exp), flag) ;
    exp = _th_int_rewrite(env,exp, flag) ;
    fprintf(rewrite_log, "result %s\n", _th_print_exp(exp)) ;
    return exp ;
}

char *_th_log_derive_push(struct env *env)
{
    fprintf(rewrite_log, "push\n") ;
    return _th_derive_push(env);
}

void _th_log_derive_pop(struct env *env)
{
    fprintf(rewrite_log, "pop\n") ;
    _th_derive_pop(env) ;
}

void _th_log_derive_pop_release(struct env *env,unsigned char *mark)
{
    fprintf(rewrite_log, "pop\n") ;
    _th_derive_pop_release(env,mark) ;
}

void _th_log_derive_and_add(struct env *env, struct _ex_intern *exp)
{
    fprintf(rewrite_log, "add %s\n", _th_print_exp(exp)) ;
    _th_derive_and_add(env,exp) ;
}

char *_th_log_start_rewrite()
{
    fprintf(rewrite_log, "start_rewrite\n") ;
    return _th_start_rewrite();
}

struct _ex_intern *_th_log_finish_rewrite(char *mark,struct env *env, struct _ex_intern *exp)
{
    fprintf(rewrite_log, "finish_rewrite\n") ;
    return _th_finish_rewrite(mark,env,exp) ;
}

void _th_log_add_attrib(int space, struct env *env, unsigned attrib, unsigned n, struct parameter *params)
{
    unsigned i ;
    
    fprintf(rewrite_log, "attrib %s %d", _th_intern_decode(attrib), n) ;
    for (i = 0; i < n; ++i) {
        fprintf(rewrite_log, " ") ;
        switch (params[i].type) {
            case SYMBOL_PARAMETER:
                fprintf(rewrite_log, "@%s", _th_intern_decode(params[i].u.symbol)) ;
                break ;
            case EXP_PARAMETER:
                fprintf(rewrite_log, "!%s", _th_print_exp(params[i].u.exp)) ;
                break ;
            case INTEGER_LIST_PARAMETER:
            case SYMBOL_LIST_PARAMETER:
                fprintf(rewrite_log, "-") ;
                break ;
            case INTEGER_PARAMETER:
                fprintf(rewrite_log, "#%d", params[i].u.integer) ;
                break ;
            case WILD:
                fprintf(rewrite_log, "*") ;
                break ;
            case FUNCTOR_MATCH:
                fprintf(rewrite_log, "&%s", _th_intern_decode(params[i].u.functor)) ;
                break ;
        }
    }
    fprintf(rewrite_log, "\n") ;
    _th_add_attrib(env,attrib,n,params) ;
}

void _th_log_derive_and_add_property(int space, struct env *env, struct _ex_intern *prop)
{
    fprintf(rewrite_log, "addp %s\n", _th_print_exp(prop)) ;
    _th_derive_and_add_property(space,env,prop) ;
}

void _th_log_add_precedence(int space, struct env *env, unsigned a, unsigned b)
{
    fprintf(rewrite_log, "prec %s %s\n", _th_intern_decode(a), _th_intern_decode(b)) ;
    _th_add_precedence(space,env,a,b) ;
}

void _th_log_add_equal_precedence(int space, struct env *env, unsigned a, unsigned b)
{
    fprintf(rewrite_log, "equal_prec %s %s\n", _th_intern_decode(a), _th_intern_decode(b)) ;
    _th_add_equal_precedence(space,env,a,b) ;
}

void _th_log_add_max_precedence(int space,struct env *env, unsigned a)
{
    fprintf(rewrite_log, "max_prec %s\n", _th_intern_decode(a)) ;
    _th_add_max_precedence(space,env,a) ;
}

#endif
