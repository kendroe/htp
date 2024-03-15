/*
 * exp_utils.c
 *
 * Utility routines for working on expressions.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <stdio.h>

#include "Globals.h"

void _th_clear_var_data(struct _ex_intern *e)
{
    int i ;

    switch(e->type) {
        case EXP_VAR:
            _th_intern_set_data(e->u.var,0) ;
            break ;
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                _th_clear_var_data(e->u.appl.args[i]) ;
            }
            break ;
        case EXP_CASE:
            _th_clear_var_data(e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
                _th_clear_var_data(e->u.case_stmt.args[i]) ;
            }
            _th_clear_var_data(e->u.case_stmt.exp) ;
            break ;
        case EXP_QUANT:
            _th_clear_var_data(e->u.quant.exp) ;
            _th_clear_var_data(e->u.quant.cond) ;
            break ;
        case EXP_INDEX:
            _th_clear_var_data(e->u.index.exp) ;
            break ;
    }
}

void _th_increment_var_data(struct _ex_intern *e)
{
    int i ;

    switch(e->type) {
        case EXP_VAR:
            _th_intern_set_data(e->u.var,_th_intern_get_data(e->u.var)+2) ;
            break ;
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                _th_increment_var_data(e->u.appl.args[i]) ;
            }
            break ;
        case EXP_CASE:
            _th_increment_var_data(e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
                _th_increment_var_data(e->u.case_stmt.args[i]) ;
            }
            _th_increment_var_data(e->u.case_stmt.exp) ;
            break ;
        case EXP_QUANT:
            _th_increment_var_data(e->u.quant.exp) ;
            _th_increment_var_data(e->u.quant.cond) ;
            break ;
        case EXP_INDEX:
            _th_increment_var_data(e->u.index.exp) ;
            break ;
    }
}

void _th_decrement_var_data(struct _ex_intern *e)
{
    int i ;

    switch(e->type) {
        case EXP_VAR:
            _th_intern_set_data(e->u.var,_th_intern_get_data(e->u.var)-2) ;
            break ;
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                _th_decrement_var_data(e->u.appl.args[i]) ;
            }
            break ;
        case EXP_CASE:
            _th_decrement_var_data(e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
                _th_decrement_var_data(e->u.case_stmt.args[i]) ;
            }
            _th_decrement_var_data(e->u.case_stmt.exp) ;
            break ;
        case EXP_QUANT:
            _th_decrement_var_data(e->u.quant.exp) ;
            _th_decrement_var_data(e->u.quant.cond) ;
            break ;
        case EXP_INDEX:
            _th_decrement_var_data(e->u.index.exp) ;
            break ;
    }
}

void _th_increment_var_data2(struct _ex_intern *e)
{
    int i ;

    switch(e->type) {
        case EXP_VAR:
            _th_intern_set_data2(e->u.var,_th_intern_get_data2(e->u.var)+1) ;
            break ;
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                _th_increment_var_data2(e->u.appl.args[i]) ;
            }
            break ;
        case EXP_CASE:
            _th_increment_var_data2(e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
                _th_increment_var_data2(e->u.case_stmt.args[i]) ;
            }
            _th_increment_var_data2(e->u.case_stmt.exp) ;
            break ;
        case EXP_QUANT:
            _th_increment_var_data2(e->u.quant.exp) ;
            _th_increment_var_data2(e->u.quant.cond) ;
            break ;
        case EXP_INDEX:
            _th_increment_var_data2(e->u.index.exp) ;
            break ;
    }
}

void _th_decrement_var_data2(struct _ex_intern *e)
{
    int i ;

    switch(e->type) {
        case EXP_VAR:
            _th_intern_set_data2(e->u.var,_th_intern_get_data2(e->u.var)-1) ;
            break ;
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                _th_decrement_var_data2(e->u.appl.args[i]) ;
            }
            break ;
        case EXP_CASE:
            _th_decrement_var_data2(e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
                _th_decrement_var_data2(e->u.case_stmt.args[i]) ;
            }
            _th_decrement_var_data2(e->u.case_stmt.exp) ;
            break ;
        case EXP_QUANT:
            _th_decrement_var_data2(e->u.quant.exp) ;
            _th_decrement_var_data2(e->u.quant.cond) ;
            break ;
        case EXP_INDEX:
            _th_decrement_var_data2(e->u.index.exp) ;
            break ;
    }
}

static int _var_list_size = 0 ;
static int _var_list_count = 0 ;
static unsigned *_var_list = NULL ;

#define VAR_LIST_INCREMENT 1024

void add_var(unsigned v)
{
    if (_var_list_count >= _var_list_size) {
        if (_var_list_size == 0) {
            _var_list = (unsigned *)MALLOC(sizeof(unsigned int) * VAR_LIST_INCREMENT) ;
            _var_list_size = VAR_LIST_INCREMENT ;
        } else {
            _var_list_size += VAR_LIST_INCREMENT ;
            _var_list = (unsigned *)REALLOC(_var_list,sizeof(unsigned int) * _var_list_size) ;
        }
    }
    _var_list[_var_list_count++] = v ;
}

static struct _ex_intern *trail;

static void _get_free_vars(struct _ex_intern *e)
{
    int i ;

    if (e->user2) {
#ifdef CHECK
        struct _ex_intern *f = trail;
        while (f) {
            if (f==e) return;
            f = f->next_cache;
        }
        fprintf(stderr, "Illegal term with user2 %s\n", _th_print_exp(e));
#else
        return;
#endif
    }

    e->next_cache = trail;
    trail = e;
    trail->user2 = e;

    switch (e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                _get_free_vars(e->u.appl.args[i]) ;
            }
            break ;
        case EXP_INDEX:
            _get_free_vars(e->u.index.exp) ;
            break ;
        case EXP_QUANT:
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])+1) ;
            }
            _get_free_vars(e->u.quant.exp),
            _get_free_vars(e->u.quant.cond) ;
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])-1) ;
            }
            break ;
        case EXP_CASE:
            _get_free_vars(e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count *2; i+=2) {
                _th_increment_var_data(e->u.case_stmt.args[i]) ;
                _get_free_vars(e->u.case_stmt.args[i+1]) ;
                _th_decrement_var_data(e->u.case_stmt.args[i]) ;
            }
            break ;
        case EXP_VAR:
            if (!_th_intern_get_data(e->u.var)) {
                add_var(e->u.var) ;
                _th_intern_set_data(e->u.var,_th_intern_get_data(e->u.var)|1) ;
            //} else {
                //printf("data %d %s\n", _th_intern_get_data(e->u.var), _th_intern_decode(e->u.var));
            }
            break ;
    }
}

static int _has_duplicate_var(struct _ex_intern *e)
{
    int i, res ;

    res = 0 ;
    switch (e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                if (_has_duplicate_var(e->u.appl.args[i])) return 1 ;
            }
            break ;
        case EXP_INDEX:
            return _has_duplicate_var(e->u.index.exp) ;
        case EXP_QUANT:
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])+2) ;
            }
            res = (_has_duplicate_var(e->u.quant.exp) ||
                   _has_duplicate_var(e->u.quant.cond)) ;
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])-2) ;
            }
            break ;
        case EXP_CASE:
            if (_has_duplicate_var(e->u.case_stmt.exp)) return 1 ;
            for (i = 0; i < e->u.case_stmt.count *2; i+=2) {
                _th_increment_var_data(e->u.case_stmt.args[i]) ;
                res = _has_duplicate_var(e->u.case_stmt.args[i+1]) ;
                _th_decrement_var_data(e->u.case_stmt.args[i]) ;
                if (res) return 1 ;
            }
            break ;
        case EXP_VAR:
            if (_th_intern_get_data(e->u.var) & 1) {
                res = 1 ;
            } else {
                add_var(e->u.var) ;
                _th_intern_set_data(e->u.var,_th_intern_get_data(e->u.var)|1) ;
            }
            break ;
    }

    return res ;
}

int _th_is_free_in(struct _ex_intern *e, unsigned v)
{
    int i, r ;

    switch (e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                if (_th_is_free_in(e->u.appl.args[i],v)) return 1 ;
            }
            return 0 ;
        case EXP_INDEX:
            return _th_is_free_in(e->u.index.exp,v) ;
        case EXP_QUANT:
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])+1) ;
            }
            r = (_th_is_free_in(e->u.quant.exp,v) || _th_is_free_in(e->u.quant.cond,v)) ;
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])-1) ;
            }
            return r ;
        case EXP_CASE:
            r = _th_is_free_in(e->u.case_stmt.exp,v) ;
            if (r) return 1 ;
            for (i = 0; i < e->u.case_stmt.count *2; i+=2) {
                _th_increment_var_data(e->u.case_stmt.args[i]) ;
                r = _th_is_free_in(e->u.case_stmt.args[i+1],v) ;
                _th_decrement_var_data(e->u.case_stmt.args[i]) ;
                if (r) return 1 ;
            }
            return 0 ;
        case EXP_VAR:
            if (!_th_intern_get_data(e->u.var)) {
                return e->u.var==v ;
            } else {
                return 0 ;
            }
        default:
            return 0 ;
    }
}

int _th_is_marked_in(struct _ex_intern *e, unsigned v)
{
    int i, r ;

    switch (e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                if (_th_is_marked_in(e->u.appl.args[i],v)) return 1 ;
            }
            return 0 ;
        case EXP_INDEX:
            return _th_is_marked_in(e->u.index.exp,v) ;
        case EXP_QUANT:
            r = (_th_is_marked_in(e->u.quant.exp,v) || _th_is_marked_in(e->u.quant.cond,v)) ;
            return r ;
        case EXP_CASE:
            r = _th_is_marked_in(e->u.case_stmt.exp,v) ;
            if (r) return 1 ;
            for (i = 0; i < e->u.case_stmt.count *2; i+=2) {
                r = _th_is_marked_in(e->u.case_stmt.args[i+1],v) ;
                if (r) return 1 ;
            }
            return 0 ;
        case EXP_MARKED_VAR:
            if (!_th_intern_get_data(e->u.var)) {
                return e->u.marked_var.var==v ;
            } else {
                return 0 ;
            }
        default:
            return 0 ;
    }
}

void _th_unflag_free_vars(struct _ex_intern *e)
{
    int i ;

    switch (e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                _th_unflag_free_vars(e->u.appl.args[i]) ;
            }
            break ;
        case EXP_INDEX:
            _th_unflag_free_vars(e->u.index.exp) ;
            break ;
        case EXP_QUANT:
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])+2) ;
            }
            _th_unflag_free_vars(e->u.quant.exp),
            _th_unflag_free_vars(e->u.quant.cond) ;
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])-2) ;
            }
            break ;
        case EXP_CASE:
            _th_unflag_free_vars(e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count *2; i+=2) {
                _th_increment_var_data(e->u.case_stmt.args[i]) ;
                _th_increment_var_data(e->u.case_stmt.args[i]) ;
                _th_unflag_free_vars(e->u.case_stmt.args[i+1]) ;
                _th_decrement_var_data(e->u.case_stmt.args[i]) ;
                _th_decrement_var_data(e->u.case_stmt.args[i]) ;
            }
            break ;
        case EXP_VAR:
            if (_th_intern_get_data(e->u.var)==1) {
                _th_intern_set_data(e->u.var, 0) ;
            }
            break ;
    }
}

unsigned *_th_get_free_vars(struct _ex_intern *e, int *c)
{
    int i ;
    //printf("free vars in %s\n", _th_print_exp(e));
    _var_list_count = 0 ;
    trail = NULL ;
    _get_free_vars(e) ;
    while (trail) {
        trail->user2 = NULL;
        trail = trail->next_cache;
    }
    for (i = 0; i < _var_list_count; ++i) {
        _th_intern_set_data(_var_list[i], 0) ;
    }
    *c = _var_list_count ;
    return _var_list ;
}

int _th_has_duplicate_var(struct _ex_intern *e)
{
    int i, res ;
    _var_list_count = 0 ;
    res = _has_duplicate_var(e) ;
    for (i = 0; i < _var_list_count; ++i) {
        _th_intern_set_data(_var_list[i], 0) ;
    }
    return res ;
}

unsigned *_th_get_free_vars_leave_marked(struct _ex_intern *e, int *c)
{
    static int count = 0;
    //printf("(%d) Getting free vars in %s\n", count, _th_print_exp(e));
    //if (count==47) {
    //    count = 0;
    //    count = 1 / count;
    //}
    //++count;
    _var_list_count = 0 ;
    _get_free_vars(e) ;
    *c = _var_list_count ;
    return _var_list ;
}

unsigned *_th_cont_free_vars_leave_marked(struct _ex_intern *e, int *c)
{
    //printf("Cont free vars %s\n", _th_print_exp(e));
    _get_free_vars(e) ;
    *c = _var_list_count ;
    return _var_list ;
}

static void _get_all_vars(struct _ex_intern *e)
{
    int i ;

    switch (e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                _get_all_vars(e->u.appl.args[i]) ;
            }
            break ;
        case EXP_INDEX:
            _get_all_vars(e->u.index.exp) ;
            break ;
        case EXP_QUANT:
            _get_all_vars(e->u.quant.exp),
            _get_all_vars(e->u.quant.cond) ;
            break ;
        case EXP_CASE:
            _get_all_vars(e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count *2; i+=2) {
                _get_all_vars(e->u.case_stmt.args[i+1]) ;
            }
            break ;
        case EXP_VAR:
            if (!_th_intern_get_data(e->u.var)) {
                add_var(e->u.var) ;
                _th_intern_set_data(e->u.var,
                    _th_intern_get_data(e->u.var)+1) ;
            }
            break ;
    }
}

unsigned *_th_get_all_vars(struct _ex_intern *e, int *c)
{
    int i ;
    _var_list_count = 0 ;
    _get_all_vars(e) ;
    for (i = 0; i < _var_list_count; ++i) {
        _th_intern_set_data(_var_list[i], 0) ;
    }
    *c = _var_list_count ;
    return _var_list ;
}

static void _get_marked_vars(struct _ex_intern *e)
{
    int i ;

    switch (e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                _get_marked_vars(e->u.appl.args[i]) ;
            }
            break ;
        case EXP_INDEX:
            _get_marked_vars(e->u.index.exp) ;
            break ;
        case EXP_QUANT:
            _get_marked_vars(e->u.quant.exp),
            _get_marked_vars(e->u.quant.cond) ;
            break ;
        case EXP_CASE:
            _get_marked_vars(e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count *2; i+=2) {
                _get_marked_vars(e->u.case_stmt.args[i+1]) ;
            }
            break ;
        case EXP_MARKED_VAR:
            if (!_th_intern_get_data(e->u.marked_var.var)) {
                add_var(e->u.marked_var.var) ;
                _th_intern_set_data(e->u.marked_var.var,
                    _th_intern_get_data(e->u.marked_var.var)+1) ;
            }
            break ;
    }
}

unsigned *_th_get_marked_vars(struct _ex_intern *e, int *c)
{
    int i ;
    _var_list_count = 0 ;
    _get_marked_vars(e) ;
    for (i = 0; i < _var_list_count; ++i) {
        _th_intern_set_data(_var_list[i], 0) ;
    }
    *c = _var_list_count ;
    return _var_list ;
}

unsigned *_th_get_marked_vars_leave_marked(struct _ex_intern *e, int *c)
{
    _var_list_count = 0 ;
    _get_marked_vars(e) ;
    *c = _var_list_count ;
    return _var_list ;
}

#define ARG_INCREMENT 4000

static unsigned arg_start, arg_size ;
static struct _ex_intern **args, **all_args ;

_th_exp_util_init()
{
    arg_size = ARG_INCREMENT ;

    all_args = args =
        (struct _ex_intern **)MALLOC(sizeof(struct _ex_intern *) * arg_size) ;
    arg_start = 0 ;
}

static void set_start(int x)
{
    arg_start += x ;
    args = all_args + arg_start ;
}

static void check_size(unsigned size)
{
    if (arg_start + size > arg_size) {
        arg_size = arg_start + size + ARG_INCREMENT ;
        all_args = (struct _ex_intern **)REALLOC(all_args,sizeof(struct _ex_intern *) * arg_size) ;
        set_start(0) ;
    }
}

static int quant_level = 0;

static int has_marked_vars(struct _ex_intern *e)
{
    int i;

    switch (e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                if (has_marked_vars(e->u.appl.args[i])) return 1;
            }
            return 0;
        case EXP_MARKED_VAR:
            return 1;
        case EXP_QUANT:
            return 1;
        case EXP_CASE:
            return 1;
        case EXP_INDEX:
            return has_marked_vars(e->u.index.exp);
        default:
            return 0;
    }
}

struct _ex_intern *_th_mark_vars(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *res ;
    int i ;

    //printf("Marking %s\n", _th_print_exp(e));

    if (!quant_level) {
        if (e->marked_term) {
            //printf("Returning mbuffered %s\n", _th_print_exp(e->marked_term));
            return e->marked_term;
        }
    }

    switch (e->type) {
        case EXP_APPL:
            check_size(e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                set_start(e->u.appl.count) ;
                res = _th_mark_vars(env,e->u.appl.args[i]) ;
                set_start(0-e->u.appl.count) ;
                args[i] = res ;
            }
            res = _ex_intern_appl_equal_env(env,e->u.appl.functor,e->u.appl.count,args,e->type_inst) ;
            if (!quant_level) {
                e->is_marked_term = 1;
                e->marked_term = res;
            }
            //printf("Returning appl %s\n", _th_print_exp(res));
            //printf("Original appl %s\n", _th_print_exp(e));
            return res;
        case EXP_INDEX:
            res = _ex_intern_index(_th_mark_vars(env,e->u.index.exp),
                                   e->u.index.functor,e->u.index.term) ;
            if (!quant_level) {
                e->is_marked_term = 1;
                e->marked_term = res;
            }
            return res;
        case EXP_QUANT:
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])+1) ;
            }
            ++quant_level;
            res = _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,
                                   e->u.quant.vars,
                                   _th_mark_vars(env,e->u.quant.exp),
                                   _th_mark_vars(env,e->u.quant.cond)) ;
            --quant_level;
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])-1) ;
            }
            if (!quant_level) {
                e->is_marked_term = 1;
                e->marked_term = res;
            }
            return res;
        case EXP_CASE:
            check_size(e->u.case_stmt.count*2) ;
            for (i = 0; i < e->u.case_stmt.count *2; i+=2) {
                set_start(e->u.case_stmt.count*2) ;
                res = e->u.case_stmt.args[i] ;
                set_start(0-e->u.case_stmt.count*2) ;
                args[i] = res ;
                _th_increment_var_data(args[i]) ;
                set_start(e->u.case_stmt.count*2) ;
                res = _th_mark_vars(env,e->u.case_stmt.args[i+1]) ;
                set_start(0-e->u.case_stmt.count*2) ;
                args[i+1] = res ;
                _th_decrement_var_data(args[i]) ;
            }
            set_start(e->u.case_stmt.count*2) ;
            res = _th_mark_vars(env,e->u.case_stmt.exp);
            set_start(0-e->u.case_stmt.count*2) ;
            res = _ex_intern_case(res,e->u.case_stmt.count,args) ;
            if (!quant_level) {
                e->is_marked_term = 1;
                e->marked_term = res;
            }
            return res;
        case EXP_VAR:
            //printf("Var case %d\n", _th_intern_get_data(e->u.var));
            if (_th_intern_get_data(e->u.var)) {
                return e ;
            } else {
                res = _ex_intern_marked_var(e->u.var,_th_intern_get_quant_level(e->u.var)) ;
                if (quant_level==0) {
                    e->marked_term = res;
                    res->is_marked_term = 1;
                }
                //printf("Making var mark %s\n", _th_print_exp(res));
                //printf("    and %s\n", _th_print_exp(e));
                return res;
            }
        default:
            if (!quant_level) {
                e->marked_term = e;
                e->is_marked_term = 1;
            }
            return e ;
    }
}

struct _ex_intern *_th_remove_marked_vars(struct env *env, struct _ex_intern *e, int level)
{
    struct _ex_intern *res ;
    int i ;

    switch (e->type) {
        case EXP_APPL:
            check_size(e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                set_start(e->u.appl.count) ;
                res = _th_remove_marked_vars(env,e->u.appl.args[i], level) ;
                set_start(0-e->u.appl.count) ;
                args[i] = res ;
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args) ;
        case EXP_INDEX:
            return _ex_intern_index(_th_remove_marked_vars(env, e->u.index.exp, level),
                                    e->u.index.functor,e->u.index.term) ;
        case EXP_QUANT:
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])+1) ;
            }
            res = _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,
                                   e->u.quant.vars,
                                   _th_remove_marked_vars(env,e->u.quant.exp, level),
                                   _th_remove_marked_vars(env,e->u.quant.cond, level)) ;
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data2(e->u.quant.vars[i],
                    _th_intern_get_data2(e->u.quant.vars[i])-1) ;
            }
            return res ;
        case EXP_CASE:
            check_size(e->u.case_stmt.count*2) ;
            for (i = 0; i < e->u.case_stmt.count *2; i+=2) {
                set_start(e->u.case_stmt.count*2) ;
                res = e->u.case_stmt.args[i] ;
                set_start(0-e->u.case_stmt.count*2) ;
                args[i] = res ;
                _th_increment_var_data2(args[i]) ;
                set_start(e->u.case_stmt.count*2) ;
                res = _th_remove_marked_vars(env, e->u.case_stmt.args[i+1], level) ;
                set_start(0-e->u.case_stmt.count*2) ;
                _th_decrement_var_data2(args[i]) ;
                args[i+1] = res ;
            }
            set_start(e->u.case_stmt.count*2) ;
            res = _th_remove_marked_vars(env,e->u.case_stmt.exp, level) ;
            set_start(0-e->u.case_stmt.count*2) ;
            return _ex_intern_case(res,e->u.case_stmt.count,args) ;
        case EXP_VAR:
            if (_th_intern_get_quant_level(e->u.var) > level && _th_intern_get_data2(e->u.var)==0) {
                return _ex_intern_small_integer(0) ;
            } else {
                return e ;
            }
        default:
            return e ;
    }
}

struct _ex_intern *_th_unmark_vars(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *res ;
    int i ;

    //_zone_print_exp("Unmarking %s", e);
    //printf("Unmarking %s\n", _th_print_exp(e));
    if (e->unmarked_term && quant_level==0) {
        //printf("Returning buffered %s\n", _th_print_exp(e->marked_term));
        //_zone_print_exp("buffered", e->unmarked_term);
        return e->unmarked_term;
    }

    switch (e->type) {
        case EXP_APPL:
            check_size(e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                set_start(e->u.appl.count) ;
                res = _th_unmark_vars(env,e->u.appl.args[i]) ;
                set_start(0-e->u.appl.count) ;
                args[i] = res ;
            }
            res = _ex_intern_appl_equal_env(env,e->u.appl.functor,e->u.appl.count,args,e->type_inst) ;
            if (quant_level==0) {
                e->unmarked_term = res;
            }
            return res;
        case EXP_INDEX:
            res = _ex_intern_index(_th_unmark_vars(env,e->u.index.exp),
                                   e->u.index.functor,e->u.index.term) ;
            if (quant_level==0) {
                e->unmarked_term = res;
            }
            return res;
        case EXP_QUANT:
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])+1) ;
            }
            ++quant_level;
            res = _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,
                                   e->u.quant.vars,
                                   _th_unmark_vars(env,e->u.quant.exp),
                                   _th_unmark_vars(env,e->u.quant.cond)) ;
            --quant_level;
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])-1) ;
            }
            if (quant_level==0) {
                e->unmarked_term = res;
            }
            return res ;
        case EXP_CASE:
            check_size(e->u.case_stmt.count*2) ;
            for (i = 0; i < e->u.case_stmt.count*2; i+=2) {
                set_start(e->u.case_stmt.count*2) ;
                res = e->u.case_stmt.args[i] ;
                set_start(0-e->u.case_stmt.count*2) ;
                args[i] = res ;
                _th_increment_var_data(args[i]) ;
                set_start(e->u.case_stmt.count*2) ;
                res = _th_unmark_vars(env,e->u.case_stmt.args[i+1]) ;
                set_start(0-e->u.case_stmt.count*2) ;
                args[i+1] = res ;
                _th_decrement_var_data(args[i]) ;
            }
            set_start(e->u.case_stmt.count*2) ;
            res = _th_unmark_vars(env,e->u.case_stmt.exp) ;
            set_start(0-e->u.case_stmt.count*2) ;
            res = _ex_intern_case(res,e->u.case_stmt.count,args) ;
            if (quant_level==0) {
                e->unmarked_term = res;
            }
            return res ;
        case EXP_MARKED_VAR:
            if (_th_intern_get_data(e->u.var)) {
                return e ;
            } else {
                return _ex_intern_var(e->u.var) ;
            }
        default:
            return e ;
    }
}

struct _ex_intern *_th_rename_marked_vars(struct env *env,struct _ex_intern *e, unsigned oname, unsigned nname)
{
    struct _ex_intern *res ;
    int i ;

    switch (e->type) {
        case EXP_APPL:
            check_size(e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                set_start(e->u.appl.count) ;
                res = _th_rename_marked_vars(env,e->u.appl.args[i], oname, nname) ;
                set_start(0-e->u.appl.count) ;
                args[i] = res ;
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args) ;
        case EXP_INDEX:
            return _ex_intern_index(_th_rename_marked_vars(env,e->u.index.exp,oname,nname),
                                    e->u.index.functor,e->u.index.term) ;
        case EXP_QUANT:
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])+1) ;
            }
            res = _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,
                                   e->u.quant.vars,
                                   _th_rename_marked_vars(env,e->u.quant.exp,oname,nname),
                                   _th_rename_marked_vars(env,e->u.quant.cond,oname,nname)) ;
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])-1) ;
            }
            return res ;
        case EXP_CASE:
            check_size(e->u.case_stmt.count*2) ;
            for (i = 0; i < e->u.case_stmt.count*2; i+=2) {
                set_start(e->u.case_stmt.count*2) ;
                res = e->u.case_stmt.args[i] ;
                set_start(0-e->u.case_stmt.count*2) ;
                args[i] = res ;
                _th_increment_var_data(args[i]) ;
                set_start(e->u.case_stmt.count*2) ;
                res = _th_rename_marked_vars(env,e->u.case_stmt.args[i+1],oname,nname) ;
                set_start(0-e->u.case_stmt.count*2) ;
                args[i+1] = res ;
                _th_decrement_var_data(args[i]) ;
            }
            set_start(e->u.case_stmt.count*2) ;
            res = _th_rename_marked_vars(env,e->u.case_stmt.exp,oname,nname) ;
            set_start(0-e->u.case_stmt.count*2) ;
            return _ex_intern_case(res,e->u.case_stmt.count,args) ;
        case EXP_MARKED_VAR:
            if (_th_intern_get_data(e->u.var) || e->u.var != oname) {
                return e ;
            } else {
                return _ex_intern_marked_var(nname,0) ;
            }
        default:
            return e ;
    }
}

struct _ex_intern *_unmark_vars_list(struct env *env,struct _ex_intern *e)
{
    struct _ex_intern *res ;
    int i ;

    switch (e->type) {
        case EXP_APPL:
            check_size(e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                set_start(e->u.appl.count) ;
                res = _unmark_vars_list(env,e->u.appl.args[i]) ;
                set_start(0-e->u.appl.count) ;
                args[i] = res ;
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args) ;
        case EXP_INDEX:
            return _ex_intern_index(_unmark_vars_list(env,e->u.index.exp),
                                    e->u.index.functor,e->u.index.term) ;
        case EXP_QUANT:
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])+1) ;
            }
            res = _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,
                                   e->u.quant.vars,
                                   _unmark_vars_list(env,e->u.quant.exp),
                                   _unmark_vars_list(env,e->u.quant.cond)) ;
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])-1) ;
            }
            return res ;
        case EXP_CASE:
            check_size(e->u.case_stmt.count*2) ;
            for (i = 0; i < e->u.case_stmt.count*2; i+=2) {
                set_start(e->u.case_stmt.count*2) ;
                res = e->u.case_stmt.args[i] ;
                set_start(0-e->u.case_stmt.count*2) ;
                args[i] = res ;
                _th_increment_var_data(args[i]) ;
                set_start(e->u.case_stmt.count*2) ;
                res = _unmark_vars_list(env,e->u.case_stmt.args[i+1]) ;
                set_start(0-e->u.case_stmt.count*2) ;
                args[i+1] = res ;
                _th_decrement_var_data(args[i]) ;
            }
            set_start(e->u.case_stmt.count*2) ;
            res = _unmark_vars_list(env,e->u.case_stmt.exp) ;
            set_start(0-e->u.case_stmt.count*2) ;
            return _ex_intern_case(res,e->u.case_stmt.count,args) ;
        case EXP_MARKED_VAR:
            if (_th_intern_get_data(e->u.marked_var.var)!=0x40000000) {
                return e ;
            } else {
                return _ex_intern_var(e->u.marked_var.var) ;
            }
        default:
            return e ;
    }
}

struct _ex_intern *_th_unmark_vars_list(struct env *env,
                                        struct _ex_intern *e,int size,
                                        unsigned *l)
{
    int i ;

    for (i = 0; i <size; ++i) {
        _th_intern_set_data(l[i], 0x40000000) ;
    }
    e = _unmark_vars_list(env,e) ;
    for (i = 0; i <size; ++i) {
        _th_intern_set_data(l[i], 0) ;
    }
    return e ;
}

struct _ex_intern *_mark_vars_list(struct env *env,struct _ex_intern *e)
{
    struct _ex_intern *res ;
    int i ;

    switch (e->type) {
        case EXP_APPL:
            check_size(e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                set_start(e->u.appl.count) ;
                res = _mark_vars_list(env,e->u.appl.args[i]) ;
                set_start(0-e->u.appl.count) ;
                args[i] = res ;
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args) ;
        case EXP_INDEX:
            return _ex_intern_index(_mark_vars_list(env,e->u.index.exp),
                                    e->u.index.functor,e->u.index.term) ;
        case EXP_QUANT:
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])+1) ;
            }
            res = _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,
                                   e->u.quant.vars,
                                   _mark_vars_list(env,e->u.quant.exp),
                                   _mark_vars_list(env,e->u.quant.cond)) ;
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])-1) ;
            }
            return res ;
        case EXP_CASE:
            check_size(e->u.case_stmt.count*2) ;
            for (i = 0; i < e->u.case_stmt.count *2; i+=2) {
                set_start(e->u.case_stmt.count*2) ;
                res = e->u.case_stmt.args[i] ;
                set_start(0-e->u.case_stmt.count*2) ;
                args[i] = res ;
                _th_increment_var_data(args[i]) ;
                set_start(e->u.case_stmt.count*2) ;
                res = _mark_vars_list(env,e->u.case_stmt.args[i+1]) ;
                set_start(0-e->u.case_stmt.count*2) ;
                args[i+1] = res ;
                _th_decrement_var_data(args[i]) ;
            }
            set_start(e->u.case_stmt.count*2) ;
            res = _mark_vars_list(env,e->u.case_stmt.exp) ;
            set_start(0-e->u.case_stmt.count*2) ;
            return _ex_intern_case(res,e->u.case_stmt.count,args) ;
        case EXP_VAR:
            if (_th_intern_get_data(e->u.var)!=0x40000000) {
                return e ;
            } else {
                return _ex_intern_marked_var(e->u.var,_th_intern_get_quant_level(e->u.var)) ;
            }
        default:
            return e ;
    }
}

struct _ex_intern *_th_mark_vars_list(struct env *env,struct _ex_intern *e,int size,
                                        unsigned *l)
{
    int i ;

    for (i = 0; i < size; ++i) {
        _th_intern_set_data(l[i], 0x40000000) ;
    }
    e = _mark_vars_list(env,e) ;
    for (i = 0; i <size; ++i) {
        _th_intern_set_data(l[i], 0) ;
    }
    return e ;
}

struct _ex_intern *_th_mark_var(struct env *env,struct _ex_intern *e,unsigned v)
{
    _th_intern_set_data(v, 0x40000000) ;
    e = _mark_vars_list(env,e) ;
    _th_intern_set_data(v, 0) ;
    return e ;
}

struct _ex_intern *_th_unmark_var(struct env *env,struct _ex_intern *e,unsigned v)
{
    struct _ex_intern *res ;
    int i ;

    switch (e->type) {
        case EXP_APPL:
            check_size(e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                set_start(e->u.appl.count) ;
                res = _th_unmark_var(env,e->u.appl.args[i],v) ;
                set_start(0-e->u.appl.count) ;
                args[i] = res ;
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args) ;
        case EXP_INDEX:
            return _ex_intern_index(_th_unmark_var(env,e->u.index.exp,v),
                                    e->u.index.functor,e->u.index.term) ;
        case EXP_QUANT:
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])+1) ;
            }
            res = _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,
                                   e->u.quant.vars,
                                   _th_unmark_var(env,e->u.quant.exp,v),
                                   _th_unmark_var(env,e->u.quant.cond,v)) ;
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])-1) ;
            }
            return res ;
        case EXP_CASE:
            check_size(e->u.case_stmt.count*2) ;
            for (i = 0; i < e->u.case_stmt.count *2; i+=2) {
                set_start(e->u.case_stmt.count*2) ;
                res = e->u.case_stmt.args[i] ;
                set_start(0-e->u.case_stmt.count*2) ;
                args[i] = res ;
                _th_increment_var_data(args[i]) ;
                set_start(e->u.case_stmt.count*2) ;
                res = _th_unmark_var(env,e->u.case_stmt.args[i+1],v) ;
                set_start(0-e->u.case_stmt.count*2) ;
                args[i+1] = res ;
                _th_decrement_var_data(args[i]) ;
            }
            set_start(e->u.case_stmt.count*2) ;
            res = _th_unmark_var(env,e->u.case_stmt.exp,v) ;
            set_start(0-e->u.case_stmt.count*2) ;
            return _ex_intern_case(res,e->u.case_stmt.count,args) ;
        case EXP_MARKED_VAR:
            if (_th_intern_get_data(e->u.var) && e->u.var==v) {
                return e ;
            } else {
                return _ex_intern_var(e->u.var) ;
            }
        default:
            return e ;
    }
}

unsigned na(unsigned var)
{
    char name[200] ;
    char *n ;
    int i ;
    unsigned v ;

    n = _th_intern_decode(var) ;
    v = var ;
    i = 0 ;
    while (_th_intern_get_data(v)) {
        sprintf(name, "%s%d", n, i++) ;
        v = _th_intern(name) ;
    }
    return v ;
}
unsigned _name_away(unsigned var)
{
    int i ;

    var = na(var) ;
    for (i = 0; i < _var_list_count; ++i) {
        _th_intern_set_data(_var_list[i],0) ;
    }
    return var ;
}

unsigned _th_name_away_from_list(int count,unsigned *vars,unsigned var)
{
    int i ;

    _var_list_count = 0 ;
    for (i = 0; i < count; ++i) {
        add_var(vars[i]) ;
        _th_intern_set_data(vars[i],1) ;
    }
    return _name_away(var) ;
}

unsigned _th_name_away(struct _ex_intern *e,unsigned var)
{
    //printf("name_away %s %s\n", _th_print_exp(e), _th_intern_decode(var));
    _get_free_vars(e) ;
    return _name_away(var) ;
}

void _th_multi_name_away(struct _ex_intern *e,unsigned var, int count, unsigned *array)
{
    int i ;

    _get_free_vars(e) ;
    for (i = 0; i < count; ++i) {
        array[i] = na(var) ;
        _th_intern_set_data(array[i],1) ;
    }
    for (i = 0; i < _var_list_count; ++i) {
        _th_intern_set_data(_var_list[i],0) ;
    }
    for (i = 0; i < count; ++i) {
        _th_intern_set_data(array[i],0) ;
    }
}

struct _ex_intern *_th_get_term(struct _ex_intern *e, int count, int *index)
{
    if (count==0) return e ;

    switch (e->type) {
        case EXP_APPL:
            if (index[0] >= e->u.appl.count) return NULL ;
            return _th_get_term(e->u.appl.args[index[0]], count-1, index+1) ;
        case EXP_QUANT:
            if (index[0] >= 2) return NULL ;
            if (index[0]==0) {
                return _th_get_term(e->u.quant.exp, count-1, index+1) ;
            } else if (index[0]==1) {
                return _th_get_term(e->u.quant.cond, count-1, index+1) ;
            } else {
                return NULL ;
            }
        case EXP_CASE:
            if (index[0] > e->u.case_stmt.count*2) return NULL ;
            if (index[0]==0) {
                return _th_get_term(e->u.case_stmt.exp, count-1, index+1) ;
            } else {
                return _th_get_term(e->u.case_stmt.args[index[0]-1], count-1, index+1) ;
            }
        default:
            return NULL ;
    }
}

struct _ex_intern *_th_replace_term(struct env *env, struct _ex_intern *e, int count, int *index,struct _ex_intern *r)
{
    struct _ex_intern **args, *exp, *cond ;
    int i ;

    if (count==0) return r ;

    switch (e->type) {
        case EXP_APPL:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                if (i==index[0]) {
                    args[i] = _th_replace_term(env,e->u.appl.args[i],count-1,index+1,r) ;
                } else {
                    args[i] = e->u.appl.args[i] ;
                }
            }
            return _ex_intern_appl_env(env, e->u.appl.functor, e->u.appl.count, args) ;
        case EXP_QUANT:
            if (index[0]==0) {
                exp = _th_replace_term(env,e->u.quant.exp,count-1,index+1,r) ;
                cond = e->u.quant.cond ;
            } else if (index[0]==1) {
                exp = e->u.quant.exp ;
                cond = _th_replace_term(env,e->u.quant.cond,count-1,index+1,r) ;
            } else {
                return e ;
            }
            return _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,e->u.quant.vars,exp,cond) ;
        case EXP_CASE:
            if (index[0]==0) {
                return _ex_intern_case(_th_replace_term(env,e->u.case_stmt.exp,count-1,index+1,r),
                                       e->u.case_stmt.count,e->u.case_stmt.args) ;
            } else {
                args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
                for (i = 0; i < e->u.case_stmt.count*2; ++i) {
                    if (index[0]==i+1) {
                        args[i] = _th_replace_term(env,e->u.case_stmt.args[i],count-1,index+1,r) ;
                    } else {
                        args[i] = e->u.case_stmt.args[i] ;
                    }
                }
                return _ex_intern_case(e->u.case_stmt.exp,e->u.case_stmt.count,args) ;
            }
        default:
            return e ;
    }
}

