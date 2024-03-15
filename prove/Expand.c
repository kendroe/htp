/*
 * expand.c
 *
 * Routines for expanding a variable and inserting universal conditions for a
 * proof.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdio.h>
#include <stdlib.h>
#include "Globalsp.h"

static struct _ex_intern **result;
static int result_size = 0;

static void check_size(int x)
{
    if (result_size < x) {
        if (result_size > 0) FREE(result) ;
        result = (struct _ex_intern **)MALLOC(sizeof(struct _ex_intern *) * x) ;
        result_size = x ;
    }
}

static struct _ex_intern *vsub ;

static struct _ex_intern *subst_info(struct env *env, struct _ex_intern *e, unsigned v, struct _ex_intern *t)
{
    struct _ex_intern **vars = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * t->u.appl.count) ;
    char s[100] ;
    int i ;
    unsigned vv ;
    struct _ex_unifier *u ;
    char *mark ;

    for (i = 0; i < t->u.appl.count; ++i) {
        sprintf(s, "v%d_", i) ;
        vv = _th_intern(s) ;
        vv = _th_name_away(e, vv) ;
        vars[i] = _ex_intern_var(vv) ;
    }
    vsub = _ex_intern_appl_env(env,t->u.appl.functor,t->u.appl.count,vars) ;

    mark = _th_alloc_mark(DERIVATION_BASE) ;

    u = _th_new_unifier(DERIVATION_BASE) ;
    u = _th_add_pair(DERIVATION_BASE,u,v,vsub) ;
    e = _th_subst(env,u,e) ;

    _th_alloc_release(DERIVATION_BASE, mark) ;

    return e ;
}

struct _ex_intern **_th_expand_var(int space, struct env *env, struct _ex_intern *e, unsigned var, unsigned count, unsigned *index)
{
    struct _ex_unifier *t = _th_checkTyping(env, _th_parse(env, "(Bool)"), e) ;
    struct _ex_intern *r = _th_exp_var_type(t, var, count, index) ;
    int i ;

    if (r->u.appl.functor==INTERN_INT||r->u.appl.functor==INTERN_REAL||
        r->u.appl.functor==INTERN_STRING) {
        return NULL ;
    } else {
        struct _ex_intern *t = _th_get_type_definition(env,r->u.appl.functor);
        if (t==NULL) return NULL ;
        check_size(t->u.appl.count*2+1) ;
        if (count==0) {
            for (i = 0; i < t->u.appl.count; ++i) {
                struct _ex_intern *args[2] ;
                result[i*2] = subst_info(env, e, var, t->u.appl.args[i]) ;
                args[0] = _ex_intern_var(var) ;
                args[1] = vsub ;
                result[i*2+1] = _ex_intern_appl_env(env,INTERN_EQUAL,2,args) ;
            }
            result[i*2] = NULL ;
        } else {
            struct _ex_intern *st = _th_get_term(e, count, index) ;
            if (st->type==EXP_QUANT) {
                struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * t->u.appl.count) ;
                struct _ex_intern **args_vsub = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * t->u.appl.count) ;
                struct _ex_intern *tmp[2] ;
                unsigned *vars ;
                int j, vc, k ;
                for (i = 0; i < t->u.appl.count; ++i) {
                    tmp[0] = st->u.quant.exp ;
                    tmp[1] = st->u.quant.cond ;
                    args[i] = subst_info(env,_ex_intern_appl_env(env,INTERN_AND,2,tmp), var, t->u.appl.args[i]) ;
                    vc = vsub->u.appl.count + st->u.quant.var_count - 1 ;
                    vars = (unsigned *)ALLOCA(sizeof(unsigned) * vc) ;
                    for (j = 0, k = 0; j < st->u.quant.var_count; ++j) {
                        if (st->u.quant.vars[j] != var) vars[k++] = st->u.quant.vars[j] ;
                    }
                    for (j = 0; j < vsub->u.appl.count; ++j) {
                        vars[j+st->u.quant.var_count-1] = vsub->u.appl.args[j]->u.var ;
                    }
                    args[i] = _ex_intern_quant(st->u.quant.quant,vc,vars,args[i]->u.appl.args[0],args[i]->u.appl.args[1]) ;
                    tmp[0] = _ex_intern_var(var) ;
                    tmp[1] = vsub ;
                    args_vsub[i] = _ex_intern_appl_env(env,INTERN_EQUAL,2,tmp) ;
                }
                switch (st->u.quant.quant) {
                    case INTERN_EXISTS: j = INTERN_OR    ; break ;
                    case INTERN_ALL:    j = INTERN_AND   ; break ;
                    case INTERN_SETQ:   j = INTERN_UNION ; break ;
                }
                result[0] = _ex_intern_appl_env(env, j, i, args) ;
                result[1] = _ex_intern_appl_env(env, INTERN_OR, i, args_vsub) ;
                result[2] = NULL ;
            } else {
                struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (t->u.appl.count * 2)) ;
                struct _ex_intern **args_vsub = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * t->u.appl.count) ;
                struct _ex_intern *tmp[2] ;
                ++index[count-1] ;
                st = _th_get_term(e,count,index) ;
                for (i = 0; i < t->u.appl.count; ++i) {
                    args[i*2+1] = subst_info(env, st, var, t->u.appl.args[i]) ;
                    args[i*2] = vsub ;
                    tmp[0] = _ex_intern_var(var) ;
                    tmp[1] = vsub ;
                    args_vsub[i] = _ex_intern_appl_env(env,INTERN_EQUAL,2,tmp) ;
                }
                result[0] = _ex_intern_case(_ex_intern_var(var), i, args) ;
                result[1] = _ex_intern_appl_env(env, INTERN_OR, i, args_vsub) ;
                result[2] = NULL ;
                --index[count-1] ;
            }
        }
        return result ;
    }
}

#define DEPTH_INCREMENT 100

static int height = 0;
static int current_size = 0;
static unsigned *stack = NULL;

static void check_depth(int size)
{
   if (size > current_size) {
       current_size += DEPTH_INCREMENT ;
       stack = (int *)realloc(stack, sizeof(int) * DEPTH_INCREMENT) ;
   }
}

static void push_index(int index)
{
    check_depth(height+1) ;
    stack[height++] = index ;
}

static void pop_index()
{
    --height ;
}

static unsigned total_var_count(struct _ex_intern *e)
{
    int i, total ;

    switch (e->type) {
        case EXP_VAR:
            return 1 ;
        case EXP_APPL:
            total = 0 ;
            for (i = 0; i < e->u.appl.count; ++i) {
                total += total_var_count(e->u.appl.args[i]) ;
            }
            return total ;
        default:
            return 0 ;
    }
}

static int bound_var_count(struct _ex_intern *e)
{
    int i, total;

    switch (e->type) {

        case EXP_APPL:
            total = 0 ;
            for (i = 0; i < e->u.appl.count; ++i) {
                total += bound_var_count(e->u.appl.args[i]) ;
            }
            return total ;
        case EXP_QUANT:
            return bound_var_count(e->u.quant.cond) +
                   bound_var_count(e->u.quant.exp) +
                   e->u.quant.var_count ;
        case EXP_CASE:
            total = bound_var_count(e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count; ++i) {
                total += total_var_count(e->u.case_stmt.args[i*2]) +
                         bound_var_count(e->u.case_stmt.args[i*2+1]) ;
            }
            return total ;
        default:
            return 0 ;
    }
}

static void add_case_vars(int space, unsigned **res, int *pos, struct _ex_intern *e) 
{
    int i ;

    switch (e->type) {
        case EXP_VAR:
            res[*pos] = (unsigned *)_th_alloc(space, sizeof(unsigned) * (2 + height)) ;
            res[*pos][0] = e->u.var ;
            res[*pos][1] = height ;
            for (i = 0; i < height; ++i) {
                res[*pos][i+2] = stack[i] ;
            }
            ++*pos ;
            break ;
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                add_case_vars(space, res, pos, e->u.appl.args[i]) ;
            }
            break ;
    }
}

static void add_bound_vars(int space, unsigned **res, int *pos, struct _ex_intern *e)
{
    int i, j ;

    switch (e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                push_index(i) ;
                add_bound_vars(space, res, pos, e->u.appl.args[i]) ;
                pop_index() ;
            }
            break ;
        case EXP_QUANT:
            for (i = 0; i < e->u.quant.var_count; ++i) {
                 res[*pos] = (unsigned *)_th_alloc(space, sizeof(unsigned) * (2 + height)) ;
                 res[*pos][0] = e->u.quant.vars[i] ;
                 res[*pos][1] = height ;
                 for (j = 0; j < height; ++j) {
                     res[*pos][j+2] = stack[j] ;
                 }
                 ++*pos ;
            }
            push_index(0) ;
            add_bound_vars(space, res, pos, e->u.quant.exp) ;
            pop_index() ;
            push_index(1) ;
            add_bound_vars(space, res, pos, e->u.quant.cond) ;
            pop_index() ;
            break ;
        case EXP_CASE:
            push_index(0) ;
            add_bound_vars(space, res, pos, e->u.case_stmt.exp) ;
            pop_index() ;
            for (i = 0; i < e->u.case_stmt.count; ++i) {
                push_index(i*2+1) ;
                add_case_vars(space, res, pos, e->u.case_stmt.args[i*2]) ;
                pop_index() ;
                push_index(i*2+2) ;
                add_bound_vars(space, res, pos, e->u.case_stmt.args[i*2+1]) ;
                pop_index() ;
            }
            break ;
    }
}

unsigned **_th_get_expandable_variables(int space, struct _ex_intern *e, int *count)
{
    unsigned *fv = _th_get_free_vars(e, count) ;
    int i, bvc = bound_var_count(e) ;
    unsigned **res = (unsigned **)_th_alloc(space, sizeof(unsigned *) * (*count + bvc)) ;

    for (i = 0; i < *count; ++i) {
        res[i] = (unsigned *)_th_alloc(space, sizeof(unsigned) * 2) ;
        res[i][0] = fv[i] ;
        res[i][1] = 0 ;
    }

    *count += bvc ;

    add_bound_vars(space, res, &i, e) ;

    return res ;
}

static int count_universal_positions(struct _ex_intern *e)
{
    int i, total ;

    switch (e->type) {
        case EXP_APPL:
            total = 0 ;
            for (i = 0; i < e->u.appl.count; ++i) {
                total += count_universal_positions(e->u.appl.args[i]) ;
            }
            return total ;
        case EXP_QUANT:
            return 1 + count_universal_positions(e->u.quant.exp) +
                       count_universal_positions(e->u.quant.cond) ;
        case EXP_CASE:
            total = count_universal_positions(e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count; ++i) {
                total += count_universal_positions(e->u.case_stmt.args[i*2+1]) ;
            }
            return total + e->u.case_stmt.count ;
        default:
            return 0 ;
    }
}

static void get_sub_positions(int space, unsigned **res, int *pos, struct _ex_intern *e)
{
    int i, j ;

    switch (e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                push_index(i) ;
                get_sub_positions(space,res,pos,e->u.appl.args[i]) ;
                pop_index() ;
            }
            break ;
        case EXP_QUANT:
            push_index(0) ;
            res[*pos] = (unsigned *)_th_alloc(space, sizeof(unsigned) * (height+1)) ;
            res[*pos][0] = height ;
            for (i = 0; i < height; ++i) {
                res[*pos][i+1] = stack[i] ;
            }
            ++*pos ;
            get_sub_positions(space,res,pos,e->u.quant.exp) ;
            pop_index();
            push_index(1) ;
            res[*pos] = (unsigned *)_th_alloc(space, sizeof(unsigned) * (height+1)) ;
            res[*pos][0] = height ;
            for (i = 0; i < height; ++i) {
                res[*pos][i+1] = stack[i] ;
            }
            ++*pos ;
            get_sub_positions(space,res,pos,e->u.quant.cond) ;
            pop_index();
            break ;
        case EXP_CASE:
            push_index(0) ;
            get_sub_positions(space,res,pos,e->u.case_stmt.exp) ;
            pop_index() ;
            for (i = 0; i < e->u.case_stmt.count; ++i) {
                push_index(i*2+2) ;
                res[*pos] = (unsigned *)_th_alloc(space, sizeof(unsigned) * (height+1)) ;
                res[*pos][0] = height ;
                for (j = 0; j < height; ++j) {
                    res[*pos][j+1] = stack[j] ;
                }
                ++*pos ;
                get_sub_positions(space,res,pos,e->u.case_stmt.args[i*2+1]) ;
                pop_index() ;
            }
            break ;
    }
}

unsigned **_th_get_universal_positions(int space, struct _ex_intern *e, int *c)
{
    int count = 1 + count_universal_positions(e) ;
    unsigned **res = (unsigned **)_th_alloc(space, sizeof(unsigned *) * count) ;
    int i = 1 ;

    res[0] = (unsigned *)_th_alloc(space, sizeof(unsigned)) ;
    res[0][0] = 0 ;
    *c = count ;
    get_sub_positions(space,res,&i,e) ;

    return res ;
}

struct _ex_intern **_th_expand_universal(int space, struct env *env, struct _ex_intern *e, struct _ex_intern *cond, unsigned count, unsigned *index)
{
    if (count==0) {
        struct _ex_intern *args[3] ;
        check_size(5) ;
        args[0] = cond ;
        args[1] = e->u.appl.args[2] ;
        args[2] = _th_flatten_top(env, _ex_intern_appl_env(env,INTERN_AND,2,args)) ;
        args[0] = e->u.appl.args[0] ;
        args[1] = e->u.appl.args[1] ;
        result[0] = _ex_intern_appl_env(env, e->u.appl.functor,3,args) ;
        args[0] = cond ;
        args[0] = _ex_intern_appl_env(env,INTERN_NOT,1,args) ;
        args[1] = e->u.appl.args[2] ;
        args[2] = _th_flatten_top(env, _ex_intern_appl_env(env,INTERN_AND,2,args)) ;
        args[0] = e->u.appl.args[0] ;
        args[1] = e->u.appl.args[1] ;
        result[2] = _ex_intern_appl_env(env, e->u.appl.functor,3,args) ;
        result[1] = cond ;
        result[3] = _ex_intern_appl_env(env,INTERN_NOT,1,result+1) ;
        result[4] = NULL ;
        return result ;
    } else {
        struct _ex_intern *args[4] ;
        args[0] = _ex_true ;
        args[2] = _ex_false ;
        args[1] = args[3] = _th_get_term(e,count,index) ;
        result[0] = _th_replace_term(env,e,count,index,_ex_intern_case(cond,2,args)) ;
        args[1] = _ex_false ;
        result[1] = _ex_intern_appl_env(env,INTERN_OR,2,args) ;
        result[2] = NULL ;
        return result ;
    }
}

static int count_all_positions(struct _ex_intern *e)
{
    int i, total ;

    switch (e->type) {
        case EXP_APPL:
            total = 1 ;
            for (i = 0; i < e->u.appl.count; ++i) {
                total += count_all_positions(e->u.appl.args[i]) ;
            }
            return total ;
        case EXP_QUANT:
            return 1 + count_all_positions(e->u.quant.exp) +
                       count_all_positions(e->u.quant.cond) ;
        case EXP_CASE:
            total = count_all_positions(e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count; ++i) {
                total += count_all_positions(e->u.case_stmt.args[i*2])
                      + count_all_positions(e->u.case_stmt.args[i*2+1]) ;
            }
            return total + e->u.case_stmt.count * 2 + 1 ;
        default:
            return 1 ;
    }
}

static void get_all_positions(int space, unsigned **res, int *pos, struct _ex_intern *e)
{
    int i ;

    res[*pos] = (unsigned *)_th_alloc(space, sizeof(unsigned) * (height+1)) ;
    res[*pos][0] = height ;
    for (i = 0; i < height; ++i) {
        res[*pos][i+1] = stack[i] ;
    }
    ++*pos ;

    switch (e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                push_index(i) ;
                get_all_positions(space,res,pos,e->u.appl.args[i]) ;
                pop_index() ;
            }
            break ;
        case EXP_QUANT:
            push_index(0) ;
            get_all_positions(space,res,pos,e->u.quant.exp) ;
            pop_index();
            push_index(1) ;
            get_all_positions(space,res,pos,e->u.quant.cond) ;
            pop_index();
            break ;
        case EXP_CASE:
            push_index(0) ;
            get_all_positions(space,res,pos,e->u.case_stmt.exp) ;
            pop_index() ;
            for (i = 0; i < e->u.case_stmt.count; ++i) {
                push_index(i*2+1) ;
                get_all_positions(space,res,pos,e->u.case_stmt.args[i*2]) ;
                pop_index() ;
                push_index(i*2+2) ;
                get_all_positions(space,res,pos,e->u.case_stmt.args[i*2+1]) ;
                pop_index() ;
            }
            break ;
    }
}

unsigned **_th_get_all_positions(int space, struct _ex_intern *e, unsigned *count)
{
    unsigned **res ;
    int pos = 0;

    *count = count_all_positions(e) ;

    res = (unsigned **)_th_alloc(space, sizeof(unsigned *) * (*count)) ;

    get_all_positions(space, res, &pos, e) ;

    return res ;
}

