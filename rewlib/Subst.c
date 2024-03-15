/*
 * subst.c
 *
 * Variable substitution functions.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>

#include "Globals.h"
#include "Intern.h"

#define TABLE_SIZE 11

struct _entry {
    struct _entry *next ;
    unsigned var ;
    struct _ex_intern *exp ;
} ;

struct _ex_unifier {
    struct _entry *table[TABLE_SIZE] ;
} entry ;

struct _ex_unifier *_th_new_unifier(unsigned space)
{
    int i ;
    struct _ex_unifier *u ;

    u = (struct _ex_unifier *)_th_alloc(space, sizeof(struct _ex_unifier)) ;

    for (i = 0; i < TABLE_SIZE; ++i) {
         u->table[i] = NULL ;
    }

    return u ;

}

struct _ex_unifier *_th_add_pair(unsigned space, struct _ex_unifier *u, unsigned v, struct _ex_intern *e)
{
    int i = v%TABLE_SIZE ;
    struct _entry *entry = (struct _entry *)_th_alloc(space,sizeof(struct _entry)) ;
    entry->next = u->table[i] ;
    u->table[i] = entry ;
    entry->var = v ;
    entry->exp = e ;

    return u ;
}

struct iterator {
        struct _ex_unifier *u ;
        struct _entry *entry ;
        int pos;
    } ;

void *_th_dom_init(int space, struct _ex_unifier *u)
{
    struct iterator *iter = (struct iterator *)_th_alloc(space,sizeof(struct iterator)) ;

    iter->u = u ;
    iter->entry = NULL ;
    iter->pos = 0 ;

    return (void *)iter ;
}

unsigned _th_dom_next(void *it)
{
    struct iterator *iter = (struct iterator *)it ;
    unsigned r ;
    int i ;

    if (iter->entry != NULL) {
        r = iter->entry->var ;
        iter->entry = iter->entry->next ;
        return r ;
    } else {
        for (i = iter->pos; i < TABLE_SIZE; ++i) {
            if (iter->u->table[i] != NULL) {
                r = iter->u->table[i]->var ;
                iter->entry = iter->u->table[i]->next ;
                iter->pos = i+1 ;
                return r ;
            }
        }
        return 0 ;
    }
}

struct _entry *_th_copy_entry(unsigned zone, struct _entry *orig)
{
    struct _entry *new_entry ;

    if (orig==NULL) return NULL ;

    new_entry = (struct _entry *)_th_alloc(zone,sizeof(struct _entry)) ;
    new_entry->next = _th_copy_entry(zone, orig->next) ;
    new_entry->var = orig->var ;
    new_entry->exp = orig->exp ;

    return new_entry ;
}

struct _ex_unifier *_th_copy_unifier(unsigned zone, struct _ex_unifier *orig)
{
    struct _ex_unifier *new_unifier ;
    int i ;

    if (orig==NULL) return NULL ;

    new_unifier = (struct _ex_unifier *)_th_alloc(zone,sizeof(struct _ex_unifier)) ;
    for (i = 0; i < TABLE_SIZE; ++i) {
        new_unifier->table[i] = _th_copy_entry(zone,orig->table[i]) ;
    }

    return new_unifier ;
}

void _th_print_unifier(struct _ex_unifier *u)
{
    int i ;
    struct _entry *e ;

    for (i = 0; i < TABLE_SIZE; ++i) {
        e = u->table[i] ;
        while(e != NULL) {
            printf("%s->%s ", _th_intern_decode(e->var), _th_print_exp(e->exp)) ;
            e = e->next ;
        }
    }
    printf("\n") ;
}

struct _ex_intern *_th_unifier_as_exp(struct env *env, struct _ex_unifier *u)
{
    int i ;
    struct _entry *e ;
    int count = 0 ;
    struct _ex_intern **args ;

    for (i = 0; i < TABLE_SIZE; ++i) {
        e = u->table[i] ;
        while(e != NULL) {
            ++count ;
            e = e->next ;
        }
    }

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count) ;
    count = 0 ;

    for (i = 0; i < TABLE_SIZE; ++i) {
        e = u->table[i] ;
        while(e != NULL) {
            args[count++] = _ex_intern_appl2_env(env,INTERN_T,_ex_intern_var(e->var),e->exp) ;
            e = e->next ;
        }
    }

    return _ex_intern_appl_env(env,INTERN_T,count,args) ;
}

void _th_zone_print_unifier(struct _ex_unifier *u)
{
    int i ;
    struct _entry *e ;

    if (u==NULL) {
        _zone_print0("Unifier: NULL") ;
        return ;
    }

    _zone_print0("Unifier:");
    _tree_indent();
    for (i = 0; i < TABLE_SIZE; ++i) {
        e = u->table[i] ;
        while(e != NULL) {
            _zone_print2("%s->%s", _th_intern_decode(e->var), _th_print_exp(e->exp)) ;
            if (e->exp==NULL || e->var==0) {
                printf("zone_print_unifier failure\n") ;
                exit(1) ;
            }
            e = e->next ;
        }
    }
    _tree_undent();
}

void _th_tree_print_unifier(struct _ex_unifier *u)
{
    int i ;
    struct _entry *e ;

    for (i = 0; i < TABLE_SIZE; ++i) {
        e = u->table[i] ;
        while(e != NULL) {
            _tree_print2("%s->%s ", _th_intern_decode(e->var), _th_print_exp(e->exp)) ;
            e = e->next ;
        }
    }
    printf("\n") ;
}

struct _ex_unifier *_th_shallow_copy_unifier(unsigned zone, struct _ex_unifier *orig)
{
    struct _ex_unifier *new_unifier ;
    int i ;

    if (orig==NULL) return NULL ;

    new_unifier = (struct _ex_unifier *)_th_alloc(zone,sizeof(struct _ex_unifier)) ;
    for (i = 0; i < TABLE_SIZE; ++i) {
        new_unifier->table[i] = orig->table[i] ;
    }

    return new_unifier ;
}

struct _ex_intern *_th_apply_entry(struct _entry *u,unsigned v)
{
    if (u==NULL) return NULL ;

    if (u->var != v) return _th_apply_entry(u->next, v) ;

    return u->exp ;
}

struct _ex_intern *_th_apply(struct _ex_unifier *u,unsigned v)
{
    return _th_apply_entry(u->table[v%TABLE_SIZE],v) ;
}

static unsigned arg_start, arg_size ;
static struct _ex_intern **args, **all_args ;

#define ARG_INCREMENT 4000

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

static struct _ex_intern *_replace(struct env *env,unsigned var, struct _ex_intern *rep, struct _ex_intern *e)
{
    struct _ex_intern *res ;
    int i ;

    switch (e->type) {
        case EXP_APPL:
            check_size(e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                set_start(e->u.appl.count) ;
                res = _replace(env,var,rep,e->u.appl.args[i]) ;
                set_start(0-e->u.appl.count) ;
                args[i] = res ;
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args) ;
        case EXP_INDEX:
            return _ex_intern_index(_replace(env,var,rep,e->u.index.exp),
                                    e->u.index.functor,e->u.index.term) ;
        case EXP_QUANT:
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data2(e->u.quant.vars[i],
                    _th_intern_get_data2(e->u.quant.vars[i])+1) ;
            }
            res = _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,
                                   e->u.quant.vars,
                                   _replace(env,var,rep,e->u.quant.exp),
                                   _replace(env,var,rep,e->u.quant.cond)) ;
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
                res = _replace(env,var,rep,e->u.case_stmt.args[i+1]) ;
                set_start(0-e->u.case_stmt.count*2) ;
                args[i+1] = res ;
                _th_decrement_var_data2(args[i]) ;
            }
            return _ex_intern_case(_replace(env,var,rep,e->u.case_stmt.exp),e->u.case_stmt.count,args) ;
        case EXP_VAR:
            if (_th_intern_get_data2(e->u.var)) {
                return e ;
            } else {
                if (e->u.var==var) {
                    return rep ;
                } else {
                    return e ;
                }
            }
        default:
            return e ;
    }
}

static void _update_unifier(struct env *env,unsigned var,struct _ex_intern *rep, struct _entry *e)
{
    if (e==NULL) return ;

    e->exp = _replace(env,var,rep,e->exp) ;
    _update_unifier(env,var,rep,e->next) ;
}

void _th_update_unifier(struct env *env,unsigned var, struct _ex_intern *rep, struct _ex_unifier *u)
{
    int i ;

    for (i = 0; i < TABLE_SIZE; ++i) _update_unifier(env,var,rep,u->table[i]) ;
}


struct _ex_intern *_th_marked_subst(struct env *env,struct _ex_unifier *u, struct _ex_intern *e)
{
    struct _ex_intern *res ;
    int i ;

    switch (e->type) {
        case EXP_APPL:
            check_size(e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                set_start(e->u.appl.count) ;
                res = _th_marked_subst(env,u,e->u.appl.args[i]) ;
                set_start(0-e->u.appl.count) ;
                args[i] = res ;
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args) ;
        case EXP_INDEX:
            return _ex_intern_index(_th_marked_subst(env,u,e->u.index.exp),
                                    e->u.index.functor,e->u.index.term) ;
        case EXP_QUANT:
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])+1) ;
            }
            res = _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,
                                   e->u.quant.vars,
                                   _th_marked_subst(env,u,e->u.quant.exp),
                                   _th_marked_subst(env,u,e->u.quant.cond)) ;
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
                res = _th_marked_subst(env,u,e->u.case_stmt.args[i+1]) ;
                set_start(0-e->u.case_stmt.count*2) ;
                args[i+1] = res ;
                _th_decrement_var_data(args[i]) ;
            }
            return _ex_intern_case(_th_marked_subst(env,u,e->u.case_stmt.exp),e->u.case_stmt.count,args) ;
        case EXP_MARKED_VAR:
            res = _th_apply(u,e->u.var) ;
            if (res==NULL) {
                return e ;
            } else {
                return res ;
            }
        default:
            return e ;
    }
}

static struct _ex_intern *_subst(struct env *env,struct _ex_unifier *u, struct _ex_intern *e)
{
    struct _ex_intern *res ;
    int i ;

    switch (e->type) {
        case EXP_APPL:
            check_size(e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                set_start(e->u.appl.count) ;
                res = _subst(env,u,e->u.appl.args[i]) ;
                set_start(0-e->u.appl.count) ;
                args[i] = res ;
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args) ;
        case EXP_INDEX:
            return _ex_intern_index(_subst(env,u,e->u.index.exp),
                                    e->u.index.functor,e->u.index.term) ;
        case EXP_QUANT:
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_set_data(e->u.quant.vars[i],
                    _th_intern_get_data(e->u.quant.vars[i])+1) ;
            }
            res = _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,
                                   e->u.quant.vars,
                                   _subst(env,u,e->u.quant.exp),
                                   _subst(env,u,e->u.quant.cond)) ;
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
                res = _subst(env,u,e->u.case_stmt.args[i+1]) ;
                set_start(0-e->u.case_stmt.count*2) ;
                args[i+1] = res ;
                _th_decrement_var_data(args[i]) ;
            }
            set_start(e->u.case_stmt.count*2) ;
            res = _subst(env,u,e->u.case_stmt.exp) ;
            set_start(0-e->u.case_stmt.count*2) ;
            return _ex_intern_case(res,e->u.case_stmt.count,args) ;
        case EXP_VAR:
            if (_th_intern_get_data(e->u.var)) {
                return e ;
            } else {
                res = _th_apply(u,e->u.var) ;
                if (res==NULL) {
                    return e ;
                } else {
                    return res ;
                }
            }
        default:
            return e ;
    }
}

struct _ex_intern *_th_subst(struct env *env,struct _ex_unifier *u,struct _ex_intern *e)
{
    /*_th_clear_var_data(e) ;*/
    return _subst(env,u,e) ;
}

