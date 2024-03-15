/*#define DEBUG*/
/*
 * transitive.c
 *
 * Routines for simplifying expressions involving transitive operators.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdio.h>
#include <stdlib.h>
#include <search.h>
#include <string.h>

#include "Globals.h"
#include "Intern.h"

#define TRANS_HASH_SIZE 99

struct _const_list {
        struct _const_list *next ;
        struct _ex_intern *e ;
    } ;

struct _ex_list {
        struct _ex_list *next ;
        struct _ex_intern *e ;
        struct _ex_list *child1, *child2 ;
        struct _ex_list *left_next, *right_next ;
        int unused : 1 ;
    } ;

struct _term_list {
        struct _term_list *next ;
        struct _ex_intern *e ;
        struct _ex_list *exps ;
    } ;

struct _unions {
    struct _ex_list *term ;
    struct _unions *next ;
} ;

struct _union_list {
        struct _ex_intern *e ;
        struct _unions *unions;
        struct _union_list *next ;
} ;

struct _attrib_list {
        struct _attrib_list *next ;
        struct parameter *parameters ;
        unsigned attrib ;
        int count ;
    } ;

static struct _ex_list *env_terms[TRANS_HASH_SIZE] ;
struct _union_list *union_terms[TRANS_HASH_SIZE] ;
static struct _const_list *env_consts[TRANS_HASH_SIZE] ;
static struct _term_list *env_left[TRANS_HASH_SIZE] ;
static struct _term_list *env_right[TRANS_HASH_SIZE] ;
static struct _ex_list *all_terms[TRANS_HASH_SIZE] ;
static struct _const_list *all_consts[TRANS_HASH_SIZE] ;
static struct _term_list *all_left[TRANS_HASH_SIZE] ;
static struct _term_list *all_right[TRANS_HASH_SIZE] ;
struct _union_list *all_union_terms[TRANS_HASH_SIZE] ;
static struct trans_stack **push_hash, **root_push_hash = NULL ;
static struct _ex_intern **terms = NULL;
static int term_count, max_term_count ;
static int flushed ;

static void print_term_table(struct _ex_list **list)
{
    int i ;
    struct _ex_list *el ;
    _tree_indent() ;
    for (i = 0; i < TRANS_HASH_SIZE; ++i) {
        el = list[i] ;
        if (list[i] != NULL) _zone_print1("Bin %d", i) ;
        _tree_indent() ;
        while (el != NULL) {
            _zone_print2("Term %d %s", el->unused, _th_print_exp(el->e)) ;
            el = el->next ;
        }
        _tree_undent() ;
    }
    _tree_undent() ;
}

static void print_left_table(struct _term_list **list)
{
    int i ;
    struct _term_list *tl ;
    struct _ex_list *el ;
    _tree_indent() ;
    for (i = 0; i < TRANS_HASH_SIZE; ++i) {
        if (list[i] != NULL) _zone_print1("Bin %d", i) ;
        _tree_indent() ;
        tl = list[i] ;
        while (tl != NULL) {
            _zone_print_exp("Term", tl->e);
            _tree_indent() ;
            el = tl->exps ;
            while (el != NULL) {
                _zone_print2("Left in %d %s", el->unused, _th_print_exp(el->e)) ;
                el = el->left_next ;
            }
            _tree_undent() ;
            tl = tl->next ;
        }
        _tree_undent() ;
    }
    _tree_undent() ;
}

static void print_right_table(struct _term_list **list)
{
    int i ;
    struct _term_list *tl ;
    struct _ex_list *el ;
    _tree_indent() ;
    for (i = 0; i < TRANS_HASH_SIZE; ++i) {
        if (list[i] != NULL) _zone_print1("Bin %d", i) ;
        _tree_indent() ;
        tl = list[i] ;
        while (tl != NULL) {
            _zone_print1("Term %s", _th_print_exp(tl->e)) ;
            _tree_indent() ;
            el = tl->exps ;
            while (el != NULL) {
                _zone_print2("Right in %d %s", el->unused, _th_print_exp(el->e)) ;
                el = el->right_next ;
            }
            _tree_undent() ;
            tl = tl->next ;
        }
        _tree_undent() ;
    }
    _tree_undent() ;
}

static void check_for_el(struct _ex_list *el)
{
    int i ;
    struct _ex_list *e ;

    for (i = 0; i < TRANS_HASH_SIZE; ++i) {
        e = env_terms[i] ;
        while (e != NULL) {
            if (e==el) return ;
            e = e->next ;
        }
    }
    printf("check_for_el failure %s\n", _th_print_exp(el->e)) ;
    fflush(stdout);
    exit(1) ;
}

static void check_table()
{
    int i ;
    struct _term_list *tl ;
    struct _ex_list *el ;

    for (i = 0; i < TRANS_HASH_SIZE; ++i) {
        tl = env_left[i] ;
        while (tl != NULL) {
            el = tl->exps ;
            while (el != NULL) {
                check_for_el(el) ;
                el = el->left_next ;
            }
            tl = tl->next ;
        }
    }
}

#define TERM_SIZE_INCREMENT 100

static struct trans_stack {
        struct trans_stack *next ;
        struct trans_stack *push_next ;
        struct trans_stack **push_hash ;
        struct _ex_intern **terms ;
        int term_count ;
        struct _ex_list *env_terms[TRANS_HASH_SIZE] ;
        struct _const_list *env_consts[TRANS_HASH_SIZE] ;
        struct _term_list *env_left[TRANS_HASH_SIZE] ;
        struct _term_list *env_right[TRANS_HASH_SIZE] ;
        struct _union_list *union_terms[TRANS_HASH_SIZE] ;
        int union_count ;
        struct _unions **union_ptrs ;
        struct _ex_list **term_ptrs ;
#ifdef DEBUG
        int zone, subzone, count ;
#endif
    } *tos = NULL ;

static int is_binary_functor(struct env *env, unsigned f)
{
    int flags = _th_get_attribute_flags(env, f);

    return flags & (ATTRIBUTE_EQ | ATTRIBUTE_NE | ATTRIBUTE_PO | ATTRIBUTE_EPO | ATTRIBUTE_TO | ATTRIBUTE_ETO);
}

//#define is_binary_functor(env, f) = (_th_get_attribute_flags(env,f) & (ATTRIBUTE_EQ | ATTRIBUTE_NE | ATTRIBUTE_PO | ATTRIBUTE_EPO | ATTRIBUTE_TO | ATTRIBUTE_ETO))

static int is_binary_ord_functors(struct env *env, unsigned f, unsigned g)
{
    int flags = _th_get_attribute_flags(env, f);
    return flags & (ATTRIBUTE_PO | ATTRIBUTE_TO);
}

static int is_binary_equal_ord_functors(struct env *env, unsigned f, unsigned g)
{
    int flags = _th_get_attribute_flags(env, f);
    return flags & (ATTRIBUTE_EPO | ATTRIBUTE_ETO);
}

static int is_binary_ord_functor(struct env *env, unsigned f)
{
    int flags = _th_get_attribute_flags(env, f);
    return flags & (ATTRIBUTE_PO | ATTRIBUTE_TO);
}

static int is_binary_equal_ord_functor(struct env *env, unsigned f)
{
    int flags = _th_get_attribute_flags(env, f);
    return flags & (ATTRIBUTE_EPO | ATTRIBUTE_ETO);
}

struct _ex_intern *_th_get_right_operand(struct env *env,struct _ex_intern *e) ;

struct _ex_intern *_th_get_left_operand(struct env *env,struct _ex_intern *e)
{
    struct parameter params[1] ;
    int c ;
    switch (e->u.appl.functor) {
        case INTERN_AND:
        case INTERN_OR:
            params[0].type = SYMBOL_PARAMETER ;
            params[0].u.symbol = e->u.appl.args[0]->u.appl.functor ;
            if (params[0].u.symbol==INTERN_NOT) {
                params[0].u.symbol = e->u.appl.args[0]->u.appl.args[0]->u.appl.functor;
            }
            _th_get_attrib(env,INTERN_EQ,1,params) ;
            if (_th_get_next_attrib(&c) != NULL) {
                return _th_get_left_operand(env,e->u.appl.args[1]) ;
            }
            _th_get_attrib(env,INTERN_NE,1,params) ;
            if (_th_get_next_attrib(&c) != NULL) {
                return _th_get_left_operand(env,e->u.appl.args[1]) ;
            }
            return _th_get_left_operand(env,e->u.appl.args[0]) ;
        case INTERN_NOT:
            return _th_get_right_operand(env,e->u.appl.args[0]) ;
        default:
            return e->u.appl.args[0] ;
    }
}

struct _ex_intern *_th_get_right_operand(struct env *env, struct _ex_intern *e)
{
    struct parameter params[1] ;
    int c ;

    switch (e->u.appl.functor) {
        case INTERN_AND:
        case INTERN_OR:
            params[0].type = SYMBOL_PARAMETER ;
            params[0].u.symbol = e->u.appl.args[0]->u.appl.functor ;
            if (params[0].u.symbol==INTERN_NOT) {
                params[0].u.symbol = e->u.appl.args[0]->u.appl.args[0]->u.appl.functor;
            }
            _th_get_attrib(env,INTERN_EQ,1,params) ;
            if (_th_get_next_attrib(&c) != NULL) {
                return _th_get_right_operand(env,e->u.appl.args[1]) ;
            }
            _th_get_attrib(env,INTERN_NE,1,params) ;
            if (_th_get_next_attrib(&c) != NULL) {
                return _th_get_right_operand(env,e->u.appl.args[1]) ;
            }
            return _th_get_right_operand(env,e->u.appl.args[0]) ;
        case INTERN_NOT:
            return _th_get_left_operand(env,e->u.appl.args[0]) ;
        default:
            return e->u.appl.args[1] ;
    }
}

int _th_is_an_eq(struct env *, struct _ex_intern *) ;
int _th_is_ne(struct env *, struct _ex_intern *) ;
int _th_is_le(struct env *, struct _ex_intern *) ;
int _th_is_lt(struct env *, struct _ex_intern *) ;

int _th_is_an_eq(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *f ;

    switch (e->u.appl.functor) {
        case INTERN_NOT:
            return _th_is_ne(env,e->u.appl.args[0]) ;
        case INTERN_AND:
            f = e->u.appl.args[0] ;
            e = e->u.appl.args[1] ;
            return (_th_is_le(env,f) && _th_is_le(env,e)) ;
        case INTERN_OR:
            return 0 ;
    }
    return _th_get_attribute_flags(env,e->u.appl.functor) & ATTRIBUTE_EQ ;
}

int _th_is_ne(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *f ;

    switch (e->u.appl.functor) {
        case INTERN_NOT:
            return _th_is_an_eq(env,e->u.appl.args[0]) ;
        case INTERN_OR:
            f = e->u.appl.args[0] ;
            e = e->u.appl.args[1] ;
            return (_th_is_lt(env,f) && _th_is_lt(env,e)) ;
        case INTERN_AND:
            return 0 ;
    }
    return _th_get_attribute_flags(env,e->u.appl.functor) & ATTRIBUTE_NE ;
}

int _th_is_lt(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *f ;

    switch (e->u.appl.functor) {
        case INTERN_NOT:
            return _th_is_le(env,e->u.appl.args[0]) ;
        case INTERN_AND:
            f = e->u.appl.args[0] ;
            e = e->u.appl.args[1] ;
            return ((_th_is_ne(env,f) && _th_is_le(env,e)) || (_th_is_le(env,f) && _th_is_ne(env,e))) ;
        case INTERN_OR:
            return 0 ;
    }
    return _th_get_attribute_flags(env,e->u.appl.functor) & (ATTRIBUTE_PO | ATTRIBUTE_TO) ;
}

int _th_is_le(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *f ;

    switch (e->u.appl.functor) {
        case INTERN_NOT:
            return _th_is_lt(env,e->u.appl.args[0]) ;
        case INTERN_OR:
            f = e->u.appl.args[0] ;
            e = e->u.appl.args[1] ;
            return ((_th_is_an_eq(env,f) && _th_is_lt(env,e)) || (_th_is_lt(env,f) && _th_is_an_eq(env,e))) ;
        case INTERN_AND:
            return 0 ;
    }
    return _th_get_attribute_flags(env,e->u.appl.functor) & (ATTRIBUTE_PO | ATTRIBUTE_TO) ;
}

static struct _ex_intern *get_type(struct env *env, struct _ex_intern *e)
{
    //_zone_print_exp("Getting type of", e);
    if (e->type==EXP_INTEGER) {
        return _ex_int;
    } else if (e->type==EXP_RATIONAL) {
        return _ex_real;
    } else if (e->type==EXP_MARKED_VAR) {
        _zone_print_exp("type", _th_get_var_type(env,e->u.marked_var.var));
        return _th_get_var_type(env,e->u.marked_var.var);
    } else if (e->type==EXP_VAR) {
        return _th_get_var_type(env,e->u.var);
    } else if (e->type==EXP_APPL) {
        struct _ex_intern *t;
        if (e->u.appl.functor==INTERN_ITE) {
            return get_type(env,e->u.appl.args[1]);
        }
        t = _th_get_type(env,e->u.appl.functor);
        //if (t==NULL) {
        //    fprintf(stderr, "e = %s\n", _th_print_exp(e));
        //    fflush(stderr);
        //}
        if (t==NULL) return NULL;
        return t->u.appl.args[1];
    } else {
        return NULL;
    }
}

static void insert_type(struct env *env, struct _ex_intern *e)
{
    //_zone_print_exp("Attempting to fill", e);
    if (e->type != EXP_APPL || e->u.appl.functor != INTERN_EQUAL || e->type_inst != NULL) return;

    e->type_inst = get_type(env,e->u.appl.args[0]);
}

static struct _ex_intern *get_insert_type(struct env *env, struct _ex_intern *e)
{
    //_zone_print_exp("Attempting to fill", e);
    if (e->type != EXP_APPL || e->u.appl.functor != INTERN_EQUAL || e->type_inst != NULL) return e->type_inst;

    return get_type(env,e->u.appl.args[0]);
}

static struct _ex_intern *mk_eq(struct env *env, unsigned op,
                                struct _ex_intern *l, struct _ex_intern *r)
{
    struct parameter params[1], *parameters ;
    int c ;
    struct _ex_intern *args[2] ;

    params[0].type = SYMBOL_PARAMETER ;
    params[0].u.symbol = op ;
    _th_get_attrib(env,INTERN_EQ,1,params) ;
    if (_th_get_next_attrib(&c) != NULL) {
        args[0] = l ;
        args[1] = r ;
        l = _ex_intern_appl_equal_env(env,op,2,args,get_insert_type(env,l)) ;
        return l;
    }
    _th_get_attrib(env,INTERN_NE,1,params) ;
    if (_th_get_next_attrib(&c) != NULL) {
        args[0] = l ;
        args[1] = r ;
        args[0] = _ex_intern_appl_equal_env(env,op,2,args,get_insert_type(env,l)) ;
        return _ex_intern_appl_env(env,INTERN_NOT,1,args) ;
    }
    _th_get_attrib(env,INTERN_PO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = l ;
        args[1] = r ;
        l = _ex_intern_appl_equal_env(env,parameters[1].u.symbol,2,args,get_insert_type(env,l)) ;
        return l;
    }
    _th_get_attrib(env,INTERN_TO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = l ;
        args[1] = r ;
        l = _ex_intern_appl_equal_env(env,parameters[1].u.symbol,2,args,get_insert_type(env,l)) ;
        return l;
    }
    _th_get_attrib(env,INTERN_EPO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = l ;
        args[1] = r ;
        l = _ex_intern_appl_equal_env(env,parameters[1].u.symbol,2,args,get_insert_type(env,l)) ;
        return l;
    }
    _th_get_attrib(env,INTERN_ETO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = l ;
        args[1] = r ;
        l = _ex_intern_appl_equal_env(env,parameters[1].u.symbol,2,args,get_insert_type(env,l)) ;
        return l;
    }
    printf("Illegal mk_eq\n") ;
    fflush(stdout);
    exit(1) ;
	return NULL ;
}

static struct _ex_intern *mk_ne(struct env *env, unsigned op,
                                struct _ex_intern *l, struct _ex_intern *r)
{
    struct parameter params[1], *parameters ;
    int c ;
    struct _ex_intern *args[2] ;

    params[0].type = SYMBOL_PARAMETER ;
    params[0].u.symbol = op ;
    _th_get_attrib(env,INTERN_EQ,1,params) ;
    if (_th_get_next_attrib(&c) != NULL) {
        args[0] = l ;
        args[1] = r ;
        args[0] = _ex_intern_appl_equal_env(env,op,2,args,get_insert_type(env,args[0])) ;
        return _ex_intern_appl_env(env,INTERN_NOT,1,args) ;
    }
    _th_get_attrib(env,INTERN_NE,1,params) ;
    if (_th_get_next_attrib(&c) != NULL) {
        args[0] = l ;
        args[1] = r ;
        l = _ex_intern_appl_equal_env(env,op,2,args,get_insert_type(env,l)) ;
        return l;
    }
    _th_get_attrib(env,INTERN_PO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = l ;
        args[1] = r ;
        args[0] = _ex_intern_appl_equal_env(env,op,2,args, get_insert_type(env,args[0]));
        return _ex_intern_appl_env(env,INTERN_NOT,1,args) ;
    }
    _th_get_attrib(env,INTERN_TO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = l ;
        args[1] = r ;
        args[0] = _ex_intern_appl_equal_env(env,op,2,args, get_insert_type(env,args[0]));
        return _ex_intern_appl_env(env,INTERN_NOT,1,args) ;
    }
    _th_get_attrib(env,INTERN_EPO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = l ;
        args[1] = r ;
        args[0] = _ex_intern_appl_equal_env(env,op,2,args, get_insert_type(env,args[0]));
        return _ex_intern_appl_env(env,INTERN_NOT,1,args) ;
    }
    _th_get_attrib(env,INTERN_ETO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = l ;
        args[1] = r ;
        args[0] = _ex_intern_appl_equal_env(env,op,2,args, get_insert_type(env,args[0]));
        return _ex_intern_appl_env(env,INTERN_NOT,1,args) ;
    }
    printf("Illegal mk_ne\n") ;
    fflush(stdout);
    exit(1) ;
	return NULL ;
}

static struct _ex_intern *mk_lt(struct env *env, unsigned op,
                                struct _ex_intern *l, struct _ex_intern *r)
{
    struct parameter params[1], *parameters ;
    int c ;
    struct _ex_intern *args[2], *args2[2] ;

    params[0].type = SYMBOL_PARAMETER ;
    params[0].u.symbol = op ;
    _th_get_attrib(env,INTERN_PO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = l ;
        args[1] = r ;
        return _ex_intern_appl_env(env,op,2,args) ;
    }
    _th_get_attrib(env,INTERN_TO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = l ;
        args[1] = r ;
        return _ex_intern_appl_env(env,op,2,args) ;
    }
    _th_get_attrib(env,INTERN_EPO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = l ;
        args[1] = r ;
        args2[0] = _ex_intern_appl_env(env,op,2,args) ;
        args2[1] = _ex_intern_appl_env(env,parameters[1].u.symbol,2,args) ;
        args2[1] = _ex_intern_appl_env(env,INTERN_NOT,1,args2+1) ;
        return _ex_intern_appl_env(env,INTERN_AND,2,args2) ;
    }
    _th_get_attrib(env,INTERN_ETO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = r ;
        args[1] = l ;
        args[0] = _ex_intern_appl_env(env,op,2,args) ;
        return _ex_intern_appl_env(env,INTERN_NOT,1,args) ;
    }
    printf("Illegal mk_lt %s %s %s %d %d\n", _th_intern_decode(op), _th_print_exp(l), _th_print_exp(r), l, r) ;
    fflush(stdout) ;
    //c = 0 ;
    //c = 1 / c ;
    exit(1) ;
    return NULL ;
}

static struct _ex_intern *mk_npo(struct env *env, unsigned op,
                                 struct _ex_intern *l, struct _ex_intern *r)
{
    struct parameter params[1], *parameters ;
    int c ;
    struct _ex_intern *args[2], *args2[2] ;

    params[0].type = SYMBOL_PARAMETER ;
    params[0].u.symbol = op ;
    _th_get_attrib(env,INTERN_PO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = r ;
        args[1] = l ;
        return _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl_env(env,op,2,args)) ;
    }
    _th_get_attrib(env,INTERN_EPO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = r ;
        args[1] = l ;
        args2[0] = _ex_intern_appl_env(env,op,2,args) ;
        args2[1] = _ex_intern_appl_env(env,parameters[1].u.symbol,2,args) ;
        args2[0] = _ex_intern_appl1_env(env,INTERN_NOT,args2[0]) ;
        return _ex_intern_appl_env(env,INTERN_OR,2,args2) ;
    }
    printf("Illegal mk_npo\n") ;
    fflush(stdout);
    exit(1) ;
}

static struct _ex_intern *mk_nepo(struct env *env, unsigned op,
                                 struct _ex_intern *l, struct _ex_intern *r)
{
    struct parameter params[1], *parameters ;
    int c ;
    struct _ex_intern *args[2], *args2[2] ;

    params[0].type = SYMBOL_PARAMETER ;
    params[0].u.symbol = op ;
    _th_get_attrib(env,INTERN_EPO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = r ;
        args[1] = l ;
        return _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl_env(env,op,2,args)) ;
    }
    _th_get_attrib(env,INTERN_PO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = r ;
        args[1] = l ;
        args2[0] = _ex_intern_appl_env(env,op,2,args) ;
        args2[1] = _ex_intern_appl_env(env,parameters[1].u.symbol,2,args) ;
        args2[0] = _ex_intern_appl1_env(env,INTERN_NOT,args2[0]) ;
        args2[1] = _ex_intern_appl1_env(env,INTERN_NOT,args2[1]) ;
        return _ex_intern_appl_env(env,INTERN_AND,2,args2) ;
    }
    printf("Illegal mk_npo\n") ;
    fflush(stdout);
    exit(1) ;
}

static struct _ex_intern *mk_le(struct env *env, unsigned op,
                                struct _ex_intern *l, struct _ex_intern *r)
{
    struct parameter params[1], *parameters ;
    int c ;
    struct _ex_intern *args[2], *args2[2] ;

    params[0].type = SYMBOL_PARAMETER ;
    params[0].u.symbol = op ;
    _th_get_attrib(env,INTERN_EPO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = l ;
        args[1] = r ;
        return _ex_intern_appl_env(env,op,2,args) ;
    }
    _th_get_attrib(env,INTERN_ETO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = l ;
        args[1] = r ;
        return _ex_intern_appl_env(env,op,2,args) ;
    }
    _th_get_attrib(env,INTERN_PO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = l ;
        args[1] = r ;
        args2[0] = _ex_intern_appl_env(env,op,2,args) ;
        args2[1] = _ex_intern_appl_env(env,parameters[1].u.symbol,2,args) ;
        return _ex_intern_appl_env(env,INTERN_OR,2,args2) ;
    }
    _th_get_attrib(env,INTERN_TO,1,params) ;
    if ((parameters=_th_get_next_attrib(&c)) != NULL) {
        args[0] = r ;
        args[1] = l ;
        args[0] = _ex_intern_appl_env(env,op,2,args) ;
        return _ex_intern_appl_env(env,INTERN_NOT,1,args) ;
    }
    printf("Illegal mk_le\n") ;
    fflush(stdout);
    exit(1) ;
	return NULL ;
}

static unsigned get_operator(struct env *env, struct _ex_intern *e, unsigned *op_type)
{
    unsigned r, s ;
    unsigned op1, op2 ;
    int flags;

    if (e->u.appl.functor==INTERN_ORIENTED_RULE &&
        e->u.appl.count==3 && e->u.appl.args[2]==_ex_true) {
        e = _ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0],e->u.appl.args[1]);
    }

    switch (e->u.appl.functor) {
        case INTERN_NOT:
            r = get_operator(env,e->u.appl.args[0],op_type) ;
            switch (*op_type) {
                case INTERN_EQ:
                    *op_type = INTERN_NE ;
                    break ;
                case INTERN_NE:
                    *op_type = INTERN_EQ ;
                    break ;
                case INTERN_TO:
                    *op_type = INTERN_ETO ;
                    break ;
                case INTERN_ETO:
                    *op_type = INTERN_TO ;
                    break ;
                case INTERN_EPO:
                    *op_type = INTERN_NEPO ;
                    break ;
                case INTERN_PO:
                    *op_type = INTERN_NPO ;
                    break ;
                case INTERN_NEPO:
                    *op_type = INTERN_EPO ;
                    break ;
                case INTERN_NPO:
                    *op_type = INTERN_PO ;
                    break ;
                default:
                    printf("Transitive: illegal term 1 %s\n", _th_print_exp(e)) ;
                    fflush(stdout);
                    exit(1) ;
            }
            return r ;
        case INTERN_AND:
            r = get_operator(env, e->u.appl.args[0], &op1) ;
            s = get_operator(env,e->u.appl.args[1], &op2) ;
            _zone_print4("sub_operators %s %s %s %s", _th_intern_decode(r), _th_intern_decode(s), _th_intern_decode(op1), _th_intern_decode(op2)) ;
            _zone_print3("terms %d %d %d", op1, op2, INTERN_NE);
            switch (op1) {
                case INTERN_NPO:
                    switch (op2) {
                        case INTERN_NE:
                            *op_type = INTERN_NEPO ;
                            break ;
                        default:
                            printf("Transitive: illegal term 2 %s\n", _th_print_exp(e)) ;
                            fflush(stdout);
                            exit(1) ;
                    }
                    break ;
                case INTERN_NE:
                    switch (op2) {
                        case INTERN_NPO:
                            *op_type = INTERN_NEPO ;
                            break ;
                        case INTERN_ETO:
                            *op_type = INTERN_TO ;
                            break ;
                        case INTERN_EPO:
                            *op_type = INTERN_PO ;
                            break ;
                        default:
                            printf("Transitive: illegal term 3 %s\n", _th_print_exp(e)) ;
                            fflush(stdout);
                            exit(1) ;
                    }
                    break ;
                case INTERN_ETO:
                    switch (op2) {
                        case INTERN_NE:
                            *op_type = INTERN_TO ;
                            break ;
                        case INTERN_ETO:
                            *op_type = INTERN_EQ ;
                            break ;
                        default:
                            printf("Transitive: illegal term 4 %s\n", _th_print_exp(e)) ;
                            fflush(stdout);
                            exit(1) ;
                    }
                    break ;
                case INTERN_EPO:
                    switch (op2) {
                        case INTERN_NE:
                            *op_type = INTERN_PO ;
                            break ;
                        case INTERN_EPO:
                            *op_type = INTERN_EQ ;
                            break ;
                        default:
                            printf("Transitive: illegal term 5 %s\n", _th_print_exp(e)) ;
                            fflush(stdout);
                            exit(1) ;
                    }
                    break ;
                default:
                    printf("Transitive: illegal term 6 %s\n", _th_print_exp(e)) ;
                    fflush(stdout);
                    exit(1) ;
            }
            if (op1==INTERN_EQ || op1==INTERN_NE) return s ;
            return r ;
        case INTERN_OR:
            r = get_operator(env, e->u.appl.args[0], &op1) ;
            s = get_operator(env,e->u.appl.args[1], &op2) ;
            switch (op1) {
                case INTERN_NEPO:
                    switch (op2) {
                        case INTERN_EQ:
                            *op_type = INTERN_NPO ;
                            break ;
                        default:
                            printf("Transitive: illegal term 7 %s\n", _th_print_exp(e)) ;
                            fflush(stdout);
                            exit(1) ;
                    }
                    break ;
                case INTERN_EQ:
                    switch (op2) {
                        case INTERN_NEPO:
                            *op_type = INTERN_NPO ;
                            break ;
                        case INTERN_TO:
                            *op_type = INTERN_ETO ;
                            break ;
                        case INTERN_PO:
                            *op_type = INTERN_EPO ;
                            break ;
                        default:
                            printf("Transitive: illegal term 8 %s\n", _th_print_exp(e)) ;
                            fflush(stdout);
                            exit(1) ;
                    }
                    break ;
                case INTERN_TO:
                    switch (op2) {
                        case INTERN_EQ:
                            *op_type = INTERN_ETO ;
                            break ;
                        case INTERN_TO:
                            *op_type = INTERN_NE ;
                            break ;
                        default:
                            printf("Transitive: illegal term 9 %s\n", _th_print_exp(e)) ;
                            fflush(stdout);
                            exit(1) ;
                    }
                    break ;
                case INTERN_PO:
                    switch (op2) {
                        case INTERN_EQ:
                            *op_type = INTERN_EPO ;
                            break ;
                        case INTERN_PO:
                            *op_type = INTERN_NE ;
                            break ;
                        default:
                            printf("Transitive: illegal term 10 %s\n", _th_print_exp(e)) ;
                            fflush(stdout);
                            exit(1) ;
                    }
                    break ;
                default:
                    printf("Transitive: illegal term 11 %s\n", _th_print_exp(e)) ;
                    fflush(stdout);
                    exit(1) ;
            }
            if (op1==INTERN_EQ || op1==INTERN_NE) return s ;
            return r ;
    }
    *op_type = 0 ;
    flags = _th_get_attribute_flags(env,e->u.appl.functor);

    if (flags & ATTRIBUTE_EQ) {
        *op_type = INTERN_EQ ;
    }
    if (flags & ATTRIBUTE_NE) {
        *op_type = INTERN_NE ;
    }
    if (flags & ATTRIBUTE_TO) {
        *op_type = INTERN_TO ;
    }
    if (flags & ATTRIBUTE_PO) {
        *op_type = INTERN_PO ;
    }
    if (flags & ATTRIBUTE_EPO) {
        *op_type = INTERN_EPO ;
    }
    if (flags & ATTRIBUTE_ETO) {
        *op_type = INTERN_ETO ;
    }
    if (e->u.appl.functor==INTERN_SEPARATE) {
        *op_type = INTERN_NE ;
    }
    return e->u.appl.functor ;
}

int _th_compatible_terms(struct env *env, struct _ex_intern *e, struct _ex_intern *f)
{
    struct parameter params[2] ;
    int c ;
    unsigned e1, e2 ;
    unsigned op1, op2 ;

#ifdef DEBUG
    _tree_print0("compatible terms");
    _tree_indent();
    _tree_print_exp("e", e);
    _tree_print_exp("f", f);
#endif

    op1 = get_operator(env,e,&e1) ;
    op2 = get_operator(env,f,&e2) ;

#ifdef DEBUG
    _tree_print2("op1, e1 = %d %d", op1, e1);
    _tree_print2("op2, e2 = %d %d", op2, e2);
#endif

    if (op1==INTERN_SEPARATE) {
#ifdef DEBUG
        _tree_undent();
#endif
        return op2==INTERN_EQUAL || op2==INTERN_SUBSET || op2==INTERN_SEPARATE;
    }
    if (op2==INTERN_SEPARATE) {
#ifdef DEBUG
        _tree_undent();
#endif
        return op1==INTERN_EQUAL || op1==INTERN_SUBSET || op1==INTERN_SEPARATE;
    }
    e1 = (e1==INTERN_EQ || e1==INTERN_NE) ;
    e2 = (e2==INTERN_EQ || e2==INTERN_NE) ;

    if (e1==e2) {
#ifdef DEBUG
        _tree_undent();
#endif
        return op1==op2 ;
    }

    if (e1 && op1==INTERN_EQUAL) {
#ifdef DEBUG
        _tree_undent();
#endif
        return 1;
    }
    if (e2 && op2==INTERN_EQUAL) {
#ifdef DEBUG
        _tree_undent();
#endif
        return 1;
   }

    if (e1) {
        params[0].type = SYMBOL_PARAMETER ;
        params[0].u.symbol = op1 ;
        params[1].type = SYMBOL_PARAMETER ;
        params[1].u.symbol = op2 ;
        _th_get_attrib(env,INTERN_EF,2,params) ;
#ifdef DEBUG
        _tree_undent();
#endif
        return (_th_get_next_attrib(&c) != NULL) ;
    }

    if (e2) {
        params[0].type = SYMBOL_PARAMETER ;
        params[0].u.symbol = op2 ;
        params[1].type = SYMBOL_PARAMETER ;
        params[1].u.symbol = op1 ;
        _th_get_attrib(env,INTERN_EF,2,params) ;
#ifdef DEBUG
        _tree_undent();
#endif
        return (_th_get_next_attrib(&c) != NULL) ;
    }

#ifdef DEBUG
    _tree_undent();
#endif

    return 0 ;
}

static int can_combine(struct env *env,struct _ex_intern *e1, struct _ex_intern *e2)
{
    struct _ex_intern *l1 = _th_get_left_operand(env,e1) ;
    struct _ex_intern *l2 = _th_get_left_operand(env,e2) ;
    struct _ex_intern *r1 = _th_get_right_operand(env,e1) ;
    struct _ex_intern *r2 = _th_get_right_operand(env,e2) ;

    return ((l1==l2 && r1==r2) || (l1==r2 && r1==l2)) ;
}

static struct _ex_intern *simplify_term(struct env *env, struct _ex_intern *e)
{
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_SUBSET && e->u.appl.count==2 &&
        e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_SET && e->u.appl.args[0]->u.appl.count==1 &&
        e->u.appl.args[1]->type==EXP_APPL && e->u.appl.args[1]->u.appl.functor==INTERN_SET && e->u.appl.args[1]->u.appl.count==1) {
        return _ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0]->u.appl.args[0],e->u.appl.args[1]->u.appl.args[0]);
    }
    if (e->type==EXP_APPL && e->u.appl.count==1 && e->u.appl.functor==INTERN_NOT &&
        e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_SUBSET && e->u.appl.args[0]->u.appl.count==2 &&
        e->u.appl.args[0]->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.args[0]->u.appl.functor==INTERN_SET && e->u.appl.args[0]->u.appl.args[0]->u.appl.count==1 &&
        e->u.appl.args[0]->u.appl.args[1]->type==EXP_APPL && e->u.appl.args[0]->u.appl.args[1]->u.appl.functor==INTERN_SET && e->u.appl.args[0]->u.appl.args[1]->u.appl.count==1) {
        return _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0]->u.appl.args[0]->u.appl.args[0],e->u.appl.args[0]->u.appl.args[1]->u.appl.args[0]));
    }
    return e ;
}

struct _ex_intern *_th_combine_operands(struct env *env,
                                           struct _ex_intern *e1,
                                           struct _ex_intern *e2,
                                           int *and_combine)
{
    struct _ex_intern *l1 = _th_get_left_operand(env,e1) ;
    struct _ex_intern *l2 = _th_get_left_operand(env,e2) ;
    struct _ex_intern *r1 = _th_get_right_operand(env,e1) ;
    struct _ex_intern *r2 = _th_get_right_operand(env,e2) ;
    unsigned op1, op2 ;
    unsigned optype1, optype2 ;

    /*printf("Testing combination of %s and ",_th_print_exp(e1)) ;
    printf("%s\n",_th_print_exp(e2)) ;*/

    if (l1 != l2 && l1 != r2 && r1 != l2 && r1 != r2) {
        return NULL ;
    }

    *and_combine = (_th_equal(env,l1,l2) && _th_equal(env,r1,r2) ||
                    _th_equal(env,l1,r2) && _th_equal(env,r1,l2)) ;

    op1 = get_operator(env, e1, &optype1) ;
    op2 = get_operator(env, e2, &optype2) ;
#ifdef DEBUG
    _zone_print1("terms %s", _th_print_exp(e1)) ;
    _zone_print1("and %s", _th_print_exp(e2)) ;
    _zone_print4("ops %s %s %s %s", _th_intern_decode(op1), _th_intern_decode(op2), _th_intern_decode(optype1), _th_intern_decode(optype2));
#endif
    if (!_th_compatible_terms(env, e1, e2)) return NULL ;

    if (op1==INTERN_SEPARATE && optype1==INTERN_NE) {
        if (*and_combine) {
            if ((op2==INTERN_SUBSET && (optype2==INTERN_PO || optype2==INTERN_EPO)) ||
                (op2==INTERN_EQUAL && optype2==INTERN_EQ)) {
                return _ex_false ;
            }
        } else {
            if (op2==INTERN_EQUAL && optype2==INTERN_EQ) {
                if (l1==l2) {
                    return _ex_intern_appl2_env(env,INTERN_SEPARATE,r1,r2) ;
                } else if (r1==l2) {
                    return _ex_intern_appl2_env(env,INTERN_SEPARATE,l1,r2) ;
                } else if (l1==r2) {
                    return _ex_intern_appl2_env(env,INTERN_SEPARATE,l2,r1) ;
                } else {
                    return _ex_intern_appl2_env(env,INTERN_SEPARATE,l1,l2) ;
                }
            } else if (op2==INTERN_SUBSET && (optype2==INTERN_EPO || optype2==INTERN_PO)) {
                if (r2==l1) {
                    return _ex_intern_appl2_env(env,INTERN_SEPARATE,r1,l2) ;
                } else if (r2==r1) {
                    return _ex_intern_appl2_env(env,INTERN_SEPARATE,l1,l2) ;
                }
            }
        }
        return e1 ;
    } else if (op2==INTERN_SEPARATE && optype2==INTERN_NE) {
        if (*and_combine) {
            if ((op1==INTERN_SUBSET && (optype1==INTERN_PO || optype1==INTERN_EPO)) ||
                (op1==INTERN_EQUAL && optype1==INTERN_EQ)) {
                return _ex_false ;
            }
        } else {
            if (op1==INTERN_EQUAL && optype1==INTERN_EQ) {
                if (l1==l2) {
                    return _ex_intern_appl2_env(env,INTERN_SEPARATE,r1,r2) ;
                } else if (r1==l2) {
                    return _ex_intern_appl2_env(env,INTERN_SEPARATE,l1,r2) ;
                } else if (l1==r2) {
                    return _ex_intern_appl2_env(env,INTERN_SEPARATE,l2,r1) ;
                } else {
                    return _ex_intern_appl2_env(env,INTERN_SEPARATE,l1,l2) ;
                }
            } else if (op1==INTERN_SUBSET && (optype1==INTERN_EPO || optype1==INTERN_PO)) {
                if (r1==l2) {
                    return _ex_intern_appl2_env(env,INTERN_SEPARATE,r2,l1) ;
                } else if (r2==r1) {
                    return _ex_intern_appl2_env(env,INTERN_SEPARATE,l1,l2) ;
                }
            }
        }
        return e1 ;
    }
#ifdef DEBUG
    _zone_print4("l1, l2, r1, r2 %d %d %d %d", l1, l2, r1, r2);
    _zone_print1("l1 = %s", _th_print_exp(l1));
    _zone_print1("r1 = %s", _th_print_exp(r1));
    _zone_print1("l2 = %s", _th_print_exp(l2));
    _zone_print1("r2 = %s", _th_print_exp(r2));
#endif

    if ((l1==l2 && r1==r2) || (l1==r2 && r1==l2)) {
        switch (optype1) {
            case INTERN_EQ:
                switch (optype2) {
                    case INTERN_EQ:
                        return e1 ;
                    case INTERN_NE:
                    case INTERN_PO:
                    case INTERN_TO:
                    case INTERN_NEPO:
                        return _ex_false ;
                    case INTERN_EPO:
                    case INTERN_ETO:
                    case INTERN_NPO:
                        return e1 ;
                }
            case INTERN_NE:
                switch (optype2) {
                    case INTERN_EQ:
                        return _ex_false ;
                    case INTERN_NE:
                        return e1 ;
                    case INTERN_PO:
                    case INTERN_TO:
                    case INTERN_NEPO:
                        return e2 ;
                    case INTERN_EPO:
                    case INTERN_ETO:
                        return simplify_term(env,mk_lt(env,op2,l2,r2)) ;
                    case INTERN_NPO:
                        return simplify_term(env,mk_nepo(env,op2,l2,r2)) ;
                }
            case INTERN_PO:
            case INTERN_TO:
                switch (optype2) {
                    case INTERN_EQ:
                        return _ex_false ;
                    case INTERN_NPO:
                        if (l1==l2) {
                            return e1 ;
                        } else {
                            return _ex_false ;
                        }
                    case INTERN_NE:
                        return e1 ;
                    case INTERN_PO:
                    case INTERN_TO:
                        if (l1==l2) {
                            return e1 ;
                        } else {
                            return _ex_false ;
                        }
                    case INTERN_NEPO:
                        if (l1==l2) {
                            return e1 ;
                        } else {
                            return _ex_false ;
                        }
                    case INTERN_EPO:
                    case INTERN_ETO:
                        if (l1==l2) {
                            return simplify_term(env,mk_lt(env,op2,l2,r2)) ;
                        } else {
                            return _ex_false ;
                        }
                }
            case INTERN_EPO:
            case INTERN_ETO:
                switch (optype2) {
                    case INTERN_EQ:
                        return e2 ;
                    case INTERN_NE:
                        return mk_lt(env,op1,l1,r1) ;
                    case INTERN_PO:
                    case INTERN_TO:
                        if (l1==l2) {
                            return e2 ;
                        } else {
                            return _ex_false ;
                        }
                    case INTERN_NPO:
                        if (l1==l2) {
                            return e1 ;
                        } else {
                            return simplify_term(env,mk_eq(env,op1,l1,r1)) ;
                        }
                    case INTERN_NEPO:
                        if (l1==l2) {
                            return simplify_term(env,mk_lt(env,op1,l1,r1)) ;
                        } else {
                            return _ex_false ;
                        }
                    case INTERN_EPO:
                    case INTERN_ETO:
                        if (l1==l2) {
                            return e2 ;
                        } else {
                            return simplify_term(env,mk_eq(env,op1,l1,r1)) ;
                        }
                }
        }
    }

    if (l1==l2 && !l1->type==EXP_INTEGER) {
        switch (optype1) {
            case INTERN_EQ:
                switch (optype2) {
                    case INTERN_EQ:
                        return simplify_term(env,mk_eq(env,op1,r1,r2)) ;
                    case INTERN_NE:
                        return simplify_term(env,mk_ne(env,op1,r1,r2)) ;
                    case INTERN_PO:
                    case INTERN_TO:
                        return simplify_term(env,mk_lt(env,op2,r1,r2)) ;
                    case INTERN_EPO:
                    case INTERN_ETO:
                        return simplify_term(env,mk_le(env,op2,r1,r2)) ;
                    case INTERN_NEPO:
                        return simplify_term(env,mk_nepo(env,op2,r1,r2)) ;
                    case INTERN_NPO:
                        return simplify_term(env,mk_npo(env,op2,r1,r2)) ;
                }
            case INTERN_NE:
                switch (optype2) {
                    case INTERN_EQ:
                        return simplify_term(env,mk_ne(env,op1,r1,r2)) ;
                    case INTERN_NE:
                    case INTERN_PO:
                    case INTERN_TO:
                    case INTERN_EPO:
                    case INTERN_ETO:
                    case INTERN_NEPO:
                    case INTERN_NPO:
                        return NULL ;
                }
            case INTERN_PO:
            case INTERN_TO:
                switch (optype2) {
                    case INTERN_EQ:
                        return simplify_term(env,mk_lt(env,op1,r2,r1)) ;
                    case INTERN_NE:
                    case INTERN_PO:
                    case INTERN_TO:
                    case INTERN_EPO:
                    case INTERN_ETO:
                    case INTERN_NEPO:
                    case INTERN_NPO:
                        return NULL ;
                }
            case INTERN_EPO:
            case INTERN_ETO:
                switch (optype2) {
                    case INTERN_EQ:
                        return simplify_term(env,mk_le(env,op1,r2,r1)) ;
                    case INTERN_NE:
                    case INTERN_PO:
                    case INTERN_TO:
                    case INTERN_EPO:
                    case INTERN_ETO:
                    case INTERN_NEPO:
                    case INTERN_NPO:
                        return NULL ;
                }
        }
    }

    if (r2==l1 && r2->type != EXP_INTEGER) {
        switch (optype1) {
            case INTERN_EQ:
                switch (optype2) {
                    case INTERN_EQ:
                        return simplify_term(env,mk_eq(env,op1,l2,r1)) ;
                    case INTERN_NE:
                        return simplify_term(env,mk_ne(env,op1,l2,r1)) ;
                    case INTERN_PO:
                    case INTERN_TO:
                        return simplify_term(env,mk_lt(env,op2,l2,r1)) ;
                    case INTERN_EPO:
                    case INTERN_ETO:
                        return simplify_term(env,mk_le(env,op2,l2,r1)) ;
                    case INTERN_NEPO:
                        return simplify_term(env,mk_nepo(env,op2,l2,r1)) ;
                    case INTERN_NPO:
                        return simplify_term(env,mk_npo(env,op2,l2,r1)) ;
                }
            case INTERN_NE:
                switch (optype2) {
                    case INTERN_EQ:
                        return simplify_term(env,mk_ne(env,op1,l2,r1)) ;
                    case INTERN_NE:
                    case INTERN_PO:
                    case INTERN_TO:
                    case INTERN_EPO:
                    case INTERN_ETO:
                    case INTERN_NPO:
                    case INTERN_NEPO:
                        return NULL ;
                }
            case INTERN_PO:
            case INTERN_TO:
                switch (optype2) {
                    case INTERN_EQ:
                        return simplify_term(env,mk_lt(env,op1,l2,r1)) ;
                    case INTERN_NPO:
                    case INTERN_NEPO:
                        return simplify_term(env,mk_nepo(env,op1,l2,r1)) ;
                    case INTERN_NE:
                        return NULL ;
                    case INTERN_PO:
                    case INTERN_TO:
                    case INTERN_EPO:
                    case INTERN_ETO:
                        return simplify_term(env,mk_lt(env,op1,l2,r1)) ;
                }
            case INTERN_EPO:
            case INTERN_ETO:
                switch (optype2) {
                    case INTERN_EQ:
                        return simplify_term(env,mk_le(env,op1,l2,r1)) ;
                    case INTERN_NPO:
                        return simplify_term(env,mk_npo(env,op1,l2,r1)) ;
                    case INTERN_NEPO:
                        return simplify_term(env,mk_nepo(env,op1,l2,r1)) ;
                    case INTERN_NE:
                        return NULL ;
                    case INTERN_PO:
                    case INTERN_TO:
                        return simplify_term(env,mk_lt(env,op1,l2,r1)) ;
                    case INTERN_EPO:
                    case INTERN_ETO:
                        return simplify_term(env,mk_le(env,op1,l2,r1)) ;
                }
        }
    }

    if (r1==l2 && r1->type != EXP_INTEGER) {
        switch (optype1) {
            case INTERN_EQ:
                switch (optype2) {
                    case INTERN_EQ:
                        return simplify_term(env,mk_eq(env,op1,l1,r2)) ;
                    case INTERN_NE:
                        return simplify_term(env,mk_ne(env,op1,l1,r2)) ;
                    case INTERN_PO:
                    case INTERN_TO:
                        return simplify_term(env,mk_lt(env,op2,l1,r2)) ;
                    case INTERN_EPO:
                    case INTERN_ETO:
                        return simplify_term(env,mk_le(env,op2,l1,r2)) ;
                    case INTERN_NEPO:
                        return simplify_term(env,mk_nepo(env,op2,l1,r2)) ;
                    case INTERN_NPO:
                        return simplify_term(env,mk_npo(env,op2,l1,r2)) ;
                }
            case INTERN_NE:
                switch (optype2) {
                    case INTERN_EQ:
                        return simplify_term(env,mk_ne(env,op1,l1,r2)) ;
                    case INTERN_NE:
                    case INTERN_PO:
                    case INTERN_TO:
                    case INTERN_EPO:
                    case INTERN_ETO:
                    case INTERN_NPO:
                    case INTERN_NEPO:
                        return NULL ;
                }
            case INTERN_PO:
            case INTERN_TO:
                switch (optype2) {
                    case INTERN_EQ:
                        return simplify_term(env,mk_lt(env,op1,l1,r2)) ;
                    case INTERN_NPO:
                    case INTERN_NEPO:
                        return simplify_term(env,mk_nepo(env,op1,l1,r2)) ;
                    case INTERN_NE:
                        return NULL ;
                    case INTERN_PO:
                    case INTERN_TO:
                    case INTERN_EPO:
                    case INTERN_ETO:
                        return simplify_term(env,mk_lt(env,op1,l1,r2)) ;
                }
            case INTERN_EPO:
            case INTERN_ETO:
                switch (optype2) {
                    case INTERN_EQ:
                        return simplify_term(env,mk_le(env,op1,l1,r2)) ;
                    case INTERN_NPO:
                        return simplify_term(env,mk_npo(env,op1,l1,r2)) ;
                    case INTERN_NEPO:
                        return simplify_term(env,mk_nepo(env,op1,l1,r2)) ;
                    case INTERN_NE:
                        return NULL ;
                    case INTERN_PO:
                    case INTERN_TO:
                        return simplify_term(env,mk_lt(env,op1,l1,r2)) ;
                    case INTERN_EPO:
                    case INTERN_ETO:
                        return simplify_term(env,mk_le(env,op1,l1,r2)) ;
                }
        }
    }

    if (r1==r2 && r1->type != EXP_INTEGER) {
        switch (optype1) {
            case INTERN_EQ:
                switch (optype2) {
                    case INTERN_EQ:
                        return simplify_term(env,mk_eq(env,op1,l1,l2)) ;
                    case INTERN_NE:
                        return simplify_term(env,mk_ne(env,op1,l1,l2)) ;
                    case INTERN_PO:
                    case INTERN_TO:
                        return simplify_term(env,mk_lt(env,op2,l2,l1)) ;
                    case INTERN_EPO:
                    case INTERN_ETO:
                        return simplify_term(env,mk_le(env,op2,l2,l1)) ;
                    case INTERN_NEPO:
                        return simplify_term(env,mk_nepo(env,op2,l2,l1)) ;
                    case INTERN_NPO:
                        return simplify_term(env,mk_npo(env,op2,l2,l1)) ;
                }
            case INTERN_NE:
                switch (optype2) {
                    case INTERN_EQ:
                        return simplify_term(env,mk_ne(env,op1,l2,l1)) ;
                    case INTERN_NE:
                    case INTERN_PO:
                    case INTERN_TO:
                    case INTERN_EPO:
                    case INTERN_ETO:
                    case INTERN_NPO:
                    case INTERN_NEPO:
                        return NULL ;
                }
            case INTERN_PO:
            case INTERN_TO:
                switch (optype2) {
                    case INTERN_EQ:
                        return simplify_term(env,mk_lt(env,op1,l1,l2)) ;
                    case INTERN_NE:
                    case INTERN_PO:
                    case INTERN_TO:
                    case INTERN_EPO:
                    case INTERN_ETO:
                    case INTERN_NEPO:
                    case INTERN_NPO:
                        return NULL ;
                }
            case INTERN_EPO:
            case INTERN_ETO:
                switch (optype2) {
                    case INTERN_EQ:
                        return simplify_term(env,mk_le(env,op1,l1,l2)) ;
                    case INTERN_NE:
                    case INTERN_PO:
                    case INTERN_TO:
                    case INTERN_EPO:
                    case INTERN_ETO:
                    case INTERN_NEPO:
                    case INTERN_NPO:
                        return NULL ;
                }
        }
    }

    return NULL ;
}

static int is_constant(struct env *env,struct _ex_intern *e)
{
    switch(e->type) {
        case EXP_INTEGER:
        case EXP_RATIONAL:
        case EXP_STRING:
            return 1 ;
        default:
            return 0 ;
    }
}

static int find_env_const(struct env *env,struct _ex_intern *e)
{
    struct _const_list *l ;
    int bin = (((unsigned)e)/4)%TRANS_HASH_SIZE ;

    l = env_consts[bin] ;

    while(l != NULL) {
        if (l->e==e) return 1 ;
        l = l->next ;
    }

    return 0 ;
}

static int find_all_const(struct env *env,struct _ex_intern *e)
{
    struct _const_list *l ;
    int bin = (((unsigned)e)/4)%TRANS_HASH_SIZE ;

    l = all_consts[bin] ;

    while(l != NULL) {
        if (l->e==e) return 1 ;
        l = l->next ;
    }

    return 0 ;
}

static struct _const_list *add_env_const(struct env *env,struct _ex_intern *e, unsigned op)
{
    struct _const_list *l ;
    int bin ;

    if (find_env_const(env,e)) return NULL ;

    l = (struct _const_list *)_th_alloc(TRANSITIVE_SPACE,sizeof(struct _const_list)) ;
    bin = (((unsigned)e)/4)%TRANS_HASH_SIZE ;
    l->next = env_consts[bin] ;
    l->e = e ;
    env_consts[bin] = l ;

    return l ;
}

static struct _const_list *add_all_const(struct env *env,struct _ex_intern *e, unsigned op)
{
    struct _const_list *l ;
    int bin ;

    if (find_all_const(env,e)) return 0 ;

    l = (struct _const_list *)_th_alloc(TRANSITIVE_SPACE,sizeof(struct _const_list)) ;
    bin = (((unsigned)e)/4)%TRANS_HASH_SIZE ;
    l->next = all_consts[bin] ;
    l->e = e ;
    all_consts[bin] = l ;

    return l ;
}

static int find_env_term(struct env *env,struct _ex_intern *e)
{
    struct _ex_list *l ;
    int bin = (((unsigned)e)/4)%TRANS_HASH_SIZE ;

    l = env_terms[bin] ;

    while(l != NULL) {
        if (l->e==e) return 1 ;
        l = l->next ;
    }

    return 0 ;
}

static int find_all_term(struct env *env,struct _ex_intern *e)
{
    struct _ex_list *l ;
    int bin = (((unsigned)e)/4)%TRANS_HASH_SIZE ;

    l = all_terms[bin] ;

    while(l != NULL) {
        if (l->e==e) return 1 ;
        l = l->next ;
    }

    return 0 ;
}

static struct _term_list *find_term(struct _term_list **tl, struct env *env,
                                    struct _ex_intern *e)
{
    struct _term_list *t ;
    int bin ;

    bin = (((unsigned)e)/4)%TRANS_HASH_SIZE ;
#ifdef DEBUG
    _zone_print1("bin = %d", bin);
#endif
    /*printf("Find term %d %s %d\n", e, _th_print_exp(e), bin) ;*/

    t = tl[bin] ;
    while(t != NULL) {
        if (t->e==e) return t ;
        t = t->next ;
    }

    t = (struct _term_list *)_th_alloc(TRANSITIVE_SPACE,sizeof(struct _term_list)) ;
    /*printf("Creating %d\n", tl) ;*/
    t->next = tl[bin] ;
    tl[bin] = t ;
    t->e = e ;
    t->exps = NULL ;
    return t ;
}

static struct _union_list *find_union_term(struct _union_list **ul, struct env *env, struct _ex_intern *e)
{
    struct _union_list *u ;
    int bin ;

    bin = (((unsigned)e)/4)%TRANS_HASH_SIZE ;

    u = ul[bin] ;
    while (u != NULL) {
        if (u->e==e) return u ;
        u = u->next ;
    }
    u = (struct _union_list *)_th_alloc(TRANSITIVE_SPACE,sizeof(struct _union_list)) ;
    u->next = ul[bin] ;
    ul[bin] = u ;
    u->e = e ;
    u->unions = NULL ;
    return u ;
}

static struct _ex_list *add_env_term(struct env *env,struct _ex_intern *e)
{
    struct _ex_intern *left = _th_get_left_operand(env,e) ;
    struct _ex_intern *right = _th_get_right_operand(env,e) ;
    struct _ex_list *l ;
    struct _term_list *t ;
    int bin, i ;
    unsigned optype;
    unsigned op = get_operator(env,e, &optype);

    if (find_env_term(env,e)) return NULL ;

    _zone_print_exp("Env term", e) ;
#ifdef DEBUG
    _tree_indent() ;
    _zone_print_exp("left %s", left) ;
    _zone_print_exp("right %s", right) ;
    _zone_print0("env terms") ;
    print_term_table(env_terms) ;
    _zone_print0("left table") ;
    print_left_table(env_left) ;
    _zone_print0("right table") ;
    print_right_table(env_right) ;
    check_table() ;
#endif
    bin = 0 ;
    if (e->u.appl.functor==INTERN_AND && e->u.appl.count==2&&
        ((_th_get_left_operand(env,e->u.appl.args[0]) != _th_get_left_operand(env,e->u.appl.args[1]) &&
          _th_get_left_operand(env,e->u.appl.args[0]) != _th_get_right_operand(env,e->u.appl.args[1])) ||
         (_th_get_right_operand(env,e->u.appl.args[0]) != _th_get_left_operand(env,e->u.appl.args[1]) &&
          _th_get_right_operand(env,e->u.appl.args[0]) != _th_get_right_operand(env,e->u.appl.args[1])))) bin = 3 / bin ;
    l = (struct _ex_list *)_th_alloc(TRANSITIVE_SPACE,sizeof(struct _ex_list)) ;
    bin = (((unsigned)e)/4)%TRANS_HASH_SIZE ;
    l->next = env_terms[bin] ;
    l->e = e ;
    env_terms[bin] = l ;

    t = find_term(env_left,env,left) ;
    l->left_next = t->exps ;
    t->exps = l ;

    t = find_term(env_right,env,right) ;
    l->right_next = t->exps ;
    t->exps = l ;

    l->unused = 0 ;
    l->child1 = l->child2 = NULL ;

    if (op==INTERN_SUBSET && optype==INTERN_EPO) {
        if (left->type==EXP_APPL && left->u.appl.functor==INTERN_UNION) {
            for (i = 0; i < left->u.appl.count; ++i) {
                struct _union_list *ul = find_union_term(union_terms,env,left->u.appl.args[i]) ;
                struct _unions *u = (struct _unions *)_th_alloc(TRANSITIVE_SPACE,sizeof(struct _unions)) ;
                u->next = ul->unions ;
                u->term = l ;
            }
        }
    }

    if (is_constant(env,left)) add_env_const(env,left,e->u.appl.functor) ;
    if (is_constant(env,right)) add_env_const(env,right,e->u.appl.functor) ;

#ifdef DEBUG
    _zone_print0("Exit add env term") ;
    check_table() ;
    _tree_undent() ;
#endif
    return l ;
}

static struct _ex_list *add_all_term(struct env *env,struct _ex_intern *e)
{
    struct _ex_intern *left = _th_get_left_operand(env,e) ;
    struct _ex_intern *right = _th_get_right_operand(env,e) ;
    struct _ex_list *l ;
    struct _term_list *t ;
    int bin, i ;
    unsigned optype;
    unsigned op = get_operator(env,e, &optype);

    if (find_all_term(env,e)) return NULL ;
    if (find_env_term(env,e)) return NULL ;

    _zone_print_exp("main term", e) ;
#ifdef DEBUG
    _tree_indent() ;
    _zone_print_exp("left", left) ;
    _zone_print_exp("right", right) ;
    _zone_print0("env terms") ;
    print_term_table(env_terms) ;
    _zone_print0("left table") ;
    print_left_table(env_left) ;
    _zone_print0("right table") ;
    print_right_table(env_right) ;
#endif

    l = (struct _ex_list *)_th_alloc(TRANSITIVE_SPACE,sizeof(struct _ex_list)) ;
    bin = (((unsigned)e)/4)%TRANS_HASH_SIZE ;
    l->next = all_terms[bin] ;
    l->e = e ;
    all_terms[bin] = l ;

    t = find_term(all_left,env,left) ;
    l->left_next = t->exps ;
    t->exps = l ;

    t = find_term(all_right,env,right) ;
    l->right_next = t->exps ;
    t->exps = l ;

    l->unused = 0 ;
    l->child1 = l->child2 = NULL ;

    if (op==INTERN_SUBSET && optype==INTERN_EPO) {
        if (left->type==EXP_APPL && left->u.appl.functor==INTERN_UNION) {
            for (i = 0; i < left->u.appl.count; ++i) {
                struct _union_list *ul = find_union_term(all_union_terms,env,left->u.appl.args[i]) ;
                struct _unions *u = (struct _unions *)_th_alloc(TRANSITIVE_SPACE,sizeof(struct _unions)) ;
                u->next = ul->unions ;
                u->term = l ;
            }
        }
    }

    if (is_constant(env,left)) add_all_const(env,left,e->u.appl.functor) ;
    if (is_constant(env,right)) add_all_const(env,right,e->u.appl.functor) ;

#ifdef DEBUG
    _tree_undent() ;
#endif

    return l ;
}

static int test_true(struct env *env, struct _ex_intern *e)
{
    return e==_ex_true ;
}

static struct _attrib_list *test_subterm_relationship(struct env *env,
       struct _ex_intern *e, int n, unsigned um, unsigned cm)
{
    struct _attrib_list *l, *nl ;
    struct parameter params[1] ;
    struct parameter *p ;
    struct _ex_intern *c ;
    struct match_return *mr ;
    char *mark ;
    int count ;

    params[0].type = FUNCTOR_MATCH ;
    params[0].u.symbol = e->u.appl.functor ;
    l = NULL ;

    /*printf("subterm test %s\n", _th_print_exp(e)) ;*/

    _th_get_attrib(env,um,1,params) ;
    while ((p = _th_get_next_attrib(&count)) != NULL) {
        if ((_th_is_ac(env,e->u.appl.functor) || _th_is_c(env,e->u.appl.functor)) &&
            n >= _th_ac_arity(env,e->u.appl.functor)) {
            nl = (struct _attrib_list *)_th_alloc(TRANSITIVE_SPACE,sizeof(struct _attrib_list)) ;
            nl->next = l ;
            l = nl ;
            l->parameters = p ;
            l->attrib = um ;
            l->count = count ;
        } else {
            if (p[0].u.exp->u.appl.args[n]==p[1].u.exp) {
                nl = (struct _attrib_list *)_th_alloc(TRANSITIVE_SPACE,sizeof(struct _attrib_list)) ;
                nl->next = l ;
                l = nl ;
                l->parameters = p ;
                l->attrib = um ;
                l->count = count ;
            }
        }
    }

    _th_get_attrib(env,cm,1,params) ;
    while ((p = _th_get_next_attrib(&count)) != NULL) {
        if ((_th_is_ac(env,e->u.appl.functor) || _th_is_c(env,e->u.appl.functor)) &&
            n >= _th_ac_arity(env,e->u.appl.functor)) {
            mark = _th_alloc_mark(MATCH_SPACE) ;
            mr = _th_match(env,p[0].u.exp,e) ;
            if (mr==NULL) continue ;
            c = _th_subst(env,mr->theta,p[4].u.exp) ;
            _th_alloc_release(MATCH_SPACE,mark) ;
            if (test_true(env,c)) {
                nl = (struct _attrib_list *)_th_alloc(TRANSITIVE_SPACE,sizeof(struct _attrib_list)) ;
                nl->next = l ;
                l = nl ;
                l->parameters = p ;
                l->attrib = cm ;
                l->count = count ;
            }
        } else {
            if (p[0].u.exp->u.appl.args[n]==p[1].u.exp) {
                nl = (struct _attrib_list *)_th_alloc(TRANSITIVE_SPACE,sizeof(struct _attrib_list)) ;
                mark = _th_alloc_mark(MATCH_SPACE) ;
                mr = _th_match(env,p[0].u.exp,e) ;
                if (mr==NULL) continue ;
                c = _th_subst(env,mr->theta,p[4].u.exp) ;
                _th_alloc_release(MATCH_SPACE,mark) ;
                if (test_true(env,c)) {
                    nl->next = l ;
                    l = nl ;
                    l->parameters = p ;
                    l->attrib = cm ;
                    l->count = count ;
                }
            }
        }
    }

    return l ;
}

static int process_env_term(struct env *env, struct _ex_intern *e,
                            struct _ex_list *c1, struct _ex_list *c2,
                            int add_const) ;

static struct add_list *make_const_comparison(struct env *env,
                                              struct _ex_intern *e1, struct _ex_intern *e2, struct add_list *al)
{
    struct _ex_intern *args[2];
	struct add_list *add;
    unsigned *tmp ;
    if (e1->type != e2->type) {
		return al ;
	}
    if (e1 == e2) {
		return al ;
	}
#ifdef DEBUG
    _zone_print_exp("Add_const_comparison %s", e1) ;
    _zone_print_exp("and %s", e2) ;
    _tree_indent() ;
#endif
    switch(e1->type) {
        case EXP_INTEGER:
            if (_th_big_less(e2->u.integer,e1->u.integer)) {
                args[0] = e2 ;
                args[1] = e1 ;
				add = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
				add->next = al;
				al = add;
                add->e = _ex_intern_appl_env(env,INTERN_NAT_LESS,2,args) ;
				add = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
				add->next = al;
				al = add;
                add->e = _ex_intern_appl_env(env,INTERN_PRECEQ,2,args) ;
            } else {
                args[0] = e1 ;
                args[1] = e2 ;
				add = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
				add->next = al;
				al = add;
                add->e = _ex_intern_appl_env(env,INTERN_NAT_LESS,2,args) ;
				add = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
				add->next = al;
				al = add;
                add->e = _ex_intern_appl_env(env,INTERN_PRECEQ,2,args) ;
            }
            break ;
        case EXP_RATIONAL:
            tmp = _th_big_copy(TRANSITIVE_SPACE,_th_big_multiply(e1->u.rational.numerator,e2->u.rational.denominator)) ;
            if (_th_big_less(tmp,
                _th_big_multiply(e2->u.rational.numerator,e1->u.rational.denominator))) {
                args[0] = e2 ;
                args[1] = e1 ;
				add = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
				add->next = al;
				al = add;
                add->e = _ex_intern_appl_env(env,INTERN_RAT_LESS,2,args) ;
				add = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
				add->next = al;
				al = add;
                add->e = _ex_intern_appl_env(env,INTERN_PRECEQ,2,args) ;
            } else {
                args[0] = e1 ;
                args[1] = e2 ;
				add = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
				add->next = al;
				al = add;
                add->e = _ex_intern_appl_env(env,INTERN_RAT_LESS,2,args) ;
				add = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
			    add->next = al;
				al = add;
                add->e = _ex_intern_appl_env(env,INTERN_PRECEQ,2,args) ;
            }
            break ;
        case EXP_STRING:
            if (strcmp(e1->u.string,e2->u.string)<0) {
                args[0] = e2 ;
                args[1] = e1 ;
				add = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
				add->next = al;
				al = add;
                add->e = _ex_intern_appl_env(env,INTERN_PRECEQ,2,args) ;
            } else {
                args[0] = e1 ;
                args[1] = e2 ;
				add = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
				add->next = al;
				al = add;
                add->e = _ex_intern_appl_env(env,INTERN_PRECEQ,2,args) ;
            }
            break ;
    }

#ifdef DEBUG
	_tree_undent();
#endif

    return al;
}

static int add_const_comparison(struct env *env,
                                struct _ex_intern *e1, struct _ex_intern *e2)
{
	struct add_list *adds = make_const_comparison(env, e1, e2, NULL);

	while (adds) {
		if (process_env_term(env,adds->e,NULL,NULL,0)) return 1;
		adds = adds->next;
	}

    return 0 ;
}

static struct add_list *create_set_term(struct env *env, struct _ex_intern *exp, struct add_list *res)
{
    unsigned optype;
    unsigned op = get_operator(env,exp, &optype);
    struct _ex_intern *l = _th_get_left_operand(env,exp);
    struct _ex_intern *r = _th_get_right_operand(env,exp);
    struct _term_list *tl;
    struct _ex_list *el;
    unsigned optypet, opt;
    struct add_list *re;

    if (op==INTERN_EQUAL) {
        struct _ex_intern *l1 = _ex_intern_appl1_env(env,INTERN_SET,l);
        struct _ex_intern *r1 = _ex_intern_appl1_env(env,INTERN_SET,r);
        tl = find_term(env_left,env,l1);
        el = tl->exps;
        while (el != NULL) {
            opt = get_operator(env,el->e,&optypet);
            if (opt==INTERN_SUBSET) {
                if (optype==INTERN_EQ) {
                    re = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list)) ;
                    re->e = mk_eq(env,INTERN_EQUAL,l1,r1);
                    re->next =res ;
                    res = re ;
                    return res ;
                } else if (optype==INTERN_NE) {
                    re = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list)) ;
                    re->e = _ex_intern_appl2_env(env,INTERN_SEPARATE,l1,r1);
                    re->next =res ;
                    res = re ;
                    return res ;
                }
            }
            el = el->left_next;
        }
        tl = find_term(env_left,env,r1);
        el = tl->exps;
        while (el != NULL) {
            opt = get_operator(env,el->e,&optypet);
            if (opt==INTERN_SUBSET) {
                if (optype==INTERN_EQ) {
                    re = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list)) ;
                    re->e = mk_eq(env,INTERN_EQUAL,l1,r1);
                    re->next =res ;
                    res = re ;
                    return res ;
                } else if (optype==INTERN_NE) {
                    re = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list)) ;
                    re->e = _ex_intern_appl2_env(env,INTERN_SEPARATE,l1,r1);
                    re->next =res ;
                    res = re ;
                    return res ;
                }
            }
            el = el->left_next;
        }
    } else if (op==INTERN_SUBSET && l->type==EXP_APPL && l->u.appl.count==1 && l->u.appl.args[0]->u.appl.functor==INTERN_SET) {
        struct _ex_intern *l1, *r1;
        l1 = l->u.appl.args[0];
        tl = find_term(env_left,env,l1);
        el = tl->exps;
        while (el != NULL) {
            opt = get_operator(env,el->e,&optypet);
            if (opt==INTERN_EQUAL) {
                r1 = _ex_intern_appl1_env(env,INTERN_SET,_th_get_right_operand(env,el->e)) ;
                if (optype==INTERN_EQ) {
                    re = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list)) ;
                    re->e = mk_eq(env,INTERN_EQUAL,l,r1);
                    re->next =res ;
                    res = re ;
                } else if (optype==INTERN_NE) {
                    re = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list)) ;
                    re->e = _ex_intern_appl2_env(env,INTERN_SEPARATE,l,r1);
                    re->next =res ;
                    res = re ;
                }
            }
            el = el->left_next;
        }
        tl = find_term(env_right,env,l1);
        el = tl->exps;
        while (el != NULL) {
            opt = get_operator(env,el->e,&optypet);
            if (opt==INTERN_EQUAL) {
                r1 = _ex_intern_appl1_env(env,INTERN_SET,_th_get_left_operand(env,el->e)) ;
                if (optype==INTERN_EQ) {
                    re = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list)) ;
                    re->e = mk_eq(env,INTERN_EQUAL,l,r1);
                    re->next =res ;
                    res = re ;
                } else if (optype==INTERN_NE) {
                    re = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list)) ;
                    re->e = _ex_intern_appl2_env(env,INTERN_SEPARATE,l,r1);
                    re->next =res ;
                    res = re ;
                }
            }
            el = el->right_next;
        }
    }
    return res;
}

static int process_env_term(struct env *env, struct _ex_intern *e,
                            struct _ex_list *c1, struct _ex_list *c2,
                            int add_consts)
{
    struct _ex_list *list ;
#ifdef DEBUG
    _debug_zone_print1("Processing env term %s", _th_print_exp(e)) ;
    _tree_indent() ;
#endif

    if ((list = add_env_term(env,e)) && !list->unused) {
        int i, ac ;
        struct _ex_intern *l = _th_get_left_operand(env,e) ;
        struct _ex_intern *r = _th_get_right_operand(env,e) ;
        int j, k ;
        struct _ex_intern *res ;
        struct _term_list *tl ;
        struct _ex_list *el ;
        unsigned optype;
        unsigned op = get_operator(env,e,&optype);
        list->child1 = c1 ;
        list->child2 = c2 ;
        if (add_consts && (is_constant(env,l) || is_constant(env,r))) {
            for (i = 0; i < TRANS_HASH_SIZE; ++i) {
                struct _const_list *el = env_consts[i] ;
                while (el != NULL) {
                    if (add_const_comparison(env,l,el->e)) {
#ifdef DEBUG
                        _tree_undent() ;
#endif
                        return 1 ;
                    }
                    if (add_const_comparison(env,r,el->e)) {
#ifdef DEBUG
                        _tree_undent() ;
#endif
                        return 1 ;
                    }
                    el = el->next ;
                }
            }
        }
        if (op==INTERN_SUBSET && optype==INTERN_EPO &&
            r->type==EXP_APPL && r->u.appl.functor==INTERN_UNION) {

            for (i = 0; i < r->u.appl.count; ++i) {
                tl = find_term(env_left,env,r->u.appl.args[i]) ;
                el = tl->exps ;
                while (el != NULL) {
                    op = get_operator(env,el->e,&optype) ;
                    if (op==INTERN_SEPARATE && optype==INTERN_NE) {
                        if (_th_get_right_operand(env,el->e)==l) {
                            struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * r->u.appl.count) ;
                            for (j = 0, k = 0; j < r->u.appl.count; ++j) {
                                if (i != j) {
                                    args[k++] = r->u.appl.args[j] ;
                                }
                            }
                            res = _ex_intern_appl2_env(env,INTERN_SUBSET,l,_ex_intern_appl_env(env,INTERN_UNION,k,args)) ;
                            if (process_env_term(env,res,list,el,add_consts)) {
#ifdef DEBUG
                                _tree_undent() ;
#endif
                                return 1 ;
                            }
                        }
                    }
                    el = el->left_next ;
                }
                tl = find_term(env_right,env,r->u.appl.args[i]) ;
                el = tl->exps ;
                while (el != NULL) {
                    op = get_operator(env,el->e,&optype) ;
                    if (op==INTERN_SEPARATE && optype==INTERN_NE) {
                        if (_th_get_left_operand(env,el->e)==l) {
                            struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * r->u.appl.count) ;
                            for (j = 0, k = 0; j < r->u.appl.count; ++j) {
                                if (i != j) {
                                    args[k++] = r->u.appl.args[j] ;
                                }
                            }
                            res = _ex_intern_appl2_env(env,INTERN_SUBSET,l,_ex_intern_appl_env(env,INTERN_UNION,k,args)) ;
                            if (process_env_term(env,res,list,el,add_consts)) {
#ifdef DEBUG
                                _tree_undent() ;
#endif
                                return 1 ;
                            }
                        }
                    }
                    el = el->right_next ;
                }
            }
        }

        if (op==INTERN_SEPARATE && optype==INTERN_NE) {
            struct _union_list *ul = find_union_term(union_terms,env,l);
            struct _unions *u = ul->unions ;
            while (u != NULL) {
                struct _ex_intern *t = u->term->e ;
                struct _ex_intern **args = ALLOCA(sizeof(struct _ex_intern *) * t->u.appl.args[1]->u.appl.count) ;
                for (i = 0, j = 0; i < t->u.appl.args[1]->u.appl.count; ++i) {
                    if (t->u.appl.args[0]->u.appl.args[i] != l) {
                        args[j++] = t->u.appl.args[1]->u.appl.args[i] ;
                    }
                    res = _ex_intern_appl2_env(env,INTERN_SUBSET,t->u.appl.args[0],_ex_intern_appl_env(env,INTERN_UNION,j,args)) ;
                    if (process_env_term(env,res,list,el,add_consts)) {
#ifdef DEBUG
                        _tree_undent() ;
#endif
                        return 1 ;
                    }
                }
                u = u->next ;
            }
            ul = find_union_term(union_terms,env,r);
            u = ul->unions ;
            while (u != NULL) {
                struct _ex_intern *t = u->term->e ;
                struct _ex_intern **args = ALLOCA(sizeof(struct _ex_intern *) * t->u.appl.args[1]->u.appl.count) ;
                for (i = 0, j = 0; i < t->u.appl.args[1]->u.appl.count; ++i) {
                    if (t->u.appl.args[0]->u.appl.args[i] != r) {
                        args[j++] = t->u.appl.args[1]->u.appl.args[i] ;
                    }
                    res = _ex_intern_appl2_env(env,INTERN_SUBSET,t->u.appl.args[0],_ex_intern_appl_env(env,INTERN_UNION,j,args)) ;
                    if (process_env_term(env,res,list,el,add_consts)) {
#ifdef DEBUG
                        _tree_undent() ;
#endif
                        return 1 ;
                    }
                }
                u = u->next ;
            }
        }

        tl = find_term(env_left,env,l) ;
        el = tl->exps ;
#ifdef DEBUG
        _zone_print_exp("tl->e", tl->e) ;
        _zone_print_exp("el->e", el->e) ;
#endif
        while (el != NULL) {
            res = _th_combine_operands(env,e,el->e,&ac) ;
#ifdef DEBUG
            _zone_print_exp("Combine result", res);
#endif
            if (res != NULL && res != e && res != el->e) {
                if (res==_ex_false) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
                if (ac) {
#ifdef DEBUG
                    _zone_print1("unused e = %s\n", _th_print_exp(e)) ;
                    _zone_print1("unused el->e = %s\n", _th_print_exp(el->e)) ;
#endif
                    el->unused = 1 ;
                    list->unused = 1 ;
                }
                if (process_env_term(env,res,list,el,add_consts)) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
            }
            el = el->left_next ;
        }
        tl = find_term(env_right,env,r) ;
        el = tl->exps ;
        while (el != NULL) {
            res = _th_combine_operands(env,e,el->e,&ac) ;
#ifdef DEBUG
            _zone_print_exp("Combine result", res);
#endif
            if (res != NULL && res != e && res != el->e) {
                if (res==_ex_false) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
                if (ac) {
#ifdef DEBUG
                    _zone_print1("unused e = %s\n", _th_print_exp(e)) ;
                    _zone_print1("unused el->e = %s\n", _th_print_exp(el->e)) ;
#endif
                    el->unused = 1 ;
                    list->unused = 1 ;
                }
                if (process_env_term(env,res,list,el,add_consts)) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
            }
            el = el->right_next ;
        }
        tl = find_term(env_left,env,r) ;
        el = tl->exps ;
        while (el != NULL) {
            res = _th_combine_operands(env,e,el->e,&ac) ;
#ifdef DEBUG
            _zone_print_exp("Combine result", res);
#endif
            if (res != NULL && res != e && res != el->e) {
                if (res==_ex_false) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
                if (ac) {
#ifdef DEBUG
                    _zone_print1("unused e = %s\n", _th_print_exp(e)) ;
                    _zone_print1("unused el->e = %s\n", _th_print_exp(el->e)) ;
#endif
                    el->unused = 1 ;
                    list->unused = 1 ;
                }
                if (process_env_term(env,res,list,el,add_consts)) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
            }
            el = el->left_next ;
        }
        tl = find_term(env_right,env,l) ;
        el = tl->exps ;
        while (el != NULL) {
            res = _th_combine_operands(env,e,el->e,&ac) ;
#ifdef DEBUG
            _zone_print_exp("Combine result", res);
#endif
            if (res != NULL && res != e && res != el->e) {
                if (res==_ex_false) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
                if (ac) {
#ifdef DEBUG
                    _zone_print1("unused e = %s\n", _th_print_exp(e)) ;
                    _zone_print1("unused el->e = %s\n", _th_print_exp(el->e)) ;
#endif
                    el->unused = 1 ;
                    list->unused = 1 ;
                }
                if (process_env_term(env,res,list,el,add_consts)) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
            }
            el = el->right_next ;
        }
    }
#ifdef DEBUG
    _tree_undent() ;
#endif
    return 0 ;
}

struct add_list *break_term(struct env *env, struct _ex_intern *e, struct add_list *al)
{
    int i ;
    struct _attrib_list *l ;
	struct add_list *a;
    int processed ;
#ifdef DEBUG
    _zone_print_exp("Break term", e);
    _tree_indent() ;
#endif
    if (e->type != EXP_APPL) {
#ifdef DEBUG
        _tree_undent() ;
#endif
        return 0 ;
    }

    for (i = 0; i < e->u.appl.count; ++i) {
        processed = 0 ;
        l = test_subterm_relationship(env, e, i, INTERN_SMI, INTERN_CSMI) ;
        while(l != NULL) {
            processed = 1 ;
#ifdef DEBUG
            _zone_print0("case 1") ;
#endif
			a = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
			a->next = al;
			al = a;
			al->e = mk_lt(env,l->parameters[2].u.symbol,e->u.appl.args[i],e);
            l = l->next ;
        }
        l = test_subterm_relationship(env, e, i, INTERN_SMD, INTERN_CSMD) ;
        while(l != NULL) {
            processed = 1 ;
#ifdef DEBUG
            _zone_print0("case 2") ;
#endif
			a = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
			a->next = al;
			al = a;
            al->e = mk_lt(env,l->parameters[2].u.symbol,e,e->u.appl.args[i]);
            l = l->next ;
        }
        l = test_subterm_relationship(env, e, i, INTERN_MI, INTERN_CMI) ;
        while(l != NULL) {
            processed = 1 ;
#ifdef DEBUG
            _zone_print0("case 3") ;
#endif
			a = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
			a->next = al;
			al = a;
            al->e = mk_le(env,l->parameters[2].u.symbol,e->u.appl.args[i],e);
            l = l->next ;
        }
        l = test_subterm_relationship(env, e, i, INTERN_MD, INTERN_CMD) ;
        while(l != NULL) {
            processed = 1 ;
#ifdef DEBUG
            _zone_print0("case 4") ;
#endif
			a = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
			a->next = al;
			al = a;
            al->e = mk_le(env,l->parameters[2].u.symbol,e,e->u.appl.args[i]);
            l = l->next ;
        }
        if (processed) {
#ifdef DEBUG
            _zone_print1("subterm %d", i) ;
#endif
            al = break_term(env,e->u.appl.args[i],al);
        }
    }
#ifdef DEBUG
    _tree_undent() ;
#endif
    return 0 ;
}

int _th_is_binary_term(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *e1, *e2 ;
    int not ;
    if (e->type != EXP_APPL) return 0 ;
    switch (e->u.appl.functor) {
        case INTERN_AND:
            if (e->u.appl.count != 2) return 0 ;
            if (!is_binary_functor(env,e->u.appl.args[0]->u.appl.functor) || !is_binary_functor(env,e->u.appl.args[1]->u.appl.functor)) return 0 ;
            e1 = e->u.appl.args[0] ;
            e2 = e->u.appl.args[1] ;
            not = 0 ;
            if (e1->u.appl.functor==INTERN_NOT) {
                ++not ;
                e1 = e1->u.appl.args[0] ;
            }
            if (e2->u.appl.functor==INTERN_NOT) {
                ++not ; ++not ;
                e2 = e2->u.appl.args[0] ;
            }
            if ((!_th_equal(env,e1->u.appl.args[0],e2->u.appl.args[1]) ||
                 !_th_equal(env,e1->u.appl.args[1],e2->u.appl.args[0])) &&
                (!_th_equal(env,e1->u.appl.args[0],e2->u.appl.args[0]) ||
                 !_th_equal(env,e1->u.appl.args[1],e2->u.appl.args[1]))) return 0 ;
            switch (not) {
                case 0:
                    return is_binary_equal_ord_functor(env,e1->u.appl.functor) &&
                           e1->u.appl.functor==e2->u.appl.functor && !_th_equal(env,e1,e2) ;
                case 1:
                    return is_binary_equal_ord_functors(env,e2->u.appl.functor,e1->u.appl.functor) ;
                case 2:
                    return is_binary_equal_ord_functors(env,e1->u.appl.functor,e2->u.appl.functor) ;
                case 3:
                    return is_binary_ord_functors(env,e1->u.appl.functor,e2->u.appl.functor) ||
                           is_binary_ord_functors(env,e2->u.appl.functor,e1->u.appl.functor) ||
                           (is_binary_ord_functor(env,e1->u.appl.functor) &&
                            e1->u.appl.functor==e2->u.appl.functor && !_th_equal(env,e1,e2)) ;
            }
            break ;
        case INTERN_OR:
            if (e->u.appl.count != 2) return 0 ;
            if (!is_binary_functor(env,e->u.appl.args[0]->u.appl.functor) || !is_binary_functor(env,e->u.appl.args[1]->u.appl.functor)) return 0 ;
            e1 = e->u.appl.args[0] ;
            e2 = e->u.appl.args[1] ;
            not = 0 ;
            if (e1->u.appl.functor==INTERN_NOT) {
                ++not ;
                e1 = e1->u.appl.args[0] ;
            }
            if (e2->u.appl.functor==INTERN_NOT) {
                ++not ; ++not ;
                e2 = e2->u.appl.args[0] ;
            }
            if ((!_th_equal(env,e1->u.appl.args[0],e2->u.appl.args[1]) ||
                 !_th_equal(env,e1->u.appl.args[1],e2->u.appl.args[0])) &&
                (!_th_equal(env,e1->u.appl.args[0],e2->u.appl.args[0]) ||
                 !_th_equal(env,e1->u.appl.args[1],e2->u.appl.args[1]))) return 0 ;
            switch (not) {
                case 0:
                    if (is_binary_ord_functors(env,e1->u.appl.functor,e2->u.appl.functor) ||
                        is_binary_ord_functors(env,e2->u.appl.functor,e1->u.appl.functor)) return 1 ;
                    if (e1->u.appl.functor != e2->u.appl.functor) return 0 ;
                    return is_binary_ord_functor(env,e1->u.appl.functor) && !_th_equal(env,e1,e2) ;
                case 1:
                    return is_binary_ord_functors(env,e1->u.appl.functor,e2->u.appl.functor) ;
                case 2:
                    return is_binary_ord_functors(env,e2->u.appl.functor,e1->u.appl.functor) ;
                case 3:
                    if (e1->u.appl.functor != e2->u.appl.functor) return 0 ;
                    return is_binary_equal_ord_functor(env,e1->u.appl.functor) && !_th_equal(env,e1,e2) ;
            }
            break ;
        case INTERN_SEPARATE:
            return e->u.appl.count==2;
        case INTERN_NOT:
            return e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.count==2 &&
                   is_binary_functor(env,e->u.appl.args[0]->u.appl.functor) ;
        default:
            return e->u.appl.count==2 && is_binary_functor(env,e->u.appl.functor) ;
    }
    return 0 ;
}

static int term_distance(struct env *env, struct _ex_intern *term1, struct _ex_intern *term2)
{
    struct _ex_intern **args1, **args2;
    int count1, count2;
    int i, count, *used, j;

    if (term1->type==EXP_APPL && term1->u.appl.functor==INTERN_NAT_PLUS) {
        count1 = term1->u.appl.count;
        args1 = term1->u.appl.args;
    } else {
        count1 = 1;
        args1 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *));
        args1[0] = term1;
    }

    if (term2->type==EXP_APPL && term2->u.appl.functor==INTERN_NAT_PLUS) {
        count2 = term2->u.appl.count;
        args2 = term2->u.appl.args;
    } else {
        count2 = 1;
        args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *));
        args2[0] = term2;
    }

    used = (int *)ALLOCA(sizeof(int) * count2);
    for (i = 0; i < count2; ++i) {
        used[i] = 0;
    }

    count = 0;
    for (i = 0; i < count1; ++i) {
        if (args1[i]->type != EXP_INTEGER) {
            for (j = 0; j < count2; ++j) {
                if (_th_get_core(env,args1[i])==_th_get_core(env,args2[j])) {
                    used[j] = 1;
                    goto cont;
                }
            }
            ++count;
cont:;
        }
    }

    for (i = 0; i < count2; ++i) {
        if (!used[i]) ++count;
    }

    return i;
}

#define USE_LESS          -2
#define USE_LESS_EQUAL    -1
#define USE_EQUAL         0
#define USE_GREATER_EQUAL 1
#define USE_GREATER       2

static int operator_mode;
static struct _ex_intern *operand, *replace;
static int is_relevant(struct env *env, struct _ex_intern *term, struct _ex_intern *l, int mode)
{
    if (term->u.appl.functor==INTERN_EQUAL) {
        operator_mode = USE_EQUAL;
        if (_th_get_core(env,term->u.appl.args[0])==l) {
            operand = term->u.appl.args[0];
            replace = term->u.appl.args[1];
        } else {
            operand = term->u.appl.args[1];
            replace = term->u.appl.args[0];
        }
        return 1;
    }
    if (term->u.appl.functor==INTERN_NOT) {
        term = term->u.appl.args[0];
        if (term->u.appl.functor != INTERN_NAT_LESS) {
            return 0;
        }
        if (_th_get_core(env,term->u.appl.args[1])==l && mode < 0) {
            operator_mode = USE_LESS_EQUAL;
            operand = term->u.appl.args[1];
            replace = term->u.appl.args[0];
            return 1;
        }
        if (_th_get_core(env,term->u.appl.args[0])==l && mode > 0) {
            operator_mode = USE_GREATER_EQUAL;
            operand = term->u.appl.args[0];
            replace = term->u.appl.args[1];
            return 1;
        }
        return 0;
    }
    if (term->u.appl.functor==INTERN_NAT_LESS) {
        if (_th_get_core(env,term->u.appl.args[1])==l && mode > 0) {
            operator_mode = USE_GREATER;
            operand = term->u.appl.args[1];
            replace = term->u.appl.args[0];
            return 1;
        }
        if (_th_get_core(env,term->u.appl.args[0])==l && mode < 0) {
            operator_mode = USE_LESS;
            operand = term->u.appl.args[0];
            replace = term->u.appl.args[1];
            return 1;
        }
    }
    return 0;
}

static struct _ex_intern *add_a_term(struct env *env, struct _ex_intern *sum, struct _ex_intern *t)
{
    struct _ex_intern *t_coef = _th_get_coef(env,t);
    struct _ex_intern *t_core = _th_get_core(env,t);
    int i, j;
    struct _ex_intern **args;

    //_zone_print_exp("Adding", t);
    //_zone_print_exp("To", sum);

    if (sum==NULL) return t;

    if (sum->type != EXP_APPL || sum->u.appl.functor != INTERN_NAT_PLUS) {
        struct _ex_intern *s_core = _th_get_core(env,sum);
        struct _ex_intern *s_coef = _th_get_coef(env,sum);
        if (t_core != s_core) {
            return _ex_intern_appl2_env(env,INTERN_NAT_PLUS,t,sum);
        }
        t_coef = _ex_intern_integer(_th_big_add(t_coef->u.integer,s_coef->u.integer));
        return _th_build_term(env,t_coef,t_core);
    } else {
        for (i = 0; i < sum->u.appl.count; ++i) {
            struct _ex_intern *s_core = _th_get_core(env,sum->u.appl.args[i]);
            struct _ex_intern *s_coef = _th_get_coef(env,sum->u.appl.args[i]);
            if (t_core==s_core) {
                t_coef = _ex_intern_integer(_th_big_add(t_coef->u.integer,s_coef->u.integer));
                args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern **) * sum->u.appl.count);
                for (j = 0; j < sum->u.appl.count; ++j) {
                    if (i==j) {
                        args[j] = _th_build_term(env,t_coef,t_core);
                    } else {
                        args[j] = sum->u.appl.args[j];
                    }
                }
                return _ex_intern_appl_env(env,INTERN_NAT_PLUS,j,args);
            }
        }
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (sum->u.appl.count + 1));
        for (i = 0; i < sum->u.appl.count; ++i) {
            args[i] = sum->u.appl.args[i];
        }
        args[i++] = t;
        return _ex_intern_appl_env(env,INTERN_NAT_PLUS,i,args);
    }
}

static struct _ex_intern *replace_a_term(struct env *env, struct _ex_intern *term, struct _ex_intern *right, struct _ex_intern *factor, struct _ex_intern *remainder, struct _ex_intern *target)
{
    struct _ex_intern *t_coef = _th_get_coef(env,term);
    struct _ex_intern *t_core = _th_get_core(env,term);

    struct _ex_intern *new_term = NULL;
    int i;

    //_zone_print_exp("term", term);
    //_zone_print_exp("right", right);
    //_zone_print_exp("target", target);

    if (target->type != EXP_APPL || target->u.appl.functor != INTERN_NAT_PLUS) {
        struct _ex_intern *s_coef = _th_get_coef(env,target);
        struct _ex_intern *s_core = _th_get_core(env,target);
        if (s_core != t_core) {
            printf("replace_a_term: term not present\n");
            exit(1);
        }
        if (remainder) new_term = add_a_term(env, new_term, _th_build_term(env,remainder,t_core));
        //t_coef = _ex_intern_integer(_th_big_divide(s_coef->u.integer,t_coef->u.integer));        
    } else {
        int added = 0;
        for (i = 0; i < target->u.appl.count; ++i) {
            struct _ex_intern *s_coef = _th_get_coef(env,target->u.appl.args[i]);
            struct _ex_intern *s_core = _th_get_core(env,target->u.appl.args[i]);
            if (s_core==t_core) {
                if (remainder) new_term = add_a_term(env, new_term, _th_build_term(env,remainder,t_core));
                //t_coef = _ex_intern_integer(_th_big_divide(s_coef->u.integer,t_coef->u.integer));
                added = 1;
            } else {
                new_term = add_a_term(env, new_term, target->u.appl.args[i]);
            }
            //_zone_print_exp("new_term", new_term);
        }
        if (!added) {
            printf("replace_a_term: term not present\n");
            exit(1);
        }
    }

    if (right->type!=EXP_APPL || right->u.appl.functor!=INTERN_NAT_PLUS) {
        struct _ex_intern *s_coef = _th_get_coef(env,right);
        struct _ex_intern *s_core = _th_get_core(env,right);
        s_coef = _ex_intern_integer(_th_big_multiply(factor->u.integer,s_coef->u.integer));
        new_term = add_a_term(env,new_term,_th_build_term(env,s_coef,s_core));
    } else {
        for (i = 0; i < right->u.appl.count; ++i) {
            struct _ex_intern *s_coef = _th_get_coef(env,right->u.appl.args[i]);
            struct _ex_intern *s_core = _th_get_core(env,right->u.appl.args[i]);
            s_coef = _ex_intern_integer(_th_big_multiply(factor->u.integer,s_coef->u.integer));
            new_term = add_a_term(env,new_term,_th_build_term(env,s_coef,s_core));
        }
    }

    //_zone_print_exp("return", new_term);

    return new_term;
}

static char s[400];

static char *pr(char *p, struct _ex_intern *e)
{
    int i;
    char n[10];

    if (e==NULL) {
        strcpy(p,"<NULL>");
        p += strlen(p);
        return p;
    }

    switch (e->type) {
        case EXP_APPL:
            strcpy(p,_th_intern_decode(e->u.appl.functor));
            p += strlen(p);
            *p++ = '(';
            if (e->u.appl.count > 0) {
                p = pr(p,e->u.appl.args[0]);
                for (i = 1; i < e->u.appl.count; ++i) {
                    *p++ = ',';
                    p = pr(p,e->u.appl.args[i]);
                }
            }
            *p++ = ')';
            return p;
        case EXP_VAR:
            strcpy(p,_th_intern_decode(e->u.var));
            p += strlen(p);
            return p;
        case EXP_INTEGER:
            sprintf(n, "%d", e->u.integer[1]);
            strcpy(p,n);
            p += strlen(p);
            return p;
        case EXP_MARKED_VAR:
            strcpy(p,_th_intern_decode(e->u.var));
            p += strlen(p);
            *p++ = '\'';
            return p;
        default:
            return p;
    }
}

static char *p_exp(struct _ex_intern *e)
{
    char *p = pr(s,e);
    *p = 0;
    return s;
}

struct step_list {
    struct step_list *next;
    int operator_type;
    struct _ex_intern *new_current;
    struct _ex_intern *rule;
    int distance_decrease;
};

static struct step_list *get_possible_steps(struct env *env,
                                            struct _ex_intern *current,
                                            struct _ex_intern *target,
                                            int mode)
{
    struct _ex_intern **args1, **args2;
    int count1, count2;
    int i, j;
    struct _ex_intern *c_core, *c_coef, *t_core, *t_coef, *r, *new_current;
    struct _ex_intern *diff;
    struct rule_operand_list *iterator;
    int d1;
    struct step_list *ret = NULL, *sl;

    if (current->type==EXP_APPL && current->u.appl.functor==INTERN_NAT_PLUS) {
        count1 = current->u.appl.count;
        args1 = current->u.appl.args;
    } else {
        count1 = 1;
        args1 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *));
        args1[0] = current;
    }

    if (target->type==EXP_APPL && target->u.appl.functor==INTERN_NAT_PLUS) {
        count2 = target->u.appl.count;
        args2 = target->u.appl.args;
    } else {
        count2 = 1;
        args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *));
        args2[0] = target;
    }

    for (i = 0; i < count1; ++i) {
        for (j = 0; j < count2; ++j) {
            if (args1[i]==args2[j]) goto cont;
        }
        if (args1[i]->type==EXP_INTEGER) goto cont;
        c_core = _th_get_core(env,args1[i]);
        c_coef = _th_get_coef(env,args1[i]);
        for (j = 0; j < count2; ++j) {
            t_core = _th_get_core(env,args2[j]);
            t_coef = _th_get_coef(env,args2[j]);
            if (t_core==c_core) break;
        }
        if (t_core != c_core) {
            diff = c_coef;
            t_coef = NULL;
        } else {
            diff = _ex_intern_integer(_th_big_sub(c_coef->u.integer,t_coef->u.integer));
        }
        //printf("    diff %d %d\n", diff->u.integer[0], diff->u.integer[1]);
        _zone_print_exp("Checking term", args1[i]);
        //printf("    c_coef %s\n", p_exp(c_coef));
        //printf("    c_core %s\n", p_exp(c_core));
        //printf("    t_core %s\n", p_exp(t_core));
        //printf("    Checking term %s\n", p_exp(args1[i]));
        r = _th_get_first_rule_by_operand(env,c_core,&iterator);
        _zone_print_exp("c_core", c_core);
        _tree_indent();
        while (r != NULL) {
            struct _ex_intern *rule = r;
            r = _th_unmark_vars(env,r);
            r = _th_extract_relation(env, r);
            _zone_print_exp("r", r);
            if (!rule->rule_simplified && is_relevant(env,r,c_core,mode)) {
                struct _ex_intern *o_coef = _th_get_coef(env,operand);
                int invert = 0;
                unsigned *z;
                //printf("        rule %s\n", p_exp(r));
                //printf("        o_coef %d %d\n", o_coef->u.integer[0], o_coef->u.integer[1]);
                //printf("        operator_mode %d\n", operator_mode);
                _zone_print0("relevant");
                if (_th_big_is_negative(diff->u.integer)) {
                    diff = _ex_intern_integer(_th_complement(diff->u.integer));
                    //printf("            invert 1\n");
                    invert = 1;
                }
                if (_th_big_is_negative(o_coef->u.integer)) {
                    o_coef = _ex_intern_integer(_th_complement(o_coef->u.integer));
                    //printf("            invert 2\n");
                    invert = 1-invert;
                }
                z = _th_big_mod(diff->u.integer,o_coef->u.integer);
                //printf("        z = %d %d\n", z[0], z[1]);
                if (z[0] != 1 || z[1] != 0) goto cont1;
                if (mode==USE_EQUAL && operator_mode!=USE_EQUAL) goto cont1;
                if (!invert && mode>0 && operator_mode<0) goto cont1;
                if (invert && mode<0 && operator_mode<0) goto cont1;
                if (!invert && mode<0 && operator_mode>0) goto cont1;
                if (invert && mode>0 && operator_mode>0) goto cont1;
                d1 = term_distance(env,current,target);
                z = _th_big_divide(diff->u.integer,o_coef->u.integer);
                if (invert) z = _th_complement(z);
                new_current = replace_a_term(env,operand,replace,_ex_intern_integer(z),t_coef,current);
                d1 -= term_distance(env,new_current,target);
                //printf("            adding\n");
                sl = (struct step_list *)_th_alloc(REWRITE_SPACE,sizeof(struct step_list));
                sl->next = ret;
                sl->rule = r;
                sl->new_current = new_current;
                sl->distance_decrease = d1;
                if (invert) operator_mode = 0-operator_mode;
                sl->operator_type = operator_mode;
                ret = sl;
            }
cont1:
            r = _th_get_next_rule_by_operand(c_core,&iterator);
        }
        _tree_undent();
cont:;
    }
    return ret;
}

static struct _ex_intern *offset;
static struct _ex_intern *strip_offset(struct env *env, struct _ex_intern *e)
{
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NAT_PLUS) {
        struct _ex_intern **args;
        int i, j;
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
        offset = NULL;
        for (i = 0, j = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type==EXP_INTEGER) {
                offset = e->u.appl.args[i];
            } else {
                args[j++] = e->u.appl.args[i];
            }
        }
        if (offset) {
            if (j==1) {
                return args[0];
            } else {
                return _ex_intern_appl_env(env,INTERN_NAT_PLUS,j,args);
            }
        } else {
            offset = _ex_intern_small_integer(0);
            return e;
        }
    } else if (e->type==EXP_INTEGER) {
        offset = e;
        return _ex_intern_small_integer(0);
    } else {
        offset = _ex_intern_small_integer(0);
        return e;
    }
}

static int search_ineq_path(struct env *env,
                            struct _ex_intern *current,
                            struct _ex_intern *target,
                            int depth,
                            int increase_count,
                            int mode)
{
    struct _ex_intern *cb, *tb, *co, *to;
    _zone_print_exp("Search path from", current);
    _zone_print_exp("to", target);
    _zone_print1("mode %d", mode);
    //printf("Search path from %s\n", p_exp(current));
    //printf("to %s\n", p_exp(target));
    //printf("mode %d\n", mode);
    cb = strip_offset(env,current);
    co = offset;
    tb = strip_offset(env,target);
    to = offset;
    if (cb==tb) {
        if (co==to && (mode==USE_EQUAL || mode==USE_LESS_EQUAL || mode==USE_GREATER_EQUAL)) return 1;
        if (_th_big_less(co->u.integer,to->u.integer) && (mode==USE_LESS_EQUAL || mode==USE_LESS)) return 1;
        if (_th_big_less(to->u.integer,co->u.integer) && (mode==USE_GREATER_EQUAL || mode==USE_GREATER)) return 1;
    }
    _tree_indent();

    if (depth > 0) {
        struct step_list *steps = get_possible_steps(env,current,target,mode);
        while (steps != NULL) {
            int new_mode = mode;
            int new_increase_count = increase_count;
            _zone_print_exp("Checking step",steps->new_current);
            //printf("Checking step %s\n", p_exp(steps->new_current));
            _tree_indent();
            //printf("with rule %s\n", p_exp(steps->rule));
            //printf("distance decrease %d\n", steps->distance_decrease);
            //printf("operator_type %d\n", steps->operator_type);
            _zone_print_exp("with rule", steps->rule);
            _zone_print1("distance_decrease %d", steps->distance_decrease);
            _zone_print1("operator_type %d",steps->operator_type);
            if ((mode==USE_GREATER || mode==USE_LESS) &&
                steps->rule->u.appl.functor==INTERN_NAT_LESS) {
                if (mode==USE_GREATER) {
                    new_mode = USE_GREATER_EQUAL;
                } else {
                    new_mode = USE_LESS_EQUAL;
                }
            }
            if (increase_count > 0 && steps->distance_decrease < 0) {
                --new_increase_count;
            }
            _tree_undent();
            if (search_ineq_path(env,steps->new_current,target,depth-1,new_increase_count,new_mode)) {
                _tree_undent();
                //printf("GOOD\n");
                _zone_print0("GOOD");
                //printf("Found path\n");
                //exit(1);
                return 1;
            }
            //printf("BAD\n");
            _zone_print0("BAD");
            steps = steps->next;
        }
        _tree_undent();
        return 0;
    } else {
        _tree_undent();
        return 0;
    }
}

struct _ex_intern *_th_search_equality(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *l = e->u.appl.args[0];
    struct _ex_intern *r = e->u.appl.args[1];
    int lsize, rsize;

    if (l->type==EXP_APPL && l->u.appl.functor==INTERN_NAT_PLUS) {
        lsize = l->u.appl.count;
    } else {
        lsize = 1;
    }
    if (r->type==EXP_APPL && r->u.appl.functor==INTERN_NAT_PLUS) {
        rsize = r->u.appl.count;
    } else {
        rsize = 1;
    }

    if (lsize==1 && rsize==1) return NULL;

    //printf("Searching equality %s\n", _th_print_exp(e));

    if (lsize < rsize && l->type != EXP_INTEGER) {
        if (search_ineq_path(env,l,r,3,1,USE_EQUAL)) return _ex_true;
        if (search_ineq_path(env,l,r,3,1,USE_GREATER)) return _ex_false;
        if (search_ineq_path(env,l,r,3,1,USE_LESS)) return _ex_false;
    } else {
        if (search_ineq_path(env,r,l,3,1,USE_EQUAL)) return _ex_true;
        if (search_ineq_path(env,r,l,3,1,USE_GREATER)) return _ex_false;
        if (search_ineq_path(env,r,l,3,1,USE_LESS)) return _ex_false;
    }
    return NULL;
}

struct _ex_intern *_th_search_less(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *l = e->u.appl.args[0];
    struct _ex_intern *r = e->u.appl.args[1];
    int lsize, rsize;

    //printf("Searching less %s\n", _th_print_exp(e));

    if (l->type==EXP_APPL && l->u.appl.functor==INTERN_NAT_PLUS) {
        lsize = l->u.appl.count;
    } else {
        lsize = 1;
    }
    if (r->type==EXP_APPL && r->u.appl.functor==INTERN_NAT_PLUS) {
        rsize = r->u.appl.count;
    } else {
        rsize = 1;
    }
    if (lsize < rsize && l->type != EXP_INTEGER) {
        if (search_ineq_path(env,l,r,3,1,USE_GREATER_EQUAL)) {
            //printf("Reduced %s to false 1\n", _th_print_exp(e));
            return _ex_false;
        }
        if (search_ineq_path(env,l,r,3,1,USE_LESS)) {
            //printf("Reduced %s to true 1\n", _th_print_exp(e));
            return _ex_true;
        }
    } else {
        if (search_ineq_path(env,r,l,3,1,USE_GREATER)) {
            //printf("Reduced %s to true 2\n", _th_print_exp(e));
            return _ex_true;
        }
        if (search_ineq_path(env,r,l,3,1,USE_LESS_EQUAL)) {
            //printf("Reduced %s to false 2\n", _th_print_exp(e));
            return _ex_false;
        }
    }
    return NULL;
}

static int r_term_distance(struct env *env, struct _ex_intern *term1, struct _ex_intern *term2)
{
    struct _ex_intern **args1, **args2;
    int count1, count2;
    int i, count, *used, j;

    if (term1->type==EXP_APPL && term1->u.appl.functor==INTERN_RAT_PLUS) {
        count1 = term1->u.appl.count;
        args1 = term1->u.appl.args;
    } else {
        count1 = 1;
        args1 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *));
        args1[0] = term1;
    }

    if (term2->type==EXP_APPL && term2->u.appl.functor==INTERN_RAT_PLUS) {
        count2 = term2->u.appl.count;
        args2 = term2->u.appl.args;
    } else {
        count2 = 1;
        args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *));
        args2[0] = term2;
    }

    used = (int *)ALLOCA(sizeof(int) * count2);
    for (i = 0; i < count2; ++i) {
        used[i] = 0;
    }

    count = 0;
    for (i = 0; i < count1; ++i) {
        if (args1[i]->type != EXP_RATIONAL) {
            for (j = 0; j < count2; ++j) {
                if (_th_r_get_core(env,args1[i])==_th_r_get_core(env,args2[j])) {
                    used[j] = 1;
                    goto cont;
                }
            }
            ++count;
cont:;
        }
    }

    for (i = 0; i < count2; ++i) {
        if (!used[i]) ++count;
    }

    return i;
}

#define USE_LESS          -2
#define USE_LESS_EQUAL    -1
#define USE_EQUAL         0
#define USE_GREATER_EQUAL 1
#define USE_GREATER       2

static int r_is_relevant(struct env *env, struct _ex_intern *term, struct _ex_intern *l, int mode)
{
    if (term->u.appl.functor==INTERN_EQUAL) {
        operator_mode = USE_EQUAL;
        if (_th_r_get_core(env,term->u.appl.args[0])==l) {
            operand = term->u.appl.args[0];
            replace = term->u.appl.args[1];
        } else {
            operand = term->u.appl.args[1];
            replace = term->u.appl.args[0];
        }
        return 1;
    }
    if (term->u.appl.functor==INTERN_NOT) {
        term = term->u.appl.args[0];
        if (term->u.appl.functor != INTERN_RAT_LESS) {
            return 0;
        }
        if (_th_r_get_core(env,term->u.appl.args[1])==l && mode < 0) {
            operator_mode = USE_LESS_EQUAL;
            operand = term->u.appl.args[1];
            replace = term->u.appl.args[0];
            return 1;
        }
        if (_th_r_get_core(env,term->u.appl.args[0])==l && mode > 0) {
            operator_mode = USE_GREATER_EQUAL;
            operand = term->u.appl.args[0];
            replace = term->u.appl.args[1];
            return 1;
        }
        return 0;
    }
    if (term->u.appl.functor==INTERN_RAT_LESS) {
        if (_th_r_get_core(env,term->u.appl.args[1])==l && mode > 0) {
            operator_mode = USE_GREATER;
            operand = term->u.appl.args[1];
            replace = term->u.appl.args[0];
            return 1;
        }
        if (_th_r_get_core(env,term->u.appl.args[0])==l && mode < 0) {
            operator_mode = USE_LESS;
            operand = term->u.appl.args[0];
            replace = term->u.appl.args[1];
            return 1;
        }
    }
    return 0;
}

static struct _ex_intern *r_add_a_term(struct env *env, struct _ex_intern *sum, struct _ex_intern *t)
{
    struct _ex_intern *t_coef = _th_r_get_coef(env,t);
    struct _ex_intern *t_core = _th_r_get_core(env,t);
    int i, j;
    struct _ex_intern **args;

    //_zone_print_exp("Adding", t);
    //_zone_print_exp("To", sum);

    if (sum==NULL) return t;

    if (sum->type != EXP_APPL || sum->u.appl.functor != INTERN_RAT_PLUS) {
        struct _ex_intern *s_core = _th_r_get_core(env,sum);
        struct _ex_intern *s_coef = _th_r_get_coef(env,sum);
        if (t_core != s_core) {
            return _ex_intern_appl2_env(env,INTERN_RAT_PLUS,t,sum);
        }
        t_coef = _th_add_rationals(t_coef,s_coef);
        return _th_r_build_term(env,t_coef,t_core);
    } else {
        for (i = 0; i < sum->u.appl.count; ++i) {
            struct _ex_intern *s_core = _th_r_get_core(env,sum->u.appl.args[i]);
            struct _ex_intern *s_coef = _th_r_get_coef(env,sum->u.appl.args[i]);
            if (t_core==s_core) {
                t_coef = _th_add_rationals(t_coef,s_coef);
                args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern **) * sum->u.appl.count);
                for (j = 0; j < sum->u.appl.count; ++j) {
                    if (i==j) {
                        args[j] = _th_r_build_term(env,t_coef,t_core);
                    } else {
                        args[j] = sum->u.appl.args[j];
                    }
                }
                return _ex_intern_appl_env(env,INTERN_RAT_PLUS,j,args);
            }
        }
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (sum->u.appl.count + 1));
        for (i = 0; i < sum->u.appl.count; ++i) {
            args[i] = sum->u.appl.args[i];
        }
        args[i++] = t;
        return _ex_intern_appl_env(env,INTERN_RAT_PLUS,i,args);
    }
}

static struct _ex_intern *r_replace_a_term(struct env *env, struct _ex_intern *term, struct _ex_intern *right, struct _ex_intern *factor, struct _ex_intern *remainder, struct _ex_intern *target)
{
    struct _ex_intern *t_coef = _th_r_get_coef(env,term);
    struct _ex_intern *t_core = _th_r_get_core(env,term);

    struct _ex_intern *new_term = NULL;
    int i;

    //_zone_print_exp("term", term);
    //_zone_print_exp("right", right);
    //_zone_print_exp("target", target);
    //_zone_print_exp("factor", factor);

    if (target->type != EXP_APPL || target->u.appl.functor != INTERN_RAT_PLUS) {
        struct _ex_intern *s_coef = _th_r_get_coef(env,target);
        struct _ex_intern *s_core = _th_r_get_core(env,target);
        if (s_core != t_core) {
            printf("replace_a_term: term not present\n");
            exit(1);
        }
        if (remainder) new_term = r_add_a_term(env, new_term, _th_r_build_term(env,remainder,t_core));
        //t_coef = _ex_intern_integer(_th_big_divide(s_coef->u.integer,t_coef->u.integer));        
    } else {
        int added = 0;
        for (i = 0; i < target->u.appl.count; ++i) {
            struct _ex_intern *s_coef = _th_r_get_coef(env,target->u.appl.args[i]);
            struct _ex_intern *s_core = _th_r_get_core(env,target->u.appl.args[i]);
            if (s_core==t_core) {
                if (remainder) new_term = r_add_a_term(env, new_term, _th_r_build_term(env,remainder,t_core));
                //t_coef = _ex_intern_integer(_th_big_divide(s_coef->u.integer,t_coef->u.integer));
                added = 1;
            } else {
                new_term = r_add_a_term(env, new_term, target->u.appl.args[i]);
            }
            //_zone_print_exp("new_term", new_term);
        }
        if (!added) {
            printf("replace_a_term: term not present\n");
            exit(1);
        }
    }

    if (right->type!=EXP_APPL || right->u.appl.functor!=INTERN_RAT_PLUS) {
        struct _ex_intern *s_coef = _th_r_get_coef(env,right);
        struct _ex_intern *s_core = _th_r_get_core(env,right);
        //_zone_print_exp("s_coef", s_coef);
        s_coef = _th_multiply_rationals(factor,s_coef);
        //_zone_print_exp("s_coef", s_coef);
        //_zone_print_exp("s_core", s_core);
        new_term = r_add_a_term(env,new_term,_th_r_build_term(env,s_coef,s_core));
    } else {
        for (i = 0; i < right->u.appl.count; ++i) {
            struct _ex_intern *s_coef = _th_r_get_coef(env,right->u.appl.args[i]);
            struct _ex_intern *s_core = _th_r_get_core(env,right->u.appl.args[i]);
            s_coef = _th_multiply_rationals(factor,s_coef);
            new_term = r_add_a_term(env,new_term,_th_build_term(env,s_coef,s_core));
        }
    }

    //_zone_print_exp("return", new_term);

    return new_term;
}

static struct step_list *r_get_possible_steps(struct env *env,
                                            struct _ex_intern *current,
                                            struct _ex_intern *target,
                                            int mode)
{
    struct _ex_intern **args1, **args2;
    int count1, count2;
    int i, j;
    struct _ex_intern *c_core, *c_coef, *t_core, *t_coef, *r, *new_current;
    struct _ex_intern *diff;
    struct rule_operand_list *iterator;
    int d1;
    struct step_list *ret = NULL, *sl;

    //fprintf(stderr, "current %s\n", _th_print_exp(current));
    //fprintf(stderr, "target %s\n", _th_print_exp(target));
    //fflush(stderr);

    if (current->type==EXP_APPL && current->u.appl.functor==INTERN_RAT_PLUS) {
        count1 = current->u.appl.count;
        args1 = current->u.appl.args;
    } else {
        count1 = 1;
        args1 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *));
        args1[0] = current;
    }

    if (target->type==EXP_APPL && target->u.appl.functor==INTERN_RAT_PLUS) {
        count2 = target->u.appl.count;
        args2 = target->u.appl.args;
    } else {
        count2 = 1;
        args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *));
        args2[0] = target;
    }

    for (i = 0; i < count1; ++i) {
        for (j = 0; j < count2; ++j) {
            if (args1[i]==args2[j]) goto cont;
        }
        if (args1[i]->type==EXP_RATIONAL) goto cont;
        //fprintf(stderr, "args1[%d] = %s\n", i, _th_print_exp(args1[i]));
        c_core = _th_r_get_core(env,args1[i]);
        c_coef = _th_r_get_coef(env,args1[i]);
        //fprintf(stderr, "c_core %s\n", _th_print_exp(c_core));
        //fprintf(stderr, "c_coef %s\n", _th_print_exp(c_coef));
        //fflush(stderr);
        for (j = 0; j < count2; ++j) {
            //fprintf(stderr, "args2[%d] = %s\n", j, _th_print_exp(args2[j]));
            t_core = _th_r_get_core(env,args2[j]);
            t_coef = _th_r_get_coef(env,args2[j]);
            //fprintf(stderr, "t_core %s\n", _th_print_exp(t_core));
            //fprintf(stderr, "t_coef %s\n", _th_print_exp(t_coef));
            //fflush(stderr);
            if (t_core==c_core) break;
        }
        if (t_core != c_core) {
            diff = c_coef;
            t_coef = NULL;
            //fprintf(stderr,"Here1\n");
            //fflush(stderr);
        } else {
            diff = _th_subtract_rationals(c_coef,t_coef);
            //fprintf(stderr,"Here2\n");
            //fflush(stderr);
        }
        //printf("    diff %d %d\n", diff->u.integer[0], diff->u.integer[1]);
        _zone_print_exp("Checking term", args1[i]);
        //printf("    c_coef %s\n", p_exp(c_coef));
        //printf("    c_core %s\n", p_exp(c_core));
        //printf("    t_core %s\n", p_exp(t_core));
        //printf("    Checking term %s\n", p_exp(args1[i]));
        r = _th_get_first_rule_by_operand(env,c_core,&iterator);
        _zone_print_exp("c_core", c_core);
        _tree_indent();
        while (r != NULL) {
            struct _ex_intern *rule = r;
            r = _th_unmark_vars(env,r);
            r = _th_extract_relation(env, r);
            _zone_print_exp("r", r);
            if (!rule->rule_simplified && r_is_relevant(env,r,c_core,mode)) {
                struct _ex_intern *o_coef = _th_r_get_coef(env,operand);
                int invert = 0;
                struct _ex_intern *z;
                //fprintf(stderr, "operand = %s\n", _th_print_exp(operand));
                //fprintf(stderr, "o_coef = %s\n", _th_print_exp(o_coef));
                //fflush(stderr);
                //printf("        rule %s\n", p_exp(r));
                //printf("        o_coef %d %d\n", o_coef->u.integer[0], o_coef->u.integer[1]);
                //printf("        operator_mode %d\n", operator_mode);
                _zone_print0("relevant");
                if (_th_big_is_negative(diff->u.rational.numerator)) {
                    diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(diff->u.rational.numerator)),diff->u.rational.denominator);
                    //printf("            invert 1\n");
                    invert = 1;
                }
                if (_th_big_is_negative(o_coef->u.rational.numerator)) {
                    o_coef = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(o_coef->u.rational.numerator)),o_coef->u.rational.denominator);
                    //printf("            invert 2\n");
                    invert = 1-invert;
                }
                if (mode==USE_EQUAL && operator_mode!=USE_EQUAL) goto cont1;
                if (!invert && mode>0 && operator_mode<0) goto cont1;
                if (invert && mode<0 && operator_mode<0) goto cont1;
                if (!invert && mode<0 && operator_mode>0) goto cont1;
                if (invert && mode>0 && operator_mode>0) goto cont1;
                d1 = term_distance(env,current,target);
                //fprintf(stderr, "%s\n", _th_print_exp(operand));
                //fprintf(stderr, "%s\n", _th_print_exp(diff));
                //fprintf(stderr, "%s\n", _th_print_exp(o_coef));
                //fflush(stderr);
                z = _th_divide_rationals(diff,o_coef);
                if (invert) z = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(z->u.rational.numerator)),z->u.rational.denominator);
                new_current = r_replace_a_term(env,operand,replace,z,NULL,current);
                d1 -= r_term_distance(env,new_current,target);
                //printf("            adding\n");
                sl = (struct step_list *)_th_alloc(REWRITE_SPACE,sizeof(struct step_list));
                sl->next = ret;
                sl->rule = r;
                sl->new_current = new_current;
                sl->distance_decrease = d1;
                if (invert) operator_mode = 0-operator_mode;
                sl->operator_type = operator_mode;
                ret = sl;
            }
cont1:
            r = _th_get_next_rule_by_operand(c_core,&iterator);
        }
        _tree_undent();
cont:;
    }
    return ret;
}

static struct _ex_intern *offset;
static struct _ex_intern *r_strip_offset(struct env *env, struct _ex_intern *e)
{
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_PLUS) {
        struct _ex_intern **args;
        int i, j;
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
        offset = NULL;
        for (i = 0, j = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type==EXP_RATIONAL) {
                offset = e->u.appl.args[i];
            } else {
                args[j++] = e->u.appl.args[i];
            }
        }
        if (offset) {
            if (j==1) {
                return args[0];
            } else {
                return _ex_intern_appl_env(env,INTERN_NAT_PLUS,j,args);
            }
        } else {
            offset = _ex_intern_small_rational(0,1);
            return e;
        }
    } else if (e->type==EXP_RATIONAL) {
        offset = e;
        return _ex_intern_small_rational(0,1);
    } else {
        offset = _ex_intern_small_rational(0,1);
        return e;
    }
}

static int r_search_ineq_path(struct env *env,
                            struct _ex_intern *current,
                            struct _ex_intern *target,
                            int depth,
                            int increase_count,
                            int mode)
{
    struct _ex_intern *cb, *tb, *co, *to;
    _zone_print_exp("Search path from", current);
    _zone_print_exp("to", target);
    _zone_print1("mode %d", mode);
    //printf("Search path from %s\n", p_exp(current));
    //printf("to %s\n", p_exp(target));
    //printf("mode %d\n", mode);
    cb = r_strip_offset(env,current);
    co = offset;
    tb = r_strip_offset(env,target);
    to = offset;
    if (cb==tb) {
        if (co==to && (mode==USE_EQUAL || mode==USE_LESS_EQUAL || mode==USE_GREATER_EQUAL)) return 1;
        if (_th_rational_less(co,to) && (mode==USE_LESS_EQUAL || mode==USE_LESS)) return 1;
        if (_th_rational_less(to,co) && (mode==USE_GREATER_EQUAL || mode==USE_GREATER)) return 1;
    }
    _tree_indent();

    if (depth > 0) {
        struct step_list *steps = r_get_possible_steps(env,current,target,mode);
        while (steps != NULL) {
            int new_mode = mode;
            int new_increase_count = increase_count;
            _zone_print_exp("Checking step",steps->new_current);
            //printf("Checking step %s\n", p_exp(steps->new_current));
            _tree_indent();
            //printf("with rule %s\n", p_exp(steps->rule));
            //printf("distance decrease %d\n", steps->distance_decrease);
            //printf("operator_type %d\n", steps->operator_type);
            _zone_print_exp("with rule", steps->rule);
            _zone_print1("distance_decrease %d", steps->distance_decrease);
            _zone_print1("operator_type %d",steps->operator_type);
            if ((mode==USE_GREATER || mode==USE_LESS) &&
                steps->rule->u.appl.functor==INTERN_NAT_LESS) {
                if (mode==USE_GREATER) {
                    new_mode = USE_GREATER_EQUAL;
                } else {
                    new_mode = USE_LESS_EQUAL;
                }
            }
            if (increase_count > 0 && steps->distance_decrease < 0) {
                --new_increase_count;
            }
            _tree_undent();
            if (r_search_ineq_path(env,steps->new_current,target,depth-1,new_increase_count,new_mode)) {
                _tree_undent();
                //printf("GOOD\n");
                _zone_print0("GOOD");
                //printf("Found path\n");
                //exit(1);
                return 1;
            }
            //printf("BAD\n");
            _zone_print0("BAD");
            steps = steps->next;
        }
        _tree_undent();
        return 0;
    } else {
        _tree_undent();
        return 0;
    }
}

struct _ex_intern *_th_r_search_equality(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *l = e->u.appl.args[0];
    struct _ex_intern *r = e->u.appl.args[1];
    int lsize, rsize;

    if (l->type==EXP_APPL && l->u.appl.functor==INTERN_RAT_PLUS) {
        lsize = l->u.appl.count;
    } else {
        lsize = 1;
    }
    if (r->type==EXP_APPL && r->u.appl.functor==INTERN_RAT_PLUS) {
        rsize = r->u.appl.count;
    } else {
        rsize = 1;
    }

    if (lsize==1 && rsize==1) return NULL;

    //printf("Searching equality %s\n", _th_print_exp(e));

    if (lsize < rsize && l->type != EXP_RATIONAL) {
        if (r_search_ineq_path(env,l,r,3,1,USE_EQUAL)) return _ex_true;
        if (r_search_ineq_path(env,l,r,3,1,USE_GREATER)) return _ex_false;
        if (r_search_ineq_path(env,l,r,3,1,USE_LESS)) return _ex_false;
    } else {
        if (r_search_ineq_path(env,r,l,3,1,USE_EQUAL)) return _ex_true;
        if (r_search_ineq_path(env,r,l,3,1,USE_GREATER)) return _ex_false;
        if (r_search_ineq_path(env,r,l,3,1,USE_LESS)) return _ex_false;
    }
    return NULL;
}

struct _ex_intern *_th_r_search_less(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *l = e->u.appl.args[0];
    struct _ex_intern *r = e->u.appl.args[1];
    int lsize, rsize;

    //printf("Searching less %s\n", _th_print_exp(e));

    if (l->type==EXP_APPL && l->u.appl.functor==INTERN_RAT_PLUS) {
        lsize = l->u.appl.count;
    } else {
        lsize = 1;
    }
    if (r->type==EXP_APPL && r->u.appl.functor==INTERN_RAT_PLUS) {
        rsize = r->u.appl.count;
    } else {
        rsize = 1;
    }
    if (lsize < rsize && l->type != EXP_RATIONAL) {
        if (r_search_ineq_path(env,l,r,3,1,USE_GREATER_EQUAL)) {
            //printf("Reduced %s to false 1\n", _th_print_exp(e));
            return _ex_false;
        }
        if (r_search_ineq_path(env,l,r,3,1,USE_LESS)) {
            //printf("Reduced %s to true 1\n", _th_print_exp(e));
            return _ex_true;
        }
    } else {
        if (r_search_ineq_path(env,r,l,3,1,USE_GREATER)) {
            //printf("Reduced %s to true 2\n", _th_print_exp(e));
            return _ex_true;
        }
        if (r_search_ineq_path(env,r,l,3,1,USE_LESS_EQUAL)) {
            //printf("Reduced %s to false 2\n", _th_print_exp(e));
            return _ex_false;
        }
    }
    return NULL;
}

struct add_list *_th_binary_descendents(struct env *env, struct _ex_intern *e1, struct _ex_intern *e2, struct _ex_intern **done_list)
{
	struct add_list *al = NULL, *a;
	struct _ex_intern *e;
    int and_combine;

	//e1 = _th_extract_relation(env, e1);
	//e2 = _th_extract_relation(env, e2);

    _zone_print_exp("e1", e1);
    _zone_print_exp("e2", e2);

	al = NULL;

	if (_th_is_binary_term(env,e1) && _th_is_binary_term(env,e2)) {
        struct _ex_intern *l1 = _th_get_left_operand(env,e1);
        struct _ex_intern *r1 = _th_get_right_operand(env,e1);
        struct _ex_intern *l2 = _th_get_left_operand(env,e1);
        struct _ex_intern *r2 = _th_get_right_operand(env,e1);

        if (l1->type==EXP_APPL && l1->u.appl.functor==INTERN_NAT_PLUS) return NULL;
        if (l2->type==EXP_APPL && l2->u.appl.functor==INTERN_NAT_PLUS) return NULL;
        if (r1->type==EXP_APPL && r1->u.appl.functor==INTERN_NAT_PLUS) return NULL;
        if (r2->type==EXP_APPL && r2->u.appl.functor==INTERN_NAT_PLUS) return NULL;

        //_zone_print_exp("Combining", e1);
		//_zone_print_exp("and", e2);

		e = _th_combine_operands(env,e1,e2,&and_combine);
		//_zone_print_exp("can combine", e);
		if (e && (done_list==NULL || e->user1==NULL)) {
			//int x = _th_get_indent();
			unsigned *fv;
			int count;
            if (done_list) {
                //extern void check_x43(struct _ex_intern *);
                //check_x43(e,1);
                e->user1 = *done_list;
                *done_list = e;
            }
			a = (struct add_list *)_th_alloc(CACHE_SPACE,sizeof(struct add_list));
			a->next = al;
			al = a;
            fv = _th_get_free_vars(e,&count);
			if (count==0) {
				e = _th_unmark_vars(env,e);
				//_th_clear_cache();
				a->e = _th_nc_rewrite(env,e);
				a->e = _th_mark_vars(env,a->e);
			} else {
				_th_clear_cache();
			    a->e = _th_int_rewrite(env,e,1);
			}
			//if (x != _th_get_indent()) exit(1);
		}
		
		//al = make_const_comparison(env,l1,l2,al);
		//al = make_const_comparison(env,l1,r2,al);
		//al = make_const_comparison(env,l2,l2,al);
		//al = make_const_comparison(env,l2,r2,al);
	}

	//_zone_print0("Done");

	return al;
}

static struct add_list *break_down_op(struct env *env, struct _ex_intern *e, struct add_list *add_list)
{
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        return break_down_op(env, e->u.appl.args[0], add_list);
    }
    if (!_th_is_binary_term(env,e)) return add_list;
    add_list = break_term(env, e->u.appl.args[0], add_list);
    add_list = break_term(env, e->u.appl.args[1], add_list);
    return add_list;
}

static struct add_list *break_down_ops_make_list(struct env *env, struct _ex_intern *e)
{
    int i ;
    struct add_list *add_list = NULL;

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_AND) {
        for (i = 0; i < e->u.appl.count; ++i) {
            add_list = break_down_op(env,e->u.appl.args[i], add_list);
        }
        return 0 ;
    }
    return break_down_op(env,e, add_list) ;
}

struct _ex_intern *_th_normalize_rule(struct env *env, struct _ex_intern *e, int is_main)
{
    if (e->type==EXP_APPL && e->u.appl.count==2 && e->u.appl.functor==INTERN_MEMBER)
    {
        return _ex_intern_appl2_env(env,INTERN_SUBSET,_ex_intern_appl1_env(env,INTERN_SET,e->u.appl.args[0]),e->u.appl.args[1]);
    }
    else if (e->type==EXP_APPL && e->u.appl.count==1 && e->u.appl.functor==INTERN_NOT &&
             e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.count==2 &&
             e->u.appl.args[0]->u.appl.functor==INTERN_MEMBER)
    {
        return _ex_intern_appl2_env(env,INTERN_SEPARATE,_ex_intern_appl1_env(env,INTERN_SET,e->u.appl.args[0]->u.appl.args[0]),
                                    e->u.appl.args[0]->u.appl.args[1]) ;
    }
    else if (e->type==EXP_APPL && e->u.appl.count==1 && e->u.appl.functor==INTERN_NOT &&
             e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.count==2 &&
             e->u.appl.args[0]->u.appl.functor==INTERN_SUBSET &&
             e->u.appl.args[0]->u.appl.args[0]->type==EXP_APPL &&
             e->u.appl.args[0]->u.appl.args[0]->u.appl.count==1 &&
             e->u.appl.args[0]->u.appl.args[0]->u.appl.functor==INTERN_SET)
    {
        return _ex_intern_appl2_env(env,INTERN_SEPARATE,e->u.appl.args[0]->u.appl.args[0],e->u.appl.args[0]->u.appl.args[1]) ;
    }
    else if (e->type==EXP_APPL && e->u.appl.count==3 &&
             (e->u.appl.functor==INTERN_ORIENTED_RULE || e->u.appl.functor==INTERN_UNORIENTED_RULE ||
             e->u.appl.functor==INTERN_FORCE_ORIENTED) && (is_main || e->u.appl.args[2]==_ex_true)) {
        return _ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0],e->u.appl.args[1]) ;
    }
    else if (e->type==EXP_APPL && e->u.appl.count==1 &&
        e->u.appl.functor==INTERN_NOT &&
        e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.count==3 &&
        (e->u.appl.args[0]->u.appl.functor==INTERN_ORIENTED_RULE || e->u.appl.args[0]->u.appl.functor==INTERN_UNORIENTED_RULE ||
         e->u.appl.args[0]->u.appl.functor==INTERN_FORCE_ORIENTED) && (is_main || e->u.appl.args[0]->u.appl.args[2]==_ex_true)) {
        return _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0]->u.appl.args[0],e->u.appl.args[0]->u.appl.args[1])) ;
    }
    return e;
}

struct _ex_intern *_th_extract_relation(struct env *env, struct _ex_intern *e)
{
	//_zone_print_exp("Extracting", e);

	if (e->type==EXP_APPL && e->u.appl.functor==INTERN_ORIENTED_RULE &&
		e->u.appl.args[1]==_ex_true && e->u.appl.args[2]==_ex_true) {
		e = e->u.appl.args[0];
	} else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_ORIENTED_RULE &&
		e->u.appl.args[1]==_ex_false && e->u.appl.args[2]==_ex_true) {
		e = e->u.appl.args[0];
		if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
			e = e->u.appl.args[0];
		} else {
			e = _ex_intern_appl1_env(env,INTERN_NOT,e);
		}
	} else if (e->type==EXP_APPL &&
		       (e->u.appl.functor==INTERN_UNORIENTED_RULE ||
			    e->u.appl.functor==INTERN_ORIENTED_RULE) &&
				e->u.appl.count==3 && e->u.appl.args[2]==_ex_true) {
		e = _ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0],e->u.appl.args[1]);
	}
	//_zone_print_exp("result", e);
	return e;
}

struct add_list *_th_unary_descendents(struct env *env, struct _ex_intern *e)
{
	struct add_list *al;

	e = _th_extract_relation(env,e);

	e = _th_normalize_rule(env, e, 0);

	if (!_th_is_binary_term(env,e)) return NULL;
	al = break_down_ops_make_list(env, e);
	al = create_set_term(env,e,al);
	return _th_get_transpositions(env, e, al);
}

struct add_list *_th_implied_descendents(struct env *env, struct _ex_intern *e)
{
    struct add_list *a;
    struct _ex_intern *r;
    struct _ex_intern *l1;
    struct _ex_intern *r1;
    struct rule *cr;
    
    a = _th_unary_descendents(env, e);
    
    e = _th_extract_relation(env,e);
    
    if (!_th_is_binary_term(env,e)) return a;
    
    l1 = _th_get_left_operand(env,e);
    r1 = _th_get_right_operand(env,e);
    
    r = _th_get_first_context_rule(env, &cr);
    
    while (r) {
        r = _th_extract_relation(env, r);
        
        if (_th_is_binary_term(env,r)) {
            struct _ex_intern *l2 = _th_get_left_operand(env,r);
            struct _ex_intern *r2 = _th_get_right_operand(env,r);
            
            //a = make_const_comparison(env,l1,l2,a);
            //a = make_const_comparison(env,l1,r2,a);
            //a = make_const_comparison(env,l2,l2,a);
            //a = make_const_comparison(env,l2,r2,a);
        }
        
        r = _th_get_next_rule(env, &cr);
    }
    
    
    return a;
}

static int break_down_ops(struct env *env, struct _ex_intern *e)
{
	struct add_list *a = break_down_ops_make_list(env, e);

	while (a) {
		if (process_env_term(env,e,NULL,NULL,1)) return 1;
		a = a->next;
	}

	return 0;
}

static int _th_process_rule(struct env *env,struct _ex_intern *e)
{
    struct _ex_intern *args[1] ;
    struct add_list *terms ;
#ifdef DEBUG
    _zone_print1("process rule %s", _th_print_exp(e)) ;
#endif
    /*printf("Process %s\n", _th_print_exp(e)) ;*/
    if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_ORIENTED_RULE || e->u.appl.functor==INTERN_UNORIENTED_RULE)) {
        if (e->u.appl.args[1]==_ex_false) {
            args[0] = e->u.appl.args[0] ;
            e = _ex_intern_appl_env(env,INTERN_NOT,1,args) ;
        } else {
            e = e->u.appl.args[0] ;
        }
    }
#ifdef DEBUG
    _zone_print1("revised %s", _th_print_exp(e)) ;
#endif
    if (break_down_ops(env,e)) return 1 ;
    terms = create_set_term(env,e,NULL) ;
    while (terms != NULL) {
        _th_process_rule(env,terms->e);
        terms = terms->next;
    }
    /*printf("Processing term %s\n", _th_print_exp(e)) ;*/
    return process_env_term(env,e,NULL,NULL,1) ;
}

static int cmp(const void *i1,const void *i2)
{
    return *((const int *)i2)-*((const int *)i1) ;
}

static int _th_flush_rules(struct env *env)
{
    int i, count ;
    unsigned hash ;
    struct  trans_stack *s ;
    struct _term_list *tl ;
    struct _union_list *ul ;

    //_zone_print1("flush tos start = %x\n", tos);

    //printf("Flushing at %d %d %d %d\n", _tree_zone, _tree_subzone, _tree_count, term_count) ;
#ifdef DEBUG
    _zone_print0("Flushing rules") ;
#endif
    _tree_indent() ;

    qsort(terms,term_count,sizeof(struct _ex_intern *),cmp) ;
    hash = 0 ;
    for (i = 0; i < term_count; ++i) {
#ifdef DEBUG
        _zone_print1("term %s", _th_print_exp(terms[i])) ;
#endif
        hash += (unsigned)terms[i] ;
    }
    hash /= 4 ;
    hash = hash%TRANS_HASH_SIZE ;
    s = push_hash[hash] ;
    while (s != NULL) {
        if (term_count != s->term_count) goto cont ;
#ifdef DEBUG
        _zone_print1("s = %x", s) ;
#endif
        for (i = 0; i < term_count; ++i) {
            if (terms[i] != s->terms[i]) goto cont ;
        }
        break ;
cont:
        s = s->push_next ;
    }

    if (s==NULL) {
        //if (term_count != 0) {
            //fprintf(stderr, "Flushing at %d %d\n", term_count, _tree_count) ;
        //}
        for (i = 0; i < term_count; ++i) {
#ifdef DEBUG
            _zone_print1("Adding %s", _th_print_exp(terms[i])) ;
#endif
            _th_process_rule(env,terms[i]) ;
        }
        _tree_undent() ;
        _zone_print1("flush tos end1 = %x\n", tos);
        return hash ;
    } else {
#ifdef DEBUG
        _zone_print3("Retrieving hash %d %d %d", s->zone, s->subzone, s->count) ;
#endif
        //for (i = 0; i < TRANS_HASH_SIZE; ++i) {
        //    env_terms[i] = s->env_terms[i] ;
        //    env_consts[i] = s->env_consts[i] ;
        //    env_left[i] = s->env_left[i] ;
        //    env_right[i] = s->env_right[i] ;
        //    union_terms[i] = s->union_terms[i] ;
        //}
        memcpy(env_terms, s->env_terms, sizeof(struct _ex_list *) * TRANS_HASH_SIZE);
        memcpy(env_consts, s->env_consts, sizeof(struct _const_list *) * TRANS_HASH_SIZE);
        memcpy(env_left, s->env_left, sizeof(struct _term_list *) * TRANS_HASH_SIZE);
        memcpy(env_right, s->env_right, sizeof(struct _term_list *) * TRANS_HASH_SIZE);
        memcpy(union_terms, s->union_terms, sizeof(struct _union_list *) * TRANS_HASH_SIZE);

        count = 0 ;
        for (i = 0; i < TRANS_HASH_SIZE; ++i) {
            ul = union_terms[i] ;
            while (ul != NULL) {
                ul->unions = s->union_ptrs[count++] ;
                ul = ul->next ;
            }
        }
        count = 0 ;
        for (i = 0; i < TRANS_HASH_SIZE; ++i) {
            tl = env_left[i] ;
            while (tl != NULL) {
                tl->exps = s->term_ptrs[count++] ;
                tl = tl->next ;
            }
            tl = env_right[i] ;
            while (tl != NULL) {
                tl->exps = s->term_ptrs[count++] ;
                tl = tl->next ;
            }
        }
        tos = s ;
        push_hash = tos->push_hash ;
        term_count = 0 ;
        _tree_undent() ;
        return -1 ;
    }
}

void _th_trans_push(struct env *env)
{
    struct trans_stack *s ;
    int i ;
    int hash ;
    int count, ucount ;
    struct _term_list *tl ;
    struct _union_list *ul ;

#ifdef DEBUG
    _zone_print0("trans push") ;
    check_table() ;
    _tree_indent() ;
#endif

    hash = _th_flush_rules(env) ;
    flushed = 0 ;
    if (hash < 0) {
#ifdef DEBUG
        _zone_print0("pre terminate") ;
        _zone_print0("env terms") ;
        print_term_table(env_terms) ;
        _zone_print0("left table") ;
        print_left_table(env_left) ;
        _zone_print0("right table") ;
        print_right_table(env_right) ;
        check_table() ;
        _tree_undent() ;
#endif
        return ;
    }
    s = tos ;
    tos = (struct trans_stack *)_th_alloc(TRANSITIVE_SPACE,sizeof(struct trans_stack)) ;
#ifdef DEBUG
    _zone_print0("Assigning tos") ;
    tos->zone = _tree_zone ;
    tos->subzone = _tree_subzone ;
    tos->count = _tree_count ;
#endif
    tos->next = s ;
    tos->push_next = push_hash[hash] ;
    tos->term_count = term_count ;
    tos->terms = (struct _ex_intern **)_th_alloc(TRANSITIVE_SPACE,sizeof(struct _ex_intern *) * max_term_count) ;
    for (i = 0; i < term_count; ++i) {
#ifdef DEBUG
        _zone_print1("%s", _th_print_exp(terms[i])) ;
#endif
        tos->terms[i] = terms[i] ;
    }
    term_count = 0 ;
    push_hash[hash] = tos ;
    push_hash = tos->push_hash = (struct trans_stack **)_th_alloc(TRANSITIVE_SPACE, sizeof(struct trans_stack *) * TRANS_HASH_SIZE) ;
    count = 0 ;
    ucount = 0 ;
    for (i = 0; i < TRANS_HASH_SIZE; ++i) {
        tos->env_terms[i] = env_terms[i] ;
        tos->env_consts[i] = env_consts[i] ;
        tos->env_left[i] = env_left[i] ;
        tos->env_right[i] = env_right[i] ;
        tos->union_terms[i] = union_terms[i] ;
        tl = env_left[i] ;
        while (tl != NULL) {
            ++count ;
            tl = tl->next ;
        }
        tl = env_right[i] ;
        while (tl != NULL) {
            ++count ;
            tl = tl->next ;
        }

        ul = union_terms[i] ;
        while (ul != NULL) {
            ++ucount ;
            ul = ul->next ;
        }
        push_hash[i] = NULL ;
    }
    tos->term_ptrs = (struct _ex_list **)_th_alloc(TRANSITIVE_SPACE,sizeof(struct _ex_list *) * count) ;
    tos->union_ptrs = (struct _unions **)_th_alloc(TRANSITIVE_SPACE,sizeof(struct _unions *) * ucount) ;
    count = 0 ;
    ucount = 0 ;
    for (i = 0; i < TRANS_HASH_SIZE; ++i) {
        tl = env_left[i] ;
        while (tl != NULL) {
            tos->term_ptrs[count++] = tl->exps ;
            tl = tl->next ;
        }
        tl = env_right[i] ;
        while (tl != NULL) {
            tos->term_ptrs[count++] = tl->exps ;
            tl = tl->next ;
        }
        ul = union_terms[i] ;
        while (ul != NULL) {
            tos->union_ptrs[ucount++] = ul->unions ;
            ul = ul->next ;
        }
    }
#ifdef DEBUG
    _zone_print0("exit trans push") ;
    _zone_print0("env terms") ;
    print_term_table(env_terms) ;
    _zone_print0("left table") ;
    print_left_table(env_left) ;
    _zone_print0("right table") ;
    print_right_table(env_right) ;
    check_table() ;
    _tree_undent() ;
#endif
}

void _th_trans_pop()
{
    int i, count, ucount ;
    struct _ex_list *l ;
    struct _term_list *tl ;
    struct _union_list *ul ;

#ifdef DEBUG
    _zone_print0("trans_pop") ;
    check_table() ;
#endif
    if (tos==NULL) {
        _zone_print0("Too many transitive pops\n");
        fprintf(stderr, "Too many transitive pops\n") ;
        fflush(stderr) ;
        //exit(1) ;
        return;
    }
    flushed = 1 ;
    for (i = 0; i < TRANS_HASH_SIZE; ++i) {
        l = env_terms[i] ;
        while (l != NULL && l != tos->env_terms[i]) {
            if (l->child1 != NULL) l->child1->unused = 0 ;
            if (l->child2 != NULL) l->child2->unused = 0 ;
            l = l->next ;
        }
        //env_terms[i] = tos->env_terms[i] ;
        //env_consts[i] = tos->env_consts[i] ;
        //env_left[i] = tos->env_left[i] ;
        //env_right[i] = tos->env_right[i] ;
        //union_terms[i] = tos->union_terms[i] ;
    }
    memcpy(env_terms,tos->env_terms, sizeof(struct _ex_list *) * TRANS_HASH_SIZE);
    memcpy(env_consts, tos->env_consts, sizeof(struct _const_list *) * TRANS_HASH_SIZE);
    memcpy(env_left, tos->env_left, sizeof(struct _term_list *) * TRANS_HASH_SIZE);
    memcpy(env_right, tos->env_right, sizeof(struct _term_list *) * TRANS_HASH_SIZE);
    memcpy(union_terms, tos->union_terms, sizeof(struct _union_list *) * TRANS_HASH_SIZE);

    term_count = tos->term_count ;
    for (i = 0; i < term_count; ++i) {
        terms[i] = tos->terms[i] ;
    }
    count = 0 ;
    ucount = 0 ;
    for (i = 0; i < TRANS_HASH_SIZE; ++i) {
        tl = env_left[i] ;
        while (tl != NULL) {
            tl->exps = tos->term_ptrs[count++] ;
            tl = tl->next ;
        }
        tl = env_right[i] ;
        while (tl != NULL) {
            tl->exps = tos->term_ptrs[count++] ;
            tl = tl->next ;
        }
        ul = union_terms[i] ;
        while (ul != NULL) {
            tos->union_ptrs[ucount++] = ul->unions ;
            ul = ul->next ;
        }
    }
    tos = tos->next ;
    if (tos==NULL) {
        push_hash = root_push_hash ;
    } else {
        push_hash = tos->push_hash ;
    }
#ifdef DEBUG
    _zone_print0("Exit trans pop") ;
    check_table() ;
#endif
}

int _th_add_rule(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *l;
    _zone_print_exp("Adding rule", e) ;
    /*printf("Adding trans %s\n", _th_print_exp(e)) ;*/
    if (e->type != EXP_APPL || e->u.appl.count != 3 ||
        e->u.appl.args[2] != _ex_true ||
        (e->u.appl.args[1] != _ex_true && e->u.appl.args[1] != _ex_false)) {
        _tree_indent();
        _zone_print0("rejected");
        _tree_undent();
        return 0 ;
    }
    l = e->u.appl.args[0] ;
    if (e->u.appl.args[1]==_ex_false) l = _ex_intern_appl1_env(env,INTERN_NOT,l) ;
    l = _th_normalize_rule(env,l,0) ;
    if (!_th_is_binary_term(env,l)) {
        _tree_indent() ;
        _zone_print0("rejected") ;
        _tree_undent() ;
        return 0 ;
    }
    e = _ex_intern_appl3_env(env,e->u.appl.functor,l,_ex_true,e->u.appl.args[2]);
    if (term_count==max_term_count) {
		//printf("Incrementing terms %d %d\n", term_count, max_term_count) ;
		//fflush(stdout) ;
        max_term_count += TERM_SIZE_INCREMENT ;
        if (max_term_count == TERM_SIZE_INCREMENT) {
            terms = (struct _ex_intern **)MALLOC(sizeof(struct _ex_intern *) * max_term_count) ;
        } else {
            terms = (struct _ex_intern **)REALLOC(terms,sizeof(struct _ex_intern *) * max_term_count) ;
        }
		//printf("Done incrementing\n") ;
		//fflush(stdout) ;
    }
    //printf("add rule %d %d %d %d %s\n", _tree_zone, _tree_subzone, _tree_count, term_count, _th_print_exp(e)) ;
    terms[term_count++] = e ;
    return 0 ;
}

struct _ex_intern *_th_strengthen(struct env *env, struct _ex_intern *base, struct _ex_intern *e)
{
	unsigned op1, op2, optype1, optype2;

	op1 = get_operator(env,base,&optype1) ;
	op2 = get_operator(env,e,&optype2) ;
#ifdef DEBUG
	_zone_print2("ops %d %d", optype1, optype2) ;
#endif
	switch(optype1) {
  	    case INTERN_EQ:
		    switch(optype2) {
		        case INTERN_EQ:
		        case INTERN_EPO:
		        case INTERN_ETO:
			        return _ex_true ;
		        case INTERN_NE:
		        case INTERN_TO:
		        case INTERN_PO:
			        return _ex_false ;
			}
		case INTERN_NE:
			switch(optype2) {
		    	case INTERN_NE:
				    return _ex_true ;
			    case INTERN_TO:
			    case INTERN_PO:
			    case INTERN_EPO:
			    case INTERN_ETO:
				    return e ;
			    case INTERN_EQ:
				    return _ex_false ;
			}
		case INTERN_PO:
		case INTERN_TO:
			switch(optype2) {
				case INTERN_NE:
				case INTERN_TO:
				case INTERN_PO:
				case INTERN_EPO:
				case INTERN_ETO:
					return _ex_true ;
				case INTERN_EQ:
					return _ex_false ;
				}
        case INTERN_EPO:
        case INTERN_ETO:
            switch(optype2) {
			    case INTERN_NE:
				case INTERN_TO:
				case INTERN_PO:
				case INTERN_EQ:
					return e ;
				case INTERN_EPO:
				case INTERN_ETO:
					return _ex_true ;
            }
	}
	return e;
}

struct _ex_intern *_th_reverse_strengthen(struct env *env, struct _ex_intern *base, struct _ex_intern *e)
{
	unsigned op1, op2, optype1, optype2;
    struct _ex_intern *l = _th_get_left_operand(env,e) ;
    struct _ex_intern *r = _th_get_right_operand(env,e) ;

	op1 = get_operator(env,base,&optype1) ;
	op2 = get_operator(env,e,&optype2) ;
	switch(optype1) {
	    case INTERN_EQ:
		    switch(optype2) {
		        case INTERN_EQ:
		        case INTERN_EPO:
		        case INTERN_ETO:
			        return _ex_true;
		        case INTERN_NE:
		        case INTERN_TO:
		        case INTERN_PO:
			        return _ex_false;
			}
		case INTERN_NE:
			switch(optype2) {
		    	case INTERN_NE:
				    return _ex_true ;
			    case INTERN_TO:
			    case INTERN_PO:
			    case INTERN_EPO:
			    case INTERN_ETO:
				    return e;
			    case INTERN_EQ:
				    return _ex_false ;
			}
		case INTERN_PO:
		case INTERN_TO:
			switch(optype2) {
				case INTERN_NE:
					return _ex_true ;
				case INTERN_EPO:
				case INTERN_ETO:
				case INTERN_EQ:
				case INTERN_TO:
				case INTERN_PO:
					return _ex_false ;
			}
        case INTERN_EPO:
        case INTERN_ETO:
            switch(optype2) {
				case INTERN_NE:
					return e;
				case INTERN_TO:
				case INTERN_PO:
					return _ex_false;	
				case INTERN_EQ:
					return e;	
				case INTERN_EPO:
				case INTERN_ETO:
					return mk_eq(env,op1,r,l);
            }
	}
	return e;
}

struct _ex_intern *_th_strengthen_term(struct env *env, struct _ex_intern *base, struct _ex_intern *e)
{
    struct _ex_intern *l, *r, *lb, *rb;

	if (!_th_is_binary_term(env,base)) return NULL;
	if (!_th_is_binary_term(env,e)) return NULL;

	lb = _th_get_left_operand(env,base);
    rb = _th_get_right_operand(env,base);
	l = _th_get_left_operand(env,e);
    r = _th_get_right_operand(env,e);

	if (lb==l && r==rb) {
		return _th_strengthen(env,base,e);
	}
	if (lb==r && l==rb) {
		return _th_reverse_strengthen(env,base,e);
	}

	return NULL;
}

struct _ex_intern *_th_or(struct env *env, struct _ex_intern *base, struct _ex_intern *e)
{
	unsigned op1, op2, optype1, optype2;
    struct _ex_intern *l = _th_get_left_operand(env,e) ;
    struct _ex_intern *r = _th_get_right_operand(env,e) ;

	op1 = get_operator(env,base,&optype1) ;
	op2 = get_operator(env,e,&optype2) ;
#ifdef DEBUG
	_zone_print2("ops %d %d", optype1, optype2) ;
#endif
	switch(optype1) {
  	    case INTERN_EQ:
		    switch(optype2) {
		        case INTERN_EQ:
		        case INTERN_EPO:
		        case INTERN_ETO:
			        return e;
		        case INTERN_NE:
                    return _ex_true;
		        case INTERN_TO:
		        case INTERN_PO:
                    //printf("Here4\n");
                    return mk_le(env,op2,l,r);
			}
		case INTERN_NE:
			switch(optype2) {
		    	case INTERN_NE:
			    case INTERN_TO:
			    case INTERN_PO:
                    return base;
			    case INTERN_EPO:
			    case INTERN_ETO:
			    case INTERN_EQ:
				    return _ex_true;
			}
		case INTERN_PO:
		case INTERN_TO:
			switch(optype2) {
				case INTERN_NE:
				case INTERN_TO:
				case INTERN_PO:
				case INTERN_EPO:
				case INTERN_ETO:
                    return e;
				case INTERN_EQ:
                    //printf("Here3\n");
					return mk_le(env,op1,l,r);
				}
        case INTERN_EPO:
        case INTERN_ETO:
            switch(optype2) {
			    case INTERN_NE:
                    return _ex_true;
				case INTERN_TO:
				case INTERN_PO:
				case INTERN_EQ:
				case INTERN_EPO:
				case INTERN_ETO:
					return base;
            }
	}
	return NULL;
}

struct _ex_intern *_th_reverse_or(struct env *env, struct _ex_intern *base, struct _ex_intern *e)
{
	unsigned op1, op2, optype1, optype2;
    struct _ex_intern *l = _th_get_left_operand(env,e) ;
    struct _ex_intern *r = _th_get_right_operand(env,e) ;

	op1 = get_operator(env,base,&optype1) ;
	op2 = get_operator(env,e,&optype2) ;
	switch(optype1) {
	    case INTERN_EQ:
		    switch(optype2) {
		        case INTERN_EQ:
		        case INTERN_EPO:
		        case INTERN_ETO:
			        return e;
		        case INTERN_NE:
                    return _ex_true;
		        case INTERN_TO:
		        case INTERN_PO:
                    //printf("Here1\n");
			        return mk_le(env,op2,l,r);
			}
		case INTERN_NE:
			switch(optype2) {
		    	case INTERN_NE:
			    case INTERN_TO:
			    case INTERN_PO:
				    return base;
			    case INTERN_EPO:
			    case INTERN_ETO:
			    case INTERN_EQ:
				    return _ex_true;
			}
		case INTERN_PO:
		case INTERN_TO:
			switch(optype2) {
				case INTERN_NE:
					return e;
				case INTERN_EPO:
                    return NULL;
				case INTERN_ETO:
                    if (optype1==INTERN_PO) return NULL;
                    return _ex_true;
				case INTERN_EQ:
                    //printf("Here2\n");
                    mk_le(env,op1,r,l);
				case INTERN_TO:
				case INTERN_PO:
					return mk_ne(env,op1,l,r);
			}
        case INTERN_EPO:
        case INTERN_ETO:
            switch(optype2) {
				case INTERN_PO:
				case INTERN_EPO:
                    return NULL;
				case INTERN_TO:
				case INTERN_ETO:
                    if (optype1==INTERN_EPO) return NULL;
				case INTERN_NE:
					return _ex_true;
				case INTERN_EQ:
					return base;	
            }
	}
	return NULL;
}

struct _ex_intern *_th_and(struct env *env, struct _ex_intern *base, struct _ex_intern *e)
{
	unsigned op1, op2, optype1, optype2;
    struct _ex_intern *l = _th_get_left_operand(env,e) ;
    struct _ex_intern *r = _th_get_right_operand(env,e) ;

	op1 = get_operator(env,base,&optype1) ;
	op2 = get_operator(env,e,&optype2) ;
#ifdef DEBUG
	_zone_print2("ops %d %d", optype1, optype2) ;
#endif
	switch(optype1) {
  	    case INTERN_EQ:
		    switch(optype2) {
		        case INTERN_EQ:
		        case INTERN_EPO:
		        case INTERN_ETO:
			        return base;
		        case INTERN_NE:
		        case INTERN_TO:
		        case INTERN_PO:
                    return _ex_false;
			}
		case INTERN_NE:
			switch(optype2) {
		    	case INTERN_NE:
			    case INTERN_TO:
			    case INTERN_PO:
                    return e;
			    case INTERN_EPO:
			    case INTERN_ETO:
                    return mk_lt(env,op2,l,r);
			    case INTERN_EQ:
				    return _ex_false;
			}
		case INTERN_PO:
		case INTERN_TO:
			switch(optype2) {
				case INTERN_NE:
				case INTERN_TO:
				case INTERN_PO:
				case INTERN_EPO:
				case INTERN_ETO:
                    return base;
				case INTERN_EQ:
                    //printf("Here3\n");
					return _ex_false;
				}
        case INTERN_EPO:
        case INTERN_ETO:
            switch(optype2) {
			    case INTERN_NE:
                    return mk_lt(env,op1,l,r);
				case INTERN_TO:
				case INTERN_PO:
				case INTERN_EQ:
                    return e;
				case INTERN_EPO:
				case INTERN_ETO:
					return base;
            }
	}
	return NULL;
}

struct _ex_intern *_th_reverse_and(struct env *env, struct _ex_intern *base, struct _ex_intern *e)
{
	unsigned op1, op2, optype1, optype2;
    struct _ex_intern *l = _th_get_left_operand(env,e) ;
    struct _ex_intern *r = _th_get_right_operand(env,e) ;

	op1 = get_operator(env,base,&optype1) ;
	op2 = get_operator(env,e,&optype2) ;
	switch(optype1) {
  	    case INTERN_EQ:
		    switch(optype2) {
		        case INTERN_EQ:
		        case INTERN_EPO:
		        case INTERN_ETO:
			        return base;
		        case INTERN_NE:
		        case INTERN_TO:
		        case INTERN_PO:
                    return _ex_false;
			}
		case INTERN_NE:
			switch(optype2) {
		    	case INTERN_NE:
			    case INTERN_TO:
			    case INTERN_PO:
                    return e;
			    case INTERN_EPO:
			    case INTERN_ETO:
                    return mk_lt(env,op2,l,r);
			    case INTERN_EQ:
				    return _ex_false;
			}
		case INTERN_PO:
		case INTERN_TO:
			switch(optype2) {
				case INTERN_NE:
                    return base;
				case INTERN_TO:
				case INTERN_PO:
				case INTERN_EPO:
				case INTERN_ETO:
				case INTERN_EQ:
                    //printf("Here3\n");
					return _ex_false;
				}
        case INTERN_EPO:
        case INTERN_ETO:
            switch(optype2) {
			    case INTERN_NE:
                    return mk_lt(env,op1,r,l);
				case INTERN_TO:
				case INTERN_PO:
                    return _ex_false;
				case INTERN_EQ:
                    return e;
				case INTERN_EPO:
				case INTERN_ETO:
					return mk_eq(env,op1,r,l);
            }
	}
	return NULL;
}

struct _ex_intern *_th_or_terms(struct env *env, struct _ex_intern *base, struct _ex_intern *e)
{
    struct _ex_intern *l, *r, *lb, *rb;

	if (!_th_is_binary_term(env,base)) return NULL;
	if (!_th_is_binary_term(env,e)) return NULL;
    if (!_th_compatible_terms(env, e, base)) return NULL ;

	lb = _th_get_left_operand(env,base);
    rb = _th_get_right_operand(env,base);
	l = _th_get_left_operand(env,e);
    r = _th_get_right_operand(env,e);

	if (lb==l && r==rb) {
		return _th_or(env,base,e);
	}
	if (lb==r && l==rb) {
		return _th_reverse_or(env,base,e);
	}

	return NULL;
}

struct _ex_intern *_th_and_terms(struct env *env, struct _ex_intern *base, struct _ex_intern *e)
{
    struct _ex_intern *l, *r, *lb, *rb;

	if (!_th_is_binary_term(env,base)) return NULL;
	if (!_th_is_binary_term(env,e)) return NULL;
    if (!_th_compatible_terms(env, e, base)) return NULL ;

	lb = _th_get_left_operand(env,base);
    rb = _th_get_right_operand(env,base);
	l = _th_get_left_operand(env,e);
    r = _th_get_right_operand(env,e);

	if (lb==l && r==rb) {
		return _th_and(env,base,e);
	}
	if (lb==r && l==rb) {
		return _th_reverse_and(env,base,e);
	}

	return NULL;
}

static struct _ex_intern *strengthen_term(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *l = _th_get_left_operand(env,e) ;
    struct _ex_intern *r = _th_get_right_operand(env,e) ;
    struct _term_list *tl ;
    struct _ex_list *el ;
    unsigned op1, op2, optype1, optype2 ;

    /*printf("Strengthening %s\n", _th_print_exp(e)) ;*/
#ifdef DEBUG
    _zone_print1("Strengthening %s\n", _th_print_exp(e)) ;
    _zone_print1("l = %s", _th_print_exp(l));
    _zone_print1("r = %s", _th_print_exp(r));
#endif
    _tree_indent() ;
    tl = find_term(env_left,env,l) ;
    for (el = tl->exps; el != NULL; el = el->left_next) {
        /*printf("    testing %s\n",_th_print_exp(el->e)) ;*/
#ifdef DEBUG
        _zone_print1("testing1 %s", _th_print_exp(el->e)) ;
        _zone_print1("right %s", _th_print_exp(r)) ;
        _zone_print1("get_right %s", _th_print_exp(_th_get_right_operand(env,el->e))) ;
        _zone_print1("compatible_terms %d", _th_compatible_terms(env,e,el->e));
#endif
        if (_th_get_right_operand(env,el->e)==r &&
            _th_compatible_terms(env,e,el->e) && !el->unused) {
            op1 = get_operator(env,el->e,&optype1) ;
            op2 = get_operator(env,e,&optype2) ;
#ifdef DEBUG
            _zone_print2("ops %d %d", optype1, optype2) ;
#endif
			return _th_strengthen(env,el->e,e);
        }
    }
    tl = find_term(env_right,env,l) ;
    for (el = tl->exps; el != NULL; el = el->right_next) {
#ifdef DEBUG
        _zone_print1("testing2 %s", _th_print_exp(el->e)) ;
#endif
        if (_th_get_left_operand(env,el->e)==r &&
            _th_compatible_terms(env,e,el->e) && !el->unused) {
            op1 = get_operator(env,el->e,&optype1) ;
            op2 = get_operator(env,e,&optype2) ;
#ifdef DEBUG
            _zone_print2("ops %d %d", optype1, optype2) ;
#endif
			return _th_reverse_strengthen(env,el->e,e);
        }
    }
    _tree_undent() ;
    return e ;
}

static int process_main_term(struct env *env, struct _ex_intern *e,
                             struct _ex_list *c1, struct _ex_list *c2)
{
    struct _ex_list *list ;

#ifdef DEBUG
    _zone_print1("process_main %s", _th_print_exp(e)) ;
    _tree_indent() ;
#endif

    if ((list = add_all_term(env,e)) && !list->unused) {
        int i, ac, j, k ;
        struct _ex_intern *l = _th_get_left_operand(env,e) ;
        struct _ex_intern *r = _th_get_right_operand(env,e) ;
        struct _ex_intern *res ;
        struct _ex_list *el ;
        struct _term_list *tl ;
        unsigned optype ;
        unsigned op = get_operator(env,e,&optype) ;

        list->child1 = c1 ;
        list->child2 = c2 ;
        /*printf("Processing main term %s\n", _th_print_exp(e)) ;*/
        if (is_constant(env,l) || is_constant(env,r)) {
            for (i = 0; i < TRANS_HASH_SIZE; ++i) {
                struct _const_list *el = env_consts[i] ;
#ifdef DEBUG
                check_table() ;
#endif
                while (el != NULL) {
                    if (add_const_comparison(env,l,el->e)) {
#ifdef DEBUG
                        _tree_undent() ;
#endif
                        return 1 ;
                    }
                    if (add_const_comparison(env,r,el->e)) {
#ifdef DEBUG
                        _tree_undent() ;
#endif
                        return 1 ;
                    }
                    el = el->next ;
                }
                el = all_consts[i] ;
                while (el != NULL) {
                    if (add_const_comparison(env,l,el->e)) {
#ifdef DEBUG
                        _tree_undent() ;
#endif
                        return 1 ;
                    }
                    if (add_const_comparison(env,r,el->e)) {
#ifdef DEBUG
                        _tree_undent() ;
#endif
                        return 1 ;
                    }
                    el = el->next ;
                }
            }
        }
        if (op==INTERN_SUBSET && optype==INTERN_EPO &&
            r->type==EXP_APPL && r->u.appl.functor==INTERN_UNION) {

            for (i = 0; i < r->u.appl.count; ++i) {
                tl = find_term(env_left,env,r->u.appl.args[i]) ;
                el = tl->exps ;
                while (el != NULL) {
                    op = get_operator(env,el->e,&optype) ;
                    if (op==INTERN_SEPARATE && optype==INTERN_NE) {
                        if (_th_get_right_operand(env,el->e)==l) {
                            struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * r->u.appl.count) ;
                            for (j = 0, k = 0; j < r->u.appl.count; ++j) {
                                if (i != j) {
                                    args[k++] = r->u.appl.args[j] ;
                                }
                            }
                            res = _ex_intern_appl2_env(env,INTERN_SUBSET,l,_ex_intern_appl_env(env,INTERN_UNION,k,args)) ;
                            if (process_main_term(env,res,list,el)) {
#ifdef DEBUG
                                _tree_undent() ;
#endif
                                return 1 ;
                            }
                        }
                    }
                    el = el->left_next ;
                }
                tl = find_term(env_right,env,r->u.appl.args[i]) ;
                el = tl->exps ;
                while (el != NULL) {
                    op = get_operator(env,el->e,&optype) ;
                    if (op==INTERN_SEPARATE && optype==INTERN_NE) {
                        if (_th_get_left_operand(env,el->e)==l) {
                            struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * r->u.appl.count) ;
                            for (j = 0, k = 0; j < r->u.appl.count; ++j) {
                                if (i != j) {
                                    args[k++] = r->u.appl.args[j] ;
                                }
                            }
                            res = _ex_intern_appl2_env(env,INTERN_SUBSET,l,_ex_intern_appl_env(env,INTERN_UNION,k,args)) ;
                            if (process_main_term(env,res,list,el)) {
#ifdef DEBUG
                                _tree_undent() ;
#endif
                                return 1 ;
                            }
                        }
                    }
                    el = el->right_next ;
                }
            }
        }

        if (op==INTERN_SEPARATE && optype==INTERN_NE) {
            struct _union_list *ul = find_union_term(union_terms,env,l);
            struct _unions *u = ul->unions ;
            while (u != NULL) {
                struct _ex_intern *t = u->term->e ;
                struct _ex_intern **args = ALLOCA(sizeof(struct _ex_intern *) * t->u.appl.args[1]->u.appl.count) ;
                for (i = 0, j = 0; i < t->u.appl.args[1]->u.appl.count; ++i) {
                    if (t->u.appl.args[0]->u.appl.args[i] != l) {
                        args[j++] = t->u.appl.args[1]->u.appl.args[i] ;
                    }
                    res = _ex_intern_appl2_env(env,INTERN_SUBSET,t->u.appl.args[0],_ex_intern_appl_env(env,INTERN_UNION,j,args)) ;
                    if (process_main_term(env,res,list,el)) {
#ifdef DEBUG
                        _tree_undent() ;
#endif
                        return 1 ;
                    }
                }
                u = u->next ;
            }
            ul = find_union_term(union_terms,env,r);
            u = ul->unions ;
            while (u != NULL) {
                struct _ex_intern *t = u->term->e ;
                struct _ex_intern **args = ALLOCA(sizeof(struct _ex_intern *) * t->u.appl.args[1]->u.appl.count) ;
                for (i = 0, j = 0; i < t->u.appl.args[1]->u.appl.count; ++i) {
                    if (t->u.appl.args[0]->u.appl.args[i] != r) {
                        args[j++] = t->u.appl.args[1]->u.appl.args[i] ;
                    }
                    res = _ex_intern_appl2_env(env,INTERN_SUBSET,t->u.appl.args[0],_ex_intern_appl_env(env,INTERN_UNION,j,args)) ;
                    if (process_main_term(env,res,list,el)) {
#ifdef DEBUG
                        _tree_undent() ;
#endif
                        return 1 ;
                    }
                }
                u = u->next ;
            }
        }

        tl = find_term(all_left,env,l) ;
        el = tl->exps ;
        while (el != NULL) {
            res = _th_combine_operands(env,e,el->e,&ac) ;
#ifdef DEBUG
            _zone_print_exp("Combine result", res);
#endif
            if (res != NULL && res != e && res != el->e) {
                if (res==_ex_false) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
                if (ac) {
#ifdef DEBUG
                    _zone_print1("unused e = %s\n", _th_print_exp(e)) ;
                    _zone_print1("unused el->e = %s\n", _th_print_exp(el->e)) ;
#endif
                    el->unused = 1 ;
                    list->unused = 1 ;
                }
#ifdef DEBUG
                _zone_print0("Here1");
#endif
                if (process_main_term(env,res,list,el)) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
            }
            el = el->left_next ;
        }
        tl = find_term(all_right,env,l) ;
        el = tl->exps ;
        while (el != NULL) {
            res = _th_combine_operands(env,e,el->e,&ac) ;
#ifdef DEBUG
            _zone_print_exp("Combine result", res);
#endif
            if (res==_ex_false) {
#ifdef DEBUG
                _tree_undent() ;
#endif
                return 1 ;
            }
            if (res != NULL && res != e && res != el->e) {
                if (res==_ex_false) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
                if (ac) {
#ifdef DEBUG
                    _zone_print1("unused e = %s\n", _th_print_exp(e)) ;
                    _zone_print1("unused el->e = %s\n", _th_print_exp(el->e)) ;
#endif
                    el->unused = 1 ;
                    list->unused = 1 ;
                }
#ifdef DEBUG
                _zone_print0("Here2");
#endif
                if (process_main_term(env,res,list,el)) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
            }
            el = el->right_next ;
        }
        tl = find_term(env_left,env,l) ;
        el = tl->exps ;
        while (el != NULL) {
            res = _th_combine_operands(env,e,el->e,&ac) ;
#ifdef DEBUG
            _zone_print_exp("Combine result", res);
#endif
            if (res==_ex_false) {
#ifdef DEBUG
                _tree_undent() ;
#endif
                return 1 ;
            }
            if (res != NULL && res != e && res != el->e) {
                if (res==_ex_false) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
                if (ac) {
#ifdef DEBUG
                    _zone_print1("unused e = %s\n", _th_print_exp(e)) ;
                    _zone_print1("unused el->e = %s\n", _th_print_exp(el->e)) ;
#endif
                    el->unused = 1 ;
                    list->unused = 1 ;
                }
#ifdef DEBUG
                _zone_print0("Here3");
#endif
                if (process_main_term(env,res,list,el)) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
            }
            el = el->left_next ;
        }
        tl = find_term(env_right,env,l) ;
        el = tl->exps ;
        while (el != NULL) {
            res = _th_combine_operands(env,e,el->e,&ac) ;
#ifdef DEBUG
            _zone_print_exp("Combine result", res);
#endif
            if (res==_ex_false) {
#ifdef DEBUG
                _tree_undent() ;
#endif
                return 1 ;
            }
            if (res != NULL && res != e && res != el->e) {
                if (res==_ex_false) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
                if (ac) {
#ifdef DEBUG
                    _zone_print1("unused e = %s\n", _th_print_exp(e)) ;
                    _zone_print1("unused el->e = %s\n", _th_print_exp(el->e)) ;
#endif
                    el->unused = 1 ;
                    list->unused = 1 ;
                }
#ifdef DEBUG
                _zone_print1("el->e = %s", _th_print_exp(el->e)) ;
                _zone_print1("e = %s", _th_print_exp(e)) ;
                _zone_print0("Here4");
#endif
                if (process_main_term(env,res,list,el)) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
            }
            el = el->right_next ;
        }
        tl = find_term(all_left,env,r) ;
        el = tl->exps ;
        while (el != NULL) {
            res = _th_combine_operands(env,e,el->e,&ac) ;
#ifdef DEBUG
            _zone_print_exp("Combine result", res);
#endif
            if (res != NULL && res != e && res != el->e) {
                if (res==_ex_false) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
                if (ac) {
#ifdef DEBUG
                    _zone_print1("unused e = %s\n", _th_print_exp(e)) ;
                    _zone_print1("unused el->e = %s\n", _th_print_exp(el->e)) ;
#endif
                    el->unused = 1 ;
                    list->unused = 1 ;
                }
#ifdef DEBUG
                _zone_print0("Here5");
#endif
                if (process_main_term(env,res,list,el)) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
            }
            el = el->left_next ;
        }
        tl = find_term(all_right,env,r) ;
        el = tl->exps ;
        while (el != NULL) {
            res = _th_combine_operands(env,e,el->e,&ac) ;
#ifdef DEBUG
            _zone_print_exp("Combine result", res);
#endif
            if (res==_ex_false) {
#ifdef DEBUG
                _tree_undent() ;
#endif
                return 1 ;
            }
            if (res != NULL && res != e && res != el->e) {
                if (res==_ex_false) return 1 ;
                if (ac) {
#ifdef DEBUG
                    _zone_print1("unused e = %s\n", _th_print_exp(e)) ;
                    _zone_print1("unused el->e = %s\n", _th_print_exp(el->e)) ;
#endif
                    el->unused = 1 ;
                    list->unused = 1 ;
                }
#ifdef DEBUG
                _zone_print0("Here6");
#endif
                if (process_main_term(env,res,list,el)) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
            }
            el = el->right_next ;
        }
        tl = find_term(env_left,env,r) ;
        el = tl->exps ;
        while (el != NULL) {
            res = _th_combine_operands(env,e,el->e,&ac) ;
#ifdef DEBUG
            _zone_print_exp("Combine result", res);
#endif
            if (res==_ex_false) return 1 ;
            if (res != NULL && res != e && res != el->e) {
                if (res==_ex_false) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
                if (ac) {
#ifdef DEBUG
                    _zone_print1("unused e = %s\n", _th_print_exp(e)) ;
                    _zone_print1("unused el->e = %s\n", _th_print_exp(el->e)) ;
#endif
                    el->unused = 1 ;
                    list->unused = 1 ;
                }
#ifdef DEBUG
                _zone_print0("Here7");
#endif
                if (process_main_term(env,res,list,el)) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
            }
            el = el->left_next ;
        }
        tl = find_term(env_right,env,r) ;
        el = tl->exps ;
        while (el != NULL) {
            res = _th_combine_operands(env,e,el->e,&ac) ;
#ifdef DEBUG
            _zone_print_exp("Combine result", res);
#endif
            if (res==_ex_false) return 1 ;
            if (res != NULL && res != e && res != el->e) {
                if (res==_ex_false) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
                if (ac) {
#ifdef DEBUG
                    _zone_print1("unused e = %s\n", _th_print_exp(e)) ;
                    _zone_print1("unused el->e = %s\n", _th_print_exp(el->e)) ;
#endif
                    el->unused = 1 ;
                    list->unused = 1 ;
                }
#ifdef DEBUG
                _zone_print0("Here8");
#endif
                if (process_main_term(env,res,list,el)) {
#ifdef DEBUG
                    _tree_undent() ;
#endif
                    return 1 ;
                }
            }
            el = el->right_next ;
        }
    }
#ifdef DEBUG
    _tree_undent() ;
#endif
    return 0 ;
}

void _th_transitive_init()
{
    int i ;

    if (terms != NULL) FREE(terms);
    terms = (struct _ex_intern **)MALLOC(sizeof(struct _ex_intern *) * TERM_SIZE_INCREMENT) ;
    term_count = 0 ;
    max_term_count = TERM_SIZE_INCREMENT ;

    if (root_push_hash != NULL) FREE(root_push_hash);
    root_push_hash = push_hash = (struct trans_stack **)MALLOC(sizeof(struct trans_stack *) * TRANS_HASH_SIZE) ;
    for (i = 0; i < TRANS_HASH_SIZE; ++i) {
        env_terms[i] = NULL ;
        env_consts[i] = NULL ;
        env_left[i] = env_right[i] = NULL ;
        push_hash[i] = 0 ;
    }
}

void _th_transitive_reset()
{
    int i ;

    if (terms == NULL) {
        terms = (struct _ex_intern **)malloc(sizeof(struct _ex_intern *) * TERM_SIZE_INCREMENT) ;
        max_term_count = TERM_SIZE_INCREMENT ;
    }
    term_count = 0 ;

    if (root_push_hash == NULL) {
        root_push_hash = push_hash = (struct trans_stack **)malloc(sizeof(struct trans_stack *) * TRANS_HASH_SIZE) ;
    }
    for (i = 0; i < TRANS_HASH_SIZE; ++i) {
        env_terms[i] = NULL ;
        env_consts[i] = NULL ;
        env_left[i] = env_right[i] = NULL ;
        push_hash[i] = 0 ;
        root_push_hash[i] = NULL ;
    }
    _th_alloc_release(TRANSITIVE_SPACE,NULL) ;
    _zone_print0("transitive reset");
    tos = NULL ;
}

static in_tran = 0 ;

static struct _ex_intern **args ;
static unsigned arg_size ;

#define ARG_INCREMENT 4000

static void check_size(unsigned size)
{
    if (size > arg_size) {
        arg_size = size + ARG_INCREMENT ;
        args = (struct _ex_intern **)REALLOC(args,sizeof(struct _ex_intern *) * arg_size) ;
    }
}

struct _ex_intern *_th_transitive(struct env *env, struct _ex_intern *orig)
{
    int i ;
    char *mark ;
    struct _ex_intern *e, *e1;
    struct add_list *al ;
    unsigned op, optype ;

    _zone_print_exp("Transitive rewrite of", orig) ;
    e1 = e = _th_normalize_rule(env,orig,1);
    _zone_print_exp("normalization", e) ;

    if ((e->type != EXP_APPL || e->u.appl.functor != INTERN_AND) && _th_is_binary_term(env,e))
    {
        al = create_set_term(env, e, NULL) ;
        op = get_operator(env,e,&optype) ;
        if (op==INTERN_EQUAL) {
            struct _ex_intern *res;
            while (al != NULL) {
                res = _th_transitive(env,al->e) ;
                if (res != al->e) return res ;
                al = al->next ;
            }
        } else if (op==INTERN_SUBSET) {
            while (al != NULL) {
                process_env_term(env,al->e,NULL,NULL,1) ;
                al = al->next ;
            }
        }
    }

    if (in_tran) return NULL ;
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_AND) {
        int ret = 0 ;
        for (i = 0; i < e->u.appl.count; ++i) {
            if (_th_is_binary_term(env,e->u.appl.args[i])) ret = 1 ;
        }
        if (!ret) return NULL ;
    } else {
        if (!_th_is_binary_term(env,e)) return NULL;
    }

#ifdef DEBUG
    check_table() ;
#endif

    _zone_print0("Process") ;
    _tree_indent() ;

    in_tran = 1 ;

    _th_trans_push (env) ;
#ifndef FAST
    if (_zone_active()) {
        _zone_print0("env terms") ;
        print_term_table(env_terms) ;
        _zone_print0("left table") ;
        print_left_table(env_left) ;
        _zone_print0("right table") ;
        print_right_table(env_right) ;
    }
#endif
#ifdef DEBUG
    _zone_print0("left table") ;
    print_left_table(env_left) ;
    _zone_print0("right table") ;
    print_right_table(env_right) ;
#endif
    mark = _th_alloc_mark(TRANSITIVE_SPACE) ;

    for (i = 0; i < TRANS_HASH_SIZE; ++i) {
        all_consts[i] = NULL ;
        all_terms[i] = NULL ;
        all_left[i] = all_right[i] = NULL ;
    }

    break_down_ops(env,e) ;
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_AND) {
        for (i = 0; i < e->u.appl.count; ++i) {
            if (e != NULL && _th_is_binary_term(env,e->u.appl.args[i]) && process_main_term(env,e->u.appl.args[i],NULL,NULL)) {
                _th_alloc_release(TRANSITIVE_SPACE,mark) ;
                _th_trans_pop() ;
                _zone_print0("Result: (False)\n") ;
                _tree_undent() ;
                in_tran = 0 ;
                return _ex_false ;
            }
        }
        check_size(e->u.appl.count) ;
        for (i = 0; i < e->u.appl.count; ++i) {
            if (_th_is_binary_term(env,e->u.appl.args[i])) {
                args[i] = strengthen_term(env,e->u.appl.args[i]) ;
            } else {
                args[i] = e->u.appl.args[i];
            }
        }
        _th_alloc_release(TRANSITIVE_SPACE,mark) ;
        _th_trans_pop () ;
        in_tran = 0 ;
        e = _ex_intern_appl_env(env,INTERN_AND,i,args) ;
        _zone_print_exp("Result", e) ;
        _tree_undent() ;
        if (e==e1) {
            return orig;
        } else {
            return e ;
        }
    } else {
#ifdef DEBUG
        _zone_print_exp("Here 1", e);
#endif
        if (e != NULL && _th_is_binary_term(env,e) && process_main_term(env,e,NULL,NULL)) {
            _th_alloc_release(TRANSITIVE_SPACE,mark) ;
            _th_trans_pop() ;
            in_tran = 0 ;
            _zone_print0("Result: (False)\n") ;
            _tree_undent() ;
            return _ex_false ;
        }
#ifdef DEBUG
        _zone_print0("env table 2\n") ;
        print_term_table(env_terms) ;
        _zone_print0("left table 2") ;
        print_left_table(env_left) ;
        _zone_print0("right table 2") ;
        print_right_table(env_right) ;
#endif
        e = strengthen_term(env,e) ;
        _th_alloc_release(TRANSITIVE_SPACE,mark) ;
        _th_trans_pop () ;
        in_tran = 0 ;
        _zone_print_exp("Result", e) ;
        _tree_undent() ;
        if (e==e1) {
            return orig;
        } else {
            return e ;
        }
    }
}

