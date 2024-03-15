/*
 * cache.c
 *
 * Routines for maintaining the rewrite cache.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdio.h>
#include <stdlib.h>
#include "Globals.h"
#include "Intern.h"

static struct _ex_intern *context ;
struct _ex_intern *_th_context ;
struct _ex_intern *_th_full_context ;
unsigned _th_cycle ;
#define MAX_LEVELS 30
unsigned _th_context_level ;
unsigned _th_context_used[MAX_LEVELS] ;
unsigned _th_context_tested[MAX_LEVELS] ;
unsigned _th_context_any_tested ;
unsigned _th_context_any_used ;
unsigned _th_violation_tested ;
unsigned _th_violation_used ;
static struct _ex_intern *quant_context ;
static int add_count = 0 ;
static struct _ex_intern *adds[MAX_ARGS] ;
static int quant_add_count = 0 ;
static struct _ex_intern *quant_adds[MAX_ARGS] ;
struct _ex_intern *_th_rewrite_next ;
static struct _ex_intern **cl ;
static int cl_count ;
static struct _ex_intern *context_stack[MAX_ARGS] ;
static struct _ex_intern *quant_context_stack[MAX_ARGS] ;
static int tos ;

int get_level() { return tos ; }

struct _ex_intern *_th_get_context()
{
    return context ;
}

static int *block_cycle_array ;
static int *block_level_array ;
static int block_array_size = 0 ;
static int block_array_top = 0 ;
static struct _ex_intern *empty_quant;

void _th_reintern_cache(struct env *env)
{
    if (context != NULL) context = _ex_reintern(env, context);
    if (_th_context != NULL) _th_context = _ex_reintern(env, _th_context);
    if (_th_full_context != NULL) _th_full_context = _ex_reintern(env, _th_full_context);
}

void _th_add_block(int level, int cycle)
{
    if (block_array_size==0) {
        block_array_size = 4000 ;
        block_cycle_array = (int *)MALLOC(sizeof(int) * 4000) ;
        block_level_array = (int *)MALLOC(sizeof(int) * 4000) ;
    } else if (block_array_size <= block_array_top) {
        block_array_size += 4000 ;
        block_cycle_array = (int *)REALLOC(block_cycle_array, sizeof(int) * block_array_size) ;
        block_level_array = (int *)REALLOC(block_level_array, sizeof(int) * block_array_size) ;
    }
    block_cycle_array[block_array_top] = cycle ;
    block_level_array[block_array_top++] = level ;
}

void _th_cancel_block(int level)
{
    while (block_array_top > 0 && block_level_array[block_array_top-1] >= level) --block_array_top ;
}

int _th_check_block(int cycle)
{
    return block_array_top==0 || block_cycle_array[block_array_top] >= cycle ;
}

void _th_cache_init()
{
    context = _ex_intern_appl(INTERN_CS,0,0) ;
    empty_quant = quant_context = _ex_intern_appl(INTERN_QC,0,0) ;
    quant_add_count = add_count = 1 ;
    _th_rewrite_next = NULL ;
    cl = (struct _ex_intern **)MALLOC(sizeof(struct _ex_intern *)) ;
    cl_count = 1 ;
    tos = 0 ;
    _th_context_level = 0 ;
}

void _th_reset_context()
{
    context = _ex_intern_appl(INTERN_CS,0,0) ;
}

void _th_cache_shutdown()
{
}

void _th_pop_context()
{
    _th_context = context = context_stack[--tos] ;
    quant_context = quant_context_stack[tos] ;
    //printf("Popping contexts %s", _th_print_exp(context)) ;
    //printf("and %s\n", _th_print_exp(quant_context)) ;
    //fflush(stdout) ;
    add_count = 1 ;
    quant_add_count = 1 ;
    --_th_context_level ;
}

static int cmp(const void *i1,const void *i2)
{
    return *((const int *)i2)-*((const int *)i1) ;
}

void _th_add_cache(struct _ex_intern *exp, struct _ex_intern *cache)
{
    exp->rewrite = cache ;
    exp->next_cache = _th_rewrite_next ;
    _th_rewrite_next = exp ;
}

void _th_flush_context()
{
    struct _ex_intern *r ;
    int i, j ;

    if (add_count > 1) {
        switch (add_count) {
            case 1:
            case 2:
                break;
            case 3:
                if (adds[1] < adds[2]) {
                    r = adds[1];
                    adds[1] = adds[2];
                    adds[2] = r;
                }
                break;
            default:
                qsort(adds+1,add_count-1,sizeof(struct _ex_intern *),cmp) ;
        }
        adds[0] = context ;
        r = _ex_intern_appl(INTERN_ACS,add_count,adds) ;
        if (r->rewrite) {
            context = r->rewrite ;
        } else {
            if (cl_count < context->u.appl.count+add_count-1) {
                cl_count = context->u.appl.count+add_count-1 ;
                cl = (struct _ex_intern **)REALLOC(cl,sizeof(struct _ex_intern *) * cl_count) ;
            }
            for (i = 0; i < context->u.appl.count; ++i) {
                cl[i] = context->u.appl.args[i] ;
            }
            for (j = 1; j < add_count; ++j) {
                cl[i+j-1] = adds[j] ;
            }
            //qsort(cl,i+add_count-1,sizeof(struct _ex_intern *),cmp) ;
            context = _ex_intern_appl(INTERN_CS,i+add_count-1,cl) ;
            r->next_cache = _th_rewrite_next ;
            _th_rewrite_next = r ;
            r->rewrite = context ;
        }
        _th_context = context ;
    }
    if (quant_add_count > 1) {
        qsort(quant_adds+1,quant_add_count-1,sizeof(struct _ex_intern *),cmp) ;
        quant_adds[0] = quant_context ;
        r = _ex_intern_appl(INTERN_AQC,quant_add_count,quant_adds) ;
        if (r->rewrite) {
            quant_context = r->rewrite ;
        } else {
            if (cl_count < quant_context->u.appl.count+quant_add_count-1) {
                cl_count = quant_context->u.appl.count+quant_add_count-1 ;
                cl = (struct _ex_intern **)REALLOC(cl,sizeof(struct _ex_intern *) * cl_count) ;
            }
            for (i = 0; i < quant_context->u.appl.count; ++i) {
                cl[i] = quant_context->u.appl.args[i] ;
            }
            for (j = 1; j < quant_add_count; ++j) {
                cl[i+j-1] = quant_adds[j] ;
            }
            qsort(cl,i+quant_add_count-1,sizeof(struct _ex_intern *),cmp) ;
            quant_context = _ex_intern_appl(INTERN_QC,i+quant_add_count-1,cl) ;
            r->next_cache = _th_rewrite_next ;
            _th_rewrite_next = r ;
            r->rewrite = quant_context ;
        }
    }
    add_count = 1 ;
    quant_add_count = 1 ;
}

void _th_print_context(struct env *env)
{
    _th_pp_tree_print(env,INTERN_DEFAULT,80,context) ;
}

void _th_push_context()
{
    ++_th_context_level ;
    if (tos==MAX_ARGS) {
        printf("Too many pushes\n") ;
        //_th_context_level = 0 ;
        //_th_context_level = 1 / _th_context_level ;
        exit(1) ;
    }
    _th_flush_context() ;
    //printf("Pushing contexts %s", _th_print_exp(context)) ;
    //printf("and %s\n", _th_print_exp(quant_context)) ;
    //fflush(stdout) ;
    quant_context_stack[tos] = quant_context ;
    _th_context = context_stack[tos++] = context ;
}

void _th_add_context_rule(struct _ex_intern *r)
{
    int i ;
    for (i = 1; i < add_count; ++i) {
        if (adds[i]==r) return ;
    }
    adds[add_count++] = r ;
    if (add_count==MAX_ARGS) {
        _th_flush_context() ;
    }
}

void _th_quant_add_context_rule(unsigned q, int level)
{
    struct _ex_intern *pair[2] ;
    pair[0] = _ex_intern_var(q) ;
    pair[1] = _ex_intern_small_integer(level) ;
    quant_adds[quant_add_count++] = _ex_intern_appl(INTERN_QP,2,pair) ;

    if (quant_add_count==MAX_ARGS) {
        _th_flush_context() ;
    }
}

static int force_stack_count = 0 ;
static struct _ex_intern *force_stack[MAX_IN_USE] ;
static struct _ex_intern *force_stack_instantiation[MAX_IN_USE] ;
static struct _ex_intern *force_stack_set[MAX_IN_USE] ;

int _th_at_nesting_limit()
{
    return force_stack_count >= MAX_IN_USE ;
}

void _th_push_rule(struct _ex_intern *rule, struct _ex_intern *instantiation)
{
    if (rule->rule_in_use > 0) {
        force_stack[force_stack_count] = NULL ;
    } else {
        force_stack[force_stack_count] = rule ;
    }
    if (instantiation->in_rewrite) {
        force_stack_instantiation[force_stack_count] = NULL ;
    } else {
        force_stack_instantiation[force_stack_count] = instantiation ;
    }
    force_stack_set[force_stack_count++] = NULL ;
}

void _th_pop_rule()
{
    --force_stack_count ;
}

static struct _ex_intern *get_nesting_state(struct env *env)
{
    struct _ex_intern *e ;
    if (force_stack_count==0) {
        return NULL ;
    } else if (e = force_stack_set[force_stack_count-1]) {
        return e ;
    } else {
        struct _ex_intern **args1 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * force_stack_count) ;
        struct _ex_intern **args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * force_stack_count) ;
        int i, j, k ;

        for (i = j = k = 0; i < force_stack_count; ++i) {
            if (force_stack[i] != NULL) {
                args1[j++] = _ex_intern_appl2_env(env, INTERN_T, force_stack[i], _ex_intern_small_integer(force_stack[i]->rule_in_use)) ;
            }
            if (force_stack_instantiation[i]) {
                args2[k++] = force_stack_instantiation[i] ;
            }
        }

        e =  _ex_intern_appl2_env(env, INTERN_T,
                 _ex_intern_appl_env(env, INTERN_SET, j, args1),
                 _ex_intern_appl_env(env, INTERN_SET, k, args2)) ;
        force_stack_set[force_stack_count-1] = e ;
        return e ;
    }
}

struct _ex_intern *_th_get_cache_rewrite(struct env *env, struct _ex_intern *e, int do_transitive)
{
    struct _ex_intern *se = e, *c, *n ;

    if (e->cache_bad) return NULL;

    //_zone_print2("cache %s %d", _th_print_exp(quant_context), _th_cond_level());
    if (quant_context==empty_quant && _th_cond_level()==0) {
        struct _ex_intern *f = e->rewrite;
        //_zone_print1("Fast cache %s", _th_print_exp(e));
        //_zone_print1("f %s", _th_print_exp(f));
        if (f) {
            struct _ex_intern *g = f->rewrite;
            struct _ex_intern *xx = NULL;
            if (g != NULL && f != g) {
                while (g && g->rewrite && g->rewrite != g && g != xx) {
                    _zone_print_exp("g", g);
                    if (g->type==EXP_VAR || g->type==EXP_MARKED_VAR) {
                        xx = g;
                    }
                    g = g->rewrite;
                }
                //e->rewrite = g;
                //while (f && f != g) {
                //    struct _ex_intern *n = f->rewrite;
                //    f->rewrite = g;
                //    f = n;
                //}
                return g;
            }
        }
        return f;      
    }

    c = _th_full_context ;

    n = get_nesting_state(env) ;

    adds[0] = e ;
    adds[1] = quant_context ;
    adds[2] = _th_gen_context(env) ;
    adds[3] = _ex_intern_small_integer(do_transitive) ;

    if (n) {
        adds[4] = n ;
        e = _ex_intern_appl(INTERN_RC,5,adds) ;
        if (e->rewrite != NULL) {
            _th_reference_cache((unsigned)e) ;
            return e->rewrite ;
        }
    }

    e = _ex_intern_appl(INTERN_RC,4,adds) ;

    /*printf("e->rewrite = %s\n", _th_print_exp(e->rewrite)) ;*/
    //_zone_print1("Testing %s", _th_print_exp(e)) ;
    if (e->rewrite != NULL) {
        //_zone_print1("Cache entry %x", e) ;
        _th_reference_cache((unsigned)e) ;
        //_zone_print1("context %s", _th_print_exp(c)) ;
        //if (se->type==EXP_APPL && se->u.appl.functor==_th_intern("disjoint")) {
            //_th_pp_zone_print(env,INTERN_DEFAULT,80,e) ;
        //}
        return e->rewrite ;
    }

    return e->rewrite ;
}

void _th_set_cache_rewrite(struct env *env, struct _ex_intern *e, struct _ex_intern *r, int do_transitive, unsigned start_cycle)
{
    struct _ex_intern *se = e, *c, *n ;
    struct _ex_intern **args ;
    int diff = (e != r) ;

    if (quant_context==empty_quant && _th_cond_level()==0) {
#ifdef FAST
        _th_add_cache_assignment(env,e,r);
#else
        _th_add_cache_assignment(env,e,r);
#endif
        //e->rewrite = r;
        //e->next_cache = _th_rewrite_next;
        //_th_rewrite_next = e;
        return;
    }

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern **) * context->u.appl.count) ;

    if (start_cycle <= _th_violation_tested) {
        if (start_cycle <= _th_violation_used) {
            n = get_nesting_state(env) ;
        } else {
            n = NULL ;
        }
        c = _th_full_context ;
        //_zone_print("Full save %s", _th_full_context) ;
    } else {
        c = _th_context ;
        n = NULL ;
        //_zone_print("Simple save") ;
    }

	adds[0] = e ;
	adds[1] = quant_context ;
	adds[2] = _th_gen_context(env) ;
	adds[3] = _ex_intern_small_integer(do_transitive) ;
	if (n != NULL) {
		adds[4] = n ;
		e = _ex_intern_appl(INTERN_RC,5,adds) ;
	} else {
		e = _ex_intern_appl(INTERN_RC,4,adds) ;
	}
    //_zone_print1("Saving %s", _th_print_exp(e)) ;
    if (e->rewrite != NULL && diff) {
        _zone_print0("Cache saving error") ;
        _zone_print_exp("context", context) ;
        _zone_print_exp("_th_context", _th_context) ;
        _zone_print_exp("e", e->rewrite) ;
        _zone_print_exp("e->rewrite", e->rewrite) ;
        printf("e = %s\n", _th_print_exp(e));
        printf("e->rewrite = %s\n", _th_print_exp(e->rewrite));
        printf("quant_context = %s\n", _th_print_exp(quant_context));
        printf("_th_cond_level() = %d\n", _th_cond_level());
        printf("Cache saving error\n") ;
        exit(1) ;
    }
    if (!e->rewrite) {
        e->next_cache = _th_rewrite_next ;
        _th_rewrite_next = e ;
        _th_save_cache((unsigned)e) ;
    //if (_zone_active() && se->type==EXP_APPL && se->u.appl.functor==_th_intern("disjoint")) {
        //char c[100] ;
        //sprintf(c, "%x",e) ;
        //_th_pp_file_print(cache,c,env,INTERN_DEFAULT,80,e) ;
    //}
        e->rewrite = r ;
    }
}

void _th_clear_cache()
{
    while(_th_rewrite_next != NULL) {
        _th_rewrite_next->rewrite = NULL ;
        _th_rewrite_next = _th_rewrite_next->next_cache ;
    }
}

