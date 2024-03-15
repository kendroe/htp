/*
 * rewrite.c
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

static struct _ex_intern **base_args ;
static int arg_start, max_args ;
int _th_quant_level ;

static int transitive_count;
static int long_transitive_count;
static int cache_count;
static int term_count;

int _th_test_mode = 0;

void _th_init_rewrite(char *log)
{
    _th_alloc_init() ;
    _tree_init(log) ;
    _th_intern_init () ;
    _th_init_bignum() ;
    _ex_init() ;
    _th_print_init() ;
    _th_cache_init() ;
    _th_transitive_init() ;
    _th_parse_init() ;
    _th_type_init() ;
    _th_crewrite_init() ;

    max_args = 4000 ;
    arg_start = 0 ;
    base_args = (struct _ex_intern **)MALLOC(sizeof(struct _ex_intern *) * max_args) ;
    _th_quant_level = 0 ;

}

void _th_shutdown_rewrite()
{
    _th_print_shutdown() ;
    _ex_shutdown() ;
    _th_cache_shutdown() ;
    _th_intern_shutdown () ;
    _tree_shutdown() ;
    _th_alloc_shutdown() ;
}

static void check_arg_size(int size)
{
    size += arg_start ;
    if (size > max_args) {
        max_args = size ;
        base_args = (struct _ex_intern **)REALLOC(base_args,
                    sizeof(struct _ex_intern *) * max_args) ;
        if (base_args==NULL) {
            printf("Error in REALLOC\n") ;
            exit(1) ;
        }
    }
    arg_start = size ;
}

void _th_and_push(struct env *env,struct _ex_intern **args, int count, int exclude)
{
    int i ;

    _zone_print1("and push %d", exclude) ;
    _tree_indent() ;

    _th_derive_push(env) ;

    for (i = 0; i < count; ++i) {
        if (i != exclude) {
            _zone_print_exp("",_th_mark_vars(env,args[i])) ;
            //_zone_enter_sub() ;
            if (exclude < 0) {
                _th_derive_add_prepared(env,_th_derive_prepare(env,args[i])) ;
            } else {
                _th_derive_add_prepared(env,_th_derive_prepare(env,args[i])) ;
            }
            //_zone_exit_sub() ;
        }
    }

    _tree_undent() ;
}

void _th_and_push1(struct env *env,struct _ex_intern **args,int count, int exclude)
{
    int i ;

    _zone_print1("and push1 %d", exclude) ;
    _tree_indent() ;

    for (i = 0; i < count; ++i) {
        if (i != exclude) {
            _zone_print_exp("",_th_mark_vars(env,args[i])) ;
            //_zone_enter_sub() ;
            if (exclude < 0) {
                _th_derive_add_prepared(env,_th_derive_prepare(env,args[i])) ;
            } else {
                _th_derive_add_prepared(env,_th_derive_prepare(env,args[i])) ;
            }
            //_zone_exit_sub() ;
        }
    }

    _tree_undent() ;
}

static struct _ex_intern *add_universal(struct _ex_intern *rule)
{
    int count ;
    unsigned *fv ;

    fv = _th_get_free_vars(rule, &count) ;
    if (count==0) return rule ;

    return _ex_intern_quant(INTERN_ALL,count,fv,rule,_ex_true) ;
}

static struct _ex_intern *make_rule(struct env *env, struct _ex_intern *e)
{
    if (e->type==EXP_QUANT && e->u.quant.quant==INTERN_ALL) {
        return make_rule(env,e->u.quant.exp) ;
    }

    if (e->type != EXP_APPL ||
        (e->u.appl.functor != INTERN_ORIENTED_RULE && e->u.appl.functor != INTERN_UNORIENTED_RULE &&
         e->u.appl.functor != INTERN_FORCE_ORIENTED) ||
        e->u.appl.count != 3) {
        return _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,e,_ex_true,_ex_true) ;
    }

    return e ;
}

struct _ex_intern *_th_and_elaborate(struct env *env, struct _ex_intern *e)
{
    int i, j, k ;
    struct _ex_intern *res = _ex_true ;

    _zone_print0("and_elaborate") ;
    _tree_indent() ;
    for (i = 0; i < e->u.appl.count; ++i) {
        _th_and_push(env,e->u.appl.args,e->u.appl.count,i) ;
        _zone_print_exp("",e->u.appl.args[i]) ;
        _th_derive_rewrite_rule(REWRITE_SPACE,env,make_rule(env,e->u.appl.args[i])) ;
        for (j = 0; j < _th_possibility_count; ++j) {
			struct _ex_intern *r = add_universal(_th_possible_rewrites[j]);
			for (k = 0; k < e->u.appl.count; ++k) {
				if (_th_equal(env,r,e->u.appl.args[k])) {
					goto cont ;
				}
			}
            res = _th_flatten_top(env, _ex_intern_appl2_env(env,INTERN_AND,res,r)) ;
cont: ;
        }
        _th_derive_pop(env) ;
    }
    _tree_undent() ;

    return res ;
}

static struct _ex_intern *and_process(struct env *env, struct _ex_intern **parms, int count)
{
    struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count) ;
    int i, j ;

    _zone_print0("processing and") ;
    _tree_indent() ;

    // Sort the arguments
    for (i = 0; i < count; ++i) {
        args[i] = parms[i] ;
    }

    _zone_print0("sorting") ;
    _tree_indent() ;
    for (i = 0; i < count; ++i) {
        for (j = i+1; j < count; ++j) {
            if (_th_smaller(env,args[j],args[i])) {
                struct _ex_intern *e = args[i] ;
                args[i] = args[j] ;
                args[j] = e ;
            }
        }
    }
    _tree_undent() ;

    for (i = 0; i < count; ++i) {
        _zone_print_exp("processing", args[i]) ;
        _tree_indent() ;
        _th_derive_push(env) ;
        for (j = 0; j < i; ++j) {
            if (_th_smaller(env, args[j],args[i])) {
                _zone_print_exp("adding env rule", args[j]) ;
                _th_derive_and_add(env, _th_mark_vars(env,args[j])) ;
            }
        }
        args[i] = _th_int_rewrite(env,args[i],1) ;
        _th_derive_pop(env) ;
        _tree_undent() ;
    }
    _tree_undent() ;

    return _ex_intern_appl_env(env,INTERN_AND,count,args) ;
}

void _th_or_push(struct env *env,struct _ex_intern **args,int count, int exclude)
{
    //struct _ex_intern *rule[3] ;
    struct _ex_intern *e ;
    int i ;

    //rule[2] = _ex_true ;
    //rule[1] = _ex_false ;

    _zone_print1("or push %d", exclude) ;
    _tree_indent() ;

    _th_derive_push(env) ;

    for (i = 0; i < count; ++i) {
        if (i != exclude) {
            e = _th_mark_vars(env,args[i]) ;
            //rule[1] = _ex_false ;
            if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT && e->u.appl.count==1) {
                e = e->u.appl.args[0] ;
            } else {
                e = _ex_intern_appl1_env(env,INTERN_NOT,e) ;
            }
            _th_derive_add_prepared(env,_th_derive_prepare(env,e)) ;
        }
    }

    _tree_undent() ;
}

static struct _ex_intern *or_process(struct env *env, struct _ex_intern **parms, int count)
{
    struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count) ;
    int i, j ;
    struct _ex_intern *rule[3] ;

    rule[1] = _ex_false ;
    rule[2] = _ex_true ;

    _zone_print0("processing or\n") ;
    _tree_indent() ;

    // Sort the arguments
    for (i = 0; i < count; ++i) {
        args[i] = parms[i] ;
    }

    _zone_print0("sorting") ;
    _tree_indent() ;
    for (i = 0; i < count; ++i) {
        for (j = i+1; j < count; ++j) {
            if (_th_smaller(env,args[j],args[i])) {
                struct _ex_intern *e = args[i] ;
                args[i] = args[j] ;
                args[j] = e ;
            }
        }
    }
    _tree_undent() ;

    for (i = 0; i < count; ++i) {
        _zone_print_exp("processing", args[i]) ;
        _tree_indent() ;
        _th_derive_push(env) ;
        for (j = 0; j < i; ++j) {
            if (_th_smaller(env, args[j],args[i])) {
                _zone_print_exp("adding env rule", args[j]) ;
                rule[0] = args[j] ;
                _th_derive_and_add(env, _ex_intern_appl_env(env,INTERN_ORIENTED_RULE,3,rule)) ;
            }
        }
        args[i] = _th_int_rewrite(env,args[i],1) ;
        _th_derive_pop(env) ;
        _tree_undent() ;
    }
    _tree_undent() ;

    return _ex_intern_appl_env(env,INTERN_OR,count,args) ;
}

struct env {
    int symbol_size ;
    struct disc *all_properties ;
    struct disc *apply_properties ;
    struct disc *derive_properties ;
    struct disc *augment_properties ;
    struct disc *macro_properties ;
    struct small_disc *context_properties ;
    struct small_disc *apply_context_properties ;
    struct context_stack *context_stack ;
    struct directive *pp_directives ;
    struct trie_l *pptrie ;
    int rebuild_trie ;
    struct rule *rules, *cr ;
    int context_level ;
    struct symbol_info *first_context_mark ;
    struct state_checks *state_checks ;
    struct add_list *heuristics ;
    struct symbol_info *table[1] ;
} ;

static int rew_equal(struct env *env, struct _ex_intern *e1, struct _ex_intern *e2)
{
	if (e1==NULL && e2==NULL) return 1 ;
	if (e1==NULL || e2==NULL) return 0 ;
	return _th_equal(env,e1,e2) ;
}

static struct _ex_intern *_rewrite_quote(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern **args, *p, *t ;
    int i ;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor == INTERN_QUOTE && e->u.appl.count == 1) {
                p = _th_int_rewrite(env, e->u.appl.args[0], 0) ;
                if (p->type==EXP_APPL && p->u.appl.functor == INTERN_QUOTE &&
                    p->u.appl.count == 1) {
                    return p->u.appl.args[0] ;
                } else {
                    return _ex_intern_appl_env(env,INTERN_QUOTE,1,&p) ;
                }
            }
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = _rewrite_quote(env, e->u.appl.args[i]) ;
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count, args) ;
        case EXP_QUANT:
            p = _rewrite_quote(env, e->u.quant.exp) ;
            t = _rewrite_quote(env, e->u.quant.cond) ;
            return _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,e->u.quant.vars,t,p) ;
        case EXP_CASE:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.case_stmt.count * 2) ;
            p = _rewrite_quote(env, e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count*2; ++i) {
                args[i] = _rewrite_quote(env, e->u.case_stmt.args[i]) ;
            }
            return _ex_intern_case(p,e->u.case_stmt.count,args) ;
        default:
            return e ;
    }
}

static struct _ex_intern *_merge_derives(struct env *env, struct _ex_intern *d1, struct _ex_intern *d2)
{
    struct _ex_intern **args ;
    int i, j ;
    
    d1 = _th_flatten_top(env, _ex_intern_appl2_env(env,INTERN_AND,d1,d2)) ;
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * d1->u.appl.count) ;
    for (i = 0, j = 0; i < d1->u.appl.count; ++i) {
        args[j++] = d1->u.appl.args[i] ;
        if (i < d1->u.appl.count-1 && d1->u.appl.args[i]==d1->u.appl.args[i+1]) ++i ;
    }
    return _ex_intern_appl_env(env, INTERN_AND, j, args) ;
}

static struct change_list has_change ;

void mark_disturbed(struct env *env, struct _ex_intern *e1, struct _ex_intern *e2, int count, struct change_list **changes, struct _ex_intern **args)
{
    int i, j ;
    struct change_list *c ;

    for (i = 0; i < count; ++i) {
        c = changes[i] ;
        if (c == NULL || c->terms==NULL) continue ;
        while (c != NULL) {
            if (c->terms != NULL && !c->execute) {
                char *mark = _th_alloc_mark(MATCH_SPACE) ;
                struct _ex_intern *ct = c->terms ;
                if (ct->type==EXP_APPL && ct->u.appl.count==1 && ct->u.appl.functor==INTERN_QUOTE) ct = ct->u.appl.args[0] ;
                if (ct->type==EXP_APPL && ct->u.appl.functor==INTERN_AND) {
                    for (j = 0; j < ct->u.appl.count; ++j) {
                        if (e1 != NULL && _th_match(env, ct->u.appl.args[j], e1)) {
                            _zone_print_exp("Retrying", c->rule) ;
                            _zone_print2("on %d %s", i, _th_print_exp(args[i])) ;
                            c->execute = 1 ;
                        } else if (e2 != NULL && _th_match(env, ct->u.appl.args[j], e2)) {
                            _zone_print_exp("Retrying", c->rule) ;
                            _zone_print2("on %d %s", i, _th_print_exp(args[i])) ;
                            c->execute = 1 ;
                        }
                    }
                } else {
                    if (e1 != NULL && _th_match(env, ct, e1)) {
                        _zone_print_exp("Retrying", c->rule) ;
                        _zone_print2("on %d %s", i, _th_print_exp(args[i])) ;
                        c->execute = 1 ;
                    } else if (e2 != NULL && _th_match(env, ct, e2)) {
                        _zone_print_exp("Retrying", c->rule) ;
                        _zone_print2("on %d %s", i, _th_print_exp(args[i])) ;
                        c->execute = 1 ;
                    }
                }
            }
            c = c->next ;
        }
    }
}

void subout_and_equals(struct env *env, int count, struct _ex_intern **args, struct change_list **changes)
{
    int i, j ;
    struct _ex_intern *e ;

    for (i = 0; i < count; ++i) {
        struct _ex_intern *f = args[i] ;
        unsigned v ;
        if (f->type==EXP_APPL && f->u.appl.count==2 && f->u.appl.functor==INTERN_EQUAL) {
            if (f->u.appl.args[0]->type==EXP_VAR) {
                v = f->u.appl.args[0]->u.var ;
                f = f->u.appl.args[1] ;
            } else if (f->u.appl.args[1]->type==EXP_VAR) {
                v = f->u.appl.args[1]->u.var ;
                f = f->u.appl.args[0] ;
            } else {
                v = 0 ;
            }
            if (v) {
                char *m = _th_alloc_mark(MATCH_SPACE) ;
                struct _ex_unifier *u = _th_new_unifier(MATCH_SPACE) ;
                _th_add_pair(MATCH_SPACE,u,v,f) ;
                for (j = 0; j < count; ++j) {
                    struct _ex_intern *g = args[j] ;
                    if (i == j) continue ;
                    if (g->type==EXP_APPL && g->u.appl.functor==INTERN_EQUAL && g->u.appl.count==2) {
                        if (g->u.appl.args[0]->type==EXP_VAR || g->u.appl.args[1]->type==EXP_VAR) continue ;
                    }
                    e = _th_subst(env,u,g) ;
                    mark_disturbed(env,e,g,count,changes,args) ;
                    args[j] = e ;
                }
                _th_alloc_release(MATCH_SPACE, m) ;
            }
        }
    }
}

static int simplify_mode = 0 ;
static int block_cycle ;
static int rewrite_level = 0 ;
static int do_immediate_check = 0 ;
static int in_check_rewrite  = 0 ;
static int do_checks = 0 ;
static char *check_mark ;
int _th_check_state ;

static struct check_record {
    struct check_record *next ;
    struct _ex_intern *result ;
    struct _ex_intern *state ;
    int check_mode ;
} *check_list = NULL ;

static void do_check_result(struct env *env, struct _ex_intern *result, int check_mode, struct _ex_intern *state)
{
    struct _ex_intern *exp ;

    if (in_check_rewrite) return ;

    in_check_rewrite = 1 ;

    exp = _ex_intern_appl3_env(env,INTERN_CHECK_VALIDITY,result,_ex_intern_small_integer(check_mode),state) ;
    exp = _th_int_rewrite(env, exp, 1) ;
    
    in_check_rewrite = 0 ;

    if (exp != _ex_false) {
        _zone_print0("Check failure") ;
        _tree_indent() ;
        _zone_print_exp("expression", result) ;
        _zone_print1("mode: %d", check_mode) ;
        _zone_print_exp("state: %s", state) ;
        _tree_undent() ;
    }
}

static struct _ex_intern *last_state ;

static void start_check_results()
{
    check_mark = _th_alloc_mark(CHECK_SPACE) ;
    last_state = _ex_true ;
}

static void finish_check_results(struct env *env)
{
    _zone_print0("Completeness failures") ;
    _tree_indent() ;
    while (check_list) {
        do_check_result(env, check_list->result, check_list->check_mode, check_list->state) ;
        check_list = check_list->next ;
    }
    _tree_undent() ;
    _th_alloc_release(CHECK_SPACE, check_mark) ;
}

void _th_check_result(struct env *env, struct _ex_intern *result, int check_mode)
{
    if (do_checks) {
        if (do_immediate_check) {
            do_check_result(env, result, check_mode + _th_check_state, last_state) ;
        } else {
            struct check_record *l = (struct check_record *)_th_alloc(CHECK_SPACE, sizeof(check_list)) ;
            l->next = check_list ;
            check_list = l ;
            l->result = result ;
            l->state = last_state ;
            l->check_mode = check_mode + _th_check_state;
        }
    }
}

struct _ex_intern *_th_augment(struct env *env, struct _ex_intern *e)
{
    int augmented = 1 ;
    int i, count, j ;
    struct _ex_intern **args, **derives, **args2, **derives2, *res ;
    struct add_list *applications, *adds, *al ;

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_AND) {
        args = e->u.appl.args ;
        count = e->u.appl.count ;
    } else {
        args = &e ;
        count = 1 ;
    }

    _zone_print0("Context rules") ;
    _tree_indent() ;
    derives = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count) ;
    for (i = 0; i < count; ++i) {
        derives[i] = _th_derive_prepare_detailed(env,args[i]) ;
    }
    _tree_undent() ;

    adds = NULL ;
    _zone_print1("Augmentation loop %d", count) ;
    _tree_indent() ;
    while (augmented) {
        augmented = 0 ;
        applications = NULL ;
        _zone_print0("Augmentation cycle") ;
        for (i = 0; i < count; ++i) {
            _zone_print2("derive %d %s", i, _th_print_exp(derives[i]));
        }
        _tree_indent() ;
        for (i = 0; i < count; ++i) {
            _zone_print2("term %d %s", i, _th_print_exp(args[i])) ;
            _tree_indent() ;
            _zone_print_exp("", args[i]) ;
            applications = _th_apply_inference_rule(env, args[i], count, args, adds, NULL, applications, -1000, 1000, i, derives) ;
            _zone_print2("Applications, changes = %d %d", applications, _th_change_list) ;
#ifndef FAST
            if (applications != NULL) _zone_print_exp("e", applications->e) ;
#endif
            _tree_undent() ;
        }
        _tree_undent() ;
        _zone_print0("Processing applications") ;
        _tree_indent() ;
        while (applications != NULL) {
            struct _ex_intern *r = applications->e ;
            _zone_print_exp("Processing", r) ;
            if (r != NULL) {
                struct _ex_intern *derive ;
                if (r->type==EXP_APPL && r->u.appl.functor==INTERN_DELETE &&
                    r->u.appl.count==1) {
                    
                    for (i = 0; i < count; ++i) {
                        if (_th_equal(env,args[i],r->u.appl.args[0])) {
                            _zone_print_exp("Deleting", args[i]) ;
                            
                            args[i] = args[--count] ;
                            derives[i] = derives[count] ;
                            augmented = 1 ;
                            goto aug_cont ;
                        }
                    }
                    
                } else if (r->type==EXP_APPL && r->u.appl.functor==INTERN_CHANGE &&
                    r->u.appl.count==2) {
                    
                    if (!(r->u.appl.args[0]==r->u.appl.args[1])) {
                    
                        for (i = 0; i < count; ++i) {
                            if (_th_equal(env,args[i],r->u.appl.args[0])) {
                            
                                if (!_th_on_add_list(env,adds,r->u.appl.args[1])) {
                                    args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (count+r->u.appl.count)) ;
                                    derives2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (count+r->u.appl.count)) ;
                                    for (j = 0; j < count; ++j) {
                                        args2[j] = args[j] ;
                                        derives2[j] = derives[j] ;
                                    }
                                    _zone_print_exp("Replacing", args[i]) ;
                                    _zone_print_exp("with", r->u.appl.args[1]) ;
                                
                                    al = (struct add_list *)ALLOCA(sizeof(struct add_list)) ;
                                    al->e = r->u.appl.args[1] ;
                                    al->next = adds ;
                                    adds = al ;
                                    args2[i] = _th_int_rewrite(env,r->u.appl.args[1], 0) ;
                                
                                    derive = _th_derive_prepare_detailed(env,args2[i]) ;
                                    //if (derives[i] != NULL && derive != NULL) {
                                    //    derive = _merge_derives(env, derives[i], derive) ;
                                    //    if (!rew_equal(env,derive,derives[i])) change = 1 ;
                                    //    derives[i] = derive ;
                                    //} else if (derive != NULL) {
                                    derives2[i] = derive ;
                                    augmented = 1 ;
                                    goto aug_cont ;
                                }
                            }
                        }
                    }
                    args2 = args;
                    derives2 = derives ;
                    _zone_print0("change failure") ;
                    goto aug_cont ;
                    
                } else if (r->type==EXP_APPL && r->u.appl.functor==INTERN_ADD &&
                    r->u.appl.count==1) {
                    
                    r = r->u.appl.args[0] ;
                }
                
                if (r->type==EXP_APPL && r->u.appl.functor==INTERN_AND) {
                    args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (count+r->u.appl.count)) ;
                    derives2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (count+r->u.appl.count)) ;
                    for (j = 0; j < count; ++j) {
                        args2[j] = args[j] ;
                        derives2[j] = derives[j] ;
                    }
                    for (j = 0; j < r->u.appl.count; ++j) {
                        if (!_th_on_add_list(env,adds,r->u.appl.args[j])) {
                            al = (struct add_list *)ALLOCA(sizeof(struct add_list)) ;
                            al->e = r->u.appl.args[j] ;
                            al->next = adds ;
                            adds = al ;
                            args2[count] = _th_int_rewrite(env, r->u.appl.args[j], 0) ;
                            derives2[count++] = _th_derive_prepare_detailed(env,args2[count]) ;
                            augmented = 1 ;
                        }
                    }
                } else {
                    al = (struct add_list *)ALLOCA(sizeof(struct add_list)) ;
                    al->e = r ;
                    al->next = adds ;
                    adds = al ;
                    args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (count+1)) ;
                    derives2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (count+1)) ;
                    _zone_print2("pre loop %d %d", j, count) ;
                    for (j = 0; j < count; ++j) {
                        args2[j] = args[j] ;
                        derives2[j] = derives[j] ;
                    }
                    args2[count] = _th_int_rewrite(env, r, 0) ;
                    derives2[count++] = _th_derive_prepare_detailed(env,args2[count]) ;
                }
                args = args2 ;
                derives = derives2 ;
                _zone_print_exp("Adding", r) ;
            }
aug_cont:
            _zone_print0("Done processing") ;
            applications = applications->next ;
        }
        _tree_undent() ;
        _zone_print0("Out of loop1") ;
    }
    _tree_undent() ;
    _zone_print1("Here a %d", count);
    if (count > 1) {
        res = _ex_intern_appl_env(env,INTERN_AND,count,args);
    } else {
        res = args[0] ;
    }
    _zone_print0("Here b");
    return res ;
}

int _th_do_context_rewrites = 1;
int _th_do_and_or_context_rewrites = 1;

struct _ex_intern *equal_elim(struct env *env, struct _ex_intern *rule, struct _ex_intern *orig)
{
    int i, count, *free_vars;
    struct _ex_intern *res = rule;

    free_vars = _th_get_free_vars_leave_marked(rule->u.appl.args[0], &count);
    if (rule->u.appl.args[2]->type==EXP_APPL && rule->u.appl.args[2]->u.appl.functor==INTERN_EQUAL &&
        rule->u.appl.args[2]->u.appl.count==2) {
        if (rule->u.appl.args[2]->u.appl.args[0]->type==EXP_VAR &&
            (_th_intern_get_data(rule->u.appl.args[2]->u.appl.args[0]->u.var)&1)==0) {
            if (_th_is_free_in(orig,rule->u.appl.args[2]->u.appl.args[0]->u.var)) {
                _zone_print0("Here2") ;
                res = _ex_intern_appl3_env(env,rule->u.appl.functor,rule->u.appl.args[0],rule->u.appl.args[1],_ex_true);
                goto finish;
            }
        } else if (rule->u.appl.args[2]->u.appl.args[1]->type==EXP_VAR &&
            (_th_intern_get_data(rule->u.appl.args[2]->u.appl.args[1]->u.var)&1)==0) {
            if (_th_is_free_in(orig,rule->u.appl.args[2]->u.appl.args[1]->u.var)) {
                _zone_print0("Here3") ;
                res = _ex_intern_appl3_env(env,rule->u.appl.functor,rule->u.appl.args[0],rule->u.appl.args[1],_ex_true);
                goto finish;
            }
        }
    } else if (rule->u.appl.args[2]->type==EXP_APPL &&
               (rule->u.appl.args[2]->u.appl.functor==INTERN_AND ||
                rule->u.appl.args[2]->u.appl.functor==INTERN_NC_AND)) {
        struct _ex_intern *cond = rule->u.appl.args[2] ;
        struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * cond->u.appl.count);
        int pos = -1;
        for (i = 0; i < cond->u.appl.count; ++i) {
            args[i] = cond->u.appl.args[i] ;
            if (pos < 0 && args[i]->type==EXP_APPL && args[i]->u.appl.functor==INTERN_EQUAL &&
                args[i]->u.appl.count==2) {
                if (args[i]->u.appl.args[0]->type==EXP_VAR && (_th_intern_get_data(args[i]->u.appl.args[0]->u.var)&1)==0) {
                    if (_th_is_free_in(orig,args[i]->u.appl.args[0]->u.var)) {
                        pos = i ;
                    }
                } else if (args[i]->u.appl.args[1]->type==EXP_VAR && (_th_intern_get_data(args[i]->u.appl.args[1]->u.var)&1)==0) {
                    if (_th_is_free_in(orig,args[i]->u.appl.args[0]->u.var)) {
                        pos = i ;
                    }
                }
            }
        }
        if (pos < 0) goto finish ;
        args[pos] = args[cond->u.appl.count-1] ;
        res = _ex_intern_appl3_env(env,rule->u.appl.functor, rule->u.appl.args[0], rule->u.appl.args[1],
                  _ex_intern_appl_env(env,cond->u.appl.functor,cond->u.appl.count-1,args)) ;
    }
finish:
    for (i = 0; i < count; ++i) {
        _th_intern_set_data(free_vars[i], 0) ;
    }
    //if (res != rule) {
    //    printf("ORIG: %s\n", _th_print_exp(rule)) ;
    //    printf("ELIM: %s\n", _th_print_exp(res)) ;
    //}
    return res;
}

//struct env **genv;

#ifdef XX
void test_bmainb(struct _ex_intern *e)
{
    struct _ex_intern *x = e;
    if (_tree_zone < 17669) return;
    if (e->type != EXP_APPL) return;
    if (strcmp(_th_intern_decode(e->u.appl.functor),"BmainB_46_f_ge_3")) return;
    if (e->u.appl.args[1]->type != EXP_VAR) return;
    if (strcmp(_th_intern_decode(e->u.appl.args[1]->u.var),"_term32")) return;
    e = e->u.appl.args[0];
    if (e->type != EXP_APPL) return;
    if (e->u.appl.functor != INTERN_NAT_PLUS) return;
    if (e->u.appl.args[1]->type != EXP_VAR) return;
    if (strcmp(_th_intern_decode(e->u.appl.args[1]->u.var),"BmainB_46_iBOT")) return;
    if (e->u.appl.args[0]->type != EXP_INTEGER) return;
    e = e->u.appl.args[0];
    if (e->u.integer[1]!=5) return;
    fprintf(stderr, "e = %s\n", _th_print_exp(x));
    exit(1);
}
#endif

static int has_the_subterm(struct _ex_intern *e, struct _ex_intern *t)
{
    int i;

    if (e==t) return 1;

    if (!e || e->type != EXP_APPL) return 0;

    for (i = 0; i < e->u.appl.count; ++i) {
        if (has_the_subterm(e->u.appl.args[i], t)) return 1;
    }

    return 0;
}

static int no_big_term(struct _ex_intern *e)
{
    int i;

    if (e->type != EXP_APPL) return 1;
    if (e->u.appl.count > 100) return 0;

    for (i = 0; i < e->u.appl.count; ++i) {
        if (!no_big_term(e->u.appl.args[i])) return 0;
    }
    return 1;
}

static struct _ex_intern *texp1, *texp2, *texp3;

int both_in_big_term(struct _ex_intern *e)
{
    int i;
    int p1 = 0, p2 = 0;

    if (e->type != EXP_APPL || e->u.appl.count < 100) return 0;

    for (i = 0; i < e->u.appl.count; ++i) {
        if (texp1==e->u.appl.args[i]) p1 = 1;
        if (e->u.appl.args[i]->type==EXP_APPL && e->u.appl.args[i]->u.appl.functor==INTERN_NOT &&
            e->u.appl.args[i]->u.appl.args[0]==texp1) p1=-1;
        if (texp2==e->u.appl.args[i]) p2 = 1;
        if (e->u.appl.args[i]->type==EXP_APPL && e->u.appl.args[i]->u.appl.functor==INTERN_NOT &&
            e->u.appl.args[i]->u.appl.args[0]==texp2) p2=-1;
    }

    return (p1 && (p1==p2));
}

struct _ex_intern *_th_int_rewrite(struct env *env, struct _ex_intern *e, int do_transitive)
{
    struct _ex_intern *res1, *res2, *stval, **args ;
    int i;
    int repeat_allowed = 1 ;
    int j;
    struct change_list no_change = { NULL, NULL, NULL, 0 } ;
    char *mark ;
    int start_cycle ;
    static int nesting_level = 0 ;
    //extern void _check_splits(struct _ex_intern *e);
    stval = e ;

    ++rewrite_level ;

    _zone_print_exp("Rewriting", e) ;
    _tree_indent() ;
    /*
    * First, check the cache
    */
    //_th_flush_context() ;
    //_zone_print1("cache %s", _th_print_exp(_th_get_context())) ;
    //_zone_print1("reduce context %s\n", _th_print_exp(_th_context)) ;
    res1 = ((e->can_cache)?_th_get_cache_rewrite(env,e,do_transitive):NULL) ;
    //_zone_print1("final context %s\n", _th_print_exp(_th_context)) ;
    ++cache_count ;
    //term_count += _th_get_context()->u.appl.count ;
    if (res1 != NULL) {
        _tree_undent() ;
        _zone_print2("From cache %d %s", e->cache_line, _th_print_exp(res1)) ;
        --rewrite_level ;
		//fprintf(stderr, "return1  %x\n", res1);
		//fflush(stderr);
        if (res1->rewrite==res1 && !res1->cache_bad) return res1 ;
        e = res1;
        _tree_indent();
    }
    ++term_count ;
    if (e->in_rewrite) {
        _zone_print0("Infinite loop") ;
        exit(1);
        block_cycle = _th_cycle ;
        //_th_violation_tested = _th_violation_used = _th_cycle ;
        _tree_undent() ;
        --rewrite_level ;
		//fprintf(stderr, "return2  %x\n", e);
		//fflush(stderr);
        return e ;
    }
    //printf("e, e->in_rewrite = %x %x\n", e, e->in_rewrite) ;
    //fflush(stdout) ;
    e->in_rewrite = rewrite_level ;
    start_cycle = _th_cycle++ ;

    if (do_transitive & 16) repeat_allowed = 0;

    /*
    * Rewrite the arguments
    */
    switch (e->type) {
        
    case EXP_APPL:
        switch (e->u.appl.functor) {
            
        case INTERN_QUOTE:
            if (e->u.appl.count==1) {
                res2 = res1 = e ;
                _tree_undent() ;
                goto finish ;
            } else {
                goto def_case ;
            }

        case INTERN_ITE:
            if (!_th_do_context_rewrites) goto def_case ;
            if (_th_cond_level()) goto def_case ;
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * 3) ;
            _zone_print0("Subterm 0");
            args[0] = res1 = _th_int_rewrite(env,e->u.appl.args[0], 1);
            if (res1==_ex_true) {
                _zone_print0("Subterm 1");
                res1 = _th_int_rewrite(env,e->u.appl.args[1], 1);
            } else if (res1==_ex_false) {
                _zone_print0("Subterm 2");
                res1 = _th_int_rewrite(env,e->u.appl.args[2], 1);
            } else if (res1->type==EXP_APPL && res1->u.appl.functor==INTERN_NOT &&
                       res1->u.appl.count==1) {
                args[0] = res1->u.appl.args[0];
                _zone_print0("Subterm 1");
                args[2] = _th_int_rewrite(env,e->u.appl.args[1], 1);
                _zone_print0("Subterm 2");
                args[1] = _th_int_rewrite(env,e->u.appl.args[2], 1);
                res1 = _ex_intern_appl_env(env,INTERN_ITE,3,args);
            } else {
                _zone_print0("Subterm 1");
                args[1] = _th_int_rewrite(env,e->u.appl.args[1], 1);
                //f = _th_negate_term(env,res1);
                _zone_print0("Subterm 2");
                args[2] = _th_int_rewrite(env,e->u.appl.args[2], 1);
                res1 = _ex_intern_appl_env(env,INTERN_ITE,3,args);
            }
            break;

        case INTERN_OR:
            args = ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                //_zone_print0("f = %x %s", f, _th_print_exp(f));
                args[i] = _th_int_rewrite(env,e->u.appl.args[i],((do_transitive & 15) | 1)) ;
#ifndef FAST
                if (args[i]!=e->u.appl.args[i]) _zone_print1("*** DIFFERENT *** %d", i);
#endif
                if (args[i]==_ex_true) {
                    res1 = _ex_true;
                    goto finish_or;
                }
            }
			res1 = _ex_intern_appl_env(env,INTERN_OR,e->u.appl.count,args);
finish_or:
            break ;
            
        case INTERN_AND:
            args = ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = _th_int_rewrite(env,e->u.appl.args[i],((do_transitive & 15) | 1)) ;
#ifndef FAST
                if (args[i]!=e->u.appl.args[i]) _zone_print1("*** DIFFERENT *** %d", i);
#endif
                if (args[i]==_ex_false) {
                    res1 = _ex_false;
                    goto finish_and;
                }
            }
			res1 = _ex_intern_appl_env(env,INTERN_AND,e->u.appl.count,args);
finish_and:
            break ;
            
        case INTERN_DEF:
        case INTERN_DEFAULT:
            res1 = e ;
            break ;
            
        case INTERN_NOT:
            mark = _th_alloc_mark(REWRITE_SPACE) ;
            i = 0;
            if (do_transitive & 4) i+=8 ;
            if (do_transitive & 8) i+=4 ;
            _zone_print0("Subterm 0") ;
            res1 = _th_int_rewrite(env,e->u.appl.args[0],i) ;
            _th_alloc_release(REWRITE_SPACE,mark) ;
            res1 = _ex_intern_appl1_env(env,INTERN_NOT,res1) ;
            break ;

        default:
def_case:
            mark = _th_alloc_mark(REWRITE_SPACE) ;
            args = ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                _zone_print1("Subterm %d",i);
                args[i] = _th_int_rewrite(env,e->u.appl.args[i],0) ;
            }
            _th_alloc_release(REWRITE_SPACE,mark) ;
            res1 = _ex_intern_appl_equal_env(env,
                e->u.appl.functor,e->u.appl.count,args,e->type_inst) ;
            }
            if (_th_is_ac(env,e->u.appl.functor) ||
                _th_is_a(env,e->u.appl.functor)) {
                res1 = _th_flatten_top(env,res1) ;
            }
            break;

        case EXP_QUANT:
            _zone_print0("Subterm 1") ;
            res2 = _th_int_rewrite(env,e->u.quant.cond,1) ;
            res1 = _th_int_rewrite(env,e->u.quant.exp,1) ;
            res1 = _ex_intern_quant(e->u.quant.quant,
                e->u.quant.var_count,
                e->u.quant.vars,
                res1,
                res2) ;
            break ;
            
        case EXP_CASE:
            _zone_print0("Subterm 0");
            res1 = _th_int_rewrite(env,e->u.case_stmt.exp,1) ;
            args = ALLOCA(sizeof(struct _ex_intern *) * e->u.case_stmt.count * 2) ;
            for (i = 0; i < e->u.case_stmt.count; ++i) {
                args[i*2] = e->u.case_stmt.args[i*2] ;
                _zone_print1("Subterm %d", i * 2 + 1);
                args[i*2+1] = _th_int_rewrite(env,e->u.case_stmt.args[i*2+1],1) ;
            }
            res1 = _ex_intern_case(res1,e->u.case_stmt.count,args) ;
            break ;
            
        case EXP_INDEX:
            _zone_print0("Subterm 0");
            res1 = _th_int_rewrite(env,e->u.index.exp,1) ;
            res1 = _ex_intern_index(res1,e->u.index.functor,e->u.index.term) ;
            break ;
            
        default:
            res1 = e ;
            break ;
    }
    
    mark = _th_alloc_mark(REWRITE_SPACE) ;
retry_top:
    /*
    * Rewrite the top
    */
    //_zone_print1("repeat allowed = %d", repeat_allowed) ;
    _zone_print_exp("Builtin for", res1);
    //_zone_print2("env = %d %d", env, &env);
    //genv = &env;
#ifdef XX
    if (res1 && both_in_big_term(res1)) {
        fprintf(stderr, "Both in big term1\n");
        exit(1);
    }
#endif
    res2 = _th_builtin(env,res1) ;
    //if (res2) {
    //    printf("%s reduces to\n", _th_print_exp(res1));
    //    printf("    %s\n", _th_print_exp(res2));
    //}
#ifdef XX
    if (res2 && both_in_big_term(res2)) {
        fprintf(stderr, "Both in big term2\n");
        exit(1);
    }
    //_zone_print2("env = %d %d", env, &env);
    if (texp1==NULL) {
        texp1 = _th_parse(env,"(rless AT9_Z AT10_Z)");
        texp2 = _th_parse(env,"(rless AT10_Z AT9_Z)");
        texp3 = _th_parse(env, "AT9_DELTA");
    }
    if (no_big_term(res1) && (has_the_subterm(res2,texp1) || has_the_subterm(res2,texp2) ||
        has_the_subterm(res1,texp1) || has_the_subterm(res1,texp2) ||
        has_the_subterm(res1,texp3) || has_the_subterm(res1,texp2))) {
        printf("builtin before %s\n", _th_print_exp(res1));
        printf("builtin after %s\n", _th_print_exp(res2));
    }
    if (res1 && res1->type==EXP_APPL && res1->u.appl.count > 100) {
        for (i = 0; i < res1->u.appl.count; ++i) {
            if (has_the_subterm(res1->u.appl.args[i],texp1) || has_the_subterm(res1->u.appl.args[i],texp2) ||
                has_the_subterm(res1->u.appl.args[i],texp3)) {
                printf("Big term pos %d is %s\n", i, _th_print_exp(res1->u.appl.args[i]));
            }
        }
    }
    if (res2 && res2->type==EXP_APPL && res2->u.appl.count > 100) {
        for (i = 0; i < res2->u.appl.count; ++i) {
            if (has_the_subterm(res2->u.appl.args[i],texp1) || has_the_subterm(res2->u.appl.args[i],texp2) ||
                has_the_subterm(res2->u.appl.args[i],texp3)) {
                printf("Big term res2 pos %d is %s\n", i, _th_print_exp(res2->u.appl.args[i]));
            }
        }
    }
#endif
    if (res2 && !repeat_allowed) {
        if (res2->type==EXP_APPL && (res2->u.appl.functor==INTERN_AND || res2->u.appl.functor==INTERN_OR) &&
            res1->type==EXP_APPL && (res1->u.appl.functor==INTERN_AND || res1->u.appl.functor==INTERN_OR)) {
            for (i = 0; i < res2->u.appl.count; ++i) {
                for (j = 0; j < res1->u.appl.count; ++j) {
                    if (res1->u.appl.args[j]==res2->u.appl.args[i]) goto cont_look;
                }
                repeat_allowed = 1;
                goto cont_res;
cont_look:;
            }
        }
        res1 = res2 ;
        goto retry_top ;
    }
cont_res:
    if (res2==NULL) {
        if (res1->rewrite != NULL && !res1->cache_bad) {
            res2 = res1->rewrite;
            while (res2->rewrite && res2->rewrite != res2 && !res2->cache_bad) res2 = res2->rewrite;
            _zone_print_exp("cache to", res2);
            _tree_undent();
            goto finish;
        }
        //res2 = _th_fast_rewrite_rule(env,res1,do_transitive & 15) ;
    } else {
        _zone_print_exp("Builtin", res2) ;
    }
    if (res2==NULL) {
        res2 = res1 ;
    }
    _th_alloc_release(REWRITE_SPACE, mark) ;

    /*
    * Repeat rewriting steps if anything has changed at the top level
    */
    if (res2 != res1 && repeat_allowed) {
        _tree_undent() ;
        //_zone_print1("stval %s", _th_print_exp(stval)) ;
        //_zone_print2("cmp %d %d", res2, stval) ;
        res2 = _th_int_rewrite(env, res2, do_transitive & 15) ;
    } else {
        _tree_undent() ;
        _zone_print2("Done %d %s", _tree_count, _th_print_exp(res2)) ;
    }

finish:

   /*
    * Save into the cache
    */
    //_zone_print1("save context %s\n", _th_print_exp(_th_context)) ;
    //_zone_print1("save exp %s", _th_print_exp(e)) ;
    //_zone_print1("can_cache = %d", e->can_cache);
    if (e->can_cache && start_cycle >= block_cycle && _th_check_block(start_cycle)) {
        //_zone_print1("*** Saving %s", _th_print_exp(e));
        //_zone_print1("Result %s", _th_print_exp(res2));
        //_zone_print2("trans, start %d %d", do_transitive, start_cycle);
        //_zone_print0("Setting 1");
        _zone_print_exp("Setting cache", e);
        _th_set_cache_rewrite(env,e,res2,do_transitive,start_cycle) ;
        //_zone_print_exp("res2->rewrite", res2->rewrite);
        if (res2->can_cache && res2->rewrite==NULL) {
            //_zone_print1("*** Saving %s", _th_print_exp(res2));
            //_zone_print1("Result %s", _th_print_exp(res2));
            //_zone_print2("trans, start %d %d", do_transitive, start_cycle);
            //_zone_print_exp("Setting 2", res2);
            _zone_print_exp("Setting cache", res2);
            _th_set_cache_rewrite(env,res2,res2,do_transitive,start_cycle) ;
        }
    }
    e->in_rewrite = 0 ;
    --rewrite_level ;
	//fprintf(stderr, "return3  %x\n", res2);
	//fflush(stderr);
    //if (res2==_ex_bool) exit(1);
    //test_bmainb(res2);
    //_check_splits(res2);
    return res2 ;
}

int _th_in_rewrite = 0 ;

char *_th_start_rewrite()
{
    char *mark ;
    int i ;

    //if (_zone_active()) {
        //start_check_results() ;
        //do_checks = 1 ;
    //} else {
        do_checks = 0 ;
    //}

    _th_push_context() ;
    transitive_count = 0 ;
    long_transitive_count = 0 ;
    cache_count = 0 ;
    term_count = 0 ;
    _th_cycle = 0 ;
    block_cycle = 0 ;
    //_th_transitive_reset() ;
    //_ex_push() ;
    mark = _th_alloc_mark(REWRITE_SPACE) ;
    _th_context = _th_get_context() ;

    for (i = 0; i < MAX_LEVELS; ++i) {
        _th_context_used[i] = 0 ;
        _th_context_tested[i] = 0 ;
    }

    _th_top_rule = NULL ;
    _th_top_backchain = NULL ;
    _th_in_rewrite = 1 ;
    _th_context_any_tested  = 0 ;
    _th_context_any_used = 0 ;
    _th_violation_tested = 0 ;
    _th_violation_used = 0 ;
    return mark ;
}

#ifdef _DEBUG
int rcmp(struct _ex_intern **r1, struct _ex_intern **r2)
{
    return (*r1)->rule_try_count - (*r2)->rule_try_count ;
}

int rcmp2(struct _ex_intern **r1, struct _ex_intern **r2)
{
    return (*r1)->backchain_tries - (*r2)->backchain_tries ;
}
#endif

struct _ex_intern *_th_finish_rewrite(char *mark, struct env *env, struct _ex_intern *res)
{
#ifdef _DEBUG
#ifndef FAST
    if (_zone_active()) {
        int count = 0, i ;
        struct _ex_intern *e = _th_top_rule ;
        struct _ex_intern **args ;
        while (e) {
            ++count ;
            e = e->next_rule ;
        }
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern **) * count) ;
        for (e = _th_top_rule, i = 0; i < count; ++i, e = e->next_rule) {
            args[i] = e ;
        }
        qsort(args,count,sizeof(struct _ex_intern *), (void *)rcmp);

        _zone_print0("Rule usage") ;
        _tree_indent() ;
        for (i = 0; i < count; ++i) {
            _zone_print3("%10d %10d %s", args[i]->rule_try_count, args[i]->rule_use_count, _th_print_exp(args[i])) ;
            args[i]->rule_try_count = args[i]->rule_use_count = 0 ;
        }
        _tree_undent() ;

        count = 0 ;
        e = _th_top_backchain ;
        while (e) {
            ++count ;
            e = e->next_backchain ;
        }
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern **) * count) ;
        for (e = _th_top_backchain, i = 0; i < count; ++i, e = e->next_backchain) {
            args[i] = e ;
        }
        qsort(args,count,sizeof(struct _ex_intern *), (void *)rcmp2);

        _zone_print0("Backchain usage") ;
        _tree_indent() ;
        for (i = 0; i < count; ++i) {
            _zone_print2("%10d %s", args[i]->backchain_tries, _th_print_exp(args[i])) ;
            args[i]->backchain_tries = 0 ;
        }
        //finish_check_results(env) ;
        _tree_undent() ;
    } else {
        while (_th_top_rule) {
            _th_top_rule->rule_try_count = _th_top_rule->rule_use_count = 0 ;
            _th_top_rule = _th_top_rule->next_rule ;
        }
        while (_th_top_backchain) {
            _th_top_backchain->backchain_tries = 0 ;
            _th_top_backchain = _th_top_backchain->next_backchain ;
        }
    }
#endif
#endif

    _th_in_rewrite = 0 ;

    _th_alloc_release(REWRITE_SPACE,mark) ;
    //_th_transitive_reset() ;
    //_ex_pop() ;
    //if (res != NULL) res = _ex_reintern(env,res) ;
    //_ex_release() ;
    _th_pop_context() ;
    _th_context = NULL ;

#ifdef _DEBUG
#ifndef FAST
    fprintf(stderr, "Transitives: %d\n", transitive_count) ;
    fprintf(stderr, "Long transitives: %d\n", long_transitive_count) ;
    fprintf(stderr, "Cache count: %d\n", cache_count) ;
    fprintf(stderr, "Term count: %d\n", term_count) ;
#endif
#endif

    return res ;
}

#define NUMBER_REWRITES
//#define SHOW_REWRITE 2252
//#define LOG_REWRITE

#ifdef LOG_REWRITE
static FILE *rewrite_log_file = NULL;
#endif

struct _ex_intern *_th_rewrite(struct env *env, struct _ex_intern *e)
{
    char *mark ;
    struct _ex_intern *res, *res2;
    static int r_count = 0;

#ifdef NUMBER_REWRITES
#ifndef FAST
    int old_tree_mute = _tree_mute;
#endif
#endif

    //_th_rewrite_next = _th_add_contexts_to_cache(env,_th_rewrite_next);

    //if (e==NULL) return NULL ;
    if (e==_ex_true || e==_ex_false) return e;

#ifdef LOG_REWRITE
    if (rewrite_log_file==NULL) {
        rewrite_log_file = fopen("log.rew", "w");
    }
#endif

#ifdef NUMBER_REWRITES
    if (e != _ex_true) {
		_zone_print1("Rewriting %d", r_count);
		_zone_print_exp("exp %s", e) ;
	}
#ifdef SHOW_REWRITE
#ifndef FAST
    if (r_count==SHOW_REWRITE) {
        _tree_start = 0;
        _tree_end = 2000000;
        _tree_sub = _tree_sub2 = -1;
        _tree_mute = 0;
    }
    if (r_count > SHOW_REWRITE) {
        fprintf(stderr, "Show rewrite count exceeded\n");
        exit(1);
    }
#endif
#endif
    ++r_count;
#endif
#ifdef LOG_REWRITE
    fprintf(rewrite_log_file,"rewrite %d: %s\n", r_count, _th_print_exp(e));
    fflush(rewrite_log_file);
#endif
    _zone_increment() ;
    res = _th_check_rewrite(e) ;
    if (res) {
        _zone_print_exp("From memory", res);
#ifdef NUMBER_REWRITES
#ifndef FAST
        _tree_mute = old_tree_mute;
#endif
        _tree_indent();
        if (e != _ex_true) _zone_print_exp("result", res);
        _tree_undent();
#endif
#ifdef LOG_REWRITE
        fprintf(rewrite_log_file,"result %d: %s\n", r_count-1, _th_print_exp(res));
        fflush(rewrite_log_file);
#endif
        return res ;
    }
    if (_th_in_rewrite) {
        res = _th_int_rewrite(env,e,1) ;
        _zone_print_exp("Result %s\n", e) ;
        _th_set_rewrite(res);
#ifdef NUMBER_REWRITES
#ifndef FAST
        _tree_mute = old_tree_mute;
#endif
        _tree_indent();
        if (e != _ex_true) _zone_print_exp("result", res);
        _tree_undent();
#endif
#ifdef LOG_REWRITE
        fprintf(rewrite_log_file,"result %d: %s\n", r_count-1, _th_print_exp(res));
        fflush(rewrite_log_file);
#endif
        return res ;
    }

    mark = _th_start_rewrite() ;
	res = e;
	e = NULL;
	res2 = NULL;
	while (res != e) {
		e = res;
        //_th_clear_cache() ;
		_zone_enter_sub();
        res = _th_int_rewrite(env,res,1) ;
		_zone_exit_sub();
		if (res != res2) res = _th_context_rewrite(env,res);
		res2 = res;
	}
    res = _th_finish_rewrite(mark, env, res) ;

    _th_set_rewrite(res) ;

    _zone_print_exp("Result", res) ;

#ifdef NUMBER_REWRITES
#ifndef FAST
    _tree_mute = old_tree_mute;
#endif
    _tree_indent();
    if (res != _ex_true) _zone_print_exp("result", res);
    _tree_undent();
#endif
#ifdef LOG_REWRITE
    fprintf(rewrite_log_file,"result %d: %s\n", r_count-1, _th_print_exp(res));
    fflush(rewrite_log_file);
#endif
    return res ;
}

struct _ex_intern *_th_nc_rewrite(struct env *env, struct _ex_intern *e)
{
    char *mark ;
    struct _ex_intern *res;
    static int r_count = 0;

#ifndef FAST
#ifdef NUMBER_REWRITES
    int old_tree_mute = _tree_mute;
#endif
#endif

    //printf("Rewriting %s\n", _th_print_exp(e));

    //if (e==NULL) return NULL ;
    //if (e==_ex_true || e==_ex_false) return e;

#ifdef LOG_REWRITE
    if (rewrite_log_file==NULL) {
        rewrite_log_file = fopen("log.rew", "w");
    }
#endif

#ifndef FAST
#ifdef NUMBER_REWRITES
#ifndef FAST
//#ifdef _DEBUG
    if (_zone_active()) {
        _zone_print3("Rewriting %d %d %s", _tree_zone, r_count, _th_print_exp(e)) ;
    } else {
        _zone_print2("Rewriting %d %d", _tree_zone, r_count);
    }
//#else
//    if (e != _ex_true) _zone_print3("Rewriting %d %d %s", _tree_zone, r_count, _th_print_exp(e)) ;
//#endif
#endif
#ifdef SHOW_REWRITE
    if (r_count==SHOW_REWRITE) {
        _tree_start = 0;
        _tree_end = 2000000;
        _tree_sub = _tree_sub2 = -1;
        _tree_mute = 0;
    }
    if (r_count > SHOW_REWRITE) {
        fprintf(stderr, "Show rewrite count exceeded 2\n");
        exit(1);
    }
#endif
#endif
    ++r_count;
#endif
#ifdef LOG_REWRITE
    fprintf(rewrite_log_file,"rewrite %d: %s\n", r_count, _th_print_exp(e));
    fflush(rewrite_log_file);
#endif
    _zone_increment() ;
#ifdef CHECK_REWRITE
    res = _th_check_rewrite(e) ;
    if (res) {
        _zone_print_exp("From memory", res);
#ifdef NUMBER_REWRITES
#ifndef FAST
        _tree_mute = old_tree_mute;
#endif
        _tree_indent();
        if (e != _ex_true) _zone_print_exp("result", res);
        _tree_undent();
#endif
#ifdef LOG_REWRITE
        fprintf(rewrite_log_file,"result %d: %s\n", r_count-1, _th_print_exp(res));
        fflush(rewrite_log_file);
#endif
        return res ;
    }
#endif
    if (_th_in_rewrite) {
		_zone_enter_sub();
        res = _th_int_rewrite(env,e,1) ;
		_zone_exit_sub();
        _zone_print1("Result %s\n", _th_print_exp(e)) ;
        _th_set_rewrite(res);
#ifdef NUMBER_REWRITES
#ifndef FAST
        _tree_mute = old_tree_mute;
#endif
        _tree_indent();
        if (e != _ex_true) _zone_print_exp("result", res);
        _tree_undent();
#endif
#ifdef LOG_REWRITE
        fprintf(rewrite_log_file,"result %d: %s\n", r_count-1, _th_print_exp(res));
        fflush(rewrite_log_file);
#endif
        return res ;
    }

    //_th_clear_cache() ;
    //_th_rewrite_next = _th_add_contexts_to_cache(env,_th_rewrite_next);
    mark = _th_start_rewrite() ;
	res = e;
	e = NULL;
	_zone_enter_sub();
    res = _th_int_rewrite(env,res,1) ;
	_zone_exit_sub();
    res = _th_finish_rewrite(mark, env, res) ;

#ifdef CHECK_REWRITE
    _th_set_rewrite(res) ;
#endif

    _zone_print_exp("Result", res) ;

#ifdef NUMBER_REWRITES
#ifndef FAST
    _tree_mute = old_tree_mute;
#endif
    _tree_indent();
    if (res != _ex_true) _zone_print_exp("result", res);
    _tree_undent();
#endif
#ifdef LOG_REWRITE
    fprintf(rewrite_log_file,"result %d: %s\n", r_count-1, _th_print_exp(res));
    fflush(rewrite_log_file);
#endif
    return res ;
}



