/*
 * derive.c
 *
 * Routines for generating derived rules and adding them to the current context
 * in the environment.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Pubolic License
 */
#include <stdio.h>
#include <stdlib.h>
#include "Globals.h"
#include "Intern.h"

static int rule_priority;

static int add_rule(struct env *env, struct _ex_intern *e)
{
    int res ;

    if (e->type != EXP_APPL || (e->u.appl.count != 3 && e->u.appl.count != 2)) return 0 ;

    //if (e->u.appl.args[0]->type==EXP_MARKED_VAR &&
    //    !strcmp(_th_intern_decode(e->u.appl.args[0]->u.var),"_term12") &&
    //    e->u.appl.args[1]->type==EXP_APPL) {
    //    printf("e = %s\n", _th_print_exp(e));
    //    exit(1);
    //}

    if (e->u.appl.functor==INTERN_AND) {
        int i ;
        res = 0 ;
        for (i = 0; i < e->u.appl.count; ++i) {
            res = (add_rule(env,e->u.appl.args[i]) || res) ;
        }
        return res ;
    }
    //_tree_print_exp("Derive Adding rule", e) ;
    if (_th_equal(env, e->u.appl.args[0],e->u.appl.args[1])) return 0 ;
    if ((e->u.appl.args[0]==_ex_true || e->u.appl.args[0]==_ex_false) &&
        (e->u.appl.args[1]==_ex_true || e->u.appl.args[1]==_ex_false))
        return 0 ;

    if (rule_priority)
    {
        e = _ex_intern_appl2_env(env,INTERN_PRIORITY,_ex_intern_small_integer(rule_priority),e);
    }

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_ORIENTED_RULE) {
        e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,e->u.appl.args[0],
                                 _th_unmark_vars(env,e->u.appl.args[1]),
                                 _th_unmark_vars(env,e->u.appl.args[2]));
    }

    //_tree_print_exp("Derive Adding rule", e) ;
    if (e->rule_simplified) {
        fprintf(stderr, "Rule already simplified %s\n", _th_print_exp(e));
        exit(1);
    }
    _zone_print_exp("Adding context rule", e);
    //printf("Rule %d %s\n", _tree_zone, _th_print_exp(e));
    res = _th_add_context_property(env,e) ;

    //if (res) {
		//_zone_print("Raw adding %s", _th_print_exp(e));
        //_th_add_context_rule(e) ;
        //_th_add_rule(env,e) ;
    //}

    return res ;
}

static int is_default(struct _ex_intern *e)
{
    return (e->type==EXP_APPL && (e->u.appl.functor==INTERN_DEF ||
            e->u.appl.functor==INTERN_DEFAULT)) ;
}

char *_th_derive_push(struct env *env)
{
    char *mark = _th_alloc_mark(REWRITE_SPACE) ;
    _th_push_context_rules(env) ;
    //_th_push_context() ;
    //_th_trans_push(env) ;
    //printf("PUSH\n");
    //_tree_print("PUSH");
    return mark ;
}

void _th_derive_pop(struct env *env)
{
    _th_pop_context_rules(env) ;
    //_th_pop_context() ;
    //printf("POP\n");
    //_th_trans_pop() ;
    //_tree_print("POP");
}

void _th_derive_pop_release(struct env *env, char *rel)
{
    _th_pop_context_rules(env) ;
    _th_pop_context() ;
    //_th_trans_pop() ;
    _th_alloc_release(REWRITE_SPACE,rel) ;
}

static unsigned arg_size, arg_start, arg_base ;
static struct _ex_intern **all_rules_base, **all_rules ;

#define ARG_INCREMENT 4000

static void check_size(unsigned size)
{
    if (size + arg_base > arg_size) {
        arg_size = size + arg_base + ARG_INCREMENT ;
        all_rules_base = (struct _ex_intern **)REALLOC(all_rules_base,sizeof(struct _ex_intern *) * arg_size) ;
    }
    all_rules = all_rules_base + arg_base ;
}

struct _ex_intern *_th_derive_simplify(struct env *env, struct _ex_intern *e)
{
    if (e->type==EXP_APPL && e->u.appl.count==3 && (e->u.appl.functor==INTERN_ORIENTED_RULE || e->u.appl.functor==INTERN_FORCE_ORIENTED) &&
        _th_equal(env,e->u.appl.args[0],e->u.appl.args[1])) {
        return _ex_true ;
    }
    if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_ORIENTED_RULE || e->u.appl.functor==INTERN_FORCE_ORIENTED) &&
        e->u.appl.args[1]==_ex_false && e->u.appl.args[0]->type==EXP_APPL &&
        e->u.appl.args[0]->u.appl.functor==INTERN_NOT) {
        struct _ex_intern *args[3] ;
        args[0] = e->u.appl.args[0]->u.appl.args[0] ;
        args[1] = _ex_true ;
        args[2] = e->u.appl.args[2] ;
        e = _ex_intern_appl_env(env,e->u.appl.functor,3,args) ;
        return _th_derive_simplify(env, e) ;
    }
    if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_ORIENTED_RULE || e->u.appl.functor==INTERN_FORCE_ORIENTED) &&
        e->u.appl.args[1]==_ex_true && e->u.appl.args[0]->type==EXP_APPL &&
        e->u.appl.args[0]->u.appl.functor==INTERN_NOT) {
        struct _ex_intern *args[3] ;
        args[0] = e->u.appl.args[0]->u.appl.args[0] ;
        args[1] = _ex_false ;
        args[2] = e->u.appl.args[2] ;
        e = _ex_intern_appl_env(env,e->u.appl.functor,3,args) ;
        return _th_derive_simplify(env, e) ;
    }
    if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_ORIENTED_RULE || e->u.appl.functor==INTERN_FORCE_ORIENTED) &&
        e->u.appl.args[1]==_ex_true && e->u.appl.args[0]->type==EXP_APPL &&
        e->u.appl.args[0]->u.appl.functor==INTERN_EQUAL &&
        _th_smaller(env,e->u.appl.args[0]->u.appl.args[0],e->u.appl.args[0]->u.appl.args[1])) {
        struct _ex_intern *args[3] ;
        args[0] = e->u.appl.args[0]->u.appl.args[1] ;
        args[1] = e->u.appl.args[0]->u.appl.args[0] ;
        args[2] = e->u.appl.args[2] ;
        e = _ex_intern_appl_env(env,e->u.appl.functor,3,args) ;
        return _th_derive_simplify(env, e) ;
    }
    if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_ORIENTED_RULE || e->u.appl.functor==INTERN_FORCE_ORIENTED) &&
        e->u.appl.args[1]==_ex_true && e->u.appl.args[0]->type==EXP_APPL &&
        e->u.appl.args[0]->u.appl.functor==INTERN_EQUAL &&
        _th_smaller(env,e->u.appl.args[0]->u.appl.args[1],e->u.appl.args[0]->u.appl.args[0])) {
        struct _ex_intern *args[3] ;
        args[0] = e->u.appl.args[0]->u.appl.args[0] ;
        args[1] = e->u.appl.args[0]->u.appl.args[1] ;
        args[2] = e->u.appl.args[2] ;
        e = _ex_intern_appl_env(env,e->u.appl.functor,3,args) ;
        return _th_derive_simplify(env, e) ;
    }
    if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_ORIENTED_RULE || e->u.appl.functor==INTERN_FORCE_ORIENTED) &&
        e->u.appl.args[1]==_ex_true && e->u.appl.args[2]==_ex_true &&
        e->u.appl.args[0]->type==EXP_APPL && (e->u.appl.args[0]->u.appl.functor==INTERN_ORIENTED_RULE || e->u.appl.args[0]->u.appl.functor==INTERN_FORCE_ORIENTED) &&
        e->u.appl.args[0]->u.appl.count==3) {
        return _th_derive_simplify(env, e->u.appl.args[0]) ;
    }

    return e ;
}

int is_interpreted_functor(struct _ex_intern *e)
{
    int functor;

    if (e->type != EXP_APPL) return 0;

    functor = e->u.appl.functor;

    return functor==INTERN_STORE || functor==INTERN_SELECT || functor==INTERN_NAT_PLUS || functor==INTERN_NAT_TIMES ||
           functor==INTERN_NAT_DIVIDE || functor==INTERN_RAT_PLUS || functor==INTERN_RAT_TIMES ||
           functor==INTERN_RAT_DIVIDE;
}

static int is_number(struct _ex_intern *e)
{
    int f;

    if (e->type==EXP_INTEGER || e->type==EXP_RATIONAL) return 1;

    if (e->type != EXP_APPL) return 0;

    f = e->u.appl.functor;

    return f==INTERN_SELECT || f==INTERN_NAT_PLUS || f==INTERN_RAT_PLUS || f==INTERN_NAT_TIMES ||
           f==INTERN_RAT_TIMES || f==INTERN_NAT_DIVIDE || f==INTERN_RAT_DIVIDE ||
           f==INTERN_NAT_MOD || f==INTERN_RAT_MOD;
}

static int is_array(struct _ex_intern *e)
{
    int f;

    if (e->type != EXP_APPL) return 0;

    f = e->u.appl.functor;

    return f==INTERN_STORE;
}

struct _ex_intern *_derive_prepare(struct env *env, struct _ex_intern *e)
{
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT &&
        e->u.appl.args[0]->type==EXP_APPL &&
        e->u.appl.args[0]->u.appl.functor==INTERN_NOT) {
        e = e->u.appl.args[0]->u.appl.args[0];
    }
    
    if (e==_ex_false) {
        //int i = 0;
        _zone_print0("warning: putting False() in context");
        fprintf(stderr, "Warning: putting False() in context\n");
        //exit(1);
        //i = 1/i;
        return NULL;
    }
    if (e==_ex_true) {
        return NULL ;
    }
    
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_AND) {
        struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
        int i ;
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = _derive_prepare(env,e->u.appl.args[i]) ;
        }
        return _th_flatten_top(env,_ex_intern_appl_env(env,INTERN_AND,e->u.appl.count,args)) ;
    }
    
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_PRIORITY && e->u.appl.count==2) {
        struct _ex_intern *f = _derive_prepare(env,e->u.appl.args[1]) ;
        return _ex_intern_appl2_env(env,INTERN_PRIORITY, e->u.appl.args[0], f) ;
    }
    
    //e = _th_mark_vars(env,e) ;
    
    if (e->type==EXP_QUANT && e->u.quant.quant==INTERN_ALL) return _derive_prepare(env, e->u.quant.exp) ;
    
    if (e->type != EXP_APPL || e->u.appl.count != 3 ||
        (e->u.appl.functor != INTERN_ORIENTED_RULE && e->u.appl.functor != INTERN_UNORIENTED_RULE &&
        e->u.appl.functor != INTERN_FORCE_ORIENTED)) {
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL && e->u.appl.count==2) {
            int count;
            struct _ex_intern *ti = e->type_inst;
            _th_get_free_vars(e,&count);
            //printf("count = %d\n", count);
            if (count==0) {
                int cmp = _th_term_compare(env,e->u.appl.args[0],e->u.appl.args[1]);
                //printf("cmp = %d\n", cmp);
                if (cmp > 0) {
                    e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,e->u.appl.args[1],e->u.appl.args[0],_ex_true) ;
                    if (ti) {
                        e->type_inst = ti;
                    }
                } else if (cmp==0) {
                    e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,_ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0],e->u.appl.args[1]),_ex_true,_ex_true) ;
                    //fprintf(stderr, "Error: %s is unoriented\n", _th_print_exp(e));
                    //exit(1);
                } else {
                    e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,e->u.appl.args[0],e->u.appl.args[1],_ex_true) ;
                    if (ti) {
                        e->type_inst = ti;
                    }
                }
            } else {
                int l = _th_smaller(env,e->u.appl.args[0],e->u.appl.args[1]) ;
                int r = _th_smaller(env,e->u.appl.args[1],e->u.appl.args[0]) ;
                if (l && !r)
                {
                    e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,e->u.appl.args[1],e->u.appl.args[0],_ex_true) ;
                    if (ti) {
                        e->type_inst = ti;
                    }
                }
                else if (r && !l)
                {
                    e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,e->u.appl.args[0],e->u.appl.args[1],_ex_true) ;
                    if (ti) {
                        e->type_inst = ti;
                    }
                }
                else
                {
                    e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,_ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0],e->u.appl.args[1]),_ex_true,_ex_true) ;
                }
            }
        } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT && e->u.appl.count==1) {
            e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,e->u.appl.args[0],_ex_false,_ex_true) ;
        } else {
            e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,e,_ex_true,_ex_true) ;
        }
    } else if (e->u.appl.args[2]==_ex_true) {
        int l = _th_smaller(env,e->u.appl.args[0],e->u.appl.args[1]) ;
        int r = _th_smaller(env,e->u.appl.args[1],e->u.appl.args[0]) ;
        if (e->u.appl.args[0]->type==EXP_MARKED_VAR && e->u.appl.args[1]->type==EXP_MARKED_VAR) {
            if (e->u.appl.args[0]<e->u.appl.args[1]) {
                l = 1;
                r = 0;
            } else {
                l = 0;
                r = 1;
            }
        }
        if (l && !r)
        {
            e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,e->u.appl.args[1],e->u.appl.args[0],_ex_true) ;
        }
        else if (r && !l)
        {
            e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,e->u.appl.args[0],e->u.appl.args[1],_ex_true) ;
        }
        else
        {
            e = _ex_intern_appl3_env(env,INTERN_UNORIENTED_RULE,e->u.appl.args[0],e->u.appl.args[1],_ex_true) ;
        }
    }
    
    return e ;
}

struct _ex_intern *_th_derive_prepare(struct env *env, struct _ex_intern *e)
{
    e = _th_mark_vars(env,e) ;
    if (e->prepare) return e->prepare;
    //printf("Derive preparing %s\n", _th_print_exp(e));
    e->prepare = _derive_prepare(env,e) ;
    //printf("res = %s\n", _th_print_exp(e->prepare));
    //if (e->prepare != _ex_true && e->prepare != _ex_false &&
    //    (e->prepare->type!=EXP_APPL || e->prepare->u.appl.functor != INTERN_ORIENTED_RULE)) exit(1);
    return e->prepare;
}

int _th_applicable_rule(struct env *env, struct _ex_intern *rule, struct _ex_intern *e)
{
    if (rule->type != EXP_APPL || rule->u.appl.count != 3) return 0;
    //if (rule->u.appl.functor==INTERN_UNORIENTED_RULE) return 0 ;

    //fv = _th_get_free_vars_leave_marked(rule->u.appl.args[0],&c) ;
    //if (c > 0) {
        //rule = _ex_intern_quant(INTERN_ALL,c,fv,rule->u.appl.args[0],_ex_true) ;
    //} else {
        //rule = rule->u.appl.args[0] ;
    //}
    rule = rule->u.appl.args[0] ;
    return _th_smaller3(env,rule,e) || _th_equal(env,rule,e) ;
}

void _th_derive_add_prepared(struct env *env, struct _ex_intern *e)
{
    if (e==NULL) return ;

    _zone_print_exp("Derive prepared testing", e) ;

    if (e->u.appl.functor==INTERN_AND) {
        int i ;
        for (i = 0; i < e->u.appl.count; ++i) {
            _zone_print_exp("Testing", e->u.appl.args[i]) ;
            add_rule(env,e->u.appl.args[i]) ;
        }
    } else {
        add_rule(env,e) ;
    }
    _zone_print0("Done");
}

struct _ex_intern *_th_negate_term(struct env *env, struct _ex_intern *term)
{
    struct _ex_intern **args;
    unsigned f;
    int i;

    if (term->type==EXP_APPL && (term->u.appl.functor==INTERN_AND || term->u.appl.functor==INTERN_OR)) {
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * term->u.appl.count);
        for (i = 0; i < term->u.appl.count; ++i) {
            args[i] = _th_negate_term(env,term->u.appl.args[i]);
        }
        f = ((term->u.appl.functor==INTERN_AND)?INTERN_OR:INTERN_AND);
        return _ex_intern_appl_env(env,f,term->u.appl.count,args);
    }
    if (term->type==EXP_APPL && term->u.appl.functor==INTERN_NOT && term->u.appl.count==1) {
        return term->u.appl.args[0];
    }
    return _ex_intern_appl1_env(env,INTERN_NOT,term);
}

struct _ex_intern *invert_rule(struct env *env, struct _ex_intern *rule)
{
    if (rule->u.appl.functor==INTERN_ORIENTED_RULE && rule->u.appl.count==3 && 
        (rule->u.appl.args[0]->u.appl.functor==INTERN_AND ||
        rule->u.appl.args[0]->u.appl.functor==INTERN_OR
        ) &&
        (rule->u.appl.args[1]==_ex_true || rule->u.appl.args[1]==_ex_false) &&
        rule->u.appl.args[2]==_ex_true) {
        return _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,
            _th_negate_term(env,rule->u.appl.args[0]),
            ((rule->u.appl.args[1]==_ex_true)?_ex_false:_ex_true),
            _ex_true);
    }
    return NULL;
}

struct _ex_intern *fix_up_rule(struct env *env, struct _ex_intern *r)
{
    if (r->type==EXP_APPL && r->u.appl.count==2 && r->u.appl.functor==INTERN_PRIORITY) {
        struct _ex_intern *e = r->u.appl.args[1] ;
        if (e->u.appl.functor==INTERN_UNORIENTED_RULE && e->u.appl.count==3) {
            e = _ex_intern_appl2_env(env,INTERN_AND,_ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,_ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0],e->u.appl.args[1]),_ex_true,e->u.appl.args[2]),e) ;
        } else if ((e->u.appl.functor!=INTERN_ORIENTED_RULE && e->u.appl.functor != INTERN_FORCE_ORIENTED && e->u.appl.functor!=INTERN_UNORIENTED_RULE && e->u.appl.functor!=INTERN_DOUBLE_ARROW && e->u.appl.functor!=INTERN_INFERENCE && e->u.appl.functor!=INTERN_MACRO_ARROW) ||
            e->u.appl.count!=3) {
            e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,e,_ex_true,_ex_true) ;
        }
        if (e==NULL) {
            r = NULL ;
        } else {
            r = _ex_intern_appl2_env(env,INTERN_PRIORITY,r->u.appl.args[0],e) ;
        }
    } else if (r->type==EXP_APPL && r->u.appl.functor==INTERN_EQUAL && r->u.appl.count==2) {
        if (_th_smaller(env,r->u.appl.args[1],r->u.appl.args[0])) {
            r = _ex_intern_appl2_env(env,INTERN_AND,
                _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,r,_ex_true,_ex_true),
                _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,r->u.appl.args[0],r->u.appl.args[1],_ex_true)) ;
        } else if (_th_smaller(env,r->u.appl.args[0],r->u.appl.args[1])) {
            r = _ex_intern_appl2_env(env,INTERN_AND,
                _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,r,_ex_true,_ex_true),
                _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,r->u.appl.args[1],r->u.appl.args[0],_ex_true)) ;
        }
    } else if (r->type==EXP_APPL && r->u.appl.functor==INTERN_UNORIENTED_RULE && r->u.appl.count==3) {
        r = _ex_intern_appl2_env(env,INTERN_AND,_ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,_ex_intern_appl2_env(env,INTERN_EQUAL,r->u.appl.args[0],r->u.appl.args[1]),_ex_true,r->u.appl.args[2]),r) ;
    } else if (r->type!=EXP_APPL || (r->u.appl.functor!=INTERN_ORIENTED_RULE && r->u.appl.functor != INTERN_FORCE_ORIENTED && r->u.appl.functor!=INTERN_UNORIENTED_RULE && r->u.appl.functor!=INTERN_DOUBLE_ARROW && r->u.appl.functor!=INTERN_INFERENCE && r->u.appl.functor!=INTERN_MACRO_ARROW) ||
        r->u.appl.count!=3) {
        r = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,r,_ex_true,_ex_true) ;
    }

    return _th_derive_simplify(env, r) ;
}

unsigned _derive_and_add(int internal, struct env *env, struct _ex_intern *rule, int priority, int base)
{
    int rule_count, check_count, possibility_count ;
    struct _ex_intern **possible_rewrites ;
    int i, j, k ;
    int res = 0 ;
    
    //printf("Adding rule %s with priority %d\n", _th_print_exp(rule), priority) ;

    _zone_print2("Adding %s with base %d", _th_print_exp(rule), base) ;

    if (rule==_ex_false||rule==_ex_true) return 0 ;
    
    if (rule->type==EXP_QUANT && rule->u.quant.quant==INTERN_ALL &&
        rule->u.quant.cond==_ex_true) {
        return _derive_and_add(internal, env,rule->u.quant.exp,priority,base) ;
    }
    
    if (rule->type==EXP_APPL && (rule->u.appl.functor==INTERN_AND || rule->u.appl.functor==INTERN_NC_AND)) {
        int base = 0 ;
        for (i = 0; i < rule->u.appl.count; ++i) {
            res = _derive_and_add(internal, env,rule->u.appl.args[i],priority, base) ;
            base = res ;
        }
        return res ;
    }
    
    if (rule->type==EXP_APPL && (rule->u.appl.functor==INTERN_USE_CONTEXT || rule->u.appl.functor==INTERN_APPLY_CONTEXT || rule->u.appl.functor==INTERN_IN_CONTEXT || rule->u.appl.functor==INTERN_MATCH || rule->u.appl.functor==INTERN_CHOOSE)) {
        return 0 ;
    }

    if (rule->type==EXP_APPL && rule->u.appl.functor==INTERN_PRIORITY && rule->u.appl.count==2 && rule->u.appl.args[0]->type==EXP_INTEGER) {
        return _derive_and_add(internal, env,rule->u.appl.args[1],rule->u.appl.args[0]->u.integer[1],base) ;
    }

    if (rule->type!=EXP_APPL || rule->u.appl.count!=3 || (rule->u.appl.functor!=INTERN_UNORIENTED_RULE && rule->u.appl.functor!=INTERN_ORIENTED_RULE &&
        rule->u.appl.functor!= INTERN_DOUBLE_ARROW && rule->u.appl.functor != INTERN_INFERENCE && rule->u.appl.functor!= INTERN_FORCE_ORIENTED && rule->u.appl.functor!= INTERN_MACRO_ARROW)) {
        if (rule->type==EXP_APPL && rule->u.appl.count==2 && rule->u.appl.functor==INTERN_EQUAL) {
            int l = _th_smaller(env,rule->u.appl.args[0],rule->u.appl.args[1]) ;
            int r = _th_smaller(env,rule->u.appl.args[1],rule->u.appl.args[0]) ;
            if (l && !r)
            {
                rule = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,rule->u.appl.args[1],rule->u.appl.args[0],_ex_true) ;
            }
            else if (r && !l)
            {
                rule = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,rule->u.appl.args[0],rule->u.appl.args[1],_ex_true) ;
            }
            else
            {
                rule = _ex_intern_appl3_env(env,INTERN_UNORIENTED_RULE,rule->u.appl.args[0],rule->u.appl.args[1],_ex_true) ;
            }
        } else {
            rule = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,rule,_ex_true,_ex_true) ;
        }
    }
    
    check_size(base+2) ;
    all_rules[base] = rule ;
    _zone_print_exp("_derive_and_add", rule);
    rule_count = base + 1;
    check_count = base;
    
    while (check_count < rule_count) {
        rule = all_rules[check_count++] ;
        arg_base += rule_count ;
        _th_derive_rewrite_rule(REWRITE_SPACE,env,rule) ;
        arg_base -= rule_count ;
        check_size(0) ;
        possibility_count = _th_possibility_count;
        possible_rewrites = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * possibility_count) ;
        for (i = 0; i < _th_possibility_count; ++i) {
            possible_rewrites[i] = _th_possible_rewrites[i] ;
        }
        for (i = 0; i < possibility_count; ++i) {
            struct _ex_intern *r = possible_rewrites[i] ;
            if (r->type==EXP_APPL && r->u.appl.functor==INTERN_AND) {
                for (j = 0; j < r->u.appl.count; ++j) {
                    struct _ex_intern *rr = r->u.appl.args[j] ;
                    arg_base += rule_count ;
                    if (internal) {
                        rr = _th_int_rewrite(env, rr, 1) ;
                    } else {
                        rr = _th_rewrite(env, rr) ;
                    }
                    arg_base -= rule_count ;
                    check_size(0) ;
                    for (k = 0; k < rule_count; ++k) {
                        if (_th_equal(env,all_rules[k], rr)) goto cont2 ;
                    }
                    check_size(rule_count+1) ;
                    all_rules[rule_count++] = rr ;
cont2: ;
                }
            } else {
                arg_base += rule_count ;
                if (internal) {
                    r = _th_int_rewrite(env, r, 1) ;
                } else {
                    r = _th_rewrite(env, r) ;
                }
                arg_base -= rule_count ;
                check_size(0) ;
                for (k = 0; k < rule_count; ++k) {
                    if (_th_equal(env,all_rules[k], r)) goto cont ;
                }
                check_size(rule_count+1) ;
                all_rules[rule_count++] = r ;
cont: ;
            }
        }
    }

#ifdef XX
    if (rule->u.appl.functor==INTERN_UNORIENTED_RULE) {
        struct _ex_intern *r ;
        r = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,rule,_ex_true,_ex_true) ;
        add_rule(env,r) ;
        if (rule->u.appl.args[2]==_ex_true) {
            r = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,
                    _ex_intern_appl2_env(env,INTERN_EQUAL,rule->u.appl.args[0],rule->u.appl.args[1]),
                    _ex_true,
                    _ex_true) ;
            add_rule(env,r) ;
        }
    }
#endif

    return rule_count ;
}

struct _ex_intern *_derive_prepare_detailed(struct env *env, struct _ex_intern *e)
{
    int count, i, j ;
    
	if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT &&
		e->u.appl.args[0]->type==EXP_APPL &&
		e->u.appl.args[0]->u.appl.functor==INTERN_NOT) {
		e = e->u.appl.args[0]->u.appl.args[0];
	}

    if (e==_ex_false||e==_ex_true) return NULL ;
    
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_AND) {
        struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = _derive_prepare_detailed(env,e->u.appl.args[i]) ;
        }
        return _th_flatten_top(env,_ex_intern_appl_env(env,INTERN_AND,e->u.appl.count,args)) ;
    }

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_PRIORITY && e->u.appl.count==2) {
        struct _ex_intern *f = _derive_prepare_detailed(env,e->u.appl.args[1]) ;
        return _ex_intern_appl2_env(env,INTERN_PRIORITY, e->u.appl.args[0], f) ;
    }
    
    if (e->type==EXP_QUANT && e->u.quant.quant==INTERN_ALL) return _derive_prepare_detailed(env,e->u.quant.exp) ;
    
    if (e->type != EXP_APPL || e->u.appl.count != 3 ||
        (e->u.appl.functor != INTERN_ORIENTED_RULE && e->u.appl.functor != INTERN_UNORIENTED_RULE &&
         e->u.appl.functor != INTERN_FORCE_ORIENTED)) {
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL && e->u.appl.count==2) {
            e = _ex_intern_appl3_env(env,INTERN_UNORIENTED_RULE,e->u.appl.args[0],e->u.appl.args[1],_ex_true) ;
        } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT && e->u.appl.count==1) {
            e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,e->u.appl.args[0],_ex_false,_ex_true) ;
        } else {
            e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,e,_ex_true,_ex_true) ;
        }
    }
    
    count = _derive_and_add(1, env, e, 0, 0) ;
    j = 0 ;
    
    for (i = 0; i < count; ++i) {
        _zone_print_exp("result rule", all_rules[j]) ;
        e = all_rules[j] = fix_up_rule(env,all_rules[i]) ;
        if (all_rules[j] != NULL) ++j ;
        if (e) {
            e = invert_rule(env,e);
            all_rules[j] = e;
            if (e) ++j;
        }
    }
    
    if (count==1) {
        e = all_rules[0] ;
    } else {
        e = _th_flatten_top(env,_ex_intern_appl_env(env,INTERN_AND,j,all_rules)) ;
    }
    
    return e ;
}

struct _ex_intern *_th_derive_prepare_detailed(struct env *env, struct _ex_intern *e)
{
    //struct _ex_intern *r ;
    e = _th_mark_vars(env,e) ;
    //x = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,e,_ex_true,_ex_true) ;

    return _derive_prepare_detailed(env,e) ;
    //if (r==x) return r ;
    //if (r && r->u.appl.functor==INTERN_AND) {
    //    for (i = 0; i < r->u.appl.count; ++i) {
    //        if (x==r->u.appl.args[i]) x = NULL ;
    //    }
    //}
    //if (r==NULL) return x ;
    //if (x==NULL) return r ;
    //return _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,r,x)) ;
}

int _th_derive_and_add(struct env *env, struct _ex_intern *e)
{
    int res, i ;
    int rule_count ;

    //struct _ex_intern *x;
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_PRIORITY)
    {
        // For now exit if the integer is too large.
        if (e->u.appl.args[0]->u.integer[0] != 1) {
            printf("Integer too large\n") ;
            exit(1);
        }
        rule_priority = (int)e->u.appl.args[0]->u.integer[1];
        e = e->u.appl.args[1];
    }

    //if (e->type==EXP_APPL && e->u.appl.count==3 &&
    //    (e->u.appl.functor==INTERN_ORIENTED_RULE ||
    //     e->u.appl.functor==INTERN_UNORIENTED_RULE ||
    //     e->u.appl.functor==INTERN_FORCE_ORIENTED ||
    //     e->u.appl.functor==INTERN_INFERENCE ||
    //     e->u.appl.functor==INTERN_MACRO_ARROW)) {
    //    x = NULL ;
    //} else {
    //    x = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,e,_ex_true,_ex_true) ;
    //}

    _zone_print_exp("Derive adding", e) ;
    _tree_indent() ;
    rule_count = _derive_and_add(1,env,e,0,0) ;
    res = 0 ;
    for (i = 0; i < rule_count; ++i) {
        struct _ex_intern *r = all_rules[i] ;
        _zone_print_exp("Trying add rule", r) ;
        if (r->type==EXP_APPL) {
            r = fix_up_rule(env,r) ;
            if (r != NULL) {
                //if (r==x) x = NULL ;
                res = (add_rule(env,r) || res) ;
                r = invert_rule(env,r);
                if (r) {
                    res = (add_rule(env,r) || res);
                }
            }
        }
    }
    //if (x) res = (add_rule(env,x) || res) ;
    _tree_undent() ;

    rule_priority = 0;

    return res ;
}

void _th_derive_and_add_property(int space, struct env *env, struct _ex_intern *e)
{
    int i ;
    int rule_count ;
    int priority = 0 ;
    //printf("Adding prop %s\n", _th_print_exp(e)) ;
    while (e->type==EXP_APPL && e->u.appl.functor==INTERN_PRIORITY && e->u.appl.count==2 &&
        e->u.appl.args[0]->type==EXP_INTEGER) {

        priority = e->u.appl.args[0]->u.integer[1] ;
        e = e->u.appl.args[1] ;
    }
    rule_count = _derive_and_add(0,env,e,0,0) ;
    for (i = 0; i < rule_count; ++i) {
        struct _ex_intern *r = all_rules[i] ;
        _zone_print_exp("Trying add rule", r) ;
        if (r->type==EXP_APPL) {
            e = r = fix_up_rule(env,r) ;
            if (priority != 0) {
                r = _ex_intern_appl2_env(env,INTERN_PRIORITY,_ex_intern_small_integer(priority),r) ;
            }
            if (r != NULL) {
                _th_add_property(env,r) ;
            }
            if (e) {
                e = invert_rule(env,e);
                if (e) {
                    _th_add_property(env,e);
                }
            }
        }
    }
}
