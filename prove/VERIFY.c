/*
 * verify.c
 *
 * A compiler that converts C code into the intermediate form of the
 * verification tool.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#include "globalsp.h"
#include "../rewlib/RewriteLog.h"

static int is_in_list(struct local_vars *lv, unsigned v)
{
    while (lv != NULL) {
        if (lv->name==v) return 1 ;
        lv = lv->next ;
    }
    return 0 ;
}

static int is_environment_rule(struct env *env, struct _ex_intern *e)
{
    int count ;

    _th_get_free_vars(e, &count) ;
    if (count != 0) return 0 ;
    return _th_all_symbols_smaller(env,e,INTERN_PRE) ;
}

static void print_assertions(struct env *env, struct _ex_intern *e)
{
    int has_normal = 0, has_environment = 0 ;

    _tree_indent() ;
    _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
    _tree_undent() ;
}

static struct _ex_intern *all_globalv(struct _ex_intern *e)
{
    unsigned vars[2] ;

    vars[0] = INTERN_GLOBAL ;
    vars[1] = INTERN_V ;

    return _ex_intern_quant(INTERN_ALL,2,vars,e,_ex_true) ;
}

static struct _ex_intern *renamev(struct env *env, struct _ex_intern *e, unsigned o, unsigned n)
{
    struct _ex_intern **args ;
    int i ;
    struct _ex_intern *f, *g ;

    switch (e->type) {
        case EXP_APPL:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
            if (e->u.appl.functor==o && e->u.appl.count==0) {
                return _ex_intern_appl_env(env,n,0,NULL) ;
            }
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = renamev(env,e->u.appl.args[i],o,n) ;
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args) ;
        case EXP_QUANT:
            f = renamev(env,e->u.quant.cond,o,n) ;
            g = renamev(env,e->u.quant.exp,o,n) ;
            return _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,e->u.quant.vars,g,f) ;
        case EXP_CASE:
            f = renamev(env,e->u.case_stmt.exp,o,n) ;
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.case_stmt.count * 2) ;
            for (i = 0; i < e->u.case_stmt.count*2; ++i) {
                args[i] = renamev(env,e->u.case_stmt.args[i],o,n) ;
            }
            return _ex_intern_case(f,e->u.case_stmt.count,args) ;
        default:
            return e ;
    }
}

static struct _ex_intern *env_rules ;

int test_post_block(struct env *env, struct _ex_intern *terms, unsigned state, unsigned stack, struct _ex_intern *e)
{
    //struct _ex_intern *terms2 = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,e,terms)) ;
    struct _ex_intern *res ;
    int i, fail ;
    char *mark ;
    int save_state ;

    terms = _th_log_rewrite(env,terms);
    _tree_print_exp("Rewriting", e);
    _zone_increment() ;
    res = _th_check_rewrite(e) ;
    if (res) {
        _tree_print_exp("From memory", res);
        return res==_ex_true ;
    }
    mark = _th_log_start_rewrite() ;

    _th_log_derive_push(env) ;

    _zone_print0("Adding context rules") ;
    _tree_indent() ;
    if (terms->type==EXP_APPL && terms->u.appl.functor==INTERN_AND) {
        for (i = 0; i < terms->u.appl.count; ++i) {
            _zone_print1("Original %s", _th_print_exp(terms->u.appl.args[i])) ;
            _th_log_derive_and_add(env, _th_derive_simplify(env,terms->u.appl.args[i])) ;
        }
    } else {
        _th_log_derive_and_add(env, _th_derive_simplify(env,terms)) ;
    }
    _tree_undent() ;

    e = renamev(env, e, INTERN_STATE, state) ;
    e = renamev(env, e, INTERN_STACK, stack) ;

    save_state = _th_check_state ;
    _th_check_state = 100 ;
    _th_test_mode = 1 ;
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_AND)
    {
        fail = 0;
        for (i = 0; i < e->u.appl.count; ++i) {
            res = _th_log_int_rewrite(env, e->u.appl.args[i], 1) ;
            _zone_print2("Result %d: %s", i, _th_print_exp(res)) ;
            fail = (fail || (res != _ex_true)) ;
        }
    }
    else
    {
        res = _th_log_int_rewrite(env, e, 1) ;
        _zone_print1("Result: %s", _th_print_exp(res)) ;
        fail = (res != _ex_true) ;
    }
    _th_test_mode = 0 ;
    _th_check_state = save_state ;

    _th_log_derive_pop(env) ;

    res = _th_log_finish_rewrite(mark, env, res) ;
    _tree_print_exp("Done", res);

    _th_set_rewrite(res) ;

    return !fail ;
}

int test_post_condition(struct env *env, struct _ex_intern *final_state, unsigned final_state_state, unsigned final_state_stack, struct _ex_intern *e)
{
    if (final_state->type==EXP_APPL && final_state->u.appl.functor==INTERN_NC_OR) {
        int i ;
        for (i = 0; i < final_state->u.appl.count; ++i) {
            if (!test_post_block(env, final_state->u.appl.args[i], final_state_state, final_state_stack, e)) return 0 ;
        }
        return 1 ;
    } else {
        return test_post_block(env, final_state, final_state_state, final_state_stack, e) ;
    }
}

void check_post_conditions(struct env *env, struct _ex_intern *final_state, unsigned final_state_state, unsigned final_state_stack, struct entry *list, struct entry *fun)
{
    struct entry *l = list ;
    struct _ex_intern *e ;
    unsigned name = _th_intern(fun->u.function.name) ;

    while(l != NULL) {
        switch (l->type) {

        case ENTRY_POSTCONDITION:
            if (l->u.cond.function==name) {
                e = l->u.cond.condition ;
                _tree_print_exp("Testing", e);
                _tree_indent() ;
                if (!test_post_condition(env, final_state, final_state_state, final_state_stack, e)) {
                    _tree_print0("*** FAILURE ***") ;
                }
                _tree_undent() ;
            }
            break ;
        }
        l = l->next ;
    }
}

struct flow_tree {
    struct flow_tree *next, *cond_next, *pred ;
    int pos ;
    int has_loop_back ;
    int flag ;
    int join_count, current_count ;
    int terminal, cond_terminal ;
    int traversed ;
    struct instruction *code ;
    struct _ex_intern *assertions ;
    unsigned state, stack ;
} ;

static struct instruction *find_next(struct instruction *code, struct instruction *current, int pos, int offset)
{
    while (offset > 0) {
        current = current->next ;
        --offset ;
    }
    if (offset < 0) {
        pos += offset ;
        while (pos--) {
            code = code->next ;
        }
        return code ;
    }
    return current ;
}

static struct flow_tree *find_node_n(struct flow_tree *t, int pos)
{
    struct flow_tree *r ;
    if (t==NULL || t->traversed) return NULL ;
    while (t != NULL && !t->traversed) {
        t->traversed = 1 ;
        if (t->pos==pos) {
            return t ;
        }
        r = find_node_n(t->cond_next, pos) ;
        if (r != NULL) {
            return r ;
        }
        t = t->next ;
    }
    return NULL ;
}

static void clear_traversed(struct flow_tree *t)
{
    while (t && t->traversed) {
        t->traversed = 0 ;
        clear_traversed(t->cond_next) ;
        t = t->next ;
    }
}

static struct flow_tree *find_node(struct flow_tree *t, int pos)
{
    struct flow_tree *ft = find_node_n(t, pos) ;
    clear_traversed(t) ;
    return ft ;
}

static int make_terminal ;
static struct flow_tree *build_flow_tree(int space, struct instruction *code, int pos, struct instruction *current, struct flow_tree *pred)
{
    struct flow_tree *p = pred, *n = NULL ;

    if (current==NULL) return NULL ;

    make_terminal = 0 ;

    while (p != NULL) {
        if (p->pos == pos) {
            p->has_loop_back = 1 ;
            make_terminal = 1 ;
            return p ;
        }
        //if (p->next != n) {
        //    n = find_node(n, pos) ;
        //    if (n != NULL) {
        //        make_terminal = 1 ;
        //        ++n->join_count ;
        //        return n ;
        //    }
        //}
        n = p ;
        p = p->pred ;
    }

    p = (struct flow_tree *)_th_alloc(space, sizeof(struct flow_tree)) ;
    p->pred = pred ;
    p->pos = pos ;
    p->has_loop_back = 0 ;
    p->code = current ;
    p->assertions = NULL ;
    p->flag = 0 ;
    p->next = p->cond_next = NULL ;
    p->terminal = p->cond_terminal = 0 ;
    p->join_count = 1 ;
    p->current_count = 0 ;
    p->traversed = 0 ;

    if (current->operation==IfZero) {
        p->next = build_flow_tree(space, code, pos+1, current->next, p) ;
        p->terminal = make_terminal ;
        p->cond_next = build_flow_tree(space, code, pos+1+current->u.arg, find_next(code, current->next, pos+1, current->u.arg), p) ;
        p->cond_terminal = make_terminal ;
    } else {

        p->cond_next = NULL ;

        if (current->operation==Jump) {
            p->next = build_flow_tree(space, code, pos+1+current->u.arg, find_next(code, current->next, pos+1, current->u.arg), p) ;
            p->terminal = make_terminal ;

        } else if (current->operation==Return) {

            p->next = NULL ;
            p->terminal = make_terminal ;

        } else {
            p->next = build_flow_tree(space, code, pos+1, current->next, p) ;
            p->terminal = make_terminal ;
        }

    }

    make_terminal = 0 ;
    return p ;
}

static int is_on_predecessor_list(struct flow_tree *t)
{
    struct flow_tree *p = t ;

    do {
        p = p->pred ;
        if (p==t) return 1 ;
    } while (p != NULL) ;
    return 0 ;
}

static int get_code_pos(struct instruction *code, struct flow_tree *current)
{
    int pos = 0 ;

    while (code != NULL && code != current->code) {
        code = code->next ;
        ++pos ;
    }
    return pos ;
}

static int is_member(struct env *env, struct _ex_intern *e, struct _ex_intern *al)
{
    int i ;

    for (i = 0; i < al->u.appl.count; ++i) {
        if (_th_equal(env,e,al->u.appl.args[i])) return 1 ;
    }
    return 0 ;
}

static void print_flow_tree(struct env *env, struct instruction *code, struct flow_tree *current)
{
    if (current == NULL) return ;

    if (current->flag) {
        _tree_undent() ;
        _tree_print1("Goto %d", get_code_pos(code, current)) ;
        _tree_indent() ;
        return ;
    }

    current->flag = 1 ;

    _tree_undent() ;
    print_assertions(env, current->assertions) ;
    _th_print_instruction(get_code_pos(code, current), current->code) ;
    _tree_indent() ;

    print_flow_tree(env, code, current->next) ;

    if (current->cond_next != NULL) {
        _tree_undent() ;
        _tree_print1("From %d", get_code_pos(code, current)) ;
        _tree_indent() ;
    }
    print_flow_tree(env, code, current->cond_next) ;
}

static int loop_next = 0 ;

static unsigned make_loop_var(int count)
{
    char l[15] ;
    sprintf(l, "loop%d", count) ;

    return _th_intern(l) ;
}

static unsigned new_loop_var(struct env *env)
{
    unsigned r = make_loop_var(loop_next++) ;

    _th_log_add_precedence(ENVIRONMENT_SPACE,env,r,INTERN_STATE) ;
    _th_log_add_precedence(ENVIRONMENT_SPACE,env,INTERN_PRE,r) ;

    return r ;
}

static unsigned make_state_var(int count)
{
    char l[15] ;
    sprintf(l, "statev%d", count) ;

    return _th_intern(l) ;
}

static unsigned last_var = 0 ;

static unsigned new_state_var(struct env *env)
{
    unsigned r = make_state_var(loop_next++) ;
    static unsigned prev_r = -1 ;

    if (prev_r != -1) {
        _th_log_add_precedence(ENVIRONMENT_SPACE,env,prev_r,r) ;
    }

    if (last_var) {
        _th_log_add_precedence(ENVIRONMENT_SPACE,env,last_var,r) ;
    }

    _th_log_add_precedence(ENVIRONMENT_SPACE,env,r,INTERN_STATE) ;
    _th_log_add_precedence(ENVIRONMENT_SPACE,env,INTERN_PRE,r) ;

    //e = _ex_intern_appl1_env(env,INTERN_VALID_STATE,_ex_intern_appl_env(env,r,0,NULL)) ;
    //_th_log_derive_and_add(env, _th_derive_simplify(env,e)) ;

    _th_reset_context() ;
    _th_clear_cache() ;

    prev_r = r ;
    last_var = r ;
    return r ;
}

static unsigned make_return_var(int count)
{
    char l[15] ;
    sprintf(l, "return%d", count) ;

    return _th_intern(l) ;
}

static unsigned new_return_var(struct env *env)
{
    unsigned r = make_return_var(loop_next++) ;

    if (last_var) {
        _th_log_add_precedence(ENVIRONMENT_SPACE,env,last_var,r) ;
    }

    _th_log_add_precedence(ENVIRONMENT_SPACE,env,r,INTERN_STATE) ;
    _th_log_add_precedence(ENVIRONMENT_SPACE,env,INTERN_PRE,r) ;

    last_var = r ;

    return r ;
}

static unsigned make_stack_var(int count)
{
    char l[15] ;
    sprintf(l, "stackv%d", count) ;

    return _th_intern(l) ;
}

static unsigned new_stack_var(struct env *env)
{
    unsigned r = make_stack_var(loop_next++) ;

    if (last_var) {
        _th_log_add_precedence(ENVIRONMENT_SPACE,env,last_var,r) ;
    }

    _th_log_add_precedence(ENVIRONMENT_SPACE,env,r,INTERN_STACK) ;
    _th_log_add_precedence(ENVIRONMENT_SPACE,env,INTERN_PRE,r) ;

    last_var = r ;

    return r ;
}

static int is_loop_var(unsigned token)
{
    char *n = _th_intern_decode(token) ;

    if (n[0] != 'l' || n[1] != 'o' || n[2] != 'o' || n[3] != 'p') return 0 ;
    n += 4 ;
    while (isdigit(*n)) ++n ;

    return *n==0 ;
}

static int loop_is_bad = 0 ;

static struct _ex_intern *build_pattern(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern **args ;
    unsigned *fv ;
    int count, i, j ;

    fv = _th_get_free_vars(e, &count) ;
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (count+1)) ;

    if (loop_next==0||loop_is_bad) {
        args[0] = _ex_intern_appl_env(env,INTERN_STACK,0,NULL) ;
    } else {
        args[0] = _ex_intern_appl_env(env,make_loop_var(loop_next-1),0,NULL) ;
    }
    j = 1 ;
    for (i = 0; i < count; ++i) {
        args[j++] = _ex_intern_var(fv[i]) ;
    }
    return _ex_intern_appl_env(env,INTERN_QUESTION_MARK,j,args) ;
}

static struct _ex_intern *build_stack_equation(struct env *env, unsigned stack, struct _ex_intern *cond, struct _ex_intern *e)
{
    struct _ex_intern *args[2], *args2[3] ;

    args[0] = _ex_intern_appl_env(env,stack,0,NULL) ;
    args[1] = _ex_intern_var(INTERN_V) ;
    args2[0] = _ex_intern_appl_env(env,INTERN_GETSTACK,2,args) ;
    args2[1] = e ;
    args2[2] = cond ;

    return _ex_intern_appl_env(env,INTERN_ORIENTED_RULE,3,args2) ;
}

static struct _ex_intern *build_stack_assignment(struct env *env, unsigned stack, int pos, struct _ex_intern *val)
{
    struct _ex_intern *args[2], *args2[3] ;

    args[0] = _ex_intern_appl_env(env,stack,0,NULL) ;
    args[1] = _ex_intern_small_integer(pos) ;
    args2[0] = _ex_intern_appl_env(env,INTERN_GETSTACK,2,args) ;
    args2[1] = val ;
    args2[2] = _ex_true ;

    return _ex_intern_appl_env(env,INTERN_UNORIENTED_RULE,3,args2) ;
}

static struct _ex_intern *build_cond_stack_assignment(struct env *env, unsigned stack, int pos, struct _ex_intern *val, struct _ex_intern *cond)
{
    struct _ex_intern *args[2], *args2[3] ;

    args[0] = _ex_intern_appl_env(env,stack,0,NULL) ;
    args[1] = _ex_intern_small_integer(pos) ;
    args2[0] = _ex_intern_appl_env(env,INTERN_GETSTACK,2,args) ;
    args2[1] = val ;
    args2[2] = cond ;

    return _ex_intern_appl_env(env,INTERN_UNORIENTED_RULE,3,args2) ;
}

static int is_binary_operation(int op)
{
    return op==INTERN_NAT_PLUS ||
           op==INTERN_NAT_MINUS ||
           op==INTERN_NAT_TIMES ||
           op==INTERN_NAT_DIVIDE ||
           op==INTERN_EQUAL ||
           op==INTERN_NAT_LESS ;
}

static int translate_operation(int op)
{
    switch (op) {
        case INTERN_CPLUS:   return INTERN_NAT_PLUS;   break ;
        case INTERN_CMINUS:  return INTERN_NAT_MINUS;  break ;
        case INTERN_CTIMES:  return INTERN_NAT_TIMES;  break ;
        case INTERN_CDIVIDE: return INTERN_NAT_DIVIDE; break ;
        default: return op ;
    }
}

static int get_stack_op(int x)
{
	return INTERN_GETSTACK ;
}

static int get_stack_type(int x)
{
	return INTERN_CINTDATUM ;
}

static void add_state_var_info(struct env *env)
{
    _th_log_add_precedence(ENVIRONMENT_SPACE,env,INTERN_STATE,INTERN_STACK) ;
    _th_log_add_max_precedence(ENVIRONMENT_SPACE,env,INTERN_STATE1) ;
    _th_log_add_precedence(ENVIRONMENT_SPACE,env,INTERN_STATE1,INTERN_STACK1) ;
}

static struct _ex_intern *ret_cond ;
static struct _ex_intern *check_for_rewrite_fix(struct env *env, struct _ex_intern *rule, struct _ex_intern *pat)
{
    char *m = _th_alloc_mark(REWRITE_SPACE) ;
    int i ;
    struct _ex_intern **args ;
    struct _ex_intern *cond ;

    if (_th_distance(env,pat,rule)==0) {
        ret_cond = _ex_true ;
        return rule ;
    }

    _zone_print0("Attempting to fix") ;
#ifndef FAST
    _th_pp_zone_print(env,INTERN_DEFAULT,200,rule) ;
#endif
    _tree_indent() ;
    /* Try a top level rewrite first */
    _th_cond_special_rewrite_rule(REWRITE_SPACE, env, rule, 0, NULL) ;
    _th_alloc_release(REWRITE_SPACE,m) ;
    for (i = 0; i < _th_possibility_count; ++i) {
        _zone_print_exp("Testing", _th_possible_rewrites[i]);
        _zone_print_exp("with condition", _th_possible_conditions[i]);
        if (_th_distance(env,pat,_th_possible_rewrites[i])==0 &&
            _th_distance(env,pat,_th_possible_conditions[i])==0) {
            ret_cond = _th_possible_conditions[i] ;
            cond = _th_possible_rewrites[i] ;
            _tree_undent() ;
#ifndef FAST
            _zone_print0("Fixed to") ;
            _th_pp_zone_print(env,INTERN_DEFAULT,200,cond) ;
            _zone_print0("With condition") ;
            _th_pp_zone_print(env,INTERN_DEFAULT,200,ret_cond) ;
#endif
            return cond ;
        }
    }

    /* Failure, if this is an APPL term then try fixing the subterms
     * individually
     */
    if (rule->type==EXP_APPL) {
        cond = _ex_true ;
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * rule->u.appl.count) ;
        for (i = 0; i < rule->u.appl.count; ++i) {
            args[i] = check_for_rewrite_fix(env,rule->u.appl.args[i],pat) ;
            if (args[i]==NULL) {
                _tree_undent() ;
                return NULL ;
            }
            cond = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,cond,ret_cond)) ;
        }
        ret_cond = cond ;
        cond = _ex_intern_appl_env(env,rule->u.appl.functor,rule->u.appl.count,args) ;
        _tree_undent() ;
#ifndef FAST
        _zone_print0("Fixed to") ;
        _th_pp_zone_print(env,INTERN_DEFAULT,200,cond) ;
        _zone_print0("With condition") ;
        _th_pp_zone_print(env,INTERN_DEFAULT,200,ret_cond) ;
#endif
        return cond ;
    }
    _tree_undent() ;
    return NULL ;
}

static struct _ex_intern *prepare(struct env *env, struct _ex_intern *rule)
{
    if (rule==_ex_false||rule==_ex_true) return NULL ;

    if (rule->type==EXP_QUANT && rule->u.quant.quant==INTERN_ALL &&
        rule->u.quant.cond==_ex_true) {
        return prepare(env,rule->u.quant.exp);
    }

    if (rule->type==EXP_APPL && rule->u.appl.count==2 &&
        rule->u.appl.functor==INTERN_EQUAL) {
        return _ex_intern_appl3_env(env,INTERN_UNORIENTED_RULE,rule->u.appl.args[0],rule->u.appl.args[1],_ex_true) ;
    }

    if (rule->type != EXP_APPL ||
        (rule->u.appl.functor != INTERN_ORIENTED_RULE && rule->u.appl.functor != INTERN_UNORIENTED_RULE)) {
        return _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,rule,_ex_true,_ex_true) ;
    }

    return rule ;
}

static struct _ex_intern *add_universal(struct _ex_intern *rule)
{
    int count ;
    unsigned *fv ;

    fv = _th_get_free_vars(rule, &count) ;
    if (count==0) return rule ;

    return _ex_intern_quant(INTERN_ALL,count,fv,rule,_ex_true) ;
}

static struct _ex_intern *all_but_modev(struct _ex_intern *rule)
{
    int count ;
    unsigned *fv ;
    int i ;

    fv = _th_get_free_vars(rule, &count) ;

    for (i = 0; i < count; ++i) {
        if (fv[i]==INTERN_MODE || fv[i]==INTERN_V) {
            fv[i] = fv[--count] ;
        }
    }

    return _ex_intern_quant(INTERN_ALL,count,fv,rule,_ex_true) ;
}

static struct _ex_intern *fix_rule(struct env *env, struct _ex_intern *rule, struct _ex_intern *pat)
{
    struct _ex_intern *l, *r, *c, *cond ;
    
    _zone_print0("fixing rule") ;
#ifndef FAST
    _th_pp_zone_print(env,INTERN_DEFAULT,200,rule) ;
#endif
    r = rule ;
    rule = prepare(env,rule) ;
    if (rule==NULL) return r ;

    if (rule->type != EXP_APPL || rule->u.appl.count < 3) return rule ;
    _tree_indent() ;
    l = check_for_rewrite_fix(env, rule->u.appl.args[0],pat) ;
    if (l != NULL) {
        _zone_print_exp("left fix", l);
        _zone_print_exp("ret_cond", ret_cond);
        cond = ret_cond ;
        r = check_for_rewrite_fix(env,rule->u.appl.args[1],pat) ;
        if (r != NULL) {
            _zone_print_exp("right fix", r);
            _zone_print_exp("ret_cond", ret_cond);
            cond = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,cond,ret_cond)) ;
            c = check_for_rewrite_fix(env,rule->u.appl.args[2],pat) ;
            if (c != NULL) {
                _zone_print_exp("cond fix", c);
                _zone_print_exp("ret_cond", ret_cond);
                _tree_undent() ;
                return add_universal(_ex_intern_appl3_env(env,rule->u.appl.functor,l,r,
                           _th_flatten_top(env,_ex_intern_appl3_env(env,INTERN_AND,cond,c,ret_cond)))) ;
            }
        }
    }

    _tree_undent() ;
    return NULL ;
}

static int check_assertion(struct env *env, struct _ex_intern *pre, struct _ex_intern *exp)
{
    //struct _ex_intern *pat ;
    struct _ex_intern *e ;
    char *mark ;

    _tree_print_exp("Checking", exp);
    _tree_indent() ;
    mark = _th_log_derive_push(env) ;
    _th_log_derive_and_add(env,pre) ;
    //pat = build_pattern(env,exp) ;
    //e = _th_normalize(env,pat,exp) ;
    _th_test_mode = 1 ;
    e = _th_log_rewrite(env,exp) ;
    _th_test_mode = 0 ;
    _th_log_derive_pop_release(env,mark) ;
    _tree_undent() ;
    _tree_print_exp("Result", e);
    return e == _ex_true ;
}

static struct _ex_intern *fix_ra(struct env *env, struct _ex_intern *rule, struct _ex_intern *pat)
{
    char *m = _th_alloc_mark(REWRITE_SPACE) ;
    int i ;
    struct _ex_intern *cond, *cond1 ;

    if (_th_equal(env,rule,pat)) return _ex_true ;

    _zone_print_exp("Attempting to fix", rule);
    _zone_print_exp("to", pat);
    _tree_indent() ;
    /* Try a top level rewrite first */
    _th_cond_special_rewrite_rule(REWRITE_SPACE, env, rule, 0, NULL) ;
    _th_alloc_release(REWRITE_SPACE,m) ;
    for (i = 0; i < _th_possibility_count; ++i) {
        //_zone_print_exp("Testing", _th_possible_rewrites[i]);
        //_zone_print_exp("with", _th_possible_conditions[i]);
        if (_th_equal(env,_th_possible_rewrites[i],pat)) {
            cond = _th_possible_conditions[i] ;
            _tree_undent() ;
            _zone_print_exp("Fixed with", cond);
            return cond ;
        }
    }

    /* Failure, if this is an APPL term then try fixing the subterms
     * individually
     */
    cond = _ex_true ;
    if (rule->type==EXP_APPL && pat->type==EXP_APPL &&
        rule->u.appl.functor==pat->u.appl.functor &&
        rule->u.appl.count==pat->u.appl.count) {
        for (i = 0; i < rule->u.appl.count; ++i) {
            cond1 = fix_ra(env,rule->u.appl.args[i],pat->u.appl.args[i]) ;
            if (cond1==NULL) {
                _tree_undent() ;
                return NULL ;
            }
            cond = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,cond,cond1)) ;
        }
    } else {
        _tree_undent() ;
        return NULL ;
    }
    _tree_undent() ;
    _zone_print_exp("Fixed to", cond);
    return cond ;
}

static struct _ex_intern *fix_rule_assertion(struct env *env, struct _ex_intern *pre, struct _ex_intern *exp)
{
    struct _ex_intern *e ;
    char *mark ;

    _tree_print_exp("fix rule assertion", exp);
    _tree_indent() ;
    mark = _th_log_derive_push(env) ;
    _th_log_derive_and_add(env,pre) ;
    e = _th_log_rewrite(env,exp->u.appl.args[0]) ;
    e = fix_ra(env,e,exp->u.appl.args[1]) ;
    if (e != NULL) {
        exp = _ex_intern_appl3_env(env,exp->u.appl.functor,
            exp->u.appl.args[0],
            exp->u.appl.args[1],
            _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,exp->u.appl.args[2],e))) ;
    } else {
        exp = NULL ;
    }
    _th_log_derive_pop_release(env,mark) ;
    _tree_undent() ;
    _tree_print_exp("Result", exp);
    return exp ;
}

struct fix_list {
    struct fix_list *next ;
    struct _ex_intern *exp ;
    struct _ex_intern *cond ;
} ;

static struct fix_list *apply_rule_exp(struct env *env, struct _ex_intern *exp, struct _ex_intern *rule)
{
    int i ;
    struct fix_list *l, *n ;
    struct _ex_intern *cond, *r ;
    struct match_return *mr ;

    if (rule->type != EXP_APPL || rule->u.appl.count != 3) return NULL ;

    _zone_print_exp("using rule", rule);
    _zone_print_exp("to modify expression", exp);
    _tree_indent() ;

    /* Try a top level match first */
    r = _th_augment_expression(env,rule,exp) ;
    mr = _th_match(env, r->u.appl.args[0], exp) ;
    l = NULL ;
    if (mr != NULL) {
        while (mr != NULL) {
            n = (struct fix_list *)_th_alloc(REWRITE_SPACE,sizeof(struct fix_list)) ;
            n->next = l ;
            l = n ;
            l->exp = _th_subst(env,mr->theta,rule->u.appl.args[1]) ;
            l->cond = _th_subst(env,mr->theta,rule->u.appl.args[2]) ;
            _zone_print_exp("top fix:", l->exp);
            _zone_print_exp("Condition:", l->cond);
            mr = mr->next ;
        }
    } else if (exp->type==EXP_APPL && exp->u.appl.count > 0) {
        struct fix_list **fa = (struct fix_list **)ALLOCA(sizeof(struct fix_list *) * exp->u.appl.count) ;
        struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count) ;
        struct fix_list **index = (struct fix_list **)ALLOCA(sizeof(struct fix_list * ) * exp->u.appl.count) ;
        for (i = 0; i < exp->u.appl.count; ++i) {
            index[i] = fa[i] = apply_rule_exp(env, exp->u.appl.args[i], rule) ;
        }
        l = NULL ;
        while (1) {
            cond = _ex_true ;
            for (i = 0; i < exp->u.appl.count; ++i) {
                args[i] = index[i]->exp ;
                cond = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,cond,index[i]->cond)) ;
            }
            n = (struct fix_list *)_th_alloc(REWRITE_SPACE, sizeof(struct fix_list)) ;
            n->next = l ;
            n->cond = cond ;
            n->exp = _ex_intern_appl_env(env,exp->u.appl.functor,exp->u.appl.count,args) ;
            _zone_print_exp("Fix:", n->exp);
            _zone_print_exp("Condition:", n->cond);
            l = n ;
            for (i = 0; i < exp->u.appl.count; ++i) {
                index[i] = index[i]->next ;
                if (index[i]==NULL) index[i]=fa[i] ;
                if (index[i]!=fa[i]) break ;
            }
            if (i==exp->u.appl.count) break ;
        }
    } else {
        l = (struct fix_list *)_th_alloc(REWRITE_SPACE,sizeof(struct fix_list)) ;
        l->next = NULL ;
        l->exp = exp ;
        l->cond = _ex_true ;
    }
    _tree_undent() ;
    return l ;
}

static int bad_term(struct _ex_intern *e)
{
    int i ;

    switch (e->type) {
        case EXP_QUANT:
            return bad_term(e->u.quant.exp) || bad_term(e->u.quant.cond) ;
        case EXP_APPL:
            if (e->u.appl.count==0 && (e->u.appl.functor==INTERN_STATE1 || e->u.appl.functor==INTERN_STACK1)) return 1 ;
            for (i = 0; i < e->u.appl.count; ++i) {
                if (bad_term(e->u.appl.args[i])) return 1 ;
            }
            return 0 ;
        default:
            return 0 ;
    }
}

static int bad_term_rule(struct _ex_intern *e)
{
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_ORIENTED_RULE) {
        return bad_term(e->u.appl.args[0]) ;
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_UNORIENTED_RULE) {
        return (bad_term(e->u.appl.args[0]) && !bad_term(e->u.appl.args[1])) ||
               (bad_term(e->u.appl.args[1]) && !bad_term(e->u.appl.args[0])) ;
    } else {
        return bad_term(e) ;
    }
}

static int cmp(const void *i1,const void *i2)
{
    return *((const int *)i2)-*((const int *)i1) ;
}

static struct _ex_intern *fix_condition(struct env *env, struct _ex_intern *rule)
{
    struct _ex_intern *cond = rule->u.appl.args[2] ;
    if (cond->type==EXP_APPL && cond->u.appl.functor==INTERN_NC_AND) {
        struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * cond->u.appl.count) ;
        int i, j ;
        for (i = 0, j = 0; i < cond->u.appl.count; ++i) {
            if (cond->u.appl.args[i] != _ex_true) {
                args[j++] = cond->u.appl.args[i] ;
            }
        }
        qsort(args,j,sizeof(struct _ex_intern *),cmp) ;
        cond = _ex_intern_appl_env(env,INTERN_NC_AND,j,args) ;
        return _ex_intern_appl3_env(env,rule->u.appl.functor,rule->u.appl.args[0],rule->u.appl.args[1],cond) ;
    } else {
        return rule ;
    }
}

static struct _ex_intern *special_reduce(int space, struct env *env, struct _ex_intern *r, struct _ex_intern *nl)
{
    struct fix_list *fl ;
    struct _ex_intern *n, *rule, *old_r ;
    char *mark ;
    int i ;
    
    _zone_print0("Reducing rule") ;
#ifndef FAST
    _th_pp_zone_print(env,INTERN_DEFAULT,80,r) ;
#endif
    _zone_print0("to") ;
    _tree_indent() ;
    
    r = prepare(env,r) ;
    
    old_r = NULL ;
    
    mark = _th_alloc_mark(REWRITE_SPACE) ;

    while (old_r != r) {
        old_r = r ;
        for (i = 0; i < nl->u.appl.count; ++i) {
            rule = nl->u.appl.args[i] ;
            rule = prepare(env,rule) ;
            
            if (r->u.appl.count != 3 || rule->u.appl.count != 3 ||
                (rule->u.appl.functor==INTERN_ORIENTED_RULE &&
                rule->u.appl.args[2]==_ex_true)
                ) {
                continue ;
                
            }
            if (!_th_smaller(env,rule->u.appl.args[1],rule->u.appl.args[0])) {
                if (_th_smaller(env,rule->u.appl.args[0],rule->u.appl.args[1])) {
                    struct _ex_intern *args[3] ;
                    args[0] = rule->u.appl.args[1] ;
                    args[1] = rule->u.appl.args[0] ;
                    args[2] = rule->u.appl.args[2] ;
                    rule = _ex_intern_appl_env(env,rule->u.appl.functor,3,args) ;
                } else {
                    continue ;
                }
            }
            //if (_th_all_symbols_smaller(env,r,INTERN_STATE1) &&
            //_th_all_symbols_smaller(env,rule,INTERN_STATE1)) {
            //_tree_undent() ;
            //return _ex_true ;
            //}
            fl = apply_rule_exp(env, r->u.appl.args[0], rule) ;
            if (fl==NULL || (fl->next == NULL && _th_equal(env,fl->exp,r->u.appl.args[0]))) fl = NULL ;
            
            while (fl != NULL) {
                if (!_th_equal(env,fl->exp,r->u.appl.args[0]) &&
                    !_th_equal(env,fl->exp,r->u.appl.args[1]) &&
                    _th_log_rewrite(env,fl->cond)==_ex_true) {
                    n = _ex_intern_appl3_env(env,r->u.appl.functor,
                        fl->exp,
                        r->u.appl.args[1],
                        r->u.appl.args[2]) ;
                    r = fix_condition(env,n) ;
                    //l = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,n,l)) ;
                    continue ;
                }
                fl = fl->next ;
            }
            
            fl = apply_rule_exp(env, r->u.appl.args[1], rule) ;
            
            if (fl==NULL || (fl->next == NULL && _th_equal(env,fl->exp,r->u.appl.args[0]))) fl = NULL ;
            
            while (fl != NULL) {
                if (!_th_equal(env,fl->exp,r->u.appl.args[1]) &&
                    !_th_equal(env,fl->exp,r->u.appl.args[0]) &&
                    _th_log_rewrite(env,fl->cond)==_ex_true) {
                    n = _ex_intern_appl3_env(env,r->u.appl.functor,
                        r->u.appl.args[0],
                        fl->exp,
                        r->u.appl.args[2]) ;
                    r = fix_condition(env,n) ;
                    continue ;
                    //l = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,n,l)) ;
                }
                fl = fl->next ;
            }
            
            fl = apply_rule_exp(env, r->u.appl.args[2], rule) ;
            
            if (fl==NULL || (fl->next == NULL && _th_equal(env,fl->exp,r->u.appl.args[2]))) fl = NULL ;
            
            while (fl != NULL) {
                //_zone_print1("Testing condition candidate %s", _th_print_exp(fl->exp)) ;
                if (!_th_equal(env,fl->exp,r->u.appl.args[2]) && _th_log_rewrite(env,fl->cond)==_ex_true) {
                    r = _ex_intern_appl3_env(env,r->u.appl.functor,
                        r->u.appl.args[0],
                        r->u.appl.args[1],
                        fl->exp) ;
                    continue ;
                    //l = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,n,l)) ;
                }
                fl = fl->next ;
            }
        }
        old_r = r ;
    }

    r = add_universal(r) ;
    _th_alloc_release(REWRITE_SPACE,mark) ;

    _tree_undent() ;

#ifndef FAST
    _th_pp_zone_print(env,INTERN_DEFAULT,80,r) ;
#endif

    return r ;
}

static struct _ex_intern *apply_rule(int space, struct env *env, struct _ex_intern *r, struct _ex_intern *rule)
{
    struct fix_list *fl ;
    struct _ex_intern *l, *n ;
    char *mark ;

    _zone_print0("Applying rules") ;
#ifndef FAST
    _th_pp_zone_print(env,INTERN_DEFAULT,80,r) ;
    _th_pp_zone_print(env,INTERN_DEFAULT,80,rule) ;
#endif
    _tree_indent() ;

    r = prepare(env,r) ;
    rule = prepare(env,rule) ;

    if (r->u.appl.count != 3 || rule->u.appl.count != 3 ||
        (rule->u.appl.functor==INTERN_ORIENTED_RULE &&
         rule->u.appl.args[2]==_ex_true)
        ) {
        _tree_undent() ;
        return _ex_true ;

    }
    if (_th_equal(env,r,rule)) {
        _tree_undent() ;
        return _ex_true ;
    }
    if (!_th_smaller(env,rule->u.appl.args[1],rule->u.appl.args[0])) {
        if (_th_smaller(env,rule->u.appl.args[0],rule->u.appl.args[1])) {
            struct _ex_intern *args[3] ;
            args[0] = rule->u.appl.args[1] ;
            args[1] = rule->u.appl.args[0] ;
            args[2] = rule->u.appl.args[2] ;
            rule = _ex_intern_appl_env(env,rule->u.appl.functor,3,args) ;
        } else {
            _tree_undent() ;
            return _ex_true ;
        }
    }
    if (rule->u.appl.args[2]==_ex_true) {
        _tree_undent() ;
        return _ex_true ;
    }
    if (_th_all_symbols_smaller(env,r,INTERN_STATE1) &&
        _th_all_symbols_smaller(env,rule,INTERN_STATE1)) {
        _tree_undent() ;
        return _ex_true ;
    }
    mark = _th_alloc_mark(REWRITE_SPACE) ;
    fl = apply_rule_exp(env, r->u.appl.args[0], rule) ;
    if (fl==NULL || (fl->next == NULL && _th_equal(env,fl->exp,r->u.appl.args[0]))) fl = NULL ;

    l = _ex_true ;
    while (fl != NULL) {
        if (!_th_equal(env,fl->exp,r->u.appl.args[0])) {
            n = _ex_intern_appl3_env(env,r->u.appl.functor,
                fl->exp,
                r->u.appl.args[1],
                _th_flatten_top(env, _ex_intern_appl2_env(env,INTERN_NC_AND,
                    fl->cond,
                    r->u.appl.args[2]))) ;
            n = fix_condition(env,n) ;
            n = add_universal(n) ;
            _th_alloc_release(REWRITE_SPACE,mark) ;
            _tree_undent() ;
            return n ;
            //l = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,n,l)) ;
        }
        fl = fl->next ;
    }

    fl = apply_rule_exp(env, r->u.appl.args[1], rule) ;
    
    if (fl==NULL || (fl->next == NULL && _th_equal(env,fl->exp,r->u.appl.args[0]))) fl = NULL ;
    
    while (fl != NULL) {
        if (!_th_equal(env,fl->exp,r->u.appl.args[1])) {
            n = _ex_intern_appl3_env(env,r->u.appl.functor,
                r->u.appl.args[0],
                fl->exp,
                _th_flatten_top(env, _ex_intern_appl2_env(env,INTERN_NC_AND,
                fl->cond,
                r->u.appl.args[2]))) ;
            n = fix_condition(env,n) ;
            n = add_universal(n) ;
            _th_alloc_release(REWRITE_SPACE,mark) ;
            _tree_undent() ;
            return n ;
            //l = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,n,l)) ;
        }
        fl = fl->next ;
    }
    
    if (l != _ex_true) {
        _tree_print_exp("combining", r);
        _tree_print_exp("and", rule);
        print_assertions(env,l) ;
    }

    _th_alloc_release(REWRITE_SPACE,mark) ;

    _tree_undent() ;
    return l ;
}

static struct _ex_intern *filter_list(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *nl = _ex_true ;
    int i ;

    if (e->type != EXP_APPL || e->u.appl.functor != INTERN_AND) {
        e = _ex_intern_appl1_env(env,INTERN_AND,e) ;
    }

    for (i = 0; i < e->u.appl.count; ++i) {
        _zone_print1("Testing %s", _th_print_exp(e->u.appl.args[i])) ;
        _tree_indent() ;
        if (!bad_term(e->u.appl.args[i])) {
            _zone_print0("good") ;
            nl = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,nl,e->u.appl.args[i])) ;
        } else {
            _zone_print0("bad") ;
        }
        _tree_undent() ;
    }
    //return _th_log_rewrite(env,nl) ;
    return nl;
}

struct fix_list *append_lists(struct fix_list *l1, struct fix_list *l2)
{
    struct fix_list *orig = l1 ;

    if (l1==NULL) return l2 ;
    while (l1->next != NULL) {
        l1 = l1->next ;
    }
    l1->next = l2 ;

    return orig ;
}

static struct _ex_intern *normalize_state(int space, struct env *env, struct _ex_intern *pre, unsigned state, unsigned stack)
{
#ifdef OLD_CODE
    struct _ex_intern *old, *nl, *res ;
    unsigned change = 1, i, j ;
    struct _ex_intern *e, *f ;
    char *mark = _th_alloc_mark(SEARCH_SPACE) ;
    char *mark2 = _th_alloc_mark(REWRITE_SPACE) ;

    _tree_print0("Result and normalization") ;
    _tree_indent() ;
    old = pre ;
    if (pre->type != EXP_APPL || pre->u.appl.functor != INTERN_AND) {
        pre = _ex_intern_appl1_env(env,INTERN_AND,pre) ;
    }
    nl = _th_log_rewrite(env,pre) ;
    _tree_print0("Original") ;
    print_assertions(env,nl) ;
    while (change) {
        struct _ex_intern **args ;
        _tree_print0("Cycle") ;
        _tree_indent() ;
        if (nl->type != EXP_APPL || nl->u.appl.functor != INTERN_AND) {
            nl = _ex_intern_appl1_env(env,INTERN_AND,nl) ;
        }
        f = nl ;
        _tree_print0("Combining") ;
        _zone_increment() ;
        _tree_indent() ;

        //_th_log_derive_push(env) ;
        //_th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,nl))) ;

        res = _th_and_elaborate(env,nl) ;
        _tree_print0("New terms") ;
        _th_pp_tree_print(env,INTERN_DEFAULT,80,res) ;
        //f = res ;
        nl = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,res,nl)) ;
        _tree_print0("Normalization") ;
        _th_pp_tree_print(env,INTERN_DEFAULT,80,nl) ;
        nl = _th_log_rewrite(env,nl) ;
        _tree_print0("Rewritten normalization") ;
        _th_pp_tree_print(env,INTERN_DEFAULT,80,nl) ;

        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * nl->u.appl.count) ;
        for (i = 0; i < nl->u.appl.count; ++i) {
            args[i] = nl->u.appl.args[i] ;
        }
        for (i = 0; i < nl->u.appl.count; ++i) {
            _th_and_push(env,args,nl->u.appl.count,-1) ;
            if (i > 0) {
                _th_and_push1(env,nl->u.appl.args,i,-1) ;
            }
            args[i] = special_reduce(SEARCH_SPACE,env,nl->u.appl.args[i],nl) ;
            _th_log_derive_pop(env) ;
        }
        f = _ex_intern_appl_env(env,INTERN_AND,nl->u.appl.count,args) ;

        _tree_undent() ;

        _tree_print0("Result") ;
        _th_pp_tree_print(env,INTERN_DEFAULT,80,f) ;

        _tree_print0("Combining") ;
        _tree_indent() ;
        for (i = 0; i < nl->u.appl.count; ++i) {
            if (bad_term_rule(nl->u.appl.args[i])) {
                for (j = 0; j < nl->u.appl.count; ++j) {
                    if (i != j) {
                        struct _ex_intern *g = apply_rule(SEARCH_SPACE,env,nl->u.appl.args[j],nl->u.appl.args[i]) ;
                        if (g != _ex_true) {
                            _tree_undent() ;
#ifndef FAST
                            _zone_print0("Adding term") ;
                            _th_pp_zone_print(env,INTERN_DEFAULT,80,g) ;
                            _zone_print0("Combining") ;
                            _tree_indent() ;
#endif
                            f = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,g,f)) ;
                        }
                    }
                }
            }
        }
        _tree_undent() ;

        //_th_log_derive_pop(env) ;

        _tree_print0("Result plus combines") ;
        _th_pp_tree_print(env,INTERN_DEFAULT,80,f) ;

        nl = _th_log_rewrite(env,f) ;
        _tree_undent() ;
        _tree_print0("Rewritten result") ;
        print_assertions(env,nl) ;
        change = !_th_equal(env,pre,nl) ;
        pre = nl ;
    }
    _th_alloc_release(SEARCH_SPACE,mark) ;
    _th_alloc_release(REWRITE_SPACE,mark2) ;
    _tree_print0("Filtering") ;
    pre = filter_list(env,pre) ;
    print_assertions(env,pre) ;
    _tree_undent() ;
    return pre ;
#else
    //struct _ex_intern *r = _th_log_rewrite(env,pre) ;
    //r = filter_list(env,r) ;
    //_tree_print0("Result") ;
    //_tree_print1("state %s", _th_intern_decode(state)) ;
    //_tree_print1("stack %s", _th_intern_decode(stack)) ;
    //_tree_indent() ;
    //_th_pp_tree_print(env,INTERN_DEFAULT,200,r) ;
    //_tree_undent() ;
    //return r ;
    return pre ;
#endif
}

struct _ex_intern *add_assertions(struct env *env, struct _ex_intern *e, struct _ex_intern *assertions)
{
    int i ;
    char *mark;
    struct _ex_intern *res;
    struct _ex_intern *adds = assertions;

    _zone_print0("Adding assertions") ;
    _zone_increment() ;
    res = _th_check_rewrite(_ex_intern_appl2_env(env,INTERN_TUPLE,e,assertions)) ;
    if (res) {
        _tree_print_exp("From memory", res);
        _tree_print0("Adding") ;
        _tree_indent() ;
        if (adds->type==EXP_APPL && adds->u.appl.functor==INTERN_AND) {
            for (i = 0; i < adds->u.appl.count; ++i) {
                _tree_print_exp("", adds->u.appl.args[i]) ;
            }
        } else {
            _tree_print_exp("", adds) ;
        }
        _tree_undent() ;
        _tree_print0("New equations") ;
        _tree_indent() ;
        if (res->type==EXP_APPL && res->u.appl.functor==INTERN_AND) {
            for (i = 0; i < res->u.appl.count; ++i) {
                _tree_print_exp("", res->u.appl.args[i]) ;
            }
        } else {
            _tree_print_exp("", res) ;
        }
        _tree_undent() ;
        return res ;
    }
    mark = _th_log_start_rewrite() ;
    _tree_indent() ;
    _zone_print0("Background") ;
    _tree_indent() ;
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_AND) {
        for (i = 0; i < e->u.appl.count; ++i) {
            _zone_print_exp("", e->u.appl.args[i]) ;
        }
    } else {
        _zone_print1("%s", _th_print_exp(e)) ;
    }
    _tree_undent() ;
    _zone_print0("New assertions before") ;
    _tree_indent() ;
    if (assertions->type==EXP_APPL && assertions->u.appl.functor==INTERN_AND) {
        for (i = 0; i < assertions->u.appl.count; ++i) {
            _zone_print1("%s", _th_print_exp(assertions->u.appl.args[i])) ;
        }
    } else {
        _zone_print1("%s", _th_print_exp(assertions)) ;
    }
    _tree_undent() ;
    _zone_print0("Derives") ;
    _tree_indent() ;
    _th_log_derive_push(env) ;
    _zone_print0("Adding derives") ;
    _tree_indent() ;
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_AND) {
        for (i = 0; i < e->u.appl.count; ++i) {
            _th_log_derive_and_add(env, _th_derive_simplify(env,e->u.appl.args[i])) ;
        }
    } else {
        _th_log_derive_and_add(env, _th_derive_simplify(env,e)) ;
    }
    _tree_undent() ;
    //_th_do_context_rewrites = 0 ;
    assertions = _th_log_int_rewrite(env, assertions, 0) ;
    //_th_do_context_rewrites = 1 ;
    _zone_print0("New assertions after rewrite") ;
    _tree_indent() ;
    if (assertions->type==EXP_APPL && assertions->u.appl.functor==INTERN_AND) {
        for (i = 0; i < assertions->u.appl.count; ++i) {
            _zone_print1("%s", _th_print_exp(assertions->u.appl.args[i])) ;
        }
    } else {
        _zone_print1("%s", _th_print_exp(assertions)) ;
    }
    _tree_undent() ;
    _zone_print0("Augmenting") ;
    assertions = _th_augment(env, assertions) ;
    _th_log_derive_pop(env) ;
    _tree_undent() ;

    _zone_print0("New assertions after") ;
    _tree_indent() ;
    if (assertions->type==EXP_APPL && assertions->u.appl.functor==INTERN_AND) {
        for (i = 0; i < assertions->u.appl.count; ++i) {
            _zone_print1("%s", _th_print_exp(assertions->u.appl.args[i])) ;
        }
    } else {
        _zone_print1("%s", _th_print_exp(assertions)) ;
    }

    _tree_undent() ;
    _tree_undent() ;

    assertions = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,e,assertions));

    assertions = _th_log_finish_rewrite(mark, env, assertions) ;
    _th_set_rewrite(assertions) ;

    _tree_print0("Adding") ;
    _tree_indent() ;
    if (adds->type==EXP_APPL && adds->u.appl.functor==INTERN_AND) {
        for (i = 0; i < adds->u.appl.count; ++i) {
            _tree_print_exp("", adds->u.appl.args[i]) ;
        }
    } else {
        _tree_print_exp("", adds) ;
    }
    _tree_undent() ;
    _tree_print0("New equations") ;
    _tree_indent() ;
    if (assertions->type==EXP_APPL && assertions->u.appl.functor==INTERN_AND) {
        for (i = 0; i < assertions->u.appl.count; ++i) {
            _tree_print_exp("", assertions->u.appl.args[i]) ;
        }
    } else {
        _tree_print_exp("", assertions) ;
    }
    _tree_undent() ;

    return assertions;
}

static struct _ex_intern *create_assertions(int space, struct env *env, struct entry *list, struct entry *fun)
{
    struct entry *l ;
    struct _ex_intern *al, *e ;
    struct local_vars *lv ;
    struct _ex_intern *args[3], *args2[3] ;
    unsigned name = _th_intern(fun->u.function.name) ;

    _tree_print0("Environment rules") ;
    _tree_indent() ;

    args2[2] = _ex_true ;
    l = list ;
    al = _ex_true ;

#ifdef XX
    info = _th_name_space->records ;
    while (info != NULL) {
        field = info->field ;
        while(field != NULL) {
            struct _ex_intern *name = _ex_intern_appl2_env(env,INTERN_CONS,
                                          _ex_intern_appl1_env(env,INTERN_CNAME,
                                              _ex_intern_string(_th_intern_decode(info->name))),
                                          _ex_intern_appl_env(env,INTERN_NIL,0,NULL)) ;
            e = _ex_intern_appl2_env(env,INTERN_FIELD,
                name,
                _ex_intern_string(_th_intern_decode(field->name))) ;
            _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
            _th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,e))) ;
            e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,
                    _ex_intern_appl2_env(env,INTERN_FIELD_TYPE,
                        name,
                        _ex_intern_string(_th_intern_decode(field->name))),
                    field->type,
                    _ex_true) ;
            _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
            _th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,e))) ;
            e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,
                    _ex_intern_appl2_env(env,INTERN_FIELD_NUM,
                        name,
                        _ex_intern_string(_th_intern_decode(field->name))),
                    _ex_intern_small_integer(field->ref_num),
                    _ex_true) ;
            _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
            _th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,e))) ;
            field = field->next ;
        }
        info = info->next ;
    }
#endif

    e = _ex_intern_appl1_env(env,INTERN_VALID_STATE,_ex_intern_appl_env(env,INTERN_PRE,0,NULL)) ;
    _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
    //_th_log_derive_and_add(env, _th_derive_simplify(env,e)) ;
    al = add_assertions(env,al,e);

    e = _ex_intern_appl1_env(env,INTERN_IMPORTANT_STATE,_ex_intern_appl_env(env,INTERN_PRE,0,NULL)) ;
    _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
    //_th_log_derive_and_add(env, _th_derive_simplify(env,e)) ;
    al = add_assertions(env,al,e);

    e = _ex_intern_appl1_env(env,INTERN_VALID_STATE,_ex_intern_appl_env(env,INTERN_STATE,0,NULL)) ;
    _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
    //_th_log_derive_and_add(env, _th_derive_simplify(env,e)) ;
    al = add_assertions(env,al,e);

    e = _ex_intern_appl1_env(env,INTERN_IMPORTANT_STATE,_ex_intern_appl_env(env,INTERN_STATE,0,NULL)) ;
    _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
    //_th_log_derive_and_add(env, _th_derive_simplify(env,e)) ;
    al = add_assertions(env,al,e);

    e = _ex_intern_appl1_env(env,INTERN_VALID_STATE,_ex_intern_appl_env(env,INTERN_STATE1,0,NULL)) ;
    _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
    //_th_log_derive_and_add(env, _th_derive_simplify(env,e)) ;
    al = add_assertions(env,al,e);

    while(l != NULL) {
        switch (l->type) {

#ifdef XX
        case ENTRY_GLOBAL_VARIABLE:
            args[0] = _ex_intern_string(_th_intern_decode(l->u.global_var.var)) ;
            args2[0] = _ex_intern_appl(INTERN_GLOBAL,1,args) ;
            args2[1] = _ex_true ;
            e = _ex_intern_appl(INTERN_ORIENTED_RULE,3,args2) ;
            _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
            _th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,e))) ;
            args2[0] = _ex_intern_appl(INTERN_GETGLOBALTYPE,1,args) ;
            args2[1] = l->u.global_var.type ;
            e = _ex_intern_appl(INTERN_ORIENTED_RULE,3,args2) ;
            _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
            _th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,e))) ;
            break ;
#endif
        case ENTRY_PRECONDITION:
            if (l->u.cond.function==name) {
                e = renamev(env,l->u.cond.condition,INTERN_STATE,INTERN_PRE) ;
                al = add_assertions(env,al,e);
                //al = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,al,e)) ;
            }
            break ;
        }
        l = l->next ;
    }

    lv = fun->u.function.local_vars ;
    while(lv != NULL) {
        args[0] = _ex_intern_string(_th_intern_decode(lv->name)) ;
        args[1] = _ex_intern_small_integer(0) ;
        args2[0] = _ex_intern_appl(INTERN_LOCAL,2,args) ;
        args2[1] = _ex_true ;
        e = _ex_intern_appl(INTERN_ORIENTED_RULE,3,args2) ;
        _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
        _th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,e))) ;
        args2[0] = _ex_intern_appl(INTERN_GETTYPE,2,args) ;
        args2[1] = lv->type ;
        e = _ex_intern_appl(INTERN_ORIENTED_RULE,3,args2) ;
        _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
        _th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,e))) ;
        lv = lv->next ;
    }

    //env_rules = _th_log_rewrite(env,al) ;

    //e = all_globalv(_ex_intern_appl3_env(env,
    //       INTERN_ORIENTED_RULE,
    //       _ex_intern_appl3_env(env,
    //           INTERN_GETVAL,
    //           _ex_intern_appl_env(env,INTERN_STATE,0,NULL),
    //           _ex_intern_var(INTERN_GLOBAL),
    //           _ex_intern_var(INTERN_V)),
    //       _ex_intern_appl3_env(env,
    //           INTERN_GETVAL,
    //           _ex_intern_appl_env(env,INTERN_PRE,0,NULL),
    //           _ex_intern_var(INTERN_GLOBAL),
    //           _ex_intern_var(INTERN_V)),
    //       _ex_true)) ;
    //al = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,al,e)) ;

    _tree_undent() ;

    return al ;
}

#define add_assertion(env,e,a) _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,e,a))

static struct _ex_intern *all_modev(struct _ex_intern *e)
{
    unsigned vars[2] ;

    vars[0] = INTERN_MODE ;
    vars[1] = INTERN_V ;

    return _ex_intern_quant(INTERN_ALL,2,vars,e,_ex_true) ;
}

static struct _ex_intern *all_v(struct _ex_intern *e)
{
    unsigned vars[1] ;

    vars[0] = INTERN_V ;

    return _ex_intern_quant(INTERN_ALL,1,vars,e,_ex_true) ;
}

static struct _ex_intern *all(struct _ex_intern *e)
{
    int count ;
    unsigned *vars = _th_get_free_vars(e, &count) ;

    return _ex_intern_quant(INTERN_ALL,count,vars,e,_ex_true) ;
}

static struct _ex_intern *inst_c(struct env *env, struct _ex_intern *state, struct _ex_intern *stack, struct _ex_intern *e, int count, struct cparameter *parameters, int pcount)
{
    struct _ex_intern **args ;
    int i ;
    struct _ex_intern *f, *g ;

    switch (e->type) {
        case EXP_APPL:
            printf("Testing %s\n", _th_print_exp(e)) ;
            printf("State = %s\n", _th_print_exp(state)) ;
            fflush(stdout);
            if (e->u.appl.functor==INTERN_GETVAL && e->u.appl.args[1]->type==EXP_APPL &&
                e->u.appl.args[1]->u.appl.functor==INTERN_LOCAL_LOC &&
                e->u.appl.args[0]==state) {
                struct _ex_intern *f = e->u.appl.args[1] ;
                int i ;
                printf("Testing replacement of %s\n", _th_print_exp(f)) ;
                fflush(stdout);
                for (i = 0; i < count; ++i) {
                    //struct _ex_intern *stack ;
                    //if (state->u.appl.functor==INTERN_STATE) {
                        //stack = stackpre ;
                    //} else {
                        //stack = _ex_intern_appl_env(env,INTERN_STACK1,0,NULL) ;
                    //}
                    if (f->u.appl.args[0]->type==EXP_STRING && _th_intern(f->u.appl.args[0]->u.string)==(int)parameters[i].name) {
                        return _ex_intern_appl2_env(env,INTERN_GETSTACK,stack,_ex_intern_small_integer(pcount-i-1)) ;
                    }
                }
            }
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = inst_c(env,state,stack,e->u.appl.args[i],count,parameters,pcount) ;
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args) ;
        case EXP_QUANT:
            f = inst_c(env,state,stack,e->u.quant.cond,count,parameters,pcount) ;
            g = inst_c(env,state,stack,e->u.quant.exp,count,parameters,pcount) ;
            return _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,e->u.quant.vars,g,f) ;
        case EXP_CASE:
            f = inst_c(env,state,stack,e->u.case_stmt.exp,count,parameters,pcount) ;
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.case_stmt.count * 2) ;
            for (i = 0; i < e->u.case_stmt.count*2; ++i) {
                args[i] = inst_c(env,state,stack,e->u.case_stmt.args[i],count,parameters,pcount) ;
            }
            return _ex_intern_case(f,e->u.case_stmt.count,args) ;
        default:
            return e ;
    }
}

static struct _ex_intern *instantiate_condition(struct env *env, unsigned state, unsigned stack, struct _ex_intern *e, struct entry *list, unsigned fun, int pcount)
{
    while (list != NULL && ((list->type != ENTRY_FUNCTION && list->type != ENTRY_EXTERN_FUNCTION) || _th_intern(list->u.function.name) != (int)fun)) {
        if (list->type==ENTRY_FUNCTION || list->type == ENTRY_EXTERN_FUNCTION) {
            printf("Function: %s\n", list->u.function.name) ;
            fflush(stdout) ;
        }
        list = list->next ;
    }
    if (list==NULL) {
        printf("Cannot find function %s\n", _th_intern_decode(fun)) ;
        exit(1) ;
    }
    printf("function = %s\n", _th_intern_decode(fun));
    printf("Expression %s\n", _th_print_exp(e));
    fflush(stdout);
    return inst_c(env,_ex_intern_appl_env(env,state,0,NULL),_ex_intern_appl_env(env,stack,0,NULL),e,list->u.function.count,list->u.function.parameters,pcount) ;
}

static struct _ex_intern *instantiate_returns(struct env *env, struct _ex_intern *e, unsigned nrv)
{
    struct _ex_intern **args ;
    int i ;
    struct _ex_intern *f, *g ;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor==INTERN_RETURN && e->u.appl.count==0) {
                return _ex_intern_appl(nrv,0,NULL) ;
            }
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = instantiate_returns(env,e->u.appl.args[i],nrv) ;
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args) ;
        case EXP_QUANT:
            f = instantiate_returns(env,e->u.quant.cond,nrv) ;
            g = instantiate_returns(env,e->u.quant.exp,nrv) ;
            return _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,e->u.quant.vars,g,f) ;
        case EXP_CASE:
            f = instantiate_returns(env,e->u.case_stmt.exp,nrv) ;
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.case_stmt.count * 2) ;
            for (i = 0; i < e->u.case_stmt.count*2; ++i) {
                args[i] = instantiate_returns(env,e->u.case_stmt.args[i],nrv) ;
            }
            return _ex_intern_case(f,e->u.case_stmt.count,args) ;
        default:
            return e ;
    }
}

#ifdef XX
static struct _ex_intern *ret_state ;
static struct _ex_intern *get_transfer(struct _ex_intern *e)
{
    struct _ex_intern *l, *r ;

    if (e->type != EXP_QUANT) return NULL ;
    if (e->u.quant.quant != INTERN_ALL) return NULL ;
    if (e->u.quant.var_count != 2) return NULL ;
    if (e->u.quant.vars[0] != INTERN_V || e->u.quant.vars[0] != INTERN_MODE) return NULL ;
    if (e->u.quant.vars[1] != INTERN_V || e->u.quant.vars[1] != INTERN_MODE) return NULL ;
    if (e->u.quant.cond != _ex_true) return NULL ;

    e = e->u.quant.exp ;

    if (e->u.appl.args[0]->type != EXP_APPL ||
        e->u.appl.args[0]->u.appl.functor != INTERN_GETVAL ||
        e->u.appl.args[1]->type != EXP_APPL ||
        e->u.appl.args[1]->u.appl.functor != INTERN_GETVAL) return NULL ;

    l = e->u.appl.args[0] ;
    r = e->u.appl.args[1] ;

    if (l->u.appl.args[1]->type != INTERN_VAR ||
        l->u.appl.args[1]->u.var != INTERN_V ||
        l->u.appl.args[2]->type != INTERN_VAR ||
        l->u.appl.args[2]->u.var != INTERN_MODE ||
        r->u.appl.args[1]->type != INTERN_VAR ||
        r->u.appl.args[1]->u.var != INTERN_V ||
        r->u.appl.args[2]->type != INTERN_VAR ||
        r->u.appl.args[2]->u.var != INTERN_MODE) return NULL ;

    if (l->u.appl.args[0]->type == EXP_APPL &&
        l->u.appl.args[1]->u.appl.functor == INTERN_STATE) {
        ret_state = r->u.appl.args[0] ;
    } else if (r->u.appl.args[0]->type == EXP_APPL &&
               r->u.appl.args[1]->u.appl.functor == INTERN_STATE) {
        ret_state = l->u.appl.args[0] ;
    } else {
        return NULL ;
    }

    return e->u.appl.args[2] ;
}
#endif

static int test_term(struct env *env, struct _ex_intern *pat, struct _ex_intern *e, int state)
{
    char *mark ;
    int i;
    struct _ex_unifier *u ;

    if (pat->type==EXP_APPL && pat->u.appl.functor==INTERN_AND) {
        for (i = 0; i < e->u.appl.count; ++i) {
            if (!test_term(env,pat->u.appl.args[i],e,state)) return 0;
        }
        return 1;
    }

    if (pat->type==EXP_APPL && pat->u.appl.functor==INTERN_OR) {
        for (i = 0; i < e->u.appl.count; ++i) {
            if (test_term(env,pat->u.appl.args[i],e,state)) return 1;
        }
        return 0;
    }

    if (e->type==EXP_QUANT && pat->type==EXP_QUANT &&
        e->u.quant.quant==INTERN_ALL && pat->u.quant.quant==INTERN_ALL) {
        e = e->u.quant.exp ;
        pat = pat->u.quant.exp ;
    }

    if (e->type==EXP_APPL && pat->type==EXP_APPL &&
        e->u.appl.functor==INTERN_ORIENTED_RULE && pat->u.appl.functor==INTERN_UNORIENTED_RULE) {
        pat = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,pat->u.appl.args[0],pat->u.appl.args[1],pat->u.appl.args[2]) ;
    }

    mark = _th_alloc_mark(MATCH_SPACE) ;

    u = _th_new_unifier(MATCH_SPACE) ;
    u = _th_add_pair(MATCH_SPACE, u, INTERN_STATE, _ex_intern_appl_env(env,state,0,NULL)) ;
    pat = _th_subst(env,u,pat);
    if (_th_match(env,pat,e)) {
        //_tree_print1("Good match %s", _th_print_exp(pat)) ;
        //_tree_print1("and %s", _th_print_exp(e)) ;
        _th_alloc_release(MATCH_SPACE, mark) ;
        return 1 ;
    }

    _th_alloc_release(MATCH_SPACE, mark) ;
    return 0 ;
}

static void check_validity(unsigned new_state, unsigned old_state, struct env *env,struct _ex_intern *assertions)
{
    int i;
    struct state_checks *sc = _th_get_state_checks(env);

    while (sc != NULL) {
        _tree_print1("testing %s", sc->name) ;
        for (i = 0; i < assertions->u.appl.count; ++i) {
            if (test_term(env,sc->condition,assertions->u.appl.args[i],new_state)) goto cont;
        }
        printf("Validity check failure %s\n", sc->name) ;
        _tree_print1("Validity check failure %s", sc->name) ;
        exit(1) ;
cont:
        sc = sc->next ;
    }
}

static struct _ex_intern *build_successor_state(int space, struct env *env, unsigned fun, struct entry *list, struct _ex_intern *pre, struct instruction *code, int branch, int pos, unsigned *state, unsigned *stack, struct _ex_intern **invariant, unsigned *label)
{
    struct _ex_intern *e, *eq, *f, *e1, *e2, *e3 ;
    int stack_op ;
    struct entry *l ;
    unsigned old_stack = *stack ;
    unsigned old_state = *state ;
    unsigned nrv ;

    _th_print_instruction(pos, code) ;
    if (code->operation == IfZero) _tree_print1("Branch %d",branch) ;
    _tree_indent() ;
    _tree_print1("state = %s", _th_intern_decode(*state)) ;
    _tree_print1("stack = %s", _th_intern_decode(*stack)) ;
    switch (code->operation) {
        case Jump:
        case Noop:
            _tree_undent() ;
            return pre;
        case Invariant:
            *invariant = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,*invariant,code->u.exp)) ;
            _tree_undent() ;
            return pre ;
        case Label:
            *label = code->u.label ;
            _tree_undent() ;
            return pre ;
        case Return:
            eq = _ex_intern_appl2_env(env,INTERN_EQUAL,
                     _ex_intern_appl_env(env,INTERN_RETURN,0,NULL),
                     _ex_intern_appl2_env(env,INTERN_GETSTACK,_ex_intern_appl_env(env,*stack,0,NULL),_ex_intern_small_integer(0))) ;
            f = add_assertions(env,pre,eq) ;
            //_tree_print1("Adding %s", _th_print_exp(eq)) ;
            _tree_undent() ;
            return f ;
        case PushConstant:
            *stack = new_stack_var(env) ;
            _tree_print1("new stack %s", _th_intern_decode(*stack)) ;
            eq = _ex_intern_appl2_env(env,INTERN_GETSTACK,
                _ex_intern_appl_env(env,old_stack,0,NULL),
                _ex_intern_appl2_env(env,INTERN_NAT_MINUS,
                    _ex_intern_var(INTERN_V),
                    _ex_intern_small_integer(1))) ;
            eq = all_v(build_stack_equation(env, *stack, _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),_ex_intern_var(INTERN_V)), eq)) ;
            //f = add_assertions(env,pre,eq) ;
            //_tree_print1("Adding %s", _th_print_exp(eq)) ;
            eq = _ex_intern_appl2_env(env,INTERN_AND,eq,build_stack_assignment(env,*stack,0,renamev(env,code->u.exp,INTERN_STATE,*state))) ;
            f = add_assertions(env,pre,eq) ;
            //_tree_print1("Adding %s", _th_print_exp(eq)) ;
            _tree_undent() ;
            return f ;
        case PushCond:
            *stack = new_stack_var(env) ;
            _tree_print1("new stack %s", _th_intern_decode(*stack)) ;
            eq = _ex_intern_appl2_env(env,INTERN_GETSTACK,
                _ex_intern_appl_env(env,old_stack,0,NULL),
                _ex_intern_appl2_env(env,INTERN_NAT_PLUS,
                    _ex_intern_var(INTERN_V),
                    _ex_intern_small_integer(1))) ;
            eq = all_v(build_stack_equation(env, *stack, _ex_true, eq)) ;
            f = add_assertion(env,pre,eq) ;
            _tree_print_exp("Adding %s", eq) ;
            e1 = build_cond_stack_assignment(env,*stack,0,_ex_intern_small_integer(1),code->u.exp) ;
            f = add_assertion(env,f,eq) ;
            _tree_print_exp("Adding", eq);
            eq = _ex_intern_appl3_env(env,INTERN_AND,
                      eq,e1,
                      build_cond_stack_assignment(env,*stack,0,_ex_intern_small_integer(0),_ex_intern_appl_env(env,INTERN_NOT,1,&code->u.exp)));
            f = add_assertions(env,f,eq) ;
            //_tree_print_exp("Adding", eq);
            _tree_undent() ;
            return f ;
        case Pop:
            *stack = new_stack_var(env) ;
            _tree_print1("new stack %s", _th_intern_decode(*stack)) ;
            eq = _ex_intern_appl2_env(env,INTERN_GETSTACK,
                _ex_intern_appl_env(env,old_stack,0,NULL),
                _ex_intern_appl2_env(env,INTERN_NAT_PLUS,
                   _ex_intern_var(INTERN_V),
                   _ex_intern_small_integer(1))) ;
            e = _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(-1),_ex_intern_var(INTERN_V)) ;
            eq = all_v(build_stack_equation(env, *stack, e, eq)) ;
            f = add_assertion(env,pre,eq) ;
            _tree_undent() ;
            return f ;
        case JumpSub:
            nrv = new_return_var(env) ;
            *stack = new_stack_var(env) ;
            *state = new_state_var(env) ;
            pre = add_assertions(env,pre,_ex_intern_appl1_env(env,INTERN_VALID_STATE,_ex_intern_appl(*state,0,NULL))) ;
            _tree_print1("new state %s", _th_intern_decode(*state)) ;
            _tree_print1("new stack %s", _th_intern_decode(*stack)) ;
            if (code->u.jumpsub.count > 0) {
                eq = _ex_intern_appl2_env(env,INTERN_GETSTACK,
                    _ex_intern_appl_env(env,old_stack,0,NULL),
                    _ex_intern_appl2_env(env,INTERN_NAT_MINUS,
                        _ex_intern_var(INTERN_V),
                        _ex_intern_small_integer(code->u.jumpsub.count-1))) ;
                    e = _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(code->u.jumpsub.count-1),_ex_intern_var(INTERN_V)) ;
            } else {
                eq = _ex_intern_appl2_env(env,INTERN_GETSTACK,
                    _ex_intern_appl_env(env,old_stack,0,NULL),
                    _ex_intern_appl2_env(env,INTERN_NAT_PLUS,
                        _ex_intern_var(INTERN_V),
                        _ex_intern_small_integer(1))) ;
                e = _ex_true ;
            }
            e = _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(code->u.jumpsub.count-1),_ex_intern_var(INTERN_V)) ;
            e1 = all_v(build_stack_equation(env, *stack, e, eq)) ;
            //f = add_assertion(env,pre,eq) ;
            //_tree_print_exp("Adding", eq);
            e = _ex_true ;
            l = list ;
            while (l != NULL) {
                if (l->type==ENTRY_MODIFIES && l->u.cond.function==code->u.jumpsub.function) {
                    if (l->u.cond.condition==_ex_true) {
                        e = _th_flatten_top(env, _ex_intern_appl2_env(env,INTERN_NC_AND,
                                e,
                                _ex_intern_appl4_env(env,INTERN_DISJOINT,
                                    l->u.cond.variable,
                                    _ex_intern_var(INTERN_V),
                                    l->u.cond.type,
                                    _ex_intern_var(INTERN_MODE)))) ;
                    } else {
                        e = _th_flatten_top(env, _ex_intern_appl2_env(env,INTERN_NC_AND,
                                e,
                                _ex_intern_appl2_env(env,INTERN_OR,
                                    _ex_intern_appl4_env(env,INTERN_DISJOINT,
                                        l->u.cond.variable,
                                        _ex_intern_var(INTERN_V),
                                        l->u.cond.type,
                                        _ex_intern_var(INTERN_MODE)),
                                    _ex_intern_appl1_env(env,INTERN_NOT,l->u.cond.condition)))) ;
                    }
                }
                l = l->next ;
            }
            e = _th_flatten_top(env, _ex_intern_appl2_env(env,INTERN_NC_AND,
                    _ex_intern_appl1_env(env,INTERN_USE_CONTEXT,_ex_intern_string("disjoint")),
                    e)) ;
            e2 = all_modev(_ex_intern_appl3_env(env,INTERN_UNORIENTED_RULE,
                      _ex_intern_appl3_env(env,INTERN_GETVAL,
                          _ex_intern_appl_env(env,old_state,0,NULL),
                          _ex_intern_var(INTERN_V),
                          _ex_intern_var(INTERN_MODE)),
                      _ex_intern_appl3_env(env,INTERN_GETVAL,
                          _ex_intern_appl_env(env,*state,0,NULL),
                          _ex_intern_var(INTERN_V),
                          _ex_intern_var(INTERN_MODE)),
                      e)) ;
            //f = add_assertion(env,f,eq) ;
            //_tree_print_exp("Adding", eq);
            l = list ;
            f = _ex_true;
            while (l != NULL) {
                if (l->type==ENTRY_PRECONDITION && l->u.cond.function==code->u.jumpsub.function) {
                    eq = l->u.cond.condition ;
                    eq = renamev(env,eq,INTERN_STATE,old_state) ;
                    //eq = renamev(env,eq,INTERN_PRE,old_state) ;
                    eq = instantiate_condition(env, old_state, old_stack, eq, list, code->u.jumpsub.function, code->u.jumpsub.count) ;
                    eq = all(eq) ;
                    f = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,eq,f));
                    //f = add_assertion(env,f,eq) ;
                    //_tree_print_exp("Adding", eq);
                } else if (l->type==ENTRY_POSTCONDITION && l->u.cond.function==code->u.jumpsub.function) {
                    eq = l->u.cond.condition ;
                    eq = renamev(env,eq,INTERN_PRE, old_state) ;
                    eq = renamev(env,eq,INTERN_STATE, *state) ;
                    eq = instantiate_condition(env, old_state, old_stack, eq, list, code->u.jumpsub.function, code->u.jumpsub.count) ;
                    eq = instantiate_returns(env, eq, nrv) ;
                    eq = all(eq) ;
                    //f = add_assertion(env,f,eq) ;
                    f = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,eq,f));
                    //_tree_print_exp("Adding", eq);
                }
                l = l->next ;
            }
            eq = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,
                     _ex_intern_appl2_env(env, INTERN_GETSTACK,
                         _ex_intern_appl_env(env,*stack,0,NULL),
                         _ex_intern_small_integer(0)),
                     _ex_intern_appl_env(env,nrv,0,NULL),
                     _ex_true) ;
            eq = _th_flatten_top(env,_ex_intern_appl4_env(env,INTERN_AND,e1,e2,eq,f));
            f = add_assertions(env,pre,eq) ;
            //eq = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,
            //         _ex_intern_appl_env(env,INTERN_STATE,0,NULL),
            //         _ex_intern_appl_env(env,new_state_var(env),0,NULL),
            //         _ex_true) ;
            //f = add_assertion(env,f,eq) ;
            //_tree_print0("Done") ;
            _tree_undent() ;
            check_validity(*state,old_state,env,f);
            return f ;
        case Operation:
            if (is_binary_operation(code->u.arg)) {
                *stack = new_stack_var(env) ;
                _tree_print1("new stack %s", _th_intern_decode(*stack)) ;
                eq = _ex_intern_appl2_env(env,INTERN_GETSTACK,
                    _ex_intern_appl_env(env,old_stack,0,NULL),
                    _ex_intern_appl2_env(env,INTERN_NAT_PLUS,
                        _ex_intern_var(INTERN_V),
                        _ex_intern_small_integer(1))) ;
                e = _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),_ex_intern_var(INTERN_V)) ;
                e1 = all_v(build_stack_equation(env, *stack, e, eq)) ;
                //f = add_assertion(env,pre,eq) ;
                //_tree_print_exp("Adding", eq);
		stack_op = get_stack_op(code->u.arg) ;
                e = _ex_intern_appl2_env(env,code->u.arg,
                        _ex_intern_appl2_env(env,stack_op,
                            _ex_intern_appl_env(env,old_stack,0,NULL),
                            _ex_intern_small_integer(1)),
                        _ex_intern_appl2_env(env,stack_op,
                            _ex_intern_appl_env(env,old_stack,0,NULL),
                            _ex_intern_small_integer(0))) ;
                if (code->u.arg == INTERN_NAT_LESS || code->u.arg==INTERN_RAT_LESS ||
                    code->u.arg == INTERN_EQUAL) {
                    e2 = build_cond_stack_assignment(env,*stack,0,_ex_intern_small_integer(1),e) ;
                    //f = add_assertion(env,f,eq) ;
                    //_tree_print_exp("Adding", eq);
                    e3 = build_cond_stack_assignment(env,*stack,0,
                        _ex_intern_small_integer(0),
                        _ex_intern_appl_env(env,INTERN_NOT,1,&e)) ;
                    //f = add_assertion(env,f,eq) ;
                    //_tree_print_exp("Adding", eq);
                    eq = _ex_intern_appl2_env(env,INTERN_NC_OR,
                        _ex_intern_appl2_env(env,INTERN_EQUAL,
                            _ex_intern_appl2_env(env,INTERN_GETSTACK,
                                _ex_intern_appl_env(env,*stack,0,NULL),
                                _ex_intern_small_integer(0)),
                            _ex_intern_small_integer(0)),
                        _ex_intern_appl2_env(env,INTERN_EQUAL,
                            _ex_intern_appl2_env(env,INTERN_GETSTACK,
                                _ex_intern_appl_env(env,*stack,0,NULL),
                                _ex_intern_small_integer(0)),
                            _ex_intern_small_integer(1))) ;
                    //_tree_print_exp("Adding", eq);
                    eq = _ex_intern_appl4_env(env,INTERN_AND,e1,e2,e3,eq);
                    f = add_assertions(env,pre,eq) ;
                } else {
                    //e = _ex_intern_appl_env(env,get_stack_type(code->u.arg),1,&e) ;
                    eq = build_stack_assignment(env,*stack,0,e) ;
                    eq = _ex_intern_appl2_env(env,INTERN_AND,e1,eq);
                    f = add_assertions(env,pre,eq) ;
                    //_tree_print_exp("Adding", eq);
                }
                _tree_undent() ;
                return f ;
            } else if (code->u.arg == INTERN_POINTER_TO_NAT) {
                *stack = new_stack_var(env) ;
                _tree_print1("new stack %s", _th_intern_decode(*stack)) ;
                e1 = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,
                    _ex_intern_appl2_env(env,INTERN_GETSTACK,_ex_intern_appl_env(env,*stack,0,NULL),_ex_intern_small_integer(0)),
                    _ex_intern_appl1_env(env,INTERN_POINTER_TO_NAT,
                        _ex_intern_appl2_env(env,INTERN_GETSTACK,_ex_intern_appl_env(env,old_stack,0,NULL),_ex_intern_small_integer(0))),
                    _ex_true) ;
                //f = add_assertion(env,pre,eq) ;
                //_tree_print_exp("Adding", eq);
                eq = _ex_intern_appl2_env(env,INTERN_GETSTACK,
                    _ex_intern_appl_env(env,*stack,0,NULL),
                    _ex_intern_var(INTERN_V)) ;
                e = _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),_ex_intern_var(INTERN_V)) ;
                eq = all_v(build_stack_equation(env, old_stack, e, eq)) ;
                eq = _ex_intern_appl2_env(env,INTERN_AND,e1,eq) ;
                f = add_assertions(env,pre,eq) ;
                //_tree_print_exp("Adding", eq);
                _tree_undent() ;
                return f ;
            } else if (code->u.arg == INTERN_NAT_TO_POINTER) {
                *stack = new_stack_var(env) ;
                _tree_print1("new stack %s", _th_intern_decode(*stack)) ;
                e1 = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,
                    _ex_intern_appl2_env(env,INTERN_GETSTACK,_ex_intern_appl_env(env,*stack,0,NULL),_ex_intern_small_integer(0)),
                    _ex_intern_appl2_env(env,INTERN_NAT_TO_POINTER,
                        _ex_intern_appl2_env(env,INTERN_GETSTACK,_ex_intern_appl_env(env,old_stack,0,NULL),_ex_intern_small_integer(0)),
                        code->u.op.param),
                    _ex_true) ;
                //f = add_assertion(env,pre,eq) ;
                //_tree_print_exp("Adding", eq);
                eq = _ex_intern_appl2_env(env,INTERN_GETSTACK,
                    _ex_intern_appl_env(env,*stack,0,NULL),
                    _ex_intern_var(INTERN_V)) ;
                e = _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),_ex_intern_var(INTERN_V)) ;
                eq = all_v(build_stack_equation(env, old_stack, e, eq)) ;
                eq = _ex_intern_appl2_env(env,INTERN_AND,e1,eq);
                f = add_assertions(env,pre,eq) ;
                //_tree_print_exp("Adding", eq);
                _tree_undent() ;
                return f ;
            } else if (code->u.arg == INTERN_NOT) {
                *stack = new_stack_var(env) ;
                _tree_print1("new stack %s", _th_intern_decode(*stack)) ;
                eq = _ex_intern_appl2_env(env,INTERN_GETSTACK,
                    _ex_intern_appl_env(env,*stack,0,NULL),
                    _ex_intern_var(INTERN_V)) ;
                e = _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),_ex_intern_var(INTERN_V)) ;
                e1 = all_v(build_stack_equation(env, old_stack, e, eq)) ;
                //f = add_assertion(env,pre,eq) ;
                //_tree_print_exp("Adding", eq);
                e = _ex_intern_appl2_env(env, INTERN_EQUAL,
                        _ex_intern_appl2_env(env,INTERN_GETSTACK,
                            _ex_intern_appl_env(env,old_stack,0,NULL),
                            _ex_intern_small_integer(0)),
                        _ex_intern_small_integer(1)) ;
                e2 = build_cond_stack_assignment(env, *stack, 0,
                    _ex_intern_small_integer(0),
                    e
                    ) ;
                //f = add_assertion(env,f,eq) ;
                //_tree_print_exp("Adding", eq);
                e = _ex_intern_appl2_env(env, INTERN_EQUAL,
                        _ex_intern_appl2_env(env,INTERN_GETSTACK,
                            _ex_intern_appl_env(env,old_stack,0,NULL),
                            _ex_intern_small_integer(0)),
                        _ex_intern_small_integer(0)) ;
                e3 = build_cond_stack_assignment(env,*stack,0,
                    _ex_intern_small_integer(1),
                    e
                    ) ;
                //f = add_assertion(env,f,eq) ;
                //_tree_print_exp("Adding", eq);
                e = _ex_intern_appl2_env(env,INTERN_NC_OR,
                        _ex_intern_appl2_env(env,INTERN_EQUAL,
                            _ex_intern_appl2_env(env,INTERN_GETSTACK,_ex_intern_appl_env(env,old_stack,0,NULL),_ex_intern_small_integer(0)),
                            _ex_intern_small_integer(0)),
                        _ex_intern_appl2_env(env,INTERN_EQUAL,
                            _ex_intern_appl2_env(env,INTERN_GETSTACK,_ex_intern_appl_env(env,old_stack,0,NULL),_ex_intern_small_integer(0)),
                            _ex_intern_small_integer(1))) ;
                eq = _ex_intern_appl4_env(env,INTERN_AND,e1,e2,e3,e);
                f = add_assertions(env,pre,eq) ;
                //_tree_print_exp("Adding", e);
                _tree_undent() ;
                return f ;
            }
            _tree_undent() ;
            return pre ;
        case Load:
            *stack = new_stack_var(env) ;
            _tree_print1("new stack %s", _th_intern_decode(*stack)) ;
            e = _ex_intern_appl2_env(env,INTERN_NAT_LESS,
                    _ex_intern_small_integer(0),
                    _ex_intern_var(INTERN_V)) ;
            eq = _ex_intern_appl2_env(env,INTERN_GETSTACK,
                    _ex_intern_appl_env(env,*stack,0,NULL),
                    _ex_intern_var(INTERN_V)) ;
            eq = all_v(build_stack_equation(env, old_stack, e, eq)) ;
            //f = add_assertion(env,pre,eq) ;
            //_tree_print_exp("Adding", eq);
            e = _ex_intern_appl3_env(env,INTERN_GETVAL,
                    _ex_intern_appl_env(env,old_state,0,NULL),
                    _ex_intern_appl2_env(env,INTERN_GETSTACK,
                        _ex_intern_appl_env(env,old_stack,0,NULL),
                        _ex_intern_small_integer(0)),
                    code->u.exp) ;
            e = build_stack_assignment(env,*stack,0,e) ;
            eq = _ex_intern_appl2_env(env,INTERN_AND,eq,e) ;
            f = add_assertions(env,pre,eq) ;
            _tree_undent() ;
            return f ;
        case Store:
            *state = new_state_var(env) ;
            pre = add_assertions(env,pre,_ex_intern_appl1_env(env,INTERN_VALID_STATE,_ex_intern_appl(*state,0,NULL))) ;
            *stack = new_stack_var(env) ;
            _tree_print1("new stack %s", _th_intern_decode(*stack)) ;
            _tree_print1("new state %s", _th_intern_decode(*state)) ;
            e = _ex_intern_appl2_env(env,INTERN_GETSTACK,
                    _ex_intern_appl_env(env,old_stack,0,NULL),
                    _ex_intern_appl2_env(env,INTERN_NAT_PLUS,
                        _ex_intern_var(INTERN_V),
                        _ex_intern_small_integer(1))) ;
            eq = _ex_intern_appl2_env(env,INTERN_NAT_LESS,
                        _ex_intern_small_integer(0),
                        _ex_intern_var(INTERN_V)) ;
            e1 = all_v(build_stack_equation(env, *stack, eq, e)) ;
            //f = add_assertion(env,pre,eq) ;
            //_tree_print_exp("Adding", eq);
            e2 = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,
                        _ex_intern_appl2_env(env,INTERN_GETSTACK,
                            _ex_intern_appl_env(env,old_stack,0,NULL),
                            _ex_intern_small_integer(0)),
                        _ex_intern_appl2_env(env,INTERN_GETSTACK,
                            _ex_intern_appl_env(env,*stack,0,NULL),
                            _ex_intern_small_integer(0)),
                        _ex_true) ;
            //f = add_assertion(env,f,eq) ;
            //_tree_print_exp("Adding", eq);
            e = _ex_intern_appl2_env(env,INTERN_GETSTACK,
                      _ex_intern_appl_env(env,old_stack,0,NULL),
                      _ex_intern_small_integer(1)) ;
            e3 = all_modev(_ex_intern_appl3_env(env,INTERN_UNORIENTED_RULE,
                      _ex_intern_appl3_env(env,INTERN_GETVAL,
                          _ex_intern_appl_env(env,old_state,0,NULL),
                          _ex_intern_var(INTERN_V),
                          _ex_intern_var(INTERN_MODE)),
                      _ex_intern_appl3_env(env,INTERN_GETVAL,
                          _ex_intern_appl_env(env,*state,0,NULL),
                          _ex_intern_var(INTERN_V),
                          _ex_intern_var(INTERN_MODE)),
                      _ex_intern_appl2_env(env,INTERN_NC_AND,
                          _ex_intern_appl1_env(env,INTERN_USE_CONTEXT,_ex_intern_string("disjoint")),
                          _ex_intern_appl4_env(env,INTERN_DISJOINT,
                              e,
                              _ex_intern_var(INTERN_V),
                              code->u.exp,
                              _ex_intern_var(INTERN_MODE))))) ;
            //f = add_assertion(env,f,eq) ;
            //_tree_print_exp("Adding", eq);
            e = _ex_intern_appl3_env(env,INTERN_UNORIENTED_RULE,
                    _ex_intern_appl3_env(env,INTERN_GETVAL,
                        _ex_intern_appl_env(env,*state,0,NULL),
                        _ex_intern_appl2_env(env,INTERN_GETSTACK,
                            _ex_intern_appl_env(env,old_stack,0,NULL),
                            _ex_intern_small_integer(1)),
                        code->u.exp),
                    _ex_intern_appl2_env(env,INTERN_GETSTACK,
                        _ex_intern_appl_env(env,old_stack,0,NULL),
                        _ex_intern_small_integer(0)),
                    _ex_true) ;
            eq = _ex_intern_appl4_env(env,INTERN_AND,e1,e2,e3,e) ;
            f = add_assertions(env,pre,eq) ;
            //_tree_print_exp("Adding", e);
            _tree_undent() ;
            check_validity(*state,old_state,env,f);
            return f ;
        case IfZero:
            *stack = new_stack_var(env) ;
            _tree_print1("new stack %s", _th_intern_decode(*stack)) ;
            if (branch) {
                e1 = _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE,
                    _ex_intern_appl2_env(env, INTERN_GETSTACK,
                        _ex_intern_appl_env(env,old_stack,0,NULL),
                        _ex_intern_small_integer(0)),
                    _ex_intern_small_integer(0),
                        _ex_true) ;
            } else {
                e1 = _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE,
                    _ex_intern_appl2_env(env,INTERN_EQUAL,
                        _ex_intern_appl2_env(env, INTERN_GETSTACK,
                            _ex_intern_appl_env(env,old_stack,0,NULL),
                            _ex_intern_small_integer(0)),
                        _ex_intern_small_integer(0)),
                            _ex_false,
                            _ex_true) ;
            }
            //f = add_assertion(env,pre,e) ;
            //_tree_print_exp("Adding", e);
            eq = _ex_intern_appl2_env(env,INTERN_GETSTACK,
                _ex_intern_appl_env(env,*stack,0,NULL),
                _ex_intern_appl2_env(env,INTERN_NAT_MINUS,
                   _ex_intern_var(INTERN_V),
                   _ex_intern_small_integer(1))) ;
            e = _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),_ex_intern_var(INTERN_V)) ;
            eq = all_v(build_stack_equation(env, old_stack, e, eq)) ;
            eq = _ex_intern_appl2_env(env,INTERN_AND,eq,e1);
            f = add_assertions(env,pre,eq) ;
            f = _th_log_rewrite(env,f) ;
            //_tree_print_exp("Adding", eq);
            _tree_undent() ;
            return f ;
        default:
            _tree_undent() ;
            return pre;
    }
}

struct _ex_intern *final_state = NULL ;
unsigned final_state_stack ;
unsigned final_state_state ;

static struct _ex_intern *add_reduction(struct env *env, struct _ex_intern *e, unsigned state1, unsigned stack1, unsigned state2, unsigned stack2)
{
    struct _ex_intern *eq1, *eq2 ;

    eq1 = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,_ex_intern_appl_env(env,state1,0,NULL),_ex_intern_appl_env(env,state2,0,NULL),_ex_true) ;
    eq2 = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,_ex_intern_appl_env(env,stack1,0,NULL),_ex_intern_appl_env(env,stack2,0,NULL),_ex_true) ;

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NC_OR) {
        int i ;
        struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
        for (i = 0; i < e->u.appl.count; ++i) args[i] = add_reduction(env,e->u.appl.args[i],state1,stack1,state2,stack2) ;
        return _ex_intern_appl_env(env,INTERN_NC_OR,i,args) ;
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_AND) {
        int i ;
        struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (e->u.appl.count+2)) ;
        for (i = 0; i < e->u.appl.count; ++i) args[i] = e->u.appl.args[i] ;
        args[i++] = eq1 ;
        args[i++] = eq2 ;
        return _ex_intern_appl_env(env,INTERN_AND,i,args) ;
    } else {
        return _ex_intern_appl3_env(env,INTERN_AND,eq1,eq2,e) ;
    }
}

static struct _ex_intern *merge_assertions(struct env *env, struct _ex_intern *e, unsigned state1, unsigned stack1, struct _ex_intern *f, unsigned *state2, unsigned *stack2)
{
    if (e==NULL) {
        return f ;
    }
    if (f==NULL) {
        *state2 = state1 ;
        *stack2 = stack1 ;
        return e ;
    }
    _tree_print0("Merging assertions") ;
    print_assertions(env,e) ;
    _tree_print0("and") ;
    print_assertions(env,f) ;
    if (!_th_has_smaller_precedence(env,state1,*state2)) {
        f = add_reduction(env,f,*state2,*stack2,state1,stack1) ;
        *state2 = state1 ;
        *stack2 = stack1 ;
    } else {
        e = add_reduction(env,e,state1,stack1,*state2,*stack2) ;
    }
    e = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_NC_OR,e,f)) ;
    _tree_print1("state = %s", _th_intern_decode(*state2)) ;
    _tree_print1("stack = %s", _th_intern_decode(*stack2)) ;
    _tree_print0("Result") ;
    print_assertions(env,e) ;
    return e ;
}

struct _ex_intern *build_loop_initial(int space, int loopn, struct env *env, struct _ex_intern *e)
{
    return renamev(env,e,INTERN_STATE, make_loop_var(loopn)) ;
}

void clear_flow_tree(struct flow_tree *ft)
{
    ft->assertions = NULL ;
    if (ft->next != NULL && !ft->terminal) clear_flow_tree(ft->next) ;
    if (ft->cond_next != NULL && !ft->terminal) clear_flow_tree(ft->cond_next) ;
}

int reaches(struct flow_tree *ft, struct flow_tree *lb)
{
    int r = 0 ;
    if (ft==NULL) return 0 ;
    if (ft==lb) return 1 ;
    if (ft->next != NULL && !ft->terminal) r = reaches(ft->next,lb) ;
    if (r) return 1 ;
    if (ft->cond_next != NULL && !ft->terminal) r = reaches(ft->cond_next,lb) ;
    return r || lb==ft->next || lb==ft->cond_next ;

}

void mark_continue_points(struct flow_tree *lb, struct flow_tree *ft)
{
    if (reaches(ft->next,lb) || reaches(ft->cond_next,lb)) {
        ft->flag = 0 ;
        if (ft->next != NULL && !ft->terminal) mark_continue_points(lb,ft->next) ;
        if (ft->cond_next != NULL && !ft->cond_terminal) mark_continue_points(lb,ft->cond_next) ;
    } else {
        ft->flag = 1 ;
    }
}

void clear_continue_points(struct flow_tree *lb, struct flow_tree *ft)
{
    ft->flag = 0 ;
    if (ft->next != NULL && !ft->terminal) clear_continue_points(lb,ft->next) ;
    if (ft->cond_next != NULL && !ft->cond_terminal) clear_continue_points(lb,ft->cond_next) ;
}

struct fix_list *find_getvals(int space, struct _ex_intern *e, struct fix_list *al)
{
    int i ;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor==INTERN_GETVAL && e->u.appl.count==3) {
                struct fix_list *n = (struct fix_list *)_th_alloc(space,sizeof(struct fix_list)) ;
                n->next = al ;
                n->exp = e ;
                al = n ;
            }
            for (i = 0; i < e->u.appl.count; ++i) {
                al = find_getvals(space,e->u.appl.args[i],al) ;
            }
            break ;
        case EXP_QUANT:
            al = find_getvals(space,e->u.quant.cond,al) ;
            al = find_getvals(space,e->u.quant.exp,al) ;
            break ;
        case EXP_CASE:
            al = find_getvals(space,e->u.case_stmt.exp,al) ;
            for (i = 0; i < e->u.case_stmt.count*2; ++i) {
                al = find_getvals(space,e->u.case_stmt.args[i],al) ;
            }
            break ;
    }
    return al ;
}

struct _ex_intern *induce_rules(int space, int loopn, struct env *env,struct _ex_intern *pre, struct _ex_intern *cycle)
{
    struct fix_list *n, *al ;
    char *mark, *mark2 ;
    struct _ex_intern *e, *init, *loop, *f, *induce ;
    int i ;

    _zone_print0("Inducing invariants") ;
    _tree_indent() ;
    e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,
             _ex_intern_appl3_env(env,INTERN_GETVAL,
                 _ex_intern_appl_env(env,make_loop_var(loopn),0,NULL),
                 _ex_intern_var(INTERN_GLOBAL),
                 _ex_intern_var(INTERN_V)),
             _ex_intern_appl3_env(env,INTERN_GETVAL,
                 _ex_intern_appl_env(env,INTERN_STATE,0,NULL),
                 _ex_intern_var(INTERN_GLOBAL),
                 _ex_intern_var(INTERN_V)),
             _ex_true) ;
    e = fix_rule_assertion(env,cycle,e) ;
    if (e != NULL) {
        induce = add_universal(e) ;
    } else {
        induce = _ex_true ;
    }

    mark = _th_log_derive_push(env) ;
    _th_log_derive_and_add(env,pre) ;
    init = cycle ;
    if (init->type != EXP_APPL || init->u.appl.functor != INTERN_AND) {
        init = _ex_intern_appl1_env(env,INTERN_AND,cycle) ;
    }
    for (i = 0; i < init->u.appl.count; ++i) {
        _zone_print_exp("Testing", init->u.appl.args[i]);
        _tree_indent() ;
        e = _th_log_rewrite(env,init->u.appl.args[i]) ;
        if (_th_equal(env,e,_ex_true)) {
           induce = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,induce,init->u.appl.args[i])) ;
        }
        _tree_undent() ;
    }
    _th_log_derive_pop_release(env, mark) ;

    mark = _th_log_derive_push(env) ;
    loop = renamev(env,pre,INTERN_STATE,make_loop_var(loopn)) ;
    loop = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,loop,cycle)) ;
    loop = _th_log_rewrite(env,loop) ;
    _th_log_derive_and_add(env,loop) ;
    init = pre ;
    if (init->type != EXP_APPL || init->u.appl.functor != INTERN_AND) {
        init = _ex_intern_appl1_env(env,INTERN_AND,pre) ;
    }
    for (i = 0; i < init->u.appl.count; ++i) {
        _zone_print_exp("Testing2", init->u.appl.args[i]);
        _tree_indent() ;
        e = _th_log_rewrite(env,init->u.appl.args[i]) ;
        if (_th_equal(env,e,_ex_true)) {
           induce = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,induce,init->u.appl.args[i])) ;
        }
        _tree_undent() ;
    }
    _th_log_derive_pop_release(env, mark) ;

    mark2 = _th_alloc_mark(REWRITE_SPACE) ;
    n = find_getvals(REWRITE_SPACE,pre,NULL) ;
    al = n ;
    while (al != NULL) {
        _zone_print_exp("Inducing rule for", al->exp);
        _tree_indent() ;
        mark = _th_log_derive_push(env) ;
        e = renamev(env,pre,INTERN_STATE,INTERN_STATE1) ;
        e = _th_log_rewrite(env,e) ;
        _th_log_derive_and_add(env,e) ;
        init = _th_log_rewrite(env,renamev(env,al->exp,INTERN_STATE,INTERN_STATE1)) ;
        _th_log_derive_pop_release(env, mark) ;
        mark = _th_log_derive_push(env) ;
        e = renamev(env,cycle,INTERN_STATE,INTERN_STATE1) ;
        e = _th_log_rewrite(env,e) ;
        _th_log_derive_and_add(env,e) ;
        loop = _th_log_rewrite(env,renamev(env,al->exp,INTERN_STATE,INTERN_STATE1)) ;
        _th_log_derive_pop_release(env, mark) ;
        _tree_undent() ;
        _zone_print_exp("init", init);
        _zone_print_exp("loop", loop);
        _tree_indent() ;
        e = _ex_intern_appl3_env(env,INTERN_INDUCE,
                _ex_intern_appl3_env(env,INTERN_GETVAL,_ex_intern_appl(make_loop_var(loopn),0,NULL),al->exp->u.appl.args[1],al->exp->u.appl.args[2]),
                init,
                loop) ;
        _tree_undent() ;
        f = _th_log_rewrite(env,e) ;
        if (!_th_equal(env,e,f) && _th_all_symbols_smaller(env,f,INTERN_STATE1)) {
            _zone_print_exp("Adding induced rule", f);
            induce = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,induce,f)) ;
        }
        al = al->next ;
    }
    _th_alloc_release(REWRITE_SPACE,mark2) ;
    _tree_undent() ;

    return induce ;
}

struct cond_info {
    struct _ex_intern *condition ;
    int pos ;
    struct cond_info *next ;
} ;

int check_invariant(struct env *env, struct cond_info *info, struct _ex_intern *e, unsigned state, unsigned stack, int pos)
{
    while (info != NULL) {
        if (info->pos==pos) {
            e = _th_log_rewrite(env,e) ;
            if (!test_post_condition(env,e,state,stack,info->condition)) {
                _tree_print0("Induction loop invariant condition failure") ;
                _tree_indent() ;
                _tree_print_exp("environment", e);
                _tree_print_exp("invariant", info->condition);
                _tree_undent() ;
            }

            return 1 ;
        }
        info = info->next ;
    }

    return 0 ;
}

void fill_flow_tree(int space, unsigned fun, struct env *env, struct entry *list, struct flow_tree *ft, struct _ex_intern *invariant, unsigned label, struct cond_info *info)
{
    struct _ex_intern *al ;
    struct _ex_intern *e ;
    unsigned state, stack, new_state, new_stack ;
    struct cond_info info_rec ;

    if (ft->flag) return ;

    if (ft->has_loop_back) {
        struct _ex_intern *l, *al, *n ;

        _tree_print0("*** PROCESSING LOOP ***") ;
        _tree_indent() ;

        /* Fill in the info record */
        info_rec.next = info ;
        info_rec.condition = invariant ;
        info_rec.pos = ft->pos ;

        state = ft->state ;
        stack = ft->stack ;

        new_stack = new_stack_var(env) ;
        new_state = new_state_var(env) ;

        n = _ex_intern_appl_env(env,state,0,NULL) ;
        l = _ex_intern_appl1_env(env,INTERN_IMPORTANT_STATE,n) ;
        _th_log_derive_and_add(env, _th_derive_simplify(env,l)) ;

        if (label) {
            _th_log_add_precedence(ENVIRONMENT_SPACE,env,label,state) ;
        }

        e = _th_log_rewrite(env,ft->assertions) ;
        al = renamev(env,invariant,INTERN_STATE,state) ;
        al = renamev(env,al,INTERN_STACK,stack) ;
        al = renamev(env,al,INTERN_LOOP,state) ;
        if (label) al = renamev(env,al,label,state) ;
        if (!test_post_condition(env,e,state,stack,al)) {
            _tree_print0("Initial loop invariant condition failure") ;
            _tree_indent() ;
            _tree_print_exp("environment", e);
            _tree_print_exp("invariant", al);
            _tree_undent() ;
        }

        al = renamev(env,invariant,INTERN_STATE,new_state) ;
        al = renamev(env,al,INTERN_STACK,new_stack) ;
        al = renamev(env,al,INTERN_LOOP,new_state) ;
        ft->assertions = al ;

        al = invariant ;
        al = renamev(env,al,INTERN_LOOP,new_state) ;
        info_rec.next = info ;
        info_rec.pos = ft->pos ;
        info_rec.condition = al ;
        info = &info_rec ;

        al = invariant ;
        al = renamev(env,al,INTERN_STACK,new_stack) ;
        al = renamev(env,al,INTERN_LOOP,new_state) ;
        al = renamev(env,al,INTERN_STATE,new_state) ;
        al = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,al,e)) ;
        ft->assertions = al ;

        ft->state = new_state ;
        ft->stack = new_stack ;

        _tree_print0("Loop state") ;
        print_assertions(env,al) ;
        _tree_undent() ;

        invariant = _ex_true ;
    }

    state = ft->state ;
    stack = ft->stack ;
    al = build_successor_state(space, env, fun, list, ft->assertions, ft->code, 0, ft->pos, &state, &stack, &invariant, &label) ;
    //al = normalize_state(space,env,al,state,stack) ;
    if (ft->next) {
        if (check_invariant(env, info, al, state, stack, ft->next->pos)) {
            return ;
        }
        ft->next->assertions = merge_assertions(env, ft->next->assertions, ft->next->state, ft->next->stack, al, &state, &stack) ;
        ft->next->stack = stack ;
        ft->next->state = state ;
        if (!ft->terminal) {
            fill_flow_tree(space, fun, env, list, ft->next, invariant, label, info) ;
        }
    } else {
        _tree_print0("Merging into final") ;
        final_state = merge_assertions(env, final_state, final_state_state, final_state_stack, al, &state, &stack) ;
        final_state_state = state ;
        final_state_stack = stack ;
    }
    if (ft->code->operation == IfZero) {
        state = ft->state ;
        stack = ft->stack ;
        al = build_successor_state(space, env, fun, list, ft->assertions, ft->code, 1, ft->pos, &state, &stack, &invariant, &label) ;
        //al = normalize_state(space,env,al,state,stack) ;
        if (ft->cond_next) {
            if (check_invariant(env, info, al, state, stack, ft->cond_next->pos)) {
                return ;
            }
            ft->cond_next->stack = stack ;
            ft->cond_next->state = state ;
            ft->cond_next->assertions = merge_assertions(env, ft->cond_next->assertions, ft->cond_next->state, ft->cond_next->stack, al, &state, &stack) ;
            if (!ft->cond_terminal) {
                fill_flow_tree(space, fun, env, list, ft->cond_next, invariant, label, info) ;
            }
        } else {
            _tree_print0("Merging into final") ;
            final_state = merge_assertions(env, final_state, final_state_state, final_state_stack, al, &state, &stack) ;
            final_state_state = state ;
            final_state_stack = stack ;
        }
    }

}

void verify(int space, struct env *env, struct entry *list, struct entry *fun)
{
    struct _ex_intern *al ;
    struct flow_tree *ft = build_flow_tree(space,fun->u.function.code, 0, fun->u.function.code, NULL) ;
    struct instruction *inst ;
    int i ;

    _th_log_derive_push(env) ;

    _tree_print1("Function %s", fun->u.function.name) ;
    _tree_indent() ;

    _tree_print0("Code") ;
    _tree_indent();
    inst = fun->u.function.code  ;
    i = 0 ;
    while (inst != NULL) {
        _th_print_instruction(i,inst) ;
        inst = inst->next ;
        ++i ;
    }
    _tree_undent();
    _tree_print0("Derivation") ;
    _tree_indent() ;

    al = create_assertions(space, env, list, fun) ;

    _th_reset_context() ;
    _th_clear_cache() ;

    al = _th_log_rewrite(env,al) ;
    al = add_assertions(env,_ex_true,al) ;

    _tree_print0("Initial state") ;
    print_assertions(env,al) ;
    if (ft!=NULL) {
        final_state = NULL ;
        ft->assertions = al ;
        ft->state = INTERN_PRE ;
        ft->stack = INTERN_STACK ;
        fill_flow_tree(space, _th_intern(fun->u.function.name), env, list, ft, _ex_true, 0, NULL) ;
    } else {
        final_state = al ;
    }

    _tree_undent() ;

    _tree_print1("Flow tree for %s", fun->u.function.name) ;
    _tree_indent() ;

    _tree_print0("Start") ;
    _tree_indent() ;
    print_flow_tree(env, fun->u.function.code, ft) ;
    _tree_undent() ;
    {
        FILE *f = fopen("precedence","w") ;
        _th_dump_precedence_info(env, f) ;
        fclose(f) ;
    }

    print_assertions(env,final_state) ;
    //final_state = _th_log_rewrite(env,final_state) ;
    //print_assertions(env,final_state) ;

    _tree_undent() ;
    _tree_print0("Verification failures") ;
    _tree_indent() ;
    check_post_conditions(env, final_state, final_state_state, final_state_stack, list, fun) ;
    _tree_undent() ;
    _tree_undent() ;

    _th_log_derive_pop(env) ;
}

void _th_verify(int space, struct env *env, struct entry *list)
{
    struct entry *fun = list ;

    //add_state_var_info(env) ;

    _th_init_memory(env) ;

    while (fun != NULL) {
        if (fun->type == ENTRY_FUNCTION) {
            verify(space, env, list, fun) ;
        }
        fun = fun->next ;
    }
}

