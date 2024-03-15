/*
 * rule_app.c
 *
 * Rule application code
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */

#include <stdlib.h>
#include "Globals.h"
#include "Intern.h"

static int cut_flag = 0 ;
#define EXCLUDE_LIMIT 5
#define CONTEXT_LIMIT 10
static unsigned exclude_set[EXCLUDE_LIMIT] ;
static int exclude_set_count = 0 ;
static unsigned context_set[CONTEXT_LIMIT] ;
int context_set_count = 0 ;
struct _ex_intern *_th_limit_term = NULL ;
static int cond_level = 0 ;
static int backchain_quant_level = 0 ;

#ifndef FAST
#define MUTE 1
#endif

#ifdef MUTE
#define START_MUTE ++_tree_mute
#define END_MUTE --_tree_mute
#else
#define START_MUTE
#define END_MUTE
#endif

int _th_cond_level()
{
    return cond_level ;
}

void _th_increment_cond_level()
{
    ++cond_level;
}

void _th_decrement_cond_level()
{
    --cond_level;
}

int _th_in_context(unsigned c)
{
    int i ;

    for (i = 0; i < context_set_count; ++i) {
        if (context_set[i]==c) return 1 ;
    }

    return 0 ;
}

struct _ex_intern *_th_gen_context(struct env *env)
{
    struct _ex_intern *args[CONTEXT_LIMIT+1] ;
    int i ;

    for (i = 0; i < context_set_count; ++i) {
        args[i] = _ex_intern_appl1_env(env,INTERN_APPLY_CONTEXT,_ex_intern_string(_th_intern_decode(context_set[i]))) ;
    }

    if (cond_level==0) args[i++] = _ex_intern_appl1_env(env,INTERN_APPLY_CONTEXT,_ex_intern_string("mainContext")) ;

    return _ex_intern_appl_env(env,INTERN_AND,i,args) ;
}

struct _ex_intern *subst_var(struct env *env, struct _ex_intern *e, unsigned var, struct _ex_intern *value)
{
	struct _ex_unifier *u = _th_new_unifier(MATCH_SPACE) ;

	u = _th_add_pair(MATCH_SPACE,u,var,value) ;

	return _th_subst(env,u,e) ;
}

static int possibility_size = 0 ;
struct _ex_intern **_th_possible_rewrites ;
struct _ex_intern **_th_possible_conditions ;

void _th_check_possible_rewrites(int count)
{
    if (count > possibility_size) {
        if (possibility_size == 0) {
            possibility_size = count + 500 ;
            _th_possible_rewrites = (struct _ex_intern **)MALLOC(sizeof(struct _ex_intern *) * possibility_size) ;
            _th_possible_conditions = (struct _ex_intern **)MALLOC(sizeof(struct _ex_intern *) * possibility_size) ;
        } else {
            possibility_size = count + 500 ;
            _th_possible_rewrites = (struct _ex_intern **)REALLOC(_th_possible_rewrites, sizeof(struct _ex_intern *) * possibility_size) ;
            _th_possible_conditions = (struct _ex_intern **)REALLOC(_th_possible_conditions, sizeof(struct _ex_intern *) * possibility_size) ;
        }
    }
}

static int condition_size = 0 ;
static int condition_base = 0 ;
static struct _ex_intern **set_base ;
static int *args_base ;
static struct _ex_unifier **unifiers_base ;
static struct _ex_intern ***saves_base ;
static struct _ex_intern **current_base ;

static void check_condition_size(int size)
{
    if (condition_base + size  > condition_size) {
        if (condition_size==0) {
            condition_size = 4000 ;
            set_base = (struct _ex_intern **)MALLOC(sizeof(struct _ex_intern *) * condition_size) ;
            args_base = (int *)MALLOC(sizeof(int) * condition_size) ;
            unifiers_base = (struct _ex_unifier **)MALLOC(sizeof(struct _ex_unifier *) * condition_size) ;
            saves_base = (struct _ex_intern ***)MALLOC(sizeof(struct _ex_intern **) * condition_size) ;
            current_base = (struct _ex_intern **)MALLOC(sizeof(struct _ex_intern *) * condition_size) ;
        } else {
            condition_size = condition_base + size + 4000 ;
            set_base = (struct _ex_intern **)REALLOC(set_base, sizeof(struct _ex_intern *) * condition_size) ;
            args_base = (int *)MALLOC(sizeof(int) * condition_size) ;
            unifiers_base = (struct _ex_unifier **)REALLOC(args_base, sizeof(struct _ex_unifier *) * condition_size) ;
            saves_base = (struct _ex_intern ***)REALLOC(saves_base, sizeof(struct _ex_intern **) * condition_size) ;
            current_base = (struct _ex_intern **)REALLOC(current_base, sizeof(struct _ex_intern *) * condition_size) ;
        }
    }
}

static struct _ex_intern *context_rewrite(struct env *env, struct _ex_intern *e, int count, int pos, struct _ex_intern **args, struct _ex_intern **derives)
{
    int i ;

    _th_derive_push(env) ;
    START_MUTE ;
    _zone_print0("Adding derived rules") ;
    _tree_indent() ;
    for (i = 0; i < count; ++i) {
        if (derives[i] != NULL && i != pos) _th_derive_add_prepared(env,derives[i]) ;
    }
    _tree_undent() ;
    END_MUTE ;
    e = _th_int_rewrite(env, e, 5) ;
    _th_derive_pop(env) ;

    return e ;
}

static struct _ex_unifier *process_condition(struct env *env, int count, struct _ex_unifier *u, int cnt, int pos, struct _ex_intern **c_args, struct _ex_intern **derives, unsigned functor)
{
    int i, j, ii ;
    
    struct _ex_intern **set = set_base + condition_base ;
    int *arg_pos = args_base + condition_base ;
    struct _ex_unifier **unifiers = unifiers_base + condition_base ;
    struct _ex_intern ***saves = saves_base + condition_base ;
    struct _ex_intern **current = current_base + condition_base ;

    condition_base += count ;

    if (!u) {
        i = count-1 ;
        goto fail ;
    }

    for (i = 0; i < count; ++i) {

        arg_pos[i] = 0 ;
        set[i] = NULL ;

        _zone_print1("Processing %d", i);

        if (current[i]->type==EXP_APPL &&
            current[i]->u.appl.functor==INTERN_CHOOSE &&
            current[i]->u.appl.count==2) {

            struct _ex_intern *f ;

            if (current[i]->u.appl.args[0]->type != EXP_VAR) goto fail ;

            _zone_print0("Choose");
            _tree_indent();
            f = context_rewrite(env, _th_unmark_vars(env, current[i]->u.appl.args[1]), cnt, pos, c_args, derives) ;

            if (f->type==EXP_APPL && f->u.appl.functor==INTERN_QUOTE && f->u.appl.count==1) f = f->u.appl.args[0] ;
            set[i] = f ;
            if (set[i]->type != EXP_APPL || set[i]->u.appl.functor != INTERN_SET) {
                set[i] = NULL ;
                _tree_undent();
                goto fail ;
            }
            arg_pos[i] = 1 ;
            unifiers[i] = _th_shallow_copy_unifier(MATCH_SPACE,u) ;
            saves[i] = (struct _ex_intern **)_th_alloc(MATCH_SPACE, sizeof(struct _ex_intern *) * count) ;

            for (j = 0; j < count; ++j) {
                saves[i][j] = current[j] ;
            }

            if (set[i]->u.appl.count == 0) {
                set[i] = NULL ;
                _tree_undent();
                goto fail ;
            }

            _zone_print1("Assigning %s", _th_intern_decode(current[i]->u.appl.args[0]->u.var)) ;
            _tree_indent() ;
            _zone_print_exp("", set[i]->u.appl.args[0]) ;
            _tree_undent() ;

            for (j = i+1; j < count; ++j) {
                current[j] = subst_var(env, current[j], current[i]->u.appl.args[0]->u.var, set[i]->u.appl.args[0]) ;
            }

            u = _th_add_pair(MATCH_SPACE, u, current[i]->u.appl.args[0]->u.var, set[i]->u.appl.args[0]) ;
            _tree_undent();

        } else if (current[i]->type==EXP_APPL &&
            current[i]->u.appl.functor==INTERN_CHOOSE_CONTEXT_RULE &&
            current[i]->u.appl.count==1) {

            struct _ex_intern *f ;
            struct _ex_intern **args ;
            struct match_return *mr ;
            struct _ex_intern *pat ;
            struct rl {
                struct rl *next ;
                struct _ex_intern *rule ;
            } *r, *rl ;
            void *iterator ;
            int priority, c ;
            unsigned v ;
            _zone_print0("Choose context rewrite");
            _tree_indent();

            _th_derive_push(env) ;
            START_MUTE ;
            _zone_print0("Adding derived rules") ;
            _tree_indent() ;
            for (ii = 0; ii < cnt; ++ii) {
                if (derives[ii] != NULL && ii != pos) _th_derive_add_prepared(env,derives[ii]) ;
            }
            _tree_undent() ;
            END_MUTE ;

            pat = current[i]->u.appl.args[0] ;
            if (pat->type==EXP_APPL && pat->u.appl.functor==INTERN_QUOTE && pat->u.appl.count==1) pat = pat->u.appl.args[0] ;

            _th_init_find_small(_th_get_context_rules(env), pat->u.appl.args[0], &iterator) ;
            rl = NULL ;
            c = 0 ;
            while(f = _th_next_find_small(&iterator,&priority)) {
                r = (struct rl *)ALLOCA(sizeof(struct rl)) ;
                r->next = rl ;
                rl = r ;
                r->rule = f ;
                _zone_print_exp("rule", f) ;
                ++c ;
            }

            _th_derive_pop(env) ;

            unifiers[i] = _th_shallow_copy_unifier(MATCH_SPACE,u) ;
            saves[i] = (struct _ex_intern **)_th_alloc(MATCH_SPACE, sizeof(struct _ex_intern *) * count) ;
            for (j = 0; j < count; ++j) {
                saves[i][j] = current[j] ;
            }


            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * c) ;
            for (j = 0; j < c; ++j) {
                args[j] = rl->rule ;
                rl = rl->next ;
            }
            set[i] = _ex_intern_appl_env(env,INTERN_SET,c,args) ;

            _zone_print_exp("pat =", pat) ;
            for (j = 0; j < set[i]->u.appl.count; ++j) {
                mr = _th_match(env,pat,set[i]->u.appl.args[j]) ;
                _zone_print2("Testing %s %d", _th_print_exp(set[i]->u.appl.args[j]), mr) ;
                if (mr != NULL ) {
                    break ;
                }
            }
            if (j==set[i]->u.appl.count) {
                _zone_print_exp("Fail", current[i]->u.appl.args[0]) ;
                _tree_undent() ;
                goto fail ;
            }

            arg_pos[i] = j+1 ;

            _zone_print_exp("Assigning", current[i]->u.appl.args[0]) ;
            _tree_indent() ;
            _zone_print_exp("", set[i]->u.appl.args[0]) ;
            _tree_undent() ;

            iterator = _th_dom_init(MATCH_SPACE,mr->theta) ;
            while (v = _th_dom_next(iterator)) {

                for (j = i+1; j < count; ++j) {
                    current[j] = subst_var(env, current[j], v, _th_apply(mr->theta,v)) ;
                }

                u = _th_add_pair(MATCH_SPACE, u, v, _th_apply(mr->theta,v)) ;
            }

            _tree_undent();

        } else if (current[i]->type==EXP_APPL &&
            current[i]->u.appl.functor==INTERN_EXCLUDE_SET) {

            unsigned v ;

            _zone_print_exp("Testing exclude set", current[i]) ;

            if (current[i]->u.appl.args[0]->type != EXP_STRING) {
                _zone_print0("fail") ;
                goto fail ;
            }

            v = _th_intern(current[i]->u.appl.args[0]->u.string) ;

            for (j = 0; j < exclude_set_count; ++i) {
                _tree_indent() ;
                _zone_print0("fail") ;
                _tree_undent() ;
                if (exclude_set[j]==v) goto fail ;
            }

            _tree_indent() ;
            _zone_print0("good") ;
            _tree_undent() ;

            if (exclude_set_count==EXCLUDE_LIMIT) goto fail ;

            exclude_set[exclude_set_count++] = v ;

        } else if (current[i]->type==EXP_APPL && current[i]->u.appl.functor==INTERN_NESTING_LIMIT &&
                   current[i]->u.appl.count==1) {

            ;

        } else if (current[i]->type==EXP_APPL &&
            (current[i]->u.appl.functor==INTERN_USE_CONTEXT || current[i]->u.appl.functor==INTERN_APPLY_CONTEXT)) {

            unsigned v ;

            _zone_print0("Applying context") ;

            if (current[i]->u.appl.args[0]->type != EXP_STRING) goto fail ;
            v = _th_intern(current[i]->u.appl.args[0]->u.string) ;

            _tree_indent() ;
            _zone_print1("%s", _th_intern_decode(v)) ;
            _tree_undent() ;

            if (context_set_count==CONTEXT_LIMIT) goto fail ;

            for (j = 0; j < context_set_count; ++j) {
                if (context_set[j]==v) goto cont ;
            }

            _zone_print0("Adding context") ;
            context_set[context_set_count++] = v ;
            goto cont ;

#ifdef XX
        } else if (current[i]->type==EXP_APPL &&
            current[i]->u.appl.functor==INTERN_APPLY_CONTEXT) {

            unsigned v ;

            if (current[i]->u.appl.args[0]->type != EXP_VAR) goto fail ;
            v = current[i]->u.appl.args[0]->u.var ;

            for (i = 0; i < context_set_count; ++i) {
                if (context_set[i]==v) goto cont ;
            }

            goto fail ;
#endif
        } else if (current[i]->type==EXP_APPL &&
            current[i]->u.appl.functor==INTERN_CUT &&
            current[i]->u.appl.count==0) {

            _zone_print0("Cut");

            cut_flag = 1 ;

        } else if (current[i]->type==EXP_APPL &&
            current[i]->u.appl.functor==INTERN_MATCH &&
            current[i]->u.appl.count==2) {

            struct match_return *m ;
            //_zone_print_exp("Matching", current[i]->u.appl.args[1]) ;
            _tree_indent() ;
            //_zone_print_exp("and", current[i]->u.appl.args[0]) ;
            if ((m = _th_match(env, current[i]->u.appl.args[1], current[i]->u.appl.args[0])) != NULL) {
                void *it ;
                _zone_print0("Good") ;
                it = _th_dom_init(MATCH_SPACE, m->theta) ;
                while (1) {
                    unsigned var = _th_dom_next(it) ;
                    if (var==0) break ;
                    _zone_print1("Assigning %s", _th_intern_decode(var));
                    _tree_indent();
                    _zone_print_exp("", _th_apply(m->theta,var)) ;
                    _tree_undent();
                    u = _th_add_pair(MATCH_SPACE, u, var, _th_apply(m->theta, var)) ;
                    for (j = i+1; j < count; ++j) {
                        current[j] = subst_var(env, current[j], var, _th_apply(m->theta, var)) ;
                    }
                }
                _tree_undent() ;
            } else {
                _zone_print0("Fail") ;
                _tree_undent() ;
                goto fail ;
            }

        } else if (current[i]->type==EXP_APPL &&
            current[i]->u.appl.functor==INTERN_CUT_LOCAL &&
            current[i]->u.appl.count==0) {

            _zone_print0("Cut local");
            for (j = 0; j < i; ++j) set[j] = NULL ;

        } else if (current[i]->type==EXP_APPL &&
            current[i]->u.appl.functor==INTERN_NOTL) {

            struct _ex_intern *e = current[i] ;

            check_condition_size(e->u.appl.count) ;

            for (j = 0; j < e->u.appl.count; ++j) {
                current_base[j + condition_base] = e->u.appl.args[j] ;
            }

            _zone_print0("Start notl") ;
            if (process_condition(env, e->u.appl.count, u, cnt, pos, c_args, derives, functor)) {
                _zone_print0("Finish notl") ;
                goto fail ;
            }
            _zone_print0("Finish notl") ;

        } else if (current[i]->type==EXP_APPL && current[i]->u.appl.functor==INTERN_IN_CONTEXT &&
                   current[i]->u.appl.count==1) {
            _zone_print0("In context") ;
            ;
        } else if (current[i]->type==EXP_APPL && current[i]->u.appl.functor==INTERN_BLOCK_CONTEXT &&
                   current[i]->u.appl.count==1) {
            _zone_print0("Block context") ;
            ;
        } else if (current[i]->type==EXP_APPL && current[i]->u.appl.functor==INTERN_NO_AUGMENT) {
            ;
        } else if (current[i]->type==EXP_APPL && current[i]->u.appl.functor==INTERN_NO_FUNCTOR) {
            if (current[i]->u.appl.args[0]->type==EXP_APPL &&
                current[i]->u.appl.args[0]->u.appl.functor==functor) goto fail;
            ;
        } else {
            struct _ex_intern *e ;
            int res = ((e = context_rewrite(env,_th_unmark_vars(env,current[i]), cnt, pos, c_args, derives))==_ex_true) ;
            _th_check_result(env, e, 10) ;
            if (!res) goto fail ;
        }
cont: ;
    }

    condition_base -= count ;
    _zone_print0("Good");
    return u ;

fail:
    do {
        if (i >= 0 && set[i] != NULL && arg_pos[i] < set[i]->u.appl.count) {
            _zone_print1("Backtrack %d", i);
            _tree_indent();
            if (current[i]->u.appl.functor==INTERN_CHOOSE) {
                u = _th_add_pair(MATCH_SPACE, _th_shallow_copy_unifier(MATCH_SPACE,unifiers[i]), current[i]->u.appl.args[0]->u.var, set[i]->u.appl.args[arg_pos[i]]) ;
                _zone_print1("Assigning %s", _th_intern_decode(current[i]->u.appl.args[0]->u.var)) ;
                _tree_indent();
                _zone_print_exp("", set[i]->u.appl.args[arg_pos[i]]) ;
                _tree_undent();
                _tree_undent();
                for (j = i+1; j < count; ++j) {
                    current[j] = subst_var(env,saves[i][j],current[i]->u.appl.args[0]->u.var, set[i]->u.appl.args[arg_pos[i]]) ;
                }
                ++arg_pos[i] ;
                goto cont ;
            } else {
                void *iterator ;
                unsigned v ;
                struct match_return *mr ;
                struct _ex_intern *pat ;

                pat = current[i]->u.appl.args[0] ;
                if (pat->type==EXP_APPL && pat->u.appl.functor==INTERN_QUOTE && pat->u.appl.count==1) pat = pat->u.appl.args[0] ;
                for (j = arg_pos[i]; j < set[i]->u.appl.count; ++j) {
                    mr = _th_match(env,pat,set[i]->u.appl.args[j]) ;
                    if (mr != NULL ) {
                        break ;
                    }
                }
                if (j==set[i]->u.appl.count) {
                    --i ;
                    _tree_undent() ;
                    goto fail ;
                }
                arg_pos[i] = j ;

                u = _th_shallow_copy_unifier(MATCH_SPACE,unifiers[i]) ;

                iterator = _th_dom_init(MATCH_SPACE, mr->theta) ;
                while (v = _th_dom_next(iterator)) {

                    for (j = i+1; j < count; ++j) {
                        current[j] = subst_var(env, saves[i][j], v, _th_apply(mr->theta,v)) ;
                    }

                    u = _th_add_pair(MATCH_SPACE, u, v, _th_apply(mr->theta,v)) ;
                }

                _zone_print_exp("Assigning", current[i]->u.appl.args[0]) ;
                _tree_indent();
                _zone_print_exp("", set[i]->u.appl.args[arg_pos[i]]) ;
                _tree_undent();
                _tree_undent();
                ++arg_pos[i] ;

                goto cont ;
            }
        }
        --i ;
    } while (i >= 0) ;

    condition_base -= count ;
    return NULL ;
}

static struct _ex_unifier *test_condition(struct env *env, struct _ex_intern *e, struct _ex_unifier *u, int cnt, int pos, struct _ex_intern **c_args, struct _ex_intern **derives, unsigned functor)
{
    int possibility_size_save = possibility_size ;
    struct _ex_intern **_th_possible_rewrites_save = _th_possible_rewrites ;
    int _th_possibility_count_save = _th_possibility_count ;
    struct _ex_intern **_th_possible_conditions_save = _th_possible_conditions ;
    possibility_size = 0 ;
    _th_possible_rewrites = NULL ;
    _th_possible_conditions = NULL ;
    
    /*printf("        cond: %s\n", _th_print_exp(e)) ;
    printf("        res: %s\n", _th_print_exp(_th_rewrite(env,_th_unmark_vars(env,e)))) ;*/
    ++cond_level ;
    if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_NC_AND || e->u.appl.functor==INTERN_ANDQ)) {

        int i ;

        _zone_print2("Testing condition %d %s", _tree_count, _th_print_exp(e)) ;
        _tree_indent() ;
        for (i = 0; i < context_set_count; ++i) {
            _zone_print1("context %s", _th_intern_decode(context_set[i])) ;
        }

        check_condition_size(e->u.appl.count) ;
        _zone_print1("size = %d\n", e->u.appl.count) ;

        for (i = 0; i < e->u.appl.count; ++i) {
            //_zone_print2("Adding term %x %s", e->u.appl.args[i], _th_print_exp(e->u.appl.args[i])) ;
            current_base[i+condition_base] = e->u.appl.args[i] ;
        }

        u = process_condition(env, e->u.appl.count, u, cnt, pos, c_args, derives, functor) ;

        if (_th_possible_rewrites != NULL) FREE(_th_possible_rewrites) ;
        if (_th_possible_conditions != NULL) FREE(_th_possible_conditions) ;
        possibility_size = possibility_size_save ;
        _th_possible_rewrites = _th_possible_rewrites_save ;
        _th_possibility_count = _th_possibility_count_save ;
        _th_possible_conditions = _th_possible_conditions_save ;

        _tree_undent() ;

        --cond_level ;

        return u;

    } else {

        struct _ex_unifier *res = (context_rewrite(env,_th_unmark_vars(env,e), cnt, pos, c_args, derives)==_ex_true)?u:NULL ;

        if (_th_possible_rewrites != NULL) FREE(_th_possible_rewrites) ;
        if (_th_possible_conditions != NULL) FREE(_th_possible_conditions) ;
        possibility_size = possibility_size_save ;
        _th_possible_rewrites = _th_possible_rewrites_save ;
        _th_possibility_count = _th_possibility_count_save ;
        _th_possible_conditions = _th_possible_conditions_save ;

        --cond_level ;

        return res ;
    }
}

static struct _ex_unifier *retest_condition(struct env *env, struct _ex_intern *e, int cnt, int pos, struct _ex_intern **c_args, struct _ex_intern **derives, unsigned functor)
{
    struct _ex_unifier *u ;

    int possibility_size_save = possibility_size ;
    struct _ex_intern **_th_possible_rewrites_save = _th_possible_rewrites ;
    int _th_possibility_count_save = _th_possibility_count ;
    struct _ex_intern **_th_possible_conditions_save = _th_possible_conditions ;
    possibility_size = 0 ;
    _th_possible_rewrites = NULL ;
    _th_possible_conditions = NULL ;

    ++cond_level ;

    /*printf("        cond: %s\n", _th_print_exp(e)) ;
    printf("        res: %s\n", _th_print_exp(_th_rewrite(env,_th_unmark_vars(env,e)))) ;*/
    _tree_indent() ;
    if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_NC_AND || e->u.appl.functor==INTERN_ANDQ)) {

        u = process_condition(env, e->u.appl.count, NULL, cnt, pos, c_args, derives, functor) ;

        if (_th_possible_rewrites != NULL) FREE(_th_possible_rewrites) ;
        if (_th_possible_conditions != NULL) FREE(_th_possible_conditions) ;
        possibility_size = possibility_size_save ;
        _th_possible_rewrites = _th_possible_rewrites_save ;
        _th_possibility_count = _th_possibility_count_save ;
        _th_possible_conditions = _th_possible_conditions_save ;

        _tree_undent() ;
        --cond_level ;
        return u;

    } else {

        if (_th_possible_rewrites != NULL) FREE(_th_possible_rewrites) ;
        if (_th_possible_conditions != NULL) FREE(_th_possible_conditions) ;
        possibility_size = possibility_size_save ;
        _th_possible_rewrites = _th_possible_rewrites_save ;
        _th_possibility_count = _th_possibility_count_save ;
        _th_possible_conditions = _th_possible_conditions_save ;

        _tree_undent() ;
        --cond_level ;
        return NULL ;
    }
}

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

struct _ex_intern *augment_union(struct env *env, struct _ex_intern *r, struct _ex_intern *e)
{
    int i, j ;
    struct _ex_intern *l = r->u.appl.args[0] ;
    if (l->type==EXP_APPL && l->u.appl.functor==INTERN_UNION &&
        e->type==EXP_APPL && e->u.appl.functor==INTERN_UNION) {

        struct _ex_intern *se, *sl, *sl2, *slr, *nr ;
        unsigned *vars ;
        int adds ;
        struct _ex_intern **args ;

        sl = NULL ;
        for (i = 0; i < l->u.appl.count; ++i) {
            if (l->u.appl.args[i]->type==EXP_APPL && l->u.appl.args[i]->u.appl.functor==INTERN_SET) {
                sl = l->u.appl.args[i] ;
                break ;
            }
        }
        if (sl==NULL) return r ;

        se = NULL ;
        for (i = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type==EXP_APPL && e->u.appl.args[i]->u.appl.functor==INTERN_SET) {
                se = e->u.appl.args[i] ;
                break ;
            }
        }
        if (se==NULL) return r ;

        if (sl->u.appl.count >= se->u.appl.count) return r ;

        adds = se->u.appl.count - sl->u.appl.count ;
        vars = ALLOCA(sizeof(unsigned) * adds) ;
        _th_multi_name_away(r,_th_intern("e"),adds,vars) ;

        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * se->u.appl.count) ;
        for (i = 0; i < sl->u.appl.count; ++i) {
            args[i] = sl->u.appl.args[i] ;
        }
        for (j = i; j < se->u.appl.count; ++j) {
            args[j] = _ex_intern_var(vars[j-i]) ;
        }
        sl2 = _ex_intern_appl_env(env,INTERN_SET,j,args) ;
        slr = _ex_intern_appl_env(env,INTERN_SET,j-i,args+i) ;

        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * l->u.appl.count) ;
        for (i = 0; i < l->u.appl.count; ++i) {
            if (l->u.appl.args[i]==sl) {
                args[i] = sl2 ;
            } else {
                args[i] = l->u.appl.args[i] ;
            }
        }
        l = _ex_intern_appl_env(env,INTERN_UNION,i,args) ;
        nr = _th_flatten_top(env, _ex_intern_appl2_env(env,INTERN_UNION,r->u.appl.args[1],slr)) ;

        return _ex_intern_appl3_env(env,r->u.appl.functor,l,nr,r->u.appl.args[2]) ;
    } else {
        return r ;
    }
}

struct _ex_intern *_th_augment_expression(struct env *env,
                                             struct _ex_intern *r, struct _ex_intern *e)
{
    struct _ex_intern *left, *right, *var ;
    unsigned v ;
    int i ;

    if (r->u.appl.args[2]->type==EXP_APPL && r->u.appl.args[2]->u.appl.functor==INTERN_NO_AUGMENT) return r;
    right = r->u.appl.args[2];
    if (right->type==EXP_APPL && right->u.appl.functor==INTERN_NC_AND) {
        for (i = 0; i < right->u.appl.count; ++i) {
            if (right->u.appl.args[i]->type==EXP_APPL &&
                right->u.appl.args[i]->u.appl.functor==INTERN_NO_AUGMENT) return r;
        }
    }

    if (r->no_top_var &&
        e->type == EXP_APPL &&
        r->u.appl.args[0]->u.appl.functor == e->u.appl.functor &&
        _th_is_ac(env,r->u.appl.args[0]->u.appl.functor) &&
        e->u.appl.count > r->u.appl.args[0]->u.appl.count) {
        check_size(e->u.appl.count) ;
        v = _th_name_away(r,INTERN_V) ;
        var = _ex_intern_var(v) ;
        for (i = 0; i < r->u.appl.args[0]->u.appl.count; ++i) {
            args[i] = r->u.appl.args[0]->u.appl.args[i] ;
        }
        args[i++] = var ;
        left = _ex_intern_appl_env(env,e->u.appl.functor,i,args) ;
        if (r->u.appl.args[1]->type==EXP_APPL &&
            r->u.appl.args[1]->u.appl.functor==e->u.appl.functor) {
            for (i = 0; i < r->u.appl.args[1]->u.appl.count; ++i) {
                args[i] = r->u.appl.args[1]->u.appl.args[i] ;
            }
        } else {
            args[0] = r->u.appl.args[1] ;
            i = 1 ;
        }
        args[i++] = var ;
        right = _ex_intern_appl_env(env,e->u.appl.functor,i,args) ;
        args[0] = left ;
        args[1] = right ;
        args[2] = r->u.appl.args[2] ;
        /*printf("orig: %s\n", _th_print_exp(r)) ;*/
        r = _ex_intern_appl_env(env,r->u.appl.functor,3,args) ;
        return augment_union(env, r, e) ;
    } else if (r->u.appl.args[0]->type==EXP_APPL && r->u.appl.args[0]->u.appl.functor==INTERN_EQUAL &&
               r->u.appl.args[0]->u.appl.count==2 && e->type==EXP_APPL && e->u.appl.functor==INTERN_ORIENTED_RULE &&
               e->u.appl.count==3 &&
               (r->u.appl.args[1]==_ex_true || r->u.appl.args[1]==_ex_false)) {
        /*unsigned var = _th_name_away(r,INTERN_V) ;*/
        return _ex_intern_appl2_env(env, INTERN_AND,
                   _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE,
                       _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE,
                           r->u.appl.args[0]->u.appl.args[0],
                           r->u.appl.args[0]->u.appl.args[1],
                           _ex_true),
                       r->u.appl.args[1],
                       r->u.appl.args[2]),
                   _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE,
                       _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE,
                           r->u.appl.args[0]->u.appl.args[1],
                           r->u.appl.args[0]->u.appl.args[0],
                           _ex_true),
                       r->u.appl.args[1],
                       r->u.appl.args[2])) ;
    } else if (r->u.appl.args[0]->type==EXP_APPL && r->u.appl.args[0]->u.appl.functor==INTERN_UNORIENTED_RULE &&
               r->u.appl.args[0]->u.appl.count==3 && e->type==EXP_APPL && e->u.appl.functor==INTERN_ORIENTED_RULE &&
               e->u.appl.count==3 &&
               (r->u.appl.args[1]==_ex_true || r->u.appl.args[1]==_ex_false)) {
        return _ex_intern_appl2_env(env, INTERN_AND,
                   _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE,
                       _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE,
                           r->u.appl.args[0]->u.appl.args[0],
                           r->u.appl.args[0]->u.appl.args[1],
                           r->u.appl.args[0]->u.appl.args[2]),
                       r->u.appl.args[1],
                       r->u.appl.args[2]),
                   _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE,
                       _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE,
                           r->u.appl.args[0]->u.appl.args[1],
                           r->u.appl.args[0]->u.appl.args[0],
                           r->u.appl.args[0]->u.appl.args[2]),
                       r->u.appl.args[1],
                       r->u.appl.args[2])) ;
    } else if (r->u.appl.args[0]->type==EXP_QUANT && e->type==EXP_QUANT &&
               r->u.appl.args[0]->u.quant.quant==INTERN_ALL && e->u.quant.quant==INTERN_ALL &&
               r->u.appl.args[0]->u.quant.var_count==e->u.quant.var_count) {
        struct _ex_intern *rl = r->u.appl.args[0]->u.quant.exp;
        struct _ex_intern *el = e->u.quant.exp;
        if (rl->type==EXP_APPL && rl->u.appl.functor==INTERN_UNORIENTED_RULE &&
            el->type==EXP_APPL && el->u.appl.functor==INTERN_ORIENTED_RULE &&
            rl->u.appl.count==3 && el->u.appl.count==3) {

            return _ex_intern_appl2_env(env, INTERN_AND,
                       _ex_intern_appl3_env(env, r->u.appl.functor,
                           _ex_intern_quant(INTERN_ALL,r->u.appl.args[0]->u.quant.var_count,r->u.appl.args[0]->u.quant.vars,
                               _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,
                                   rl->u.appl.args[0],
                                   rl->u.appl.args[1],
                                   rl->u.appl.args[2]),
                               r->u.appl.args[0]->u.quant.cond),
                           r->u.appl.args[1],
                           r->u.appl.args[2]),
                       _ex_intern_appl3_env(env, r->u.appl.functor,
                           _ex_intern_quant(INTERN_ALL,r->u.appl.args[0]->u.quant.var_count,r->u.appl.args[0]->u.quant.vars,
                               _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,
                                   rl->u.appl.args[1],
                                   rl->u.appl.args[0],
                                   rl->u.appl.args[2]),
                               r->u.appl.args[0]->u.quant.cond),
                           r->u.appl.args[1],
                           r->u.appl.args[2])) ;
        }
    }
    return augment_union(env, r, e) ;
}

struct _rule_try {
	struct _ex_intern *e ;
	int priority ;
        int is_context ;
} ;

static struct _rule_try *tries ;
int try_count = 0 ;

static void r_check_size(int size)
{
    if (size > try_count) {
        size += 4000 ;
        if (try_count == 0) {
            tries = (struct _rule_try *)MALLOC(size * sizeof(struct _rule_try)) ;
        } else {
            tries = (struct _rule_try *)REALLOC(tries, size * sizeof(struct _rule_try)) ;
        }
        try_count = size ;
    }
}

int cmp(struct _rule_try *r1, struct _rule_try *r2)
{
	return r1->priority - r2->priority ;
}

static struct _ex_unifier *bvmap;

static struct _ex_intern *nabv(struct env *env, struct _ex_intern *nae, struct _ex_intern *rule)
{
    int i, j, c;
    unsigned *fv;

    switch (rule->type) {

        case EXP_APPL:
            for (i = 0; i < rule->u.appl.count; ++i) {
                nae = nabv(env,nae,rule->u.appl.args[i]);
            }
            break;

        case EXP_QUANT:
            for (i = 0; i < rule->u.quant.var_count; ++i) {
                //printf("Testing var %s %s\n",_th_intern_decode(rule->u.quant.vars[i]),_th_print_exp(nae));
                if (_th_apply(bvmap,rule->u.quant.vars[i])==NULL) {
                    struct _ex_intern *na = _ex_intern_var(_th_name_away(nae,rule->u.quant.vars[i]));
                    nae = _ex_intern_appl2_env(env,INTERN_T,nae,na);
                    //printf("Adding var %s %s\n", _th_intern_decode(rule->u.quant.vars[i]),_th_print_exp(na));
                    bvmap = _th_add_pair(MATCH_SPACE,bvmap,rule->u.quant.vars[i],na);
                }
            }
            nae = nabv(env,nae,rule->u.quant.exp);
            nae = nabv(env,nae,rule->u.quant.cond);
            break;

        case EXP_CASE:
            nae = nabv(env,nae,rule->u.case_stmt.exp);
            for (i = 0; i < rule->u.case_stmt.count; ++i) {
                fv = _th_get_free_vars(rule->u.case_stmt.args[i*2], &c);
                for (j = 0; j < c; ++j) {
                    if (!_th_is_free_in(nae,fv[j])) {
                        struct _ex_intern *na = _ex_intern_var(_th_name_away(nae,fv[j]));
                        nae = _ex_intern_appl2_env(env,INTERN_T,nae,na);
                        bvmap = _th_add_pair(MATCH_SPACE,bvmap,fv[j],na);
                    }
                }
                nae = nabv(env,nae,rule->u.case_stmt.args[i*2+1]);
            }
            break;

        default:
            return nae;
    }

    return nae;
}

static struct _ex_intern *do_nabv(struct env *env, struct _ex_intern *rule)
{

    int i, c, j;
    struct _ex_intern **args, *exp, *cond;
    unsigned *vars, *fv;

    switch (rule->type) {

        case EXP_APPL:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * rule->u.appl.count);
            for (i = 0; i < rule->u.appl.count; ++i) {
                args[i] = do_nabv(env,rule->u.appl.args[i]);
            }
            return _ex_intern_appl_env(env,rule->u.appl.functor,rule->u.appl.count,args);

        case EXP_QUANT:
            exp = do_nabv(env,rule->u.quant.exp);
            cond = do_nabv(env,rule->u.quant.cond);
            vars = (unsigned *)ALLOCA(sizeof(unsigned) * rule->u.quant.var_count);
            for (i = 0; i < rule->u.quant.var_count; ++i) {
                struct _ex_unifier *u;
                u = _th_new_unifier(MATCH_SPACE);
                u = _th_add_pair(MATCH_SPACE,u,rule->u.quant.vars[i],_th_apply(bvmap,rule->u.quant.vars[i]));
                vars[i] = _th_apply(bvmap,rule->u.quant.vars[i])->u.var;
                exp = _th_subst(env,u,exp);
                cond = _th_subst(env,u,cond);
            }
            return _ex_intern_quant(rule->u.quant.quant,rule->u.quant.var_count,vars,exp,cond);

        case EXP_CASE:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * rule->u.case_stmt.count *2);
            for (i = 0; i < rule->u.case_stmt.count; ++i) {
                fv = _th_get_free_vars(rule->u.case_stmt.args[i*2], &c);
                exp = rule->u.case_stmt.args[i*2];
                cond = rule->u.case_stmt.args[i*2+1];
                for (j = 0; j < c; ++j) {
                    struct _ex_unifier *u;
                    u = _th_new_unifier(MATCH_SPACE);
                    u = _th_add_pair(MATCH_SPACE,u,fv[j],_th_apply(bvmap,fv[j]));
                    exp = _th_subst(env,u,exp);
                    cond = _th_subst(env,u,cond);
                }
                cond = do_nabv(env,cond);
                args[i*2] = exp;
                args[i*2+1] = cond;
            }
            exp = do_nabv(env,rule->u.case_stmt.exp);
            return _ex_intern_case(exp,rule->u.case_stmt.count,args);

        default:
            return rule;
    }
}

static struct _ex_intern *name_away_bv(struct env *env, struct _ex_intern *rule, struct _ex_intern *e)
{
    struct _ex_intern *nae = _ex_intern_appl2_env(env,INTERN_T,rule,e);

    bvmap = _th_new_unifier(MATCH_SPACE);

    nae = nabv(env,nae,rule);

    return do_nabv(env,rule);
}

struct _ex_intern *_th_rewrite_rule(struct env *env, struct _ex_intern *e, int do_transitive)
{
    struct small_disc *s = _th_get_forward_context_rules(env) ;
    struct disc *d = _th_get_forward_rules(env) ;
    struct match_return *mr ;
    struct _ex_intern *r, *r2 ;
    void *iterator ;
    struct disc_iterator di ;
    char *mark ;
    int save_cut_flag = cut_flag ;
    struct _ex_intern *save_limit_term = _th_limit_term ;
    int save_exclude_set_count = exclude_set_count ;
    unsigned save_exclude_set[EXCLUDE_LIMIT] ;
    int save_context_set_count = context_set_count ;
    unsigned save_context_set[CONTEXT_LIMIT] ;
    int priority, c, i, j, k ;
    struct _ex_intern **rules, *cond, *cond2 ;
    int *priorities, *is_context ;
    int cut_priority ;
    struct _ex_unifier *u ;
    int back_chain_save = backchain_quant_level ;
    unsigned functor;
    int levels;

    backchain_quant_level = _th_quant_level ;
    cut_flag = 0 ;
    _th_limit_term = e ;

    for (i = 0; i < save_exclude_set_count; ++i) {
        save_exclude_set[i] = exclude_set[i] ;
    }
    exclude_set_count = 0 ;
    for (i = 0; i < save_context_set_count; ++i) {
        save_context_set[i] = context_set[i] ;
    }
    context_set_count = 0 ;

    _zone_print_exp("Applying rules for", e) ;
    _tree_indent() ;
    for (i = 0; i < save_context_set_count; ++i) {
        _zone_print1("context %s", _th_intern_decode(save_context_set[i])) ;
    }
    
    mark = _th_alloc_mark(MATCH_SPACE) ;
    
    c = 0 ;
    
    _th_init_find(&di, d, e) ;
    while (r = _th_next_find(&di,&priority)) {
        r_check_size(c+1) ;
        tries[c].e = r ;
        tries[c].priority = priority ;
        tries[c].is_context = 0 ;
        _zone_print_exp("Trying", r);
        ++c ;
    }

    _th_init_find_small(s, e, &iterator) ;
    while(r = _th_next_find_small(&iterator,&priority)) {
        if (r != _th_get_block_rule(env)) {
            r_check_size(c+1) ;
            tries[c].e = r ;
            tries[c].priority = priority ;
            tries[c].is_context = 1 ;
            ++c ;
        }
    }
    
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_ORIENTED_RULE && e->u.appl.count==3) {
        struct _ex_intern *e1 = _ex_intern_appl2_env(env, INTERN_EQUAL, e->u.appl.args[0], e->u.appl.args[1]) ;

        _th_init_find(&di, d, e1) ;
        while (r = _th_next_find(&di,&priority)) {
            r_check_size(c+1) ;
            tries[c].e = r ;
            tries[c].priority = priority ;
            tries[c].is_context = 0 ;
            ++c ;
        }

        _th_init_find_small(s, e1, &iterator) ;
        while(r = _th_next_find_small(&iterator,&priority)) {
            r_check_size(c+1) ;
            tries[c].e = r ;
            tries[c].priority = priority ;
            tries[c].is_context = 1 ;
            ++c ;
        }
    }

    qsort(tries,c,sizeof(struct _rule_try),cmp) ;
    rules = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * c) ;
    priorities = (int *)ALLOCA(sizeof(int) * c) ;
    is_context = (int *)ALLOCA(sizeof(int) * c) ;
    for (i = 0; i < c; ++i) {
        rules[i] = tries[i].e ;
        rules[i]->in_rewrite |= 0x80000000;
        priorities[i] = tries[i].priority ;
        is_context[i] = tries[i].is_context ;
    }
    for (i = 0; i < c; ++i) {
        if (rules[i]->in_rewrite & 0x80000000) {
            rules[i]->in_rewrite &= 0x7fffffff;
        } else {
            rules[i] = NULL;
        }
    }
    
    for (i = 0; ((!cut_flag || priorities[i] <= cut_priority) && i < c); ++i) {
        //_zone_print2("checking %s %d", _th_print_exp(rules[i]), do_transitive) ;
        if (rules[i]==NULL) goto cont2;
        //for (j = 0; j < i; ++j) {
        //    if (rules[i]==rules[j]) goto cont2;
        //}
        r = rules[i] ;
        if (r->u.appl.functor==INTERN_FORCE_ORIENTED && r->rule_in_use==MAX_IN_USE) {
            goto cont2 ;
        }
        ++r->rule_in_use ;
        cond = r->u.appl.args[2] ;
        if ((do_transitive & 4) && r->u.appl.args[1]==_ex_false) goto cont ;
        if ((do_transitive & 8) && r->u.appl.args[1]==_ex_true) goto cont ;
        if (cond->type==EXP_APPL && (cond->u.appl.functor==INTERN_NC_AND || cond->u.appl.functor==INTERN_ANDQ)) {
            for (j = 0; j < cond->u.appl.count; ++j) {
                cond2 = cond->u.appl.args[j] ;
                if (cond2->type==EXP_APPL && (cond2->u.appl.functor==INTERN_APPLY_CONTEXT || cond2->u.appl.functor==INTERN_IN_CONTEXT) && cond2->u.appl.count==1 &&
                    cond2->u.appl.args[0]->type==EXP_STRING) {
                    unsigned sym = _th_intern(cond2->u.appl.args[0]->u.string) ;
                    if (cond_level==0 && sym==INTERN_MAIN_CONTEXT) goto good ;
                    for (k = 0; k < save_context_set_count; ++k) {
                        if (sym==save_context_set[k]) goto good ;
                    }
                    goto cont ;
                } else if (cond2->type==EXP_APPL && cond2->u.appl.functor==INTERN_BLOCK_CONTEXT && cond2->u.appl.count==1 &&
                    cond2->u.appl.args[0]->type==EXP_STRING) {
                    unsigned sym = _th_intern(cond2->u.appl.args[0]->u.string) ;
                    if (cond_level==0 && sym==INTERN_MAIN_CONTEXT) goto cont ;
                    for (k = 0; k < save_context_set_count; ++k) {
                        if (sym==save_context_set[k]) goto cont ;
                    }
                    goto good ;
                } else if (cond2->u.appl.functor==INTERN_NESTING_LIMIT) {
                    unsigned x = cond2->u.integer[1] ;
                    if (r->rule_in_use > x) goto cont ;
                }
good: ;
            }
        }
        r = _th_augment_expression(env,r,e) ;
        _zone_print_exp("augment", r);
        if (r->u.appl.functor==INTERN_AND) {
            r2 = r->u.appl.args[1] ;
            r = r->u.appl.args[0] ;
        } else {
            r2 = NULL ;
        }
try_the_other:
        //_zone_print_exp("Matching", r->u.appl.args[0]);
        //_zone_print_exp("and", e);
        mr = _th_match(env, r->u.appl.args[0], e) ;
        if (mr && r->has_special_term) {
            //struct _ex_intern *r1;
            //printf("Name away %s\n", _th_print_exp(r));
            //printf("and %s\n", _th_print_exp(e));
            r = name_away_bv(env,r,e) ;
            //if (r1->u.appl.args[0]==NULL) {
            //    printf("Name away %s\n", _th_print_exp(r));
            //    printf("%s\n", _th_print_exp(e));
            //    printf("result: %s\n", _th_print_exp(r1));
            //   fflush(stdout);
            //}
            //r = r1;
            mr = _th_match(env,r->u.appl.args[0], e) ;
        }
        while (mr != NULL) {
            _zone_print2("Testing rule %s with priority %d", _th_print_exp(r), priorities[i]) ;
            _tree_indent() ;
            context_set_count = 0 ;
            if (is_context[i]) {
                _th_mark_tested(env, rules[i]) ;
            }
#ifdef _DEBUG
            if (_th_in_rewrite) {
                if (rules[i]->rule_try_count==0) {
                    rules[i]->next_rule = _th_top_rule ;
                    _th_top_rule = rules[i] ;
                }
                ++rules[i]->rule_try_count ;
            }
#endif
            if (rules[i]->u.appl.functor==INTERN_FORCE_ORIENTED) _th_violation_tested = _th_cycle ;
            if (r->u.appl.args[0]->type==EXP_APPL) {
                functor = r->u.appl.args[0]->u.appl.functor;
            } else {
                functor = 0;
            }
            if (u = test_condition(env, _th_subst(env,mr->theta,r->u.appl.args[2]), mr->theta, 0, 0, NULL, NULL, functor)) {
                if (is_context[i]) {
                    _th_mark_used(env, rules[i]) ;
                }
#ifdef _DEBUG
                if (_th_in_rewrite) ++rules[i]->rule_use_count ;
#endif
                if (rules[i]->u.appl.functor==INTERN_FORCE_ORIENTED) _th_violation_used = _th_cycle ;
                _zone_print_exp("Applying", r) ;
                levels = _th_exp_depth(r);
                r = _th_subst(env,u,r->u.appl.args[1]) ;
                //if (r->type == EXP_APPL && _th_is_ac(env,r->u.appl.functor)) {
                //    r = _th_flatten_top(env,r) ;
                //}
                r = _th_flatten_level(env,r,levels) ;
                _zone_print_exp("Rewriting", e) ;
                _zone_print_exp("to", r) ;
                _th_zone_print_unifier(u) ;
                _th_alloc_release(MATCH_SPACE,mark) ;
                _tree_undent() ;
                _tree_undent() ;
                cut_flag = save_cut_flag ;
                exclude_set_count = save_exclude_set_count ;
                for (j = 0; j < exclude_set_count; ++j) {
                    exclude_set[j] = save_exclude_set[j] ;
                }
                context_set_count = save_context_set_count ;
                for (j = 0; j < context_set_count; ++j) {
                    context_set[j] = save_context_set[j] ;
                }
                _th_limit_term = save_limit_term ;
                backchain_quant_level = back_chain_save ;
                --rules[i]->rule_in_use ;
                return r ;
            }
            cut_priority = priorities[i] ;
            mr = mr->next ;
            _tree_undent() ;
        }
        if (r2 != NULL) {
            r = r2 ;
            r2 = NULL ;
            goto try_the_other ;
        }
cont:;
        --rules[i]->rule_in_use ;
cont2:;
    }
    
    _th_alloc_release(MATCH_SPACE,mark) ;
    
    _tree_undent() ;
    
    cut_flag = save_cut_flag ;
    exclude_set_count = save_exclude_set_count ;
    for (i = 0; i < exclude_set_count; ++i) {
        exclude_set[i] = save_exclude_set[i] ;
    }
    context_set_count = save_context_set_count ;
    for (i = 0; i < context_set_count; ++i) {
        context_set[i] = save_context_set[i] ;
    }
    _th_limit_term = save_limit_term ;
    backchain_quant_level = back_chain_save ;
    return NULL ;
}

struct _ex_intern *_th_fast_rewrite_rule(struct env *env, struct _ex_intern *e, int do_transitive)
{
    struct small_disc *s = _th_get_forward_context_rules(env) ;
    struct match_return *mr ;
    struct _ex_intern *r;
    void *iterator ;
    char *mark ;
    int priority, c, i;
    struct _ex_intern *cond;
    int levels;
    //struct _ex_intern *br = _th_get_block_rule(env);
    //int noo = !_th_use_only_original(env);

    _zone_print_exp("Fast applying rules for", e) ;
    _tree_indent() ;
    //if (br) _zone_print_exp("block_rule", br);

    mark = _th_alloc_mark(MATCH_SPACE) ;
    
    c = 0 ;
    
    _th_init_find_small(s, e, &iterator) ;
    while(r = _th_next_find_small(&iterator,&priority)) {
        //_zone_print1("rule %d %s", _th_print_exp(r));
        if (!r->rule_blocked) {
            r_check_size(c+1) ;
            tries[c].e = r ;
            tries[c].e->in_rewrite |= 0x80000000;
            tries[c].priority = priority ;
            tries[c].is_context = 1 ;
            ++c ;
        }
    }
    
    for (i = 0; i < c; ++i) {
        r = tries[i].e ;
        cond = r->u.appl.args[2] ;
        if ((do_transitive & 4) && r->u.appl.args[1]==_ex_false) goto cont ;
        if ((do_transitive & 8) && r->u.appl.args[1]==_ex_true) goto cont ;
        _zone_print_exp("Matching", r->u.appl.args[0]);
        _zone_print_exp("and", e);
        mr = _th_match(env, r->u.appl.args[0], e) ;
        if (mr && r->has_special_term) {
            //struct _ex_intern *r1;
            //printf("Name away %s\n", _th_print_exp(r));
            //printf("and %s\n", _th_print_exp(e));
            r = name_away_bv(env,r,e) ;
            //if (r1->u.appl.args[0]==NULL) {
            //    printf("Name away %s\n", _th_print_exp(r));
            //    printf("%s\n", _th_print_exp(e));
            //    printf("result: %s\n", _th_print_exp(r1));
            //   fflush(stdout);
            //}
            //r = r1;
            mr = _th_match(env,r->u.appl.args[0], e) ;
        }
        while (mr != NULL) {
            _zone_print1("Testing rule %s", _th_print_exp(r)) ;
            _tree_indent() ;
#ifdef _DEBUG
            //if (_th_in_rewrite) {
            //    if (rules[i]->rule_try_count==0) {
            //        rules[i]->next_rule = _th_top_rule ;
            //        _th_top_rule = rules[i] ;
            //    }
            //    ++rules[i]->rule_try_count ;
            //}
#endif
            if (r->u.appl.args[2]==_ex_true) {
#ifdef _DEBUG
                //if (_th_in_rewrite) ++rules[i]->rule_use_count ;
#endif
                levels = _th_exp_depth(r);
                _zone_print_exp("Applying", r) ;
                r = _th_subst(env,mr->theta,r->u.appl.args[1]) ;
                //if (r->type == EXP_APPL && _th_is_ac(env,r->u.appl.functor)) {
                //    r = _th_flatten_top(env,r) ;
                //}
                r = _th_flatten_level(env,r,levels) ;
                _zone_print_exp("Rewriting", e) ;
                _zone_print_exp("to", r) ;
                _th_zone_print_unifier(mr->theta) ;
                _th_alloc_release(MATCH_SPACE,mark) ;
                _tree_undent() ;
                _tree_undent() ;
                return r ;
            }
            mr = mr->next ;
            _tree_undent() ;
        }
cont:;
    }
    
    _th_alloc_release(MATCH_SPACE,mark) ;
    
    _tree_undent() ;
    
    return NULL ;
}

void _th_remove_context(struct _ex_intern *e, int count, unsigned *index)
{
    int i, c ;
    unsigned *fv ;

    if (count > 0) {
        struct _ex_intern *term = _th_get_term(e, count-1, index) ;
        switch (term->type) {
            case EXP_QUANT:
                for (i = 0; i < e->u.quant.var_count; ++i) {
                    _th_intern_pop_quant(term->u.quant.vars[i]) ;
                }
                --_th_quant_level ;
                break ;
            case EXP_CASE:
                fv = _th_get_free_vars(e->u.case_stmt.args[index[count]-2], &c) ;
                for (i = 0; i < c; ++i) {
                    _th_intern_pop_quant(fv[i]) ;
                }
                --_th_quant_level ;
                break ;
        }
        _th_remove_context(e, count-1, index) ;
    }
}

void _th_create_context(int space, struct env *env, struct _ex_intern *e, int count, int *index)
{
    int i;
    struct _ex_intern *rule[3] ;

    if (count==0) return ;

    switch (e->type) {
        case EXP_APPL:
            switch(e->u.appl.functor) {
                case INTERN_ORIENTED_RULE:
                case INTERN_UNORIENTED_RULE:
                case INTERN_FORCE_ORIENTED:
                    if (index[0] < 2) {
                        rule[1] = rule[2] = _ex_true ;
                        rule[0] = _th_mark_vars(env,e->u.appl.args[2]) ;
                        _th_derive_and_add(env, _ex_intern_appl_env(env,INTERN_ORIENTED_RULE,3,rule)) ;
                    }
                    break ;
                case INTERN_AND:
                    for (i = 0; i < e->u.appl.count; ++i) {
                        rule[1] = rule[2] = _ex_true ;
                        if (i != index[0]) {
                            rule[0] = _th_mark_vars(env,e->u.appl.args[i]) ;
                            _th_derive_and_add(env, _ex_intern_appl_env(env,INTERN_ORIENTED_RULE,3,rule)) ;
                        }
                    }
                    break ;
                case INTERN_OR:
                    for (i = 0; i < e->u.appl.count; ++i) {
                        rule[1] = _ex_false ;
                        rule[2] = _ex_true ;
                        if (i != index[0]) {
                            rule[0] = _th_mark_vars(env,e->u.appl.args[i]) ;
                            _th_derive_and_add(env, _ex_intern_appl_env(env,INTERN_ORIENTED_RULE,3,rule)) ;
                        }
                    }
                    break ;
            }
            break ;
        case EXP_QUANT:
            ++_th_quant_level ;
            for (i = 0; i < e->u.quant.var_count; ++i) {
                _th_intern_push_quant(REWRITE_SPACE,e->u.quant.vars[i],_th_quant_level) ;
                _th_quant_add_context_rule(e->u.quant.vars[i],_th_quant_level) ;
            }
            break ;
        case EXP_CASE:
            if (index[0]>0 && index[0]%2==0) {
                int count ;
                unsigned *fv = _th_get_free_vars(e->u.case_stmt.args[index[0]-2], &count) ;
                rule[0] = _th_mark_vars(env,e->u.case_stmt.exp) ;
                ++_th_quant_level ;
                for (i = 0; i < count; ++i) {
                    _th_intern_push_quant(REWRITE_SPACE,fv[i],_th_quant_level) ;
                    _th_quant_add_context_rule(fv[i],_th_quant_level) ;
                }
                rule[1] = _th_mark_vars(env,e->u.case_stmt.args[index[0]-2]) ;
                rule[2] = _ex_true ;
                _th_derive_and_add(env,_ex_intern_appl_env(env,INTERN_ORIENTED_RULE,3,rule)) ;
            }
            break ;
    }

    e = _th_get_term(e,1,index) ;
    _th_create_context(space,env,e,count-1,index+1) ;
}

void _th_special_rewrite_rule(int space, struct env *env, struct _ex_intern *term, unsigned icount, unsigned *index)
{
    struct small_disc *s = _th_get_context_rules(env) ;
    struct disc *d = _th_get_all_rules(env) ;
    struct match_return *mr ;
    struct _ex_intern *r, *sub, *res, *e ;
    int count ;
    unsigned *fv ;
    int i ;
    void *iterator ;
    struct disc_iterator di ;
    char *mark, *rmark ;
    struct _ex_unifier *u ;
    unsigned functor;

    mark = _th_alloc_mark(MATCH_SPACE) ;
    rmark = _th_alloc_mark(REWRITE_SPACE) ;

    _zone_print_exp("Special rewrite", term) ;
    _tree_indent() ;

    _th_possibility_count = 0 ;

    _th_push_context() ;
    _th_create_context(space,env,term,icount,index) ;

    e = _th_get_term(term, icount, index) ;

    _th_init_find_small(s, e, &iterator) ;

    while(r = _th_next_find_small(&iterator,NULL)) {
        r = _th_augment_expression(env,r,e) ;
        mr = _th_match(env, r->u.appl.args[0], e) ;
        while(mr != NULL) {
            _zone_print_exp("Testing rule", r) ;
            _tree_indent() ;
            _zone_print_exp("Condition",_th_subst(env,mr->theta,r->u.appl.args[2])) ;
            if (r->u.appl.args[0]->type==EXP_APPL) {
                functor = r->u.appl.args[0]->u.appl.functor;
            } else {
                functor = 0;
            }
            if (u = test_condition(env, _th_subst(env,mr->theta,r->u.appl.args[2]), mr->theta, 0, 0, NULL, NULL, functor)) {
                sub = r->u.appl.args[1] ;
                fv = _th_get_free_vars(sub, &count) ;
                sub = _th_unmark_vars(env,sub) ;
                for (i = 0; i < count; ++i) {
                    if (!_th_is_free_in(r->u.appl.args[0], fv[i])) {
                        sub = _th_mark_var(env,sub,fv[i]) ;
                    }
                }
                res = _th_subst(env,u,sub) ;
                _th_check_possible_rewrites(_th_possibility_count+1) ;
                _th_possible_conditions[_th_possibility_count] = _ex_true ;
                res = _th_replace_term(env, term, icount, index, res) ;
                _th_possible_rewrites[_th_possibility_count] = _th_flatten(env,res) ;
                //if (res->type == EXP_APPL && _th_is_ac(env,res->u.appl.functor)) {
                //    _th_possible_rewrites[_th_possibility_count] = _th_flatten_top(env,res) ;
                //} else {
                //    _th_possible_rewrites[_th_possibility_count] = res ;
                //}
                _zone_print2("Adding result %d %s", _th_possibility_count, _th_print_exp(_th_possible_rewrites[_th_possibility_count])) ;
                ++_th_possibility_count ;
            }
            mr = mr->next ;
            _tree_undent() ;
        }
    }

    _th_init_find(&di, d, e) ;

    /*printf("Expression: %s\n", _th_print_exp(e)) ;*/
    while(r = _th_next_find(&di,NULL)) {
        /*printf("    Testing rule %s\n", _th_print_exp(r)) ;*/
        r = _th_augment_expression(env,r,e) ;
        /*printf("        Augment %s\n", _th_print_exp(r)) ;*/
        mr = _th_match(env, r->u.appl.args[0], e) ;
        /*printf("        mr = %d\n", mr) ;*/
        while (mr != NULL) {
            _zone_print_exp("Testing rule", r) ;
            _tree_indent() ;
            _zone_print_exp("Condition", _th_subst(env,mr->theta,r->u.appl.args[2])) ;
            if (r->u.appl.args[0]->type==EXP_APPL) {
                functor = r->u.appl.args[0]->u.appl.functor;
            } else {
                functor = 0;
            }
            if (u = test_condition(env, _th_subst(env,mr->theta,r->u.appl.args[2]), mr->theta, 0, 0, NULL, NULL, functor)) {
                sub = r->u.appl.args[1] ;
                fv = _th_get_free_vars(sub, &count) ;
                sub = _th_unmark_vars(env,sub) ;
                for (i = 0; i < count; ++i) {
                    if (!_th_is_free_in(r->u.appl.args[0], fv[i])) {
                        sub = _th_mark_var(env,sub,fv[i]) ;
                    }
                }
                res = _th_subst(env,u,sub) ;
                _th_check_possible_rewrites(_th_possibility_count+1) ;
                _th_possible_conditions[_th_possibility_count] = _ex_true ;
                res = _th_replace_term(env, term, icount, index, res) ;
                _th_possible_rewrites[_th_possibility_count] = _th_flatten(env,res) ;
                //if (res->type == EXP_APPL && _th_is_ac(env,res->u.appl.functor)) {
                //    _th_possible_rewrites[_th_possibility_count] = _th_flatten_top(env,res) ;
                //} else {
                //    _th_possible_rewrites[_th_possibility_count] = res ;
                //}
                _zone_print2("Adding %d %s", _th_possibility_count, _th_print_exp(_th_possible_rewrites[_th_possibility_count])) ;
                ++_th_possibility_count ;
            }
            mr = mr->next ;
            _tree_undent() ;
        }
    }

    _th_remove_context(term, icount, index) ;
    _th_pop_context() ;

    _th_alloc_release(MATCH_SPACE,mark) ;
    _th_alloc_release(REWRITE_SPACE,rmark) ;

    _tree_undent() ;
}

void _th_special_rewrite_rule_no_var(int space, struct env *env, struct _ex_intern *term, unsigned icount, unsigned *index)
{
    struct small_disc *s = _th_get_context_rules(env) ;
    struct disc *d = _th_get_all_rules(env) ;
    struct match_return *mr ;
    struct _ex_intern *r, *sub, *res, *e ;
    int count ;
    unsigned *fv ;
    int i ;
    void *iterator ;
    struct disc_iterator di ;
    char *mark, *rmark ;
    struct _ex_unifier *u ;
    unsigned functor;

    mark = _th_alloc_mark(MATCH_SPACE) ;
    rmark = _th_alloc_mark(REWRITE_SPACE) ;

    _zone_print_exp("Special rewrite", term) ;
    _tree_indent() ;

    _th_possibility_count = 0 ;
    _zone_print1("here-1 %d\n", _th_possibility_count) ;

    _th_push_context() ;
    _th_create_context(space,env,term,icount,index) ;

    e = _th_get_term(term, icount, index) ;

    _th_init_find_small(s, e, &iterator) ;

    while(r = _th_next_find_small(&iterator,NULL)) {
        //_zone_print1("here1 %d\n", _th_possibility_count) ;
        r = _th_augment_expression(env,r,e) ;
		if (r->u.appl.args[0]->type==EXP_VAR) continue;
        mr = _th_match(env, r->u.appl.args[0], e) ;
        while(mr != NULL) {
            _zone_print_exp("Testing rule", r) ;
            _tree_indent() ;
            _zone_print_exp("Condition",_th_subst(env,mr->theta,r->u.appl.args[2])) ;
            if (r->u.appl.args[0]->type==EXP_APPL) {
                functor = r->u.appl.args[0]->u.appl.functor;
            } else {
                functor = 0;
            }
            if (u = test_condition(env, _th_subst(env,mr->theta,r->u.appl.args[2]), mr->theta, 0, 0, NULL, NULL, functor)) {
                sub = r->u.appl.args[1] ;
                fv = _th_get_free_vars(sub, &count) ;
                sub = _th_unmark_vars(env,sub) ;
                for (i = 0; i < count; ++i) {
                    if (!_th_is_free_in(r->u.appl.args[0], fv[i])) {
                        sub = _th_mark_var(env,sub,fv[i]) ;
                    }
                }
                res = _th_subst(env,u,sub) ;
                _th_check_possible_rewrites(_th_possibility_count+1) ;
                _th_possible_conditions[_th_possibility_count] = _ex_true ;
                res = _th_replace_term(env, term, icount, index, res) ;
                _th_possible_rewrites[_th_possibility_count] = _th_flatten(env,res) ;
                //if (res->type == EXP_APPL && _th_is_ac(env,res->u.appl.functor)) {
                //    _th_possible_rewrites[_th_possibility_count] = _th_flatten_top(env,res) ;
                //} else {
                //    _th_possible_rewrites[_th_possibility_count] = res ;
                //}
                _zone_print2("Adding result %d %s", _th_possibility_count, _th_print_exp(_th_possible_rewrites[_th_possibility_count])) ;
                ++_th_possibility_count ;
                _zone_print1("here2 %d\n", _th_possibility_count) ;
            }
            mr = mr->next ;
            _tree_undent() ;
        }
    }
    _zone_print1("here3 %d\n", _th_possibility_count) ;

    _th_init_find(&di, d, e) ;

    /*printf("Expression: %s\n", _th_print_exp(e)) ;*/
    while(r = _th_next_find(&di,NULL)) {
        _zone_print1("here4 %d\n", _th_possibility_count) ;
        /*printf("    Testing rule %s\n", _th_print_exp(r)) ;*/
        r = _th_augment_expression(env,r,e) ;
		if (r->u.appl.args[0]->type==EXP_VAR) continue;
        /*printf("        Augment %s\n", _th_print_exp(r)) ;*/
        mr = _th_match(env, r->u.appl.args[0], e) ;
        /*printf("        mr = %d\n", mr) ;*/
        _zone_print1("here5 %d\n", _th_possibility_count) ;
        while (mr != NULL) {
            _zone_print1("here6 %d\n", _th_possibility_count) ;
            _zone_print_exp("Testing rule", r) ;
            _tree_indent() ;
            _zone_print1("here6.5 %d\n", _th_possibility_count) ;
            _zone_print_exp("Condition", _th_subst(env,mr->theta,r->u.appl.args[2])) ;
            _zone_print1("here7 %d\n", _th_possibility_count) ;
            if (r->u.appl.args[0]->type==EXP_APPL) {
                functor = r->u.appl.args[0]->u.appl.functor;
            } else {
                functor = 0;
            }
            if (u = test_condition(env, _th_subst(env,mr->theta,r->u.appl.args[2]), mr->theta, 0, 0, NULL, NULL, functor)) {
                sub = r->u.appl.args[1] ;
                fv = _th_get_free_vars(sub, &count) ;
                sub = _th_unmark_vars(env,sub) ;
                for (i = 0; i < count; ++i) {
                    if (!_th_is_free_in(r->u.appl.args[0], fv[i])) {
                        sub = _th_mark_var(env,sub,fv[i]) ;
                    }
                }
                res = _th_subst(env,u,sub) ;
                _th_check_possible_rewrites(_th_possibility_count+1) ;
                _th_possible_conditions[_th_possibility_count] = _ex_true ;
                res = _th_replace_term(env, term, icount, index, res) ;
                _th_possible_rewrites[_th_possibility_count] = _th_flatten(env,res) ;
                //if (res->type == EXP_APPL && _th_is_ac(env,res->u.appl.functor)) {
                //    _th_possible_rewrites[_th_possibility_count] = _th_flatten_top(env,res) ;
                //} else {
                //    _th_possible_rewrites[_th_possibility_count] = res ;
                //}
                _zone_print2("Adding %d %s", _th_possibility_count, _th_print_exp(_th_possible_rewrites[_th_possibility_count])) ;
                ++_th_possibility_count ;
            }
            _zone_print1("here8 %d\n", _th_possibility_count) ;
            mr = mr->next ;
            _tree_undent() ;
        }
    }

    _th_remove_context(term, icount, index) ;
    _th_pop_context() ;

    _th_alloc_release(MATCH_SPACE,mark) ;
    _th_alloc_release(REWRITE_SPACE,rmark) ;

    _tree_undent() ;
}

int _th_keep_inductive ;


void _th_cond_special_rewrite_rule(int space, struct env *env, struct _ex_intern *term, unsigned icount, unsigned *index)
{
    struct small_disc *s = _th_get_context_rules(env) ;
    struct disc *d = _th_get_all_rules(env) ;
    struct match_return *mr ;
    struct _ex_intern *r, *sub, *res, *e, *cond ;
    int count ;
    unsigned *fv ;
    int i ;
    void *iterator ;
    struct disc_iterator di ;
    char *mark, *rmark ;

    mark = _th_alloc_mark(MATCH_SPACE) ;
    rmark = _th_alloc_mark(REWRITE_SPACE) ;

    /*printf("Rewriting %s\n", _th_print_exp(e)) ;*/

    _th_possibility_count = 0 ;

    _th_push_context() ;
    _th_create_context(space,env,term,icount,index) ;

    fv = _th_get_free_vars(term, &count) ;
    _th_keep_inductive = 1 ;
    for (i = 0; i < count; ++i) {
        if (_th_intern_get_quant_level(fv[i])) {
            _th_keep_inductive = 0 ;
            break ;
        }
    }

    e = _th_get_term(term, icount, index) ;

    _th_init_find_small(s, e, &iterator) ;

    while(r = _th_next_find_small(&iterator,NULL)) {
        r = _th_augment_expression(env,r,e) ;
        mr = _th_match(env, r->u.appl.args[0], e) ;
        while(mr != NULL) {
            cond = r->u.appl.args[2] ;
            fv = _th_get_free_vars(cond, &count) ;
            cond = _th_unmark_vars(env,cond) ;
            for (i = 0; i < count; ++i) {
                if (!_th_is_free_in(r->u.appl.args[0], fv[i])) {
                    cond = _th_mark_var(env,cond,fv[i]) ;
                }
            }
            _th_check_possible_rewrites(_th_possibility_count+1) ;
            _th_possible_conditions[_th_possibility_count] = _th_subst(env,mr->theta,cond) ;
            sub = r->u.appl.args[1] ;
            fv = _th_get_free_vars(sub, &count) ;
            sub = _th_unmark_vars(env,sub) ;
            for (i = 0; i < count; ++i) {
                if (!_th_is_free_in(r->u.appl.args[0], fv[i])) {
                    sub = _th_mark_var(env,sub,fv[i]) ;
                }
            }
            res = _th_subst(env,mr->theta,sub) ;
            res = _th_replace_term(env, term, icount, index, res) ;
            _th_possible_rewrites[_th_possibility_count] = _th_flatten(env,res) ;
            //if (res->type == EXP_APPL && _th_is_ac(env,res->u.appl.functor)) {
            //    _th_possible_rewrites[_th_possibility_count] = _th_flatten_top(env,res) ;
            //} else {
            //    _th_possible_rewrites[_th_possibility_count] = res ;
            //}
            ++_th_possibility_count ;
            mr = mr->next ;
        }
    }

    _th_init_find(&di, d, e) ;

    /*printf("Expression: %s\n", _th_print_exp(e)) ;*/
    while(r = _th_next_find(&di,NULL)) {
        /*printf("    Testing rule %s\n", _th_print_exp(r)) ;*/
        r = _th_augment_expression(env,r,e) ;
        /*printf("        Augment %s\n", _th_print_exp(r)) ;*/
        mr = _th_match(env, r->u.appl.args[0], e) ;
        /*printf("        mr = %d\n", mr) ;*/
        while (mr != NULL) {
            cond = r->u.appl.args[2] ;
            fv = _th_get_free_vars(cond, &count) ;
            cond = _th_unmark_vars(env,cond) ;
            for (i = 0; i < count; ++i) {
                if (!_th_is_free_in(r->u.appl.args[0], fv[i])) {
                    cond = _th_mark_var(env,cond,fv[i]) ;
                }
            }
            _th_check_possible_rewrites(_th_possibility_count+1) ;
            _th_possible_conditions[_th_possibility_count] = _th_subst(env,mr->theta,cond) ;
            sub = r->u.appl.args[1] ;
            fv = _th_get_free_vars(sub, &count) ;
            sub = _th_unmark_vars(env,sub) ;
            for (i = 0; i < count; ++i) {
                if (!_th_is_free_in(r->u.appl.args[0], fv[i])) {
                    sub = _th_mark_var(env,sub,fv[i]) ;
                }
            }
            res = _th_subst(env,mr->theta,sub) ;
            res = _th_replace_term(env, term, icount, index, res) ;
            _th_possible_rewrites[_th_possibility_count] = _th_flatten(env,res) ;
            //if (res->type == EXP_APPL && _th_is_ac(env,res->u.appl.functor)) {
            //    _th_possible_rewrites[_th_possibility_count] = _th_flatten_top(env,res) ;
            //} else {
            //    _th_possible_rewrites[_th_possibility_count] = res ;
            //}
            ++_th_possibility_count ;
            mr = mr->next ;
        }
    }

    _th_remove_context(term, icount, index) ;
    _th_pop_context() ;

    _th_alloc_release(MATCH_SPACE, mark) ;
    _th_alloc_release(REWRITE_SPACE,rmark) ;
}

void _th_derive_rewrite_rule(int space, struct env *env, struct _ex_intern *e)
{
    struct disc *d = _th_get_derive_rules(env) ;
    struct match_return *mr ;
    struct _ex_intern *r, *sub, *res, *exp ;
    struct disc_iterator di ;
    char *mark, *rmark ;
    struct _ex_intern *priority = NULL ;
    struct _ex_unifier *u ;
    int i ;
    unsigned functor;

    mark = _th_alloc_mark(MATCH_SPACE) ;
    rmark = _th_alloc_mark(REWRITE_SPACE) ;
    
    _zone_print_exp("Derive rewrite", e) ;
    _tree_indent() ;
    
    _th_possibility_count = 0 ;
    
    _th_init_find(&di, d, e) ;
    
    while (e->type==EXP_APPL && e->u.appl.functor==INTERN_PRIORITY && e->u.appl.count==2) {
        priority = e->u.appl.args[0] ;
        e = e->u.appl.args[1] ;
    }
    
    /*printf("Expression: %s\n", _th_print_exp(e)) ;*/
    while(r = _th_next_find(&di,NULL)) {
        /*printf("    Testing rule %s\n", _th_print_exp(r)) ;*/
        r = _th_augment_expression(env,r,e) ;
        /*printf("        Augment %s\n", _th_print_exp(r)) ;*/
        mr = _th_match(env, r->u.appl.args[0], e) ;
        /*printf("        mr = %d\n", mr) ;*/
        while (mr != NULL) {
            _zone_print_exp("Testing rule", r) ;
            _tree_indent() ;
            _zone_print_exp("Condition", _th_subst(env,mr->theta,r->u.appl.args[2])) ;
            if (r->u.appl.args[0]->type==EXP_APPL) {
                functor = r->u.appl.args[0]->u.appl.functor;
            } else {
                functor = 0;
            }
            if (u = test_condition(env, (exp = _th_subst(env,mr->theta,r->u.appl.args[2])),mr->theta, 0, 0, NULL, NULL, functor)) {
                sub = r->u.appl.args[1] ;
                sub = _th_unmark_vars(env,sub) ;
                res = _th_subst(env,u,sub) ;
                _th_check_possible_rewrites(_th_possibility_count+1) ;
                _th_possible_conditions[_th_possibility_count] = _ex_true ;
                _th_possible_rewrites[_th_possibility_count] = _th_flatten(env,res) ;
                //if (res->type == EXP_APPL && _th_is_ac(env,res->u.appl.functor)) {
                //    _th_possible_rewrites[_th_possibility_count] = _th_flatten_top(env,res) ;
                //} else {
                //    _th_possible_rewrites[_th_possibility_count] = res ;
                //}
                if (priority) {
                    _th_possible_rewrites[_th_possibility_count] = _ex_intern_appl2_env(env,INTERN_PRIORITY,priority,_th_possible_rewrites[_th_possibility_count]) ;
                }
                for (i = 0; i < _th_possibility_count; ++i) {
                    if (_th_possible_rewrites[i]==_th_possible_rewrites[_th_possibility_count]) goto cont1;
                }
                _zone_print_exp("Adding", _th_possible_rewrites[_th_possibility_count]) ;
                ++_th_possibility_count ;
cont1:;
            }
            while (u && (u = retest_condition(env, exp, 0, 0, NULL, NULL, functor))) {
                sub = r->u.appl.args[1] ;
                sub = _th_unmark_vars(env,sub) ;
                res = _th_subst(env,u,sub) ;
                _th_check_possible_rewrites(_th_possibility_count+1) ;
                _th_possible_conditions[_th_possibility_count] = _ex_true ;
                _th_possible_rewrites[_th_possibility_count] = _th_flatten(env,res) ;
                //if (res->type == EXP_APPL && _th_is_ac(env,res->u.appl.functor)) {
                //    _th_possible_rewrites[_th_possibility_count] = _th_flatten_top(env,res) ;
                //} else {
                //    _th_possible_rewrites[_th_possibility_count] = res ;
                //}
                if (priority) {
                    _th_possible_rewrites[_th_possibility_count] = _ex_intern_appl2_env(env,INTERN_PRIORITY,priority,_th_possible_rewrites[_th_possibility_count]) ;
                }
                for (i = 0; i < _th_possibility_count; ++i) {
                    if (_th_possible_rewrites[i]==_th_possible_rewrites[_th_possibility_count]) goto cont2;
                }
                _zone_print_exp("Adding", _th_possible_rewrites[_th_possibility_count]) ;
                ++_th_possibility_count ;
cont2:;
            }
            mr = mr->next ;
            _tree_undent() ;
        }
    }
    
    _th_alloc_release(MATCH_SPACE,mark) ;
    _th_alloc_release(REWRITE_SPACE,rmark) ;
    
    _tree_undent() ;
}

struct _ex_intern *_th_gargs = NULL ;
struct _ex_intern *_th_current_exp = NULL ;

int _th_on_add_list(struct env *env, struct add_list *al, struct _ex_intern *e)
{
    while (al) {
        if (_th_equal(env,e,al->e)) return 1 ;
        al = al->next ;
    }
    return 0 ;
}

int valid_operator(struct env *env, struct _ex_intern *e, struct add_list *al)
{
    int i, j ;

    _zone_print_exp("Testing", e) ;
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_ADD) {

        e = e->u.appl.args[0] ;
        goto add_test ;

    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_DELETE) {

        e = e->u.appl.args[0] ;

        for (i = 0; i < _th_gargs->u.appl.count; ++i) {
            if (_th_equal(env, e, _th_gargs->u.appl.args[i])) {
                return 1 ;
            }
        }

        _zone_print0("fail") ;
        return 0 ;

    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_REPLACE) {

        for (i = 0; i < _th_gargs->u.appl.count; ++i) {
            if (_th_equal(env, e->u.appl.args[0], _th_gargs->u.appl.args[i])) {
                e = e->u.appl.args[1] ;
                goto add_test ;
            }
        }

        _zone_print0("fail") ;
        return 0 ;
    }

add_test:
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_AND) {
        for (j = 0; j < e->u.appl.count; ++j) {
            for (i = 0; i < _th_gargs->u.appl.count; ++i) {
                if (_th_equal(env, e->u.appl.args[j], _th_gargs->u.appl.args[i])) {
                    goto cont ;
                }
            }
            if (_th_on_add_list(env, al, e->u.appl.args[j])) goto cont ;
            return 1 ;
cont: ;
        }
        _zone_print0("fail") ;
        return 0 ;
    } else {
        for (i = 0; i < _th_gargs->u.appl.count; ++i) {
            if (_th_equal(env, e, _th_gargs->u.appl.args[i])) {
                _zone_print0("fail") ;
                return 0 ;
            }
        }
        if (_th_on_add_list(env, al, e)) return 0 ;
    }
    
    return 1 ;
}

struct change_list *_th_change_list ;

struct add_list *_th_apply_inference_rule(struct env *env, struct _ex_intern *e, int count, struct _ex_intern **args, struct add_list *al, struct change_list *changes, struct add_list *tail, int min, int max, int n, struct _ex_intern **derives)
{
    struct disc *d = _th_get_augment_rules(env) ;
    struct match_return *mr ;
    struct _ex_intern *r, *r2 ;
    struct disc_iterator di ;
    char *mark ;
    int save_cut_flag = cut_flag ;
    int priority, c, i ;
    struct _ex_intern **rules ;
    int *priorities ;
    int cut_priority ;
    struct _ex_unifier *u ;
    struct _ex_intern *gargs_save = _th_gargs ;
    struct _ex_intern *current_exp_save = _th_current_exp ;
    struct _ex_intern *cond ;
    struct change_list *cl = NULL, *change_list = NULL ;
    int save_context_set_count = context_set_count ;
    unsigned save_context_set[CONTEXT_LIMIT] ;
    struct _ex_intern **args_set = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count) ;
    unsigned functor;

    for (i = 0; i < save_context_set_count; ++i) {
        save_context_set[i] = context_set[i] ;
    }

    cut_flag = 0 ;
    
    //_th_print_disc(d) ;
    
    for (i = 0; i < count; ++i) args_set[i] = args[i] ;
    _th_gargs = _ex_intern_appl_env(env,INTERN_SET,count,args_set) ;
    _th_current_exp = e ;
    
    _zone_print_exp("Applying rules for", e) ;
    _tree_indent() ;
    
    mark = _th_alloc_mark(MATCH_SPACE) ;
    
    if (changes == NULL) {
        
        c = 0 ;
        
        _th_init_find(&di, d, e) ;
        while (r = _th_next_find(&di,&priority)) {
            r_check_size(c+1) ;
            tries[c].e = r ;
            tries[c].priority = priority ;
            //printf("rule = %s\n", _th_print_exp(r)) ;
            ++c ;
        }
        qsort(tries,c,sizeof(struct _rule_try),cmp) ;
        rules = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * c) ;
        priorities = (int *)ALLOCA(sizeof(int) * c) ;
        //printf("c = %d\n", c) ;
        for (i = 0; i < c; ++i) {
            rules[i] = tries[i].e ;
            priorities[i] = tries[i].priority ;
        }
        
        cut_priority = -32767 ;
        for (i = 0; ((!cut_flag || priorities[i] <= cut_priority) && i < c); ++i) {
            if (priorities[i] >= min && priorities[i] <= max) {
                r = rules[i] ;
                r = _th_augment_expression(env,r,e) ;
                if (r->u.appl.functor==INTERN_AND) {
                    r2 = r->u.appl.args[1] ;
                    r = r->u.appl.args[0] ;
                } else {
                    r2 = NULL ;
                }
try_other:
                //printf("Matching %s", _th_print_exp(r)) ;
                //printf(" and %s\n", _th_print_exp(e)) ;
                mr = _th_match(env, r->u.appl.args[0], e) ;
                if (r->u.appl.args[0]->type==EXP_APPL) {
                    functor = r->u.appl.args[0]->u.appl.functor;
                } else {
                    functor = 0;
                } 
                _zone_print2("r = %s mr = %d\n", _th_print_exp(r), mr) ;
                _zone_print_exp("e =", e) ;
                while (mr != NULL) {
                    _zone_print_exp("Testing rule", r) ;
                    _tree_indent() ;
                    cond = _th_subst(env,mr->theta,r->u.appl.args[2]) ;
                    if (cond->type==EXP_APPL && cond->u.appl.count==2 && cond->u.appl.functor==INTERN_FIRE_ON_CHANGE) {
                        cl = (struct change_list *)_th_alloc(REWRITE_SPACE,sizeof(struct change_list)) ;
                        _zone_print_exp("Adding change", r) ;
                        cl->next = change_list ;
                        cl->terms = cond->u.appl.args[0] ;
                        cl->rule = r ;
                        cl->execute = 0 ;
                        change_list = cl ;
                        cond = cond->u.appl.args[1] ;
                    }
                    context_set_count = 0 ;
                    //_zone_enter_sub() ;
                    u = test_condition(env, cond, mr->theta, count, n, args, derives, functor) ;
                    //_zone_exit_sub() ;
                    _zone_print1("u = %d", u) ;
                    do {
                        struct _ex_intern *res ;
                        if (u==NULL) break ;
                        res = _th_subst(env,u,r->u.appl.args[1]) ;
                        //_zone_print1("res = %s", _th_print_exp(res)) ;
                        if (valid_operator(env, res, al)) {
                            struct add_list *a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list)) ;
                            res = _th_flatten(env,res) ;
                            //if (res->type == EXP_APPL && _th_is_ac(env,res->u.appl.functor)) {
                            //    res = _th_flatten_top(env,res) ;
                            //}
                            //_zone_print1("Augmenting with %s", _th_print_exp(res)) ;
                            a->next = tail ;
                            tail = a ;
                            a->e = res ;
                        }
                        u = retest_condition(env, cond, count, n, args, derives, functor) ;
                    } while (u != NULL) ;
                    cut_priority = priorities[i] ;
                    mr = mr->next ;
                    _tree_undent() ;
                }
                if (r2 != NULL) {
                    r = r2 ;
                    r2 = NULL ;
                    goto try_other ;
                }
            }
        }
    } else {
        while (changes != NULL) {
            _zone_print_exp("Rule:", changes->rule) ;
            _zone_print_exp("Changes", changes->terms) ;
            if (changes->execute) {
                r = changes->rule ;
                mr = _th_match(env, r->u.appl.args[0], e) ;
                if (r->u.appl.args[0]->type==EXP_APPL) {
                    functor = r->u.appl.args[0]->u.appl.functor;
                } else {
                    functor = 0;
                }
                _zone_print2("r = %s mr = %d\n", _th_print_exp(r), mr) ;
                _zone_print_exp("e =", e) ;
                while (mr != NULL) {
                    _zone_print_exp("Testing rule", r) ;
                    _tree_indent() ;
                    cond = _th_subst(env,mr->theta,r->u.appl.args[2]) ;
                    if (cond->type==EXP_APPL && cond->u.appl.count==2 && cond->u.appl.functor==INTERN_FIRE_ON_CHANGE) {
                        cl = (struct change_list *)_th_alloc(REWRITE_SPACE,sizeof(struct change_list)) ;
                        cl->next = change_list ;
                        cl->terms = cond->u.appl.args[0] ;
                        cl->rule = r ;
                        cl->execute = 0 ;
                        change_list = cl ;
                        cond = cond->u.appl.args[1] ;
                    }
                    //_zone_enter_sub() ;
                    u = test_condition(env, cond, mr->theta, count, n, args, derives, functor) ;
                    //_zone_exit_sub();
                    _zone_print1("u = %d", u) ;
                    do {
                        struct _ex_intern *res ;
                        if (u==NULL) break ;
                        res = _th_subst(env,u,r->u.appl.args[1]) ;
                        if (valid_operator(env, res, al)) {
                            struct add_list *a = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list)) ;
                            res = _th_flatten(env,res) ;
                            //if (res->type == EXP_APPL && _th_is_ac(env,res->u.appl.functor)) {
                            //    res = _th_flatten_top(env,res) ;
                            //}
                            _zone_print_exp("Augmenting with", res) ;
                            a->next = tail ;
                            tail = a ;
                            a->e = res ;
                        }
                        u = retest_condition(env, cond, count, n, args, derives, functor) ;
                    } while (u != NULL) ;
                    mr = mr->next ;
                    _tree_undent() ;
                }
            }
            changes = changes->next ;
        }
    }
    _th_alloc_release(MATCH_SPACE,mark) ;
    
    _tree_undent() ;
    
    cut_flag = save_cut_flag ;
    _th_gargs = gargs_save ;
    _th_current_exp = current_exp_save ;
    context_set_count = save_context_set_count ;
    for (i = 0; i < context_set_count; ++i) {
        context_set[i] = save_context_set[i] ;
    }

    _th_change_list = change_list ;
    return tail ;
}

struct _ex_intern *_th_macro_expand(struct env *env, struct _ex_intern *e, struct _ex_intern *tail)
{
    struct disc *d = _th_get_macro_rules(env) ;
    struct match_return *mr ;
    struct _ex_intern *r ;
    struct disc_iterator di ;
    char *mark ;
    int save_cut_flag = cut_flag ;
    int priority, c, i ;
    struct _ex_intern **rules ;
    int *priorities ;
    int cut_priority ;
    struct _ex_unifier *u ;
    struct _ex_intern *current_exp_save = _th_current_exp ;
    struct _ex_intern *cond ;
    int save_context_set_count = context_set_count ;
    unsigned save_context_set[CONTEXT_LIMIT] ;
    struct add_list *al = NULL ;
    unsigned functor;

    for (i = 0; i < save_context_set_count; ++i) {
        save_context_set[i] = context_set[i] ;
    }

    cut_flag = 0 ;
    

    //_th_print_disc(d) ;
    
    _tree_print_exp("Expanding macro", e);
    _tree_indent() ;
    
    mark = _th_alloc_mark(MATCH_SPACE) ;
    
    c = 0 ;
    
    _th_init_find(&di, d, e) ;
    while (r = _th_next_find(&di,&priority)) {
        r_check_size(c+1) ;
        tries[c].e = r ;
        tries[c].priority = priority ;
        //printf("rule = %s\n", _th_print_exp(r)) ;
        ++c ;
    }
    qsort(tries,c,sizeof(struct _rule_try),cmp) ;
    rules = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * c) ;
    priorities = (int *)ALLOCA(sizeof(int) * c) ;
    //printf("c = %d\n", c) ;
    for (i = 0; i < c; ++i) {
        rules[i] = tries[i].e ;
        priorities[i] = tries[i].priority ;
    }
    
    for (i = 0; i < c; ++i) {
        r = rules[i] ;
        if (r->u.appl.args[0]->type==EXP_APPL) {
            functor = r->u.appl.args[0]->u.appl.functor;
        } else {
            functor = 0;
        }
        r = _th_augment_expression(env,r,e) ;
        //printf("Matching %s", _th_print_exp(r)) ;
        //printf(" and %s\n", _th_print_exp(e)) ;
        mr = _th_match(env, r->u.appl.args[0], e) ;
        _zone_print2("r = %s mr = %d\n", _th_print_exp(r), mr) ;
        _zone_print_exp("e =", e) ;
        while (mr != NULL) {
            _zone_print_exp("Testing rule", r) ;
            _tree_indent() ;
            cond = _th_subst(env,mr->theta,r->u.appl.args[2]) ;
            context_set_count = 1 ;
            context_set[0] = INTERN_MACRO_CONTEXT ;
            u = test_condition(env, cond, mr->theta, 0, 0, NULL, NULL, functor) ;
            do {
                struct _ex_intern *res ;
                struct add_list *a = (struct add_list *)ALLOCA(sizeof(struct add_list)) ;
                a->next = al ;
                if (u==NULL) break ;
                res = _th_subst(env,u,r->u.appl.args[1]) ;
                _zone_print_exp("Adding", res) ;
                a->e = res ;
                al = a ;
                u = retest_condition(env, cond, 0, 0, NULL, NULL, functor) ;
            } while (u != NULL) ;
            cut_priority = priorities[i] ;
            mr = mr->next ;
            _tree_undent() ;
        }
    }
    
    _th_alloc_release(MATCH_SPACE,mark) ;
    
    while (al != NULL) {
        _zone_print_exp("Processing", al->e) ;
        if (al->e->type==EXP_APPL && al->e->u.appl.functor==INTERN_ADD &&
            al->e->u.appl.count==1) {
            r = al->e->u.appl.args[0] ;
            if (r->type==EXP_APPL && r->u.appl.functor==INTERN_QUOTE && r->u.appl.count==1) r = r->u.appl.args[0] ;
            _th_derive_and_add_property(ENVIRONMENT_SPACE,env,r) ;
        } else if (al->e->type==EXP_APPL && (al->e->u.appl.functor==INTERN_CONS || al->e->u.appl.functor==INTERN_APPEND)) {
            tail = _ex_intern_appl2_env(env,INTERN_APPEND,al->e,tail) ;
            tail = _th_int_rewrite(env,tail,0) ;
        } else {
            tail = _ex_intern_appl2_env(env,INTERN_CONS,al->e,tail) ;
        }
        al = al->next ;
    }

    cut_flag = save_cut_flag ;
    context_set_count = save_context_set_count ;
    for (i = 0; i < context_set_count; ++i) {
        context_set[i] = save_context_set[i] ;
    }

    _tree_undent() ;
    
    return tail ;
}

