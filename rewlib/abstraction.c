/*
 * abstraction.c
 *
 * Routines for abstraction subterms of a rule.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdio.h>
#include <stdlib.h>
#include "Globals.h"
#include "Intern.h"


#define PARENT_BOOL  0
#define PARENT_EUF   1
#define PARENT_ARITH 2
#define PARENT_ARRAY 3
#define PARENT_NONE  4
#define PARENT_SOME  5

int _th_enable_abstraction = 1;

static int is_bool(struct _ex_intern *e)
{
    int functor;

    if (e->type != EXP_APPL) return 0;

    functor = e->u.appl.functor;

    return functor==INTERN_AND || functor==INTERN_OR || functor==INTERN_XOR || functor==INTERN_NOT ||
           functor==INTERN_EQUAL || functor==INTERN_ORIENTED_RULE || functor==INTERN_NAT_LESS ||
           functor==INTERN_RAT_LESS;
}

static int is_arith(struct _ex_intern *e)
{
    int functor;

    if (e->type != EXP_APPL) return 0;

    functor = e->u.appl.functor;

    return functor==INTERN_NAT_PLUS || functor==INTERN_NAT_TIMES || functor==INTERN_NAT_MOD ||
           functor==INTERN_NAT_DIVIDE || functor==INTERN_RAT_PLUS || functor==INTERN_RAT_TIMES ||
           functor==INTERN_RAT_DIVIDE || functor==INTERN_RAT_MOD;
}

struct _ex_intern *abstract_condition(struct env *env, struct _ex_intern *e, int parent_mode);

static struct _ex_intern *make_abstraction(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *var = _th_get_root(ENVIRONMENT_SPACE,env,e);
    //struct _ex_intern *rule = _ex_intern_appl2_env(env,INTERN_EQUAL,var,e);

    _zone_print_exp("Adding", e);
    _zone_print_exp("as", var);

    //_th_assert_predicate(env,abstract_condition(env,rule,PARENT_NONE));

    return var;
}

struct _ex_intern *abstract_condition(struct env *env, struct _ex_intern *e, int parent_mode)
{
    int i;
    struct _ex_intern **args;
    int mode;

    _zone_print_exp("Abstracting", e);
    if (_th_enable_abstraction==0 || e->type != EXP_APPL) return e;

    if (parent_mode==PARENT_NONE || !_th_uninterpreted_functor(e->u.appl.functor)) {
        if ((e->u.appl.functor==INTERN_EQUAL || e->u.appl.functor==INTERN_ORIENTED_RULE) &&
            (e->u.appl.args[0]->type != EXP_APPL || e->u.appl.args[1]->type != EXP_APPL ||
             e->u.appl.args[1]==_ex_true || e->u.appl.args[1]==_ex_false ||
             e->u.appl.args[0]==_ex_true || e->u.appl.args[0]==_ex_false)) {
            mode = PARENT_NONE;
        } else if (parent_mode==PARENT_NONE && e->u.appl.functor==INTERN_NOT) {
            mode = PARENT_NONE;
        } else {
            mode = PARENT_SOME;
        }
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = abstract_condition(env,e->u.appl.args[i],mode);
        }
        return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
    }

    return make_abstraction(env,e);
#ifdef OLD
    int do_abstraction = 0;
    int functor;
    int change, i, mode;
    struct _ex_intern **args;

    switch (e->type) {
        case EXP_APPL:
            if (e==_ex_true || e==_ex_false) return e;
            functor = e->u.appl.functor;
            switch (parent_mode) {
                case PARENT_BOOL:
                    if (functor==INTERN_EQUAL || functor==INTERN_ORIENTED_RULE) {
                        do_abstraction = !is_bool(e->u.appl.args[0]) && !is_bool(e->u.appl.args[1]);
                    } else {
                        do_abstraction = (functor != INTERN_AND && functor != INTERN_NOT &&
                                          functor != INTERN_OR && functor != INTERN_XOR &&
                                          functor != INTERN_ITE);
                    }
                    break;
                case PARENT_EUF:
                    do_abstraction = 1;
                    break;
                case PARENT_ARITH:
                    do_abstraction = (functor != INTERN_NAT_PLUS && functor != INTERN_NAT_TIMES &&
                                      functor != INTERN_NAT_DIVIDE && functor != INTERN_NAT_MOD &&
                                      functor != INTERN_RAT_PLUS && functor != INTERN_RAT_TIMES &&
                                      functor != INTERN_RAT_DIVIDE && functor != INTERN_RAT_MOD &&
                                      functor != INTERN_NAT_TO_RAT && functor != INTERN_RAT_TO_NAT);
                    break;
                case PARENT_ARRAY:
                    do_abstraction = (functor != INTERN_STORE && functor != INTERN_SELECT);
                    break;
                    
            }
            if (do_abstraction) {
                return make_abstraction(env,e);
            }
            switch (e->u.appl.functor) {
                case INTERN_AND:
                case INTERN_OR:
                case INTERN_XOR:
                case INTERN_NOT:
                case INTERN_ITE:
                    mode = PARENT_BOOL;
                    break;
                case INTERN_NAT_PLUS:
                case INTERN_RAT_PLUS:
                case INTERN_NAT_TIMES:
                case INTERN_RAT_TIMES:
                case INTERN_NAT_DIVIDE:
                case INTERN_RAT_DIVIDE:
                case INTERN_NAT_MOD:
                case INTERN_RAT_MOD:
                    mode = PARENT_ARITH;
                    break;
                case INTERN_EQUAL:
                    if (e->type_inst==_ex_real || e->type_inst==_ex_int ||
                        is_arith(e->u.appl.args[0]) || is_arith(e->u.appl.args[1])) {
                        mode = PARENT_ARITH;
                    } else if (e->type_inst==_ex_bool || is_bool(e->u.appl.args[0]) ||
                        is_bool(e->u.appl.args[1])) {
                        mode = PARENT_BOOL;
                    } else {
                        mode = PARENT_EUF;
                    }
                default:
                    mode = PARENT_EUF;
            }
            change = 0;
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            for (i = 0; i < e->u.appl.count; ++i) {
                if (i==1 && functor==INTERN_ITE) mode = parent_mode;
                if (change) {
                    args[i] = abstract_condition(env,_th_nc_rewrite(env,e->u.appl.args[i]),mode);
                } else {
                    args[i] = abstract_condition(env,e->u.appl.args[i],mode);
                    if (args[i] != e->u.appl.args[i]) change = 1;
                }
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
        case EXP_QUANT:
            return make_abstraction(env,e);
        default:
            return e;
    }
#endif
}

struct _ex_intern *_th_abstract_condition(struct env *env, struct _ex_intern *e)
{
    return abstract_condition(env, e, PARENT_NONE);
}
