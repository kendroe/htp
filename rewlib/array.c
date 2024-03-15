/*
 * array.c
 *
 * Routines for handling array expressions
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"

struct _ex_intern *_th_simplify_select(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *f = e->u.appl.args[0];
#ifdef ORIG
    if (f->type==EXP_APPL && f->u.appl.functor==INTERN_STORE) {
        struct _ex_intern *test = _ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[1],f->u.appl.args[1]);
        test = _th_nc_rewrite(env,test);
        if (test==_ex_true) {
            return f->u.appl.args[2];
        } else if (test==_ex_false) {
            return _ex_intern_appl2_env(env,INTERN_SELECT,f->u.appl.args[0],e->u.appl.args[1]);
        }
    }
#endif
    if (f->type==EXP_APPL && f->u.appl.functor==INTERN_STORE) {
        struct _ex_intern *test = _ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[1],f->u.appl.args[1]);
        return _ex_intern_appl3_env(env,INTERN_ITE,
                    test,
                    f->u.appl.args[2],
                    _ex_intern_appl2_env(env,INTERN_SELECT,f->u.appl.args[0],e->u.appl.args[1]));
    }
    return NULL;
}

struct _ex_intern *_th_simplify_store(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *f = e->u.appl.args[2];

    if (f->type==EXP_APPL && f->u.appl.functor==INTERN_SELECT) {
        if (f->u.appl.args[0]==e->u.appl.args[0] && f->u.appl.args[1]==e->u.appl.args[1]) {
            return e->u.appl.args[0];
        }
    }

    f = e->u.appl.args[0];
    if (f->type==EXP_APPL && f->u.appl.functor==INTERN_STORE &&
        ((int)f->u.appl.args[1]) > ((int)e->u.appl.args[1]) &&
        _th_nc_rewrite(env,_ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[1],f->u.appl.args[1]))==_ex_false) {
        return _ex_intern_appl3_env(env,INTERN_STORE,
                   _ex_intern_appl3_env(env,INTERN_STORE,f->u.appl.args[0],e->u.appl.args[1],e->u.appl.args[2]),
                   f->u.appl.args[1],
                   f->u.appl.args[2]);
    }
    return NULL;
}

struct _ex_intern *_th_simplify_array_equality(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *l = e->u.appl.args[0];
    struct _ex_intern *r = e->u.appl.args[1];

    if (l->type != EXP_APPL || r->type != EXP_APPL ||
        l->u.appl.functor != INTERN_STORE || r->u.appl.functor != INTERN_STORE) {
        return NULL;
    }

    if (l->u.appl.args[1]==r->u.appl.args[1]) {
        return _ex_intern_appl2_env(env,INTERN_AND,
                   _ex_intern_appl2_env(env,INTERN_EQUAL,l->u.appl.args[2],r->u.appl.args[2]),
                   _ex_intern_appl3_env(env,INTERN_EE,l->u.appl.args[0],r->u.appl.args[0],l->u.appl.args[1]));
    }

    return NULL;
}

struct _ex_intern *_th_simplify_ee(struct env *env, struct _ex_intern *e)
{
    int i, j;
    struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
    struct rule *cr;
    struct _ex_intern *r;

    if (e->u.appl.args[0]==e->u.appl.args[1]) return _ex_true;

    args[0] = e->u.appl.args[0];
    args[1] = e->u.appl.args[1];

    for (j = 2, i = 2; i < e->u.appl.count; ++i) {
        if (i==2 || e->u.appl.args[i] != e->u.appl.args[i-1]) {
            args[j++] = e->u.appl.args[i];
        }
    }

    if (i != j) return _ex_intern_appl_env(env,INTERN_EE,j,args);

    if (((int)args[1]) < ((int)args[0])) {
        struct _ex_intern *x = args[0];
        args[0] = args[1];
        args[1] = x;
        for (i = 2; i < e->u.appl.count; ++i) {
            args[i] = e->u.appl.args[i];
        }
        return _ex_intern_appl_env(env,INTERN_EE,e->u.appl.count,args);
    }

    r = _th_get_first_context_rule(env,&cr);
    while (r) {
        if (r->u.appl.args[0]->type==EXP_APPL &&
            r->u.appl.args[1]==_ex_true && r->u.appl.args[0]->u.appl.functor==INTERN_EE &&
            r->u.appl.args[0]->u.appl.args[0]==_th_mark_vars(env,e->u.appl.args[0]) &&
            r->u.appl.args[0]->u.appl.args[1]==_th_mark_vars(env,e->u.appl.args[1])) {
            for (i = 2, j = 2; i < e->u.appl.count; ++i) {
                if (j < r->u.appl.args[0]->u.appl.count &&
                    _th_mark_vars(env,e->u.appl.args[i])==r->u.appl.args[0]->u.appl.args[j]) {
                    ++j;
                }
            }
            if (j==r->u.appl.args[0]->u.appl.count) return _ex_true;
        }
        r = _th_get_next_rule(env,&cr);
    }

    return NULL;
}
