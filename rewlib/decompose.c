/*
 * decompose.c
 *
 * Routines for decomposing complex expressions.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"
#include "Doc.h"

static int vn = 1;

struct _ex_intern *trail;

GDEF("invariant tree_path trail next_cache *");
GDEF("invariant SET(trail next_cache *) subset SET(_ex_set)");
GDEF("invariant ALL(x in SET(_ex_set) - SET(trail next_cache *)) x->user2==NULL");
GDEF("invariant ALL(x in SET(_ex_set) - SET(trail next_cache *)) x->user3==NULL");

static int term_in_trail(struct _ex_intern *e)
{
    struct _ex_intern *t = trail;

    while (t) {
        if (t==e) return 1;
        t = t->next_cache;
    }

    return 0;
}

static struct _ex_intern *invert(struct env *env, struct _ex_intern *e)
{
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        return e->u.appl.args[0];
    } else {
        return _ex_intern_appl1_env(env,INTERN_NOT,e);
    }
}

static struct _ex_intern *get_type(struct env *env, struct _ex_intern *exp)
{
    struct _ex_intern *t;

    switch (exp->type) {
        case EXP_INTEGER:
            return _ex_int;
            break;
        case EXP_RATIONAL:
            return _ex_real;
            break;
        case EXP_VAR:
            return _th_get_var_type(env,exp->u.var);
            break;
        case EXP_APPL:
            if (exp->u.appl.functor==INTERN_ITE) {
                t = get_type(env,exp->u.appl.args[1]);
                return t;
            } else {
                t = _th_get_type(env,exp->u.appl.functor);
                return t->u.appl.args[1];
            }
            break;
        default:
            return NULL;
    }
}

static struct _ex_intern *get_var(struct env *env, struct _ex_intern *type)
{
    char name[10];

    sprintf(name, "cnf_%d", vn++);
    _th_set_var_type(env,_th_intern(name),type);
    return _ex_intern_var(_th_intern(name));
}

static struct _ex_intern *variablize(struct env *env, struct learn_info *info, struct _ex_intern *e, struct parent_list *list);

//static int checkit = 0;

static struct _ex_intern *remove_nested_ite(struct env *env, struct learn_info *info, struct parent_list *list, struct _ex_intern *e)
{
    int i;
    struct _ex_intern **args;
    struct _ex_intern *eq;

    //if (checkit && !term_in_trail(0xa2aa874)) {
    //    printf("Fail 1b\n");
    //    exit(1);
    //}
    if (e->type != EXP_APPL) return e;

    if (e->user3) {
        //struct _ex_intern *r = trail;
        //while (r) {
        //    if (r==e) goto cont;
        //    r = r->next_cache;
        //}
        //fprintf(stderr, "Error: term not in trail %s\n", _th_print_exp(e));
        //fprintf(stderr, "User2: %s\n", _th_print_exp(e->user2));
        //exit(1);
//cont:
        return e->user3;
    }

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);

    //printf("Here0\n");
    //if (checkit && !term_in_trail(0xa2aa874)) {
    //    printf("Fail 1bb\n");
    //    exit(1);
    //}
    if (e->u.appl.functor==INTERN_ITE) {
        struct _ex_intern *vtype = get_type(env,e->u.appl.args[1]);
        struct _ex_intern *v = get_var(env, vtype);
        struct _ex_intern *c;
        //++_th_block_complex;
        //printf("Here1\n");
        //_zone_print_exp("Nested ite", e);
        //_zone_print_exp("user2", e->u.appl.args[0]->user2);
        //printf("Abstracting ite %s\n", _th_print_exp(e));
        //printf("type %s\n", _th_print_exp(get_type(env,e->u.appl.args[1])));
        //printf("var = %s\n", _th_print_exp(v));
        //--_th_block_complex;
        //if (checkit && !term_in_trail(0xa2aa874)) {
        //    printf("Fail 1c\n");
        //    exit(1);
        //}
        //if (checkit && !term_in_trail(0xa2aa874)) {
        //    printf("Fail 1d\n");
        //    exit(1);
        //}
        c = args[0] = variablize(env,info,e->u.appl.args[0],list);
        //if (checkit && !term_in_trail(0xa2aa874)) {
        //    printf("Fail 1h\n");
        //    exit(1);
        //}
        eq = _ex_intern_equal(env,vtype,v,remove_nested_ite(env,info,list,e->u.appl.args[1]));
        args[1] = _ex_intern_appl1_env(env,INTERN_NOT,eq);
        _th_transfer_to_learn(env,info,list,_ex_intern_appl_env(env,INTERN_AND,2,args));
        if (c->type==EXP_APPL && c->u.appl.functor==INTERN_NOT) {
            args[0] = c->u.appl.args[0];
        } else {
            args[0] = _ex_intern_appl1_env(env,INTERN_NOT,c);
        }
        //if (checkit && !term_in_trail(0xa2aa874)) {
        //    printf("Fail 1i\n");
        //    exit(1);
        //}
        eq = _ex_intern_equal(env,vtype,v,remove_nested_ite(env,info,list,e->u.appl.args[2]));
        args[1] = _ex_intern_appl1_env(env,INTERN_NOT,eq);
        //if (checkit && !term_in_trail(0xa2aa874)) {
        //    printf("Fail 1ii\n");
        //    exit(1);
        //}
        _th_transfer_to_learn(env,info,list,_ex_intern_appl_env(env,INTERN_AND,2,args));
        //if (checkit && !term_in_trail(0xa2aa874)) {
        //    printf("Fail 1iii\n");
        //    exit(1);
        //}
        if (e->user2==NULL) {
            //if (term_in_trail(e)) {
            //    printf("Fail 1\n");
            //    exit(1);
            //}
            e->next_cache = trail;
            trail = e;
        }
        //if (!term_in_trail(e)) {
        //    printf("Fail 2\n");
        //    exit(1);
        //}
        //if (checkit && !term_in_trail(0xa2aa874)) {
        //    printf("Fail 1iiii\n");
        //    exit(1);
        //}
        e->user3 = v;
        //if (e==0xa2aa874) {
        //    printf("*** ADDING USER3 2 ***\n");
        //}
        return v;
    }

    for (i = 0; i < e->u.appl.count; ++i) {
        //if (checkit && !term_in_trail(0xa2aa874)) {
        //    printf("Fail 1j\n");
        //    exit(1);
        //}
        args[i] = remove_nested_ite(env,info,list,e->u.appl.args[i]);
    }

    if (e->user2==NULL) {
        //if (term_in_trail(e)) {
        //    printf("Fail 3\n");
        //    exit(1);
        //}
        e->next_cache = trail;
        trail = e;
    }
    //if (!term_in_trail(e)) {
    //    printf("Fail 4\n");
    //    exit(1);
    //}
    //if (e==0xa2aa874) {
    //    printf("*** ADDING USER3 3 ***\n");
    //}
    e->user3 = _ex_intern_appl_equal_env(env,e->u.appl.functor,e->u.appl.count,args,e->type_inst);
    return e->user3;
}

static struct _ex_intern *traverse_term(struct env *env, struct learn_info *info, struct parent_list *list, struct _ex_intern *e)
{
    int i;
    struct _ex_intern **args;

    //if (checkit && !term_in_trail(0xa2aa874)) {
    //    printf("Fail 1a\n");
    //    exit(1);
    //}
    if (e->user3) {
        //struct _ex_intern *r = trail;
        //while (r) {
        //    if (r==e) goto cont;
        //    r = r->next_cache;
        //}
        //fprintf(stderr, "Error: term not in trail %s\n", _th_print_exp(e));
        //fprintf(stderr, "User2: %s\n", _th_print_exp(e->user2));
//cont:
        return e->user3;
    }

    if (e->type != EXP_APPL) return e;

    //if (checkit && !term_in_trail(0xa2aa874)) {
    //    printf("Fail 1k\n");
    //    exit(1);
    //}
    if (e->u.appl.functor != INTERN_AND && e->u.appl.functor != INTERN_OR && e->u.appl.functor != INTERN_NOT &&
        e->u.appl.functor != INTERN_XOR &&
        e->u.appl.functor != INTERN_ITE && e->u.appl.functor != INTERN_EQUAL) return remove_nested_ite(env,info,list,e);

    if (e->u.appl.functor == INTERN_EQUAL && get_type(env,e->u.appl.args[0])!=_ex_bool) {
        return remove_nested_ite(env,info,list,e);
    }

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
    for (i = 0; i < e->u.appl.count; ++i) {
        args[i] = traverse_term(env,info,list,e->u.appl.args[i]);
    }

    if (e->user2==NULL) {
        //if (term_in_trail(e)) {
        //    printf("Fail 5\n");
        //    exit(1);
        //}
        e->next_cache = trail;
        trail = e;
    }
    //if (!term_in_trail(e)) {
    //    printf("Fail 6\n");
    //    exit(1);
    //}
    //if (e==0xa2aa874) {
    //    printf("*** ADDING USER3 1 ***\n");
    //    checkit = 1;
    //}
    e->user3 = _ex_intern_appl_equal_env(env,e->u.appl.functor,e->u.appl.count,args,e->type_inst);
    return e->user3;
}

void transfer_xor(struct env *env, struct learn_info *info, struct parent_list *list,
                  struct _ex_intern *e, struct _ex_intern *r)
{
    int *inverts = (int *)ALLOCA(sizeof(int) * e->u.appl.count);
    struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (e->u.appl.count+1));
    int i, invc;

    for (i = 0; i < e->u.appl.count; ++i) {
        inverts[i] = 0;
    }

    while (1) {
        invc = 0;
        for (i = 0; i < e->u.appl.count; ++i) {
            if (inverts[i]) ++invc;
        }
        for (i = 0; i < e->u.appl.count; ++i) {
            if (inverts[i]) {
                args[i] = invert(env,variablize(env,info,e->u.appl.args[i],list));
            } else {
                args[i] = variablize(env,info,e->u.appl.args[i],list);
            }
        }
        if ((invc&1)==0) {
            args[i] = r;
        } else {
            args[i] = _ex_intern_appl1_env(env,INTERN_NOT,r);
        }
        _th_transfer_to_learn(env,info,list,_ex_intern_appl_env(env,INTERN_AND,e->u.appl.count+1,args));
        for (i = 0; i < e->u.appl.count; ++i) {
            if (inverts[i]) {
                inverts[i] = 0;
            } else {
                goto cont;
            }
        }
cont:
        if (i < e->u.appl.count) {
            inverts[i] = 1;
        } else {
            return;
        }

    }
}

static struct _ex_intern *variablize(struct env *env, struct learn_info *info, struct _ex_intern *e, struct parent_list *list)
{
    struct _ex_intern *r;
    struct _ex_intern **args;
    int i;

    if (e->type != EXP_APPL) return e;

    if (e->user2) {
        //struct _ex_intern *r = trail;
        //while (r) {
        //    if (r==e) goto cont;
        //    r = r->next_cache;
        //}
        //fprintf(stderr, "Error: (variablize) term not in trail %s\n", _th_print_exp(e));
        //fprintf(stderr, "User2: %s\n", _th_print_exp(e->user2));
//cont:
        return e->user2;
    }

    _zone_print_exp("variablize", e);
    _tree_indent();

    switch (e->u.appl.functor) {
        case INTERN_AND:
            r = get_var(env,_ex_bool);
            if (e->user3==NULL) {
                e->next_cache = trail;
                trail = e;
                //if (term_in_trail(e)) {
                //    printf("Fail 7\n");
                //    exit(1);
                //}
            }
            //if (!term_in_trail(e)) {
            //    printf("fail %x %s\n", e->user3, _th_print_exp(e->user3));
            //    printf("Fail 8 %x %s\n", e->user3, _th_print_exp(e));
            //    exit(1);
            //}
            e->user2 = r;
            //printf("Variablize and %s\n", _th_print_exp(r));
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (e->u.appl.count+1));
            for (i = 0; i < e->u.appl.count; ++i) {
                struct _ex_intern *s;
                args[i] = variablize(env,info,e->u.appl.args[i],list);
                s = invert(env,args[i]);
                s = _ex_intern_appl2_env(env,INTERN_AND,r,s);
                _th_transfer_to_learn(env,info,list,s);
            }
            args[i] = invert(env,r);
            _th_transfer_to_learn(env,info,list,_ex_intern_appl_env(env,INTERN_AND,i+1,args));
            _tree_undent();
            return r;
        case INTERN_OR:
            r = get_var(env,_ex_bool);
            if (e->user3==NULL) {
                e->next_cache = trail;
                trail = e;
                //if (term_in_trail(e)) {
                //    printf("Fail 9\n");
                //   exit(1);
                //}
            }
            //if (!term_in_trail(e)) {
            //    printf("Fail 10\n");
            //    exit(1);
            //}
            e->user2 = r;
            //printf("Variablize or %s\n", _th_print_exp(r));
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (e->u.appl.count+1));
            for (i = 0; i < e->u.appl.count; ++i) {
                struct _ex_intern *s;
                s = variablize(env,info,e->u.appl.args[i],list);
                args[i] = invert(env,s);
                _th_transfer_to_learn(env,info,list,_ex_intern_appl2_env(env,INTERN_AND,invert(env,r),s));
            }
            args[i] = r;
            _th_transfer_to_learn(env,info,list,_ex_intern_appl_env(env,INTERN_AND,i+1,args));
            _tree_undent();
            return r;
        case INTERN_NOT:
            r = invert(env,variablize(env,info,e->u.appl.args[0],list));
            _tree_undent();
            return r;
        case INTERN_ITE:
            r = get_var(env,_ex_bool);
            //printf("Variablize ite %s\n", _th_print_exp(r));
            if (e->user3==NULL) {
                e->next_cache = trail;
                trail = e;
                //if (term_in_trail(e)) {
                //    printf("Fail 11\n");
                //    exit(1);
                //}
            }
            //if (!term_in_trail(e)) {
            //    printf("Fail 12\n");
            //    exit(1);
            //}
            e->user2 = r;
            _th_transfer_to_learn(env,info,list,_ex_intern_appl3_env(env,INTERN_AND,r,variablize(env,info,e->u.appl.args[0],list),invert(env,variablize(env,info,e->u.appl.args[1],list))));
            _th_transfer_to_learn(env,info,list,_ex_intern_appl3_env(env,INTERN_AND,r,invert(env,variablize(env,info,e->u.appl.args[0],list)),invert(env,variablize(env,info,e->u.appl.args[2],list))));
            _th_transfer_to_learn(env,info,list,_ex_intern_appl3_env(env,INTERN_AND,invert(env,r),variablize(env,info,e->u.appl.args[0],list),variablize(env,info,e->u.appl.args[1],list)));
            _th_transfer_to_learn(env,info,list,_ex_intern_appl3_env(env,INTERN_AND,invert(env,r),invert(env,variablize(env,info,e->u.appl.args[0],list)),variablize(env,info,e->u.appl.args[2],list)));
            _tree_undent();
            return r;
        case INTERN_XOR:
            r = get_var(env,_ex_bool);
            //printf("    boolean equal  %s\n", _th_print_exp(r));
            //printf("    type0 %s\n", _th_print_exp(get_type(env,e->u.appl.args[0])));
            //printf("    type1 %s\n", _th_print_exp(get_type(env,e->u.appl.args[1])));
            if (e->user3==NULL) {
                e->next_cache = trail;
                trail = e;
            }
            e->user2 = r;
            transfer_xor(env,info,list,e,r);
            _tree_undent();
            return r;
        case INTERN_EQUAL:
            //printf("Processing equal %s\n", _th_print_exp(e));
            if (get_type(env,e->u.appl.args[0])==_ex_bool) {
                r = get_var(env,_ex_bool);
                //printf("    boolean equal  %s\n", _th_print_exp(r));
                //printf("    type0 %s\n", _th_print_exp(get_type(env,e->u.appl.args[0])));
                //printf("    type1 %s\n", _th_print_exp(get_type(env,e->u.appl.args[1])));
                if (e->user3==NULL) {
                    e->next_cache = trail;
                    trail = e;
                    //if (term_in_trail(e)) {
                    //    printf("Fail 13\n");
                    //    exit(1);
                    //}
                }
                //if (!term_in_trail(e)) {
                //    printf("Fail 14\n");
                //    exit(1);
                //}
                e->user2 = r;
                _th_transfer_to_learn(env,info,list,_ex_intern_appl3_env(env,INTERN_AND,r,variablize(env,info,e->u.appl.args[0],list),invert(env,variablize(env,info,e->u.appl.args[1],list))));
                _th_transfer_to_learn(env,info,list,_ex_intern_appl3_env(env,INTERN_AND,r,invert(env,variablize(env,info,e->u.appl.args[0],list)),variablize(env,info,e->u.appl.args[1],list)));
                _th_transfer_to_learn(env,info,list,_ex_intern_appl3_env(env,INTERN_AND,invert(env,r),variablize(env,info,e->u.appl.args[0],list),variablize(env,info,e->u.appl.args[1],list)));
                _th_transfer_to_learn(env,info,list,_ex_intern_appl3_env(env,INTERN_AND,invert(env,r),invert(env,variablize(env,info,e->u.appl.args[0],list)),invert(env,variablize(env,info,e->u.appl.args[1],list))));
                _tree_undent();
                return r;
            }
        default:
            //if (checkit && !term_in_trail(0xa2aa874)) {
            //    printf("Fail 1g\n");
            //   exit(1);
            //}
            e = remove_nested_ite(env,info,list,e);
            _tree_undent();
            return e;
    }
}

static void add_top_tuple(struct env *env, struct learn_info *info, struct _ex_intern *e, struct parent_list *list)
{
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_AND) {
        int i;
        struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = variablize(env,info,e->u.appl.args[i],list);
			//args[i] = _th_simp(env,args[i]);
        }
        _th_transfer_to_learn(env,info,list,_ex_intern_appl_env(env,INTERN_AND,e->u.appl.count,args));
    } else {
        _th_transfer_to_learn(env,info,list,_ex_intern_appl1_env(env,INTERN_AND,variablize(env,info,e,list)));
    }
}

void _th_add_to_learn(struct env *env, struct learn_info *info, struct _ex_intern *e, struct parent_list *list)
{
    trail = NULL;

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_OR) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            add_top_tuple(env,info,e->u.appl.args[i],list);
        }
    } else {
        add_top_tuple(env,info,e,list);
    }

    while (trail) {
        trail->user2 = NULL;
        trail->user3 = NULL;
        trail = trail->next_cache;
    }
}

struct _ex_intern *_th_remove_nested_ite(struct env *env, struct learn_info *info, struct _ex_intern *e, struct parent_list *list)
{
    struct _ex_intern *res;

    trail = NULL;

    res = traverse_term(env,info,list,e);

    while (trail) {
        trail->user2 = NULL;
        trail->user3 = NULL;
        //if (trail==0xa2aa874) {
        //    printf("*** Removing USER3 1\n");
        //}
        //checkit = 0;
        trail = trail->next_cache;
    }

    return res;
}

static struct add_list *ret_vnf;

static struct _ex_intern *variablize_all_functions(struct env *env, struct _ex_intern *e, struct add_list *funs)
{
    struct _ex_intern **args;
    int i;

    if (e->user2) return e->user2;
    if (e->user3==NULL) {
        e->next_cache = trail;
        trail = e;
    }

    if (e->type != EXP_APPL) {
        ret_vnf = funs;
        return e->user2 = e;
    }

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern **) * e->u.appl.count);

    if (e->u.appl.functor==INTERN_XOR ||
        e->u.appl.functor==INTERN_AND || e->u.appl.functor==INTERN_OR || e->u.appl.functor==INTERN_NOT ||
        e->u.appl.functor==INTERN_ITE || e->u.appl.functor==INTERN_RAT_PLUS || e->u.appl.functor==INTERN_RAT_TIMES ||
        e->u.appl.functor==INTERN_RAT_DIVIDE || e->u.appl.functor==INTERN_RAT_MINUS || e->u.appl.functor==INTERN_RAT_LESS ||
        e->u.appl.functor==INTERN_NAT_PLUS || e->u.appl.functor==INTERN_NAT_MINUS || e->u.appl.functor==INTERN_NAT_TIMES ||
        e->u.appl.functor==INTERN_NAT_DIVIDE || e->u.appl.functor==INTERN_NAT_LESS || e->u.appl.functor==INTERN_EQUAL ||
        e->u.appl.count==0) {
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = variablize_all_functions(env,e->u.appl.args[i],funs);
            funs = ret_vnf;
        }
        return e->user2 = _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
    } else {
        struct _ex_intern *vtype = get_type(env,e);
        struct _ex_intern *nvar = get_var(env, vtype);
        struct add_list *l = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        //printf("Variablize all functions %s\n", _th_print_exp(nvar));
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = variablize_all_functions(env,e->u.appl.args[i],funs);
            funs = ret_vnf;
        }
        l->next = funs;
        funs = l;
        l->e = _ex_intern_equal(env,vtype,nvar,_ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args));
        ret_vnf = funs;
        return e->user2 = nvar;
    }
}

static struct _ex_intern *variablize_nested_functions(struct env *env, struct _ex_intern *e, struct add_list *funs)
{
    struct _ex_intern **args;
    int i;

    if (e->user2) return e->user2;
    if (e->user3==NULL) {
        e->next_cache = trail;
        trail = e;
    }

    if (e->type != EXP_APPL) {
        ret_vnf = funs;
        return e->user2 = e;
    }

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern **) * e->u.appl.count);

    if (e->u.appl.functor==INTERN_XOR ||
        e->u.appl.functor==INTERN_AND || e->u.appl.functor==INTERN_OR || e->u.appl.functor==INTERN_NOT ||
        e->u.appl.functor==INTERN_ITE || e->u.appl.functor==INTERN_RAT_PLUS || e->u.appl.functor==INTERN_RAT_TIMES ||
        e->u.appl.functor==INTERN_RAT_DIVIDE || e->u.appl.functor==INTERN_RAT_MINUS || e->u.appl.functor==INTERN_RAT_LESS ||
        e->u.appl.functor==INTERN_NAT_PLUS || e->u.appl.functor==INTERN_NAT_MINUS || e->u.appl.functor==INTERN_NAT_TIMES ||
        e->u.appl.functor==INTERN_NAT_DIVIDE || e->u.appl.functor==INTERN_NAT_LESS || e->u.appl.functor==INTERN_EQUAL ||
        e->u.appl.count==0) {
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = variablize_nested_functions(env,e->u.appl.args[i],funs);
            funs = ret_vnf;
        }
        e->user2 = _ex_intern_appl_equal_env(env,e->u.appl.functor,e->u.appl.count,args,e->type_inst);
        return e->user2;
    } else {
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = variablize_all_functions(env,e->u.appl.args[i],funs);
            funs = ret_vnf;
        }
        e->user2 = _ex_intern_appl_equal_env(env,e->u.appl.functor,e->u.appl.count,args,e->type_inst);
        return e->user2;
    }
}

static struct _ex_intern *variablize_functions(struct env *env, struct _ex_intern *e)
{
    int count;
    struct _ex_intern **args;
    struct add_list *l;

    trail = NULL;

    e = variablize_nested_functions(env,e,NULL);
    l = ret_vnf;
    count = 0;
    while (l) {
        ++count;
        l = l->next;
    }

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (count+1));
    args[0] = e;
    
    while (trail) {
        trail->user2 = NULL;
        trail->user3 = NULL;
        trail = trail->next_cache;
    }

    count = 1;
    l = ret_vnf;
    while (l) {
        args[count++] = _ex_intern_appl1_env(env,INTERN_NOT,l->e);
        l = l->next;
    }

    return _ex_intern_appl_env(env,INTERN_OR,count,args);
}

struct add_list *collect_terminal_functions(struct _ex_intern *e, struct add_list *funs)
{
    int i;
    struct add_list *funs2;

    if (e->user2) return funs;
    e->next_cache = trail;
    if (e->user3==NULL) {
        trail = e;
        e->user2 = _ex_false;
    }

    if (e->type != EXP_APPL) return funs;

    if (e->u.appl.functor==INTERN_XOR ||
        e->u.appl.functor==INTERN_AND || e->u.appl.functor==INTERN_OR || e->u.appl.functor==INTERN_NOT ||
        e->u.appl.functor==INTERN_ITE || e->u.appl.functor==INTERN_RAT_PLUS || e->u.appl.functor==INTERN_RAT_TIMES ||
        e->u.appl.functor==INTERN_RAT_DIVIDE || e->u.appl.functor==INTERN_RAT_MINUS || e->u.appl.functor==INTERN_RAT_LESS ||
        e->u.appl.functor==INTERN_NAT_PLUS || e->u.appl.functor==INTERN_NAT_MINUS || e->u.appl.functor==INTERN_NAT_TIMES ||
        e->u.appl.functor==INTERN_NAT_DIVIDE || e->u.appl.functor==INTERN_NAT_LESS || e->u.appl.functor==INTERN_EQUAL ||
        e->u.appl.count==0) {
        for (i = 0; i < e->u.appl.count; ++i) {
            funs = collect_terminal_functions(e->u.appl.args[i],funs);
            if (e->u.appl.args[i]->user2==_ex_true) e->user2 = _ex_true;
        }
        return funs;
    } else {
        funs2 = funs;
        for (i = 0; i < e->u.appl.count; ++i) {
            funs = collect_terminal_functions(e->u.appl.args[i],funs);
            if (e->u.appl.args[i]->user2==_ex_true) e->user2 = _ex_true;
        }
        if (funs != funs2 || e->user2==_ex_true) {
            return funs;
        }
        funs2 = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        funs2->next = funs;
        funs2->e = e;
        e->user2 = _ex_true;
        return funs2;
    }
}

struct tail_list {
    struct tail_list *next;
    struct _ex_intern *e;
    struct _ex_intern *v;
};

struct f_list {
    struct f_list *next;
    unsigned functor;
    struct tail_list *list;
};

static struct f_list *functors;

static struct add_list *sub_functors(struct env *env, struct add_list *l, struct _ex_intern *e)
{
    struct _ex_intern *f, *nvar;
    struct tail_list *t, *nt;
    struct add_list *prev;
    struct _ex_intern **args;
    struct add_list *rest;
    struct f_list *ff;
    int i;

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * l->e->u.appl.count);

    f = l->e;
    ff = functors;
    while (ff) {
        if (ff->functor==f->u.appl.functor) {
            goto cont;
        }
        ff = ff->next;
    }
    ff = (struct f_list *)_th_alloc(REWRITE_SPACE,sizeof(struct f_list));
    ff->next = functors;
    functors = ff;
    ff->functor = f->u.appl.functor;
    ff->list = NULL;
cont:
    t = ff->list;
    prev = NULL;
    while (l != NULL) {
        if (l->e->u.appl.functor==f->u.appl.functor) {
            if (prev) {
                prev->next = l->next;
            } else {
                rest = l->next;
            }
            nt = (struct tail_list *)_th_alloc(REWRITE_SPACE,sizeof(struct tail_list));
            nt->next = t;
            t = nt;
            f = t->e = l->e;
            nt = t->next;
            nvar = get_var(env, get_type(env,f));
            //printf("sub functors %s\n", _th_print_exp(nvar));
            //printf("term %s\n", _th_print_exp(f));
            //printf("type %s\n", _th_print_exp(get_type(env,f)));
            while (nt) {
                //printf("f = %s\n", _th_print_exp(f));
                //printf("nt, nt->e = %x %s\n", nt, _th_print_exp(nt->e));
                //fflush(stdout);
                for (i = 0; i < f->u.appl.count; ++i) {
                    args[i] = _ex_intern_equal(env,get_type(env,nt->e->u.appl.args[i]),nt->e->u.appl.args[i],f->u.appl.args[i]);
                }
                nvar = _ex_intern_appl3_env(env,INTERN_ITE,_ex_intern_appl_env(env,INTERN_AND,i,args),nt->v,nvar);
                nt = nt->next;
            }
            t->v = nvar;
            t->e->next_cache = trail;
            trail = t->e;
            t->e->user2 = nvar;
            //_zone_print_exp("Substituting", t->e);
            //_zone_print_exp("with", nvar);
        } else {
            prev = l;
        }
        l = l->next;
    }
    ff->list = t;
    return rest;
}

static struct _ex_intern *sub_terms(struct env *env, struct _ex_intern *e)
{
    int i;
    struct _ex_intern **args, *r;

    if (e->user2 && e->user2 != _ex_true && e->user2 != _ex_false) {
        return e->user2;
    }

    if (e->type==EXP_APPL) {
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = sub_terms(env,e->u.appl.args[i]);
        }
        r = _ex_intern_appl_equal_env(env,e->u.appl.functor,e->u.appl.count,args,e->type_inst);
        //if (r->user2) {
        //    fprintf(stderr, "Error term %s has sub\n", _th_print_exp(r));
        //    fprintf(stderr, "    orig: %s\n", _th_print_exp(e));
        //    exit(1);
        //}
        if (e->user2==NULL) {
            e->next_cache = trail;
            trail = e;
        }
        e->user2 = r;
        return r;
    }

    return e;
}

GDEF("pre _th_variablize_functions trail==NULL");
GDEF("post _th_variablize_functions trail==NULL");

struct _ex_intern *_th_variablize_functions(struct env *env, struct _ex_intern *e)
{
    functors = NULL;

    ++_th_block_complex;
    _zone_print_exp("variablize_functions", e);
    --_th_block_complex;
    e = variablize_functions(env,e);
    ++_th_block_complex;
    _zone_print_exp("after abstraction", e);
    --_th_block_complex;

    while (1) {
        struct add_list *l, *ll;
        trail = NULL;
        l = collect_terminal_functions(e,NULL);
        ll = l;
        _zone_print0("Terminals");
        _tree_indent();
        while (ll) {
            ++_th_block_complex;
            _zone_print_exp("term", ll->e);
            --_th_block_complex;
            fflush(stdout);
            ll = ll->next;
        }
        _tree_undent();
        while (trail) {
            trail->user2 = NULL;
            trail->user3 = NULL;
            trail = trail->next_cache;
        }
        if (l==NULL) {
            //printf("Result: %s\n", _th_print_exp(e));
            return e;
        }
        while (l) {
            l = sub_functors(env,l,e);
        }
        e = sub_terms(env,e);
        while (trail) {
            trail->user2 = NULL;
            trail->user3 = NULL;
            trail = trail->next_cache;
        }
    }
}
