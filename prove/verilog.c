/*
 * verilog.c
 *
 * Routines for handling the Verilog interface of the theorem prover
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "Globalsp.h"
#include "../rewlib/RewriteLog.h"

int module_space = -1;
char *module_mark;
struct module_list *modules;
struct env *verilog_env;
int verilog_derivation;

struct module_list *find_module(unsigned name)
{
    struct module_list *ml = modules;

    while (ml != NULL) {
        if (ml->name==name) return ml;
        ml = ml->next;
    }

    ml = (struct module_list *)_th_alloc(module_space,sizeof(struct module_list));
    ml->next = modules;
    modules = ml;
    ml->name = name;
    ml->declarations = NULL;
    ml->assertions = NULL;
    ml->is_root_module = 1;
    ml->children = NULL;
    ml->trigger_order = NULL;
    ml->state_var_list = NULL;
    ml->clock_var_list = NULL;
    ml->groups = NULL;
    ml->assign_exp = NULL;
    ml->effects = NULL;

    return ml;
}

struct _ex_intern *find_parameter(struct module_list *module, char *name,
                                  int *count)
{
    struct add_list *al = module->declarations;

    *count = 0;

    while (al != NULL) {
        if (al->e->type == EXP_APPL && al->e->u.appl.functor==INTERN_PARAMETER &&
            al->e->u.appl.count >= 2 &&
            al->e->u.appl.args[0]->type==EXP_STRING) {
            if (!strcmp(al->e->u.appl.args[0]->u.string,name)) {
                return al->e->u.appl.args[1];
            }
            ++*count;
        }
        al = al->next;
    }

    return NULL;
}

struct _ex_intern *find_connection(struct module_list *parent, struct _ex_intern *instance,
                                   char *variable)
{
    struct add_list *al = parent->declarations;

    while (al != NULL) {
        if (al->e->type==EXP_APPL && al->e->u.appl.functor==INTERN_CONNECT &&
            al->e->u.appl.count >= 3 && al->e->u.appl.args[0]->type==EXP_STRING &&
            instance->type==EXP_APPL && instance->u.appl.count >= 2 &&
            instance->u.appl.args[0]->type==EXP_STRING &&
            !strcmp(al->e->u.appl.args[0]->u.string,instance->u.appl.args[0]->u.string) &&
            al->e->u.appl.args[1]->type==EXP_STRING &&
            !strcmp(variable,al->e->u.appl.args[1]->u.string)) {

            return al->e->u.appl.args[2];
        }
        al = al->next;
    }

    return NULL;
}

struct _ex_intern *instantiate_assertion(struct env *env,
                                         struct module_list *module,
                                         struct module_list *parent,
                                         struct _ex_intern *instance,
                                         struct _ex_intern *assertion)
{
    int i;
    struct _ex_intern **args, *p;

    switch (assertion->type) {
        case EXP_APPL:
            if (assertion->u.appl.functor==INTERN_REFERENCE) {
                if (p = find_parameter(module, assertion->u.appl.args[0]->u.string, &i)) {
                    if (instance && instance->u.appl.count > 2+i) return instance->u.appl.args[i+2];
                    return p->u.appl.args[1];
                }
                if (instance &&
                    (p = find_connection(parent, instance, assertion->u.appl.args[0]->u.string))) {
                    return p;
                }
            } else if (assertion->u.appl.functor==INTERN_PAR &&
                       assertion->u.appl.count >= 1 &&
                       assertion->u.appl.args[0]->type==EXP_STRING) {
                if (p = find_parameter(module, assertion->u.appl.args[0]->u.string, &i)) {
                    if (instance && instance->u.appl.count > 2) return instance->u.appl.args[i+2];
                    return p;
                }
            }
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * assertion->u.appl.count);
            for (i = 0; i < assertion->u.appl.count; ++i) {
                args[i] = instantiate_assertion(env, module, parent, instance, assertion->u.appl.args[i]);
            }
            return _ex_intern_appl_env(env,assertion->u.appl.functor,assertion->u.appl.count,args);
        case EXP_QUANT:
            return _ex_intern_quant(assertion->u.quant.quant, assertion->u.quant.var_count,
                                    assertion->u.quant.vars,
                                    instantiate_assertion(env,module,parent,instance,
                                        assertion->u.quant.exp),
                                    instantiate_assertion(env,module,parent,instance,
                                        assertion->u.quant.cond));
        default:
            return assertion;
    }
}

struct add_list *instantiate_module(struct module_list *module,
                                    struct module_list *parent,
                                    int base,
                                    struct _ex_intern *instance)
{
    struct add_list *al = module->assertions,
                    *inst, *inste, *ret;
    struct _ex_intern *r;

    while (al != NULL) {
        if (al->e->type==EXP_APPL && al->e->u.appl.functor==INTERN_NOSPEC) {
            al = module->declarations;
            inste = NULL;
            ret = NULL;
            while (al != NULL) {
                if (al->e->type==EXP_APPL) {
                    switch (al->e->u.appl.functor) {
                        case INTERN_ASSIGN:
                            r = _ex_intern_appl6_env(verilog_env,INTERN_ASSIGN,
                                al->e->u.appl.args[0],
                                al->e->u.appl.args[1],
                                al->e->u.appl.args[2],
                                al->e->u.appl.args[3],
                                al->e->u.appl.args[4],
                                _ex_intern_small_integer(base+al->e->u.appl.args[5]->u.integer[1]));
                            goto common;
                        case INTERN_CONDITION_ROOT:
                            r = _ex_intern_appl1_env(verilog_env,INTERN_CONDITION_ROOT,
                                _ex_intern_small_integer(base+al->e->u.appl.args[0]->u.integer[1]));
                            goto common;
                        case INTERN_CONDITION_EDGE:
                            r = _ex_intern_appl4_env(verilog_env,INTERN_CONDITION_EDGE,
                                _ex_intern_small_integer(base+al->e->u.appl.args[0]->u.integer[1]),
                                _ex_intern_small_integer(base+al->e->u.appl.args[1]->u.integer[1]),
                                _ex_intern_small_integer(base+al->e->u.appl.args[2]->u.integer[1]),
                                al->e->u.appl.args[2]);
common:
                            inst = (struct add_list *)_th_alloc(module_space,sizeof(struct add_list));
                            if (inste) {
                                inste->next = inst;
                            } else {
                                ret = inst;
                            }
                            inste = inst;
                            inst->next = NULL;
                            printf("Instantiation: %s\n", _th_print_exp(r));
                            inst->e = instantiate_assertion(verilog_env,module,parent,instance,r);
                            break;
                        case INTERN_WIRE:
                        case INTERN_WIRE_VECTOR:
                        case INTERN_REG:
                        case INTERN_REG_VECTOR:
                            if (al->e->u.appl.count >= 1 &&
                                al->e->u.appl.args[0]->type==EXP_STRING) {
                                printf("Error: cannot expand local declaration of %s\n",
                                    al->e->u.appl.args[0]->u.string);
                            } else {
                                printf("Error: cannot expand local declaration\n");
                            }
                            break;
                    }
                }
                al = al->next;
            }
            return ret;
        }
        al = al->next;
    }
    return NULL;
}

int condition_count(struct add_list *al)
{
    int nodes = 0;
    while (al != NULL) {
        if (al->e->type==EXP_APPL && (al->e->u.appl.functor==INTERN_CONDITION_EDGE ||
            al->e->u.appl.functor==INTERN_CONDITION_ROOT)) {
            ++nodes;
        }
        al = al->next;
    }
    return nodes;
}

void instantiate_modules()
{
    struct module_list *ml = modules;
    struct module_pointer_list *mpl;
    int count;

    while (ml != NULL) {
        count = condition_count(ml->declarations);
        mpl = ml->children;
        while (mpl != NULL) {
            mpl->instantiation = instantiate_module(mpl->module,ml,count,mpl->instance_exp);
            count += condition_count(mpl->module->declarations);
            mpl = mpl->next;
        }
        ml = ml->next;
    }
    printf("Done instantiating modules\n");
}

void read_pmv_file(char *source)
{
    char name[1000];
    char line[10000];
    FILE *file;
    struct _ex_intern *e;
    struct module_list *module;
    struct add_list *al;
    struct module_pointer_list *p;
    struct add_list *ale = NULL;

    strcpy(name, source);
    strcpy(name+strlen(name)-2,".pmv");
    file = fopen(name, "r");
    if (file==NULL) {
        printf("Error: File %s didn't compile\n", source);
        return;
    }

    module = NULL;

    while(1) {
        fgets(line, 9999, file);
        if (feof(file)) break;
        if (line[0]=='#' || line[0] < ' ') continue;
        e = _th_parse(verilog_env,line);
        if (e==NULL) {
            printf("Error: Illegal line: %s\n", line);
            printf("*END\n");
            exit(1);
        }
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_ASSIGN) {
            e = _ex_intern_appl6_env(verilog_env,INTERN_ASSIGN,
                    e->u.appl.args[0],
                    e->u.appl.args[1],
                    _th_flatten(verilog_env,
                        _ex_intern_appl2_env(verilog_env,INTERN_AND,
                            e->u.appl.args[2],
                            e->u.appl.args[3])),
                    e->u.appl.args[3],
                    e->u.appl.args[4],
                    e->u.appl.args[5]);
        }
#ifdef _DEBUG
        _th_check(verilog_env,_ex_bool,e) ;
#endif
        //printf("e = %s\n", _th_print_exp(e));
        if (e != NULL && e->type==EXP_APPL && e->u.appl.count==1 && e->u.appl.args[0]->type==EXP_STRING &&
            e->u.appl.functor==INTERN_MODULE) {
            module = find_module(_th_intern(e->u.appl.args[0]->u.string));
            ale = NULL;
            /* *** TEMPORARY *** */
            al = (struct add_list *)_th_alloc(module_space, sizeof(struct add_list));
            al->next = NULL;
            if (ale==NULL) {
                module->declarations = al;
            } else {
                ale->next = al;
            }
            ale = al;
            al->e = _ex_intern_appl1_env(verilog_env, INTERN_STATE_VAR, _ex_intern_string("ramState"));
            module->state_var_list = (struct var_list *)_th_alloc(module_space,sizeof(struct var_list));
            module->state_var_list->next = NULL;
            module->state_var_list->var = _th_intern("ramState");
        } else if (module != NULL) {
            if (e != NULL && e->type==EXP_APPL && e->u.appl.count>=2 && e->u.appl.args[0]->type==EXP_STRING &&
                e->u.appl.args[1]->type==EXP_STRING && e->u.appl.functor==INTERN_INSTANCE) {
                p = (struct module_pointer_list *)_th_alloc(module_space,sizeof(struct module_pointer_list));
                p->next = module->children;
                module->children = p;
                p->instance_exp = e;
                p->instantiation = NULL;
                p->module = find_module(_th_intern(e->u.appl.args[1]->u.string));
                p->module->is_root_module = 0;
                p->instance = _th_intern(e->u.appl.args[0]->u.string);
            }
            al = (struct add_list *)_th_alloc(module_space, sizeof(struct add_list));
            al->next = NULL;
            if (ale==NULL) {
                module->declarations = al;
            } else {
                ale->next = al;
            }
            ale = al;
            //_tree_start = 0 ; _tree_end = 20000 ; _tree_mute = 0 ; _tree_sub = _tree_sub2 = -1 ;
            e = _th_rewrite(verilog_env,e);
            al->e = e;
        }
    }
    fclose(file);
}

void read_assert_file(char *name)
{
    char line[10000];
    FILE *file;
    struct _ex_intern *e;
    struct module_list *module;
    struct add_list *al;
    struct add_list *ale = NULL;

    file = fopen(name, "r");
    if (file==NULL) {
        printf("Error: File %s didn't compile\n", name);
        return;
    }

    module = NULL;

    while(1) {
        fgets(line, 9999, file);
        if (feof(file)) break;
        if (line[0]=='#' || line[0] < ' ') continue;
        e = _th_parse(verilog_env,line);
        if (e==NULL) {
            printf("Error: Cannot parse %s\n", line);
        }
        if (e != NULL && e->type==EXP_APPL && e->u.appl.count==1 && e->u.appl.args[0]->type==EXP_STRING &&
            e->u.appl.functor==INTERN_MODULE) {
            module = find_module(_th_intern(e->u.appl.args[0]->u.string));
            ale = module->assertions;
            while (ale && ale->next) ale = ale->next;
        } else if (module != NULL && e != NULL) {
            al = (struct add_list *)_th_alloc(module_space, sizeof(struct add_list));
            if (ale) {
                ale->next = al;
            } else {
                module->assertions = al;
            }
            al->next = NULL;
            ale = al;
            al->e = e;
        }
    }
    fclose(file);
}

struct assign_group *add_assign_to_group(struct assign_group *groups, struct _ex_intern *assign)
{
    unsigned var;
    struct assign_group *g;
    struct add_list *al, *ale;

    if (assign->u.appl.args[0]->type==EXP_APPL &&
        assign->u.appl.args[0]->u.appl.functor==INTERN_REFERENCE &&
        assign->u.appl.args[0]->u.appl.count >= 1 &&
        assign->u.appl.args[0]->u.appl.args[0]->type==EXP_STRING) {
        var = _th_intern(assign->u.appl.args[0]->u.appl.args[0]->u.string);
    } else if (assign->u.appl.args[0]->type==EXP_APPL &&
        assign->u.appl.args[0]->u.appl.functor==INTERN_VEC_INDEX &&
        assign->u.appl.args[0]->u.appl.count > 1 &&
        assign->u.appl.args[0]->u.appl.args[0]->type==EXP_APPL &&
        assign->u.appl.args[0]->u.appl.args[0]->u.appl.functor==INTERN_REFERENCE &&
        assign->u.appl.args[0]->u.appl.args[0]->u.appl.count >= 1 &&
        assign->u.appl.args[0]->u.appl.args[0]->u.appl.args[0]->type==EXP_STRING) {
        var = _th_intern(assign->u.appl.args[0]->u.appl.args[0]->u.appl.args[0]->u.string);
    } else {
        return groups;
    }

    g = groups;

    while (g != NULL) {
        if (g->variable==var) break;
        g = g->next;
    }

    if (g == NULL) {
        g = (struct assign_group *)_th_alloc(module_space, sizeof(struct assign_group));
        g->cut_processed = 0;
        g->next = groups;
        g->assigns = NULL;
        g->variable = var;
        groups = g;
    }

    if (g->assigns == NULL) {
        g->assigns = al = (struct add_list *)_th_alloc(module_space, sizeof(struct add_list));
    } else {
        ale = g->assigns;
        while (ale->next != NULL) {
            ale = ale->next;
        }
        ale->next = al = (struct add_list *)_th_alloc(module_space, sizeof(struct add_list));
    }

    al->next = NULL;
    al->e = assign;

    return groups;
}

void add_trigger_pair(struct trigger_order *t, struct trigger_order *o)
{
    struct trigger_order_list *l;

    l = t->children;
    while (l != NULL) {
        if (l->order==o) return;
        l = l->next;
    }

    l = (struct trigger_order_list *)_th_alloc(module_space, sizeof(struct trigger_order_list));
    l->next = t->children;
    t->children = l;
    l->order = o;

    l = (struct trigger_order_list *)_th_alloc(module_space, sizeof(struct trigger_order_list));
    l->next = o->parents;
    o->parents = l;
    l->order = t;
}

struct trigger_order *add_trigger(struct trigger_order *order, struct trigger_order *o, unsigned trigger)
{
    struct trigger_order *t = order;
    struct trigger_order_list *l;

    //printf("adding trigger %s %s %s\n", _th_intern_decode(trigger), _th_intern_decode(t->var), _th_intern_decode(o->var));

    while (t != NULL && t->var != trigger) {
        t = t->next;
    }

    if (t==NULL) {
        t = (struct trigger_order *)_th_alloc(module_space, sizeof(struct trigger_order));
        t->next = order;
        t->parents = t->children = NULL;
        t->var = trigger;
        order = t;
    }

    add_trigger_pair(t,o);

    l = o->children;
    while (l != NULL) {
        add_trigger_pair(t,l->order);
        l = l->next;
    }

    l = t->parents;
    while (l != NULL) {
        add_trigger_pair(l->order,o);
        l = l->next;
    }
    return order;
}

struct trigger_order *add_triggers(struct trigger_order *order, struct trigger_order *o, struct _ex_intern *exp)
{
    int i;

    switch (exp->type) {

         case EXP_APPL:
             if (exp->u.appl.count==2 &&
                 (exp->u.appl.functor==INTERN_EDGE ||
                  exp->u.appl.functor==INTERN_POSEDGE ||
                  exp->u.appl.functor==INTERN_NEGEDGE) &&
                  exp->u.appl.args[0]->type==EXP_STRING) {
                 return add_trigger(order, o, _th_intern(exp->u.appl.args[0]->u.string));
             }
             for (i = 0; i < exp->u.appl.count; ++i) {
                 order = add_triggers(order, o, exp->u.appl.args[i]);
             }
             return order;

         case EXP_QUANT:
             order = add_triggers(order, o, exp->u.quant.exp);
             return add_triggers(order, o, exp->u.quant.cond);

         default:
             return order;
    }
}

struct trigger_order_list *add_trigger_to_list(struct trigger_order *t, struct trigger_order_list *list, unsigned trigger)
{
    struct trigger_order_list *l, *c;

    //printf("adding trigger %s %s %s\n", _th_intern_decode(trigger), _th_intern_decode(t->var), _th_intern_decode(o->var));

    while (t != NULL && t->var != trigger) {
        t = t->next;
    }

    if (t==NULL) return list;

    l = (struct trigger_order_list *)_th_alloc(module_space, sizeof(struct trigger_order_list));
    l->next = list;
    list = l;
    l->order = t;

    c = t->children;
    while (c != NULL) {
        l = (struct trigger_order_list *)_th_alloc(module_space, sizeof(struct trigger_order_list));
        l->next = list;
        list = l;
        l->order = c->order;

        c = c->next;
    }

    return list;
}

struct trigger_order_list *add_node_triggers(struct trigger_order *t, struct trigger_order_list *list, struct _ex_intern *exp)
{
    int i;

    switch (exp->type) {

         case EXP_APPL:
             if (exp->u.appl.count==2 &&
                 (exp->u.appl.functor==INTERN_EDGE ||
                  exp->u.appl.functor==INTERN_POSEDGE ||
                  exp->u.appl.functor==INTERN_NEGEDGE) &&
                  exp->u.appl.args[0]->type==EXP_STRING) {
                 return add_trigger_to_list(t, list, _th_intern(exp->u.appl.args[0]->u.string));
             }
             for (i = 0; i < exp->u.appl.count; ++i) {
                 list = add_node_triggers(t, list, exp->u.appl.args[i]);
             }
             return list;

         case EXP_QUANT:
             list = add_node_triggers(t, list, exp->u.quant.exp);
             return add_node_triggers(t, list, exp->u.quant.cond);

         default:
             return list;
    }
}

struct trigger_order *add_trigger_order(struct trigger_order *order, struct _ex_intern *assign)
{
    unsigned var;
    struct trigger_order *o;

    //printf("add_trigger_order %s\n", _th_print_exp(assign));
    if (assign->u.appl.args[0]->type==EXP_APPL &&
        assign->u.appl.args[0]->u.appl.functor==INTERN_REFERENCE &&
        assign->u.appl.args[0]->u.appl.count >= 1 &&
        assign->u.appl.args[0]->u.appl.args[0]->type==EXP_STRING) {
        //printf("Adding assign %s\n", assign->u.appl.args[0]->u.appl.args[0]->u.string);
        var = _th_intern(assign->u.appl.args[0]->u.appl.args[0]->u.string);
    } else if (assign->u.appl.args[0]->type==EXP_APPL &&
        assign->u.appl.args[0]->u.appl.functor==INTERN_VEC_INDEX &&
        assign->u.appl.args[0]->u.appl.count > 1 &&
        assign->u.appl.args[0]->u.appl.args[0]->type==EXP_APPL &&
        assign->u.appl.args[0]->u.appl.args[0]->u.appl.functor==INTERN_REFERENCE &&
        assign->u.appl.args[0]->u.appl.args[0]->u.appl.count >= 1 &&
        assign->u.appl.args[0]->u.appl.args[0]->u.appl.args[0]->type==EXP_STRING) {
        var = _th_intern(assign->u.appl.args[0]->u.appl.args[0]->u.appl.args[0]->u.string);
    } else {
        return order;
    }

    o = order;

    while (o != NULL) {
        if (o->var==var) break;
        o = o->next;
    }

    if (o == NULL) {
        o = (struct trigger_order *)_th_alloc(module_space, sizeof(struct trigger_order));
        o->next = order;
        o->parents = o->children = NULL;
        o->var = var;
        order = o;
    }

    order = add_triggers(order, o, assign->u.appl.args[3]);

    return order;
}

void get_range(unsigned var, struct module_list *module, int *hi, int *lo, int *decl)
{
    struct add_list *al = module->declarations;

    while (al != NULL) {
        if (al->e->type==EXP_APPL &&
            (al->e->u.appl.functor==INTERN_REG_VECTOR ||
             al->e->u.appl.functor==INTERN_WIRE_VECTOR ||
             al->e->u.appl.functor==INTERN_INPUT_VECTOR ||
             al->e->u.appl.functor==INTERN_OUTPUT_VECTOR ||
             al->e->u.appl.functor==INTERN_INOUT_VECTOR ||
             al->e->u.appl.functor==INTERN_REG ||
             al->e->u.appl.functor==INTERN_WIRE ||
             al->e->u.appl.functor==INTERN_INPUT ||
             al->e->u.appl.functor==INTERN_OUTPUT ||
             al->e->u.appl.functor==INTERN_INOUT) &&
            al->e->u.appl.count >= 1 &&
            al->e->u.appl.args[0]->type==EXP_STRING &&
            _th_intern(al->e->u.appl.args[0]->u.string)==(int)var) {
            if (al->e->u.appl.count==3 &&
                al->e->u.appl.args[1]->type==EXP_INTEGER &&
                al->e->u.appl.args[2]->type==EXP_INTEGER) {
                *hi = (int)al->e->u.appl.args[1]->u.integer[1];
                *lo = (int)al->e->u.appl.args[1]->u.integer[2];
            } else {
                *hi = *lo = -1;
            }
            *decl = al->e->u.appl.functor;
            return;
        }
        al = al->next;
    }
    *hi = *lo = -1;
}

struct _ex_intern *cut_assertion(struct module_list *module,
                                 struct _ex_intern *assertion,
                                 struct _ex_intern *cut)
{
    if (cut->u.appl.args[0]->u.appl.functor==INTERN_VEC_INDEX) {
        if (assertion->u.appl.args[0]->u.appl.functor==INTERN_VEC_INDEX) {
            int al, ah, cl, ch;
            ah = assertion->u.appl.args[0]->u.appl.args[1]->u.integer[1];
            al = assertion->u.appl.args[0]->u.appl.args[2]->u.integer[1];
            ch = cut->u.appl.args[0]->u.appl.args[1]->u.integer[1];
            cl = cut->u.appl.args[0]->u.appl.args[2]->u.integer[1];
            if (cl > ah || al > ch) return assertion;
            if (cl==al && ch==ah) {
                goto assert;
            }
            printf("Error: Cannot handle overlapping bit index ranges\n");
            return assertion;
        } else {
            int cl, ch, rl, rh, d;
            int count;
            struct _ex_intern *args[5];
            struct _ex_intern *low_assert, *high_assert, *assert1;
            ch = cut->u.appl.args[0]->u.appl.args[1]->u.integer[1];
            cl = cut->u.appl.args[0]->u.appl.args[2]->u.integer[1];
            get_range(_th_intern(assertion->u.appl.args[0]->u.appl.args[0]->u.string),
                      module,&rh,&rl,&d);
            if (cl==rl) {
                low_assert = NULL;
            } else {
                low_assert = _th_flatten(verilog_env,_ex_intern_appl6_env(verilog_env,INTERN_ASSIGN,
                    _ex_intern_appl3_env(verilog_env,INTERN_VEC_INDEX,
                        assertion->u.appl.args[0],
                        _ex_intern_small_integer(cl-1),
                        _ex_intern_small_integer(rl)),
                    _ex_intern_appl3_env(verilog_env,INTERN_VEC_INDEX,
                        assertion->u.appl.args[1],
                        _ex_intern_small_integer(cl-1),
                        _ex_intern_small_integer(rl)),
                    assertion->u.appl.args[2],
                    assertion->u.appl.args[3],
                    _ex_intern_appl1_env(verilog_env,INTERN_DELAY,_ex_intern_small_integer(0)),
                    assertion->u.appl.args[5]));
            }
            if (ch==rh) {
                high_assert = NULL;
            } else {
                high_assert = _th_flatten(verilog_env,_ex_intern_appl6_env(verilog_env,INTERN_ASSIGN,
                    _ex_intern_appl3_env(verilog_env,INTERN_VEC_INDEX,
                        assertion->u.appl.args[0],
                        _ex_intern_small_integer(rh),
                        _ex_intern_small_integer(ch+1)),
                    _ex_intern_appl3_env(verilog_env,INTERN_VEC_INDEX,
                        assertion->u.appl.args[1],
                        _ex_intern_small_integer(rh),
                        _ex_intern_small_integer(ch+1)),
                    assertion->u.appl.args[2],
                    assertion->u.appl.args[3],
                    _ex_intern_appl1_env(verilog_env,INTERN_DELAY,_ex_intern_small_integer(0)),
                    assertion->u.appl.args[5]));
            }
            assert1 = _th_flatten(verilog_env,_ex_intern_appl6_env(verilog_env,INTERN_ASSIGN,
                cut->u.appl.args[0],
                _ex_intern_appl3_env(verilog_env,INTERN_VEC_INDEX,
                assertion->u.appl.args[1],
                _ex_intern_small_integer(ch),
                _ex_intern_small_integer(cl)),
                _ex_intern_appl2_env(verilog_env,INTERN_AND,
                    assertion->u.appl.args[2],
                    _ex_intern_appl1_env(verilog_env,INTERN_NOT,cut->u.appl.args[2])),
                assertion->u.appl.args[3],
                _ex_intern_appl1_env(verilog_env,INTERN_DELAY,_ex_intern_small_integer(0)),
                assertion->u.appl.args[5]));
            args[0] = assert1;
            count = 1;
            if (low_assert) args[count++] = low_assert;
            if (high_assert) args[count++] = high_assert;
            return _ex_intern_appl_env(verilog_env,INTERN_AND,count,args);
        }
    } else {
assert:
        return _th_flatten(verilog_env,_ex_intern_appl6_env(verilog_env,INTERN_ASSIGN,
            assertion->u.appl.args[0],
            assertion->u.appl.args[1],
            _ex_intern_appl2_env(verilog_env,INTERN_AND,
                assertion->u.appl.args[2],
                _ex_intern_appl1_env(verilog_env,INTERN_NOT,cut->u.appl.args[2])),
            assertion->u.appl.args[3],
            _ex_intern_appl1_env(verilog_env,INTERN_DELAY,_ex_intern_small_integer(0)),
            assertion->u.appl.args[5]));
    }
}

int expansion_count = 0;

void expand_assertion(struct add_list *al)
{
    struct add_list *aln;
    int i;

    //printf("Expanding\n%s\n", _th_pp_print(verilog_env, INTERN_DEFAULT, 80, al->e));
    if (al->e->u.appl.functor==INTERN_AND) {
        for (i = 1; i < al->e->u.appl.count; ++i) {
            ++expansion_count;
            //if (expansion_count > 100) {
            //    printf("Error: too many assertions\n");
            //    exit(1);
            //}
            aln = (struct add_list *)_th_alloc(module_space,sizeof(struct add_list));
            aln->next = al->next;
            //aln->e = _th_rewrite(verilog_env,al->e->u.appl.args[i]);
            aln->e = al->e->u.appl.args[i];
            //printf("    term: %s\n", _th_print_exp(aln->e));
            if (aln->e->u.appl.args[2]==_ex_false) aln->e = _ex_false;
            al->next = aln;
        }
        //printf("Processing\n%s\n", _th_pp_print(verilog_env, INTERN_DEFAULT, 80, al->e));
        //al->e = _th_rewrite(verilog_env,al->e->u.appl.args[0]);
        al->e = al->e->u.appl.args[0];
        //printf("    term: %s\n", _th_pp_print(verilog_env, INTERN_DEFAULT, 80, al->e));
    } else {
        //al->e = _th_rewrite(verilog_env,al->e);
        //printf("    term: %s\n", _th_pp_print(verilog_env, INTERN_DEFAULT, 80, al->e));
    }
    if (al->e->u.appl.args[2]==_ex_false) al->e = _ex_false;
}

void process_assertions(struct module_list *module, struct assign_group *group)
{
    struct add_list *al, *a, *aln, *cut;
    int count = 0;

    al = group->assigns;

    while (al != NULL) {
        ++count;
        //printf("Info:        a: %s\n", _th_print_exp(al->e));
        al = al->next;
    }

    printf("Info:     process_assertions %s %d\n", _th_intern_decode(group->variable), count);

    al = group->assigns;

    expansion_count = 0;

    while (al != NULL) {
        cut = aln = al->next;
        while (cut != NULL) {
            if (cut->e != _ex_false) {
                a = al;
                while (a != aln) {
                    struct add_list *an = a->next;
                    if (a->e != _ex_false) {
                        int do_pr = 0;
                        //if (a->e->u.appl.args[0] != a->e->u.appl.args[1]) {
                        //if (count==3) {
                        //    printf("Cutting %s\n", _th_print_exp(a->e));
                        //    printf("    with %s\n", _th_print_exp(cut->e));
                        //    do_pr = 1;
                        //}
                        a->e = cut_assertion(module, a->e, cut->e);
                        //if (do_pr) printf("    Result %s\n", _th_print_exp(a->e));
                        expand_assertion(a);
                    }
                    a = an;
                }
            }
            cut = cut->next;
        }
        al = aln;
    }

    al = NULL;
    aln = group->assigns;
    
    while (aln != NULL) {
        aln->e = _th_rewrite(verilog_env,aln->e);
        if (aln->e==_ex_false || aln->e->u.appl.args[2]==_ex_false) {
            if (al==NULL) {
                group->assigns = aln->next;
            } else {
                al->next = aln->next;
            }
            aln = aln->next;
        } else {
            aln->e = instantiate_assertion(verilog_env,module,module,NULL,aln->e);
            al = aln;
            aln = aln->next;
        }
    }

    group->cut_processed = 1;
}

#ifdef CONDITION_CHECK
int is_c_used(struct _ex_intern *rule_c, struct _ex_intern *condition)
{
    int i, j;

    if (rule_c==condition) return 1;

    if (rule_c->type==EXP_APPL && rule_c->u.appl.functor==INTERN_NC_AND) {
        for (i = 0; i < rule_c->u.appl.count; ++i) {
            if (is_c_used(rule_c->u.appl.args[i], condition)) return 1;
        }
    }

    if (rule_c->type==EXP_APPL &&
        (rule_c->u.appl.functor==INTERN_AND || rule_c->u.appl.functor==INTERN_OR) &&
        condition->type==EXP_APPL &&
        rule_c->u.appl.functor==condition->u.appl.functor) {
        for (i = 0; i < condition->u.appl.count; ++i) {
            for (j = 0; j < rule_c->u.appl.count; ++j) {
                if (condition->u.appl.args[i]==rule_c->u.appl.args[j]) goto next;
            }
            goto cont;
next:;
        }
    }
cont:

    if (rule_c->type==EXP_APPL &&
        (rule_c->u.appl.functor==INTERN_AND || rule_c->u.appl.functor==INTERN_OR)) {
        for (i = 0; i < rule_c->u.appl.count; ++i) {
            if (is_c_used(rule_c->u.appl.args[i], condition)) return 1;
        }
    }

    return 0;
}

int is_condition_used(struct _ex_intern *rule, struct _ex_intern *condition)
{
    return is_c_used(rule->u.appl.args[2], condition);
}

struct add_list *build_condition_list(struct module_list *module, struct _ex_intern *rule)
{
    int i;
    struct add_list *result, *r;

    result = NULL;

    for (i = 0; i < module->condition_node_count; ++i) {
        if (is_condition_used(rule, module->condition_nodes[i].condition) {
            r = (struct add_list *)_th_alloc(module_space, sizeof(struct add_list));
            r->next = result;
            result = r;
            r->e = module->condition_nodes[i].condition;
        }
    }

    return result;
}

struct add_list *get_rule_conditions(struct module_list *module, struct _ex_intern *rule)
{
    struct applicable_conditions *conds;
    int hash = (((int)rule)/4)%RULE_HASH_SIZE;
    conds = module->applicable_rules[hash];
    while (conds != NULL) {
        if (conds->exp==rule) return conds->conditions;
        conds = conds->next;
    }
    conds = (struct applicable_conditions *)_th_alloc(module_space,sizeof(struct applicable_conditions));
    conds->next = module->applicable_rules[hash];
    module->applicable_rules[hash] = conds;
    conds->conditions = build_condition_list(module, rule);
    return conds->conditions;
}
#endif

struct effects_list *find_effects_list(struct module_list *module, char *var)
{
    struct variable_list *vars = module->effects;

    while (vars  && strcmp(var,vars->variable)) {
        vars = vars->next;
    }

    if (!vars) return NULL;
    return vars->effects_list;
}

int add_effects(struct module_list *module, char *var, char *effect)
{
    struct variable_list *vars = module->effects;
    struct effects_list *effects;

    //_tree_print2("Adding effect %s %s", var, effect);

    while (vars != NULL) {
        if (!strcmp(vars->variable,var)) break;
        vars = vars->next;
    }

    if (vars==NULL) {
        vars = (struct variable_list *)_th_alloc(module_space,sizeof(struct variable_list));
        vars->next = module->effects;
        module->effects = vars;
        vars->variable = var;
        vars->effects_list = NULL;
    }

    effects = vars->effects_list;

    while (effects != NULL) {
        if (!strcmp(effects->variable, effect)) return 0;
        effects = effects->next;
    }

    effects = (struct effects_list *)_th_alloc(module_space,sizeof(struct effects_list));
    effects->next = vars->effects_list;
    effects->variable = effect;
    vars->effects_list = effects;

    return 1;
}

void effect_transitive_closure(struct module_list *module)
{
    int added_effects = 1;
    struct variable_list *var1;
    struct effects_list *effects1, *effects2;

    while (added_effects) {
        added_effects = 0;

        var1 = module->effects;
        while (var1 != NULL) {
            effects1 = var1->effects_list;
            while (effects1 != NULL) {
                effects2 = find_effects_list(module,effects1->variable);
                while (effects2 != NULL) {
                    if (add_effects(module,var1->variable,effects2->variable)) {
                        added_effects = 1;
                    }
                    effects2 = effects2->next;
                }
                effects1 = effects1->next;
            }
            var1 = var1->next;
        }
    }
}

void add_assign_exp_effects(struct module_list *module, char *var, struct _ex_intern *exp)
{
    int i;

    switch (exp->type) {

         case EXP_APPL:
             if (exp->u.appl.count==2 &&
                 exp->u.appl.functor==INTERN_REFERENCE &&
                 exp->u.appl.args[0]->type==EXP_STRING) {
                 add_effects(module, var, exp->u.appl.args[0]->u.string);
             }
             for (i = 0; i < exp->u.appl.count; ++i) {
                 add_assign_exp_effects(module, var, exp->u.appl.args[i]);
             }
             break;

         case EXP_QUANT:
             add_assign_exp_effects(module, var, exp->u.quant.exp);
             add_assign_exp_effects(module, var, exp->u.quant.cond);
             break;

    }
}

static void add_assign_effects(struct module_list *module, struct _ex_intern *exp)
{
    char *var = "";
    if (exp->u.appl.args[0]->type==EXP_APPL &&
        exp->u.appl.args[0]->u.appl.functor==INTERN_REFERENCE) {
        var = exp->u.appl.args[0]->u.appl.args[0]->u.string;
    }
    _tree_print2("Adding effects %s %s", var, _th_print_exp(exp->u.appl.args[1]));
    _tree_print2("Adding effects %s %s", var, _th_print_exp(exp->u.appl.args[2]));
    _tree_print2("Adding effects %s %s", var, _th_print_exp(exp->u.appl.args[3]));
    add_assign_exp_effects(module, var, exp->u.appl.args[1]);
    add_assign_exp_effects(module, var, exp->u.appl.args[2]);
    add_assign_exp_effects(module, var, exp->u.appl.args[3]);
}

static void build_condition_edge_tree(struct module_list *module)
{
    struct add_list *al;
    int nodes = 0;
    int node;
    int parent;
    struct child_edge_list *child;
    struct module_pointer_list *mpl;
    struct variable_list *var;
    struct effects_list *effects;

    fprintf(stderr,"Processing module %s\n", _th_intern_decode(module->name));

    nodes = condition_count(module->declarations);
    fprintf(stderr, "nodes = %d\n", nodes);
    mpl = module->children;
    while (mpl != NULL) {
        nodes += condition_count(mpl->instantiation);
        mpl = mpl->next;
    }
    fprintf(stderr, "inst nodes = %d\n", nodes);
    module->condition_node_count = nodes;
    module->condition_nodes = (struct condition_node *)_th_alloc(module_space,sizeof(struct condition_node) * nodes);
    memset(module->condition_nodes,0,sizeof(struct condition_node) * nodes);

    al = module->declarations;
    while (al != NULL) {
        if (al->e->type==EXP_APPL) {
            if (al->e->u.appl.functor==INTERN_ASSIGN) {
                _tree_print_exp("Assign", al->e);
                _tree_indent();
                add_assign_effects(module, al->e);
                _tree_undent();
            }
        }
        al = al->next;
    }
    mpl = module->children;
    while (mpl != NULL) {
        al = mpl->instantiation;
        while (al != NULL) {
            if (al->e->type==EXP_APPL && al->e->u.appl.functor==INTERN_ASSIGN) {
                _tree_print_exp("Inst assign", al->e);
                _tree_indent();
                add_assign_effects(module, al->e);
                _tree_undent();
            }
            al = al->next;
        }
        mpl = mpl->next;
    }

    _tree_print0("Var effects");
    _tree_indent();
    var = module->effects;
    while (var != NULL) {
        _tree_print1("Var: %s effected by", var->variable);
        effects = var->effects_list;
        _tree_indent();
        while (effects != NULL) {
            _tree_print1("%s", effects->variable);
            effects = effects->next;
        }
        _tree_undent();
        var = var->next;
    }
    _tree_undent();
    effect_transitive_closure(module);
    _tree_print0("Var effects (Transitive closure)");
    _tree_indent();
    var = module->effects;
    while (var != NULL) {
        _tree_print1("Var: %s effected by", var->variable);
        effects = var->effects_list;
        _tree_indent();
        while (effects != NULL) {
            _tree_print1("%s", effects->variable);
            effects = effects->next;
        }
        _tree_undent();
        var = var->next;
    }
    _tree_undent();

    al = module->declarations;
    while (al != NULL) {
        if (al->e->type==EXP_APPL) {
            if (al->e->u.appl.functor==INTERN_CONDITION_ROOT) {
                node = al->e->u.appl.args[0]->u.integer[1];
                fprintf(stderr, "Root node %d\n", node);
                fflush(stderr);
                module->condition_nodes[node].parent = -1;
                module->condition_nodes[node].branch = 0;
                module->condition_nodes[node].variable_list = NULL;
                printf("Edge: %s\n", _th_print_exp(al->e));
            } else if (al->e->u.appl.functor==INTERN_CONDITION_EDGE) {
                node = al->e->u.appl.args[1]->u.integer[1];
                fprintf(stderr, "Node: %d\n", node);
                fflush(stderr);
                parent = al->e->u.appl.args[0]->u.integer[1];
                module->condition_nodes[node].parent = parent;
                module->condition_nodes[node].branch = al->e->u.appl.args[2]->u.integer[1];
                module->condition_nodes[node].condition = al->e->u.appl.args[3];
                module->condition_nodes[node].variable_list = NULL;
                child = (struct child_edge_list *)_th_alloc(module_space,sizeof(struct child_edge_list));
                child->next = module->condition_nodes[parent].children;
                module->condition_nodes[parent].children = child;
                child->child = node;
                printf("Cond: %s\n", _th_print_exp(al->e));
            }
        }
        al = al->next;
    }

    al = module->declarations;
    while (al != NULL) {
        if (al->e->type==EXP_APPL) {
            if (al->e->u.appl.functor==INTERN_CONDITION_VARIABLE) {
                int node = al->e->u.appl.args[0]->u.integer[1];
                while (node >= 0 && node < module->condition_node_count) {
                    char *var;
                    struct variable_list *vl;
                    node = module->condition_nodes[node].branch;
                    if (node >= 0) {
                        vl = module->condition_nodes[node].variable_list;
                        var = al->e->u.appl.args[1]->u.string;
                        while (vl != NULL) {
                            if (!strcmp(vl->variable,var)) goto finish;
                            vl = vl->next;
                        }
                        vl = (struct variable_list *)_th_alloc(module_space,sizeof(struct variable_list));
                        vl->next = module->condition_nodes[node].variable_list;
                        module->condition_nodes[node].variable_list = vl;
                        vl->variable = var;
                        vl->effects_list = find_effects_list(module, var);
                        fprintf(stderr, "Added variable %d %s\n", node, var);
                        fflush(stderr);
                    }
finish:;
                    node = module->condition_nodes[node].parent;
                }
            }
        }
        al = al->next;
    }

    mpl = module->children;
    while (mpl != NULL) {
        al = mpl->instantiation;
        while (al != NULL) {
            if (al->e->type==EXP_APPL) {
                if (al->e->u.appl.functor==INTERN_CONDITION_ROOT) {
                    node = al->e->u.appl.args[0]->u.integer[1];
                    module->condition_nodes[node].branch = -1;
                    module->condition_nodes[node].parent = -1;
                    printf("Edge: %s\n", _th_print_exp(al->e));
                } else if (al->e->u.appl.functor==INTERN_CONDITION_EDGE) {
                    node = al->e->u.appl.args[1]->u.integer[1];
                    module->condition_nodes[node].branch = al->e->u.appl.args[2]->u.integer[1];
                    parent = al->e->u.appl.args[0]->u.integer[1];
                    module->condition_nodes[node].parent = parent;
                    module->condition_nodes[node].condition = al->e->u.appl.args[3];
                    child = (struct child_edge_list *)_th_alloc(module_space,sizeof(struct child_edge_list));
                    child->next = module->condition_nodes[parent].children;
                    module->condition_nodes[parent].children = child;
                    child->child = node;
                    printf("Cond: %s\n", _th_print_exp(al->e));
                }
            }
            al = al->next;
        }
        mpl = mpl->next;
    }
}

static void build_trigger_order(struct module_list *module)
{
    struct add_list *al;
    struct module_pointer_list *mpl;
    int i;

    module->trigger_order = NULL;
    al = module->declarations;
    while (al != NULL) {
        if (al->e->type==EXP_APPL && al->e->u.appl.functor==INTERN_ASSIGN) {
            module->trigger_order = add_trigger_order(module->trigger_order, al->e);
        }
        al = al->next;
    }
    mpl = module->children;
    while (mpl != NULL) {
        al = mpl->instantiation;
        while (al != NULL) {
            if (al->e->type==EXP_APPL && al->e->u.appl.functor==INTERN_ASSIGN) {
                module->trigger_order = add_trigger_order(module->trigger_order, al->e);
            }
            al = al->next;
        }
        mpl = mpl->next;
    }

    for (i = 0; i < module->condition_node_count; ++i) {
        if (module->condition_nodes[i].condition) {
            printf("Building node triggers for %d %s\n", i, _th_print_exp(module->condition_nodes[i].condition));
            module->condition_nodes[i].parents = add_node_triggers(module->trigger_order, NULL, module->condition_nodes[i].condition);
        }
    }
}

static void print_trigger_order(struct module_list *module)
{
    struct trigger_order *t = module->trigger_order;
    struct trigger_order_list *l;

    printf("Info: TRIGGER ORDER FOR %s\n", _th_intern_decode(module->name));
    while (t != NULL) {
        printf("Info: Var: %s\n", _th_intern_decode(t->var));
        l = t->parents;
        if (l) {
            printf("Info:     Parents:\n");
            while (l != NULL) {
                printf("Info:         %s\n", _th_intern_decode(l->order->var));
                l = l->next;
            }
        }
        l = t->children;
        if (l) {
            printf("Info:     Children:\n");
            while (l != NULL) {
                printf("Info:         %s\n", _th_intern_decode(l->order->var));
                l = l->next;
            }
        }
        t = t->next;
    }
}

static int smaller_var(struct module_list *module, char *var1, char *var2)
{
    struct trigger_order *t = module->trigger_order;
    struct trigger_order_list *l;
    unsigned v1 = _th_intern(var1), v2 = _th_intern(var2);

    while (t != NULL) {
        if (t->var==v1) {
            l = t->children;
            while (l != NULL) {
                if (l->order->var==v2) return 1;
                l = l->next;
            }
            return 0;
        }
        t = t->next;
    }
    return 0;
}

int has_loop_back(struct trigger_order *child, struct trigger_order *start)
{
    struct trigger_order_list *l;

    if (child==start) return 1;

    l = child->children;
    while (l) {
        if (has_loop_back(l->order, start)) return 1;
        l = l->next;
    }

    return 0;
}

int has_circular_reference(struct trigger_order *t)
{
    struct trigger_order_list *list;

    list = t->children;
    while (list != NULL) {
        if (has_loop_back(list->order, t)) return 1;
        list = list->next;
    }

    return 0;
}

int check_for_trigger_errors(struct module_list *module)
{
    struct trigger_order *t = module->trigger_order;
    int error = 0;

    while (t != NULL) {
        if (has_circular_reference(t)) {
            error = 1;
            printf("Error: Circular reference for %s in module %s\n",
                _th_intern_decode(t->var), _th_intern_decode(module->name));
        }
        t = t->next;
    }

    return error;
}

struct _ex_intern *substitute_assign(struct env *env, struct _ex_intern *exp, struct _ex_intern *reference, struct _ex_intern *value)
{
    int i;
    struct _ex_intern *c, *e;
    struct _ex_intern **args;
    /**********/

    switch (exp->type) {

        case EXP_APPL:
            if (exp==reference) return value;
            if (exp->u.appl.functor==INTERN_EDGE &&
                reference->u.appl.args[0]==exp->u.appl.args[0] &&
                reference->u.appl.args[1]==exp->u.appl.args[1]) {
                return _ex_intern_appl1_env(env,INTERN_NOT,
                    _ex_intern_appl2_env(env,INTERN_EQUAL,reference,value));
            }
            if (exp->u.appl.functor==INTERN_POSEDGE &&
                reference->u.appl.args[0]==exp->u.appl.args[0] &&
                reference->u.appl.args[1]==exp->u.appl.args[1]) {
                return _ex_intern_appl2_env(env,INTERN_AND,
                    _ex_intern_appl2_env(env,INTERN_EQUAL,reference,_ex_intern_small_integer(0)),
                    _ex_intern_appl1_env(env,INTERN_NOT,
                        _ex_intern_appl2_env(env,INTERN_EQUAL,value,_ex_intern_small_integer(0))));
            }
            if (exp->u.appl.functor==INTERN_NEGEDGE &&
                reference->u.appl.args[0]==exp->u.appl.args[0] &&
                reference->u.appl.args[1]==exp->u.appl.args[1]) {
                return _ex_intern_appl2_env(env,INTERN_AND,
                    _ex_intern_appl2_env(env,INTERN_EQUAL,value,_ex_intern_small_integer(0)),
                    _ex_intern_appl1_env(env,INTERN_NOT,
                        _ex_intern_appl2_env(env,INTERN_EQUAL,reference,_ex_intern_small_integer(0))));
            }
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count);
            for (i = 0; i < exp->u.appl.count; ++i) {
                args[i] = substitute_assign(env,exp->u.appl.args[i],reference,value);
            }
            return _ex_intern_appl_env(env,exp->u.appl.functor,exp->u.appl.count,args);

        case EXP_QUANT:
            e = substitute_assign(env, exp->u.quant.exp, reference, value);
            c = substitute_assign(env, exp->u.quant.cond, reference, value);
            return _ex_intern_quant(exp->u.quant.quant,exp->u.quant.var_count,exp->u.quant.vars,e,c);

        default:
            return exp;
    }
}

struct _ex_intern *advance_references(struct env *env, struct _ex_intern *exp, unsigned var)
{
    int i;
    struct _ex_intern *c, *e;
    struct _ex_intern **args;
    char *variable;

    /**********/

    switch (exp->type) {

        case EXP_APPL:
            variable = _th_intern_decode(var);

            if ((exp->u.appl.functor==INTERN_REFERENCE ||
                 exp->u.appl.functor==INTERN_EDGE ||
                 exp->u.appl.functor==INTERN_POSEDGE ||
                 exp->u.appl.functor==INTERN_NEGEDGE) &&
                exp->u.appl.args[0]->type==EXP_STRING &&
                !strcmp(exp->u.appl.args[0]->u.string,variable)) {
                return _ex_intern_appl2_env(env,exp->u.appl.functor,
                            exp->u.appl.args[0],
                            _ex_intern_appl3_env(env,INTERN_NEXT,
                                exp->u.appl.args[1],
                                _ex_intern_string("CLK"),
                                _ex_intern_small_integer(1)));
            }
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count);
            for (i = 0; i < exp->u.appl.count; ++i) {
                args[i] = advance_references(env,exp->u.appl.args[i],var);
            }
            return _ex_intern_appl_env(env,exp->u.appl.functor,exp->u.appl.count,args);

        case EXP_QUANT:
            e = advance_references(env, exp->u.quant.exp, var);
            c = advance_references(env, exp->u.quant.cond, var);
            return _ex_intern_quant(exp->u.quant.quant,exp->u.quant.var_count,exp->u.quant.vars,e,c);

        default:
            return exp;
    }
}

int needs_substitute(struct env *env, struct _ex_intern *exp, struct _ex_intern *reference)
{
    int i;

    /**********/

    switch (exp->type) {

        case EXP_APPL:
            if (exp==reference) return 1;
            if (exp->u.appl.functor==INTERN_EDGE &&
                reference->u.appl.args[0]==exp->u.appl.args[0] &&
                reference->u.appl.args[1]==exp->u.appl.args[1]) {
                return 1;
            }
            if (exp->u.appl.functor==INTERN_POSEDGE &&
                reference->u.appl.args[0]==exp->u.appl.args[0] &&
                reference->u.appl.args[1]==exp->u.appl.args[1]) {
                return 1;
            }
            if (exp->u.appl.functor==INTERN_NEGEDGE &&
                reference->u.appl.args[0]==exp->u.appl.args[0] &&
                reference->u.appl.args[1]==exp->u.appl.args[1]) {
                return 1;
            }
            for (i = 0; i < exp->u.appl.count; ++i) {
                if (needs_substitute(env,exp->u.appl.args[i],reference)) return 1;
            }
            return 0;

        case EXP_QUANT:
            if (needs_substitute(env, exp->u.quant.exp, reference)) return 1;
            return needs_substitute(env, exp->u.quant.cond, reference);

        default:
            return 0;
    }
}

struct _ex_intern *substitute_condition(struct env *env, struct _ex_intern *exp, struct assign_group *parent)
{
    struct add_list *p;
    struct _ex_intern *cond1, *rhs;

    if (exp->type==EXP_APPL && (exp->u.appl.functor==INTERN_AND || exp->u.appl.functor==INTERN_OR)) {
        struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count);
        int i;
        for (i = 0; i < exp->u.appl.count; ++i) {
            if (needs_substitute(env,exp->u.appl.args[i],parent->assigns->e->u.appl.args[0])) {
                args[i] = substitute_condition(env,exp->u.appl.args[i],parent);
            } else {
                args[i] = exp->u.appl.args[i];
            }
        }
        return _th_flatten(env,_ex_intern_appl_env(env,exp->u.appl.functor,exp->u.appl.count,args));
    }

    p = parent->assigns;
    cond1 = _ex_false;
    printf("Info:     parents\n");
    while (p != NULL) {
        printf("Info:     p: %s\n", _th_print_exp(p->e));
        rhs = _ex_intern_appl2_env(verilog_env,INTERN_AND,
            p->e->u.appl.args[2],
            substitute_assign(
                verilog_env,
                exp,
                p->e->u.appl.args[0],
                p->e->u.appl.args[1]));
        rhs = _th_rewrite(env,rhs);
        if (rhs==_ex_true) return _ex_true;
        if (rhs != _ex_false) {
            if (cond1==_ex_false) {
                cond1 = rhs;
            } else {
                cond1 = _th_flatten(verilog_env,
                    _ex_intern_appl2_env(verilog_env,INTERN_OR,cond1,rhs));
            }
        }
        p = p->next;
    }

    return cond1;
}

void substitute_group(struct module_list *module, struct assign_group *group, struct assign_group *parent)
{
    struct add_list *a;

#ifdef OLD_CODE
    nl = NULL;
#endif
    _tree_print1("substitute group %s", _th_intern_decode(parent->variable));
    _tree_indent();
    a = group->assigns;
    printf("Info: Substitute group %s %s %s\n",
        _th_intern_decode(module->name),
        _th_intern_decode(group->variable),
        _th_intern_decode(parent->variable));
    while (a != NULL) {
        _tree_print_exp("old", a->e);
        a->e = advance_references(verilog_env,a->e,parent->variable);
        _tree_print_exp("new", a->e);
#ifdef OLD_CODE
        if (needs_substitute(verilog_env,a->e->u.appl.args[1],parent->assigns->e->u.appl.args[0])) {
            p = parent->assigns;
            while (p != NULL) {
                printf("Info:     Matrix substitute %s %s %s\n",
                    _th_intern_decode(module->name),
                   _th_intern_decode(group->variable),
                    _th_intern_decode(parent->variable));
                printf("Info:     Matrix substituting %s\n", _th_print_exp(a->e));
                printf("Info:     With %s\n", _th_print_exp(p->e));
                rhs = substitute_assign(verilog_env,
                    a->e->u.appl.args[1],
                    p->e->u.appl.args[0],
                    p->e->u.appl.args[1]);
                cond = substitute_assign(verilog_env,
                    a->e->u.appl.args[2],
                    p->e->u.appl.args[0],
                    p->e->u.appl.args[1]);
                cond = _th_flatten(verilog_env,_ex_intern_appl2_env(verilog_env,INTERN_AND,cond,p->e->u.appl.args[2]));
                cond = _th_rewrite(verilog_env,cond);
                if (cond != _ex_false) {
                    rhs = _ex_intern_appl6_env(verilog_env,
                        INTERN_ASSIGN,
                        a->e->u.appl.args[0],
                        rhs,
                        cond,
                        a->e->u.appl.args[3],
                        a->e->u.appl.args[4],
                        a->e->u.appl.args[5]);
                    n = (struct add_list *)_th_alloc(module_space,sizeof(struct add_list));
                    n->next = nl;
                    nl = n;
                    n->e = rhs;
                    printf("Info:     Adding %s\n", _th_print_exp(n->e));
                }
                p = p->next;
            }
        } else if (needs_substitute(verilog_env,a->e->u.appl.args[2],parent->assigns->e->u.appl.args[0])) {
            printf("Info:     Cond substitute %s %s %s\n",
                _th_intern_decode(module->name),
                _th_intern_decode(group->variable),
                _th_intern_decode(parent->variable));
            printf("Info:     Condition Substituting %s\n", _th_print_exp(a->e));
            cond = substitute_condition(verilog_env,a->e->u.appl.args[2],parent);
            n = (struct add_list *)_th_alloc(module_space,sizeof(struct add_list));
            n->next = nl;
            nl = n;
            n->e = _ex_intern_appl6_env(verilog_env,INTERN_ASSIGN,
                       a->e->u.appl.args[0],
                       a->e->u.appl.args[1],
                       cond,
                       a->e->u.appl.args[3],
                       a->e->u.appl.args[4],
                       a->e->u.appl.args[5]);
            n->e = _th_rewrite(verilog_env,n->e);
            printf("Info:     result %s\n", _th_print_exp(n->e));
        } else {
            n = (struct add_list *)_th_alloc(module_space,sizeof(struct add_list));
            n->next = nl;
            nl = n;
            n->e = a->e;
        }
#endif
        a = a->next;
    }
#ifdef OLD_CODE
    group->assigns = nl;
#endif
    _tree_undent();
}

int group_built(struct module_list *module, unsigned var)
{
    struct assign_group *g;

    g = module->groups;
    while (g != NULL) {
        if (g->variable==var) return g->cut_processed;
        g = g->next;
    }

    return 1;
}

int all_parents_built(struct module_list *module, unsigned var)
{
    struct trigger_order *t = module->trigger_order;
    struct trigger_order_list *l;

    while (t != NULL) {
        if (t->var==var) break;
        t = t->next;
    }
    if (t==NULL) return 1;
    l = t->parents;
    while (l != NULL) {
        if (!group_built(module,l->order->var)) return 0;
        l = l->next;
    }
    return 1;
}

#define NEW_CODE
void build_assertions(struct module_list *module)
{
    struct add_list *al;
    struct module_pointer_list *mpl;
    struct assign_group *group;
    //int i;

#ifdef NEW_CODE
    struct trigger_order *order;
    int cycle;
#endif

    _tree_print1("Building assertions for %s", _th_intern_decode(module->name));
    _tree_indent();

    _tree_print0("Adding assigns");
    _tree_indent();
    module->groups = NULL;
    al = module->declarations;
    while (al != NULL) {
        if (al->e->type==EXP_APPL && al->e->u.appl.functor==INTERN_ASSIGN) {
            _tree_print_exp("Adding assign", al->e);
            _tree_indent();
            module->groups = add_assign_to_group(module->groups, al->e);
            _tree_undent();
        }
        al = al->next;
    }
    mpl = module->children;
    while (mpl != NULL) {
        al = mpl->instantiation;
        while (al != NULL) {
            if (al->e->type==EXP_APPL && al->e->u.appl.functor==INTERN_ASSIGN) {
                _tree_print_exp("Adding inst assign", al->e);
                _tree_indent();
                module->groups = add_assign_to_group(module->groups, al->e);
                _tree_undent();
            }
            al = al->next;
        }
        mpl = mpl->next;
    }
    _tree_undent();

#ifdef NEW_CODE
    cycle = 1;
    while (cycle) {
        cycle = 0;
        group = module->groups;
        while (group != NULL) {
            if (!group->cut_processed && all_parents_built(module, group->variable)) {
                struct _ex_intern *r;
                _tree_print1("Processing group %s", _th_intern_decode(group->variable));
                _tree_indent();
                order = module->trigger_order;
                while (order != NULL) {
                    if (order->var==group->variable) {
                        struct trigger_order_list *l = order->parents;
                        while (l != NULL) {
                            struct assign_group *parent;
                            parent = module->groups;
                            while (parent != NULL) {
                                if (parent->variable==l->order->var) break;
                                parent = parent->next;
                            }
                            if (parent != NULL) substitute_group(module,group,parent);
                            l = l->next;
                        }
                        break;
                    }
                    order = order->next;
                }
                al = group->assigns;
                while (al != NULL) {
                    struct _ex_unifier *u;
                    char *mark = _th_alloc_mark(MATCH_SPACE);

                    u = _th_new_unifier(MATCH_SPACE);
                    _th_add_pair(MATCH_SPACE,u,INTERN_CURRENT,
                        _ex_intern_appl3_env(verilog_env,INTERN_NEXT,
                            _ex_intern_var(INTERN_CURRENT),
                            _ex_intern_string("CLK"),
                            _ex_intern_small_integer(-1)));

                    al->e = _ex_intern_appl6_env(verilog_env,INTERN_ASSIGN,
                        al->e->u.appl.args[0],
                        _th_subst(verilog_env,u,al->e->u.appl.args[1]),
                        _th_subst(verilog_env,u,al->e->u.appl.args[2]),
                        _th_subst(verilog_env,u,al->e->u.appl.args[3]),
                        al->e->u.appl.args[4],
                        al->e->u.appl.args[5]);
                    _tree_print_exp("new assert", al->e);
                    al = al->next;
                    _th_alloc_release(MATCH_SPACE,mark);
                }
                get_range(group->variable,module,&group->high,&group->low,&group->decl);
                al = (struct add_list *)_th_alloc(module_space,sizeof(struct add_list));
                al->next = group->assigns;
                group->assigns = al;
                r = _ex_intern_appl2_env(verilog_env,INTERN_REFERENCE,
                        _ex_intern_string(_th_intern_decode(group->variable)),
                        _ex_intern_appl3_env(verilog_env,INTERN_NEXT,
                            _ex_intern_var(INTERN_CURRENT),
                            _ex_intern_string("CLK"),
                            _ex_intern_small_integer(-1)));
                al->e = _ex_intern_appl6_env(verilog_env,INTERN_ASSIGN,
                    _ex_intern_appl2_env(verilog_env,INTERN_REFERENCE,
                        _ex_intern_string(_th_intern_decode(group->variable)),
                        _ex_intern_var(INTERN_CURRENT)),
                    r,
                    _ex_true,
                    _ex_true,
                    _ex_intern_appl1_env(verilog_env,INTERN_DELAY,_ex_intern_small_integer(0)),
                    _ex_intern_small_integer(0));
                process_assertions(module,group);
                _tree_undent();
                cycle = 1;
            }
            group = group->next;
        }
    }
#else
    group = module->groups;
    while (group != NULL) {
        struct _ex_intern *r;
        get_range(group->variable,module,&group->high,&group->low,&group->decl);
        al = (struct add_list *)_th_alloc(module_space,sizeof(struct add_list));
        al->next = group->assigns;
        group->assigns = al;
        r = _ex_intern_appl2_env(verilog_env,INTERN_REFERENCE,
            _ex_intern_string(_th_intern_decode(group->variable)),
            _ex_intern_var(INTERN_CURRENT));
        al->e = _ex_intern_appl6_env(verilog_env,INTERN_ASSIGN,
            r,
            r,
            _ex_true,
            _ex_true,
            _ex_intern_appl1_env(verilog_env,INTERN_DELAY,_ex_intern_small_integer(0)),
            _ex_intern_small_integer(0));
        process_assertions(module,group);
        group = group->next;
    }
#endif

#ifdef XX
    for (i = 0; i < module->condition_node_count; ++i) {
        struct trigger_order_list *l = module->condition_nodes[i].parents;
        while (l != NULL) {
            module->condition_nodes[i].condition = _th_rewrite(verilog_env,advance_references(verilog_env,module->condition_nodes[i].condition,l->order->var));
            l = l->next;
        }
    }
#endif

    _tree_undent();
}

int load_model(char *proj)
{
    char line[1000];
    char command[1000], *c;
    int len;
    struct module_list *ml;
    int space;
    FILE *f;
    FILE *project;

    if (module_space==-1) {
        module_space = _th_find_space();
    }

    if (verilog_env==NULL) {
        verilog_env = _th_default_env(ENVIRONMENT_SPACE);
    }

    project = fopen(proj,"r");

    if (project==NULL) {
        printf("Error: No such project\n");
        printf("*END\n0\n");
        return 0;
    }
    while (1) {
        fgets(line,998,project);
        if (feof(project)) break;
        len = strlen(line);
        line[len-1] = 0;
        //printf("Processing '%s' '%s'\n", line, line+len-2);
        if (len > 2 && !strcmp(line+len-3,".v")) {
            sprintf(command, "vl2mv %s", line);
            system(command);
            read_pmv_file(line);
        } else if (len > 5 && !strcmp(line+len-6,".asrt")) {
            read_assert_file(line);
        } else if (len > 4 && !strcmp(line+len-5,".der")) {
            //int space;
            //space = derivation_space[derivation_count] = _th_find_space() ;
            //derivation[derivation_count] = _th_load_derivation(space,line) ;
            //derivation_name[derivation_count] = strdup(line) ;
        }
    }

    instantiate_modules();
    ml = modules;
    //_tree_start = _tree_end = 1294;
    //_tree_sub = _tree_sub2 = -1;
    while (ml != NULL) {
        build_condition_edge_tree(ml);
        fflush(stdout);
        build_trigger_order(ml);
        print_trigger_order(ml);
        check_for_trigger_errors(ml);
        build_assertions(ml);
        ml = ml->next;
    }

    strcpy(line, proj);
    c = line+strlen(line)-1;
    while (c > line && *c != '.') --c;
    if (c==line) {
        c = line+strlen(line);
    }
    strcpy(c, ".der");

    f = fopen(line, "r");
    if (f==NULL) {
        f = fopen(line, "w");
    }
    fclose(f);

    space = _th_derivation_space[_th_derivation_count] = _th_find_space() ;
    _th_derivation[_th_derivation_count] = _th_load_derivation(space,line) ;
    _th_derivation_name[_th_derivation_count] = strdup(line) ;

    verilog_derivation = _th_derivation_count;

    return _th_derivation_count++;
}

struct _ex_intern *build_assign_assertion(struct _ex_intern *assign, char *clock)
{
    if (assign->u.appl.args[0]->u.appl.functor==INTERN_REFERENCE) {
        return _th_flatten(verilog_env,
            _ex_intern_appl3_env(verilog_env,INTERN_UNORIENTED_RULE,
                   _ex_intern_appl2_env(verilog_env,INTERN_REFERENCE,
                       assign->u.appl.args[0]->u.appl.args[0],
                       _ex_intern_appl3_env(verilog_env,INTERN_NEXT,
                           assign->u.appl.args[0]->u.appl.args[1],
                           _ex_intern_string(clock),
                           _ex_intern_small_integer(1))),
                   assign->u.appl.args[1],
                   assign->u.appl.args[2]));
    } else {
        return _th_flatten(verilog_env,
            _ex_intern_appl3_env(verilog_env,INTERN_UNORIENTED_RULE,
                   _ex_intern_appl3_env(verilog_env,INTERN_VEC_INDEX,
                       _ex_intern_appl2_env(verilog_env,INTERN_REFERENCE,
                           assign->u.appl.args[0]->u.appl.args[0]->u.appl.args[0],
                           _ex_intern_appl3_env(verilog_env,INTERN_NEXT,
                               assign->u.appl.args[0]->u.appl.args[0]->u.appl.args[1],
                               _ex_intern_string(clock),
                               _ex_intern_small_integer(1))),
                       assign->u.appl.args[0]->u.appl.args[1],
                       assign->u.appl.args[0]->u.appl.args[2]),
                   assign->u.appl.args[1],
                   assign->u.appl.args[2]));
    }
}

static struct _ex_intern *flatten_nc_and(struct env *env, struct _ex_intern *exp)
{
    int i, j;
    int count;
    struct _ex_intern **args;

    if (exp->type != EXP_APPL || exp->u.appl.functor != INTERN_NC_AND) return exp;

    count = exp->u.appl.count;
    for (i = 0; i < exp->u.appl.count; ++i) {
        if (exp->u.appl.args[i]->type==EXP_APPL &&
            (exp->u.appl.args[i]->u.appl.functor==INTERN_AND ||
             exp->u.appl.args[i]->u.appl.functor==INTERN_NC_AND)) {
            count += exp->u.appl.args[i]->u.appl.count-1;
        }
    }

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
    count = 0;
    for (i = 0; i < exp->u.appl.count; ++i) {
        if (exp->u.appl.args[i]->type==EXP_APPL &&
            (exp->u.appl.args[i]->u.appl.functor==INTERN_AND ||
             exp->u.appl.args[i]->u.appl.functor==INTERN_NC_AND)) {
            for (j = 0; j < exp->u.appl.args[i]->u.appl.count; ++j) {
                args[count++] = exp->u.appl.args[i]->u.appl.args[j];
            }
        } else {
            args[count++] = exp->u.appl.args[i];
        }
    }

    return _ex_intern_appl_env(env,INTERN_NC_AND,count,args);
}

struct _ex_intern *build_assign_assertion_future(struct _ex_intern *assign, char *clock)
{
    struct _ex_unifier *u;
    char *mark = _th_alloc_mark(MATCH_SPACE);

    u = _th_new_unifier(MATCH_SPACE);
    _th_add_pair(MATCH_SPACE,u,INTERN_CURRENT,
        _ex_intern_appl3_env(verilog_env,INTERN_NEXT,
            _ex_intern_var(INTERN_CURRENT),
            _ex_intern_string(clock),
            _ex_intern_var(INTERN_NEXT)));
            //_ex_intern_appl2_env(verilog_env,INTERN_NAT_MINUS,
            //    _ex_intern_var(INTERN_NEXT),
            //    _ex_intern_small_integer(1))));

    if (assign->u.appl.args[0]->u.appl.functor==INTERN_REFERENCE) {
        return _th_rewrite(verilog_env,_th_flatten(verilog_env,
            _ex_intern_appl3_env(verilog_env,INTERN_UNORIENTED_RULE,
                   _ex_intern_appl2_env(verilog_env,INTERN_REFERENCE,
                       assign->u.appl.args[0]->u.appl.args[0],
                       _ex_intern_appl3_env(verilog_env,INTERN_NEXT,
                           assign->u.appl.args[0]->u.appl.args[1],
                           _ex_intern_string(clock),
                           _ex_intern_var(INTERN_NEXT))),
                   _th_subst(verilog_env,u,assign->u.appl.args[1]),
                   _th_subst(verilog_env,u,
                       flatten_nc_and(verilog_env,
                           _ex_intern_appl2_env(verilog_env,INTERN_NC_AND,
                               _ex_intern_appl1_env(verilog_env,INTERN_IN_CONTEXT,_ex_intern_string("mainContext")),
                               //_ex_intern_appl2_env(verilog_env,INTERN_NAT_LESS,
                               //    _ex_intern_small_integer(0),
                               //    _ex_intern_var(INTERN_NEXT)),
                               assign->u.appl.args[2]))))));
    } else {
        return _th_rewrite(verilog_env,_th_flatten(verilog_env,
            _ex_intern_appl3_env(verilog_env,INTERN_UNORIENTED_RULE,
                   _ex_intern_appl3_env(verilog_env,INTERN_VEC_INDEX,
                       _ex_intern_appl2_env(verilog_env,INTERN_REFERENCE,
                           assign->u.appl.args[0]->u.appl.args[0]->u.appl.args[0],
                           _ex_intern_appl3_env(verilog_env,INTERN_NEXT,
                               assign->u.appl.args[0]->u.appl.args[0]->u.appl.args[1],
                               _ex_intern_string(clock),
                               _ex_intern_var(INTERN_NEXT))),
                       assign->u.appl.args[0]->u.appl.args[1],
                       assign->u.appl.args[0]->u.appl.args[2]),
                   _th_subst(verilog_env,u,assign->u.appl.args[1]),
                   _th_subst(verilog_env,u,
                       flatten_nc_and(verilog_env,
                           _ex_intern_appl2_env(verilog_env,INTERN_NC_AND,
                               _ex_intern_appl1_env(verilog_env,INTERN_IN_CONTEXT,_ex_intern_string("mainContext")),
                               //_ex_intern_appl2_env(verilog_env,INTERN_NAT_LESS,
                               //    _ex_intern_small_integer(0),
                               //    _ex_intern_var(INTERN_NEXT)),
                               assign->u.appl.args[2]))))));
    }
}

static char *hnames[2] = { "time_induction", NULL };

struct _ex_intern *find_reference(struct _ex_intern *e)
{
    int i;
    struct _ex_intern *res;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor==INTERN_REFERENCE && e->u.appl.count==2 &&
                e->u.appl.args[1]->type==EXP_VAR) {
                return e;
            }
            for (i = 0; i < e->u.appl.count; ++i) {
                res = find_reference(e->u.appl.args[i]);
                if (res) return res;
            }
            return NULL;

        //case EXP_QUANT:
            //res = find_reference(e->u.quant.exp);
            //if (res) return res;
            //res = find_reference(e->u.quant.cond);
            //return res;

        default:
            return NULL;
    }
}

int no_next_greater_one(struct _ex_intern *e)
{
    int i, res;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor==INTERN_NEXT &&
                e->u.appl.count==3 &&
                (e->u.appl.args[2]->type != EXP_INTEGER ||
                 e->u.appl.args[2]->u.integer[0] != 1 ||
                 e->u.appl.args[2]->u.integer[1] != 1)) {
                return 0;
            }
            for (i = 0; i < e->u.appl.count; ++i) {
                if (!no_next_greater_one(e->u.appl.args[i])) return 0;
            }
            return 1;

        case EXP_QUANT:
            res = no_next_greater_one(e->u.quant.exp);
            if (!res) return 0;
            res = no_next_greater_one(e->u.quant.cond);
            return res;

        default:
            return 1;
    }
}

static int has_reference(struct _ex_intern *e, char *var)
{
    int i;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor==INTERN_REFERENCE && e->u.appl.count==2 &&
                e->u.appl.args[1]->type==EXP_VAR && e->u.appl.args[0]->type==EXP_STRING) {
                return !strcmp(var,e->u.appl.args[0]->u.string);
            }
            for (i = 0; i < e->u.appl.count; ++i) {
                if (has_reference(e->u.appl.args[i], var)) return 1;
            }
            return 0;

        case EXP_QUANT:
            if (has_reference(e->u.quant.exp, var)) return 1;
            return has_reference(e->u.quant.cond, var);

        default:
            return 0;
    }
}

int check_parent_for_reference(struct heuristic_node *node, char *var)
{
    while (node != NULL) {
        if (has_reference(node->property, var)) return 1;
        if (has_reference(node->before_property, var)) return 1;
        node = node->parent;
    }
    return 0;
}

int has_new_reference(struct heuristic_node *node, struct _ex_intern *e)
{
    int i;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor==INTERN_REFERENCE && e->u.appl.count==2 &&
                e->u.appl.args[1]->type==EXP_VAR && e->u.appl.args[0]->type==EXP_STRING) {
                if (!check_parent_for_reference(node, e->u.appl.args[0]->u.string)) return 1;
            }
            for (i = 0; i < e->u.appl.count; ++i) {
                if (has_new_reference(node, e->u.appl.args[i])) return 1;
            }
            return 0;

        case EXP_QUANT:
            if (has_new_reference(node, e->u.quant.exp)) return 1;
            return has_new_reference(node, e->u.quant.cond);

        default:
            return 0;
    }
}

static int repeat_time_induction(struct heuristic_node *node)
{
    struct _ex_intern *prop = node->property;
    struct heuristic_node *n;

    n = node;
    while (n && (n->heuristic==NULL || !strcmp(n->heuristic,"time_induction"))) n = n->parent;
    if (!n) return 1;

    n = node->parent;

    return has_new_reference(n, node->property);

#ifdef XX
    while (node != NULL) {
        //printf("Info: Checking %s ", _th_print_exp(node->property));
        //printf("Info: Against %s\n", _th_print_exp(prop));
        //if (node->parent) printf("Info: Heuristic: %s\n", node->parent->heuristic);
        if (node->parent && !strcmp(node->parent->heuristic,"time_induction") &&
            !has_new_reference(node->parent,node->property)) return 1;
        node = node->parent;
    }
    return 0;
#endif
}

static struct _ex_intern *find_state_rule(struct env *env, struct _ex_intern *exp)
{
    int i;
    struct _ex_intern *time, *nt;

    switch (exp->type) {
        case EXP_APPL:
            switch (exp->u.appl.functor) {
                case INTERN_REFERENCE:
                    if (exp->u.appl.count==2 && exp->u.appl.args[0]->type==EXP_STRING &&
                        _th_rewrite(env,_ex_intern_appl1_env(env,INTERN_STATE_VAR,exp->u.appl.args[0]))==_ex_true) {
                        return exp;
                    }
                    return NULL;

                default:
                    time = NULL;
                    for (i = 0; i < exp->u.appl.count; ++i) {
                        nt = find_state_rule(env, exp->u.appl.args[i]);
                        if (time==NULL ||
                            (nt != NULL && _th_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_LESS,nt->u.appl.args[1],time->u.appl.args[1])))) {
                            time = nt;
                        }
                    }
                    return time;
            }

        case EXP_QUANT:
            time = find_state_rule(env,exp->u.quant.exp);
            nt = find_state_rule(env,exp->u.quant.exp);
            if (time==NULL ||
                (nt != NULL &&
                 _th_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_LESS,nt->u.appl.args[1],time->u.appl.args[1])))) {
                return nt;
            } else {
                return time;
            }

        default:
            return 0;
    }
}

static int time_in_range(struct env *env, struct _ex_intern *exp, struct _ex_intern *time)
{
    int i;

    switch (exp->type) {
        case EXP_APPL:
            switch (exp->u.appl.functor) {
                case INTERN_REFERENCE:
                    if (exp->u.appl.count==2 && exp->u.appl.args[0]->type==EXP_STRING &&
                        _th_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_LESS,time,exp->u.appl.args[1]))==_ex_true) {
                        return 1;
                    }
                    return 0;

                default:
                    for (i = 0; i < exp->u.appl.count; ++i) {
                        if (time_in_range(env, exp->u.appl.args[i], time)) return 1;
                    }
                    return 0;
            }

        case EXP_QUANT:
            if (time_in_range(env,exp->u.quant.exp, time)) return 1;
            return time_in_range(env,exp->u.quant.cond, time);

        default:
            return 0;
    }
}

static struct _ex_intern *lt;
static int less_time(struct env *env, struct _ex_intern *exp)
{
    if (exp->type != EXP_APPL || exp->u.appl.functor != INTERN_REFERENCE  || exp->u.appl.count != 2) return 0;

    //_tree_print_exp("Testing", _ex_intern_appl2_env(env,INTERN_NAT_LESS,exp->u.appl.args[1],lt));
    //_tree_print_exp("Result", _th_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_LESS,exp->u.appl.args[1],lt)));
    if (_th_rewrite(env,exp->u.appl.args[1])==lt) return 1;

    return _th_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_LESS,exp->u.appl.args[1],lt))==_ex_true;
}

static int signal_weight(struct env *env, struct _ex_intern *rule)
{
    if (rule->type != EXP_APPL || rule->u.appl.count != 3 ||
        rule->u.appl.args[0]->type != EXP_APPL || rule->u.appl.args[0]->u.appl.count != 2 ||
        rule->u.appl.args[0]->u.appl.functor != INTERN_REFERENCE ||
        rule->u.appl.args[0]->u.appl.args[0]->type != EXP_STRING) return 1;

    if (_th_rewrite(env,_ex_intern_appl1_env(env,INTERN_STATE_VAR,
                    rule->u.appl.args[0]->u.appl.args[0]))==_ex_true) return 100;

    return 1;
}

static struct add_list *get_possible_values(struct env *env, struct add_list *values, struct _ex_intern *v, struct add_list *values_seen)
{
    int i;
    struct _ex_intern *context_rule_set;
    struct _ex_intern **args;
    struct match_return *mr;
    struct add_list vs, *vl;
    int count;

    _tree_print_exp("Getting values for", v);
    _tree_indent();
    context_rule_set = _th_get_context_rule_set(env);
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * context_rule_set->u.appl.count);
    count = 0;

    if (v->u.appl.args[1]->type != EXP_APPL ||
        v->u.appl.args[1]->u.appl.functor != INTERN_NEXT) {
        v = _ex_intern_appl2_env(env,v->u.appl.functor,v->u.appl.args[0],
                _ex_intern_appl3_env(env,INTERN_NEXT,v->u.appl.args[1],
                                     _ex_intern_string("CLK"),
                                     _ex_intern_small_integer(0)));
    }
    vs.next = values_seen;
    vs.e = v->u.appl.args[0];
    for (i = 0; i < context_rule_set->u.appl.count; ++i) {
        _tree_print_exp("Testing", context_rule_set->u.appl.args[i]);
        mr = _th_match(env,context_rule_set->u.appl.args[i]->u.appl.args[0], v);
        if (mr != NULL) {
            _tree_print0("Match");
            _tree_indent();
            _tree_print_exp("",_th_subst(env,mr->theta,context_rule_set->u.appl.args[i]->u.appl.args[2]));
            _tree_print_exp("",_th_rewrite(env,_th_subst(env,mr->theta,context_rule_set->u.appl.args[i]->u.appl.args[2])));
            _tree_undent();
        }
        if (mr != NULL && (_th_rewrite(env,_th_subst(env,mr->theta,
                           context_rule_set->u.appl.args[i]->u.appl.args[2])) != _ex_false)) {
            _tree_print0("accepting");
            args[count] = _th_rewrite(env,_th_subst(env,mr->theta,
                                          context_rule_set->u.appl.args[i]->u.appl.args[1]));
            _tree_print_exp("Value", args[count]);
            if (args[count]->type==EXP_APPL &&
                (args[count]->u.appl.functor != INTERN_REFERENCE ||
                 args[count]->u.appl.count != 2)) {
                _tree_undent();
                return NULL;
            }
            ++count;
        }
    }

    for (i = 0; i < count; ++i) {
        if (args[i]->type==EXP_INTEGER) {
            struct add_list *add = values;
            while (add != NULL) {
                if (add->e==args[i]) {
                    goto cont;
                }
                add = add->next;
            }
            add = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            add->next = values;
            values = add;
            add->e = args[i];
        } else {
            vl = &vs;
            while (vl != NULL) {
                if (vl->e== args[i]->u.appl.args[0]) goto cont;
                vl = vl->next;
            }
            values = get_possible_values(env, values, args[i], &vs);
            if (values==NULL) {
                _tree_undent();
                return NULL;
            }
        }
cont:;
    }
    _tree_undent();
    return values;
}

static void build_decendent_tree(struct env *env, struct heuristic_node *node, struct _ex_intern *v)
{
    struct add_list *values = get_possible_values(env,NULL,v,NULL);
    struct heuristic_node *child;

    if (values==NULL) return;

    node->heuristic = "state_split";

    //_tree_start = 0; _tree_end = 2000000;
    //_tree_sub = _tree_sub2 = -1;
    //_tree_mute = 0;

    while (values != NULL) {
        struct _ex_intern *assumption;
        assumption = _th_rewrite(env,_ex_intern_appl2_env(env, INTERN_EQUAL, v, values->e));
        if (assumption != _ex_false) {
            child = _th_new_node(node);
            child->property = _th_flatten(env,_ex_intern_appl2_env(env,INTERN_OR,_ex_intern_appl1_env(env,INTERN_NOT,assumption),node->property));
            //_tree_print_exp("term:", _ex_intern_appl2_env(env, INTERN_EQUAL, v, values->e));
            //child->assumption = assumption;
            child->assumption = assumption;
            //if (child->assumption==_ex_false) exit(1);
        }
        values = values->next;
    }

    //_tree_mute = 1;

    return;
}

static int has_var_assign(struct env *env, struct heuristic_node *node, struct _ex_intern *ref)
{
    while (node) {
        if (node->assumption->type==EXP_APPL &&
            node->assumption->u.appl.count==2 &&
            node->assumption->u.appl.functor==INTERN_EQUAL &&
            (node->assumption->u.appl.args[0]==ref || node->assumption->u.appl.args[1]==ref)) {
            return 1;
        }
        if (node->assumption->type==EXP_APPL &&
            node->assumption->u.appl.functor==INTERN_ORIENTED_RULE &&
            node->assumption->u.appl.count==3 &&
            (node->assumption->u.appl.args[0]==ref || node->assumption->u.appl.args[1]==ref)) {
            return 1;
        }
        node = node->parent;
    }
    return 0;
}

static int all_references_smaller(struct module_list *module, struct env *env, struct _ex_intern *e, char *var, struct _ex_intern *time)
{
    int i;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor==INTERN_REFERENCE && e->u.appl.count==2 &&
                e->u.appl.args[0]->type==EXP_STRING) {
                struct _ex_intern *r = _ex_intern_appl2_env(env,INTERN_NAT_LESS,e->u.appl.args[1], time);
                if (_th_rewrite(env, r)==_ex_true) return 1;
                r = _ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[1], time);
                if (_th_rewrite(env, r)!=_ex_true) return 0;
                return smaller_var(module,e->u.appl.args[0]->u.string,var);
            }
            for (i = 0; i < e->u.appl.count; ++i) {
                if (!all_references_smaller(module, env, e->u.appl.args[i], var, time)) return 0;
            }
            return 1;

        case EXP_QUANT:
            if (!all_references_smaller(module, env, e->u.quant.exp, var, time)) return 0;
            return all_references_smaller(module, env, e->u.quant.cond, var, time);

        default:
            return 1;
    }
}

#define OFFSET 1

int all_times_equal_smaller(struct env *env, struct _ex_intern *e, struct _ex_intern *time)
{
    int i;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor==INTERN_REFERENCE && e->u.appl.count==2 &&
                e->u.appl.args[0]->type==EXP_STRING) {
                struct _ex_intern *r;
                if (e->u.appl.args[1]==time) return 1;
                r = _ex_intern_appl2_env(env,INTERN_NAT_LESS,
                        _ex_intern_appl3_env(env,INTERN_NEXT,
                            e->u.appl.args[1],
                            _ex_intern_string("CLK"),
                            _ex_intern_small_integer(OFFSET)),
                        time);
                return _th_rewrite(env, r)==_ex_true;
            }
            for (i = 0; i < e->u.appl.count; ++i) {
                if (!all_times_equal_smaller(env, e->u.appl.args[i], time)) return 0;
            }
            return 1;

        //case EXP_QUANT:
        //    if (!all_times_equal_smaller(env, e->u.quant.exp, time)) return 0;
        //    return all_times_equal_smaller(env, e->u.quant.cond, time);

        default:
            return 1;
    }
}

static void state_var_case(struct env *env, struct heuristic_node *node, struct module_list *ml)
{
    char *mark1, *mark2, *mark3;
    struct _ex_intern *e, *v, *vr;
    struct var_list *vl;
    int time = 0;
    struct heuristic_node *p = node->parent;

    //while (p && (!p->heuristic || (strcmp(p->heuristic, "state_split") && strcmp(p->heuristic, "state_cases")))) {
    //    p = p->parent;
    //}
    //if (p && p->before_property==p->property) return;

    //printf("Entering generate universal\n");
    //fflush(stdout);

    mark1 = _th_alloc_mark(MATCH_SPACE);
    mark2 = _th_alloc_mark(ENVIRONMENT_SPACE);
    mark3 = _th_alloc_mark(REWRITE_SPACE);
    _ex_push();

    while (1) {
        e = _ex_intern_var(INTERN_CURRENT);
        if (time > 0) {
            e = _ex_intern_appl3_env(env, INTERN_NEXT, e,
                    _ex_intern_string("CLK"), _ex_intern_small_integer(time));
        }
        if (all_times_equal_smaller(env,node->property,e)) break;
        vl = ml->state_var_list;
        while (vl != NULL) {
            v = _ex_intern_appl2_env(env,INTERN_REFERENCE,
                    _ex_intern_string(_th_intern_decode(vl->var)),e);
            vr = _th_rewrite(env,v);
            if (!has_var_assign(env,node,vr)) {

                build_decendent_tree(env, node, vr);
                _th_alloc_release(MATCH_SPACE,mark1);
                _th_alloc_release(ENVIRONMENT_SPACE,mark2);
                _th_alloc_release(REWRITE_SPACE,mark3);
                node = node->first_child;
                _ex_pop();
                while (node) {
                    node->assumption = _ex_reintern(env,node->assumption);
                    node->property = _ex_reintern(env,node->property);
                    node = node->next;
                }
                _th_reintern_cache(env);
                _ex_release();
                return;
            }
            vl = vl->next;
        }
        ++time;
    }

    _th_alloc_release(MATCH_SPACE,mark1);
    _th_alloc_release(ENVIRONMENT_SPACE,mark2);
    _th_alloc_release(REWRITE_SPACE,mark3);
    _ex_pop();
    _th_reintern_cache(env);
    _ex_release();
}

int has_assign(struct _ex_intern *exp, struct _ex_intern *term, struct _ex_intern *value)
{
    if (exp->type==EXP_APPL && exp->u.appl.functor==INTERN_OR) {
        int i;
        for (i = 0; i < exp->u.appl.count; ++i) {
            if (exp->u.appl.args[i]->type==EXP_APPL &&
                exp->u.appl.args[i]->u.appl.functor==INTERN_NOT &&
                exp->u.appl.args[i]->u.appl.count==1) {
                struct _ex_intern *t = exp->u.appl.args[i]->u.appl.args[0];
                if (t->type==EXP_APPL &&
                    (t->u.appl.functor==INTERN_EQUAL ||
                     t->u.appl.functor==INTERN_ORIENTED_RULE)) {
                    if (t->u.appl.args[0]==term) {
                        if (t->u.appl.args[1]==value) {
                            return 1;
                        } else {
                            return -1;
                        }
                    }
                    if (t->u.appl.args[1]==term) {
                        if (t->u.appl.args[0]==value) {
                            return 1;
                        } else {
                            return -1;
                        }
                    }
                }
            }
        }
    }
    return 0;
}

#define UNTRACABLE_VALUE ((struct add_list *)1)

static struct add_list *get_state_conditions(struct env *env, struct add_list *values, struct _ex_intern *term, struct _ex_intern *value, struct _ex_intern *cond, struct _ex_intern *exp)
{
    int i;
    struct _ex_intern *context_rule_set;
    struct _ex_intern **args, **conds, *c;
    struct match_return *mr;
    int count;

    _tree_print_exp("Getting state conditions", term);
    _tree_indent();
    _tree_print_exp("term", term);
    _tree_print_exp("value", value);
    _tree_print_exp("exp", exp);
    _tree_print_exp("cond", cond);
    i = has_assign(exp,term,value);
    if (i) {
        //if (cond==_ex_true) {
        //    _tree_undent();
        //    return UNTRACABLE_VALUE;
        //}
        if (i > 0) {
            struct add_list *add;
            add = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            add->next = values;
            values = add;
            add->e = cond;
            _tree_print0("Value specified in expression");
        } else {
            _tree_print0("Eliminated");
        }
        _tree_undent();
        return values;
    }
    if (term->type != EXP_INTEGER &&
        (term->type != EXP_APPL ||
         term->u.appl.functor != INTERN_REFERENCE ||
         term->u.appl.count !=2 ||
         term->u.appl.args[0]->type != EXP_STRING ||
         term->u.appl.args[1]->type != EXP_APPL ||
         term->u.appl.args[1]->u.appl.functor != INTERN_NEXT)) {
        _tree_undent();
        return UNTRACABLE_VALUE;
    }
    context_rule_set = _th_get_context_rule_set(env);
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * context_rule_set->u.appl.count);
    conds = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * context_rule_set->u.appl.count);
    count = 0;

    for (i = 0; i < context_rule_set->u.appl.count; ++i) {
        _tree_print_exp("Testing", context_rule_set->u.appl.args[i]);
        mr = _th_match(env,context_rule_set->u.appl.args[i]->u.appl.args[0], term);
        if (mr != NULL) {
            _tree_print0("Match");
            _tree_indent();
            _tree_print_exp("",_th_subst(env,mr->theta,context_rule_set->u.appl.args[i]->u.appl.args[2]));
            _tree_print_exp("",_th_rewrite(env,_th_subst(env,mr->theta,context_rule_set->u.appl.args[i]->u.appl.args[2])));
            _tree_undent();
        }
        if (mr != NULL && ((c = _th_rewrite(env,_th_subst(env,mr->theta,
                            context_rule_set->u.appl.args[i]->u.appl.args[2]))) != _ex_false) &&
                            (context_rule_set->u.appl.args[i]->u.appl.args[1]->type != EXP_INTEGER ||
                             context_rule_set->u.appl.args[i]->u.appl.args[1]==value)) {
            _tree_print0("accepting");
            args[count] = _th_rewrite(env,_th_subst(env,mr->theta,
                                          context_rule_set->u.appl.args[i]->u.appl.args[1]));
            conds[count] = c;
            _tree_print_exp("Value", args[count]);
            _tree_print_exp("Cond", conds[count]);
            if (args[count]->type==EXP_APPL &&
                (args[count]->u.appl.functor != INTERN_REFERENCE ||
                 args[count]->u.appl.count != 2)) {
                _tree_undent();
                return NULL;
            }
            ++count;
        }
    }

    for (i = 0; i < count; ++i) {
        if (conds[i]->type==EXP_APPL && conds[i]->u.appl.functor==INTERN_NC_AND) {
            conds[i] = _ex_intern_appl_env(env,INTERN_AND,
                conds[i]->u.appl.count,conds[i]->u.appl.args);
        }
        if (args[i]->type==EXP_INTEGER) {
            struct add_list *add;
            add = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            add->next = values;
            values = add;
            add->e = _th_flatten(env,_ex_intern_appl2_env(env,INTERN_AND,conds[i],cond));
        } else {
            values = get_state_conditions(env, values, args[i], value,
                _th_flatten(env,_ex_intern_appl2_env(env,INTERN_AND,conds[i],cond)), exp);
            if (values==NULL || values==UNTRACABLE_VALUE) {
                _tree_undent();
                return values;
            }
        }
    }
    _tree_undent();
    return values;
}

static void build_state_tree(struct env *env, struct heuristic_node *node, struct _ex_intern *v, struct _ex_intern *value)
{
    struct add_list *values = get_state_conditions(env,NULL,v,value,_ex_true,node->parent->property);
    struct heuristic_node *child, *prev_child;

    _tree_print1("values = %d", values);
    if (values==UNTRACABLE_VALUE) return;

    node->heuristic = "state_cases";
    prev_child = NULL;

    //_tree_start = 0; _tree_end = 2000000;
    //_tree_sub = _tree_sub2 = -1;
    //_tree_mute = 0;

    while (values != NULL) {
        struct _ex_intern *assumption;
        assumption = _th_rewrite(env,values->e);
        if (assumption != _ex_false) {
            child = _th_new_node(node);
            child->property = _th_flatten(env,_ex_intern_appl2_env(env,INTERN_OR,_ex_intern_appl1_env(env,INTERN_NOT,assumption),node->property));
            //_tree_print_exp("term:", _ex_intern_appl2_env(env, INTERN_EQUAL, v, values->e));
            //child->assumption = assumption;
            child->assumption = assumption;
            //if (child->assumption==_ex_false) exit(1);
            prev_child = child;
        }
        values = values->next;
    }

    //_tree_mute = 1;

    if (!prev_child) {
        child = _th_new_node(node);
        child->property = _ex_true;
        child->assumption = _ex_true;
    }

    return;
}

static void state_condition_case(struct env *env, struct heuristic_node *node)
{
    char *mark1, *mark2, *mark3;
    struct _ex_intern *v, *vr;
    int have_var = 0;
    //printf("Entering generate universal\n");
    //fflush(stdout);

    if (node->parent==NULL || strcmp(node->parent->heuristic,"state_split")) return;
    mark1 = _th_alloc_mark(MATCH_SPACE);
    mark2 = _th_alloc_mark(ENVIRONMENT_SPACE);
    mark3 = _th_alloc_mark(REWRITE_SPACE);
    _ex_push();

    if (node->assumption->u.appl.args[0]->type==EXP_INTEGER) {
        vr = node->assumption->u.appl.args[0];
        v = node->assumption->u.appl.args[1];
    } else {
        vr = node->assumption->u.appl.args[1];
        v = node->assumption->u.appl.args[0];
    }

    _tree_print_exp("State condition case", v);
    _tree_print_exp("State condition case", vr);

    build_state_tree(env, node, v, vr);

    _th_alloc_release(MATCH_SPACE,mark1);
    _th_alloc_release(ENVIRONMENT_SPACE,mark2);
    _th_alloc_release(REWRITE_SPACE,mark3);
    _ex_pop();
    _th_reintern_cache(env);
    node = node->first_child;
    while (node) {
        node->assumption = _ex_reintern(env,node->assumption);
        node->property = _ex_reintern(env,node->property);
        node = node->next;
    }
    _ex_release();
}

int no_negatives(struct _ex_intern *e)
{
    int i;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor==INTERN_REFERENCE && e->u.appl.count==2 &&
                e->u.appl.args[0]->type==EXP_STRING) {
                if (e->u.appl.args[1]->type==EXP_APPL &&
                    e->u.appl.args[1]->u.appl.functor==INTERN_NEXT) {
                    struct _ex_intern *f = e->u.appl.args[1]->u.appl.args[2];
                    return f->u.integer[0]==1 && (!(f->u.integer[1]&0x80000000));
                }
            }
            for (i = 0; i < e->u.appl.count; ++i) {
                if (!no_negatives(e->u.appl.args[i])) return 0;
            }
            return 1;

        case EXP_QUANT:
            if (!no_negatives(e->u.quant.exp)) return 0;
            return no_negatives(e->u.quant.cond);

        default:
            return 1;
    }
}

static int is_constant(struct _ex_intern *e)
{
    return e->type==EXP_INTEGER || e->type==EXP_STRING;
}

int largest_time(struct _ex_intern *e)
{
    int i;
    int time, max_time = 0;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor==INTERN_REFERENCE && e->u.appl.count==2 &&
                e->u.appl.args[0]->type==EXP_STRING &&
                e->u.appl.args[1]->type==EXP_APPL &&
                e->u.appl.args[1]->u.appl.functor==INTERN_NEXT) {
                struct _ex_intern *f = e->u.appl.args[1];
                if (f->u.appl.args[0]->type==EXP_VAR &&
                    f->u.appl.args[0]->u.var==INTERN_CURRENT &&
                    f->u.appl.args[1]->type==EXP_STRING &&
                    !strcmp(f->u.appl.args[1]->u.string,"CLK") &&
                    f->u.appl.args[2]->type==EXP_INTEGER) {
                    return f->u.appl.args[2]->u.integer[1];
                }
            }
            for (i = 0; i < e->u.appl.count; ++i) {
                time = largest_time(e->u.appl.args[i]);
                if (time > max_time) max_time = time;
            }
            return max_time;

        case EXP_QUANT:
            max_time = largest_time(e->u.quant.exp);
            time = largest_time(e->u.quant.cond);
            if (time > max_time) {
                return time;
            } else {
                return max_time;
            }

        default:
            return 0;
    }
}

static int exp_has_variable(struct module_list *module, char *var, struct _ex_intern *exp)
{
    int i;
    struct effects_list *effects;

    switch (exp->type) {
        case EXP_APPL:
            if (exp->u.appl.functor==INTERN_REFERENCE) {
                if (exp->u.appl.args[0]->type==EXP_STRING &&
                    !strcmp(var,exp->u.appl.args[0]->u.string)) return 1;
                effects = find_effects_list(module, exp->u.appl.args[0]->u.string);
                while (effects != NULL) {
                    if (!strcmp(effects->variable,var)) return 1;
                    effects = effects->next;
                }
            }
            for (i = 0; i < exp->u.appl.count; ++i) {
                if (exp_has_variable(module, var, exp->u.appl.args[i])) {
                    return 1;
                }
            }
            return 0;

        case EXP_QUANT:
            if (exp_has_variable(module,var,exp->u.quant.exp)) {
                return 1;
            }
            return exp_has_variable(module,var,exp->u.quant.cond);

        default:
            return 0;
    }
}

static int no_negative_next(struct _ex_intern *exp)
{
    int i;

    switch (exp->type) {
        case EXP_APPL:
            if (exp->u.appl.functor==INTERN_NEXT) {
                if (exp->u.appl.args[2]->type!=EXP_VAR) return 0;
            }
            for (i = 0; i < exp->u.appl.count; ++i) {
                if (!no_negative_next(exp->u.appl.args[i])) {
                    return 0;
                }
            }
            return 1;

        case EXP_QUANT:
            if (!no_negative_next(exp->u.quant.exp)) {
                return 0;
            }
            return no_negative_next(exp->u.quant.cond);

        default:
            return 1;
    }
}

static struct _ex_intern *build_rule(struct module_list *module, struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *f;

    if (e->type!=EXP_APPL || e->u.appl.count!=1 ||
        e->u.appl.functor!=INTERN_NOT) {
        return NULL;
    }
    e = e->u.appl.args[0];
    if (e->type != EXP_APPL || e->u.appl.count != 2 || e->u.appl.functor != INTERN_EQUAL) {
        return NULL;
    }
    if (e->u.appl.args[0]->type==EXP_APPL &&
        e->u.appl.args[0]->u.appl.functor==INTERN_REFERENCE &&
        all_references_smaller(module,env,e->u.appl.args[1],e->u.appl.args[0]->u.appl.args[0]->u.string,e->u.appl.args[0]->u.appl.args[1])) {
        f = e->u.appl.args[1];
        e = e->u.appl.args[0];
    } else if (e->u.appl.args[1]->type==EXP_APPL &&
        e->u.appl.args[1]->u.appl.functor==INTERN_REFERENCE &&
        all_references_smaller(module,env,e->u.appl.args[0],e->u.appl.args[1]->u.appl.args[0]->u.string,e->u.appl.args[1]->u.appl.args[1])) {
        f = e->u.appl.args[0];
        e = e->u.appl.args[1];
    } else {
        return NULL;
    }
    return _th_mark_vars(env,_ex_intern_appl3_env(env,INTERN_FORCE_ORIENTED,e,f,_ex_true));
}

static struct _ex_intern *add_constant_assigns(struct env *env, struct heuristic_node *node, struct _ex_intern *property, struct module_list *module)
{
    int i;
    struct _ex_intern *context_rule_set, *prop;
    struct _ex_intern **args, *terms;
    //struct match_return *mr;
    //struct heuristic_node *n;
    int count, t;
    struct _ex_unifier *u;
    struct _ex_intern *assigns;
    //int start, end, sub, sub2, mute;

    _tree_print_exp("Testing constant assigns for", property);
    _tree_indent();

    //parent = node->parent;
    //n = node;

    //while (parent && !strcmp(parent->heuristic, "move_earlier_cycle")) parent = parent->parent;

    //if (parent && !strcmp(parent->heuristic, "add_constant_assigns")) {
    //    _tree_print0("root failure");
    //    _tree_undent();
    //    return;
    //}

    //parent = node->parent;
    //while (parent && strcmp(parent->heuristic,"state_split")) {
    //    n = parent;
    //    parent = parent->parent;
    //}
    //if (parent==NULL) {
    //    _tree_print0("parent failure");
    //    _tree_undent();
    //    return;
    //}

    if (module->assign_exp==NULL) {
        context_rule_set = _th_get_context_rule_set(env);
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * context_rule_set->u.appl.count);
        count = 0;
        for (i = 0; i < context_rule_set->u.appl.count; ++i) {
            struct _ex_intern *r = context_rule_set->u.appl.args[i];
            if (r->u.appl.args[0]->type==EXP_APPL && r->u.appl.args[0]->u.appl.functor==INTERN_REFERENCE) {
                args[count++] = r;
            }
        }
        module->assign_exp = _ex_intern_appl_env(env,INTERN_TUPLE,count,args);
    } else {
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * module->assign_exp->u.appl.count);
    }


    _th_log_derive_push(env);
    _tree_print0("context");
    _tree_indent();
    //_th_build_context(env,node->property);
    for (i = 0; i < property->u.appl.count; ++i) {
        struct _ex_intern *e = build_rule(module,env,property->u.appl.args[i]);
        if (!e) {
            e = property->u.appl.args[i];
            if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                e = e->u.appl.args[0];
            } else {
                e = _ex_intern_appl1_env(env,INTERN_NOT,e);
            }
            e = _th_mark_vars(env,e);
        }
        _tree_print_exp("", e);
        //start = _tree_start;
        //end = _tree_end;
        //sub = _tree_sub;
        //sub2 = _tree_sub2;
        //mute = _tree_mute;
        //_tree_start = 0;
        //_tree_end = 1000000;
        //_tree_sub = -1;
        //_tree_sub2 = 1000000;
        //_tree_mute = 0;
        _th_log_derive_and_add(env,_th_derive_simplify(env,e));
        //_tree_start = start;
        //_tree_end = end;
        //_tree_sub = sub;
        //_tree_sub2 = sub2;
        //_tree_mute = mute;
    }
    _tree_undent();

    terms = NULL;
        
    for (t = node->time_step; t < node->time_step+2; ++t) {
        prop = module->assign_exp;
        count = 0;
        for (i = 0; i < prop->u.appl.count; ++i) {
            //if (is_constant(prop->u.appl.args[i]->u.appl.args[1]) &&
            //    exp_has_variable(module,prop->u.appl.args[i]->u.appl.args[0]->u.appl.args[0]->u.string,property)) {
            if (exp_has_variable(module,prop->u.appl.args[i]->u.appl.args[0]->u.appl.args[0]->u.string,property) &&
                (t > 0 || no_negative_next(prop->u.appl.args[i]))) {
                args[count++] = prop->u.appl.args[i];
            }
        }
        prop = _ex_intern_appl_env(env,INTERN_TUPLE,count,args);
        
        //tmax = largest_time(node->property);
        //_tree_print1("tmax = %d", tmax);
        //for (t = 0; t < tmax; ++t) {
        u = _th_new_unifier(MATCH_SPACE);
        u = _th_add_pair(MATCH_SPACE,u,INTERN_NEXT,_ex_intern_small_integer(t));
        assigns = _th_subst(env,u,prop);
        //_th_test_mode = 1;
        _th_do_and_or_context_rewrites = 0;
        assigns = _th_rewrite(env,assigns);
        _th_do_and_or_context_rewrites = 1;
        //_th_test_mode = 0;
        _tree_print1("Cycle %d", t);
        _tree_indent();
        for (i = 0; i < assigns->u.appl.count; ++i) {
            struct _ex_intern *r = assigns->u.appl.args[i];
            if (r==_ex_false) {
                _tree_print0("Degenerate rule");
                //n = _th_new_node(node);
                //node->heuristic = "add_constant_assigns";
                //n->property = _ex_true;
                //n->assumption = _ex_true;
                _th_log_derive_pop(env);
                _tree_undent();
                _tree_undent();
                return _ex_true;
            }
            //_tree_print_exp("Testing assign", r);
            //printf("r = %s\n", _th_print_exp(r));
            //fflush(stdout);
            if (r->type==EXP_APPL && r->u.appl.count>1) {
                //_tree_print0("good");
                if (r->u.appl.count==3 && r->u.appl.args[2]==_ex_true) {
                    _tree_print_exp("Adding", r);
                    if (r->u.appl.functor==INTERN_ORIENTED_RULE) {
                        if (terms==NULL) {
                            terms = _ex_intern_appl1_env(env,INTERN_NOT,r);
                        } else {
                            terms = _th_flatten(env,
                                _ex_intern_appl2_env(env,INTERN_OR,
                                terms,
                                _ex_intern_appl1_env(env,INTERN_NOT,r)));
                        }
                    } else {
                        if (terms==NULL) {
                            terms = _ex_intern_appl1_env(env,INTERN_NOT,
                                _ex_intern_appl2_env(env,INTERN_EQUAL,r->u.appl.args[1],r->u.appl.args[0]));
                        } else {
                            terms = _th_flatten(env,
                                _ex_intern_appl2_env(env,INTERN_OR,
                                terms,
                                _ex_intern_appl1_env(env,INTERN_NOT,
                                _ex_intern_appl2_env(env,INTERN_EQUAL,r->u.appl.args[1],r->u.appl.args[0]))));
                        }
                    }
                } else if (r->type==EXP_APPL && r->u.appl.count==2 && r->u.appl.functor==INTERN_EQUAL) {
                    _tree_print_exp("Adding", r);
                    if (terms==NULL) {
                        terms = _ex_intern_appl1_env(env,INTERN_NOT,
                            _ex_intern_appl2_env(env,INTERN_EQUAL,r->u.appl.args[1],r->u.appl.args[0]));
                    } else {
                        terms = _th_flatten(env,
                            _ex_intern_appl2_env(env,INTERN_OR,
                            terms,
                            _ex_intern_appl1_env(env,INTERN_NOT,
                            _ex_intern_appl2_env(env,INTERN_EQUAL,r->u.appl.args[1],r->u.appl.args[0]))));
                    }
                }
            }
        }
        _tree_undent();
    }
    _th_log_derive_pop(env);

    if (terms==NULL) {
        _tree_print0("term failure");
        _tree_undent();
        return NULL;
    }

    //n = _th_new_node(node);
    //node->heuristic = "add_constant_assigns";
    //n->property = _th_flatten(env,_ex_intern_appl2_env(env,INTERN_OR,terms,node->property));
    //n->assumption = terms;

    _tree_undent();

    return _th_flatten(env,_ex_intern_appl2_env(env,INTERN_OR,terms,property));
}

struct _ex_intern *apply_assigns(struct env *env, struct _ex_intern *exp,
                                 struct _ex_intern *assigns, struct _ex_intern *assigns_base)
{
    struct _ex_intern **args, *e, *c;
    int i, j;

    switch (exp->type) {
        case EXP_APPL:
            if (exp->u.appl.functor==INTERN_REFERENCE && exp->u.appl.count==2) {
                //_tree_print_exp("Testing term", exp);
                for (j = 0; j < assigns->u.appl.count; ++j) {
                    struct _ex_intern *assign = assigns->u.appl.args[j];
                    struct _ex_intern *lhs, *rhs;
                    struct _ex_intern *bassign = assigns_base->u.appl.args[j];
                    char *s = bassign->u.appl.args[0]->u.appl.args[0]->u.string;
                    struct match_return *mr;
#ifdef XX
                    int rev = 0;
                    if (assign->u.appl.args[0]->type != EXP_APPL ||
                        assign->u.appl.args[0]->u.appl.functor != INTERN_REFERENCE ||
                        strcmp(assign->u.appl.args[0]->u.appl.args[0]->u.string,s)) {
                        rev = 1;
                    } else if (assign->u.appl.args[1]->type==EXP_APPL &&
                        assign->u.appl.args[1]->u.appl.functor==INTERN_REFERENCE &&
                        largest_time(assign->u.appl.args[1]) >
                        largest_time(assign->u.appl.args[0])) {
                        rev = 1;
                    }
                    if (rev) {
                        lhs = assign->u.appl.args[1];
                        rhs = assign->u.appl.args[0];
                    } else {
                        lhs = assign->u.appl.args[0];
                        rhs = assign->u.appl.args[1];
                    }
#endif
                    lhs = assign->u.appl.args[0];
                    rhs = assign->u.appl.args[1];
                    mr = _th_match(env, lhs, exp);
                    if (mr) {
                        _tree_print_exp("Testing", assign);
                        _tree_indent();
                        _tree_print_exp("on", exp);
                        _tree_print_exp("cond", _th_rewrite(env,_th_subst(env,mr->theta,assign->u.appl.args[2])));
                        _tree_undent();
                    }
                    if (mr != NULL &&
                        _th_rewrite(env,_th_subst(env,mr->theta,assign->u.appl.args[2]))==_ex_true) {
                        struct _ex_intern *res = apply_assigns(env,_th_subst(env, mr->theta, rhs), assigns, assigns_base);
                        _tree_print_exp("Applying", assign);
                        _tree_indent();
                        _tree_print_exp("to", exp);
                        _tree_print_exp("get", res);
                        _tree_undent();
                        return res;
                    }
                }
            }
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count);
            for (i = 0; i < exp->u.appl.count; ++i) {
                args[i] = apply_assigns(env, exp->u.appl.args[i], assigns, assigns_base);
            }
            return _ex_intern_appl_env(env,exp->u.appl.functor,exp->u.appl.count,args);

        case EXP_QUANT:
            e = apply_assigns(env,exp->u.quant.exp,assigns,assigns_base);
            c = apply_assigns(env,exp->u.quant.cond,assigns,assigns_base);
            return _ex_intern_quant(exp->u.quant.quant,exp->u.quant.var_count,exp->u.quant.vars,e,c);

        default:
            return exp;
    }
}

static void move_to_earlier_step(struct env *env, struct heuristic_node *node, struct module_list *module)
{
    int i;
    struct _ex_intern *context_rule_set, *prop;
    struct _ex_intern **args, *exp;
    //struct match_return *mr;
    struct heuristic_node *n;
    int count;

    _tree_print_exp("Testing move_to_earlier_step for", prop);
    _tree_indent();

    //parent = node->parent;
    //n = node;

    //while (parent && !strcmp(parent->heuristic, "move_earlier_cycle")) parent = parent->parent;

    //if (parent && !strcmp(parent->heuristic, "add_constant_assigns")) {
    //    _tree_print0("root failure");
    //    _tree_undent();
    //    return;
    //}

    //parent = node->parent;
    //while (parent && strcmp(parent->heuristic,"state_split")) {
    //    n = parent;
    //    parent = parent->parent;
    //}
    //if (parent==NULL) {
    //    _tree_print0("parent failure");
    //    _tree_undent();
    //    return;
    //}

    if (module->assign_exp==NULL) {
        context_rule_set = _th_get_context_rule_set(env);
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * context_rule_set->u.appl.count * 2);
        count = 0;
        for (i = 0; i < context_rule_set->u.appl.count; ++i) {
            struct _ex_intern *r = context_rule_set->u.appl.args[i];
            if (r->u.appl.args[0]->type==EXP_APPL && r->u.appl.args[0]->u.appl.functor==INTERN_REFERENCE) {
                args[count++] = r;
            }
        }
        module->assign_exp = _ex_intern_appl_env(env,INTERN_TUPLE,count,args);
    } else {
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * module->assign_exp->u.appl.count * 2);
    }

    _th_log_derive_push(env);
    _th_build_context(env,node->property);

    prop = module->assign_exp;
    count = 0;
    for (i = 0; i < prop->u.appl.count; ++i) {
        if (exp_has_variable(module,prop->u.appl.args[i]->u.appl.args[0]->u.appl.args[0]->u.string,node->property)) {
            struct _ex_intern *p = prop->u.appl.args[i];
            _tree_print_exp("Prop rule", p);
            if (p->u.appl.args[0]->type != EXP_APPL ||
                p->u.appl.args[0]->u.appl.functor != INTERN_REFERENCE ||
                p->u.appl.args[0]->u.appl.args[1]->type != EXP_APPL ||
                p->u.appl.args[0]->u.appl.args[1]->u.appl.functor != INTERN_NEXT ||
                p->u.appl.args[0]->u.appl.args[1]->u.appl.args[2]->type != EXP_VAR) {
                args[count++] = _th_mark_var(env,
                                    _ex_intern_appl3_env(env,INTERN_UNORIENTED_RULE,
                                        p->u.appl.args[1],
                                        p->u.appl.args[0],
                                        p->u.appl.args[2]),
                                    INTERN_CURRENT);
            } else {
                args[count++] = _th_mark_var(env,p,INTERN_CURRENT);
            }
            if (no_negative_next(p)) {
                struct _ex_unifier *u;
                u = _th_new_unifier(MATCH_SPACE);
                u = _th_add_pair(MATCH_SPACE,u,INTERN_NEXT,_ex_intern_small_integer(0));
                p = _th_subst(env,u,p);
                p = _ex_intern_appl3_env(env,
                    p->u.appl.functor,
                    _th_rewrite(env,p->u.appl.args[0]),
                    _th_rewrite(env,p->u.appl.args[1]),
                    _th_rewrite(env,p->u.appl.args[2]));
                _tree_print_exp("Zero prop", p);
                args[count++] = _th_mark_var(env,p,INTERN_CURRENT);
            }
        }
    }
    prop = _ex_intern_appl_env(env,INTERN_TUPLE,count,args);

    //tmax = largest_time(node->property);
    //_tree_print1("tmax = %d", tmax);
    exp = node->property;
    //for (t = 0; t < tmax; ++t) {
        //struct _ex_unifier *u;
        //struct _ex_intern *assigns;
        //u = _th_new_unifier(MATCH_SPACE);
        //u = _th_add_pair(MATCH_SPACE,u,INTERN_NEXT,_ex_intern_small_integer(t));
        //assigns = _th_subst(env,u,prop);
        //assigns = _th_rewrite(env,assigns);
        exp = apply_assigns(env, exp, prop, prop);
    //}

    _th_log_derive_pop(env);

    if (exp==node->property) {
        _tree_print0("term failure");
        _tree_undent();
        return;
    }

    n = _th_new_node(node);
    node->heuristic = "add_constant_assigns";
    n->property = exp;
    n->assumption = _ex_true;

    _tree_undent();
}

static struct _ex_intern *move_to_earlier_cycle(struct env *env, struct heuristic_node *node, struct _ex_intern *prop, struct module_list *module)
{
    int i, j;
    struct _ex_intern **args, **rules, *e;
    struct heuristic_node *parent, *n;
    int change, local_change;

    _tree_print_exp("Testing for move to earlier cycle", prop);
    _tree_indent();

    parent = node->parent;
    n = node;

    if (parent && !strcmp(parent->heuristic, "move_earlier_cycle")) {
        _tree_print0("root failure");
        _tree_undent();
        return NULL;
    }

    if (prop->type != EXP_APPL || prop->u.appl.functor != INTERN_OR) {
        _tree_print0("property format failure");
        _tree_undent();
        return NULL;
    }

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * prop->u.appl.count);
    rules = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * prop->u.appl.count);
    for (i = 0; i < prop->u.appl.count; ++i) {
        args[i] = prop->u.appl.args[i];
        rules[i] = NULL;
    }

    //_tree_print2("change, count = %d %df", change, node->property->u.appl.count);
    _th_log_derive_push(env);
    for (i = 0; i < prop->u.appl.count; ++i) {
        rules[i] = build_rule(module,env,args[i]);
        if (rules[i]) _th_log_derive_and_add(env,_th_derive_simplify(env,rules[i]));
    }

    change = 0;
    for (i = 0; i < prop->u.appl.count; ++i) {
        if (!rules[i]) {
            e = _th_rewrite(env, args[i]);
            if (e != args[i]) {
                change = 1;
                //_tree_print_exp("Change", e);
                args[i] = e;
            }
        }
    }
    _th_log_derive_pop(env);

    local_change = 1;
    while (local_change) {
        local_change = 0;
        for (i = 0; i < prop->u.appl.count; ++i) {
            if (rules[i]) {
                _th_log_derive_push(env);
                for (j = 0; j < prop->u.appl.count; ++j) {
                    if (rules[j] && i != j) {
                        _th_log_derive_and_add(env,_th_derive_simplify(env,rules[j]));
                    }
                }
                e = _th_rewrite(env,args[i]);
                if (e != args[i]) {
                    change = 1;
                    local_change = 1;
                    args[i] = e;
                    rules[i] = build_rule(module,env,e);
                }
                _th_log_derive_pop(env);
            }
        }
    }

    if (!change) {
        _tree_print0("no simplifications");
        _tree_undent();
        return NULL;
    }

    //n = _th_new_node(node);
    //node->heuristic = "move_earlier_cycle";
    //n->property = _th_flatten(env,_ex_intern_appl_env(env,INTERN_OR,node->property->u.appl.count,args));
    //n->assumption = _ex_true;

    _tree_undent();

    return _th_flatten(env,_ex_intern_appl_env(env,INTERN_OR,prop->u.appl.count,args));
}

static struct _ex_intern *get_limit(struct env *env, struct heuristic_node *node)
{
    while (node->parent != NULL && strcmp(node->parent->heuristic, "state_split")) {
        node = node->parent;
    }
    if (node->parent) {
        if (node->assumption->u.appl.args[0]->type==EXP_INTEGER) {
            return _th_unmark_vars(env,node->assumption->u.appl.args[1]->u.appl.args[1]);
        } else {
            return _th_unmark_vars(env,node->assumption->u.appl.args[0]->u.appl.args[1]);
        }
    } else {
        return _ex_intern_var(INTERN_CURRENT);
    }
}

static struct _ex_intern *state_universal(struct env *env, struct heuristic_node *node)
{
    //struct _ex_intern *signal = find_state_rule(env, exp);
    //struct _ex_intern *time, *result;

    //if (signal==NULL) return NULL;

    _tree_print0("Testing state universal");
    //_tree_indent();
    lt = get_limit(env, node);
    _tree_print_exp("limit", lt);
    return _th_generate_universal(env,node->property,less_time,NULL);
}

#ifdef XX
static struct _ex_intern *state_universal(struct env *env, struct _ex_intern *exp)
{
    struct _ex_intern *signal = find_state_rule(env, exp);
    struct _ex_intern *time, *result;

    if (signal==NULL) return NULL;

    _tree_print0("Testing state universal");
    _tree_indent();
    time = _th_rewrite(env, _ex_intern_appl3_env(env,INTERN_NEXT,signal->u.appl.args[1],
        _ex_intern_string("CLK"),_ex_intern_small_integer(1)));
    do {
        _tree_print_exp("time", time);
        signal = _ex_intern_appl2_env(env,INTERN_REFERENCE, signal->u.appl.args[0], time);
        //result = _th_generate_universal(env,signal,NULL,NULL);
        //if (result) {
        //    _tree_print_exp("state", result);
        //    _tree_undent();
        //    return result;
        //}
        time = _th_rewrite(env, _ex_intern_appl3_env(env,INTERN_NEXT,time,
            _ex_intern_string("CLK"),_ex_intern_small_integer(1)));
        lt = time;
        printf("signal = %s", _th_print_exp(signal));
        fflush(stdout);
        _th_rewrite(env,_ex_true);
        result = _th_generate_universal(env,_ex_intern_appl2_env(env,INTERN_TUPLE,_th_rewrite(env,signal),exp),
            less_time,signal_weight);
        if (result) {
            _tree_print_exp("other", result);
            _tree_undent();
            return result;
        }
    } while (signal !=NULL && time_in_range(env, exp, time));

    _tree_undent();
    return NULL;
}
#endif

static int exp_has_var_list(struct module_list *module, struct variable_list *list, struct _ex_intern *exp)
{
    while (list != NULL) {
        if (exp_has_variable(module,list->variable,exp)) return 1;
        list = list->next;
    }

    return 0;
}

static int exp_has_var(struct variable_list *list, struct _ex_intern *exp)
{
    int i;
    //struct effects_list *effects;

    switch (exp->type) {
        case EXP_APPL:
            if (exp->u.appl.functor==INTERN_REFERENCE) {
                struct variable_list *l = list;
                while (l != NULL) {
                    if (exp->u.appl.args[0]->type==EXP_STRING &&
                        !strcmp(l->variable,exp->u.appl.args[0]->u.string)) return 1;
                    //effects = l->effects_list;
                    //while (effects != NULL) {
                    //    if (exp->u.appl.args[0]->type==EXP_STRING &&
                    //        !strcmp(effects->variable,exp->u.appl.args[0]->u.string)) return 1;
                    //    effects = effects->next;
                    //}
                    l = l->next;
                }
            }
            for (i = 0; i < exp->u.appl.count; ++i) {
                if (exp_has_var(list, exp->u.appl.args[i])) {
                    return 1;
                }
            }
            return 0;

        case EXP_QUANT:
            if (exp_has_var(list,exp->u.quant.exp)) {
                return 1;
            }
            return exp_has_var(list,exp->u.quant.cond);

        default:
            return 0;
    }
}

struct child_edge_list *normalize(struct env *env, struct heuristic_node *node,
                                  struct module_list *module, struct child_edge_list *list,
                                  int cycle)
{
    struct _ex_intern *e;
    struct child_edge_list *l;
    struct child_edge_list *f, *p, *c;

    if (list==NULL) return NULL;

    _tree_print1("Normalizing %d", list->child);
    _tree_indent();

    l = module->condition_nodes[list->child].children;
    while (l != NULL) {
        e = module->condition_nodes[l->child].condition;
        if (e != NULL) {
            struct _ex_unifier *u;
            u = _th_new_unifier(HEURISTIC_SPACE);
            _th_add_pair(HEURISTIC_SPACE,u,INTERN_CURRENT,
                _ex_intern_appl3_env(env,INTERN_NEXT,
                _ex_intern_var(INTERN_CURRENT),
                _ex_intern_string("CLK"),
                _ex_intern_small_integer(cycle)));
            e = _th_subst(env,u,e);
            e = _th_rewrite(env,e);
            if (e != _ex_true && e != _ex_false) {
                _tree_undent();
                list->next = normalize(env, node, module, list->next, cycle);
                return list;
            }
        }
        l = l->next;
    }

    l = module->condition_nodes[list->child].children;
    p = f = NULL;
    while (l != NULL) {
        e = module->condition_nodes[l->child].condition;
        if (cycle > 0 && e != NULL) {
            struct _ex_unifier *u;
            u = _th_new_unifier(HEURISTIC_SPACE);
            _th_add_pair(HEURISTIC_SPACE,u,INTERN_CURRENT,
                _ex_intern_appl3_env(env,INTERN_NEXT,
                _ex_intern_var(INTERN_CURRENT),
                _ex_intern_string("CLK"),
                _ex_intern_small_integer(cycle)));
            e = _th_subst(env,u,e);
            
        }
        if (e != NULL && _th_rewrite(env,e)==_ex_true) {
            c = (struct child_edge_list *)_th_alloc(HEURISTIC_SPACE,sizeof(struct child_edge_list));
            if (p==NULL) {
                f = c;
            } else {
                p->next = c;
            }
            c->child = l->child;
            c->next = NULL;
            p = c;
        }
        l = l->next;
    }
    if (p != NULL) {
        p->next = list->next;
        list = p;
    } else {
        list = list->next;
    }
    list = normalize(env, node, module, list, cycle);

    _tree_undent();

    return list;
}

void normalize_nodes(struct env *env, struct heuristic_node *node, struct module_list *module, int cycle)
{
    int i, count;
    struct child_edge_list *list, *l;

    list = NULL;

    _tree_print0("Normalize nodes");
    _tree_indent();

    _tree_print0("Before");
    _tree_indent();
    for (i = 0; i < node->condition_count; ++i) {
        l = (struct child_edge_list *)_th_alloc(HEURISTIC_SPACE, sizeof(struct child_edge_list));
        l->next = list;
        l->child = node->conditions[i];
        list = l;
        _tree_print1("Node %d", l->child);
    }
    _tree_undent();

    _th_log_derive_push(env);
    _th_build_context(env,node->property);
    list = normalize(env, node, module, list, cycle);
    _th_log_derive_pop(env);

    l = list;
    count = 0;
    while (l != NULL) {
        ++count;
        l = l->next;
    }
    node->conditions = (int *)_th_alloc(HEURISTIC_SPACE,sizeof(int) * count);
    node->condition_count = count;

    _tree_print0("After");
    _tree_indent();
    l = list;
    i = 0;
    while (l != NULL) {
        _tree_print1("Node %d", l->child);
        node->conditions[i] = l->child;
        l = l->next;
        ++i;
    }
    _tree_undent();

    _tree_undent();
}

void generate_children(struct env *env, struct heuristic_node *node, struct module_list *module,
                       struct child_edge_list *children, struct child_edge_list *in_condition,
                       struct _ex_intern *exp, int time_step, int cond_pos)
{
    struct child_edge_list cond;
    struct _ex_intern *e, *rew;

    if (children==NULL) {
        struct heuristic_node *n = _th_new_node(node);
        int count, i;
        struct child_edge_list *c;
        int *nodes;
        count = 0;
        c = in_condition;
        while (c != NULL) {
            c = c->next;
            ++count;
        }
        nodes = (int *)_th_alloc(HEURISTIC_SPACE, sizeof(int) * (count + node->condition_count-1));
        for (i = 1; i < node->condition_count; ++i) {
            if (i <= cond_pos) {
                nodes[i-1] = node->conditions[i-1];
            } else {
                nodes[i-1] = node->conditions[i];
            }
        }
        c = in_condition;
        for (i = 0; i < count; ++i) {
            nodes[i+node->condition_count-1] = c->child;
            c = c->next;
        }
        n->conditions = nodes;
        n->condition_count = node->condition_count-1+count;
        _tree_print1("count %d", n->condition_count);
        _tree_print_exp("Leaf", exp);
        n->assumption = exp;
        n->property = _th_flatten(env,_ex_intern_appl2_env(env,INTERN_OR,node->property,
            _ex_intern_appl1_env(env,INTERN_NOT,exp)));

        normalize_nodes(env,n,module, n->time_step);

        return;
    }

    _tree_print_exp("Generate children", module->condition_nodes[children->child].condition);
    _tree_indent();
    rew = module->condition_nodes[children->child].condition;
    if (time_step > 0) {
        struct _ex_unifier *u;
        u = _th_new_unifier(HEURISTIC_SPACE);
        _th_add_pair(HEURISTIC_SPACE,u,INTERN_CURRENT,
            _ex_intern_appl3_env(env,INTERN_NEXT,
            _ex_intern_var(INTERN_CURRENT),
            _ex_intern_string("CLK"),
            _ex_intern_small_integer(time_step)));
        rew = _th_subst(env,u,rew);
        
    }
    rew = _th_rewrite(env,rew);

    if (!module->condition_nodes[children->child].valid_for_node) {
        _tree_print0("Out1");
        generate_children(env,node,module,children->next,in_condition,exp,time_step, cond_pos);
    } else if (rew==_ex_true) {
        cond.next = in_condition;
        cond.child = children->child;
        _tree_print0("In1");
        generate_children(env,node,module,children->next,&cond,exp,time_step, cond_pos);
    } else if (rew==_ex_false) {
        _tree_print0("Out2");
        generate_children(env,node,module,children->next,in_condition,exp,time_step, cond_pos);
    } else {
        e = _th_flatten(env,_ex_intern_appl2_env(env,INTERN_AND,exp,rew));
        e = _th_rewrite(env,e);
        if (e != _ex_false) {
            cond.next = in_condition;
            cond.child = children->child;
            _tree_print0("In2");
            generate_children(env,node,module,children->next,&cond,e,time_step, cond_pos);
        }

        e = _th_flatten(env,_ex_intern_appl2_env(env,INTERN_AND,exp,
                _ex_intern_appl1_env(env,INTERN_NOT,rew)));
        e = _th_rewrite(env,e);
        if (e != _ex_false) {
            _tree_print0("Out3");
            generate_children(env,node,module,children->next,in_condition,e,time_step, cond_pos);
        }
    }
    _tree_undent();
}

static void print_c_tree(struct env *env, struct module_list *module, int node)
{
    struct child_edge_list *children = module->condition_nodes[node].children;
    //_tree_print1("node %d:", t_exp(module->condition_nodes[node].condition);
    _tree_indent();
    while (children != NULL) {
        print_c_tree(env, module, children->child);
        children = children->next;
    }
    _tree_undent();
}

static void print_cond_tree(struct env *env, struct module_list *module)
{
    int i;

    _tree_print0("Condition tree");
    _tree_indent();
    for (i =0; i < module->condition_node_count; ++i) {
        if (module->condition_nodes[i].condition==NULL) print_c_tree(env,module,i);
    }
    _tree_undent();
}

static struct heuristic_node *have_induction(struct heuristic_node *node)
{
    struct heuristic_node *parent;

    parent = node->parent;
    while (parent != NULL) {
        if (!strcmp(parent->heuristic,"time_induction")) return parent;
        parent = parent->parent;
    }

    return 0;
}

static void condition_tree(struct env *env, struct heuristic_node *node, struct module_list *module)
{
    int i;

    if (node->conditions==NULL) {
        int roots, root;
//cont:
        //if (node->time_step > 0) return;
        if (node->time_step > 0) {
            struct _ex_intern *e = _ex_intern_appl3_env(env, INTERN_NEXT,
                    _ex_intern_var(INTERN_CURRENT),
                    _ex_intern_string("CLK"), _ex_intern_small_integer(node->time_step));
            if (all_times_equal_smaller(env,node->property,e)) return;
        }
        roots = 0;
        for (i = 0; i < module->condition_node_count; ++i) {
            if (module->condition_nodes[i].condition==NULL) ++roots;
        }
        node->condition_count = roots;
        node->conditions = (int *)_th_alloc(HEURISTIC_SPACE,sizeof(int) * roots);
        roots = 0;
        for (i = 0; i < module->condition_node_count; ++i) {
            if (module->condition_nodes[i].condition==NULL) {
                root = i;
                while (module->condition_nodes[root].children &&
                       module->condition_nodes[root].children->next==NULL &&
                       module->condition_nodes[module->condition_nodes[root].children->child].condition==_ex_true) {
                    root = module->condition_nodes[root].children->child;
                }
                node->conditions[roots++] = root;
            }
        }
        normalize_nodes(env,node,module,node->time_step);
        _tree_print0("Nodes");
        _tree_indent();
        for (i = 0; i < node->condition_count; ++i) {
            _tree_print2("Node %d %s", node->conditions[i], _th_print_exp(module->condition_nodes[node->conditions[i]].condition));
        }
        _tree_undent();
    }

    if (node->condition_count==0) return;

    _tree_print2("Testing for valid condition %d %s\n", node->time_step, _th_print_exp(node->property));
    _tree_indent();
    for (i = 0; i < node->condition_count; ++i) {
        int has_valid_child = 0;
        struct child_edge_list *child = module->condition_nodes[node->conditions[i]].children;
        _tree_print1("Testing condition %d", node->conditions[i]);
        _tree_indent();
        while (child != NULL) {
            int branch = module->condition_nodes[child->child].branch;
            struct variable_list *vl = module->condition_nodes[branch].variable_list;
            _tree_print0("variables");
            _tree_indent();
            while (vl != NULL) {
                _tree_print1("%s", vl->variable);
                vl = vl->next;
            }
            _tree_undent();
            _tree_print2("Child, branch %d %d\n", child->child, branch);
            has_valid_child = (module->condition_nodes[child->child].valid_for_node =
                exp_has_var_list(module, module->condition_nodes[branch].variable_list, node->property)) ||
                has_valid_child;
            child = child->next;
        }
        _tree_undent();
        _tree_print1("has valid child %d", has_valid_child);
        if (has_valid_child) break;
    }
    _tree_undent();
    _tree_print2("i = %d %d", i, node->condition_count);
    if (i==node->condition_count) {
        struct heuristic_node *hi = have_induction(node);
        struct heuristic_node *n;
        if (hi && node->time_step==0) return;
        if (node->time_step > 0) {
            struct _ex_intern *e = _ex_intern_appl3_env(env, INTERN_NEXT,
                    _ex_intern_var(INTERN_CURRENT),
                    _ex_intern_string("CLK"), _ex_intern_small_integer(node->time_step));
            if (hi && all_times_equal_smaller(env,hi->property,e)) {
                n = _th_new_node(node);
                n->time_step = 0;
                n->conditions = NULL;
                n->property = node->property;
                n->assumption = _ex_true;
                node->heuristic = "time_step_zero";
                return;
            }
        }
        n = _th_new_node(node);
        n->time_step = node->time_step+1;
        n->conditions = NULL;
        n->property = node->property;
        n->assumption = _ex_true;
        node->heuristic = "time_step";
        return;
    }

    _th_log_derive_push(env);
    _th_build_context(env,node->property);

    generate_children(env, node, module, module->condition_nodes[node->conditions[i]].children,
        NULL, _ex_true, node->time_step, i);

    _th_log_derive_pop(env);

    if (node->first_child) {
        node->heuristic = "condition_tree";
        node = node->first_child;
        _tree_print1("Condition tree cases %d", node->time_step);
        _tree_indent();
        while (node != NULL) {
            _tree_print0("Node");
            _tree_indent();
            for (i = 0; i < node->condition_count; ++i) {
                _tree_print2("Condition %d %s", node->conditions[i], _th_print_exp(module->condition_nodes[node->conditions[i]].condition));
            }
            _tree_undent();
            node = node->next;
        }
        _tree_undent();
    }
}

static int timing_offset_var(struct _ex_intern *e, unsigned var)
{
    int i;
    int offset, min_offset;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor==INTERN_REFERENCE && e->u.appl.count==2 &&
                e->u.appl.args[0]->type==EXP_STRING) {
                struct _ex_intern *f = e->u.appl.args[1];
                if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NEXT && f->u.appl.count==3) {
                    struct _ex_intern *g = f->u.appl.args[2];
                    if (g->type==EXP_VAR && g->u.var==var) {
                        return 0;
                    }
                    if (g->type==EXP_APPL && g->u.appl.functor==INTERN_NAT_PLUS && g->u.appl.count==2) {
                        if (g->u.appl.args[0]->type==EXP_VAR && g->u.appl.args[0]->u.var==var &&
                            g->u.appl.args[1]->type==EXP_INTEGER) {
                            struct _ex_intern *h;
                            h = g->u.appl.args[1];
                            if (h->u.integer[0]==1) return h->u.integer[1];
                        }
                        if (g->u.appl.args[1]->type==EXP_VAR && g->u.appl.args[1]->u.var==var &&
                            g->u.appl.args[0]->type==EXP_INTEGER) {
                            struct _ex_intern *h;
                            h = g->u.appl.args[0];
                            if (h->u.integer[0]==1) return h->u.integer[1];
                        }
                    }
                }
            }
            min_offset = -1;
            for (i = 0; i < e->u.appl.count; ++i) {
                offset = timing_offset_var(e->u.appl.args[i], var);
                if (min_offset = -1 || (offset > -1 && offset < min_offset)) {
                    min_offset = offset;
                }
                if (offset==0) return 0;
            }
            return min_offset;

        case EXP_QUANT:
            offset = timing_offset_var(e->u.quant.exp, var);
            if (offset==0) return 0;
            min_offset = timing_offset_var(e->u.quant.cond, var);
            if (min_offset==-1) return offset;
            if (offset > -1 && offset < min_offset) {
                return offset;
            } else {
                return min_offset;
            }

        default:
            return -1;
    }
}

static struct _ex_intern *split_exists(struct env *env, struct _ex_intern *e, int time)
{
    struct _ex_intern *exp1, *exp2, *exp3;
    int i, offset;
    unsigned var;

    /**********/

    if (e->type != EXP_QUANT) return NULL;
    if (e->u.quant.quant!=INTERN_EXISTS) return NULL;

    _tree_print_exp("Testing", e);

    for (i = 0; i < e->u.quant.var_count; ++i) {
        offset = timing_offset_var(e->u.quant.exp,e->u.quant.vars[i]);
        var = e->u.quant.vars[i];
        if (offset >= 0) break;
    }

    _tree_print1("offset = %d", offset);

    if (offset < 0) return NULL;

    time -= offset;
    if (time+1<0) return NULL;

    if (time < 0) {
        exp1 = _ex_false;
    } else {
        exp1 = _ex_intern_quant(INTERN_EXISTS,e->u.quant.var_count,e->u.quant.vars,
                   _th_flatten(env,_ex_intern_appl2_env(env,INTERN_AND,
                       _ex_intern_appl2_env(env,INTERN_EQUAL,
                           _ex_intern_var(var),
                           _ex_intern_small_integer(time)),
                       e->u.quant.exp)),
                   e->u.quant.cond);
        exp1 = _th_rewrite(env,exp1);
    }

    exp2 = _ex_intern_quant(INTERN_EXISTS,e->u.quant.var_count,e->u.quant.vars,
               _th_flatten(env,_ex_intern_appl2_env(env,INTERN_AND,
                   _ex_intern_appl2_env(env,INTERN_EQUAL,
                       _ex_intern_var(var),
                       _ex_intern_small_integer(time+1)),
                   e->u.quant.exp)),
               e->u.quant.cond);
    exp2 = _th_rewrite(env,exp2);

    if (exp1==_ex_false) {
        exp3 = _ex_intern_quant(INTERN_EXISTS,e->u.quant.var_count,e->u.quant.vars,
            _th_flatten(env,_ex_intern_appl2_env(env,INTERN_AND,
                _ex_intern_appl1_env(env,INTERN_NOT,
                    _ex_intern_appl2_env(env,INTERN_EQUAL,
                        _ex_intern_var(var),
                        _ex_intern_small_integer(time+1))),
                    e->u.quant.exp)),
                e->u.quant.cond);
        exp3 = _th_rewrite(env,exp3);
    } else {
        exp3 = _ex_intern_quant(INTERN_EXISTS,e->u.quant.var_count,e->u.quant.vars,
            _th_flatten(env,_ex_intern_appl3_env(env,INTERN_AND,
                _ex_intern_appl1_env(env,INTERN_NOT,
                    _ex_intern_appl2_env(env,INTERN_EQUAL,
                    _ex_intern_var(var),
                _ex_intern_small_integer(time))),
                _ex_intern_appl1_env(env,INTERN_NOT,
                    _ex_intern_appl2_env(env,INTERN_EQUAL,
                        _ex_intern_var(var),
                        _ex_intern_small_integer(time+1))),
                    e->u.quant.exp)),
                e->u.quant.cond);
    }
    exp3 = _th_rewrite(env,exp3);
    if (exp1==_ex_false && exp2==_ex_false) return NULL;
    if (exp3==e) return NULL;

    return _ex_intern_appl3_env(env,INTERN_OR,exp1,exp2,exp3);
}

static struct _ex_intern *find_and_split_exists(struct env *env, struct heuristic_node *node, struct _ex_intern *prop)
{
    int i;
    struct _ex_intern *e, *f;
    //struct heuristic_node *n;

    //e = node->property;
    e = prop;

    _tree_print0("Testing split exists");
    _tree_indent();

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_OR) {
        for (i = 0; i < e->u.appl.count; ++i) {
            f = split_exists(env,e->u.appl.args[i],node->time_step);
            if (f != NULL) {
                struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
                int j;
                for (j = 0; j < prop->u.appl.count; ++j) {
                    if (i != j) {
                        args[j] = prop->u.appl.args[j];
                    } else {
                        args[j] = f;
                    }
                }
                f = _ex_intern_appl_env(env,INTERN_OR,prop->u.appl.count,args);
                f = _th_flatten(env,f);
                goto cont;
            }
        }
        _tree_undent();
        return NULL;
    } else {
        f = split_exists(env,e,node->time_step);
        if (e==NULL) {
            _tree_undent();
            return NULL;
        }
    }
cont:
    //n = _th_new_node(node);
    //node->heuristic = "divide_exists";
    //n->property = f;
    //n->assumption = _ex_true;

    _tree_undent();

    return f;
}

static struct match_return *matched_terms(struct env *env, struct _ex_intern *p, struct _ex_intern *e)
{
    struct match_return *mr;

    mr = _th_match(env,p,e);
    if (mr) return mr;
    if (p->type==EXP_APPL && p->u.appl.count==1 && p->u.appl.functor==INTERN_NOT) {
        mr = _th_match(env,p->u.appl.args[0],e);
        if (mr) return mr;
    }
    if (e->type==EXP_APPL && e->u.appl.count==1 && e->u.appl.functor==INTERN_NOT) {
        mr = _th_match(env,p,e->u.appl.args[0]);
        if (mr) return mr;
    }
    if (e->type==EXP_APPL && p->type==EXP_APPL && e->u.appl.count==2 && p->u.appl.count==2 &&
        e->u.appl.functor==INTERN_EQUAL && p->u.appl.functor==INTERN_EQUAL) {
        if (e->u.appl.args[1]->type==EXP_INTEGER) {
            e = e->u.appl.args[0];
        } else if (e->u.appl.args[0]->type==EXP_INTEGER) {
            e = e->u.appl.args[1];
        } else {
            goto cont;
        }
        if (p->u.appl.args[1]->type==EXP_INTEGER) {
            p = p->u.appl.args[0];
        } else if (p->u.appl.args[0]->type==EXP_INTEGER) {
            p = p->u.appl.args[1];
        } else {
            goto cont;
        }
        mr = _th_match(env,p,e);
        if (mr) return mr;
    }
cont:
    return NULL;
}

static struct _ex_intern *extract_not_all(struct env *env, struct heuristic_node *node, struct _ex_intern *prop)
{
    int i, j, k;
    struct _ex_intern *e, *f, *r;
    //struct heuristic_node *n;
    char *mark;

    //e = node->property;
    e = prop;

    _tree_print0("Testing extract not all");
    _tree_indent();

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_OR) {
        for (i = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type==EXP_APPL && e->u.appl.args[i]->u.appl.functor==INTERN_NOT &&
                e->u.appl.args[i]->u.appl.count==1) {
                f = e->u.appl.args[i]->u.appl.args[0];
                if (f->type==EXP_QUANT && f->u.quant.quant==INTERN_ALL &&
                    f->u.quant.cond==_ex_true) {
                    f = _th_mark_vars(env,f);
                    f = f->u.quant.exp;
                    _tree_print_exp("Testing", f);
                    if (f->type==EXP_APPL && f->u.appl.functor==INTERN_OR) {
                        mark = _th_alloc_mark(MATCH_SPACE);
                        for (j = 0; j < f->u.appl.count; ++j) {
                            for (k = 0; k < e->u.appl.count; ++k) {
                                struct match_return *mr;
                                if (i != k) {
                                    mr = matched_terms(env,f->u.appl.args[j],e->u.appl.args[k]);
                                    if (mr != NULL) {
                                        _tree_print_exp("Got result for", e->u.appl.args[k]);
                                        _tree_print_exp("and", f->u.appl.args[j]);
                                        r = _th_subst(env,mr->theta,f);
                                        _th_log_derive_push(env);
                                        _th_build_context(env,prop);
                                        r = _th_rewrite(env,_ex_intern_appl1_env(env,INTERN_NOT,r));
                                        _th_log_derive_pop(env);
                                        _tree_print_exp("rewrite", r);
                                        if (r != _ex_false) {
                                            _th_alloc_release(MATCH_SPACE,mark);
                                            goto cont;
                                        }
                                    }
                                }
                            }
                        }
                        _th_alloc_release(MATCH_SPACE,mark);
                    }
                }
            }
        }
    }
    _tree_undent();
    return NULL;
cont:
    //n = _th_new_node(node);
    //node->heuristic = "extract_not_all";
    //_tree_print_exp("Adding", r);
    //n->property = _th_flatten(env,_ex_intern_appl2_env(env,INTERN_OR,e,r));
    //n->assumption = _ex_true;

    _tree_undent();

    return _th_flatten(env,_ex_intern_appl2_env(env,INTERN_OR,e,r));
}

static struct _ex_intern *extract_exists(struct env *env, struct heuristic_node *node, struct _ex_intern *prop)
{
    int i, k;
    struct _ex_intern *e, *f, *r;
    //struct heuristic_node *n;
    char *mark;

    //e = node->property;
    e = prop;

    _tree_print0("Testing extract exists");
    _tree_indent();

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_OR) {
        for (i = 0; i < e->u.appl.count; ++i) {
            f = e->u.appl.args[i];
            if (f->type==EXP_QUANT && f->u.quant.quant==INTERN_EXISTS &&
                f->u.quant.cond==_ex_true) {
                f = _th_mark_vars(env,f);
                f = f->u.quant.exp;
                _tree_print_exp("Testing", f);
                mark = _th_alloc_mark(MATCH_SPACE);
                for (k = 0; k < e->u.appl.count; ++k) {
                    struct match_return *mr;
                    if (i != k) {
                        mr = matched_terms(env,f,e->u.appl.args[k]);
                        if (mr != NULL) {
                            _tree_print_exp("Got result for", e->u.appl.args[k]);
                            _tree_print_exp("and", f);
                            r = _th_subst(env,mr->theta,f);
                            _th_log_derive_push(env);
                            _th_build_context(env,prop);
                            r = _th_rewrite(env,r);
                            _th_log_derive_pop(env);
                            _tree_print_exp("rewrite", r);
                            if (r != _ex_false) {
                                _th_alloc_release(MATCH_SPACE,mark);
                                goto cont;
                            }
                        }
                    }
                    _th_alloc_release(MATCH_SPACE,mark);
                }
            }
        }
    }
    _tree_undent();
    return NULL;
cont:
    //n = _th_new_node(node);
    //node->heuristic = "extract_not_all";
    //_tree_print_exp("Adding", r);
    //n->property = _th_flatten(env,_ex_intern_appl2_env(env,INTERN_OR,e,r));
    //n->assumption = _ex_true;

    _tree_undent();

    return _th_flatten(env,_ex_intern_appl2_env(env,INTERN_OR,e,r));
}

static void elaborate_heuristics(struct env *env, struct heuristic_node *node, struct module_list *ml)
{
    struct _ex_intern *e, *r;
    struct heuristic_node *n;
    int did_move_to_earlier_cycle = 0;
    char *mark;

    if (node->parent && !strcmp(node->parent->heuristic,"elaborate")) return;

    _tree_print0("Testing elaborate\n");
    _tree_indent();
    r = e = node->property;

    mark = _th_alloc_mark(REWRITE_SPACE);
    _ex_push();

    while (r) {
        r = find_and_split_exists(env,node,e);
        if (r) {
            e = _th_rewrite(env,r);
            _tree_print0("good");
        }
    }

    r = e;

    while (r) {
        r = NULL;
again1:
        r = extract_not_all(env,node,e);
        if (r) {
            did_move_to_earlier_cycle = 0;
            e = _th_rewrite(env,r);
            _tree_print0("good");
            goto again1;
        } else {
again15:
            r = extract_exists(env,node,e);
            if (r) {
                did_move_to_earlier_cycle = 0;
                e = _th_rewrite(env,r);
                _tree_print0("good");
                goto again15;
            } else {
again2:
                r = add_constant_assigns(env,node,e,ml);
                if (r) {
                    did_move_to_earlier_cycle = 0;
                    e = _th_rewrite(env,r);
                    _tree_print0("good");
                    goto again2;
                } else {
                    if (!did_move_to_earlier_cycle) r = move_to_earlier_cycle(env,node,e,ml);
                    if (r) {
                        did_move_to_earlier_cycle = 1;
                        e = _th_rewrite(env,r);
                        _tree_print0("good");
                    }
                }
            }
        }
    }

    _th_clear_cache();
    _th_transitive_reset();
    _ex_pop();
    if (e != NULL) e = _ex_reintern(env, e);
    _th_reintern_cache(env);
    _ex_release();

    _th_alloc_release(REWRITE_SPACE,mark);

    if (e != node->property) {
        n = _th_new_node(node);
        node->heuristic = "elaborate";
        _tree_print_exp("Adding", e);
        n->property = e;
        n->assumption = _ex_true;
    }

    _tree_undent();
}

void induction_heuristic(struct env *env, struct heuristic_node *node)
{
    struct _ex_intern *e;

    if (have_induction(node)) return;
    e = find_reference(node->property);
    if (e && no_next_greater_one(node->property) &&
        repeat_time_induction(node)) {
        struct _ex_unifier *u;
        struct heuristic_node *base_case, *inductive_case;
        _tree_print0("induction");
        base_case = _th_new_node(node);
        inductive_case = _th_new_node(node);
        u = _th_new_unifier(HEURISTIC_SPACE);
        _th_add_pair(HEURISTIC_SPACE,u,e->u.appl.args[1]->u.var,_ex_intern_small_integer(0));
        inductive_case->next = NULL;
        base_case->assumption = _ex_true;
        base_case->property = _th_subst(env,u,node->property);
        inductive_case->assumption = _th_mark_vars(env,node->property);
        u = _th_new_unifier(HEURISTIC_SPACE);
        _th_add_pair(HEURISTIC_SPACE,u,INTERN_CURRENT,
            _ex_intern_appl3_env(env,INTERN_NEXT,
            _ex_intern_var(INTERN_CURRENT),
            _ex_intern_string("CLK"),
            _ex_intern_small_integer(2)));
        e = _th_subst(env,u,node->property);
        u = _th_new_unifier(HEURISTIC_SPACE);
        _th_add_pair(HEURISTIC_SPACE,u,INTERN_CURRENT,
            _ex_intern_appl3_env(env,INTERN_NEXT,
            _ex_intern_var(INTERN_CURRENT),
            _ex_intern_string("CLK"),
            _ex_intern_small_integer(1)));
        inductive_case->assumption = _th_subst(env,u,node->property);
        inductive_case->property = _th_flatten(env,_ex_intern_appl2_env(env,INTERN_OR,
            _ex_intern_appl1_env(env,INTERN_NOT,inductive_case->assumption),
            e));
        inductive_case->time_step = 1;
        node->heuristic = "time_induction";
    }
}

static struct module_list *gml;

static int verilog_heuristics(struct env *env, struct heuristic_node *node, char *heuristic)
{
    //struct _ex_intern *e;

    //_th_global_heuristics(0,env,node,NULL);
    //if (node->first_child) return 1;
    elaborate_heuristics(env,node,gml);
    if (node->first_child) return 1;
    //find_and_split_exists(env,node);
    //if (node->first_child) return 1;
    //extract_not_all(env,node);
    //if (node->first_child) return 1;
    //move_to_earlier_cycle(env,node);
    //if (node->first_child) return 1;
    //add_constant_assigns(env,node,gml);
    //if (node->first_child) return 1;
    //move_to_earlier_cycle(env,node,gml);
    //if (node->first_child) return 1;
    induction_heuristic(env,node);
    if (node->first_child) return 1;
    condition_tree(env,node,gml);
    if (node->first_child) return 1;

#ifdef OLD_HEURISTICS
    state_condition_case(env,node);
    if (node->first_child) return 1;
    move_to_earlier_cycle(env,node,gml);
    if (node->first_child) return 1;
    add_constant_assigns(env,node);
    if (node->first_child) return 1;
    state_var_case(env,node,gml);
    if (node->first_child) return 1;
    _ex_push();
    e = state_universal(env, node);
    _th_clear_cache();
    _th_transitive_reset();
    _ex_pop();
    if (node->first_child) return 1;
    if (e != NULL) e = _ex_reintern(env, e);
    _th_reintern_cache(env);
    _ex_release();
    if (e) {
        struct heuristic_node *base_case, *not_case;
        _tree_print0("state universal");
        base_case = _th_new_node(node);
        not_case = _th_new_node(node);
        //_tree_start = 0; _tree_end = 2000000;
        //_tree_sub = _tree_sub2 = -1;
        //_tree_mute = 0;
        //base_case->assumption = _th_mark_vars(env,_th_rewrite(env, e));
        base_case->assumption = e;
        base_case->property = _th_flatten(env,_ex_intern_appl2_env(env,INTERN_OR,_ex_intern_appl1_env(env,INTERN_NOT,e),node->property));;
        //not_case->assumption = _th_mark_vars(env,_th_rewrite(env, _ex_intern_appl1_env(env,INTERN_NOT,e)));
        not_case->assumption = _ex_intern_appl1_env(env,INTERN_NOT,e);
        //_tree_mute = 1;
        not_case->property = _th_flatten(env,_ex_intern_appl2_env(env,INTERN_OR,node->property,e));
        node->heuristic = "state_universal";
    }

    // divider

    e = find_reference(node->property);
    if (e && no_next_greater_one(node->property) &&
        repeat_time_induction(node)) {
        struct _ex_unifier *u;
        struct heuristic_node *base_case, *inductive_case;
        _tree_print0("induction");
        base_case = _th_new_node(node);
        inductive_case = _th_new_node(node);
        u = _th_new_unifier(HEURISTIC_SPACE);
        _th_add_pair(HEURISTIC_SPACE,u,e->u.appl.args[1]->u.var,_ex_intern_small_integer(0));
        inductive_case->next = NULL;
        base_case->assumption = _ex_true;
        base_case->property = _th_subst(env,u,node->property);
        inductive_case->assumption = _th_mark_vars(env,node->property);
        u = _th_new_unifier(HEURISTIC_SPACE);
        _th_add_pair(HEURISTIC_SPACE,u,INTERN_CURRENT,
            _ex_intern_appl3_env(env,INTERN_NEXT,
            _ex_intern_var(INTERN_CURRENT),
            _ex_intern_string("CLK"),
            _ex_intern_small_integer(1)));
        inductive_case->property = _th_subst(env,u,node->property);
        node->heuristic = "time_induction";
        return 1;
    }
#endif

    return 0;
}

void _th_add_verilog_assertions(struct env *env, struct module_list *ml)
{
    struct add_list *al;
    struct assign_group *g;
    struct module_pointer_list *mpl;
    struct _ex_intern *e;
    struct _ex_intern **args;
    int count;

    _tree_print0("add_verilog_assertions");
    _tree_indent();
    al = ml->declarations;
    while (al != NULL) {
        if (al->e->type==EXP_APPL && al->e->u.appl.functor==INTERN_ASSIGN) {
        } else {
            _tree_print_exp("Adding non-assign", al->e);
            _th_log_derive_and_add(env, (e = _th_derive_simplify(env,al->e)));
            _tree_indent();
            _tree_print_exp("rule", e);
            if (al->e->type==EXP_APPL) {
                switch (al->e->u.appl.functor) {
                    case INTERN_REG_VECTOR:
                    case INTERN_WIRE_VECTOR:
                    case INTERN_INPUT_VECTOR:
                    case INTERN_OUTPUT_VECTOR:
                    case INTERN_INOUT_VECTOR:
                    case INTERN_REG:
                    case INTERN_WIRE:
                    case INTERN_INPUT:
                    case INTERN_OUTPUT:
                    case INTERN_INOUT:
                        if (al->e->u.appl.count==1) {
                            e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,
                                    _ex_intern_appl1_env(env,INTERN_SIGNAL_WIDTH,al->e->u.appl.args[0]),
                                    _ex_intern_small_integer(1),
                                    _ex_true);
                        } else {
                            e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,
                                    _ex_intern_appl1_env(env,INTERN_SIGNAL_WIDTH,al->e->u.appl.args[0]),
                                    _ex_intern_small_integer(
                                        al->e->u.appl.args[1]->u.integer[1]-
                                            al->e->u.appl.args[2]->u.integer[1]+1),
                                    _ex_true);
                        }
                        break;
                    default:
                        e = NULL;
                }
                if (e) {
                    _th_log_derive_and_add(env, (e = _th_derive_simplify(env,e)));
                    _tree_print_exp("rule", e);
                }
            }
            _tree_undent();
        }
        al = al->next;
    }

    count = 0;
    g = ml->groups;
    while (g != NULL) {
        al = g->assigns;
        while (al != NULL) {
            ++count;
            al = al->next;
        }
        g = g->next;
    }

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);

    count = 0;
    g = ml->groups;
    while (g != NULL) {
        al = g->assigns;
        while (al != NULL) {
            //_th_log_derive_and_add(env,
            //    _th_derive_simplify(env, build_assign_assertion(al->e,"CLK")));
            _tree_print_exp("Adding assign2", al->e);
            e = build_assign_assertion_future(al->e,"CLK");
            args[count++] = e;
            _tree_indent();
            _tree_print_exp("rule", e);
            _tree_undent();
            al = al->next;
        }
        g = g->next;
    }
    ml->assign_exp = _ex_intern_appl_env(env,INTERN_TUPLE,count,args);

    mpl = ml->children;
    while (mpl != NULL) {
        al = mpl->instantiation;
        while (al != NULL) {
            if (al->e->type==EXP_APPL && al->e->u.appl.functor==INTERN_ASSIGN) {
            } else {
                _tree_print_exp("Adding assign3", al->e);
                _th_log_derive_and_add(env, (e = _th_derive_simplify(env,al->e)));
                _tree_indent();
                _tree_print_exp("rule", e);
                _tree_undent();
            }
            al = al->next;
        }
        mpl = mpl->next;
    }
    _tree_undent();
}

struct _ex_intern *_th_verify_assertion(struct module_list *ml, struct _ex_intern *e, char *local)
{
    struct _ex_intern *res ;
    char *mark, *env_mark ;
    int save_state ;
#ifndef FAST
    int tree_start_save, tree_end_save, tree_sub_save, tree_sub2_save;
#endif
    struct heuristic_node *node;
    struct env *env;

    setApplicationHook(verilog_heuristics,hnames);

    mark = _th_log_start_rewrite() ;

#ifndef FAST
    if (local) {
        tree_start_save = _tree_start;
        tree_end_save = _tree_end;
        tree_sub_save = _tree_sub;
        tree_sub2_save = _tree_sub2;
        _tree_start = 0;
        _tree_end = 2000000;
        _tree_sub = _tree_sub2 = -1;
        _tree_start_local(local);
        _tree_print2("Processing assertion %s in module %s",
            _th_print_exp(e), _th_intern_decode(ml->name));
    }
#endif

    _tree_print0("Adding context rules") ;
    _tree_indent() ;

    env_mark = _th_alloc_mark(ENVIRONMENT_SPACE);

    env = _th_copy_env(ENVIRONMENT_SPACE,verilog_env);

    _th_log_derive_push(env) ;

    env = _th_build_module_env(env,ml->name,_th_derivation[verilog_derivation]);

    _th_add_verilog_assertions(env, ml) ;
    _th_derive_add_prepared(env,_th_derive_prepare(verilog_env,
        _ex_intern_appl1_env(env,INTERN_NOT,
            _ex_intern_appl2_env(env,INTERN_NAT_LESS,
                _ex_intern_var(INTERN_CURRENT),
                _ex_intern_small_integer(0))))) ;

    gml = ml;

    //terms = _th_log_rewrite(env,terms);

    _tree_undent();

    _tree_print_exp("Rewriting", e);
    _zone_increment() ;
    //res = _th_check_rewrite(e) ;
    //if (res) {
    //    _tree_print_exp("From memory", res);
    //    return res==_ex_true ;
    //}
    //if (terms->type==EXP_APPL && terms->u.appl.functor==INTERN_AND) {
    //    for (i = 0; i < terms->u.appl.count; ++i) {
    //        _zone_print1("Original %s", _th_print_exp(terms->u.appl.args[i])) ;
    //        _th_log_derive_and_add(env, _th_derive_simplify(env,terms->u.appl.args[i])) ;
    //    }
    //} else {
    //    _th_log_derive_and_add(env, _th_derive_simplify(env,terms)) ;
    //}
    //_tree_undent() ;

    //e = renamev(env, e, INTERN_STATE, state) ;
    //e = renamev(env, e, INTERN_STACK, stack) ;

    save_state = _th_check_state ;
    _th_check_state = 100 ;
    _th_test_mode = 1 ;
    print_cond_tree(env,ml);
    node = heuristic_solve(env, e);
    //res = _th_log_int_rewrite(verilog_env, e, 1) ;
    //_zone_print1("Result: %s", _th_print_exp(res)) ;

    _th_test_mode = 0 ;
    _th_check_state = save_state ;

    _th_log_derive_pop(env) ;

    if (node) {
        res = node->property;
    } else {
        res = _ex_false;
    }
    if (is_finished(node)) res = _ex_true;

    _th_alloc_release(ENVIRONMENT_SPACE,env_mark);

    res = _th_log_finish_rewrite(mark, env, res) ;
    _tree_print_exp("Done:", res);

    _th_set_rewrite(res) ;

#ifndef FAST
    if (local) {
        _tree_finish_local();
        _tree_start = tree_start_save;
        _tree_end = tree_end_save;
        _tree_sub = tree_sub_save;
        _tree_sub2 = tree_sub2_save;
    }
#endif

    return res;
}
