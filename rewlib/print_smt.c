/*
 * print_smt.c
 *
 * Routines for printing smt expressions
 * expression.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>

#include "Globals.h"
#include "Intern.h"

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

static struct _ex_intern *trail;

static void print_types(struct env *env, FILE *f, struct _ex_intern *e)
{
    struct _ex_intern *t;
    int i;

    switch (e->type) {
        case EXP_VAR:
            if (e->user2) return;
            t = get_type(env,e);
            if (t==_ex_bool) {
                fprintf(f, "    :extrapreds ((%s))\n", _th_intern_decode(e->u.var));
            } else if (t==_ex_real && _th_hack_conversion) {
                if (_th_hack_has_int) {
                    fprintf(f, "    :extrafuns ((%s Int))\n", _th_intern_decode(e->u.var));
                } else {
                    fprintf(f, "    :extrafuns ((%s Real))\n", _th_intern_decode(e->u.var));
                }
            } else if (t==_ex_int) {
                if (_th_hack_has_real && _th_hack_conversion) {
                    fprintf(f, "    :extrafuns ((%s Real))\n", _th_intern_decode(e->u.var));
                } else {
                    fprintf(f, "    :extrafuns ((%s Int))\n", _th_intern_decode(e->u.var));
                }
            } else {
                fprintf(f, "    :extrafuns ((%s %s))\n", _th_intern_decode(e->u.var), _th_intern_decode(t->u.appl.functor));
            }
            e->user2 = trail;
            trail = e;
            break;
        case EXP_APPL:
            if (e->user2) return;
            e->user2 = trail;
            trail = e;
            for (i = 0; i < e->u.appl.count; ++i) {
                print_types(env,f,e->u.appl.args[i]);
            }
            break;
    }
}

static void print_functors(struct env *env, FILE *f, struct _ex_intern *e)
{
    int i;

    if (e->type != EXP_APPL) return;
    if (e==_ex_true || e==_ex_false) return;

    if (e->user2) return;
    e->user2 = trail;
    trail = e;

    if (e->u.appl.functor != INTERN_NAT_PLUS && e->u.appl.functor != INTERN_NAT_TIMES &&
        e->u.appl.functor != INTERN_NAT_DIVIDE && e->u.appl.functor != INTERN_NAT_DIVIDE &&
        e->u.appl.functor != INTERN_NAT_MOD && e->u.appl.functor != INTERN_RAT_PLUS &&
        e->u.appl.functor != INTERN_RAT_TIMES && e->u.appl.functor != INTERN_RAT_MINUS &&
        e->u.appl.functor != INTERN_RAT_MOD && e->u.appl.functor != INTERN_RAT_DIVIDE &&
        e->u.appl.functor != INTERN_EQUAL && e->u.appl.functor != INTERN_XOR &&
        e->u.appl.functor != INTERN_AND && e->u.appl.functor != INTERN_OR &&
        e->u.appl.functor != INTERN_NOT && e->u.appl.functor != INTERN_ITE &&
        e->u.appl.functor != INTERN_NAT_LESS && e->u.appl.functor != INTERN_RAT_LESS &&
        e->u.appl.functor != INTERN_NAT_TO_RAT && e->u.appl.functor != INTERN_RAT_TO_NAT &&
        !_th_intern_get_data2(e->u.appl.functor)) {
        struct _ex_intern *type = _th_get_type(env,e->u.appl.functor);
        struct _ex_intern *t = type->u.appl.args[0];
        if (type->u.appl.args[1]==_ex_bool) {
            fprintf(f, "    :extrapreds ((%s", _th_intern_decode(e->u.appl.functor));
        } else {
            fprintf(f, "    :extrafuns ((%s", _th_intern_decode(e->u.appl.functor));
        }
        if (t->type==EXP_APPL && t->u.appl.functor==INTERN_TUPLE) {
            for (i = 0; i < t->u.appl.count; ++i) {
                fprintf(f, " %s", _th_intern_decode(t->u.appl.args[i]->u.appl.functor));
            }
        } else {
            fprintf(f, " %s", _th_intern_decode(t->u.appl.functor));
        }
        if (type->u.appl.args[1]==_ex_bool) {
            fprintf(f, "))\n");
        } else {
            fprintf(f, " %s))\n", _th_intern_decode(type->u.appl.args[1]->u.appl.functor));
        }
        _th_intern_set_data2(e->u.appl.functor,1);
    }

    for (i = 0; i < e->u.appl.count; ++i) {
        print_functors(env,f,e->u.appl.args[i]);
    }
}

static void clear_functors(struct env *env, FILE *f, struct _ex_intern *e)
{
    int i;

    if (e->type != EXP_APPL) return;
    if (e==_ex_true || e==_ex_false) return;

    if (e->user2) return;
    e->user2 = trail;
    trail = e;

    if (_th_intern_get_data2(e->u.appl.functor)) {
        _th_intern_set_data2(e->u.appl.functor,0);
    }

    for (i = 0; i < e->u.appl.count; ++i) {
        clear_functors(env,f,e->u.appl.args[i]);
    }
}

static struct _ex_intern *times_mo(struct _ex_intern *e)
{
    static struct _ex_intern *mo = NULL;

    if (mo==NULL) mo = _ex_intern_small_rational(-1,1);

    if (e->type != EXP_APPL) return NULL;

    if (e->u.appl.functor != INTERN_RAT_TIMES) return NULL;

    if (e->u.appl.count != 2) return NULL;

    if (e->u.appl.args[0]==mo) return e->u.appl.args[1];

    if (e->u.appl.args[1]==mo) return e->u.appl.args[0];

    return NULL;
}

static void print_formula(FILE *f, struct env *env, struct _ex_intern *e)
{
    int i;
    char *symbol;

    if (e==_ex_true) {
        fprintf(f, "true");
        return;
    } else if (e==_ex_false) {
        fprintf(f, "false");
        return;
    }

    switch (e->type) {
        case EXP_VAR:
            fprintf(f, "%s", _th_intern_decode(e->u.var));
            break;
        case EXP_INTEGER:
            fprintf(f, "%s", _th_print_exp(e));
            break;
        case EXP_RATIONAL:
            if (_th_big_is_negative(e->u.rational.numerator)) {
                e = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(e->u.rational.numerator)),e->u.rational.denominator);
                i = 1;
                fprintf(f, "(~ ");
            } else {
                i = 0;
            }
            if (e->u.rational.denominator[0]==1 && e->u.rational.denominator[1]==1) {
                fprintf(f, "%s", _th_print_exp(_ex_intern_integer(e->u.rational.numerator)));
            } else {
                fprintf(f, "(/ %s", _th_print_exp(_ex_intern_integer(e->u.rational.numerator)));
                fprintf(f, " %s)", _th_print_exp(_ex_intern_integer(e->u.rational.denominator)));
            }
            if (i) {
                fprintf(f,")");
            }
            break;
        case EXP_APPL:
            switch (e->u.appl.functor) {
                case INTERN_AND:
                    symbol = "and";
                    goto finish;
                case INTERN_XOR:
                    symbol = "xor";
                    goto finish;
                case INTERN_OR:
                    symbol = "or";
                    goto finish;
                case INTERN_ITE:
                    if (get_type(env,e->u.appl.args[1])==_ex_bool) {
                        symbol = "if_then_else";
                    } else {
                        symbol = "ite";
                    }
                    goto finish;
                case INTERN_NOT:
                    if (e->u.appl.args[0]==_ex_true) {
                        fprintf(f, "false");
                        break;
                    } else if (e->u.appl.args[0]==_ex_false) {
                        fprintf(f, "true");
                        break;
                    } else {
                        symbol = "not";
                        goto finish;
                    }
                case INTERN_NAT_TO_RAT:
                case INTERN_RAT_TO_NAT:
                    print_formula(f,env,e->u.appl.args[0]);
                    break;
                case INTERN_NAT_PLUS:
                case INTERN_RAT_PLUS:
                    if (e->u.appl.count==2 && e->u.appl.functor==INTERN_RAT_PLUS) {
                        struct _ex_intern *x;
                        if (e->u.appl.args[0]->type==EXP_RATIONAL && _th_big_is_negative(e->u.appl.args[0]->u.rational.numerator)) {
                            fprintf(f,"(- ");
                            print_formula(f,env,e->u.appl.args[1]);
                            fprintf(f, " ");
                            print_formula(f,env,_ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(e->u.appl.args[0]->u.rational.numerator)),e->u.appl.args[0]->u.rational.denominator));
                            fprintf(f, ")");
                            break;
                        }
                        if (e->u.appl.args[1]->type==EXP_RATIONAL && _th_big_is_negative(e->u.appl.args[1]->u.rational.numerator)) {
                            fprintf(f,"(- ");
                            print_formula(f,env,e->u.appl.args[0]);
                            fprintf(f, " ");
                            print_formula(f,env,_ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(e->u.appl.args[1]->u.rational.numerator)),e->u.appl.args[1]->u.rational.denominator));
                            fprintf(f, ")");
                            break;
                        }
                        if (x = times_mo(e->u.appl.args[0])) {
                            fprintf(f,"(- ");
                            print_formula(f,env,e->u.appl.args[1]);
                            fprintf(f, " ");
                            print_formula(f,env,x);
                            fprintf(f, ")");
                            break;
                        }
                        if (x = times_mo(e->u.appl.args[1])) {
                            fprintf(f,"(- ");
                            print_formula(f,env,e->u.appl.args[0]);
                            fprintf(f, " ");
                            print_formula(f,env,x);
                            fprintf(f, ")");
                            break;
                        }
                    }
                    symbol = "+";
                    goto finish;
                case INTERN_NAT_TIMES:
                case INTERN_RAT_TIMES:
                    symbol = "*";
                    goto finish;
                case INTERN_NAT_DIVIDE:
                case INTERN_RAT_DIVIDE:
                    symbol = "/";
                    goto finish;
                case INTERN_NAT_MINUS:
                case INTERN_RAT_MINUS:
                    symbol = "-";
                    goto finish;
                case INTERN_NAT_LESS:
                case INTERN_RAT_LESS:
                    if (_th_is_difference_logic() && _th_extract_relationship(env,e)) {
                        if (_th_diff->u.rational.numerator[0]==1 && _th_diff->u.rational.numerator[1]==0) {
                            //printf("Here1\n");
                            fprintf(f, "(< (- %s", _th_print_exp(_th_left));
                            fprintf(f, " %s) 0)", _th_print_exp(_th_right));
                        } else {
                            struct _ex_intern *d = _ex_intern_rational(
                                _th_big_copy(REWRITE_SPACE,_th_complement(_th_diff->u.rational.numerator)),
                                _th_diff->u.rational.denominator);
                            //printf("Here2\n");
                            fprintf(f, "(< (- %s", _th_print_exp(_th_left));
                            fprintf(f, " %s) ", _th_print_exp(_th_right));
                            print_formula(f,env,d);
                            fprintf(f, ")");
                        }
                        return;
                    }
                    //printf("Here3\n");
                    symbol = "<";
                    goto finish;
                case INTERN_EQUAL:
                    if (get_type(env,e->u.appl.args[0])==_ex_bool) {
                        symbol = "iff";
                    } else {
                        if (_th_is_difference_logic() && _th_extract_relationship(env,e)) {
                            //printf("Printing %s\n", _th_print_exp(e));
                            if (_th_diff->u.rational.numerator[0]==1 && _th_diff->u.rational.numerator[1]==0) {
                                fprintf(f, "(= (- %s", _th_print_exp(_th_left));
                                fprintf(f, " %s) 0)", _th_print_exp(_th_right));
                            } else {
                                fprintf(f, "(= (- %s", _th_print_exp(_th_right));
                                fprintf(f, " %s) ", _th_print_exp(_th_left));
                                print_formula(f,env,_th_diff);
                                fprintf(f, ")");
                            }
                            return;
                        }
                        symbol = "=";
                    }
                    goto finish;
                default:
                    symbol = _th_intern_decode(e->u.appl.functor);
finish:
                    fprintf(f,"(%s", symbol);
                    for (i = 0; i < e->u.appl.count; ++i) {
                        fprintf(f, " ");
                        print_formula(f,env,e->u.appl.args[i]);
                    }
                    fprintf(f,")");
            }
            break;
    }
}

static void print_as_smt(FILE *f, struct env *env, int indent, struct _ex_intern *e, int extra_right)
{
    int i;
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_AND && e->u.appl.count > 1) {
        fprintf(f,"%*s", indent, "");
        for (i = 1; i < e->u.appl.count; ++i) {
            fprintf(f,"(and ");
        }
        fprintf(f,"\n");
        for (i = 0; i < e->u.appl.count; ++i) {
            print_as_smt(f,env,indent+4,e->u.appl.args[i],i);
        }
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_OR) {
        fprintf(f,"%*s", indent, "");
        for (i = 1; i < e->u.appl.count; ++i) {
            fprintf(f,"(or ");
        }
        fprintf(f,"\n");
        for (i = 0; i < e->u.appl.count; ++i) {
            print_as_smt(f,env,indent+4,e->u.appl.args[i],i);
        }
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_XOR) {
        fprintf(f,"%*s", indent, "");
        for (i = 1; i < e->u.appl.count; ++i) {
            fprintf(f,"(xor ");
        }
        fprintf(f,"\n");
        for (i = 0; i < e->u.appl.count; ++i) {
            print_as_smt(f,env,indent+4,e->u.appl.args[i],i);
        }
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_ITE && get_type(env,e->u.appl.args[1])==_ex_bool) {
        fprintf(f,"%*s(if_then_else\n", indent, "");
        for (i = 0; i < e->u.appl.count; ++i) {
            print_as_smt(f,env,indent+4,e->u.appl.args[i], 0);
        }
        fprintf(f,"%*s)", indent, "");
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_ITE) {
        fprintf(f,"%*s(ite\n", indent, "");
        for (i = 0; i < e->u.appl.count; ++i) {
            print_as_smt(f,env,indent+4,e->u.appl.args[i], 0);
        }
        fprintf(f,"%*s)", indent, "");
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL &&
               get_type(env,e->u.appl.args[0])==_ex_bool) {
            fprintf(f,"%*s(iff\n", indent, "");
        for (i = 0; i < e->u.appl.count; ++i) {
            print_as_smt(f,env,indent+4,e->u.appl.args[i], 0);
        }
        fprintf(f,"%*s)", indent, "");
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT &&
               e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_EQUAL &&
               get_type(env,e->u.appl.args[0]->u.appl.args[0])==_ex_bool) {
        fprintf(f,"%*s(not (iff\n", indent, "");
        e = e->u.appl.args[0];
        for (i = 0; i < e->u.appl.count; ++i) {
            print_as_smt(f,env,indent+4,e->u.appl.args[i], 0);
        }
        fprintf(f,"%*s))", indent, "");
    } else if (e==_ex_true || (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT && e->u.appl.args[0]==_ex_false)) {
        fprintf(f, "%*strue", indent, "");
    } else if (e==_ex_false || (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT && e->u.appl.args[0]==_ex_true)) {
        fprintf(f, "%*sfalse", indent, "");
    } else if (e->type==EXP_VAR) {
        fprintf(f, "%*s%s", indent, "", _th_print_exp(e));
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        fprintf(f,"%*s(not\n", indent, "");
        print_as_smt(f,env,indent+4,e->u.appl.args[0], 0);
        fprintf(f,"%*s)", indent, "");
    } else {
        fprintf(f,"%*s", indent, "");
        print_formula(f,env,e);
    }
    if (extra_right) {
        fprintf(f, ")\n");
    } else {
        fprintf(f, "\n");
    }
}

static int var_count = 0;

static struct _ex_intern *get_var(int i, struct _ex_intern *type)
{
    char name[10];

    if (type==NULL) {
        struct _ex_intern *e;
        sprintf(name, "$htp_%d", i);
        e = _ex_intern_var(_th_intern(name));
        if (e->user2) return e;
        sprintf(name, "?htp_%d", i);
        return _ex_intern_var(_th_intern(name));
    } else if (type==_ex_bool) {
        sprintf(name, "$htp_%d", i);
    } else {
        sprintf(name, "?htp_%d", i);
    }
    return _ex_intern_var(_th_intern(name));
}

static void mark_duplicate_subterms(struct env *env, struct _ex_intern *e)
{
    int i;

    if (e->type==EXP_VAR || e->type==EXP_INTEGER || e->type==EXP_RATIONAL || e==_ex_true || e==_ex_false) return;

    //if (e->type==EXP_APPL && e->u.appl.functor != INTERN_NOT && e->u.appl.functor != INTERN_AND &&
    //    e->u.appl.functor != INTERN_XOR &&
    //    e->u.appl.functor != INTERN_OR && e->u.appl.functor != INTERN_ITE) return;

    if (e->type==EXP_APPL && e->user2==NULL) {
        for (i = 0; i < e->u.appl.count; ++i) {
            mark_duplicate_subterms(env,e->u.appl.args[i]);
        }
    }

    if (e->user2==_ex_true) {
        struct _ex_intern *var = get_var(var_count++, get_type(env,e));
        e->user2 = var;
        e->user1 = NULL;
        var->user2 = e;
        var->next_cache = trail;
        _th_set_var_type(env,var->u.var,_th_get_exp_type(env,e));
        trail = var;
    } else if (e->user2==NULL && (e->type != EXP_APPL || e->u.appl.functor != INTERN_RAT_PLUS)) {
        e->user2 = _ex_true;
        e->user1 = NULL;
        e->next_cache = trail;
        trail = e;
    }
}

static struct _ex_intern *int_add_subs(struct env *env, struct _ex_intern *e, struct _ex_intern *var)
{
    int i;
    struct _ex_intern **args;

    if (e->user2 && e->user2 != _ex_true && e->user2 != var) return e->user2;
    if (e->user2 && e->user1) {
        if (((int)e->user1)==2) {
            fprintf(stderr, "Illegal user1 for %s\n", _th_print_exp(e));
            fprintf(stderr, "user2 is %s\n", _th_print_exp(e->user2));
            exit(1);
        }
        return e->user1;
    }

    if (e->type==EXP_APPL) {
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = int_add_subs(env,e->u.appl.args[i],var);
        }
        if (e->user2==NULL) {
            e->next_cache = trail;
            e->user2 = _ex_true;
            e->user1 = NULL;
            trail = e;
        }
		if (i > 0) {
            return e->user1 = _ex_intern_appl_equal_env(env,e->u.appl.functor,i,args,_ex_int);
		} else {
			return e->user1 = e;
		}
    }

    return e;
}

static struct _ex_intern *add_subs(struct env *env, struct _ex_intern *e, struct _ex_intern *var)
{
    struct _ex_intern *old_trail = trail;
    struct _ex_intern *ret;

    ret = int_add_subs(env,e,var);

    while (trail != old_trail && trail) {
        struct _ex_intern *t = trail->next_cache;
        trail->user1 = NULL;
        trail->user2 = NULL;
        trail->next_cache = NULL;
        trail = t;
    }

    while (old_trail != _ex_true && old_trail != NULL) {
        old_trail->user1 = NULL;
        old_trail = old_trail->next_cache;
    }
    return ret;
}

static int int_all_vars_printed(struct _ex_intern *e, struct _ex_intern *var)
{
    int i;

    //printf("Checking term %s\n", _th_print_exp(e));
    //printf("    var %s\n", _th_print_exp(e->user2));
    //if (e->user2) printf("    var ptr %s\n", _th_print_exp(e->user2->user2));

    if (e->user2 && e->user2 != var && e->user2->type == EXP_VAR && e->user2->user2->type != EXP_VAR) return 0;

    if (e==_ex_true || e==_ex_false || e->type != EXP_APPL) return 1;

    if (e->user2 && e->user1==e) return 1;

    for (i = 0; i < e->u.appl.count; ++i) {
        if (!int_all_vars_printed(e->u.appl.args[i],var)) return 0;
    }

    if (e->user2==NULL) {
        e->next_cache = trail;
        e->user2 = _ex_true;
        trail = e;
    }

    e->user1 = e;

    return 1;
}

static int all_vars_printed(struct _ex_intern *e, struct _ex_intern *var)
{
    struct _ex_intern *old_trail = trail;
    int ret;

    ret = int_all_vars_printed(e,var);

    while (trail != old_trail && trail) {
        struct _ex_intern *t = trail->next_cache;
        trail->user1 = NULL;
        trail->user2 = NULL;
        trail->next_cache = NULL;
        trail = t;
    }

    while (old_trail && old_trail != _ex_true) {
        old_trail->user1 = NULL;
        old_trail = old_trail->next_cache;
    }
    return ret;
}

void _th_print_state(struct env *env, struct parent_list *list, struct learn_info *info, struct _ex_intern *e, FILE *f, char *name, char *status, char *logic)
{
    struct parent_list *l;
    int i;
    struct add_list *terms, *term, *nterms;
    struct _ex_intern *t;

    var_count = 0;

    //check_user2(env,"print_state1");

    fprintf(f, "(benchmark %s\n", name);
    fprintf(f, "    :source { HTP generated }\n");
    fprintf(f, "    :status %s\n", status);
    fprintf(f, "    :logic %s\n", logic);

    trail = _ex_true;
    print_types(env,f,e);
    l = list;
    while (l) {
        if (l->split) print_types(env,f,l->split);
        l = l->next;
    }
    if (info) {
        t = _th_get_first_neg_tuple(info);
        while (t) {
            print_types(env,f,t);
            t = _th_get_next_neg_tuple(info);
        }
    }
    while (trail) {
        struct _ex_intern *t = trail;
        trail = t->user2;
        t->user2 = NULL;
    }
    trail = _ex_true;

    //check_user2(env,"print_state2");
    print_functors(env,f,e);
    l = list;
    while (l) {
        if (l->split) print_functors(env,f,l->split);
        l = l->next;
    }
    if (info) {
        t = _th_get_first_neg_tuple(info);
        while (t) {
            print_functors(env,f,t);
            t = _th_get_next_neg_tuple(info);
        }
    }
    while (trail) {
        struct _ex_intern *t = trail;
        trail = t->user2;
        t->user2 = NULL;
    }
    trail = _ex_true;
    clear_functors(env,f,e);
    l = list;
    while (l) {
        if (l->split) clear_functors(env,f,l->split);
        l = l->next;
    }
    if (info) {
        t = _th_get_first_neg_tuple(info);
        while (t) {
            clear_functors(env,f,t);
            t = _th_get_next_neg_tuple(info);
        }
    }

    while (trail) {
        struct _ex_intern *t = trail;
        trail = t->user2;
        t->user2 = NULL;
    }
    trail = _ex_true;
    mark_duplicate_subterms(env,e);
    //check_user2(env,"print_state3");
    while (list) {
        if (list->split) {
            fprintf(f, "    :assumption ");
            //printf("Assumption %s\n", _th_print_exp(list->split));
            print_formula(f,env,list->split);
            fprintf(f, "\n");
        }
        list = list->next;
    }
    fprintf(f, "    :formula\n");
    terms = NULL;
    for (i = 0; i < var_count; ++i) {
        struct _ex_intern *var = get_var(i,NULL);
        if (all_vars_printed(var->user2,var)) {
            if (get_type(env,var->user2)==_ex_bool) {
                fprintf(f, "    (flet (");
            } else {
                fprintf(f, "    (let (");
            }
            print_formula(f,env,var);
            fprintf(f, " ");
            print_formula(f,env,add_subs(env,var->user2,var));
            fprintf(f, ")\n");
            var->user2 = var;
        } else {
            term = (struct add_list *)ALLOCA(sizeof(struct add_list));
            term->next = terms;
            terms = term;
            term->e = var;
        }
    }
    //check_user2(env,"print_state4");
    do {
        nterms = NULL;
        //printf("Here2a\n");
        while (terms) {
            //printf("Testing %s\n", _th_print_exp(terms->e));
            //printf("    exp %s\n", _th_print_exp(terms->e->user2));
            //printf("    exp %s\n", _th_print_exp(add_subs(env,terms->e->user2,terms->e)));
            if (all_vars_printed(terms->e->user2,terms->e)) {
                if (get_type(env,terms->e->user2)==_ex_bool) {
                    fprintf(f, "    (flet (");
                } else {
                    fprintf(f, "    (let (");
                }
                print_formula(f,env,terms->e);
                fprintf(f, " ");
                print_formula(f,env,add_subs(env,terms->e->user2,terms->e));
                fprintf(f, ")\n");
                terms->e->user2 = terms->e;
            } else {
                term = (struct add_list *)ALLOCA(sizeof(struct add_list));
                term->next = nterms;
                nterms = term;
                term->e = terms->e;
            }
            terms = terms->next;
        }
        terms = nterms;
    } while (terms);

    //check_user2(env,"print_state5");
    if (info) {
        fprintf(f, "        (and\n");
        //printf("e = %s\n", _th_print_exp(e));
        if (e != _ex_true) {
            print_as_smt(f,env,12,add_subs(env,e,NULL), 0);
        }
        t = _th_get_first_neg_tuple(info);
        if (t==NULL && e==_ex_true) {
            fprintf(f, "            true\n");
        }
        while (t) {
            //printf("t = %s\n", _th_print_exp(t));
            //printf("t->user2 = %s\n", _th_print_exp(t->user2));
            //printf("subs = %s\n", _th_print_exp(add_subs(env,t,NULL)));
            //if (t->type==EXP_APPL && t->u.appl.functor==INTERN_RAT_PLUS) {
            //    fprintf("Illegal term %s\n", _th_print_exp(t));
            //    exit(1);
            //}
            print_as_smt(f,env,12,add_subs(env,t,NULL), 0);
            t = _th_get_next_neg_tuple(info);
        }
        fprintf(f, "        )\n");
    } else {
        print_as_smt(f,env,8,add_subs(env,e,NULL), 0);
    }
    fprintf(f, "    ");
    for (i = 0; i < var_count; ++i) fprintf(f,")");
    fprintf(f, "\n");

    fprintf(f,"    )\n");
    while (trail && trail != _ex_true) {
        struct _ex_intern *t = trail;
        trail = t->next_cache;
        t->next_cache = NULL;
        //printf("Clearing %s\n", _th_print_exp(t));
        //printf("    cuser2 %s\n", _th_print_exp(t->user2));
        if (t->user2->type==EXP_VAR) {
            t->user2->user2 = NULL;
        }
        t->user2 = NULL;
    }
}
