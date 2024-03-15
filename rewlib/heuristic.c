/*
 * heuristic.c
 *
 * Routines that provide a shell for heuristic theorem proving.
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
#include "RewriteLog.h"

int _th_break_pressed = 0;

static char **heuristic_names;
static int (*hook)();

struct rule_list {
    struct rule_list *next;
    struct _ex_intern *e;
    int sign;
};

struct condition_list {
    struct condition_list *next;
    struct _ex_intern *e;
    struct rule_list *rules;
};

void setApplicationHook(int (*f)(struct env *, struct heuristic_node *, char *), char **hn)
{
    hook = f;
    heuristic_names = hn;
}

static struct _ex_intern *context_rule_set = NULL;

static struct condition_list *add_a_condition(struct condition_list *set, struct _ex_intern *e, struct _ex_intern *rule, int sign)
{
    struct condition_list *al = set;

    while (al != NULL) {
        if (al->e==e) {
            struct rule_list *r, *pr, *nr;
            pr = NULL;
            r = al->rules;
            while (r != NULL) {
                if (r->e > rule) break;
                r = r->next;
            }
            nr = (struct rule_list *)_th_alloc(HEURISTIC_SPACE,sizeof(struct rule_list));
            nr->next = r;
            nr->sign = sign;
            nr->e = rule;
            if (pr==NULL) {
                al->rules = nr;
            } else {
                pr->next = nr;
            }
            return set;
        }
        al = al->next;
    }

    al = (struct condition_list *)_th_alloc(HEURISTIC_SPACE, sizeof(struct condition_list));
    al->next = set;
    al->e = e;
    al->rules = (struct rule_list *)_th_alloc(HEURISTIC_SPACE, sizeof(struct rule_list));
    al->rules->next = NULL;
    al->rules->e = rule;

    return al;
}

static struct condition_list *add_conditions(struct condition_list *set, struct _ex_intern *e, struct _ex_intern *rule)
{
    int i;

    switch (e->type) {
        case EXP_APPL:
            switch (e->u.appl.functor) {
                case INTERN_AND:
                case INTERN_OR:
                case INTERN_NC_AND:
                    for (i = 0; i < e->u.appl.count; ++i) {
                        set = add_conditions(set, e->u.appl.args[i], rule);
                    }
                    return set;
                case INTERN_NOT:
                    return add_a_condition(set, e->u.appl.args[0], rule, -1);
                default:
                    return add_a_condition(set, e, rule, 1);
            }

        default:
            return add_a_condition(set, e, rule, 1);
    }
}

static struct _ex_unifier *match_rule(struct env *env, struct _ex_intern *rule, struct _ex_intern *exp,
                                      int (*qualify)(struct env *env, struct _ex_intern *))
{
    int i;
    struct _ex_unifier *u;
    struct match_return *m;

    //_tree_print_exp("Matching", rule);
    //_tree_print_exp("against", exp);
    if ((qualify==NULL || (*qualify)(env,exp)) &&
         (m = _th_match(env,rule->u.appl.args[0],exp))) {
        //_tree_print0("Good");
        return m->theta;
    }

    switch (exp->type) {
        case EXP_APPL:
            for (i = 0; i < exp->u.appl.count; ++i) {
                if (u = match_rule(env,rule,exp->u.appl.args[i],qualify)) {
                    return u;
                }
            }
            return 0;

        case EXP_QUANT:
            if (u = match_rule(env,rule,exp->u.quant.exp,qualify)) {
                return u;
            }
            u = match_rule(env,rule,exp->u.quant.cond,qualify);
            return u;

        default:
            return 0;
    }
}

static struct _ex_intern *_cond;
static struct _ex_unifier *applicable_rule(struct env *env, struct _ex_intern *rule, struct _ex_intern *exp, int sign, struct _ex_intern *rhs,
                                           int (*qualify)(struct env *env, struct _ex_intern *))
{
    int i;
    struct _ex_unifier *u;
    struct match_return *m;
    struct _ex_intern *r;

    _tree_print_exp("Testing applicable rule", rule);
    _tree_indent();
    _tree_print_exp("To expression", exp);

    if (rule==_ex_true || rule==_ex_false) {
        _tree_undent();
        return NULL;
    }

    if ((qualify==NULL || (*qualify)(env,exp)) &&
        (m = _th_match(env,rule->u.appl.args[0],exp))) {
        if (sign) {
            r = _th_subst(env,m->theta,rule->u.appl.args[1]);
            r = _th_rewrite(env, _ex_intern_appl2_env(env,INTERN_EQUAL,r,rhs));
            _tree_print_exp("sign test", _ex_intern_appl2_env(env,INTERN_EQUAL,r,rhs));
            if (sign > 0 && r==_ex_false) goto cont;
            if (sign < 0 && r==_ex_true) goto cont;
        }
        _cond = _th_rewrite(env,_th_subst(env,m->theta,rule->u.appl.args[2]));
        if (_cond==_ex_false) goto cont;
        _tree_print2("Match %d %s\n", sign, _th_print_exp(rhs));
        _tree_undent();
        return m->theta;
    }

cont:
    switch (exp->type) {
        case EXP_APPL:
            switch (exp->u.appl.functor) {
                case INTERN_NOT:
                    if (sign) {
                        if (rhs==_ex_true) {
                            rhs = _ex_false;
                        } else if (rhs==_ex_false) {
                            rhs = _ex_true;
                        } else {
                            sign = 0;
                            rhs = NULL;
                        }
                    }
                    u = applicable_rule(env,rule,exp->u.appl.args[0],sign,rhs,qualify);
                    _tree_undent();
                    if (u) _tree_print0("match");
                    return u;

                case INTERN_AND:
                    for (i = 0; i < exp->u.appl.count; ++i) {
                        _th_and_push(env,exp->u.appl.args,exp->u.appl.count,i);
                        r = _ex_intern_appl3_env(env,
                            rule->u.appl.functor,
                            rule->u.appl.args[0],
                            rule->u.appl.args[1],
                            _th_rewrite(env,rule->u.appl.args[2]));
                        if (u = applicable_rule(env,r,exp->u.appl.args[i], sign, rhs, qualify)) {
                            _th_derive_pop(env);
                            _tree_undent();
                            if (u) _tree_print0("match");
                            return u;
                        }
                        _th_derive_pop(env);
                    }
                    _tree_print0("No match\n");
                    _tree_undent();
                    return 0;

                case INTERN_OR:
                    for (i = 0; i < exp->u.appl.count; ++i) {
                        _th_or_push(env,exp->u.appl.args,exp->u.appl.count,i);
                        r = _ex_intern_appl3_env(env,
                            rule->u.appl.functor,
                            rule->u.appl.args[0],
                            rule->u.appl.args[1],
                            _th_rewrite(env,rule->u.appl.args[2]));
                        //printf("or applicable rule\n");
                        if (u = applicable_rule(env,r,exp->u.appl.args[i], sign, rhs, qualify)) {
                            //printf("done or applicable rule\n");
                            _th_derive_pop(env);
                            _tree_undent();
                            if (u) _tree_print0("match");
                            return u;
                        }
                        //printf("done or applicable rule\n");
                        _th_derive_pop(env);
                    }
                    _tree_print0("No match\n");
                    _tree_undent();
                    return 0;

                case INTERN_EQUAL:
#ifdef ORIG
                    if (sign > 0 && rhs==_ex_true) {
                        if (u = applicable_rule(env,rule,exp->u.appl.args[0], sign, exp->u.appl.args[1], qualify)) {
                            _tree_undent();
                            if (u) _tree_print0("match");
                            return u;
                        }
                        return applicable_rule(env,rule,exp->u.appl.args[1], sign, exp->u.appl.args[0], qualify);
                    } else if (sign > 0 && rhs==_ex_false) {
                        if (u = applicable_rule(env,rule,exp->u.appl.args[0], -1, exp->u.appl.args[1], qualify)) {
                            _tree_undent();
                            if (u) _tree_print0("match");
                            return u;
                        }
                        u = applicable_rule(env,rule,exp->u.appl.args[1], -1, exp->u.appl.args[0], qualify);
                        _tree_undent();
                        if (u) _tree_print0("match");
                        return u;
                    }
                    goto def_case;
#endif
                    u = applicable_rule(env,rule,exp->u.appl.args[0], 1, exp->u.appl.args[1], qualify);
                    if (u) {
                        _tree_undent();
                        _tree_print0("match");
                        return u;
                    }
                    u = applicable_rule(env,rule,exp->u.appl.args[1], 1, exp->u.appl.args[0], qualify);
                    if (u) {
                        _tree_undent();
                        _tree_print0("match");
                    }
                    return u;

                case INTERN_ORIENTED_RULE:
#ifdef OLD
                    if (sign > 0 && rhs==_ex_true) {
                        if (u = applicable_rule(env,rule,exp->u.appl.args[0], sign, exp->u.appl.args[1], qualify)) {
                            _tree_undent();
                            if (u) _tree_print0("match");
                            return u;
                        }
                        if (u = applicable_rule(env,rule,exp->u.appl.args[1], sign, exp->u.appl.args[0], qualify)) {
                            _tree_undent();
                            if (u) _tree_print0("match");
                            return u;
                        }
                        u = applicable_rule(env,rule,exp->u.appl.args[2], 0, NULL, qualify);
                        _tree_undent();
                        return u;

                    } else if (sign > 0 && rhs==_ex_false) {
                        if (u = applicable_rule(env,rule,exp->u.appl.args[0], -1, exp->u.appl.args[1], qualify)) {
                            _tree_undent();
                            if (u) _tree_print0("match");
                            return u;
                        }
                        if (u = applicable_rule(env,rule,exp->u.appl.args[1], -1, exp->u.appl.args[0], qualify)) {
                            _tree_undent();
                            if (u) _tree_print0("match");
                            return u;
                        }
                        if (u) _tree_print0("match");
                        u = applicable_rule(env,rule,exp->u.appl.args[2], 0, NULL, qualify);
                        _tree_undent();
                        return u;
                    }
                    goto def_case;
#endif
                    _tree_print0("oriented rule");
                    if (u = applicable_rule(env,rule,exp->u.appl.args[0], 1, exp->u.appl.args[1], qualify)) {
                        _tree_undent();
                        _tree_print0("match");
                        return u;
                    }
                    if (u = applicable_rule(env,rule,exp->u.appl.args[1], 1, exp->u.appl.args[0], qualify)) {
                        _tree_undent();
                        _tree_print0("match");
                        return u;
                    }
                    u = applicable_rule(env,rule,exp->u.appl.args[2], 0, NULL, qualify);
                    _tree_undent();
                    return u;
                default:
//def_case:
                    for (i = 0; i < exp->u.appl.count; ++i) {
                        if (u = applicable_rule(env,rule,exp->u.appl.args[i], 0, NULL, qualify)) {
                            _tree_undent();
                            if (u) _tree_print0("match");
                            return u;
                        }
                    }
            }
            _tree_print0("No match\n");
            _tree_undent();
            return 0;

        case EXP_QUANT:
            if (u = applicable_rule(env,rule,exp->u.quant.exp, 0, NULL, qualify)) {
                _tree_undent();
                if (u) _tree_print0("match");
                return u;
            }
            u = applicable_rule(env,rule,exp->u.quant.cond, 0, NULL, qualify);
            _tree_undent();
            if (u) _tree_print0("match");
            return u;

        default:
            _tree_print0("No match\n");
            _tree_undent();
            return 0;
    }
}

static int uses_only_rules(struct _ex_intern *exp, struct condition_list **rules, int count)
{
    int i;

    for (i = 0; i < count; ++i) {
        if (rules[i]->e==exp) return 1;
    }

    switch (exp->type) {
        case EXP_APPL:
            switch (exp->u.appl.functor) {
                case INTERN_NOT:
                    return uses_only_rules(exp->u.appl.args[0], rules, count);

                case INTERN_AND:
                case INTERN_OR:
                    for (i = 0; i < exp->u.appl.count; ++i) {
                        if (!uses_only_rules(exp->u.appl.args[i], rules, count)) return 0;
                    }
                    return 1;

                default:
                    return 0;
            }

        case EXP_QUANT:
            if (!uses_only_rules(exp->u.quant.exp, rules, count)) return 0;
            return uses_only_rules(exp->u.quant.cond, rules, count);

        default:
            return 0;
    }
}

static int has_subterm(struct _ex_intern *exp, struct _ex_intern *sub)
{
    int i;

    if (exp==sub) return 1;

    switch (exp->type) {
        case EXP_APPL:
            switch (exp->u.appl.functor) {
                case INTERN_NOT:
                    return has_subterm(exp->u.appl.args[0], sub);

                case INTERN_AND:
                case INTERN_OR:
                    for (i = 0; i < exp->u.appl.count; ++i) {
                        if (has_subterm(exp->u.appl.args[i], sub)) return 1;
                    }
                    return 0;

                default:
                    return 0;
            }

        case EXP_QUANT:
            if (has_subterm(exp->u.quant.exp, sub)) return 0;
            return has_subterm(exp->u.quant.cond, sub);

        default:
            return 0;
    }
}

static int is_negative_term(struct _ex_intern *exp1, struct _ex_intern *exp2)
{
    if (exp1->type==EXP_APPL && exp1->u.appl.functor==INTERN_NOT && exp1->u.appl.count==1) {
        return exp1->u.appl.args[0]==exp2;
    }
    if (exp2->type==EXP_APPL && exp2->u.appl.functor==INTERN_NOT && exp2->u.appl.count==1) {
        return exp2->u.appl.args[0]==exp1;
    }
    if (exp1->type==EXP_APPL && exp2->type==EXP_APPL && exp1->u.appl.count==exp2->u.appl.count &&
        ((exp1->u.appl.functor==INTERN_AND && exp2->u.appl.functor==INTERN_OR) ||
        (exp1->u.appl.functor==INTERN_OR && exp2->u.appl.functor==INTERN_AND))) {
        int *v = (int *)ALLOCA(sizeof(int) * exp1->u.appl.count);
        int i, j;
        for (i = 0; i < exp1->u.appl.count; ++i) {
            v[i] = 0;
        }
        for (i = 0; i < exp1->u.appl.count; ++i) {
            int has_neg = 0;
            for (j = 0; j < exp1->u.appl.count; ++j) {
                if (v[j]==0 && is_negative_term(exp1->u.appl.args[i],exp2->u.appl.args[j])) {
                    v[j] = 1;
                    has_neg = 1;
                }
            }
            if (!has_neg) return 0;
        }
        for (i = 0; i < exp1->u.appl.count; ++i) {
            if (!v[i]) return 0;
        }
        return 1;
    }
    return 0;
}

static int has_negative_subterm(struct _ex_intern *exp, struct _ex_intern *sub)
{
    int i;

    if (is_negative_term(exp,sub)) return 1;

    switch (exp->type) {
        case EXP_APPL:
            switch (exp->u.appl.functor) {
                case INTERN_NOT:
                    return has_negative_subterm(exp->u.appl.args[0], sub);

                case INTERN_AND:
                case INTERN_OR:
                    for (i = 0; i < exp->u.appl.count; ++i) {
                        if (has_negative_subterm(exp->u.appl.args[i], sub)) return 1;
                    }
                    return 0;

                default:
                    return 0;
            }

        case EXP_QUANT:
            if (has_negative_subterm(exp->u.quant.exp, sub)) return 0;
            return has_negative_subterm(exp->u.quant.cond, sub);

        default:
            return 0;
    }
}

static struct _ex_intern *inclusive_subterm(struct _ex_intern *exp, struct _ex_intern *cond, struct condition_list **rules, int count)
{
    int i;
    struct _ex_intern *r;

    if ((cond->type != EXP_APPL || 
         cond->u.appl.count != 1 ||
         cond->u.appl.functor != INTERN_NOT) &&
        uses_only_rules(cond, rules, count) && has_subterm(cond, exp)) return cond;

    switch (cond->type) {
        case EXP_APPL:
            switch (cond->u.appl.functor) {
                case INTERN_NOT:
                    return inclusive_subterm(exp, cond->u.appl.args[0], rules, count);

                case INTERN_AND:
                case INTERN_OR:
                    for (i = 0; i < cond->u.appl.count; ++i) {
                        r = inclusive_subterm(exp,cond->u.appl.args[i], rules, count);
                        if (r!=exp) return r;
                    }
                    return exp;

                default:
                    return exp;
            }

        case EXP_QUANT:
            if (inclusive_subterm(exp, cond->u.quant.exp, rules, count)) return exp;
            return inclusive_subterm(exp, cond->u.quant.cond, rules, count);

        default:
            return 0;
    }
}

static struct _ex_intern *reduce_subterm(struct env *env, struct _ex_intern *exp, struct _ex_intern *cond, struct _ex_intern *term)
{
    int i;

    if (has_subterm(cond, term)) return term;
    if (has_negative_subterm(cond, term)) return term;

    switch (term->type) {
        case EXP_APPL:
            switch (term->u.appl.functor) {
                case INTERN_NOT:
                    return reduce_subterm(env, exp, cond, term->u.appl.args[0]);

                case INTERN_AND:
                case INTERN_OR:
                    if (cond->u.appl.functor==term->u.appl.functor) {
                        int j, k, hst;
                        struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * term->u.appl.count);
                        k = 0; hst = 0;
                        for (i = 0; i < term->u.appl.count; ++i) {
                            for (j = 0; j < cond->u.appl.count; ++j) {
                                if (cond->u.appl.args[j]==term->u.appl.args[i]) goto good;
                            }
                            continue;
good:
                            hst = (hst || has_subterm(term->u.appl.args[i], exp));
                            args[k++] = term->u.appl.args[i];
                        }
                        if (hst && k > 1) {
                            return _ex_intern_appl_env(env,cond->u.appl.functor,k,args);
                        }
                    } else {
                        int j, k, hst;
                        struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * term->u.appl.count);
                        k = 0; hst = 0;
                        for (i = 0; i < term->u.appl.count; ++i) {
                            for (j = 0; j < cond->u.appl.count; ++j) {
                                if (is_negative_term(cond->u.appl.args[j],term->u.appl.args[i])) goto good2;
                            }
                            continue;
good2:
                            hst = (hst || has_negative_subterm(term->u.appl.args[i], exp));
                            args[k++] = term->u.appl.args[i];
                        }
                        if (hst && k > 1) {
                            return _ex_intern_appl_env(env,term->u.appl.functor,k,args);
                        }
                    }
                    for (i = 0; i < cond->u.appl.count; ++i) {
                        if (has_subterm(term->u.appl.args[i], exp)) {
                           return reduce_subterm(env, exp, cond, term->u.appl.args[i]);
                        }
                    }
                    return exp;

                default:
                    return exp;
            }

        default:
            return exp;
    }
}

static int is_identical_set(struct condition_list *exp,
                            struct condition_list *sub)
{
    struct rule_list *re, *rs;

    re = exp->rules;
    rs = sub->rules;

    while (re != NULL && rs != NULL) {
        if (re->e != rs->e) return 0;
        re = re->next;
        rs = rs->next;
    }
    if (re || rs) return 0;
    return 1;
}

static struct _ex_intern *get_complete_term(struct env *env, struct condition_list *cond, struct condition_list *all)
{
    struct condition_list **rules;
    int count;
    struct condition_list *c;
    struct rule_list *r;
    struct _ex_intern *e, *t;

    _tree_print_exp("Entering get complete_term", cond->e);

    c = all;
    count = 0;
    while (c != NULL) {
        ++count;
        c = c->next;
    }

    rules = (struct condition_list **)ALLOCA(sizeof(struct condition_list *) * count);

    count = 0;
    c = all;
    while (c != NULL) {
        if (c == cond || is_identical_set(c, cond)) {
            _tree_print_exp("    Other term", c->e);
            rules[count++] = c;
        }
        c = c->next;
    }
    _tree_print1("Count = %d\n", count);
    if (count==1) return cond->e;

    r = cond->rules;

    e = _th_rewrite(env,r->e->u.appl.args[1]);
    _tree_print_exp("e", e);
    t = inclusive_subterm(cond->e, e, rules, count);
    _tree_print_exp("Inclusive subterm", t);
    if (t==cond->e) return cond->e;

    r = r->next;

    while (r != NULL) {
        e = _th_rewrite(env,r->e->u.appl.args[1]);
        _tree_print_exp("Reducing with", e);
        t = reduce_subterm(env, cond->e, e, t);
        _tree_print_exp("    reduced to", t);
        if (t==cond->e) return t;
        r = r->next;
    }

    return t;
}

static int is_instantiated(struct env *env, struct _ex_intern *cond, struct heuristic_node *node)
{
    while (node != NULL) {
        if (cond==node->assumption ||
            (node->assumption->type==EXP_APPL && node->assumption->u.appl.functor==INTERN_NOT &&
             node->assumption->u.appl.count==1 && cond==node->assumption->u.appl.args[0])) return 1;
        node = node->parent;
    }
    return 0;
}

static int instantiated_condition_count(struct env *env, struct _ex_intern *cond, struct heuristic_node *node)
{
    int i;
    int count = 0;

    switch (cond->type) {
        case EXP_APPL:
            switch (cond->u.appl.functor) {
                case INTERN_AND:
                case INTERN_OR:
                    for (i = 0; i < cond->u.appl.count; ++i) {
                        count += is_instantiated(env, cond->u.appl.args[i], node);
                    }
                    return count;
                case INTERN_NOT:
                    return is_instantiated(env, cond->u.appl.args[0], node);
                default:
                    return is_instantiated(env, cond, node);
            }

        default:
            return is_instantiated(env, cond, node);
    }
}

static int is_false(struct env *env, struct _ex_intern *cond, struct heuristic_node *node)
{
    int i;

    /**********/

    //_tree_print_exp("testing is_false", cond);

    if (cond->type==EXP_APPL) {
        switch (cond->u.appl.functor) {
            case INTERN_AND:
                for (i = 0; i < cond->u.appl.count; ++i) {
                    if (is_false(env, cond->u.appl.args[i], node)) return 1;
                }
                return 0;

            case INTERN_OR:
                for (i = 0; i < cond->u.appl.count; ++i) {
                    if (!is_false(env, cond->u.appl.args[i], node)) return 0;
                }
                return 1;

            case INTERN_NOT:
                while (node) {
                    if (node->assumption==cond->u.appl.args[0]) return 1;
                    node = node->parent;
                }
                return 0;
        }
    }
    while (node) {
        //_tree_print_exp("assumption", node->assumption);
        if (node->assumption->type==EXP_APPL &&
            node->assumption->u.appl.functor==INTERN_NOT) {
            if (node->assumption->u.appl.args[0]==cond) return 1;
        }
        node = node->parent;
    }
    return 0;
}

void _th_build_context(struct env *env, struct _ex_intern *exp)
{
    if (exp->type != EXP_APPL || exp->u.appl.functor != INTERN_OR) {
        _th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,_ex_intern_appl1_env(env,INTERN_NOT,exp))));
    } else {
        int i;
        for (i = 0; i < exp->u.appl.count; ++i) {
            _th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,_ex_intern_appl1_env(env,INTERN_NOT,exp->u.appl.args[i]))));
        }
    }
}

struct _ex_intern *_th_generate_universal(struct env *env, struct _ex_intern *property,
                                          int (*qualify)(struct env *, struct _ex_intern *),
                                          int (*weight)(struct env *, struct _ex_intern *))
{
    int i;
    struct condition_list *conditions = NULL;
    struct condition_list *c, *cond;
    struct rule_list *rules;
    int count, max_count;
    struct _ex_unifier *u;
    char *mark1, *mark2, *mark3, *mark4;
    struct _ex_intern *e;

    //printf("Entering generate universal\n");
    //fflush(stdout);

    mark1 = _th_alloc_mark(MATCH_SPACE);
    mark2 = _th_alloc_mark(ENVIRONMENT_SPACE);
    mark3 = _th_alloc_mark(HEURISTIC_SPACE);
    mark4 = _th_alloc_mark(REWRITE_SPACE);

    context_rule_set = _th_get_context_rule_set(env);

    _th_do_context_rewrites = 0;

    //_tree_print0("Rewrites");
    _tree_indent();
    for (i = 0; i < context_rule_set->u.appl.count; ++i) {
        //printf("Before applicable rule %s\n", _th_print_exp(context_rule_set->u.appl.args[i]));
        //fflush(stdout);
        //_tree_print_exp("Testing rule", context_rule_set->u.appl.args[i]);
        //_tree_indent();
        if ((context_rule_set->u.appl.args[i]->u.appl.functor==INTERN_ORIENTED_RULE ||
             context_rule_set->u.appl.args[i]->u.appl.functor==INTERN_FORCE_ORIENTED) &&
             match_rule(env,context_rule_set->u.appl.args[i], property, qualify) &&
             (u = applicable_rule(env, context_rule_set->u.appl.args[i], property, 1, _ex_true, qualify))) {
            //struct _ex_intern *res = _cond;
            //_tree_start = 0; _tree_end = 20000000;
            //_tree_sub = _tree_sub2 = -1;
            //_tree_mute = 0;
            //res = _th_rewrite(env, _th_subst(env,u,_cond));
            //_tree_mute = 1;
            //_tree_print_exp("cond", _th_subst(env,u,_cond));
            _tree_print_exp("_cond =", _cond);
            if (_cond != _ex_true && _cond != _ex_false) {
                conditions = add_conditions(conditions, _cond,
                    _ex_intern_appl2_env(env,INTERN_TUPLE,
                        context_rule_set->u.appl.args[i],
                        _cond));
            }
        //} else {
        //    printf("After applicable rule\n");
        //    fflush(stdout);
        }
        //_tree_undent();
    }
    _tree_undent();

    _th_do_context_rewrites = 1;

    c = conditions;
    max_count = -1;
    cond = NULL;
    _tree_print0("Applicable rule tabulations");
    _tree_indent();
    while (c != NULL) {
        count = 0;
        rules = c->rules;
        _tree_print_exp("term", c->e);
        _tree_indent();
        while (rules != NULL) {
            if (weight) {
                count += (*weight)(env,rules->e);
            } else {
                ++count;
            }
            _tree_print_exp("rule", rules->e);
            rules = rules->next;
        }
        _tree_undent();
        _tree_print1("count = %d", count);
        if (count > max_count) {
            cond = c;
            max_count = count;
        }
        c = c->next;
    }
    _tree_undent();

    //printf("Exiting generate universal\n");
    //fflush(stdout);

    if (cond != NULL) {
        _tree_print0("From rules");
        _tree_indent();
        rules = cond->rules;
        while (rules != NULL) {
            _tree_print_exp("", rules->e);
            rules = rules->next;
        }
        _tree_undent();
        e = get_complete_term(env, cond, conditions);
        //e = cond->e;
    } else {
        e = NULL;
    }

    _th_alloc_release(MATCH_SPACE, mark1);
    _th_alloc_release(ENVIRONMENT_SPACE, mark2);
    _th_alloc_release(HEURISTIC_SPACE, mark3);
    _th_alloc_release(REWRITE_SPACE, mark4);

    return e;
}

static int bound;
static unsigned var;
static int is_bound(struct _ex_intern *e)
{
    int res;
    _tree_print_exp("Testing is_bound", e);
    if (e->type != EXP_APPL) return 0;
    switch (e->u.appl.functor) {

        case INTERN_NOT:
            res = is_bound(e->u.appl.args[0]);
            if (res > 0) {
                ++bound;
                return -1;
            } else if (res < 0) {
                --bound;
                return 1;
            }
            return 0;

        case INTERN_NAT_LESS:
            if (e->u.appl.args[0]->type==EXP_INTEGER && e->u.appl.args[1]->type==EXP_VAR) {
                if (e->u.appl.args[0]->u.integer[0] != 1) return 0;
                var = e->u.appl.args[1]->u.var;
                bound = e->u.appl.args[0]->u.integer[1];
                ++bound;
                _tree_print1("Low bound %d", bound);
                return -1;
            } else if (e->u.appl.args[1]->type==EXP_INTEGER && e->u.appl.args[0]->type==EXP_VAR) {
                if (e->u.appl.args[1]->u.integer[0] != 1) return 0;
                var = e->u.appl.args[0]->u.var;
                bound = e->u.appl.args[1]->u.integer[1];
                --bound;
                _tree_print1("High bound %d", bound);
                return 1;
            }
            return 0;
    }
    return 0;
}

int _th_max_expand = 16;

static struct _ex_intern *split_exists(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *exp;
    int i, j, k, l;
    int dir1, bound1, dir2, bound2;
    unsigned var1;
    struct _ex_intern **args1, **args2, **args1b;

    /**********/

    if (e->type != EXP_QUANT) return NULL;
    if (e->u.quant.quant!=INTERN_EXISTS) return NULL;
    if (e->u.quant.exp->type != EXP_APPL || e->u.quant.exp->u.appl.functor!=INTERN_AND) {
        return NULL;
    }

    exp = e->u.quant.exp;
    for (i = 0; i < exp->u.appl.count; ++i) {
        if (dir1 = is_bound(exp->u.appl.args[i])) {
            for (j = 0; j < exp->u.quant.var_count; ++j) {
                if (var==e->u.quant.vars[j]) goto cont;
            }
            return NULL;
        }
    }
    return NULL;
cont:
    var1 = var;
    bound1 = bound;

    for (j = i+1; j < exp->u.appl.count; ++j) {
        if ((dir2 = is_bound(exp->u.appl.args[j])) && var==var1 && dir2 != dir1) {
            goto cont2;
        }
    }
    return NULL;
cont2:
    bound2 = bound;
    if (dir1 > 0) {
        k = bound1;
        bound1 = bound2;
        bound2 = k;
    }
    if (bound2 - bound1 + 1 > _th_max_expand) return NULL;

    args1 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (exp->u.appl.count+1));
    args1b = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (exp->u.appl.count+1));
    for (k = 0, l = 0; k < exp->u.appl.count; ++k) {
        if (k != i && k != j) {
            args1[l++] = exp->u.appl.args[k];
        }
    }
    args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (bound2 - bound1 + 1));
    _tree_print2("Bounds %d %d", bound1, bound2);
    for (k = bound1; k <= bound2; ++k) {
        int m;
        args1[l] = _ex_intern_appl2_env(env,INTERN_EQUAL,_ex_intern_var(var),_ex_intern_small_integer(k));
        for (m = 0; m <= l; ++m) args1b[m] = args1[m];
        args2[k-bound1] = _ex_intern_quant(INTERN_EXISTS,e->u.quant.var_count,e->u.quant.vars,
            _ex_intern_appl_env(env,INTERN_AND,l+1,args1b),_ex_true);
    }
    return _ex_intern_appl_env(env,INTERN_OR,bound2-bound1+1,args2);
}

struct _ex_intern *find_and_split_exists(struct env *env, struct _ex_intern *e)
{
    int i;
    struct _ex_intern *exp;
    exp = split_exists(env, e);
    if (exp) return exp;

    switch (e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                exp = find_and_split_exists(env, e->u.appl.args[i]);
                if (exp) {
                    int j;
                    struct _ex_intern **args;
                    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
                    for (j = 0; j < e->u.appl.count; ++j) {
                        if (j==i) {
                            args[j] = exp;
                        } else {
                            args[j] = e->u.appl.args[j];
                        }
                    }
                    return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
                }
            }
            return 0;

        default:
            return 0;
    }
}

struct heuristic_node *_th_new_node(struct heuristic_node *parent)
{
     struct heuristic_node *n = (struct heuristic_node *)_th_alloc(HEURISTIC_SPACE,sizeof(struct heuristic_node));

     if (parent==NULL) {
         memset(n,0,sizeof(struct heuristic_node));
     } else {
         memcpy(n,parent,sizeof(struct heuristic_node));
         if (parent->first_child==NULL) {
             parent->first_child = n;
         } else {
             struct heuristic_node *c = n->first_child;
             while (c->next) {
                 c = c->next;
             }
             c->next = n;
         }
     }
     n->parent = parent;
     n->first_child = n->next = NULL;
     n->heuristic = NULL;

     return n;
}

int _th_global_heuristics(int do_universal, struct env *env, struct heuristic_node *node, char *heuristic)
{
    struct _ex_intern *e;

    if (!do_universal) {
        e = find_and_split_exists(env, node->property);
        if (e) {
            struct heuristic_node *n = _th_new_node(node);
            _tree_print0("split exists");
            e = _th_flatten(env,e);
            node->first_child = n;
            n->property = e;
            n->assumption = _ex_true;
            node->heuristic = "SPLIT_EXISTS";
            return 1;
        }
    }

    if (do_universal) {
        _ex_push();
        e = _th_generate_universal(env, node->property, NULL, NULL);
        _th_clear_cache();
        _th_transitive_reset();
        _ex_pop();
        if (e != NULL) e = _ex_reintern(env, e);
        _th_reintern_cache(env);
        _ex_release();
        if (e) {
            struct heuristic_node *base_case, *not_case;
            _tree_print0("universal");
            base_case = _th_new_node(node);
            not_case = _th_new_node(node);
            //base_case->assumption = _th_mark_vars(env, _th_rewrite(env, e));
            base_case->assumption = e;
            base_case->property = _th_flatten(env,_ex_intern_appl2_env(env,INTERN_OR,_ex_intern_appl1_env(env,INTERN_NOT,e),node->property));;
            //not_case->assumption = _th_mark_vars(env, _th_rewrite(env, _ex_intern_appl1_env(env,INTERN_NOT,e)));
            not_case->assumption = _ex_intern_appl1_env(env,INTERN_NOT,e);
            not_case->property = _th_flatten(env,_ex_intern_appl2_env(env,INTERN_OR,node->property,e));
            node->heuristic = "universal";
            return 1;
        }
    }

    return 0;
}

int is_finished(struct heuristic_node *node)
{
    if (node==NULL) return 0;
    if (node->property == _ex_true) return 1;
    if (node->first_child) {
        struct heuristic_node *c = node->first_child;
        while (c != NULL) {
            if (!is_finished(c)) return 0;
            c = c->next;
        }
        return 1;
    }
    return 0;
}

static int heuristic_indent = 0;
static int heuristic_count;

struct heuristic_node *heuristic_solve_int(struct env *env, struct heuristic_node *node)
{
    int i;
    char *mark;
    if (_th_break_pressed || heuristic_indent > 6000 || heuristic_count > 40000) return NULL;

    node->before_property = node->property;
    _tree_print_exp("Solving", node->property);
    //_tree_start = 0; _tree_end = 20000000;
    //_tree_sub = _tree_sub2 = -1;
    //_tree_mute = 0;
    mark = _th_alloc_mark(REWRITE_SPACE);
    _ex_push();
    node->property = _th_rewrite(env, node->property);
    _th_clear_cache();
    _th_transitive_reset();
    _ex_pop();
    if (node->property != NULL) node->property = _ex_reintern(env, node->property);
    _th_reintern_cache(env);
    _ex_release();
    _th_alloc_release(REWRITE_SPACE,mark);
    //_tree_mute = 1;
    _tree_print_exp("After rewrite", node->property);
    if (node->property==_ex_true || node->property==_ex_false) {
        printf("Info: %6d ", ++heuristic_count);
        for (i = 0; i < heuristic_indent; ++i) printf(" ");
        printf("leaf\n");
        if (node->property==_ex_true) {
            _tree_print0("Good");
        } else {
            struct heuristic_node *n;
            _tree_print0("Bad");
            printf("Warning: failed node,  Back trace is as follows:\n");
            n = node;
            while (n != NULL) {
                printf("Warning:     To prove %s\n", _th_pp_print(env,INTERN_DEFAULT,2000,n->before_property));
                if (n->parent) {
                    printf("Warning:         when %s from %s\n", _th_pp_print(env,INTERN_DEFAULT,2000,n->assumption),
                        n->parent->heuristic);
                } else {
                    printf("Warning:         when %s from root\n", _th_pp_print(env,INTERN_DEFAULT,2000,n->assumption));
                }
                n = n->parent;
            }
        }
        return node;
    }

    i = 0;
    if (hook != NULL) {
        i = (*hook)(env, node, NULL);
    } else {
        _th_global_heuristics(0, env, node, NULL);
        if (!node->first_child) _th_global_heuristics(1, env, node, NULL);
    }

    if (node->first_child) {
        struct heuristic_node *c = node->first_child;
        printf("Info: %6d ", ++heuristic_count);
        for (i = 0; i < heuristic_indent; ++i) printf(" ");
        if (strlen(node->heuristic) >= 9 && !strcmp(node->heuristic+strlen(node->heuristic)-9, "universal")) {
            _tree_print_exp("", node->first_child->assumption);
            printf("Applied heuristic %s %s\n", node->heuristic, _th_pp_print(env,INTERN_DEFAULT,2000,c->assumption));
        } else {
            printf("Applied heuristic %s\n", node->heuristic);
        }
        printf("Info: %6d ", heuristic_count);
        for (i = 0; i < heuristic_indent; ++i) printf(" ");
        printf("To: %s\n", _th_pp_print(env,INTERN_DEFAULT,2000,node->before_property));
        printf("Info: %6d ", heuristic_count);
        for (i = 0; i < heuristic_indent; ++i) printf(" ");
        printf("Rewrite: %s\n", _th_pp_print(env,INTERN_DEFAULT,2000,node->property));
        heuristic_indent += 2;
        while (c != NULL) {
            _tree_print0("Child");
            _tree_indent();
            _tree_print_exp("To prove", c->property);
            _tree_print_exp("Assuming", c->assumption);

            //_th_log_derive_push(env) ;
            //if (c->assumption->type==EXP_APPL && c->assumption->u.appl.functor==INTERN_AND) {
            //    int i;
            //    for (i = 0; i < c->assumption->u.appl.count; ++i) {
            //        _th_log_derive_and_add(env, _th_derive_simplify(env,c->assumption->u.appl.args[i]));
            //    }
            //} else {
            //    _th_log_derive_and_add(env, _th_derive_simplify(env,c->assumption));
            //}
            if (!heuristic_solve_int(env, c)) return NULL;
            //_th_log_derive_pop(env);
            _tree_undent();
            c = c->next;
        }
        heuristic_indent -= 2;
    } else {
        printf("Info: %6d ", ++heuristic_count);
        for (i = 0; i < heuristic_indent; ++i) printf(" ");
        printf("leaf");
        if (node->property==_ex_true) {
            printf("\n");
        } else {
            struct heuristic_node *n;
            printf(" %s\n", _th_pp_print(env,INTERN_DEFAULT,2000,node->property));
            printf("Warning: failed node,  Back trace is as follows:\n");
            n = node;
            while (n != NULL) {
                printf("Warning:     To prove %s\n", _th_pp_print(env,INTERN_DEFAULT,2000,n->before_property));
                if (n->parent) {
                    printf("Warning:         when %s from %s\n", _th_pp_print(env,INTERN_DEFAULT,2000,n->assumption),
                        n->parent->heuristic);
                } else {
                    printf("Warning:         when %s from root\n", _th_pp_print(env,INTERN_DEFAULT,2000,n->assumption));
                }
                n = n->parent;
            }
        }
        
    }

    if (is_finished(node)) {
        _tree_print0("Good");
    } else {
        _tree_print0("Bad");
    }

    return node;
}

struct heuristic_node *heuristic_solve(struct env *env, struct _ex_intern *exp)
{
    struct heuristic_node *node = _th_new_node(NULL);

    _th_break_pressed = 0;

    heuristic_count = 0;

    //_tree_start = 0;
    //_tree_end = 40000;
    //_tree_sub = _tree_sub2 = -1;
    //_tree_mute = 0;

    node->property = exp;
    node->assumption = _ex_true;

    _tree_print1("Heuristic solve of %s", _th_pp_print(env,INTERN_DEFAULT,2000,node->property));
    _tree_indent();
    node = heuristic_solve_int(env, node);
    _tree_undent();
    if (_th_break_pressed) {
        printf("Error: break\n");
    }
    return node;
}

struct heuristic_node *apply_heuristic(struct env *env, struct _ex_intern *exp, char *heuristic)
{
    return NULL;
}
