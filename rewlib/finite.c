/*
 * finite.c
 *
 * Routines for simplifying expressions that involve an integer with a small
 * number of possible values
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"

static struct _ex_intern *coefficient;
static struct _ex_intern *get_coefficient(struct env *env, struct _ex_intern *e)
{
    _zone_print_exp("Get coefficient %s", e);
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NAT_TIMES) {
        int i;
        _zone_print0("case 1");
        for (i = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type==EXP_INTEGER) {
                struct _ex_intern **args;
                int j, k;
                coefficient = e->u.appl.args[i];
                args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
                for (j = 0, k = 0; j < e->u.appl.count; ++j) {
                    if (i != j) args[k++] = e->u.appl.args[j];
                }
                if (k==1) {
                    return args[0];
                } else {
                    return _ex_intern_appl_env(env,INTERN_NAT_TIMES,k,args);
                }
            }
        }
        coefficient = _ex_intern_small_integer(1);
        return e;
    } else if (e->type==EXP_INTEGER) {
        _zone_print0("case 2");
        coefficient = e;
        return _ex_intern_small_integer(1);
    } else {
        _zone_print0("case 3");
        coefficient = _ex_intern_small_integer(1);
        return e;
    }
}

static int equation_count(struct _ex_intern *e)
{
    int count = 0;

    if (e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_NAT_PLUS) {
        count += e->u.appl.args[0]->u.appl.count;
    } else {
        ++count;
    }

    if (e->u.appl.args[1]->type==EXP_APPL && e->u.appl.args[1]->u.appl.functor==INTERN_NAT_PLUS) {
        count += e->u.appl.args[1]->u.appl.count;
    } else {
        ++count;
    }

    return count;
}

static void create_canonical_equation(struct env *env, struct _ex_intern *e, struct _ex_intern **coefficients, struct _ex_intern **terms)
{
    int pos = 0;
    int i, j;
    struct _ex_intern *f;
    unsigned *g;

    if (e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_NAT_PLUS) {
        for (i = 0; i < e->u.appl.args[0]->u.appl.count; ++i) {
            terms[pos] = get_coefficient(env,e->u.appl.args[0]->u.appl.args[i]);
            //_zone_print1("pos %d", pos);
            //_zone_print1("term %s", _th_print_exp(terms[pos]));
            //_zone_print1("coefficient %s", _th_print_exp(coefficient));
            coefficients[pos++] = coefficient;
        }
    } else {
        _zone_print0("here3");
        terms[pos] = get_coefficient(env,e->u.appl.args[0]);
        //_zone_print1("pos %d", pos);
        //_zone_print1("term %s", _th_print_exp(terms[pos]));
        //_zone_print1("coefficient %s", _th_print_exp(coefficient));
        coefficients[pos++] = coefficient;
    }

    if (e->u.appl.args[1]->type==EXP_APPL && e->u.appl.args[1]->u.appl.functor==INTERN_NAT_PLUS) {
        _zone_print0("Here4");
        for (i = 0; i < e->u.appl.args[1]->u.appl.count; ++i) {
            terms[pos] = get_coefficient(env,e->u.appl.args[1]->u.appl.args[i]);
            //_zone_print1("pos %d", pos);
            //_zone_print1("term %s", _th_print_exp(terms[pos]));
            //_zone_print1("coefficient %s", _th_print_exp(coefficient));
            coefficients[pos++] = _ex_intern_integer(_th_complement(coefficient->u.integer));
        }
    } else {
        _zone_print0("Here5");
        terms[pos] = get_coefficient(env,e->u.appl.args[1]);
        //_zone_print1("pos %d", pos);
        //_zone_print1("term %s", _th_print_exp(terms[pos]));
        //_zone_print1("coefficient %s", _th_print_exp(coefficient));
        coefficients[pos++] = _ex_intern_integer(_th_complement(coefficient->u.integer));
    }

    for (i = 0; i < pos-1; ++i) {
        for (j = 0; j < pos-1; ++j) {
            if (terms[j] > terms[j+1]) {
                f = terms[j];
                terms[j] = terms[j+1];
                terms[j+1] = f;
                f = coefficients[j];
                coefficients[j] = coefficients[j+1];
                coefficients[j+1] = f;
            }
        }
    }

    g = coefficients[0]->u.integer;
    //_zone_print2("a g[0], g[1] = %d %d", g[0], g[1]);
    if (_th_big_is_negative(g)) {
        g = _th_big_copy(REWRITE_SPACE,_th_complement(g));
    }
    for (i = 1; i < pos; ++i) {
        if (_th_big_is_negative(coefficients[i]->u.integer)) {
            g = _th_big_copy(REWRITE_SPACE,_th_big_gcd(g,_th_big_copy(REWRITE_SPACE,_th_complement(coefficients[i]->u.integer))));
		} else {
            g = _th_big_copy(REWRITE_SPACE,_th_big_gcd(g,coefficients[i]->u.integer));
        }
        //_zone_print2("b coefficients[0], coefficients[1] = %d %d", coefficients[i]->u.integer[0], coefficients[i]->u.integer[1]);
        //_zone_print2("b g[0], g[1] = %d %d", g[0], g[1]);
    }

    //_zone_print2("g[0], g[1] = %d %d", g[0], g[1]);
    for (i = 0; i < pos; ++i) {
        coefficients[i] = _ex_intern_integer(_th_big_divide(coefficients[i]->u.integer,g));
        //_zone_print1("r coef %s", _th_print_exp(coefficients[i]));
        //_zone_print1("r term %s", _th_print_exp(terms[i]));
    }
}

static int compatible_equations(int count1, struct _ex_intern **coefficients1, struct _ex_intern **terms1, int count2, struct _ex_intern **coefficients2, struct _ex_intern **terms2)
{
    int pos1, pos2;

    pos1 = pos2 = 0;
    while (pos1 < count1 && pos2 < count2) {
        if (terms1[pos1]->type==EXP_INTEGER) {
            ++pos1;
        } else if (terms2[pos2]->type==EXP_INTEGER) {
            ++pos2;
        } else {
            if (coefficients1[pos1] != coefficients2[pos2] ||
                terms1[pos1] != terms2[pos2]) return 0;
            ++pos1;
            ++pos2;
        }
    }
    return 1;
}

struct equation_record {
    struct equation_record *next;
    int type;
    int count;
    struct _ex_intern **coefficients;
    struct _ex_intern **terms;
};

static struct equation_record *make_equation_record(struct env *env, struct _ex_intern *e)
{
    struct equation_record *r = (struct equation_record *)_th_alloc(REWRITE_SPACE,sizeof(struct equation_record));
    int i;
    unsigned one[2];

    _zone_print_exp("Making equation record for", e);
    _tree_indent();

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        e = e->u.appl.args[0];
        if (e->type != EXP_APPL || e->u.appl.functor != INTERN_NAT_LESS) {
			_tree_undent();
			return NULL;
		}
        r->type = INTERN_NOT;
    } else if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_EQUAL || e->u.appl.functor==INTERN_NAT_LESS)) {
        r->type = e->u.appl.functor;
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_ORIENTED_RULE) {
        r->type = INTERN_EQUAL;
    } else {
        _tree_undent();
        return NULL;
    }

    r->count = equation_count(e);
    //_zone_print1("count = %d", r->count);
    r->coefficients = (struct _ex_intern **)_th_alloc(REWRITE_SPACE,sizeof(struct _ex_intern *) * r->count);
    r->terms = (struct _ex_intern **)_th_alloc(REWRITE_SPACE,sizeof(struct _ex_intern *) * r->count);
    create_canonical_equation(env,e,r->coefficients,r->terms);

    i = 0;
    if (r->terms[0]->type==EXP_INTEGER) ++i;
    //_zone_print1("i = %d", i);
    //_zone_print1("negative = %d", _th_big_is_negative(r->coefficients[i]->u.integer));
    //_zone_print2("coefficient %x %x", r->coefficients[i]->u.integer[0], r->coefficients[i]->u.integer[1]);
    if (_th_big_is_negative(r->coefficients[i]->u.integer)) {
        for (i = 0; i < r->count; ++i) {
            r->coefficients[i] = _ex_intern_integer(_th_complement(r->coefficients[i]->u.integer));
        }
        if (r->type==INTERN_NAT_LESS) {
            one[0] = 1;
            one[1] = 1;
            r->type = INTERN_NOT;
            for (i = 0; i < r->count; ++i) {
                if (r->terms[i]->type==EXP_INTEGER) {
                    r->coefficients[i] = _ex_intern_integer(_th_big_add(r->coefficients[i]->u.integer,one));
                }
            }
        } else if (r->type==INTERN_NOT) {
            one[0] = 1;
            one[1] = 1;
            r->type = INTERN_NAT_LESS;
            for (i = 0; i < r->count; ++i) {
                if (r->terms[i]->type==EXP_INTEGER) {
                    r->coefficients[i] = _ex_intern_integer(_th_big_sub(r->coefficients[i]->u.integer,one));
                }
            }
        }
    }

    r->next = NULL;

#ifndef FAST
    if (_zone_active()) {
        _zone_print1("type = %d", r->type);
        for (i = 0; i < r->count; ++i) {
            _zone_print_exp("coef", r->coefficients[i]);
            _zone_print_exp("term", r->terms[i]);
        }
    }
#endif

    _tree_undent();
    return r;
}

struct _ex_intern *get_offset(struct equation_record *r)
{
    int i;

    for (i = 0; i < r->count; ++i) {
        if (r->terms[i]->type==EXP_INTEGER) return r->coefficients[i];
    }

    return _ex_intern_small_integer(0);
}

static struct _ex_intern *make_not(struct env *env, struct equation_record *r, struct _ex_intern *offset)
{
    struct _ex_intern **args;
    int pos, i;

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (r->count+1));
    for (pos = 0, i = 0; i < r->count; ++i) {
        if (r->terms[i]->type != EXP_INTEGER) {
            args[pos++] = _ex_intern_appl2_env(env,INTERN_NAT_TIMES,r->terms[i],r->coefficients[i]);
        }
    }
    args[pos++] = offset;

    return _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_EQUAL,_ex_intern_appl_env(env,INTERN_NAT_PLUS,pos,args),_ex_intern_small_integer(0)));
}

static struct _ex_intern *make_bottom1(struct env *env, struct equation_record *r, struct _ex_intern *offset)
{
    struct _ex_intern **args;
    int pos, i;
    unsigned one[2];

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (r->count+1));
    for (pos = 0, i = 0; i < r->count; ++i) {
        if (r->terms[i]->type != EXP_INTEGER) {
            args[pos++] = _ex_intern_appl2_env(env,INTERN_NAT_TIMES,r->terms[i],r->coefficients[i]);
        }
    }
    one[0] = 1;
    one[1] = 1;
    offset = _ex_intern_integer(_th_big_sub(offset->u.integer,one));
    args[pos++] = offset;

    return _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_appl_env(env,INTERN_NAT_PLUS,pos,args),_ex_intern_small_integer(0));
}

static struct _ex_intern *make_top1(struct env *env, struct equation_record *r, struct _ex_intern *offset)
{
    struct _ex_intern **args;
    int pos, i;
    unsigned one[2];

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (r->count+1));
    for (pos = 0, i = 0; i < r->count; ++i) {
        if (r->terms[i]->type != EXP_INTEGER) {
            args[pos++] = _ex_intern_appl2_env(env,INTERN_NAT_TIMES,r->terms[i],r->coefficients[i]);
        }
    }
    one[0] = 1;
    one[1] = 1;
    offset = _ex_intern_integer(_th_big_add(offset->u.integer,one));
    args[pos++] = offset;

    return _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),_ex_intern_appl_env(env,INTERN_NAT_PLUS,pos,args));
}

static struct _ex_intern *make_bottom(struct env *env, struct equation_record *r, struct _ex_intern *offset)
{
    struct _ex_intern **args;
    int pos, i;

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (r->count+1));
    for (pos = 0, i = 0; i < r->count; ++i) {
        if (r->terms[i]->type != EXP_INTEGER) {
            args[pos++] = _ex_intern_appl2_env(env,INTERN_NAT_TIMES,r->terms[i],r->coefficients[i]);
        }
    }
    args[pos++] = offset;

    return _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_appl_env(env,INTERN_NAT_PLUS,pos,args),_ex_intern_small_integer(0));
}

static struct _ex_intern *make_top(struct env *env, struct equation_record *r, struct _ex_intern *offset)
{
    struct _ex_intern **args;
    int pos, i;

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (r->count+1));
    for (pos = 0, i = 0; i < r->count; ++i) {
        if (r->terms[i]->type != EXP_INTEGER) {
            args[pos++] = _ex_intern_appl2_env(env,INTERN_NAT_TIMES,r->terms[i],r->coefficients[i]);
        }
    }
    args[pos++] = offset;

    return _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(0),_ex_intern_appl_env(env,INTERN_NAT_PLUS,pos,args));
}

struct _ex_intern *_th_invert_or_equations(struct env *env, struct _ex_intern *exp)
{
    int i, size, pos;
    struct equation_record *first, *rest, *r;
    struct _ex_intern *top, *bottom, *min_eq, *max_eq;
    struct _ex_intern *e;
    unsigned *diff;
    unsigned one[2];
    struct _ex_intern **args;

    _zone_print_exp("Invert or_equations", exp);
    // This function is buggy (it is disabled for now)
    return NULL;

    if (exp->type != EXP_APPL || exp->u.appl.functor != INTERN_OR) return NULL;
    if (exp->u.appl.count < 2) return NULL;

    _tree_indent();

    first = make_equation_record(env, exp->u.appl.args[0]);
    if (first==NULL) {
        _tree_undent();
        return NULL;
    }

    rest = NULL;

    for (i = 1; i < exp->u.appl.count; ++i) {
        r = make_equation_record(env,exp->u.appl.args[i]);
        if (r==NULL) {
            _tree_undent();
            return NULL;
        }
        if (!compatible_equations(first->count, first->coefficients, first->terms, r->count, r->coefficients, r->terms)) {
            _tree_undent();
            return NULL;
        }
        r->next = rest;
        rest = r;
    }

    first->next = rest;

    top = bottom = min_eq = max_eq = NULL;

    r = first;
    while (r) {
        e = get_offset(r);
        switch (r->type) {
            case INTERN_NAT_LESS:
                if (top==NULL) {
                    top = e;
                } else if (_th_big_less(top->u.integer,e->u.integer)) {
                    top = e;
                }
                break;

            case INTERN_NOT:
                if (bottom==NULL) {
                    bottom = e;
                } else if (_th_big_less(e->u.integer,bottom->u.integer)) {
                    bottom = e;
                }
                break;

            case INTERN_EQUAL:
                if (min_eq==NULL) {
                    min_eq = max_eq = e;
                } else {
                    if (_th_big_less(e->u.integer,min_eq->u.integer)) {
                        min_eq = e;
                    }
                    if (_th_big_less(max_eq->u.integer,e->u.integer)) {
                        max_eq = e;
                    }
                }
                break;
        }
        r = r->next;
    }

    one[0] = 1;
    one[1] = 1;

    _zone_print1("min_eq = %s", _th_print_exp(min_eq));
    _zone_print1("max_eq = %s", _th_print_exp(max_eq));
    _zone_print1("top = %s", _th_print_exp(top));
    _zone_print1("bottom = %s", _th_print_exp(bottom));

    if (!top && !bottom) {
        diff = _th_big_sub(max_eq->u.integer, min_eq->u.integer);
        diff = _th_big_add(diff,one);
        if (diff[0]==1 && (diff[1] & 0x80000000)==0 &&
            ((int)diff[1]) <= _th_integrate_split_limit) {
            size = diff[1];
            pos = 0;
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (size+2));
            for (i = 0; i < size; ++i) {
                one[1] = i;
                e = _ex_intern_integer(_th_big_add(min_eq->u.integer,one));
                r = first;
                while (r != NULL) {
                    if (get_offset(r)==e) break;
                    r = r->next;
                }
                if (r==NULL) {
                    args[pos++] = make_not(env,first,e);
                }
            }
            args[pos++] = make_bottom1(env,first,min_eq);
            args[pos++] = make_top1(env,first,max_eq);
            _tree_undent();
            return _ex_intern_appl_env(env,INTERN_AND,pos,args);
        }
    } else if (top && bottom) {
        diff = _th_big_sub(top->u.integer, bottom->u.integer);
        //_zone_print2("diff %d %d", diff[0], diff[1]);
        if (diff[0]==1 && (diff[1] & 0x80000000)==0 &&
            ((int)diff[1]) <= _th_integrate_split_limit) {
            size = diff[1];
            pos = 0;
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (size+2));
            for (i = -1; i <= size; ++i) {
                one[1] = i;
                e = _ex_intern_integer(_th_big_add(bottom->u.integer,one));
                r = first;
                while (r != NULL) {
                    if (r->type==INTERN_EQUAL && get_offset(r)==e) break;
                    r = r->next;
                }
                if (r==NULL) {
                    args[pos++] = make_not(env,first,e);
                }
            }
            _tree_undent();
            return _ex_intern_appl_env(env,INTERN_AND,pos,args);
        }
    } else if (top) {
        diff = _th_big_sub(top->u.integer, min_eq->u.integer);
        _zone_print2("diff %d %d", diff[0], diff[1]);
        if (diff[0]==1 && (diff[1] & 0x80000000)==0 &&
            ((int)diff[1]) <= _th_integrate_split_limit) {
            size = diff[1];
            pos = 0;
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (size+2));
            for (i = 0; i <= size; ++i) {
                one[1] = i;
                e = _ex_intern_integer(_th_big_add(min_eq->u.integer,one));
                r = first;
                while (r != NULL) {
                    if (r->type==INTERN_EQUAL && get_offset(r)==e) break;
                    r = r->next;
                }
                if (r==NULL) {
                    args[pos++] = make_not(env,first,e);
                }
            }
            one[1] = 1;
            args[pos++] = make_bottom(env,first,_ex_intern_integer(_th_big_sub(min_eq->u.integer,one)));
            _tree_undent();
            return _ex_intern_appl_env(env,INTERN_AND,pos,args);
        }
    } else if (bottom) {
        diff = _th_big_sub(max_eq->u.integer, bottom->u.integer);
        if (diff[0]==1 && (diff[1] & 0x80000000)==0 &&
            ((int)diff[1]) <= _th_integrate_split_limit) {
            size = diff[1];
            pos = 0;
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (size+2));
            for (i = -1; i <= size; ++i) {
                one[1] = i;
                e = _ex_intern_integer(_th_big_add(bottom->u.integer,one));
                r = first;
                while (r != NULL) {
                    if (r->type==INTERN_EQUAL && get_offset(r)==e) break;
                    r = r->next;
                }
                if (r==NULL) {
                    args[pos++] = make_not(env,first,e);
                }
            }
            args[pos++] = make_top1(env,first,max_eq);
            _tree_undent();
            return _ex_intern_appl_env(env,INTERN_AND,pos,args);
        }
    }

    _tree_undent();
    return NULL;
}

static struct _ex_intern *no_vars_free_in(struct _ex_intern *term, int count, unsigned *vars)
{
    int i;

    for (i = 0; i < count; ++i) {
        if (_th_is_free_in(term,vars[i])) {
            return NULL;
        }
    }

    return term;
}

int _th_integrate_split_limit = 10;

static struct _ex_intern *trans_constant(struct _ex_intern *cond, int dir, struct _ex_intern *term, int count, unsigned *vars)
{
    struct add_list *trans_list = NULL, *n, *t;
    int i, added;
    struct _ex_intern *e, *f;

    if (no_vars_free_in(term,count,vars)) return term;

    trans_list = (struct add_list *)ALLOCA(sizeof(struct add_list));
    trans_list->next = NULL;
    trans_list->e = term;

    //_zone_print_exp("Trans", term);

    added = 1;
    while (added) {
        added = 0;
        for (i = 0; i < cond->u.appl.count; ++i) {
            e = cond->u.appl.args[i];
            if (e->type==EXP_APPL) {
                if (e->u.appl.functor==INTERN_NAT_LESS) {
                    if (dir) {
                        f = e->u.appl.args[0];
                        t = trans_list;
                        while (t) {
                            if (t->e==f) {
                                f = e->u.appl.args[1];
                                break;
                            }
                            t = t->next;
                        }
                        if (t) {
                            t = trans_list;
                            while (t) {
                                if (t->e==f) goto cont;
                                t = t->next;
                            }
                            //_zone_print_exp("trans", f);
                            if (no_vars_free_in(f,count,vars)) return f;
                            n = (struct add_list *)ALLOCA(sizeof(struct add_list));
                            n->next = trans_list;
                            trans_list = n;
                            added = 1;
                        }
                    } else {
                        f = e->u.appl.args[1];
                        t = trans_list;
                        while (t) {
                            if (t->e==f) {
                                f = e->u.appl.args[0];
                                break;
                            }
                            t = t->next;
                        }
                        if (t) {
                            t = trans_list;
                            while (t) {
                                if (t->e==f) goto cont;
                                t = t->next;
                            }
                            //_zone_print_exp("trans", f);
                            if (no_vars_free_in(f,count,vars)) return f;
                            n = (struct add_list *)ALLOCA(sizeof(struct add_list));
                            n->next = trans_list;
                            trans_list = n;
                            added = 1;
                        }
                    }
                } else if (e->u.appl.functor==INTERN_NOT) {
                    e = e->u.appl.args[0];
                    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NAT_LESS) {
                        if (dir) {
                            f = e->u.appl.args[0];
                            t = trans_list;
                            while (t) {
                                if (t->e==f) {
                                    f = e->u.appl.args[1];
                                    break;
                                }
                                t = t->next;
                            }
                            if (t) {
                                t = trans_list;
                                while (t) {
                                    if (t->e==f) goto cont;
                                    t = t->next;
                                }
                                //_zone_print_exp("trans", f);
                                if (no_vars_free_in(f,count,vars)) return f;
                                n = (struct add_list *)ALLOCA(sizeof(struct add_list));
                                n->next = trans_list;
                                trans_list = n;
                                added = 1;
                            }
                        } else {
                            f = e->u.appl.args[1];
                            t = trans_list;
                            while (t) {
                                if (t->e==f) {
                                    f = e->u.appl.args[0];
                                    break;
                                }
                                t = t->next;
                            }
                            if (t) {
                                t = trans_list;
                                while (t) {
                                    if (t->e==f) goto cont;
                                    t = t->next;
                                }
                                //_zone_print_exp("trans", f);
                                if (no_vars_free_in(f,count,vars)) return f;
                                n = (struct add_list *)ALLOCA(sizeof(struct add_list));
                                n->next = trans_list;
                                trans_list = n;
                                added = 1;
                            }
                        }
                    }
                } else if (e->u.appl.functor==INTERN_EQUAL) {
                    f = e->u.appl.args[1];
                    t = trans_list;
                    while (t) {
                        if (t->e==f) {
                            f = e->u.appl.args[0];
                            break;
                        }
                        t = t->next;
                    }
                    if (t) {
                        t = trans_list;
                        while (t) {
                            if (t->e==f) goto cont;
                            t = t->next;
                        }
                        //_zone_print_exp("trans", f);
                        if (no_vars_free_in(f,count,vars)) return f;
                        n = (struct add_list *)ALLOCA(sizeof(struct add_list));
                        n->next = trans_list;
                        trans_list = n;
                        added = 1;
                    }
                    f = e->u.appl.args[0];
                    t = trans_list;
                    while (t) {
                        if (t->e==f) {
                            f = e->u.appl.args[1];
                            break;
                        }
                        t = t->next;
                    }
                    if (t) {
                        t = trans_list;
                        while (t) {
                            if (t->e==f) goto cont;
                            t = t->next;
                        }
                        //_zone_print_exp("trans", f);
                        if (no_vars_free_in(f,count,vars)) return f;
                        n = (struct add_list *)ALLOCA(sizeof(struct add_list));
                        n->next = trans_list;
                        trans_list = n;
                        added = 1;
                    }
                }
            }
cont: ;
        }
    }

    return NULL;
}

struct _ex_intern *_th_trans_constant(struct _ex_intern *cond, int dir, struct _ex_intern *term, int count, unsigned *fv)
{
    if (count==0) fv = _th_get_free_vars(cond, &count);

    return trans_constant(cond, dir, term, count, fv);
}

static struct _ex_intern *finite_variable_expansion(struct env *env, struct _ex_intern *set)
{
    int i, j, var_pos;
    unsigned var;
    struct _ex_intern *e, *min, *max, *f, **args;
    unsigned *vars;
    struct _ex_unifier *u ;

    //_zone_print1("Shared separation %s", _th_print_exp(set));

    if (set->u.quant.cond->type != EXP_APPL || set->u.quant.cond->u.appl.functor != INTERN_AND) return NULL;
    if (!_th_is_constant(env, set->u.quant.exp)) return NULL;
    if (set->u.quant.var_count < 1) return NULL;

    for (i = 0; i < set->u.quant.var_count; ++i) {
         var = set->u.quant.vars[i];
         e = set->u.quant.cond;
         min = NULL;
         max = NULL;
         //_zone_print1("Checking %d", i);
         for (j = 0; j < e->u.appl.count; ++j) {
             f = e->u.appl.args[j];
             //_zone_print_exp("term", f);
             if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NAT_LESS) {
                 if (f->u.appl.args[0]->type==EXP_VAR && f->u.appl.args[0]->u.var==var && max==NULL) {
                     max = trans_constant(e,1,f->u.appl.args[1], set->u.quant.var_count, set->u.quant.vars);
					 if (max) {
                         max = _th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_MINUS,max,_ex_intern_small_integer(1)),1);
                         if (max->type != EXP_INTEGER) max = NULL;
					 }
                 }
                 if (f->u.appl.args[1]->type==EXP_VAR && f->u.appl.args[1]->u.var==var && min==NULL) {
                     min = trans_constant(e,0,f->u.appl.args[0], set->u.quant.var_count, set->u.quant.vars);
					 if (min) {
                         min = _th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,min,_ex_intern_small_integer(1)),1);
                         if (min && min->type != EXP_INTEGER) min = NULL;
					 }
                 }
             }
             if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NOT) {
                 f = f->u.appl.args[0];
                 if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NAT_LESS) {
                     if (f->u.appl.args[0]->type==EXP_VAR && f->u.appl.args[0]->u.var==var && min==NULL) {
                         min = trans_constant(e,0,f->u.appl.args[1], set->u.quant.var_count, set->u.quant.vars);
                         if (min->type != EXP_INTEGER) min = NULL;
                     }
                     if (f->u.appl.args[1]->type==EXP_VAR && f->u.appl.args[1]->u.var==var && max==NULL) {
                         max = trans_constant(e,1,f->u.appl.args[0], set->u.quant.var_count, set->u.quant.vars);
                         if (max && max->type != EXP_INTEGER) max = NULL;
                     }
                 }
             }
             //_zone_print2("free3 %d %d", min, max);
             //_zone_print2("in_set[%d] = %d", j, in_set[j]);
         }
         if (!min || !max) {
             goto cont;
         }
         f = _th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_MINUS,max,min),1);
         if (f->type != EXP_INTEGER) goto cont;
         if (f->u.integer[0] != 1) goto cont;
         if (f->u.integer[1] & 0x80000000) goto cont;
         if (((int)f->u.integer[1]) > _th_integrate_split_limit) goto cont;
         //_zone_print0("free4");
         var_pos = i;
         goto good;
cont: ;
    }
    return NULL;
good:
    //_zone_print_exp("good", e);
    //_zone_print_exp("min", min);
    //_zone_print_exp("max", max);
    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (f->u.integer[1]+1));
    vars = (unsigned *)ALLOCA(sizeof(unsigned) * set->u.quant.var_count);
    for (i = 0, j = 0; i < set->u.quant.var_count; ++i) {
        if (i != var_pos) vars[j++] = set->u.quant.vars[i];
    }
    for (i = 0; i <= ((int)f->u.integer[1]); ++i) {
        u = _th_new_unifier(REWRITE_SPACE);
        u = _th_add_pair(REWRITE_SPACE,u,var,_th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,min,_ex_intern_small_integer(i)),1));
        args[i] = _ex_intern_appl1_env(env,INTERN_SETSIZE,
                      _ex_intern_quant(INTERN_SETQ,set->u.quant.var_count-1,vars,
                          _th_subst(env,u,set->u.quant.exp),
                          _th_subst(env,u,set->u.quant.cond)));
    }
    return _ex_intern_appl_env(env,INTERN_NAT_PLUS,i,args);
}

static struct _ex_intern *free_finite_variable_expansion(struct env *env, struct _ex_intern *set)
{
    int i, j, count;
    unsigned var, *fv;
    struct _ex_intern *e, *min, *max, *f, *comp, *v;
    struct _ex_intern *rules = _th_get_context_rule_set(env);
    struct _ex_unifier *u ;

    //_zone_print1("Shared separation %s", _th_print_exp(set));

    if (set->u.quant.cond->type != EXP_APPL || set->u.quant.cond->u.appl.functor != INTERN_AND) return NULL;
    if (!_th_is_constant(env, set->u.quant.exp)) return NULL;
    if (set->u.quant.var_count < 1) return NULL;

    fv = _th_get_free_vars(set, &count);
    for (i = 0; i < count; ++i) {
         var = fv[i];
         e = set->u.quant.cond;
         min = NULL;
         max = NULL;
         //_zone_print1("Checking %d", i);
         for (j = 0; j < rules->u.appl.count; ++j) {
             f = rules->u.appl.args[j];
             _zone_print2("Free finite %s %s", _th_intern_decode(var), _th_print_exp(rules->u.appl.args[j]));
             //_zone_print_exp("term", f);
             if (f->u.appl.args[2]==_ex_true) {
                 if (f->u.appl.args[1]==_ex_true) {
                     f = f->u.appl.args[0];
                     if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NAT_LESS) {
                         if (f->u.appl.args[0]->type==EXP_MARKED_VAR && f->u.appl.args[0]->u.var==var && max==NULL) {
                             max = f->u.appl.args[1];
                             if (max->type==EXP_INTEGER) {
                                 max = _th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_MINUS,max,_ex_intern_small_integer(1)),1);
                             } else {
                                 max = NULL;
                             }
                         }
                         if (f->u.appl.args[1]->type==EXP_MARKED_VAR && f->u.appl.args[1]->u.var==var && min==NULL) {
                             min = f->u.appl.args[0];
                             if (min->type==EXP_INTEGER) {
                                 min = _th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,min,_ex_intern_small_integer(1)),1);
                             } else {
                                 min = NULL;
                             }
                         }
                     }
                 }
                 if (f->u.appl.args[1]==_ex_false) {
                     f = f->u.appl.args[0];
                     if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NAT_LESS) {
                         if (f->u.appl.args[0]->type==EXP_MARKED_VAR && f->u.appl.args[0]->u.var==var && min==NULL) {
                             min = f->u.appl.args[1];
                             if (min->type != EXP_INTEGER) min = NULL;
                         }
                         if (f->u.appl.args[1]->type==EXP_MARKED_VAR && f->u.appl.args[1]->u.var==var && max==NULL) {
                             max = f->u.appl.args[0];
                             if (max->type != EXP_INTEGER) max = NULL;
                         }
                     }
                 }
             }
             //_zone_print2("free3 %d %d", min, max);
             //_zone_print2("in_set[%d] = %d", j, in_set[j]);
         }
         if (!min || !max) {
             goto cont;
         }
         f = _th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_MINUS,max,min),1);
         if (f->type != EXP_INTEGER) goto cont;
         if (f->u.integer[0] != 1) goto cont;
         if (f->u.integer[1] & 0x80000000) goto cont;
         if (((int)f->u.integer[1]) > _th_integrate_split_limit) goto cont;
         //_zone_print0("free4");
         goto good;
cont: ;
    }
    return NULL;
good:
    //_zone_print_exp("good", e);
    //_zone_print_exp("min", min);
    //_zone_print_exp("max", max);
    comp = _ex_intern_small_integer(0);
    for (i = 0; i <= ((int)f->u.integer[1]); ++i) {
        u = _th_new_unifier(REWRITE_SPACE);
        u = _th_add_pair(REWRITE_SPACE,u,var,(v = _th_int_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,min,_ex_intern_small_integer(i)),1)));
        e = _ex_intern_appl1_env(env,INTERN_SETSIZE,_th_subst(env,u,set));
        comp = _ex_intern_appl3_env(env,INTERN_ITE,
                    _ex_intern_appl2_env(env,INTERN_EQUAL,_ex_intern_var(var),v),
                    e,
                    comp);
    }
    return comp;
}

static struct _ex_intern *process_not_equals(struct env *env, struct _ex_intern *var, struct _ex_intern *e)
{
	struct _ex_intern *max = _th_get_upper_bound(env,var);
	struct _ex_intern *min = _th_get_lower_bound(env,var);
	struct add_list *adds, *a;
    int has_ne;

	unsigned one[2] = { 1, 1 };

	if (max != NULL && min != NULL) {
        struct _ex_intern *m = max;
		//fprintf(stderr, "min = %s\n", _th_print_exp(min));
		//fprintf(stderr, "max = %s\n", _th_print_exp(max));
		//fprintf(stderr, "m = %s\n", _th_print_exp(m));
		//fprintf(stderr, "e = %s\n", _th_print_exp(e));
		//fflush(stderr);
		if (e==m) {
			m = _ex_intern_integer(_th_big_sub(m->u.integer,one));
			adds = _th_get_not_equals(env,var);
			has_ne = 1;
			while (has_ne) {
				has_ne = 0;
				a = adds;
				while (a) {
					if (a->e==m) {
						has_ne = 1;
						break;
					}
					a = a->next;
				}
				if (has_ne) {
					m = _ex_intern_integer(_th_big_sub(m->u.integer,one));
					if (_th_big_less(m->u.integer,min->u.integer)) return _ex_false;
				}
			}
			if (min==m) {
				return _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,var,m,_ex_true);
			}
			m = _ex_intern_integer(_th_big_add(m->u.integer,one));
			return _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,_ex_intern_appl2_env(env,INTERN_NAT_LESS,var,m),_ex_true,_ex_true);
		}
		
		m = min->u.integer;
		
		if (e==m) {
			m = _ex_intern_integer(_th_big_add(m->u.integer,one));
			adds = _th_get_not_equals(env,var);
			has_ne = 1;
			while (has_ne) {
				has_ne = 0;
				a = adds;
				while (a) {
					if (a->e==m) {
						has_ne = 1;
						break;
					}
					a = a->next;
				}
				if (has_ne) {
					m = _ex_intern_integer(_th_big_add(m->u.integer,one));
					if (_th_big_less(max->u.integer,m->u.integer)) return _ex_false;
				}
			}
			if (max==m) {
				return _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,var,m,_ex_true);
			}
			m = _ex_intern_integer(_th_big_sub(m->u.integer,one));
			return _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,_ex_intern_appl2_env(env,INTERN_NAT_LESS,m,var),_ex_true,_ex_true);
		}
	}

	return _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,_ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,var,e,_ex_true),_ex_false,_ex_true);
}

static struct _ex_intern *process_max(struct env *env, struct _ex_intern *var, struct _ex_intern *e)
{
	struct _ex_intern *min = _th_get_lower_bound(env,var);
	struct add_list *adds, *a;
    int has_ne;

	unsigned one[2] = { 1, 1 };
    struct _ex_intern *m = _ex_intern_integer(_th_big_sub(e->u.integer,one));

	if (min != NULL) {
		//fprintf(stderr, "min = %s\n", _th_print_exp(min));
		//fprintf(stderr, "m = %s\n", _th_print_exp(m));
		//fprintf(stderr, "e = %s\n", _th_print_exp(e));
		//fflush(stderr);
		adds = _th_get_not_equals(env,var);
		has_ne = 1;
		while (has_ne) {
			has_ne = 0;
			a = adds;
			while (a) {
				if (a->e==m) {
					has_ne = 1;
					break;
				}
				a = a->next;
			}
			if (has_ne) {
				m = _ex_intern_integer(_th_big_sub(m->u.integer,one));
				if (_th_big_less(m->u.integer,min->u.integer)) return _ex_false;
			}
		}
		if (min==m) {
			return _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,var,m,_ex_true);
		}
	}
	m = _ex_intern_integer(_th_big_add(m->u.integer,one));
	return _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,_ex_intern_appl2_env(env,INTERN_NAT_LESS,var,m),_ex_true,_ex_true);
}

static struct _ex_intern *process_min(struct env *env, struct _ex_intern *var, struct _ex_intern *e)
{
	struct _ex_intern *max = _th_get_upper_bound(env,var);
	struct add_list *adds, *a;
    int has_ne;

	unsigned one[2] = { 1, 1 };
    struct _ex_intern *m = _ex_intern_integer(_th_big_add(e->u.integer,one));

	if (max != NULL) {
		//fprintf(stderr, "max = %s\n", _th_print_exp(max));
		//fprintf(stderr, "m = %s\n", _th_print_exp(m));
		//fprintf(stderr, "e = %s\n", _th_print_exp(e));
		//fflush(stderr);
		adds = _th_get_not_equals(env,var);
		has_ne = 1;
		while (has_ne) {
			has_ne = 0;
			a = adds;
			while (a) {
				if (a->e==m) {
					has_ne = 1;
					break;
				}
				a = a->next;
			}
			if (has_ne) {
				m = _ex_intern_integer(_th_big_add(m->u.integer,one));
				if (_th_big_less(max->u.integer,m->u.integer)) return _ex_false;
			}
			//fprintf(stderr, "   m = %s\n", _th_print_exp(m));
		}
		if (max==m) {
			return _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,var,m,_ex_true);
		}
	}
	m = _ex_intern_integer(_th_big_sub(m->u.integer,one));
	//fprintf(stderr, "Done\n");
	//fflush(stderr);
	return _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,_ex_intern_appl2_env(env,INTERN_NAT_LESS,m,var),_ex_true,_ex_true);
}

struct _ex_intern *_th_augment_finite_rule(struct env *env, struct _ex_intern *rule)
{
	if (rule->type==EXP_APPL && rule->u.appl.functor==INTERN_ORIENTED_RULE &&
		rule->u.appl.count==3 && rule->u.appl.args[2]==_ex_true) {
		struct _ex_intern *r = rule->u.appl.args[0];
		if (rule->u.appl.args[1]==_ex_false && r->type==EXP_APPL &&
			(r->u.appl.functor==INTERN_EQUAL || r->u.appl.functor==INTERN_ORIENTED_RULE)) {
			if (r->u.appl.args[0]->type==EXP_INTEGER) {
				return process_not_equals(env,r->u.appl.args[1],r->u.appl.args[0]);
			} else if (r->u.appl.args[1]->type==EXP_INTEGER) {
				return process_not_equals(env,r->u.appl.args[0],r->u.appl.args[1]);
			}
		} else if (rule->u.appl.args[1]==_ex_true && r->type==EXP_APPL &&
		           r->u.appl.functor==INTERN_NAT_LESS) {
			if (r->u.appl.args[0]->type==EXP_INTEGER) {
				return process_min(env,r->u.appl.args[1],r->u.appl.args[0]);
			} else if (r->u.appl.args[1]->type==EXP_INTEGER) {
				return process_max(env,r->u.appl.args[0],r->u.appl.args[1]);
			}
		}
	}

	return rule;
}

