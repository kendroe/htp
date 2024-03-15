/*
 * case_split.c
 *
 * Heuristics for doing case splitting of an expression.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>

#include "Intern.h"
#include "Globals.h"

//#ifdef _DEBUG
//#define _zone_print _tree_print
//#define _zone_print1 _tree_print
//#define _zone_print2 _tree_print
//#define _zone_print3 _tree_print
//#endif

int _th_do_learn = 3600;
static int new_learn = 1;
int _th_do_unate = 1;
int _th_score_mode = 2;
int _th_use_composite_conds = 0;

static int get_index(unsigned *vars, int count, unsigned var)
{
    int i;
    
    for (i = 0; i < count; ++i) {
        if (vars[i]==var) return i;
    }
    fprintf(stderr, "get_index: missing var\n");
    exit(1);
}

static struct _ex_intern *divide_list(struct env *env, struct _ex_intern *exp)
{
    int count, i, j, k, small, c, cnt, pos;
    unsigned *fv;
    unsigned *vars;
    int *groups;
    struct _ex_intern **args, **args2;

	_zone_print_exp("Splitting", exp);
	_tree_indent();

    if (exp->type != EXP_APPL || exp->u.appl.functor != INTERN_AND) {
		_tree_undent();
        return _ex_intern_appl1_env(env,INTERN_AND,exp);
    }

    fv = _th_get_free_vars(exp, &count);
    vars = (unsigned *)ALLOCA(sizeof(unsigned) * count);
    groups = (int *)ALLOCA(sizeof(int) * count);
    for (i = 0; i < count; ++i) {
        vars[i] = fv[i];
        groups[i] = i;
    }

    for (i = 0; i < exp->u.appl.count; ++i) {
        fv = _th_get_free_vars(exp->u.appl.args[i], &c);
		//_zone_print_exp("Processing", exp->u.appl.args[i]);
        small = count+1;
		//_tree_indent();
        for (j = 0; j < c; ++j) {
			//_zone_print3("Marking var %s (%d,%d)", _th_intern_decode(fv[j]), get_index(vars,count,fv[j]), groups[get_index(vars,count,fv[j])]);
            if (groups[get_index(vars,count,fv[j])] < small) {
				small = groups[get_index(vars,count,fv[j])];
			}
        }
		//_tree_undent();
        while (groups[small] != small) {
            small = groups[small];
        }
        for (j = 0; j < c; ++j) {
			int index = get_index(vars,count,fv[j]);
			if (index != groups[index]) {
				groups[groups[index]] = small;
			}
            groups[index] = small;
        }
    }

	for (i = 0; i < count; ++i) {
	    small = groups[i];
		if (groups[small] != small) {
			groups[i] = groups[small];
		}
	}

    c = 0;
    for (j = 0; j < count; ++j) {
		_zone_print3("var %s maps %d to %d", _th_intern_decode(vars[j]), j, groups[j]);
        if (groups[j]==j) ++c;
    }

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * c);

    small = 0;
    for (i = 0; i < c; ++i) {
        while (small != groups[small]) ++small;
        args2 = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count);
        pos = 0;
        for (j = 0; j < exp->u.appl.count; ++j) {
            fv = _th_get_free_vars(exp->u.appl.args[j], &cnt);
            for (k = 0; k < cnt; ++k) {
                if (groups[get_index(vars,count,fv[k])]==small) {
                    args2[pos++] = exp->u.appl.args[j];
                    goto next;
                }
            }
next: ;
        }
        args[i] = _ex_intern_appl_env(env,INTERN_AND,pos,args2);
        ++small;
    }

	_tree_undent();
    return _ex_intern_appl_env(env,INTERN_AND,c,args);
}

static int case_count;

static struct _ex_intern *_th_divide_variable(struct env *env, struct _ex_intern *exp, unsigned var, struct _ex_intern *min, struct _ex_intern *max)
{
    struct _ex_intern *f, *comp, *e, *v;
    struct _ex_unifier *u;
    char *mark;
    int i;

    _zone_print1("Case analysis of %s", _th_intern_decode(var));
    _tree_indent();
    _zone_print_exp("min", min);
    _zone_print_exp("max", max);

    mark = _th_alloc_mark(MATCH_SPACE);

    f = _th_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_MINUS,max,min));
    if (f->type != EXP_INTEGER ||
        f->u.integer[0] != 1 ||
        f->u.integer[1] & 0x80000000 ||
        ((int)f->u.integer[1]) > _th_integrate_split_limit) {
        case_count = -1;
        _zone_print0("Failure");
        _tree_undent();
        return NULL;
    }

    case_count = 0;

    comp = _ex_false;
    for (i = 0; i <= ((int)f->u.integer[1]); ++i) {
        u = _th_new_unifier(MATCH_SPACE);
        v = _th_rewrite(env,_ex_intern_appl2_env(env,INTERN_NAT_PLUS,min,_ex_intern_small_integer(i)));
        _zone_print2("%s = %s", _th_intern_decode(var), _th_print_exp(v));
        _tree_indent();
        u = _th_add_pair(MATCH_SPACE,u,var,v);
        e = _th_subst(env,u,exp);
        _zone_print_exp("substituted expression", e);
        if (!_th_is_constant(env,e)) ++case_count;
        comp = _ex_intern_appl3_env(env,INTERN_ITE,
                    _ex_intern_appl2_env(env,INTERN_EQUAL,_ex_intern_var(var),v),
                    e,
                    comp);
        _tree_undent();
    }

    _th_alloc_release(MATCH_SPACE,mark);

    _zone_print1("count = %d", case_count);
    _tree_undent();
    return comp;
}

static struct _ex_intern *analyze_and_split(struct env *env, struct fd_handle *fd, struct _ex_intern *exp)
{
    unsigned *fv, *vars;
    int *counts;
    //struct _ex_intern **results;
    int i, count, pos, min_cases;
    struct _ex_intern *min, *max;
    struct _ex_intern *context_rules = _th_get_context_rule_set(env);

    _zone_print_exp("Analyzing", exp);
    _tree_indent();

    fv = _th_get_free_vars(exp, &count);
    vars = (unsigned *)ALLOCA(sizeof(unsigned) * count);
    counts = (int *)ALLOCA(sizeof(int) * count);
    //results = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern **) * count);
    for (i = 0; i < count; ++i) {
        vars[i] = fv[i];
    }

#ifdef XX
    for (i = 0; i < count; ++i) {
        min = _th_get_min(env, context_rules, exp, vars[i]);
        max = _th_get_max(env, context_rules, exp, vars[i]);
        if (min==NULL || max==NULL) {
            results[i] = NULL;
            counts[i] = -1;
        } else {
            results[i] = _th_divide_variable(env, exp, vars[i], min, max);
            counts[i] = case_count;
        }
    }
#endif

    pos = -1;

    for (i = 0; i < count; ++i) {
		struct _ex_intern *cnt = _fd_get_value_count(env,fd,vars[i]);
		int count;
		if (cnt->u.integer[0]==1 && cnt->u.integer[1] < 0x7fffffff &&
			cnt->u.integer[1] > 1) {
			count = (int)cnt->u.integer[1];
		} else {
			count = 0;
		}
        if (count > 0 && (pos < 0 || count < min_cases)) {
            min_cases = count;
            pos = i;
        }
    }


    if (pos < 0) {
        _zone_print0("No division");
        _tree_undent();
        return NULL;
    } else {
        _zone_print1("Dividing with %s", _th_intern_decode(vars[pos]));
        _tree_undent();
		min = _fd_get_min_value(env,fd,vars[pos]);
		max = _fd_get_max_value(env,fd,vars[pos]);
        //result = _th_divide_variable(env, exp, vars[pos], min, max);
		return _ex_intern_var(vars[pos]);
    }
}

static struct _ex_intern *process_case(struct env *env, struct fd_handle *fd, struct _ex_intern *exp);

static struct _ex_intern *process_children(struct env *env, struct fd_handle *fd, unsigned var, int v, struct _ex_intern *exp)
{
    struct _ex_intern *t, *f;
	struct _ex_intern *value;
    struct _ex_intern *count = _fd_get_value_count(env,fd,var);

	_zone_print3("Process children %s %d %s", _th_intern_decode(var), v, _th_print_exp(count));
	if (v < (int)count->u.integer[1]) {
		value = _fd_get_value_n(env,fd,var,v);
        _zone_print2("Processing case %s=%s", _th_intern_decode(var), _th_print_exp(value));
        _tree_indent();
		_fd_instantiate(env,fd,var,value);
        t = process_case(env, fd, exp);
		_fd_revert(fd);
        if (t==NULL) t = exp;
        _tree_undent();
        f = process_children(env, fd, var, v+1, exp);
        return _ex_intern_appl3_env(env, INTERN_ITE, _ex_intern_appl2_env(env,INTERN_EQUAL,_ex_intern_var(var),value), t, f);
    } else {
        return exp;
    }
}

static struct _ex_intern *process_case(struct env *env, struct fd_handle *fd, struct _ex_intern *exp)
{
	struct _ex_intern *v;
    _zone_print_exp("Processing", exp);
    _tree_indent();
    v = analyze_and_split(env,fd,exp);
    if (v != NULL) {
		_fd_push(fd);
        exp = process_children(env,fd,v->u.var,0,exp);
		_fd_pop(fd);
    }
    _tree_undent();
    return exp;
}

struct _ex_intern *_th_case_split(struct env *env, struct _ex_intern *exp)
{
    struct _ex_intern *independent_cases = divide_list(env, exp);
    struct _ex_intern **args;
	struct fd_handle *fd;
    int i;

    _zone_print_exp("_th_case_split", exp);

    if (independent_cases->u.appl.count==0) return independent_cases;

    _tree_indent();
    _zone_print_exp("cases", independent_cases);

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * independent_cases->u.appl.count);
    for (i = 0; i < independent_cases->u.appl.count; ++i) {
    	fd = _fd_solve(env,independent_cases->u.appl.args[i]);
		if (fd != NULL) {
            args[i] = process_case(env,fd,independent_cases->u.appl.args[i]);
		} else {
			args[i] = independent_cases->u.appl.args[i];
		}
    }

    _tree_undent();

    return _ex_intern_appl_env(env,INTERN_AND,i,args);
}

static struct _ex_intern *term_trail;

int _th_same_count(struct env *env, struct _ex_intern *e, struct _ex_intern *ref)
{
    int i, count;
    
    if (e->type != ref->type) return 0;
    
    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor != ref->u.appl.functor) return 0;
            if (e->u.appl.count != ref->u.appl.count) return 0;
            
            count = 1;
            if (_th_is_ac(env,e->u.appl.functor) || _th_is_c(env,e->u.appl.functor)) {
                int j, pos, gsc, c;
                int *used = (int *)ALLOCA(sizeof(int) * e->u.appl.count);
                for (i = 0; i < e->u.appl.count; ++i) {
                    used[i] = 0;
                }
                for (i = 0; i < e->u.appl.count; ++i) {
                    gsc = -1;
                    for (j = 0; j < e->u.appl.count; ++j) {
                        if (!used[j]) {
                            c = _th_same_count(env,e->u.appl.args[i],ref->u.appl.args[j]);
                            if (c > gsc) {
                                pos = j;
                                gsc = c;
                            }
                        }
                    }
                    used[pos] = 1;
                    count += gsc;
                }
                return count;
            } else {
                for (i = 0; i < e->u.appl.count; ++i) {
                    count += _th_same_count(env,e->u.appl.args[i],ref->u.appl.args[i]);
                }
                return count;
            }
            
        case EXP_QUANT:
            if (e->u.quant.quant != ref->u.quant.quant) return 0;
            return 1+_th_same_count(env,e->u.quant.exp,ref->u.quant.exp)+
                _th_same_count(env,e->u.quant.cond,ref->u.quant.cond);
            
        default:
            if (e==ref) {
                return 1;
            } else {
                return 0;
            }
    }
}

struct _ex_intern *total_count(struct env *env, struct _ex_intern *e)
{
    int i;
    struct _ex_intern *count, *t;

    if (e->user2) {
#ifdef TEST
        if (e->user2->type != EXP_INTEGER) {
            printf("Non-integer cache value %x\n", e->user2);
            fflush(stdout);
            printf("cache %d\n", e->user2->type);
            fflush(stdout);
            printf("value %s\n", _th_print_exp(e->user2));
            fflush(stdout);
            printf("e = %s\n", _th_print_exp(e));
            exit(1);
        }
        printf("cache returning %d %d %d %d\n", e->user2->u.integer[0], e->user2->u.integer[1], e->user2->u.integer[2], e->user2->u.integer[3]);
#endif
        return e->user2;
    }

    e->next_cache = term_trail;
    term_trail = e;

    switch (e->type) {
        case EXP_APPL:
            count = _ex_intern_small_integer(1);
            for (i = 0; i < e->u.appl.count; ++i) {
                t = total_count(env,e->u.appl.args[i]);
                count = _ex_intern_integer(_th_big_add(count->u.integer,t->u.integer));
            }
            e->user2 = count;
            return count;
        
        case EXP_QUANT:
            count = _ex_intern_small_integer(1);
            t = total_count(env,e->u.quant.exp);
            count = _ex_intern_integer(_th_big_add(count->u.integer,t->u.integer));
            t = total_count(env,e->u.quant.cond);
            count = _ex_intern_integer(_th_big_add(count->u.integer,t->u.integer));
            e->user2 = count;
            return count;

        default:
            e->user2 = _ex_intern_small_integer(1);
            return e->user2;
    }
}

struct _ex_intern *_th_total_count(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *count;

    term_trail = NULL;

    _th_clear_cache();

    count = total_count(env,e);

    while (term_trail) {
        term_trail->user2 = NULL;
        term_trail = term_trail->next_cache;
    }

    return count;
}

struct term_list *_th_sort_terms(struct env *env, struct term_list *list)
{
	struct term_list *l, *n, *p;
	int change;

	change = 1;
	while (change) {
		change = 0;
		l = list;
		p = NULL;
		while (l && l->next) {
			if (l->count < l->next->count) {
				n = l->next;
				l->next = n->next;
				n->next = l;
				if (p==NULL) {
					list = n;
				} else {
				    p->next = n;
				}
				l = n;
				change = 1;
			}
			p = l;
			l = l->next;
		}
	}

	return list;
}

static int threshold_count(struct env *env, struct _ex_intern *e, struct add_list *list)
{
    struct add_list *l = list;
    int count = 0, c;
    int *top;
    int i, j;
    
    while (l) {
        ++count;
        l = l->next;
    }
    
    count = (count + 9) / 10;
    top = (int *)ALLOCA(sizeof(int) * count);
    
    for (i = 0; i < count; ++i) top[i] = 0;
    
    l = list;
    while (l) {
        c = _th_term_count(env,e,l->e);
        for (i = 0; i < count; ++i) {
            if (top[i] > c) {
                goto cont;
            }
        }
cont:
        if (i) {
            for (j = 0; j < i-2; ++j) {
                top[j] = top[j+1];
            }
            top[i-1] = c;
        }
        l = l->next;
    }
    return top[0];
}

static int valid_subterm(struct env *env, struct _ex_intern *e, struct _ex_intern *r)
{
    int i;
    
    if (e==r) return 1;
    
    if (e->type==r->type) {
        switch (e->u.appl.functor) {
            case EXP_APPL:
                if (e->u.appl.functor==r->u.appl.functor && e->u.appl.count==r->u.appl.count) {
                    if (_th_is_ac(env,e->u.appl.functor) || _th_is_c(env,e->u.appl.functor)) {
                        int *used, j;
                        used = (int *)ALLOCA(sizeof(int) * e->u.appl.count);
                        for (i = 0; i < e->u.appl.count; ++i) {
                            used[i] = 0;
                        }
                        for (i = 0; i < e->u.appl.count; ++i) {
                            for (j = 0; j < e->u.appl.count; ++j) {
                                if (!used[j]) {
                                    if (valid_subterm(env,e->u.appl.args[i],r->u.appl.args[j])) {
                                        used[j] = 1;
                                        goto cont1;
                                    }
                                }
                            }
                            goto cont;
cont1:;
                        }
                        return 1;
                    } else {
                        for (i = 0; i < e->u.appl.count; ++i) {
                            if (!valid_subterm(env,e->u.appl.args[i],r->u.appl.args[i])) goto cont;
                        }
                        return 1;
                    }
                }
cont:
                break;
            case EXP_QUANT:
                if (e->u.quant.quant==r->u.quant.quant) {
                    if (valid_subterm(env,e->u.quant.exp,r->u.quant.exp) &&
                        valid_subterm(env,e->u.quant.cond,r->u.quant.cond)) return 1;
                }
                break;
        }
    }
    
    switch (e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                if (valid_subterm(env,e->u.appl.args[i],r)) return 1;
            }
            break;
        case EXP_QUANT:
            if (valid_subterm(env,e->u.quant.exp,r) ||
                valid_subterm(env,e->u.quant.cond,r)) return 1;
    }
    
    return 0;
}

int top_match(struct env *env, struct _ex_intern *e, struct _ex_intern *r)
{
    if (e->type==r->type) {
        switch (e->type) {
            case EXP_APPL:
                return e->u.appl.functor==r->u.appl.functor &&
                    e->u.appl.count==r->u.appl.count;
            case EXP_QUANT:
                return e->u.quant.quant==r->u.quant.quant;
            default:
                return e==r;
        }
    }
    
    return 0;
}

struct elim_list {
	struct elim_list *next;
	struct _ex_intern *term;
	struct _ex_intern *e;
	struct _ex_intern *r;
};

static struct elim_list *eliminated_terms(struct env *env, struct _ex_intern *e, struct _ex_intern *r, struct elim_list *a);

static struct elim_list *list;
static struct _ex_intern *subterm_find(struct env *env, struct _ex_intern *e, struct _ex_intern *r, struct elim_list *a)
{
	int i;
	if (top_match(env,e,r) && valid_subterm(env,e,r)) {
		switch (e->type) {
		    case EXP_APPL:
				for (i = 0; i < e->u.appl.count; ++i) {
					if (valid_subterm(env,e->u.appl.args[i],r)) goto cont;
				}
				goto def;
			case EXP_QUANT:
				if (valid_subterm(env,e->u.quant.exp,r) ||
					valid_subterm(env,e->u.quant.cond,r)) goto cont;
def:
			default:
				list = eliminated_terms(env,e,r,a);
				return _ex_intern_appl_env(env,INTERN_TUPLE,0,NULL);
		}
	}
cont:
	switch (e->type) {
	    case EXP_APPL:
			for (i = 0; i < e->u.appl.count; ++i) {
				if (valid_subterm(env,e->u.appl.args[i],r)) {
					struct _ex_intern *f = subterm_find(env,e->u.appl.args[i],r,a);
					struct _ex_intern **args;
					int j;
					args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
					for (j = 0; j < e->u.appl.count; ++j) {
						args[j] = e->u.appl.args[j];
					}
					args[i] = f;
					return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
				}
			}
			list = a;
			return e;
		case EXP_QUANT:
			if (valid_subterm(env,e->u.quant.exp,r)) {
				struct _ex_intern *f = subterm_find(env,e->u.quant.exp,r,a);
				return _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,e->u.quant.vars,f,e->u.quant.cond);
			}
			if (valid_subterm(env,e->u.quant.cond,r)) {
				struct _ex_intern *f = subterm_find(env,e->u.quant.cond,r,a);
				return _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,e->u.quant.vars,e->u.quant.exp,f);
			}
		default:
			list = a;
			return e;
	}
}

static struct elim_list *eliminated_terms(struct env *env, struct _ex_intern *e, struct _ex_intern *r, struct elim_list *a)
{
    int i;
    struct elim_list *al;
    struct _ex_intern *term;
    
    if (e==r) return a;
    
    if (e->type == r->type) {
        switch (e->type) {
            case EXP_APPL:
                if (e->u.appl.functor != r->u.appl.functor || e->u.appl.count != r->u.appl.count) {
                    goto no_match;
                }
                if (_th_is_ac(env,e->u.appl.functor) || _th_is_c(env,e->u.appl.functor)) {
                    int j, *used, *taken, *map;
                    used = (int *)ALLOCA(sizeof(int) * e->u.appl.count);
                    taken = (int *)ALLOCA(sizeof(int) * e->u.appl.count);
                    map = (int *)ALLOCA(sizeof(int) * e->u.appl.count);
                    for (i = 0; i < e->u.appl.count; ++i) {
                        taken[i] = 0;
                        used[i] = 0;
                    }
                    for (i = 0; i < e->u.appl.count; ++i) {
                        for (j = 0; j < e->u.appl.count; ++j) {
                            if (!used[j]) {
                                if (e->u.appl.args[i]==r->u.appl.args[j]) {
                                    taken[i] = 1;
                                    used[j] = 1;
                                    map[i] = j;
                                    goto cont0;
                                }
                            }
                        }
cont0:;
                    }
                    for (i = 0; i < e->u.appl.count; ++i) {
                        for (j = 0; j < e->u.appl.count; ++j) {
                            if (!used[j]) {
                                if (top_match(env,e->u.appl.args[i],r->u.appl.args[j]) &&
                                    valid_subterm(env,e->u.appl.args[i],r->u.appl.args[j])) {
                                    taken[i] = 1;
                                    used[j] = 1;
                                    map[i] = j;
                                    goto cont1;
                                }
                            }
                        }
cont1:;
                    }
                    for (i = 0; i < e->u.appl.count; ++i) {
                        if (!taken[i]) {
                            for (j = 0; j < e->u.appl.count; ++j) {
                                if (!used[j]) {
                                    if (valid_subterm(env,e->u.appl.args[i],r->u.appl.args[j])) {
                                        taken[i] = 1;
                                        used[j] = 1;
                                        map[i] = j;
                                        goto cont2;
                                    }
                                }
                            }
                        }
cont2:;
                    }
                    for (i = 0, j = 0; i < e->u.appl.count; ++i) {
                        if (taken[i]) {
                            a = eliminated_terms(env,e->u.appl.args[i],r->u.appl.args[map[i]],a);
                        } else {
                            al = a;
                            a = (struct elim_list *)_th_alloc(REWRITE_SPACE,sizeof(struct elim_list));
                            a->next = al;
                            a->term = a->e = e->u.appl.args[i];
                            a->r = r;
                        }
                    }
                    return a;
                } else {
                    for (i = 0; i < e->u.appl.count; ++i) {
                        a = eliminated_terms(env,e->u.appl.args[i],r->u.appl.args[i],a);
                    }
                    return a;
                }
            case EXP_QUANT:
                if (e->u.quant.quant != r->u.quant.quant) {
                    goto no_match;
                }
                a = eliminated_terms(env,e->u.quant.exp,r->u.quant.exp,a);
                return eliminated_terms(env,e->u.quant.cond,r->u.quant.cond,a);
        }
    }
    
no_match:
    term = subterm_find(env,e,r,a);
    a = list;
    al = (struct elim_list *)_th_alloc(REWRITE_SPACE,sizeof(struct elim_list));
    al->next = a;
    al->e = e;
    al->term = term;
    al->r = r;
    return al;
}

#ifdef OLD_UNATE

#define UNATE_TRUE  1
#define UNATE_FALSE 2

static int is_unate(struct _ex_intern *e)
{
    int res, res1, res2, ret;
    if (e->type!=EXP_APPL) return UNATE_TRUE|UNATE_FALSE;

    if (e->unate_processed) {
        res = 0;
        if (e->unate_false) res += UNATE_FALSE;
        if (e->unate_true) res += UNATE_TRUE;
        return res;
    }

    switch (e->u.appl.functor) {
        case INTERN_ITE:
            res = is_unate(e->u.appl.args[0]);
            res1 = is_unate(e->u.appl.args[1]);
            res2 = is_unate(e->u.appl.args[2]);
            ret = 0;
            if (e->u.appl.args[1]==_ex_true) {
                if ((res & UNATE_TRUE) || (res2 & UNATE_TRUE)) ret |= UNATE_TRUE;
            } else if (e->u.appl.args[1]==_ex_false) {
                if ((res & UNATE_TRUE) || (res2 & UNATE_FALSE)) ret |= UNATE_FALSE;
            }
            if (e->u.appl.args[2]==_ex_true) {
                if ((res & UNATE_FALSE) || (res2 & UNATE_TRUE)) ret |= UNATE_TRUE;
            } else if (e->u.appl.args[2]==_ex_false) {
                if ((res & UNATE_FALSE) || (res1 & UNATE_FALSE)) ret |= UNATE_FALSE;
            }
            break;
        case INTERN_NOT:
            switch (is_unate(e->u.appl.args[0])) {
                case 0:
                    ret = 0;
                case UNATE_TRUE:
                    ret = UNATE_FALSE;
                case UNATE_FALSE:
                    ret = UNATE_TRUE;
                case (UNATE_TRUE|UNATE_FALSE):
                    ret = (UNATE_TRUE|UNATE_FALSE);
            }
            break;
        case INTERN_AND:
        case INTERN_OR:
            ret = 0;
            break;
        default:
            ret = UNATE_TRUE|UNATE_FALSE;
    }

    e->unate_processed = 1;
    if (ret & UNATE_TRUE) e->unate_true = 1;
    if (ret & UNATE_FALSE) e->unate_false = 1;
    //if (ret) {
    //    printf("Unate term %s\n", _th_print_exp(e));
    //}
    return ret;
}

static struct _ex_intern *find_unate(struct _ex_intern *e)
{
    int u;

    if (!is_unate(e)) return NULL;

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_ITE) {

        if (e->u.appl.args[1]==_ex_true) {
            u = is_unate(e->u.appl.args[0]);
            if (u & UNATE_TRUE) return find_unate(e->u.appl.args[0]);
            u = is_unate(e->u.appl.args[2]);
            if (u & UNATE_TRUE) return find_unate(e->u.appl.args[2]);
        }

        if (e->u.appl.args[1]==_ex_false) {
            u = is_unate(e->u.appl.args[0]);
            if (u & UNATE_TRUE) return find_unate(e->u.appl.args[0]);
            u = is_unate(e->u.appl.args[2]);
            if (u & UNATE_FALSE) return find_unate(e->u.appl.args[2]);
        }

        if (e->u.appl.args[2]==_ex_true) {
            u = is_unate(e->u.appl.args[0]);
            if (u & UNATE_FALSE) return find_unate(e->u.appl.args[0]);
            u = is_unate(e->u.appl.args[1]);
            if (u & UNATE_TRUE) return find_unate(e->u.appl.args[1]);
        }

        if (e->u.appl.args[2]==_ex_false) {
            u = is_unate(e->u.appl.args[0]);
            if (u & UNATE_FALSE) return find_unate(e->u.appl.args[0]);
            u = is_unate(e->u.appl.args[1]);
            if (u & UNATE_FALSE) return find_unate(e->u.appl.args[1]);
        }

    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {

        return find_unate(e->u.appl.args[0]);

    } else if (e->type != EXP_APPL || (e->u.appl.functor != INTERN_AND && e->u.appl.functor != INTERN_OR)) {

        return e;

    }

    return NULL;
}
#endif

static int split_count;
static int unate_count;
static int elimination_count;
static int solved_cases;
static int learned_unates;
static int restart_count;
static int backjump_count;
struct learn_info *info;

struct _ex_intern *_th_choose_case(struct env *env, struct _ex_intern *e)
{
    struct term_list *l;
    struct term_list *list;
#ifdef SHOW_ELIMINATED
    struct elim_list *a;
#endif
    struct _ex_intern *count, *min_count, *tcount, *fcount;
    struct _ex_intern *t_case, *f_case, *rt_case, *rf_case;
    struct _ex_intern *ret;
    struct _ex_intern *args[4];
    //int threshold = threshold_count(env,e,l);
    char *mark;
    
    _tree_print0("Choosing case");
    
    mark = _th_alloc_mark(REWRITE_SPACE);

    l = _th_get_terms(env,e,NULL);

    if (l==NULL) return NULL;
    
    l = _th_sort_terms(env,l);
    list = l;
    count = 0;

    while (l != NULL) {
        ++count;
        l = l->next;
    }
    _tree_print1("Total terms: %d", count);

    l = list;
    _tree_indent();
    min_count = _th_total_count(env,e);
    min_count = _ex_intern_integer(_th_big_add(min_count->u.integer,min_count->u.integer));
    _tree_print_exp("Initial min_count =", min_count);
    //_tree_print1("Threshold = %d", threshold);
    
    while (l != NULL) {
        int tc = l->count;
        //if (tc >= threshold && !_th_another_cond_as_subterm(env,l->e,list)) {
        _tree_print_exp("Checking", l->e);
        if (!_th_another_cond_as_subterm(env,l->e,list) && l->e != e) {
            if (tc > 1) {
                _tree_print2("Evaluating(%d) %s", tc, _th_print_exp(l->e));
            } else {
                _tree_print_exp("Evaluating term", l->e);
            }
            _tree_indent();
            _tree_print1("Terms = %d", _th_total_count(env,l->e));
            count = 0;
            _th_derive_push(env);
            if (_th_assert_predicate(env,l->e)) {
                _tree_print0("Inconsistent condition");
                t_case = _ex_true;
            } else {
                _th_clear_cache();
                t_case = _th_nc_rewrite(env,e);
#ifdef SHOW_ELIMINATED
                a = eliminated_terms(env,e,t_case,NULL);
                if (a) {
                    _tree_print0("Eliminated terms");
                    _tree_indent();
                    while (a) {
                        _tree_print_exp("term", a->term);
                        _tree_indent();
                        _tree_print_exp("e", a->e);
                        _tree_print_exp("r", a->r);
                        _tree_undent();
                        a = a->next;
                    }
                    _tree_undent();
                }
#endif
            }
            tcount = _th_total_count(env,t_case);
#ifndef FAST
            if (t_case==e) {
                _tree_print0("--same");
            }
            _tree_print_exp("tcount =", tcount);
#endif
            _th_derive_pop(env);
            _th_derive_push(env);
            if (_th_deny_predicate(env,l->e)) {
                _tree_print0("Inconsistent negation");
                f_case = _ex_true;
            } else {
                _th_clear_cache();
                f_case = _th_nc_rewrite(env,e);
#ifdef SHOW_ELIMINATED
                a = eliminated_terms(env,e,f_case,NULL);
                if (a) {
                    _tree_print0("Eliminated terms");
                    _tree_indent();
                    while (a) {
                        _tree_print_exp("term", a->term);
                        _tree_indent();
                        _tree_print_exp("e", a->e);
                        _tree_print_exp("r", a->r);
                        _tree_undent();
                        a = a->next;
                    }
                    _tree_undent();
                }
#endif
            }
#ifndef FAST
            if (f_case==e) {
                _tree_print0("--same");
            }
#endif
            fcount = _th_total_count(env,f_case);
            _tree_print_exp("fcount =", fcount);
            _th_derive_pop(env);
            count = _ex_intern_integer(_th_big_add(tcount->u.integer,fcount->u.integer));
            _tree_print_exp("count =", count);
            if (t_case==_ex_true || f_case==_ex_true ||
                t_case==_ex_false || f_case==_ex_false) {
                rt_case = t_case;
                rf_case = f_case;
                _tree_undent();
                min_count = count;
                ret = l->e;
                goto done;
            }
            if (!_th_big_less(min_count->u.integer,count->u.integer)) {
                _tree_undent();
                _tree_print0("Choosing case");
                _tree_indent();
                rt_case = t_case;
                rf_case = f_case;
                min_count = count;
                ret = l->e;
            }
            _tree_undent();
        }
        l = l->next;
    }
    
done:
    _tree_print_exp("Choice", ret);
    _tree_print_exp("Count", min_count);
    
    args[0] = _ex_true;
    args[1] = rt_case;
    args[2] = _ex_false;
    args[3] = rf_case;
    
    _tree_undent();
    if (rt_case==_ex_true || rf_case==_ex_true || rt_case==_ex_false ||
        rf_case==_ex_false) {
        ++elimination_count;
        _tree_print0("CASE ELIMINATION CHOICE");
    }
    
    _th_alloc_release(REWRITE_SPACE,mark);
    if (ret==NULL) {
        return NULL;
    } else {
        return _ex_intern_case(ret,2,args);
    }
}

static struct _ex_intern *transform_exp(struct env *env, struct _ex_intern *e, int term)
{
    int i, j;
    struct _ex_intern **args;
    struct _ex_intern *f, *g, *h;

    if (e->user2) return e->user2;
    e->next_cache = term_trail;
    term_trail = e;

    if (e->type != EXP_APPL || !_th_check_term(e,term)) {
        e->user2 = e;
        return e;
    }

    switch (e->u.appl.functor) {
        case INTERN_NOT:
            f = e->u.appl.args[0];
            g = transform_exp(env,f,term);
            if (f==g) {
                e->user2 = e;
                return e;
            } else if (g==_ex_false) {
                e->user2 = _ex_true;
                return _ex_true;
            } else if (g==_ex_true) {
                e->user2 = _ex_false;
                return _ex_false;
            } else {
                f = e->user2 = _ex_intern_appl1_env(env,INTERN_NOT,g);
                return f;
            }
        case INTERN_OR:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            for (i = 0, j = 0; i < e->u.appl.count; ++i) {
                f = transform_exp(env,e->u.appl.args[i],term);
                if (f==_ex_true) {
                    e->user2 = _ex_true;
                    return _ex_true;
                } else if (f != _ex_false) {
                    args[j++] = f;
                }
            }
            if (j==0) {
                e->user2=_ex_false;
                return _ex_false;
            } else if (j==1) {
                e->user2 = args[0];
                return args[0];
            } else {
                f = e->user2 = _ex_intern_appl_env(env,INTERN_OR,j,args);
                return f;
            }
        case INTERN_AND:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            for (i = 0, j = 0; i < e->u.appl.count; ++i) {
                f = transform_exp(env,e->u.appl.args[i],term);
                if (f==_ex_false) {
                    e->user2 = _ex_false;
                    return _ex_false;
                } else if (f != _ex_true) {
                    args[j++] = f;
                }
            }
            if (j==0) {
                e->user2=_ex_true;
                return _ex_true;
            } else if (j==1) {
                e->user2 = args[0];
                return args[0];
            } else {
                f = e->user2 = _ex_intern_appl_env(env,INTERN_AND,j,args);
                return f;
            }
        case INTERN_ITE:
            f = transform_exp(env,e->u.appl.args[0],term);
            g = transform_exp(env,e->u.appl.args[1],term);
            h = transform_exp(env,e->u.appl.args[2],term);
            if (f==_ex_true) {
                e->user2 = g;
                return g;
            } else if (f==_ex_false) {
                e->user2 = h;
                return h;
            } else if (g==h) {
                e->user2 = g;
                return g;
            } else {
                f = e->user2 = _ex_intern_appl3_env(env,INTERN_ITE,f,g,h);
                return f;
            }
        case INTERN_EQUAL:
            f = transform_exp(env,e->u.appl.args[0],term);
            g = transform_exp(env,e->u.appl.args[1],term);
            if (f==g) {
                e->user2 = _ex_true;
                return _ex_true;
            } else if ((f==_ex_true && g==_ex_false) || (f==_ex_false && g==_ex_true)) {
                e->user2 = _ex_false;
                return _ex_false;
            } else {
                f = e->user2 = _ex_intern_appl2_env(env,INTERN_EQUAL,f,g);
                return f;
            }
        default:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = transform_exp(env,e->u.appl.args[i],term);
            }
            f = e->user2 = _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
            return f;
    }
}

static struct _ex_intern *remove_case(struct env *env, struct _ex_intern *e, struct _ex_intern *term, struct _ex_intern *reduce)
{
    term_trail = term;
    term->user2 = reduce;
    term->next_cache = NULL;

    e = transform_exp(env,e,_th_get_term_position(term));

    while(term_trail) {
        term_trail->user2 = NULL;
        term_trail = term_trail->next_cache;
    }

    return e;
}

static int rule_score(struct env *env, struct _ex_intern *t)
{
    struct _ex_intern *r;
    struct rule *cr;
    int count = 0;

    r = _th_get_first_context_rule(env,&cr);
    _th_mark_simplified(env);
    while (r) {
        if (!r->rule_simplified) {
            r = _th_unmark_vars(env,r);
            if (r!=t && r->u.appl.args[0]!=t && (r->u.appl.args[1]==_ex_true || r->u.appl.args[1]==_ex_false || t->type != EXP_APPL || t->u.appl.functor != INTERN_EQUAL ||
                (t->u.appl.args[0] != r->u.appl.args[0] && t->u.appl.args[1] != r->u.appl.args[0]) ||
                (t->u.appl.args[0] != r->u.appl.args[1] && t->u.appl.args[1] != r->u.appl.args[1]))) {
                struct _ex_intern *rs = _th_get_score(env,r,t);
                int tc = rs->u.appl.args[0]->u.integer[1];
                count += tc;
            }
        }
        r = _th_get_next_rule(env,&cr);
    }
    _th_clear_simplified(env);

    return count;
}

static int has_ite_rule(struct env *env)
{
    struct _ex_intern *r;
    struct rule *cr;

    r = _th_get_first_context_rule(env,&cr);
    _th_mark_simplified(env);
    while (r) {
        if (!r->rule_simplified && _th_my_contains_ite(r)) {
            _th_clear_simplified(env);
            return 1;
        }
        r = _th_get_next_rule(env,&cr);
    }
    _th_clear_simplified(env);

    return 0;
}

static struct parent_list *splits;

int has_subterm(struct _ex_intern *a, struct _ex_intern *b, int level)
{
    int i;

    if (a==b) return 1;

    if (level==0) return 0;

    if (b->type==EXP_APPL) {
        for (i = 0; i < b->u.appl.count; ++i) {
            if (has_subterm(a,b->u.appl.args[i],level-1)) return 1;
        }
    }
    
    return 0;
}

void _check_splits(struct _ex_intern *e)
{
    struct parent_list *s = splits;

    while (s != NULL) {
        if (has_subterm(s->split,e,5)) {
            printf("Split 1");
            exit(1);
        }
        if (s->split->type==EXP_APPL && s->split->u.appl.functor==INTERN_NOT && has_subterm(s->split->u.appl.args[0],e,5)) {
            printf("split 2");
            exit(1);
        }
        s = s->next;
    }
}

int term_used(struct parent_list *p, struct _ex_intern *e)
{
    //struct _ex_intern *le = e;
    //if (le->type==EXP_APPL && le->u.appl.functor==INTERN_NOT) {
    //    le = le->u.appl.args[0];
    //}
    while (p) {
        struct _ex_intern *base = p->split;
        //if (base->type==EXP_APPL && base->u.appl.functor==INTERN_NOT) {
        //    base = base->u.appl.args[0];
        //}
        //if (base==le) {
        //    return 1;
        //}
        if (p->split==e) return 1;
        p = p->next;
    }
    return 0;
}

struct _ex_intern *_th_fast_choose_case(struct env *env, struct _ex_intern *e, struct term_list *list, struct learn_info *info, struct parent_list *parent)
{
    struct term_list *l;
    struct _ex_intern *t_case, *f_case;
    struct _ex_intern *ret, *args[4], *rets;
    char *mark;
    struct _ex_intern *max_count;
    int max_learn, count, min_reject;
    //int emax;
    struct parent_list *p;
    //int max_countx, max_county;
    //struct _ex_intern *rety;

    _tree_print0("Choosing case");
    
    mark = _th_alloc_mark(REWRITE_SPACE);

    l = list;

    count = 0;
    while (l != NULL) {
        ++count;
        l = l->next;
    }
    _tree_print1("Total terms: %d", count);

    l = list;
    _tree_indent();

    max_count = _ex_intern_small_integer(-1);
    max_learn = 0;
    min_reject = 1000000;
    //emax = 0;
    //max_county = -1;
    ret = NULL;
    while (l != NULL) {
        struct _ex_intern *le = _th_int_rewrite(env,l->e,0);
        _zone_print_exp("Term", l->e);
#ifndef FAST
        if (!le->in_hash) {
            _th_simp(env,le);
            //_th_print_difference_table(env);
            //fprintf(stderr, "Term %s not in hash table\n", _th_print_exp(l->e));
            //exit(1);
        }
#endif
        if (!le->in_hash) {
            _tree_indent();
            _th_simp(env,le);
            _tree_undent();
            _zone_print_exp("Simplification", le);
        }
        while (le->find && le->find != le) le = le->find;
        if ((_th_use_composite_conds || e==_ex_true || e==_ex_false || !_th_another_cond_as_subterm(env,le,list)) && le != e && le != _ex_true && le != _ex_false) {
            struct _ex_intern *rs;
            //int tcx = rsx->u.appl.args[0]->u.integer[1];
            struct _ex_intern *tc;
            //int es;
            int lc = 0;
            int r = 0;
            _tree_print_exp("Checking", le);
            p = parent;
            //_tree_indent();
            while (p) {
                struct _ex_intern *base = p->split;
                if (base->type==EXP_APPL && base->u.appl.functor==INTERN_NOT) {
                    base = base->u.appl.args[0];
                }
                //_tree_print_exp("Base", base);
                //_tree_print_exp("Testing base", base);
                //_tree_print_exp("Term", le);
                //_tree_print2("addrs %x %x", base, le);
                //_tree_print4("addrs %x %x %x %x", base->u.appl.args[0], base->u.appl.args[1], le->u.appl.args[0], le->u.appl.args[1]);
                if (base==le) {
                    //_tree_print_exp("Skipping", le);
                    //_tree_undent();
                    goto cont;
                }
                p = p->next;
            }
            //_tree_undent();
            //struct _ex_intern *rs = _th_reduction_score(env,list,l,e);
            _zone_print0("Here2");
            if (e != _ex_true && e != _ex_false) {
                rs = _th_get_score(env,e,le);
            } else {
                rs = _ex_intern_appl3_env(env,INTERN_TUPLE,_ex_intern_small_integer(0),e,e);
            }
            //es = _th_score_equality(env,le);
            //int tcx = rsx->u.appl.args[0]->u.integer[1];
            tc = rs->u.appl.args[0];
            // + rule_score(env,le);
            if (_th_do_learn) {
                lc = _th_learn_score(env,info,le,parent);
                r = _th_get_reject_count(env,info,le);
            }
            if (tc->u.integer[0]==1 && tc->u.integer[1]==-1) {
                //_tree_undent();
                rets = rs;
                ret = le;
                goto finish;
            }
            _tree_print_exp("Evaluating nodes of", le);
            _tree_print_exp("Score", tc);
            _tree_print1("reject count %d", r);
#ifndef FAST
            _tree_print1("learn score %d\n", lc);
#endif
            //_tree_print1("equality score %d", es);
            //if (tc==0) {
            //    exit(1);
            //}
            //if (tcx > max_county) {
            //    max_county = tcx;
            //    rety = le;
            //}
            //if (new_learn) {
                //if (_th_big_less(max_count->u.integer, tc->u.integer)) {
                //if (_th_big_less(max_count->u.integer, tc->u.integer) ||
                //    (max_count==tc && emax < es)) {
                    //ret = le;
                    //rets = rs;
                    //emax = es;
                    //max_count = tc;
                    //max_learn = lc;
                    //max_countx = tcx;
                    //_tree_print0("Choosing");
                //}
            //} else {
                if (lc > max_learn ||
                    (lc==max_learn && r < min_reject) ||
                    (lc==max_learn && r==min_reject && _th_big_less(max_count->u.integer, tc->u.integer))) {
                //if (lc > max_learn || (lc==max_learn && _th_big_less(max_count->u.integer, tc->u.integer)) ||
                //    (lc==max_learn && tc==max_count && emax < es)) {
                    ret = le;
                    rets = rs;
                    max_count = tc;
                    max_learn = lc;
                    min_reject = r;
                    //emax = es;
                    //max_countx = tcx;
                    _tree_print0("Choosing");
                }
            //}
        } else {
            _zone_print_exp("Skipping", le);
        }
cont:
        l = l->next;
    }
    //if (max_countx < max_count/2) {
    //    _tree_print_exp("Different", rety);
    //    exit(1);
    //}

    if (ret==NULL) {
        _tree_undent();
        return NULL;
    }

finish:
    //if (ret->type==EXP_VAR || ret->type==EXP_MARKED_VAR) {
        //t_case = rets->u.appl.args[1];
        //if (t_case != _th_nc_rewrite(env,t_case)) {
        //    printf("Rewrite error1\n");
        //    exit(1);
        //}
        //f_case = rets->u.appl.args[2];
        //if (f_case != _th_nc_rewrite(env,f_case)) {
        //    printf("Rewrite error2\n");
        //    exit(1);
        //}
    //} else {
    t_case = rets->u.appl.args[1];
        //_th_derive_push(env);
        //if (_th_assert_predicate(env,ret)) {
            //_tree_print0("Inconsistent true condition");
            //t_case = _ex_true;
        //} else {
            //struct _ex_intern *x;
            //_th_clear_cache();
            //t_case = _th_nc_rewrite(env,rets->u.appl.args[1]);
            //x = _th_nc_rewrite(env,t_case);
            //if (x != t_case) {
            //    fprintf(stderr, "Illegal _th_term_rewrite");
            //    exit(1);
            //}
        //}
#ifndef FAST
        //if (t_case==e) {
            //_tree_print0("--same");
        //}
#endif
    f_case = rets->u.appl.args[2];
        //_th_derive_pop(env);
        //_th_derive_push(env);
        //if (_th_deny_predicate(env,ret)) {
            //_tree_print0("Inconsistent negation");
            //f_case = _ex_true;
        //} else {
            //struct _ex_intern *x;
            //_th_clear_cache();
            //f_case = _th_nc_rewrite(env,rets->u.appl.args[2]);
            //x = _th_nc_rewrite(env,f_case);
            //if (x != f_case) {
            //    fprintf(stderr, "Illegal _th_term_rewrite");
            //    exit(1);
            //}
        //}
#ifndef FAST
        //if (f_case==e) {
            //_tree_print0("--same");
        //}
#endif
        //_th_derive_pop(env);
    //}

    _tree_print_exp("Choice", ret);
    _tree_print2("learn, reject %d %d", max_learn, min_reject);
    _tree_print1("Count %d", max_count->u.integer[1]);
    
    args[0] = _ex_true;
    args[1] = t_case;
    args[2] = _ex_false;
    args[3] = f_case;
    
    _tree_undent();
    //if (t_case==_ex_true || f_case==_ex_true || t_case==_ex_false ||
    //    f_case==_ex_false) {
    //    ++elimination_count;
    //    _tree_print0("CASE ELIMINATION CHOICE");
    //}
    
    _th_alloc_release(REWRITE_SPACE,mark);
    if (ret==NULL) {
        return NULL;
    } else {
        return _ex_intern_case(ret,2,args);
    }
}

struct _ex_intern *_th_first_choose_case(struct env *env, struct _ex_intern *e, struct term_list *list, struct learn_info *info)
{
    struct term_list *l;
    struct _ex_intern *t_case, *f_case;
    struct _ex_intern *ret, *args[4];
    char *mark;
    int max_count, count;
    //int max_countx, max_county;
    //struct _ex_intern *rety;

    _tree_print_exp("Choosing case for", e);
    
    mark = _th_alloc_mark(REWRITE_SPACE);

    l = list;

    count = 0;
    while (l != NULL) {
        ++count;
        l = l->next;
    }
    _tree_print1("Total terms: %d", count);

    l = list;
    _tree_indent();

    max_count = -1;
    //max_county = -1;
    ret = NULL;
    while (l != NULL) {
        if (!_th_another_cond_as_subterm(env,l->e,list) && l->e != e) {
            ret = l->e;
            goto finish;
        }
    }
    //if (max_countx < max_count/2) {
    //    _tree_print_exp("Different", rety);
    //    exit(1);
    //}

    if (ret==NULL) {
        _tree_undent();
        return NULL;
    }

finish:
    //if (ret->type==EXP_VAR || ret->type==EXP_MARKED_VAR) {
        //t_case = rets->u.appl.args[1];
        //if (t_case != _th_nc_rewrite(env,t_case)) {
        //    printf("Rewrite error1\n");
        //    exit(1);
        //}
        //f_case = ret;
        //if (f_case != _th_nc_rewrite(env,f_case)) {
        //    printf("Rewrite error2\n");
        //    exit(1);
        //}
    //} else {
        _th_derive_push(env);
        if (_th_assert_predicate(env,ret)) {
            _tree_print0("Inconsistent true condition");
            t_case = _ex_true;
        } else {
            //struct _ex_intern *x;
            _th_clear_cache();
            t_case = _th_nc_rewrite(env,ret);
            //x = _th_nc_rewrite(env,t_case);
            //if (x != t_case) {
            //    fprintf(stderr, "Illegal _th_term_rewrite");
            //    exit(1);
            //}
        }
#ifndef FAST
        if (t_case==e) {
            _tree_print0("--same");
        }
#endif
        _th_derive_pop(env);
        _th_derive_push(env);
        if (_th_deny_predicate(env,ret)) {
            _tree_print0("Inconsistent negation");
            f_case = _ex_true;
        } else {
            //struct _ex_intern *x;
            _th_clear_cache();
            f_case = _th_nc_rewrite(env,ret);
            //x = _th_nc_rewrite(env,f_case);
            //if (x != f_case) {
            //    fprintf(stderr, "Illegal _th_term_rewrite");
            //    exit(1);
            //}
        }
#ifndef FAST
        if (f_case==e) {
            _tree_print0("--same");
        }
#endif
        _th_derive_pop(env);
    //}

    _tree_print_exp("Choice", ret);
    _tree_print1("Count %d", max_count);
    
    args[0] = _ex_true;
    args[1] = t_case;
    args[2] = _ex_false;
    args[3] = f_case;
    
    _tree_undent();
    if (t_case==_ex_true || f_case==_ex_true || t_case==_ex_false ||
        f_case==_ex_false) {
        ++elimination_count;
        _tree_print0("CASE ELIMINATION CHOICE");
    }
    
    _th_alloc_release(REWRITE_SPACE,mark);
    if (ret==NULL) {
        return NULL;
    } else {
        return _ex_intern_case(ret,2,args);
    }
}

int _th_find_all_fails = 0;

struct parent_list *add_reductions(struct env *env)
{
    struct rule *cr;
    struct parent_list *a, *ret = NULL;
    struct _ex_intern *r;

    //printf("ADD REDUCTIONS\n");

    _th_mark_simplified(env);
    r = _th_get_first_context_rule(env, &cr);
	while (r != NULL) {
        if (!r->rule_simplified) {
            //printf("Adding %x %s\n", r, _th_print_exp(r));
            a = (struct parent_list *)_th_alloc(CHECK_SPACE,sizeof(struct parent_list));
            a->next = ret;
            ret = a;
#ifdef XX
            if (r->u.appl.args[2]==_ex_true) {
                if (r->u.appl.args[1]==_ex_false) {
                    r = _ex_intern_appl1_env(env,INTERN_NOT,_th_unmark_vars(env,r->u.appl.args[0]));
                } else if (r->u.appl.args[1]==_ex_true) {
                    r = _th_unmark_vars(env,r->u.appl.args[0]);
                } else {
                    r = _th_unmark_vars(env,_ex_intern_appl2_env(env,INTERN_EQUAL,r->u.appl.args[0],r->u.appl.args[1]));
                }
            } else {
                r = _th_unmark_vars(env,r);
            }
#endif
            a->split = r;
        } else {
            //printf("Simplified %x %s\n", r, _th_print_exp(r));
        }
        r = _th_get_next_rule(env,&cr);
    }
    _th_clear_simplified(env);

    //ret = _th_add_equalities(ret, env);

    return ret;
}

static int do_restart = 0;

static int do_backjump = 0;

static struct term_list *add_equalities(struct env *env, struct term_list *list)
{
    struct add_list *al = _th_collect_restricted_equalities(env);

    while (al != NULL) {
        struct term_list *l = list;
        struct term_list *n;
        while (l != NULL) {
            if (l->e==al->e) goto cont;
            l = l->next;
        }
        n = (struct term_list *)_th_alloc(REWRITE_SPACE,sizeof(struct term_list));
        n->next = list;
        list = n;
        n->count = n->total_count = 0;
        n->dependencies = n->neg_dependencies = NULL;
        n->e = al->e;
cont:
        al = al->next;
    }

    return list;
}

static int all_unates(struct parent_list *l)
{
    while (l) {
        if (!l->unate) return 0;
        l = l->next;
    }
    return 1;
}
static int backjump_place(struct env *env, struct learn_info *info, struct parent_list *p)
{
#ifdef OLD
    int lc;
    _tree_print_exp("Checking backjump place", p->split);
    lc = _th_learn_score(env,info,p->split,p->next);
    _tree_print1("learn score %d", lc);
    if (lc>0) return 0;
    p = p->next;
    while (p && !all_unates(p)) {
        if (!p->unate) {
            lc = _th_learn_score(env,info,p->split,p->next);
            _tree_print_exp("exp", p->split);
            _tree_print1("learn score %d", lc);
            if (lc==0) return 0;
        }
        p = p->next;
    }

    return 1;
#endif
    //p = p->next;
    //while (p && p->unate) {
    //    p = p->next;
    //}
    return !(p->unate) && p->used_in_learn;
}

static int no_backjump_place(struct env *env, struct learn_info *info, struct parent_list *p)
{
#ifdef OLD
    while (p && !all_unates(p)) {
        if (!p->unate &&_th_learn_score(env,info,p->split,p->next)==0) return 0;
        p = p->next;
    }

    return 1;
#endif
    p = p->next;
    while (p) {
        if (!p->unate && !p->used_in_learn) return 0;
        p = p->next;
    }
    return 1;
}

static int decision_level = 0;

struct type_term_list {
    struct type_term_list *next;
    struct _ex_intern *e, *type;
};

static struct type_term_list *collect_subterms(struct env *env, struct _ex_intern *e, struct type_term_list *rest)
{
    struct type_term_list *a;
    int i;

    if (e->user1==NULL) {
        struct _ex_intern *t;
        a = (struct type_term_list *)_th_alloc(REWRITE_SPACE,sizeof(struct type_term_list));
        a->next = rest;
        a->e = e;
        rest = a;
        e->user1 = (struct _ex_intern *)a;
        switch (e->type) {
            case EXP_VAR:
                a->type = _th_get_var_type(env,e->u.var);
                break;
            case EXP_APPL:
                t = _th_get_type(env,e->u.appl.functor);
                a->type = t->u.appl.args[1];
                for (i = 0; i < e->u.appl.count; ++i) {
                    rest = collect_subterms(env, e->u.appl.args[i], rest);
                }
                break;
            case EXP_INTEGER:
                a->type = _ex_int;
                break;
            case EXP_RATIONAL:
                a->type = _ex_real;
                break;
        }
    }

    return rest;
}

static struct type_term_list *collect_terms(struct env *env, struct term_list *terms)
{
    struct type_term_list *a = NULL;

    while (terms) {
        a = collect_subterms(env,terms->e,a);
        terms = terms->next;
    }

    return a;
}

static struct term_list *collect_equalities(struct env *env, struct term_list *terms)
{
    struct type_term_list *tl = collect_terms(env,terms);
    struct type_term_list *t = tl;
    struct term_list *nterms = NULL, *nt;

    while (t) {
        t->e->user1 = NULL;
        t = t->next;
    }

    while (tl) {
        t = tl->next;
        while (t) {
            if ((t->e->type != EXP_APPL || t->e->u.appl.functor != INTERN_EQUAL) &&
                (tl->e->type != EXP_APPL || tl->e->u.appl.functor != INTERN_EQUAL)) {
                //printf("testing %s\n", _th_print_exp(t->e));
                //printf("    and %s\n", _th_print_exp(tl->e));
                if ((t->e->type==EXP_VAR || tl->e->type==EXP_VAR) &&
                    t->type==tl->type) {
                    nt = (struct term_list *)_th_alloc(HEURISTIC_SPACE,sizeof(struct term_list));
                    //printf("*** ADDING\n");
                    nt->next = nterms;
                    nt->count = nt->total_count = 0;
                    nt->dependencies = nt->neg_dependencies = NULL;
                    nt->e = _ex_intern_appl2_env(env,INTERN_EQUAL,t->e,tl->e);
                    nterms = nt;
                }
            }
            t = t->next;
        }
        tl = tl->next;
    }

    return nterms;
}

static struct term_list *eq_list = NULL;

static int is_legal_term(struct env *env, struct _ex_intern *e)
{
    int i;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor < INTERN_EE) return 0;
            for (i = 0; i < e->u.appl.count; ++i) {
                if (!is_legal_term(env,e->u.appl.args[i])) return 0;
            }
            return 1;
        case EXP_VAR:
            return _th_get_var_type(env,e->u.var) != NULL;
        case EXP_INTEGER:
        case EXP_RATIONAL:
            return 1;
        default:
            return 0;
    }
}

static struct _ex_intern *find_equality(struct env *env)
{
    struct _ex_intern *e1, *e2, *eq, *t1, *t2;

    e1 = _ex_get_first_term();
    while (e1) {
        //printf("    Testing %s\n", _th_print_exp(e1));
        if (is_legal_term(env,e1)) {
            //printf("        is legal\n");
            e2 = _ex_get_first_term();
            while (e2) {
                if (e1 != e2 && is_legal_term(env,e2)) {
                    switch (e1->type) {
                        case EXP_VAR:
                            t1 = _th_get_var_type(env,e1->u.var);
                            break;
                        case EXP_APPL:
                            t1 = _th_get_type(env,e1->u.appl.functor);
                            if (t1) t1 = t1->u.appl.args[1];
                            break;
                        case EXP_INTEGER:
                            t1 = _ex_int;
                            break;
                        case EXP_RATIONAL:
                            t1 = _ex_real;
                            break;
                        default:
                            t1 = NULL;
                    }
                    switch (e2->type) {
                        case EXP_VAR:
                            t2 = _th_get_var_type(env,e2->u.var);
                            break;
                        case EXP_APPL:
                            t2 = _th_get_type(env,e2->u.appl.functor);
                            if (t2) t2 = t2->u.appl.args[1];
                            break;
                        case EXP_INTEGER:
                            t2 = _ex_int;
                            break;
                        case EXP_RATIONAL:
                            t2 = _ex_real;
                            break;
                        default:
                            t2 = NULL;
                    }
                    if (t1==t2 && t1 != NULL) {
                        eq = _ex_find_equality(e1,e2);
                        if (eq != NULL) {
                            while (eq->find && eq->find != eq) {
                                eq = eq->find;
                            }
                            while (eq->rewrite && eq->rewrite != eq) {
                                eq = eq->rewrite;
                            }
                        }
                        if (eq != _ex_true && eq != _ex_false) {
                            return eq;
                        }
                    }
                }
                e2 = e2->next_term;
            }
        }
        e1 = e1->next_term;
    }

    return NULL;
}

struct _ex_intern *theorem;

static void check_theorem(struct env *env)
{
    int i, j, have_false;

    if (theorem->type != EXP_APPL || theorem->u.appl.functor != INTERN_OR) return;

    for (i = 0; i < theorem->u.appl.count; ++i) {
        struct _ex_intern *e = theorem->u.appl.args[i];
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_AND) {
            have_false = 0;
            for (j = 0; j < e->u.appl.count; ++j) {
                struct _ex_intern *f = e->u.appl.args[j];
                struct _ex_intern *g;
                struct _ex_intern *test = _ex_false;
                if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NOT) {
                    f = f->u.appl.args[0];
                    test = _ex_true;
                }
                g = f;
                while (g->rewrite && g->rewrite != g) g = g->rewrite;
                if (g==test) have_false = 1;
                //if (g!=_ex_true && g!=_ex_false) {
                //    _tree_print2("Incomplete model %d %d", i, j);
                //    _tree_indent();
                //    _tree_print_exp("disjunct", e);
                //    _tree_print_exp("term", f);
                //    _tree_print_exp("rewrite", g);
                //    _tree_undent();
                //}
            }
            if (!have_false) {
                _tree_print1("Pos %d", i);
                _tree_print_exp("No false in", e);
                _tree_indent();
                for (j = 0; j < e->u.appl.count; ++j) {
                    struct _ex_intern *f = e->u.appl.args[j];
                    struct _ex_intern *g = f;
                    while (g->rewrite && g != g->rewrite) g = g->rewrite;
                    _tree_print1("pos %d", j);
                    _tree_print_exp("term", f);
                    _tree_print_exp("rew", g);
                }
                _tree_undent();
            }
        } else {
            struct _ex_intern *f;
            struct _ex_intern *test = _ex_false;
            if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                e = e->u.appl.args[0];
                test = _ex_true;
            }
            f = e;
            while (f->rewrite && f != f->rewrite) {
                f = f->rewrite;
            }
            if (f != test) {
                _tree_print1("Pos failure %d", i);
                _tree_indent();
                _tree_print_exp("term", e);
                _tree_print_exp("reduces to", f);
                _tree_undent();
            }
        }
    }
}

//static struct _ex_intern *x_88;
//static struct _ex_intern *rl;

//struct _ex_intern *gtest = NULL;
//struct _ex_intern *gtest2 = NULL;

static int is_equality(struct _ex_intern *e)
{
    if (e->type != EXP_APPL) return 0;

    if (e->u.appl.functor != INTERN_EQUAL) return 0;

    if (e->u.appl.args[0]->type != EXP_VAR && e->u.appl.args[1]->type != EXP_VAR) return 0;

    return 1;
}

static struct _ex_intern *de_trail;

static struct _ex_intern *de(struct env *env, struct _ex_intern *v, struct _ex_intern *rep, struct _ex_intern *e)
{
    int i;
    struct _ex_intern **args;
    struct _ex_intern *r;

    if (e==v) return rep;

    if (e->type != EXP_APPL) return e;

    if (e->user2) return e->user2;

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
    for (i = 0; i < e->u.appl.count; ++i) {
        args[i] = de(env,v,rep,e->u.appl.args[i]);
    }

    r = _ex_intern_appl_equal_env(env,e->u.appl.functor,i,args,e->type_inst);

    e->next_cache = de_trail;
    de_trail = e;
    e->user2 = r;

    return r;
}

static struct _ex_intern *delete_equality(struct env *env, struct _ex_intern *v, struct _ex_intern *rep, struct _ex_intern *e)
{
    struct _ex_intern *r;

    de_trail = NULL;

    r = de(env,v,rep,e);

    while (de_trail) {
        e = de_trail;
        de_trail = de_trail->next_cache;
        e->user2 = NULL;
    }

    return r;
}

static void ce(struct _ex_intern *e)
{
    int i;

    if (e->type != EXP_APPL) return;

    if (e->user2) return;

	if (e->u.appl.functor==INTERN_EQUAL && e->type_inst==NULL) {
		printf("Illegal term: %s\n", _th_print_exp(e));
		exit(1);
	}

    for (i = 0; i < e->u.appl.count; ++i) {
        ce(e->u.appl.args[i]);
    }

    e->next_cache = de_trail;
    de_trail = e;
    e->user2 = e;
}

static void check_equality(struct _ex_intern *e)
{
    de_trail = NULL;

    ce(e);

    while (de_trail) {
        e = de_trail;
        de_trail = de_trail->next_cache;
        e->user2 = NULL;
    }
}

static struct parent_list *trail;
static struct _ex_intern *res;

static struct add_list *delete_equalities(struct env *env, struct add_list *un, struct _ex_intern *e, struct learn_info *info)
{
    struct add_list *pun, *run, *a;
    struct parent_list *p;
    int change = 0;

    _tree_print0("Processing equalities");
    _tree_indent();

#ifndef FAST
    pun = un;
    _zone_print("Unates before");
    _tree_indent();
    while (pun) {
        _zone_print_exp("un", pun->e);
        pun = pun->next;
    }
    _tree_undent();
#endif

    res = e;
    run = un;
    pun = NULL;

    while (un) {
        if (is_equality(un->e)) {
            struct _ex_intern *v, *rep;
            _tree_print_exp("eq", un->e);
            if (un->e->u.appl.args[0]->type==EXP_VAR) {
                v = un->e->u.appl.args[0];
                rep = un->e->u.appl.args[1];
            } else {
                v = un->e->u.appl.args[1];
                rep = un->e->u.appl.args[0];
            }
            if (!_th_is_free_in(rep,v->u.var)) {
                change = 1;
                _tree_indent();
                _zone_print_exp("Replacing", v);
                _zone_print_exp("with", rep);
                _tree_undent();
                if (pun) {
                    pun->next = un->next;
                } else {
                    run = un->next;
                }
                a = run;
                while (a) {
                    a->e = delete_equality(env,v,rep,a->e);
                    a = a->next;
                }
                p = trail;
                while (p) {
                    p->split = delete_equality(env,v,rep,p->split);
                    p = p->next;
                }
                res = delete_equality(env,v,rep,res);
                _th_elim_var(env,info,v->u.var,rep);
            }
        }
        pun = un;
        un = un->next;
    }

    if (change) {
        _zone_print0("Rewrites");
        _tree_indent();
        res = _th_nc_rewrite(env,res);
        un = run;
        while (un) {
            un->e = _th_nc_rewrite(env,un->e);
            un = un->next;
        }
        p = trail;
        while (p) {
            p->split = _th_nc_rewrite(env,p->split);
            p = p->next;
        }
        _tree_undent();
#ifndef FAST
        pun = un;
        _zone_print("Unates after");
        _tree_indent();
        while (pun) {
            _zone_print_exp("un", pun->e);
            pun = pun->next;
        }
        _tree_undent();
#endif
        _tree_undent();
        return delete_equalities(env,run,res,info);
    } else {
        _tree_undent();
        return run;
    }
}

int _th_equality_only = 0;

static void c_and_print(struct env *env, struct _ex_intern *e, char *n)
{
    char name[30];
    static int nc = 0;
    sprintf(name, "%s%d.out", n, nc++);
    _th_print_state(env,trail,NULL,_ex_intern_appl1_env(env,INTERN_NOT,e),fopen(name,"w"),_th_get_name(),_th_get_status_name(),_th_get_logic_name());
}

/*#define PUSH_COUNT*/

static struct _ex_intern *preprocess(struct env *env, struct _ex_intern *e, struct parent_list *p, struct fail_list *fl, struct learn_info *learn, struct term_list *list, int ld)
{
	struct _ex_intern *split, *ps;
    char *mark;
#ifndef FAST
    struct parent_list *at;
#endif
    struct parent_list *p2, *porig;
    struct add_list *un, *u;
    int i;
#ifndef FAST
    int initial_indent = _tree_get_indent();
#endif

#ifdef PUSH_COUNT
    int pc = _th_push_count(env);
#endif

    //c_and_print(env,e,"preprocess");
    //_th_yices_ce_value(env,e);

    mark = _th_alloc_mark(REWRITE_SPACE);

    _zone_increment();
    ++_th_block_complex;
    _tree_print2("Preprocessing %d %s", _tree_zone, _th_print_exp(e));
    --_th_block_complex;
	_tree_indent();

    if (e==_ex_true) {
    	_tree_undent();
        _th_alloc_release(REWRITE_SPACE,mark);
		_tree_print0("Solved");
#ifdef PUSH_COUNT
        if (pc != _th_push_count(env)) {
            fprintf(stderr, "Push count error 1\n");
            exit(1);
        }
#endif
#ifndef FAST
        if (_tree_get_indent() != initial_indent) {
            fprintf(stderr, "Indents do not align 1 %d %d\n", _tree_get_indent(), initial_indent);
            exit(1);
        }
#endif
        trail = p;
        _th_alloc_release(REWRITE_SPACE,mark);
        return e;
	}

#ifndef FAST
    if (_zone_active()) {
        _tree_print0("Reductions");
        _tree_indent();
        at = add_reductions(env);
        while (at != NULL) {
            _tree_print_exp("term", at->split);
            at = at->next;
        }
        _tree_undent();
    }
    //_th_print_equality_info(env);
#endif

    _th_update_dependency_table(env, (e != _ex_false));
        
    //_th_get_dependency_cache();

    if (_th_do_unate && e != _ex_false && e != _ex_true) {
#ifndef FAST
        if (_zone_active()) {
            struct term_list *l = list;
            _tree_print0("terms");
            _tree_indent();
            while (l) {
                struct dependencies *d = l->dependencies;
                _tree_print_exp("t", l->e);
                _tree_indent();
                if (d) {
                    _tree_print0("dependencies");
                    _tree_indent();
                    while (d) {
                        _tree_print_exp("d", d->term->e);
                        _tree_print_exp("reduction", d->reduction);
                        d = d->next;
                    }
                    _tree_undent();
                }
                d = l->neg_dependencies;
                if (d) {
                    _tree_print0("neg dependencies");
                    _tree_indent();
                    while (d) {
                        _tree_print_exp("d", d->term->e);
                        _tree_print_exp("reduction", d->reduction);
                        d = d->next;
                    }
                    _tree_undent();
                }
                _tree_undent();
                l = l->next;
            }
            _tree_undent();
        }
#endif

        //check_cycle(env, "unate 1");
        un = _th_eliminate_unates(env,e,list);
        
        while (un && term_used(p,un->e)) {
            un = un->next;
        }

        //check_cycle(env, "unate 2");
        if (un) {
            struct parent_list *pp = p;
#ifdef XX
            if (_th_equality_only) {
                trail = p;
                un = delete_equalities(env,un,e,learn);
                return res;
            } else {
                un = delete_equalities(env,un,_th_reduced_exp,learn);
                _th_reduced_exp = res;
            }
#endif
            while (pp) {
                //_tree_print_exp("Parent", pp->split);
                pp->used_in_learn = 0;
                pp = pp->next;
            }
            ++_th_block_complex;
            _tree_print_exp("Reduced", _th_reduced_exp);
            --_th_block_complex;
            if (_th_reduced_exp->type==EXP_APPL && _th_reduced_exp->u.appl.functor==INTERN_OR) {
                for (i = 0; i < _th_reduced_exp->u.appl.count; ++i) {
                    struct _ex_intern *f = _th_reduced_exp->u.appl.args[i];
                    if (f->type != EXP_APPL || (f->u.appl.functor != INTERN_AND &&
                        f->u.appl.functor != INTERN_NOT && f->u.appl.functor != INTERN_OR &&
                        f->u.appl.functor != INTERN_ITE &&
                        (f->u.appl.functor!=INTERN_EQUAL || !_th_is_boolean_term(env,f->u.appl.args[0])))) {
                        //printf("New term 1 %s\n", _th_print_exp(f));
                        _th_new_term(f);
                    } else if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NOT) {
                        f = f->u.appl.args[0];
                        if (f->type != EXP_APPL || (f->u.appl.functor != INTERN_AND &&
                            f->u.appl.functor != INTERN_NOT && f->u.appl.functor != INTERN_OR &&
                            f->u.appl.functor != INTERN_ITE &&
                            (f->u.appl.functor!=INTERN_EQUAL || !_th_is_boolean_term(env,f->u.appl.args[0])))) {
                            //printf("New term 2 %s\n", _th_print_exp(f));
                            _th_new_term(f);
                        }
                    }
                }
            }

            _tree_print0("Eliminated the following unates:");
            _tree_indent();
            u = un;
            while (u) {
                _tree_print_exp("unate", u->e);
                //if (term_used(p,u->e)) {
                //    _tree_indent();
                //    _tree_print("Already done");
                //    _tree_undent();
                //}
                u = u->next;
            }
            _tree_undent();
            if (_th_reduced_exp==_ex_true) {
                //check_cycle(env, "unate 3");
                //if (new_learn && _th_do_learn) {
                //    do_backjump = _th_learn(env,learn,p,list,1);
                //    if (do_backjump && backjump_place(env,learn,p)) do_backjump = 0;
                //}
                _tree_print0("Reduced to true");
                _tree_undent();
                _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
                if (pc != _th_push_count(env)) {
                    fprintf(stderr, "Push count error 9\n");
                    exit(1);
                }
#endif
#ifndef FAST
                if (_tree_get_indent() != initial_indent) {
                    fprintf(stderr, "Indents do not align 8 %d %d\n", _tree_get_indent(), initial_indent);
                    exit(1);
                }
#endif
                u = un;
                while (u) {
                    p2 = (struct parent_list *)_th_alloc(CHECK_SPACE,sizeof(struct parent_list));
                    p2->next = p;
                    p = p2;
                    p->exp = e;
                    p->split = u->e;
                    p->used_in_learn = 0;
                    p->rhs = 1;
                    p->unate = 2;
                    ++unate_count;
                    ++split_count;
                    u = u->next;
                }
                trail = p;
                _th_alloc_release(REWRITE_SPACE,mark);
                return _ex_true;
            } else {
                int all_vars = 1;
                u = un;
                porig = p;
                _tree_print0("Processing unates");
                _tree_indent();
                while (u) {
                    struct _ex_intern *f;
                    //if (has_positive_cycle(env) || has_bad_model(env,p)) {
                    //    dump_state(env,p);
                    //    fprintf(stderr, "Undetected cycle\n");
                    //    exit(1);
                    //}
                    //check_cycle(env, "unate 4");
                    _zone_print_exp("*** SIMPLIFYING", u->e);
                    u->e = _th_simp(env,u->e);
                    _zone_print_exp("TO", u->e);
                    if (u->e->type==EXP_VAR ||
                        (u->e->u.appl.functor==INTERN_NOT && u->e->u.appl.count==1 && u->e->u.appl.args[0]->type==EXP_VAR)) {
                        f = u->e;
                        while (f->find != f) f = f->find;
                    } else {
                        all_vars = 0;
                        f = _th_simp(env,u->e);
                    }
                    _zone_print_exp("f", f);
                    if (f != _ex_true) {
                        p2 = (struct parent_list *)_th_alloc(CHECK_SPACE,sizeof(struct parent_list));
                        p2->next = p;
                        p = p2;
                        p->exp = e;
                        p->used_in_learn = 0;
                        p->rhs = 1;
                        p->unate = 2;
                        ++unate_count;
                        ++split_count;
                        p->split = f;
                        if (f==_ex_false) {
                            _tree_print0("Unate elimination");
                            _tree_undent();
                            _tree_undent();
                            _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
                            if (pc != _th_push_count(env)) {
                                fprintf(stderr, "Push count error 10\n");
                                exit(1);
                            }
#endif
#ifndef FAST
                            if (_tree_get_indent() != initial_indent) {
                                fprintf(stderr, "Indents do not align 9\n");
                                exit(1);
                            }
#endif
                            trail = p;
                            _th_alloc_release(REWRITE_SPACE,mark);
                            return _ex_false;
                        } else if (_th_assert_predicate(env,f)) {
                            _tree_print0("Unate contradiction");
                            _tree_undent();
                            _tree_undent();
                            _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
                            if (pc != _th_push_count(env)) {
                                fprintf(stderr, "Push count error 11\n");
                                exit(1);
                            }
#endif
#ifndef FAST
                            if (_tree_get_indent() != initial_indent) {
                                fprintf(stderr, "Indents do not align 10\n");
                                exit(1);
                            }
#endif
                            trail = p;
                            _th_alloc_release(REWRITE_SPACE,mark);
                            return _ex_true;
                        }
                    }
                    u = u->next;
                    while (u != NULL && term_used(p,u->e)) {
                        _zone_print_exp("SKIPPING", u->e);
                        u = u->next;
                    }
                }
                _tree_undent();
                _tree_print0("Proving reduced expression");
                trail = p;
                //c_and_print(env,_th_reduced_exp,"before_simp");
                //_th_yices_ce_value(env,_th_reduced_exp);
                if (!all_vars) {
                    ps = _th_reduced_exp;
                    split = _th_reduced_exp = _th_simp(env,_th_reduced_exp);
                }
                ++decision_level;
                split = preprocess(env,_th_reduced_exp, p, fl,learn, list, 2);
                --decision_level;
                _tree_undent();
                _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
                if (pc != _th_push_count(env)) {
                    fprintf(stderr, "Push count error 12\n");
                    exit(1);
                }
#endif
#ifndef FAST
                if (_tree_get_indent() != initial_indent) {
                    fprintf(stderr, "Indents do not align 11\n");
                    exit(1);
                }
#endif
                _th_alloc_release(REWRITE_SPACE,mark);
                return split;
            }
        }
    }

#ifdef XX
    switch (_th_score_mode) {
        case 0:
            split = _th_first_choose_case(env,e,list,info);
            break;
        case 1:
            split = _th_choose_case(env,e);
            break;
        case 2:
            //splits = p;
            if (e==_ex_true || e==_ex_false) {
                split = _th_learn_choose(env,info,parents);
            } else {
                split = _th_fast_choose_case(env,e,list,info,p);
            }
            //splits = NULL;
            break;
    }

    at = (struct parent_list *)_th_alloc(CHECK_SPACE,sizeof(struct parent_list));
    at->next = p;
    at->split = split->u.case_stmt.exp;
    at->used_in_learn = 0;
    at->exp = e;
    af = (struct parent_list *)_th_alloc(CHECK_SPACE,sizeof(struct parent_list));
    af->next = p;
    af->used_in_learn = 0;
    af->split = _ex_intern_appl1_env(env,INTERN_NOT,split->u.case_stmt.exp);
    af->exp = e;

    at->unate = 0;
    af->unate = 0;
#endif

  	_tree_undent();
    _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
    if (pc != _th_push_count(env)) {
        fprintf(stderr, "Push count error 15\n");
        exit(1);
    }
#endif
#ifndef FAST
    if (_tree_get_indent() != initial_indent) {
        fprintf(stderr, "Indents do not align 14\n");
        exit(1);
    }
#endif

    trail = p;
    _th_alloc_release(REWRITE_SPACE,mark);
	return e;
}

int _th_do_domain_score = 0;

static struct _ex_intern *special_simp(struct env *env, struct _ex_intern *e)
{
	if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_RAT_PLUS || e->u.appl.functor==INTERN_RAT_LESS)) {
		struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
		int i;
		for (i = 0; i < e->u.appl.count; ++i) {
			args[i] = special_simp(env,e->u.appl.args[i]);
		}
		return _ex_intern_appl_env(env,e->u.appl.functor,i,args);
	}
	while (e->find && e->find != e) e = e->find;
	return e;
}

static void check_trail(struct env *env, struct parent_list *p)
{
	struct add_list *al;
    int i = 1;
    struct _ex_intern *t = _ex_true;
	struct _ex_intern *f = _ex_false;
    struct _ex_intern *tm = _ex_true;
	struct _ex_intern *fm = _ex_false;
    struct parent_list *pp = p;
    extern int print_cc;
    struct _ex_intern *left = _th_left;
	struct _ex_intern *right = _th_right;
	struct _ex_intern *diff = _th_diff;
	int delta = _th_delta;
#ifdef PRINT1
	extern struct _ex_intern *add_left, *add_right, *add_e;
	struct _ex_intern *ale = add_left, *ar = add_right, *ae = add_e;
#endif

	_zone_print0("Check trail\n");
	_tree_indent();

	while (tm->merge) tm = tm->merge;
	while (fm->merge) fm = fm->merge;

	if (tm==fm) {
		i = 0;
		fprintf(stderr, "_ex_true and _ex_false merged\n");
		t = _ex_true;
		f = _ex_false;
		while (t) {
			fprintf(stderr, "t %s\n", _th_print_exp(t));
			t = t->merge;
		}
		while (f) {
			fprintf(stderr, "f %s\n", _th_print_exp(f));
			f = f->merge;
		}
	} else {
		while (p) {
			_zone_print1("split %s", _th_print_exp(p->split));
			if (p->split->type==EXP_APPL && p->split->u.appl.functor==INTERN_NOT) {
				struct _ex_intern *e = p->split->u.appl.args[0];
				struct _ex_intern *f;
				if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_LESS) {
					//while (e->find && e->find != e && e->find->type==EXP_APPL && e->find->u.appl.functor==INTERN_RAT_LESS) {
					//	e = e->find;
					//}
					e = _ex_intern_appl2_env(env,INTERN_RAT_LESS,_th_simp(env,e->u.appl.args[0]),_th_simp(env,e->u.appl.args[1]));
					f = _th_check_cycle_rless(env,e,&al);
					if (_th_int_rewrite(env,e,0)==e && f!=_ex_false) {
						fprintf(stderr, "check cycles rless failure %s\n", _th_print_exp(p->split));
						fprintf(stderr, "e = %s\n", _th_print_exp(e));
						fprintf(stderr, "f = %s\n", _th_print_exp(f));
						fprintf(stderr, "left = %s\n", _th_print_exp(_th_left));
						fprintf(stderr, "right = %s\n", _th_print_exp(_th_right));
						fprintf(stderr, "diff = %s\n", _th_print_exp(_th_diff));
						fprintf(stderr, "delta = %d\n", delta);
#ifdef PRINT1
						fprintf(stderr, "add_left = %s\n", _th_print_exp(ale));
						fprintf(stderr, "add_right = %s\n", _th_print_exp(ar));
						fprintf(stderr, "add_e = %s\n", _th_print_exp(ae));
						print_cc = 1;
						_th_check_cycle_rless(env,e,&al);
#endif
                        i = 0;
					}
				}
				f = p->split->u.appl.args[0];
				while (f->find && f->find != f) {
					f = f->find;
				}
				if (f != _ex_false) {
					fprintf(stderr, "Unverified term 1 %s\n", _th_print_exp(p->split));
					fprintf(stderr, "%s\n", _th_print_exp(e));
					f = p->split->u.appl.args[0];
					while (f->find) {
						fprintf(stderr, "%s\n", _th_print_exp(f->find));
						f = f->find;
					}
					i = 0;
				}
			} else {
				struct _ex_intern *e = p->split;
				struct _ex_intern *f;
				if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_LESS) {
					//while (e->find && e->find != e && e->find->type==EXP_APPL && e->find->u.appl.functor==INTERN_RAT_LESS) {
					//	e = e->find;
					//}
					e = _ex_intern_appl2_env(env,INTERN_RAT_LESS,_th_simp(env,e->u.appl.args[0]),_th_simp(env,e->u.appl.args[1]));
					f = _th_check_cycle_rless(env,e,&al);
					if (_th_int_rewrite(env,e,0)==e && f!=_ex_true) {
						fprintf(stderr, "check cycles rless failure %s\n", _th_print_exp(p->split));
						fprintf(stderr, "e = %s\n", _th_print_exp(e));
						fprintf(stderr, "f = %s\n", _th_print_exp(f));
						fprintf(stderr, "left find %s\n", _th_print_exp(e->u.appl.args[0]->find));
						fprintf(stderr, "right find %s\n", _th_print_exp(e->u.appl.args[1]->find));
						fprintf(stderr, "left = %s\n", _th_print_exp(_th_left));
						fprintf(stderr, "right = %s\n", _th_print_exp(_th_right));
						fprintf(stderr, "diff = %s\n", _th_print_exp(_th_diff));
						fprintf(stderr, "delta = %d\n", delta);
#ifdef PRINT1
						fprintf(stderr, "add_left = %s\n", _th_print_exp(ale));
						fprintf(stderr, "add_right = %s\n", _th_print_exp(ar));
						fprintf(stderr, "add_e = %s\n", _th_print_exp(ae));
						print_cc = 1;
						printf("**** CC for %s ***\n", _th_print_exp(e));
						_th_check_cycle_rless(env,e,&al);
						print_cc = 0;
#endif
                        i = 0;
					}
				}
				e = p->split;
				while (e->find && e->find != e) {
					e = e->find;
				}
				if (e != _ex_true) {
					fprintf(stderr, "Unverified term 2 %s\n", _th_print_exp(p->split));
					fprintf(stderr, "%s\n", _th_print_exp(e));
					i = 0;
				}
			}
			p = p->next;
		}
	}

	_tree_undent();
	_zone_print0("End check trail\n");

	if (i==0) {
		_th_display_difference_table(env);
		printf("Parents:\n");
		while (pp) {
			printf("    %s\n", _th_print_exp(pp->split));
			pp = pp->next;
		}
	}
	i = 1/i;
}

struct fail_list *prove(struct env *env, struct _ex_intern *e, struct parent_list *p, struct fail_list *fl, struct learn_info *learn, struct term_list *list, int ld)
{
	struct _ex_intern *split, *ps;
    char *mark, *emark, *rmark;
    struct parent_list *at, *af, *p2, *porig;
    struct fail_list *fl1;
    struct add_list *un, *u;
    struct mark_info *minfo;
    //struct rule *cr;
    //struct _ex_intern *r, *rt;
    struct _ex_intern *rt;
    int learn_domain, i;
#ifndef FAST
    int initial_indent = _tree_get_indent();
#endif
    //extern void check_integrity(struct env *env, char *place);
    extern int has_positive_cycle(struct env *env);
    //static struct _ex_intern *test = NULL, *test2 = NULL;
    //static struct _ex_intern *t1, *t2, *t3;

#ifdef PUSH_COUNT
    int pc = _th_push_count(env);
#endif

	//check_trail(env,p);

	//printf("Prove\n");

#ifdef XX
    if (test==NULL) {
        struct add_list *al;
        if (t1==NULL) {
            t1 = _th_parse(env, "x_7");
            t2 = _th_parse(env, "x_8");
            t3 = _th_parse(env, "x_6");
        }
        al = t1->used_in;
        while (al) {
            if (al->e->type==EXP_APPL && al->e->u.appl.functor==INTERN_RAT_LESS &&
                al->e->u.appl.args[0]==t1 && al->e->u.appl.args[1]==t2) {
                test = al->e;
            }
            al = al->next;
        }
        al = t1->used_in;
        while (al) {
            if (al->e->type==EXP_APPL && al->e->u.appl.functor==INTERN_RAT_LESS &&
                al->e->u.appl.args[0]==t1 && al->e->u.appl.args[1]==t3) {
                test2 = al->e;
            }
            al = al->next;
        }
    }
    //if (gtest2==NULL) {
    //    struct add_list *al;
    //    if (t1==NULL) {
    //        t1 = _th_parse(env, "x_8");
    //        t2 = _th_parse(env, "x_92");
    //    }
    //    al = t1->used_in;
    //    while (al) {
    //        if (al->e->type==EXP_APPL && al->e->u.appl.functor==INTERN_EQUAL &&
    //            al->e->u.appl.args[0]==t1 && al->e->u.appl.args[1]==t2) {
    //            test = al->e;
    //        }
    //        al = al->next;
    //    }
    //}
    //if (test && _zone_active()) gtest = test;
#endif

    //check_user2_error(info);

    //check_integrity(env, "prove");
    //printf("Here1\n");
    //fflush(stdout);

    //if (e != _ex_true) _th_collect_and_print_classes(env,1);

    //at = p;
    //while (at) {
    //    if (at->split->type==EXP_VAR) exit(1);
    //    at = at->next;
    //}
    //check_cycle(env, "enter prove");
    //check_env(env, "1");

    do_restart = (do_restart || (_th_do_learn > 0 && _th_check_restart(_th_do_learn)));
	if (do_restart) {
		//printf("End prove (restart)\n");
		return fl;
	}

    mark = _th_alloc_mark(REWRITE_SPACE);

    _zone_increment();
    //if (_th_matches_yices_ce(p)) {
    //    _tree_print("CE BRANCH");
    //}
    _tree_print2("Proving %d %s", _tree_zone, _th_print_exp(e));
	_tree_indent();
    //_th_print_trail("Trail", p);

    //if (x_88==NULL) {
    //    x_88 = _th_parse(env,"x_88");
    //    rl = _th_parse(env,"(rless x_92 x_88)");
    //}
    //_tree_print_exp("x_88->find", x_88->find);
    //_tree_print_exp("rl->find", rl->find);

    //if (test) _tree_print_exp("test->find =", test->find);
    //if (test2) _tree_print_exp("test2->find =", test2->find);

    //if (has_positive_cycle(env) || has_bad_model(env,p)) {
    //    dump_state(env,p);
    //    fprintf(stderr, "Undetected cycle\n");
    //    _tree_print0("Undetected cycle");
    //    _th_print_difference_table(env);
    //    exit(1);
    //}

    if (_th_do_learn && learn==NULL) {
        info = learn = _th_new_learn_info(env);
    }

    //if (_th_do_learn) check_explanation(env,learn,p);

    //_tree_indent();
    //if (_th_do_learn && _th_solved_case(env,learn,p)) {
    //    _tree_undent();
    //    _tree_print("Has solved case");
    //    _tree_indent();
    //}
    //_tree_undent();

    //_th_print_assignments(learn);

    //printf("Here2\n");
    //fflush(stdout);

    if (e==_ex_true) {
        //_tree_print2("Here1 %d %d", new_learn, _th_do_learn);
        if (new_learn && _th_do_learn) {
            //printf("Here2a\n");
            //fflush(stdout);
            do_backjump = _th_learn(env,learn,p,list,ld);
            //printf("Here2b\n");
            //fflush(stdout);
            //if (do_backjump && backjump_place(env,learn,p)) do_backjump = 0;
        }
    	_tree_undent();
        _th_alloc_release(REWRITE_SPACE,mark);
		_tree_print0("Solved");
#ifdef PUSH_COUNT
        if (pc != _th_push_count(env)) {
            fprintf(stderr, "Push count error 1\n");
            exit(1);
        }
#endif
#ifndef FAST
        if (_tree_get_indent() != initial_indent) {
            fprintf(stderr, "Indents do not align 1 %d %d\n", _tree_get_indent(), initial_indent);
            exit(1);
        }
#endif
        //if (_th_matches_yices_ce(p)) {
        //    //dump_state(env,p);
        //    fprintf(stderr, "Failed path\n");
        //    exit(1);
        //}
		//printf("End prove 1\n");
        return fl;
	}

    //printf("Here3\n");
    //fflush(stdout);

    if (_th_do_learn) {
        split = _th_learned_unate_case(env,info,p);

        if (split) {
            ++learned_unates;
            _tree_undent();
            _tree_print_exp("Learned unate", split);
            _tree_indent();

            //_th_derive_push(env);

            p2 = (struct parent_list *)_th_alloc(CHECK_SPACE,sizeof(struct parent_list));
            p2->next = p;
            p = p2;
            //if (split->type==EXP_APPL && split->u.appl.functor==INTERN_NOT) {
            //    split = split->u.appl.args[0];
            //} else {
            //    split = _ex_intern_appl1_env(env,INTERN_NOT,split);
            //}
            p->exp = e;
            p->used_in_learn = 0;
            p->rhs = 1;
            p->unate = 1;
            p->split = split;
            ++unate_count;
            ++split_count;
            //split = _th_abstract_condition(env,split);
            //if (test) _tree_print_exp("test->find =", test->find);
            //if (test2) _tree_print_exp("test2->find =", test2->find);
			if (split->type==EXP_APPL && split->u.appl.functor==INTERN_NOT) {
                _zone_print1("merge %s\n", _th_print_exp(split->u.appl.args[0]->merge));
			}
			//_th_print_trail("Before assert 1", p);
            if ((learn_domain = _th_add_assignment(env,learn,split,decision_level)) || (_th_learned_domain_case?0:_th_assert_predicate(env,split))) {
                _tree_print0("Learned contradiction");
                //_th_derive_pop(env);
                if (new_learn && e==_ex_false) do_backjump = _th_learn(env,info,p,list,learn_domain);
                //if (do_backjump && backjump_place(env,info,p)) do_backjump = 0;
                _th_delete_assignment(env,learn,split);
                _tree_undent();
                _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
                if (pc != _th_push_count(env)) {
                    fprintf(stderr, "Push count error 2\n");
                    exit(1);
                }
#endif
#ifndef FAST
                if (_tree_get_indent() != initial_indent) {
                    fprintf(stderr, "Indents do not align 2 %d %d\n", _tree_get_indent(), initial_indent);
                    exit(1);
                }
#endif
                //if (_th_matches_yices_ce(p)) {
                //    fprintf(stderr,"Failed path 2\n");
                //    dump_state(env,p);
                //    exit(1);
                //}
				//printf("End prove 2\n");
                return fl;
            }
            //if (test) _tree_print_exp("test->find =", test->find);
            //if (test2) _tree_print_exp("test2->find =", test2->find);
            if (!_th_learned_domain_case) e = _th_simp(env,e);
            if (e==_ex_true) {
                _tree_print0("Reduced to true\n");
                //_th_derive_pop(env);
                if (new_learn) do_backjump = _th_learn(env,info,p,list,2);
                //if (do_backjump && backjump_place(env,info,p)) do_backjump = 0;
                _th_delete_assignment(env,learn,split);
                _tree_undent();
                _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
                if (pc != _th_push_count(env)) {
                    fprintf(stderr, "Push count error 3\n");
                    exit(1);
                }
#endif
#ifndef FAST
                if (_tree_get_indent() != initial_indent) {
                    fprintf(stderr, "Indents do not align 3\n");
                    exit(1);
                }
#endif
                //if (_th_matches_yices_ce(p)) {
                //    //dump_state(env,p);
                //    fprintf(stderr,"Failed path 3\n");
                //    exit(1);
                //}
				//printf("End prove 3\n");
                return fl;
            }
            //check_env(env, "2");
            _tree_undent();
            fl1 = prove(env,e, p, fl, learn, list, 1);
            if (fl1 != fl) {
                _tree_print0("BAD Branch");
                fl = fl1;
            }
            //_th_derive_pop(env);
            _th_delete_assignment(env,learn,split);
            _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
            if (pc != _th_push_count(env)) {
                fprintf(stderr, "Push count error 4\n");
                exit(1);
            }
#endif
#ifndef FAST
            if (_tree_get_indent() != initial_indent) {
                fprintf(stderr, "Indents do not align 4\n");
                exit(1);
            }
#endif
			//printf("End prove 4\n");
            return fl;
        }
    }

    //printf("Here4\n");
    //fflush(stdout);

#ifndef FAST
    if (_zone_active()) {
        _tree_print0("Reductions");
        _tree_indent();
        at = add_reductions(env);
        while (at != NULL) {
            _tree_print_exp("term", at->split);
            at = at->next;
        }
        _tree_undent();
    }
    //_th_print_equality_info(env);
#endif

#ifdef CHECK_SOLVED_CASE
    if (_th_do_learn && learn && _th_solved_case(env,learn,p)) {
        ++solved_cases;
        _tree_print0("Solved from a learned tuple");
        fprintf(stderr, "Solved from a learned tuple\n");
        exit(1);
        //if (e==_ex_false) _th_learn(env,learn,p,list,0);
        //_tree_undent();
        //_th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
        //if (pc != _th_push_count(env)) {
        //    fprintf(stderr, "Push count error 5\n");
        //    exit(1);
        //}
#endif
        //return fl;
    }
#endif

    //printf("Here5\n");
    //fflush(stdout);
    //if (list==NULL || (_th_do_learn==0 && e != _ex_false && e != _ex_true)) {
        //if (list!=NULL) {
        //    printf("zone = %d\n", _tree_zone);
        //    printf("Here %s\n", _th_print_exp(e));
        //}
        //rt = e;
        //r = _th_get_first_context_rule(env,&cr);
        //_th_mark_simplified(env);
        //_tree_indent();
        //while (r) {
        //    if (!r->rule_simplified) {
        //        //if (x) _tree_print0("simplified");
        //        if (r->u.appl.args[2]==_ex_true) {
        //            struct _ex_intern *x = _th_int_rewrite(env,_th_unmark_vars(env,r),1);
        //            //_tree_print("Adding");
        //            if (x->type==EXP_APPL && x->u.appl.functor==INTERN_ORIENTED_RULE) {
        //                rt = _ex_intern_appl2_env(env,INTERN_AND,_th_int_rewrite(env,_th_unmark_vars(env,_ex_intern_appl2_env(env,INTERN_EQUAL,x->u.appl.args[0],x->u.appl.args[1])),0),rt);
        //            }
        //        }
        //    }
        //    r = _th_get_next_rule(env,&cr);
        //}
        //_th_clear_simplified(env);
        //_tree_undent();
        
        //if (_th_do_learn && learn) rt = _th_add_learn_terms(learn, rt);
        _th_update_dependency_table(env, (e != _ex_false));
        
        list = _th_get_dependency_cache();
        //if (!_th_use_composite_conds) list = _th_eliminate_composite_conds(env,list);
        
        //_th_fill_dependencies(env,list);

        //eq_list = collect_equalities(env,list);
    //}
    //check_cycle(env, "learned unate");

backjump_start:
    //if (test) _tree_print_exp("test->find =", test->find);
    //if (test2) _tree_print_exp("test2->find =", test2->find);

    //printf("Here6\n");
    //fflush(stdout);

    if (_th_do_learn) {
        split = _th_learned_unate_case(env,info,p);

        if (split) {
            ++learned_unates;
            _tree_undent();
            _tree_print_exp("Learned unate", split);
            _tree_indent();
            
            //_th_derive_push(env);
            p2 = (struct parent_list *)_th_alloc(CHECK_SPACE,sizeof(struct parent_list));
            p2->next = p;
            p = p2;
            if (split->type==EXP_APPL && split->u.appl.functor==INTERN_NOT) {
                p->split = split->u.appl.args[0];
            } else {
                p->split = _ex_intern_appl1_env(env,INTERN_NOT,split);
            }
            p->used_in_learn = 0;
            p->exp = e;
            p->rhs = 1;
            p->unate = 1;
            p->split = split;
            ++unate_count;
            ++split_count;
            //split = _th_abstract_condition(env,split);

            //printf("Split = %s\n", _th_print_exp(split));
			//_th_print_trail("Before assert 2", p);
            if ((learn_domain = _th_add_assignment(env,learn,split,decision_level)) || (_th_learned_domain_case?0:_th_assert_predicate(env,split))) {
                _tree_print0("Learned contradiction");
                //_th_derive_pop(env);
                //printf("Learn domain = %d\n", learn_domain);
                if (new_learn && e==_ex_false) do_backjump = _th_learn(env,info,p,list,learn_domain);
                //if (do_backjump && backjump_place(env,info,p)) do_backjump = 0;
                _th_delete_assignment(env,learn,split);
                _tree_undent();
                _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
                if (pc != _th_push_count(env)) {
                    fprintf(stderr, "Push count error 6\n");
                    exit(1);
                }
#endif
#ifndef FAST
                if (_tree_get_indent() != initial_indent) {
					fprintf(stderr, "Test2\n");
                    fprintf(stderr, "Indents do not align 5b %d %d\n", _tree_get_indent(), initial_indent);
                    exit(1);
                }
#endif
				//printf("End prove 5\n");
                return fl;
            }
            if (!_th_learned_domain_case) e = _th_simp(env,e);
            if (e==_ex_true) {
                _tree_print0("Reduced to true\n");
                //_th_derive_pop(env);
                if (new_learn) do_backjump = _th_learn(env,info,p,list,2);
                //if (do_backjump && backjump_place(env,info,p)) do_backjump = 0;
                _th_delete_assignment(env,learn,split);
                _tree_undent();
                _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
                if (pc != _th_push_count(env)) {
                    fprintf(stderr, "Push count error 7\n");
                    exit(1);
                }
#endif
#ifndef FAST
                if (_tree_get_indent() != initial_indent) {
                    fprintf(stderr, "Indents do not align 6\n");
                    exit(1);
                }
#endif
				//printf("End prove 6\n");
                return fl;
            }
            //check_env(env, "2");
            _tree_undent();
            fl1 = prove(env,e, p, fl, learn, list, 1);
            if (fl1 != fl) {
                _tree_print0("BAD Branch");
                fl = fl1;
            }
            //_th_derive_pop(env);
            _th_delete_assignment(env,learn,split);
            _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
            if (pc != _th_push_count(env)) {
                fprintf(stderr, "Push count error 8\n");
                exit(1);
            }
#endif
#ifndef FAST
            if (_tree_get_indent() != initial_indent) {
                fprintf(stderr, "Indents do not align 7\n");
                exit(1);
            }
#endif
			//printf("End prove 7\n");
            return fl;
        }
    }

    //check_cycle(env, "backjump place");
    if (_th_do_unate && e != _ex_false && e != _ex_true) {
#ifndef FAST
        if (_zone_active()) {
            struct term_list *l = list;
            _tree_print0("terms");
            _tree_indent();
            while (l) {
                struct dependencies *d = l->dependencies;
                _tree_print_exp("t", l->e);
                _tree_indent();
                if (d) {
                    _tree_print0("dependencies");
                    _tree_indent();
                    while (d) {
                        _tree_print_exp("d", d->term->e);
                        _tree_print_exp("reduction", d->reduction);
                        d = d->next;
                    }
                    _tree_undent();
                }
                d = l->neg_dependencies;
                if (d) {
                    _tree_print0("neg dependencies");
                    _tree_indent();
                    while (d) {
                        _tree_print_exp("d", d->term->e);
                        _tree_print_exp("reduction", d->reduction);
                        d = d->next;
                    }
                    _tree_undent();
                }
                _tree_undent();
                l = l->next;
            }
            _tree_undent();
        }
#endif

        //check_cycle(env, "unate 1");
        un = _th_eliminate_unates(env,e,list);
        
        while (un && term_used(p,un->e)) {
            un = un->next;
        }

        //check_cycle(env, "unate 2");
        if (un) {
            struct parent_list *pp = p;
            while (pp) {
                //_tree_print_exp("Parent", pp->split);
                pp->used_in_learn = 0;
                pp = pp->next;
            }
            _tree_print_exp("Reduced", _th_reduced_exp);
            if (_th_reduced_exp->type==EXP_APPL && _th_reduced_exp->u.appl.functor==INTERN_OR) {
                for (i = 0; i < _th_reduced_exp->u.appl.count; ++i) {
                    struct _ex_intern *f = _th_reduced_exp->u.appl.args[i];
                    if (f->type != EXP_APPL || (f->u.appl.functor != INTERN_AND &&
                        f->u.appl.functor != INTERN_NOT && f->u.appl.functor != INTERN_OR &&
                        f->u.appl.functor != INTERN_ITE &&
                        (f->u.appl.functor!=INTERN_EQUAL || !_th_is_boolean_term(env,f->u.appl.args[0])))) {
                        //printf("New term 1 %s\n", _th_print_exp(f));
                        _th_new_term(f);
                    } else if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NOT) {
                        f = f->u.appl.args[0];
                        if (f->type != EXP_APPL || (f->u.appl.functor != INTERN_AND &&
                            f->u.appl.functor != INTERN_NOT && f->u.appl.functor != INTERN_OR &&
                            f->u.appl.functor != INTERN_ITE &&
                            (f->u.appl.functor!=INTERN_EQUAL || !_th_is_boolean_term(env,f->u.appl.args[0])))) {
                            //printf("New term 2 %s\n", _th_print_exp(f));
                            _th_new_term(f);
                        }
                    }
                }
            }

            _tree_print0("Eliminated the following unates:");
            _tree_indent();
            u = un;
            while (u) {
                _tree_print_exp("unate", u->e);
                //if (term_used(p,u->e)) {
                //    _tree_indent();
                //    _tree_print("Already done");
                //    _tree_undent();
                //}
                u = u->next;
            }
            _tree_undent();
            if (_th_reduced_exp==_ex_true) {
                //check_cycle(env, "unate 3");
                //if (new_learn && _th_do_learn) {
                //    do_backjump = _th_learn(env,learn,p,list,1);
                //    if (do_backjump && backjump_place(env,learn,p)) do_backjump = 0;
                //}
                _tree_print0("Reduced to true");
                _tree_undent();
                _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
                if (pc != _th_push_count(env)) {
                    fprintf(stderr, "Push count error 9\n");
                    exit(1);
                }
#endif
#ifndef FAST
                if (_tree_get_indent() != initial_indent) {
                    fprintf(stderr, "Indents do not align 8 %d %d\n", _tree_get_indent(), initial_indent);
                    exit(1);
                }
#endif
				//printf("End prove 8\n");
                return fl;
            } else {
                struct add_list *added = NULL, *a;
                int all_vars = 1;
                u = un;
                porig = p;
                _zone_print0("Processing unates");
                _tree_indent();
                while (u) {
                    struct _ex_intern *f;
                    //if (has_positive_cycle(env) || has_bad_model(env,p)) {
                    //    dump_state(env,p);
                    //    fprintf(stderr, "Undetected cycle\n");
                    //    exit(1);
                    //}
                    //check_cycle(env, "unate 4");
                    _zone_print_exp("*** SIMPLIFYING", u->e);
                    u->e = _th_simp(env,u->e);
                    _zone_print_exp("TO", u->e);
                    if (u->e->type==EXP_VAR ||
                        (u->e->u.appl.functor==INTERN_NOT && u->e->u.appl.count==1 && u->e->u.appl.args[0]->type==EXP_VAR)) {
                        f = u->e;
                        while (f->find != f) f = f->find;
                    } else {
                        all_vars = 0;
                        f = _th_simp(env,u->e);
                    }
                    _zone_print_exp("f", f);
                    if (f != _ex_true) {
                        p2 = (struct parent_list *)_th_alloc(CHECK_SPACE,sizeof(struct parent_list));
                        p2->next = p;
                        p = p2;
                        p->exp = e;
                        p->used_in_learn = 0;
                        p->rhs = 1;
                        p->unate = 2;
                        ++unate_count;
                        ++split_count;
                        p->split = f;
                        if (f==_ex_false) {
                            while (added) {
                                if (_th_do_learn) _th_delete_assignment(env,learn,added->e);
                                added = added->next;
                            }
                            _tree_print0("Unate elimination");
                            _tree_undent();
                            _tree_undent();
                            _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
                            if (pc != _th_push_count(env)) {
                                fprintf(stderr, "Push count error 10\n");
                                exit(1);
                            }
#endif
#ifndef FAST
                            if (_tree_get_indent() != initial_indent) {
                                fprintf(stderr, "Indents do not align 9\n");
                                exit(1);
                            }
#endif
							//printf("End prove 9\n");
                            return fl;
                        } else if ((_th_do_learn?_th_add_assignment(env,learn,f,decision_level):0) || _th_assert_predicate(env,f)) {
                            if (_th_do_learn) _th_delete_assignment(env,learn,f);
                            _tree_print0("Unate contradiction");
                            //if (_th_do_learn && new_learn) {
                            //    do_backjump = _th_learn(env,info,p,list,1);
                            //    if (do_backjump && backjump_place(env,info,p)) do_backjump = 0;
                            //}
                            if (_th_do_learn) {
                                while (added) {
                                    _th_delete_assignment(env,learn,added->e);
                                    added = added->next;
                                }
                            }
                            _tree_undent();
                            _tree_undent();
                            _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
                            if (pc != _th_push_count(env)) {
                                fprintf(stderr, "Push count error 11\n");
                                exit(1);
                            }
#endif
#ifndef FAST
                            if (_tree_get_indent() != initial_indent) {
                                fprintf(stderr, "Indents do not align 10\n");
                                exit(1);
                            }
#endif
							//printf("End prove 10\n");
                            return fl;
                        }
                        a = (struct add_list *)ALLOCA(sizeof(struct add_list));
                        a->next = added;
                        a->e = f;
                        added = a;
                    }
                    u = u->next;
                    while (u != NULL && term_used(p,u->e)) {
                        u = u->next;
                    }
                }
                _tree_undent();
                _tree_print0("Proving reduced expression");
                if (!all_vars) {
                    ps = _th_reduced_exp;
                    split = _th_reduced_exp = _th_simp(env,_th_reduced_exp);
                }
#ifdef YICES
                if (_th_get_indent()==19 && _tree_zone >= 492524) {
                    struct _ex_intern *y1, *y2, *y3, *y4, *y5;
                    struct _ex_intern *s1, *s2;
                    _tree_print0("Computing Yices values");
                    _tree_indent();
                    s1 = _th_simp(env,e);
                    s2 = _th_simp(env,ps);
                    y1 = _th_yices_ce_value(env,split);
                    y2 = _th_yices_ce_value(env,e);
                    y3 = _th_yices_ce_value(env,s1);
                    y4 = _th_yices_ce_value(env,ps);
                    y5 = _th_yices_ce_value(env,s2);
                    _tree_undent();
                    _tree_print_exp("before val", y2);
                    _tree_print_exp("after val", y1);
                    _tree_print_exp("before revisited val", y3);
                    _tree_print_exp("after unsimplified val", y4);
                    _tree_print_exp("after resimplified val", y5);
                    fprintf(stderr, "Yices exit\n");
                    exit(1);
                }
#endif
                ++decision_level;
                fl1 = prove(env,_th_reduced_exp, p, fl,learn, list, 2);
                --decision_level;
                if (fl1 != fl) {
                    _zone_print_exp("original",e);
                    _zone_print_exp("reduced",split);
#ifndef FAST
                    //add_state(env,p,_ex_intern_appl1_env(env,INTERN_NOT,split),"reduced");
                    //add_state(env,porig,_ex_intern_appl1_env(env,INTERN_NOT,e),"orig");
#endif
                    _tree_print0("BAD Branch");
                    fl = fl1;
                }
                while (added) {
                    if (_th_do_learn) _th_delete_assignment(env,learn,added->e);
                    added = added->next;
                }
                _tree_undent();
                _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
                if (pc != _th_push_count(env)) {
                    fprintf(stderr, "Push count error 12\n");
                    exit(1);
                }
#endif
#ifndef FAST
                if (_tree_get_indent() != initial_indent) {
                    fprintf(stderr, "Indents do not align 11\n");
                    exit(1);
                }
#endif
				//printf("End prove 11\n");
                return fl;
            }
        }
    }

    if (learn) {
        struct _ex_intern *before = e;
        e = _th_transfer_to_learn(env,info,p,e);
        if (e==_ex_false && before != _ex_false) {
            if (_th_do_domain_score) _th_learn_add_score_dependencies(env,info);
            theorem = before;
        }
        _tree_print_exp("After transfer", e);
    }

    _tree_print1("learn term count %d", _th_learn_term_count(info));

    switch (_th_score_mode) {
        case 0:
            split = _th_first_choose_case(env,e,list,info);
            break;
        case 1:
            split = _th_choose_case(env,e);
            break;
        case 2:
            //splits = p;
            if (e==_ex_true || e==_ex_false) {
                struct _ex_intern *args[4];
                split = _th_learn_choose(env,info,p);
                if (split) {
                    //split = _th_simp(env,_th_nc_rewrite(env,split));
                    args[0] = _ex_true;
                    args[1] = e;
                    args[2] = _ex_false;
                    args[3] = e;
                    split = _ex_intern_case(split,2,args);
                }
            } else {
                split = _th_fast_choose_case(env,e,list,info,p);
            }
            //splits = NULL;
            break;
    }

    if (split==NULL) {
        struct _ex_intern *args[4];
        struct _ex_intern *x = find_equality(env);
        if (x) {
            args[0] = _ex_true;
            args[1] = e;
            args[2] = _ex_false;
            args[3] = e;
            split = _ex_intern_case(x,2,args);
            //printf("x = %s\n", _th_print_exp(x));
        }
    }

    if (split==NULL) {
		struct fail_list *f;
//#ifndef FAST
        FILE *file;
        struct parent_list *pp;
//#endif
		_tree_undent();
		_tree_print0("Failed case");
		f = (struct fail_list *)_th_alloc(CHECK_SPACE,sizeof(struct fail_list));
        f->e = e;
		f->next = fl;
        f->conditions = p;
        f->reduced_form = add_reductions(env);
//#ifndef FAST
        //_th_collect_and_print_classes(env,2);
        _th_print_difference_table(env);
		//_th_display_difference_table(env);
        _th_learn_print_assignments(info);
        //dump_state(env, p);
        file = fopen("dump.smt","w");
        _th_print_state(env,p,NULL,_ex_true,file,"dump.smt","unknown","any");
        fclose(file);
		//check_trail(env,p);
        //check_unates(learn,p,"sat");
        //print_term_assignments(learn);
        //check_integrity(env, "Failed leaf", p);
        //if (has_positive_cycle(env)) {
        //    fprintf(stderr, "Undetected cycle\n");
        //    _tree_print("Undetected cycle");
        //}
//#endif
        //check_theorem(env);
        _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
        if (pc != _th_push_count(env)) {
            fprintf(stderr, "Push count error 13\n");
            exit(1);
        }
#endif
		//check_trail(env,p->next);
#ifndef FAST
        if (_tree_get_indent() != initial_indent) {
            fprintf(stderr, "Indents do not align 12\n");
            exit(1);
        }
        _tree_print0("Inequalities");
        _tree_indent();
        pp = p;
        while (p) {
            e = p->split;
            if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_EQUAL || e->u.appl.functor==INTERN_RAT_LESS)) {
                if (e->u.appl.functor != INTERN_RAT_LESS) goto pc_1;
                _tree_print_exp("cond", p->split);
                _tree_indent();
                e = _ex_intern_appl2_env(env,e->u.appl.functor,_th_simp(env,e->u.appl.args[0]),_th_simp(env,e->u.appl.args[1]));
            } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                struct _ex_intern *f = e->u.appl.args[0];
                if (f->type==EXP_APPL && (f->u.appl.functor==INTERN_EQUAL || f->u.appl.functor==INTERN_RAT_LESS)) {
                    if (f->u.appl.functor != INTERN_RAT_LESS) goto pc_1;
                    _tree_print_exp("cond", p->split);
                    _tree_indent();
                    f = _ex_intern_appl2_env(env,f->u.appl.functor,_th_simp(env,f->u.appl.args[0]),_th_simp(env,f->u.appl.args[1]));
                    e = _ex_intern_appl1_env(env,INTERN_NOT,f);
                } else {
                    _tree_print_exp("cond", p->split);
                    _tree_indent();
                }
            } else {
                goto pc_1;
                _tree_print_exp("cond", p->split);
                _tree_indent();
            }
            _tree_undent();
            _tree_print_exp("reduced", e);
pc_1:
            p = p->next;
        }
        _tree_undent();
        _tree_print0("Negations");
        _tree_indent();
        p = pp;
        while (p) {
            e = p->split;
            if (e->type != EXP_APPL || e->u.appl.functor != INTERN_NOT ||
                e->u.appl.args[0]->type != EXP_APPL || e->u.appl.args[0]->u.appl.functor != INTERN_EQUAL) goto pc_2;
            _tree_print_exp("cond", p->split);
            _tree_indent();
            if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_EQUAL || e->u.appl.functor==INTERN_RAT_LESS)) {
                e = _ex_intern_appl2_env(env,e->u.appl.functor,_th_simp(env,e->u.appl.args[0]),_th_simp(env,e->u.appl.args[1]));
            } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                struct _ex_intern *f = e->u.appl.args[0];
                if (f->type==EXP_APPL && (f->u.appl.functor==INTERN_EQUAL || f->u.appl.functor==INTERN_RAT_LESS)) {
                    f = _ex_intern_appl2_equal_env(env,f->u.appl.functor,_th_simp(env,f->u.appl.args[0]),_th_simp(env,f->u.appl.args[1]),f->type_inst);
                    e = _ex_intern_appl1_env(env,INTERN_NOT,f);
                }
            }
            _tree_undent();
            _tree_print_exp("reduced", e);
            if (e->u.appl.args[0]->u.appl.args[0]==e->u.appl.args[0]->u.appl.args[1]) {
                _tree_print0("*** SAME ***");
            }
pc_2:
            p = p->next;
        }
        _tree_undent();
        _tree_print0("All");
        _tree_indent();
        p = pp;
        while (p) {
            e = p->split;
            _tree_print_exp("cond", p->split);
            _tree_indent();
#ifdef XX
			if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_EQUAL || e->u.appl.functor==INTERN_RAT_LESS)) {
                e = _ex_intern_appl2_equal_env(env,e->u.appl.functor,_th_simp(env,e->u.appl.args[0]),_th_simp(env,e->u.appl.args[1]),e->type_inst);
                if (e->u.appl.functor==INTERN_EQUAL && e->u.appl.args[0] != e->u.appl.args[1]) {
                    _tree_print0("Error");
                    fprintf(stderr, "Equality not properly working\n");
                    exit(1);
                }
            } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                struct _ex_intern *f = e->u.appl.args[0];
                if (f->type==EXP_APPL && (f->u.appl.functor==INTERN_EQUAL || f->u.appl.functor==INTERN_RAT_LESS)) {
                    f = _ex_intern_appl2_env(env,f->u.appl.functor,_th_simp(env,f->u.appl.args[0]),_th_simp(env,f->u.appl.args[1]));
                    e = _ex_intern_appl1_env(env,INTERN_NOT,f);
                    if (e->u.appl.functor==INTERN_EQUAL && e->u.appl.args[0] == e->u.appl.args[1]) {
                        _tree_print0("Error");
                        fprintf(stderr, "Inequality not properly working\n");
                        exit(1);
                    }
                }
            }
#endif
			_tree_undent();
            _tree_print_exp("reduced", e);
            p = p->next;
        }
        _tree_undent();
#endif
		//printf("End prove 12\n");
		return f;
    } else {
        ++split_count;
    }

    _tree_print_exp("Split", split->u.case_stmt.exp);
#ifndef FAST
	if (split->u.case_stmt.exp->type==EXP_APPL && split->u.case_stmt.exp->u.appl.functor==INTERN_EQUAL &&
		split->u.case_stmt.exp->type_inst==NULL) {
			fprintf(stderr, "Badly formed expression %s\n", _th_print_exp(split->u.case_stmt.exp));
			exit(1);
	}
    if (!split->u.case_stmt.exp->in_hash) {
        fprintf(stderr, "Case2 split not in hash table\n");
        exit(1);
    }
#endif
    //printf("Split: %s\n", _th_print_exp(split->u.case_stmt.exp));

#ifdef SPLIT_CHECK
    porig = p;
    learn_domain = 0;
    while (porig) {
        struct _ex_intern *e = porig->split;
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
            e = e->u.appl.args[0];
        }
        //_tree_print_exp("Tail", porig->split);
        if (split->u.case_stmt.exp==e) {
            fprintf(stderr, "Repeated case %s\n", _th_print_exp(e));
            exit(1);
        }
        ++learn_domain;
        porig = porig->next;
    }
    _tree_print1("split depth %d", learn_domain);
    if (learn_domain < _tree_get_indent()) {
        fprintf(stderr, "Illegal depth\n");
        exit(1);
    }
    if (learn_domain > 1200) {
        porig = p;
        while (porig) {
            printf("split = %s\n", _th_print_exp(porig->split));
            porig = porig->next;
        }
        fprintf(stderr, "Too main splits\n");
        exit(1);
    }
#endif

    at = (struct parent_list *)_th_alloc(CHECK_SPACE,sizeof(struct parent_list));
    at->next = p;
    at->split = split->u.case_stmt.exp;
    at->used_in_learn = 0;
    at->exp = e;
    af = (struct parent_list *)_th_alloc(CHECK_SPACE,sizeof(struct parent_list));
    af->next = p;
    af->used_in_learn = 0;
    af->split = _ex_intern_appl1_env(env,INTERN_NOT,split->u.case_stmt.exp);
    af->exp = e;

    at->unate = 0;
    af->unate = 0;
    if (split->u.case_stmt.args[1]==_ex_true || split->u.case_stmt.args[3]==_ex_true ||
        split->u.case_stmt.args[1]==_ex_false || split->u.case_stmt.args[3]==_ex_false) {
        struct parent_list *pp = p;
        while (pp) {
            pp->used_in_learn = 0;
            pp = pp->next;
        }
        if (_th_do_learn && new_learn && e==_ex_false) {
            if ((split->u.case_stmt.args[1]==_ex_true && split->u.case_stmt.args[0]==_ex_true) ||
                (split->u.case_stmt.args[2]==_ex_true && split->u.case_stmt.args[3]==_ex_true)) {
                _th_derive_push(env);
                _th_assert_predicate(env,at->split);
                do_backjump = _th_learn(env,learn,at,list,1);
                //if (do_backjump && backjump_place(env,learn,p)) do_backjump = 0;
                _th_derive_pop(env);
            } else if ((split->u.case_stmt.args[1]==_ex_true && split->u.case_stmt.args[0]==_ex_false) ||
                       (split->u.case_stmt.args[3]==_ex_true && split->u.case_stmt.args[2]==_ex_false)) {
                _th_derive_push(env);
                _th_assert_predicate(env,af->split);
                do_backjump = _th_learn(env,learn,af,list,1);
                //if (do_backjump && backjump_place(env,learn,p)) do_backjump = 0;
                _th_derive_pop(env);
            }
        }
    }

    if (do_backjump || do_restart) {
        //if (!do_restart && backjump_place(env,learn,at)) {
        //    _tree_print0("BACKJUMP");
        //    do_backjump = 0;
        //    goto backjump_start;
        //}
        _tree_undent();
        _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
        if (pc != _th_push_count(env)) {
            fprintf(stderr, "Push count error 14\n");
            exit(1);
        }
#endif
#ifndef FAST
        if (_tree_get_indent() != initial_indent) {
            fprintf(stderr, "Indents do not align 13\n");
            exit(1);
        }
#endif
		//printf("End prove 13\n");
        return fl;
    }

	if (split->u.case_stmt.args[0]==_ex_true &&
		split->u.case_stmt.args[2]==_ex_false) {
        at->rhs = 0;
        af->rhs = 1;
        _ex_used_in_push();
        minfo = _th_term_cache_push();
		emark = _th_alloc_mark(ENVIRONMENT_SPACE);
		rmark = _th_alloc_mark(REWRITE_SPACE);
        _th_derive_push(env);
        ++decision_level;
        if (e==_ex_true || e==_ex_false) _th_lock_table();
        rt = NULL;
        //if (split->u.case_stmt.exp->type != EXP_VAR) {
            //_th_collect_and_print_classes(env,0);
            if ((_th_do_learn?(learn_domain = _th_add_assignment(env,learn,split->u.case_stmt.exp,decision_level)):0) || _th_assert_predicate(env,split->u.case_stmt.exp)) {
                rt = _ex_true;
                _tree_print1("Assert contradiction %d", learn_domain);
            } else {
                learn_domain = 2;
            }
            //_th_collect_and_print_classes(env,rt != _ex_true);
        //}
		_tree_print0("True case 1");
		if (!rt) {
			//check_trail(env,p);
			rt = _th_simp(env,split->u.case_stmt.args[1]);
			//check_trail(env,p);
            //check_env(env, "4");
		    fl1 = prove(env, rt, at, fl, learn, list, learn_domain);
		} else {
			fl1 = fl;
		}
        if (fl1 != fl) {
            _tree_print0("BAD Branch");
#ifndef FAST
            //add_state(env,p,_ex_intern_appl1_env(env,INTERN_NOT,e),NULL);
#endif
            fl = fl1;
        //} else {
        //    _th_add_list(env,learn,at);
        }
        --decision_level;
        if (_th_do_learn) _th_delete_assignment(env,learn,split->u.case_stmt.exp);
		_th_derive_pop(env);
        _th_alloc_release(ENVIRONMENT_SPACE,emark);
        _th_alloc_release(REWRITE_SPACE,rmark);
        _th_term_cache_pop(minfo);
        _ex_used_in_pop();
        if (do_backjump && !do_restart && backjump_place(env,learn,at)) {
            //check_cycle(env, "backjump 4");
            _tree_print0("BACKJUMP");
            do_backjump = 0;
            //exit(1);
            goto backjump_start;
        }
        if (!do_restart && !do_backjump && (_th_find_all_fails || fl==NULL)) {
            _ex_used_in_push();
            minfo = _th_term_cache_push();
    		emark = _th_alloc_mark(ENVIRONMENT_SPACE);
    		rmark = _th_alloc_mark(REWRITE_SPACE);
            _th_derive_push(env);
            if (e==_ex_true || e==_ex_false) _th_lock_table();
            ++decision_level;
            rt = NULL;
            //if (split->u.case_stmt.exp->type != EXP_VAR) {
                //struct _ex_intern *e = _th_abstract_condition(env,split->u.case_stmt.exp);
                //_th_collect_and_print_classes(env,0);
                if ((_th_do_learn?(learn_domain = _th_add_assignment(env,learn,_ex_intern_appl1_env(env,INTERN_NOT,split->u.case_stmt.exp),decision_level)):0) ||
                    _th_deny_predicate(env,split->u.case_stmt.exp)) {
                    rt = _ex_true;
                    _tree_print1("Deny contradiction %d", learn_domain);
                } else {
                    learn_domain = 2;
                }
                //_th_collect_and_print_classes(env,rt != _ex_true);
            //}
            _tree_print0("False case");
			if (!rt) {
    			//check_trail(env,p);
				rt = _th_simp(env,split->u.case_stmt.args[3]);
    			//check_trail(env,p);
                //check_env(env, "5");
                fl1 = prove(env, rt, af, fl, learn, list, learn_domain);
			} else {
				fl1 = fl;
			}
            --decision_level;
            if (_th_do_learn) _th_delete_assignment(env,learn,split->u.case_stmt.exp);
            _th_derive_pop(env);
            _th_alloc_release(ENVIRONMENT_SPACE,emark);
            _th_alloc_release(REWRITE_SPACE,rmark);
            _th_term_cache_pop(minfo);
            _ex_used_in_pop();
            if (do_backjump && !do_restart && backjump_place(env,learn,af)) {
                //check_cycle(env, "backjump 4");
                _tree_print0("BACKJUMP");
                do_backjump = 0;
                //exit(1);
                goto backjump_start;
            }
            if (fl1 != fl) {
                _tree_print0("BAD Branch");
                //add_state(env,p,_ex_intern_appl1_env(env,INTERN_NOT,e),NULL);
                fl = fl1;
            }
        }
	} else if (split->u.case_stmt.args[0]==_ex_false &&
	           split->u.case_stmt.args[2]==_ex_true) {
        at->rhs = 0;
        af->rhs = 1;
        _ex_used_in_push();
        minfo = _th_term_cache_push();
        //_tree_print1("minfo %x", minfo);
		emark = _th_alloc_mark(ENVIRONMENT_SPACE);
		rmark = _th_alloc_mark(REWRITE_SPACE);
		_th_derive_push(env);
        if (e==_ex_true || e==_ex_false) _th_lock_table();
        ++decision_level;
        rt = NULL;
        //check_env(env, "6b");
        //if (split->u.case_stmt.exp->type != EXP_VAR) {
            //struct _ex_intern *e = _th_abstract_condition(env,split->u.case_stmt.exp);
            //_th_collect_and_print_classes(env,0);
            if ((_th_do_learn?(learn_domain = _th_add_assignment(env,learn,split->u.case_stmt.exp,decision_level)):0) ||
                _th_assert_predicate(env,split->u.case_stmt.exp)) {
                rt = _ex_true;
                _tree_print1("Assert contradiction %d", learn_domain);
            } else {
                learn_domain = 2;
            }
            //_th_collect_and_print_classes(env,rt != _ex_true);
        //}
   		_tree_print0("True case");
        //check_env(env, "6a");
		if (!rt) {
			//check_trail(env,p);
			rt = _th_simp(env, split->u.case_stmt.args[3]);
            //check_env(env, "6");
			//check_trail(env,p);
		    fl1 = prove(env, rt, at, fl, learn, list, learn_domain);
		} else {
			fl1 = fl;
		}
        --decision_level;
        if (_th_do_learn) _th_delete_assignment(env,learn,split->u.case_stmt.exp);
		_th_derive_pop(env);
        _th_alloc_release(ENVIRONMENT_SPACE,emark);
        _th_alloc_release(REWRITE_SPACE,rmark);
        _th_term_cache_pop(minfo);
        _ex_used_in_pop();
        if (do_backjump && !do_restart && backjump_place(env,learn,at)) {
            //check_cycle(env, "backjump 6");
            _tree_print0("BACKJUMP");
            do_backjump = 0;
            //exit(1);
            goto backjump_start;
        }
        if (fl1 != fl) {
            _tree_print0("BAD Branch");
            //add_state(env,p,_ex_intern_appl1_env(env,INTERN_NOT,e),NULL);
            fl = fl1;
        //} else {
        //    _th_add_list(env,learn,at);
        }
        if (!do_restart && !do_backjump && (_th_find_all_fails || fl==NULL)) {
            _ex_used_in_push();
            minfo = _th_term_cache_push();
            emark = _th_alloc_mark(ENVIRONMENT_SPACE);
            rmark = _th_alloc_mark(REWRITE_SPACE);
            _th_derive_push(env);
            ++decision_level;
            if (e==_ex_true || e==_ex_false) _th_lock_table();
            rt = NULL;
            //if (split->u.case_stmt.exp->type != EXP_VAR) {
                //struct _ex_intern *e = _th_abstract_condition(env,split->u.case_stmt.exp);
                //_th_collect_and_print_classes(env,0);
                if ((_th_do_learn?(learn_domain = _th_add_assignment(env,learn,_ex_intern_appl1_env(env,INTERN_NOT,split->u.case_stmt.exp),decision_level)):0) ||
                    _th_deny_predicate(env,split->u.case_stmt.exp)) {
                    _tree_print1("Deny contradiction %d", learn_domain);
                    rt = _ex_true;
                } else {
                    learn_domain = 2;
                }
                //_th_collect_and_print_classes(env,rt != _ex_true);
            //}
            _tree_print0("False case");
			if (!rt) {
    			//check_trail(env,p);
				rt = _th_simp(env, split->u.case_stmt.args[1]);
    			//check_trail(env,p);
                //check_env(env, "7");
                fl1 = prove(env, rt, af, fl, learn, list, learn_domain);
			} else {
				fl1 = fl;
			}
            if (_th_do_learn) _th_delete_assignment(env,learn,split->u.case_stmt.exp);
            --decision_level;
            _th_derive_pop(env);
            _th_alloc_release(ENVIRONMENT_SPACE,emark);
            _th_alloc_release(REWRITE_SPACE,rmark);
            _th_term_cache_pop(minfo);
            _ex_used_in_pop();
            if (do_backjump && !do_restart && backjump_place(env,learn,af)) {
                ///check_cycle(env, "backjump 7");
                _tree_print0("BACKJUMP");
                do_backjump = 0;
                //exit(1);
                goto backjump_start;
            }
            if (fl1 != fl) {
                _tree_print0("BAD Branch");
                //add_state(env,p,_ex_intern_appl1_env(env,INTERN_NOT,e),NULL);
                fl = fl1;
            }
        }
	} else {
		printf("Illegal split\n");
		exit(1);
	}

  	_tree_undent();
    _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
    if (pc != _th_push_count(env)) {
        fprintf(stderr, "Push count error 15\n");
        exit(1);
    }
#endif
#ifndef FAST
    if (_tree_get_indent() != initial_indent) {
        fprintf(stderr, "Indents do not align 14\n");
        exit(1);
    }
#endif
    //printf("End prove\n");
	return fl;
}

double _th_initial_conflict_limit = 100;
double _th_bump_decay = 1.05;
double _th_random_probability = 0.02;
double _th_conflict_factor = 1.5;

static double conflict_limit;
static int conflict_count;

//#define MATCHES_YICES 1

static struct _ex_intern *user2_sub(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern **args;
	int i;

	if (e->user2) return e->user2;

	if (e->type != EXP_APPL) return e;

	args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
	for (i = 0; i < e->u.appl.count; ++i) {
		args[i] = user2_sub(env,e->u.appl.args[i]);
	}

	if (e->u.appl.functor==INTERN_EQUAL) {
		return _ex_intern_equal(env,e->type_inst,args[0],args[1]);
	} else {
	    return _ex_intern_appl_env(env,e->u.appl.functor,i,args);
	}
}

#define PARENT_LIST_CHECK 1

#ifdef PARENT_LIST_CHECK
static struct _ex_intern *the_theorem;
static void check_parent_list(struct env *env, struct parent_list *p)
{
	struct parent_list *p1;
    struct _ex_intern *e;

	p1 = p;
	while (p1) {
		struct _ex_intern *e;
		if (p1->split->type==EXP_APPL && p1->split->u.appl.functor==INTERN_NOT) {
			e = p1->split->u.appl.args[0];
			e->user2 = _ex_false;
		} else {
			e = p1->split;
			e->user2 = _ex_true;
		}
		p1 = p1->next;
	}
	e = user2_sub(env,the_theorem);
	if (_th_int_rewrite(env,e,0)==_ex_false) {
		printf("Bad parent set\n");
		while (p1) {
			printf("p %s\n", _th_print_exp(p1->split));
			p1 = p1->next;
		}
		exit(1);
	}
	p1 = p;
	while (p1) {
		struct _ex_intern *e;
		if (p1->split->type==EXP_APPL && p1->split->u.appl.functor==INTERN_NOT) {
			e = p1->split->u.appl.args[0];
			e->user2 = NULL;
		} else {
			e = p->split;
			e->user2 = NULL;
		}
		p1 = p1->next;
	}
}
#endif

struct fail_list *sat_prove(struct env *env, struct parent_list *p, struct fail_list *fl, struct learn_info *learn, struct term_list *list, int ld)
{
	struct _ex_intern *split, *pos_split, *neg_split, *ps;
    int split_sign;
	char *mark, *emark, *rmark;
    struct parent_list *at, *af, *p2, *porig;
    struct fail_list *fl1;
    struct add_list *un, *u;
    struct mark_info *minfo;
    struct _ex_intern *rt;
    int learn_domain, i;
#ifndef FAST
    int initial_indent = _tree_get_indent();
#endif
    extern int has_positive_cycle(struct env *env);

#ifdef PUSH_COUNT
    int pc = _th_push_count(env);
#endif

#ifdef PARENT_LIST_CHECK
	check_parent_list(env,p);
#endif

	printf("indent aaaaa %d\n", _tree_get_indent());

	//check_trail(env,p);

	//printf("Prove\n");


    //check_user2_error(info);

    //check_integrity(env, "prove");
    //printf("Here1\n");
    //fflush(stdout);

    //if (e != _ex_true) _th_collect_and_print_classes(env,1);

    //at = p;
    //while (at) {
    //    if (at->split->type==EXP_VAR) exit(1);
    //    at = at->next;
    //}
    //check_cycle(env, "enter prove");
    //check_env(env, "1");

    //do_restart = (do_restart || (_th_do_learn > 0 && _th_check_restart(_th_do_learn)));
	if (do_restart) {
		//printf("End prove (restart)\n");
		return fl;
	}

    mark = _th_alloc_mark(REWRITE_SPACE);

    _zone_increment();
    //if (_th_matches_yices_ce(p)) {
    //    _tree_print("CE BRANCH");
    //}
    _tree_print1("Proving %d", _tree_zone);
	_tree_indent();
    //_th_print_trail("Trail", p);

    //if (has_positive_cycle(env) || has_bad_model(env,p)) {
    //    dump_state(env,p);
    //    fprintf(stderr, "Undetected cycle\n");
    //    _tree_print0("Undetected cycle");
    //    _th_print_difference_table(env);
    //    exit(1);
    //}

	printf("indent aaaa %d\n", _tree_get_indent());
    if (_th_do_learn && learn==NULL) {
        info = learn = _th_new_learn_info(env);
    }

	printf("indent aaa %d\n", _tree_get_indent());
#ifdef XX
	//_tree_print2("Here1 %d %d", new_learn, _th_do_learn);
	if (new_learn && _th_do_learn) {
		//printf("Here2a\n");
		//fflush(stdout);
		do_backjump = _th_learn(env,learn,p,list,ld);
		++conflict_count;
		++backjump_count;
		_th_learn_increase_bump(learn,_th_bump_decay);
		if (conflict_count >= conflict_limit) do_restart = 1;
		//printf("Here2b\n");
		//fflush(stdout);
		//if (do_backjump && backjump_place(env,learn,p)) do_backjump = 0;
	}
	_tree_undent();
	_th_alloc_release(REWRITE_SPACE,mark);
	_tree_print0("Solved");
#ifdef PUSH_COUNT
	if (pc != _th_push_count(env)) {
		fprintf(stderr, "Push count error 1\n");
		exit(1);
	}
#endif
#ifndef FAST
	if (_tree_get_indent() != initial_indent) {
		fprintf(stderr, "Indents do not align 1 %d %d\n", _tree_get_indent(), initial_indent);
		exit(1);
	}
#endif

	//if (_th_matches_yices_ce(p)) {
	//    //dump_state(env,p);
	//    fprintf(stderr, "Failed path\n");
	//    exit(1);
	//}
	//printf("End prove 1\n");
	return fl;
#endif

    //printf("Here3\n");
    //fflush(stdout);

    //printf("Here4\n");
    //fflush(stdout);

backjump_start:
	printf("indent aa %d\n", _tree_get_indent());
    if (_th_do_learn) {
        split = _th_learned_unate_case(env,info,p);

        if (split) {
#ifdef XX
			p2 = p;
			while (p2) {
				if (p2->split==split) {
					fprintf(stderr, "Duplicate split %s\n", _th_print_exp(split));
					exit(1);
				}
				p2 = p2->next;
			}
#endif
			++learned_unates;
            _tree_undent();
            _tree_print2("Learned unate %d %s", _th_learned_domain_case, _th_print_exp(split));
            _tree_indent();
            
            //_th_derive_push(env);
            p2 = (struct parent_list *)_th_alloc(CHECK_SPACE,sizeof(struct parent_list));
            p2->next = p;
            p = p2;
            if (split->type==EXP_APPL && split->u.appl.functor==INTERN_NOT) {
                p->split = split->u.appl.args[0];
            } else {
                p->split = _ex_intern_appl1_env(env,INTERN_NOT,split);
            }
#ifdef MATCH_YICES
			if (_th_matches_yices_ce(env,p->next,split)) {
                FILE *file = fopen("dump.smt","w");
				fprintf(stderr, "_th_matches_yices_ce 1\n");
				p->split = split;
                _th_print_state(env,p,NULL,_ex_true,file,"dump.smt","unknown","any");
				exit(1);
			}
#endif
            p->used_in_learn = 0;
            p->exp = _ex_false;
            p->rhs = 1;
            p->unate = 1;
            p->split = split;
            ++unate_count;
            ++split_count;
            //split = _th_abstract_condition(env,split);

            //printf("Split = %s\n", _th_print_exp(split));
			//_th_print_trail("Before assert 2", p);
            if ((learn_domain = _th_add_assignment(env,learn,split,decision_level)) || (_th_learned_domain_case?0:_th_add_predicate(env,split,NULL))) {
				_tree_print1("Learned contradiction ", learn_domain);
				//_th_derive_pop(env);
                //printf("Learn domain = %d\n", learn_domain);
#ifdef MATCH_YICES
				if (_th_matches_yices_ce(env,p,NULL)) {
                    FILE *file = fopen("dump.smt","w");
					fprintf(stderr, "_th_matches_yices_ce 2\n");
					_th_print_state(env,p,NULL,_ex_true,file,"dump.smt","unknown","any");
					while (p) {
						printf("split %s\n", _th_print_exp(p->split));
						p = p->next;
					}
					exit(1);
				}
#endif
				if (new_learn) {
					do_backjump = _th_learn(env,info,p,list,learn_domain);
					//if (do_backjump) _th_print_trail("backjump", p);
					++conflict_count;
            		++backjump_count;
					_th_learn_increase_bump(learn,_th_bump_decay);
					//printf("Backjump, conflict count = %d %d %g\n", backjump_count, conflict_count, conflict_limit);
					//_tree_print3("Backjump, conflict count = %d %d %g\n", backjump_count, conflict_count, conflict_limit);
             		if (conflict_count >= conflict_limit) do_restart = 1;
				}
                //if (do_backjump && backjump_place(env,info,p)) do_backjump = 0;
                _th_delete_assignment(env,learn,split);
                _tree_undent();
                _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
                if (pc != _th_push_count(env)) {
                    fprintf(stderr, "Push count error 6\n");
                    exit(1);
                }
#endif
#ifndef FAST
                if (_tree_get_indent() != initial_indent) {
					fprintf(stderr, "Test1\n");
                    fprintf(stderr, "Indents do not align 5a %d %d\n", _tree_get_indent(), initial_indent);
                    exit(1);
                }
#endif
				//printf("End prove 5\n");
                return fl;
            }
            //check_env(env, "2");
            _tree_undent();
            fl1 = sat_prove(env, p, fl, learn, list, 1);
            if (fl1 != fl) {
                _tree_print0("BAD Branch");
                fl = fl1;
            }
            //_th_derive_pop(env);
            _th_delete_assignment(env,learn,split);
            _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
            if (pc != _th_push_count(env)) {
                fprintf(stderr, "Push count error 8\n");
                exit(1);
            }
#endif
#ifndef FAST
            if (_tree_get_indent() != initial_indent) {
                fprintf(stderr, "Indents do not align 7\n");
                exit(1);
            }
#endif
			//printf("End prove 7\n");
            return fl;
        }
    }

    _tree_print1("learn term count %d", _th_learn_term_count(info));

	printf("indent a %d\n", _tree_get_indent());
    pos_split = split = _th_learn_choose_signed(env,info,p,_th_random_probability);
    if (split==NULL) {
		struct fail_list *f;
//#ifndef FAST
        FILE *file;
        struct parent_list *pp;
//#endif
#ifdef PARENT_LIST_CHECK
    	check_parent_list(env,p);
#endif
		_tree_undent();
		_tree_print0("Failed case");
		printf("indent %d\n", _tree_get_indent());
		f = (struct fail_list *)_th_alloc(CHECK_SPACE,sizeof(struct fail_list));
        f->e = _ex_false;
		f->next = fl;
        f->conditions = p;
        f->reduced_form = add_reductions(env);
//#ifndef FAST
        //_th_collect_and_print_classes(env,2);
        _th_print_difference_table(env);
		//_th_display_difference_table(env);
        _th_learn_print_assignments(info);
        //dump_state(env, p);
        file = fopen("dump.smt","w");
        _th_print_state(env,p,NULL,_ex_true,file,"dump.smt","unknown","any");
        fclose(file);
		//check_trail(env,p);
        //check_unates(learn,p,"sat");
        //print_term_assignments(learn);
        //check_integrity(env, "Failed leaf", p);
        //if (has_positive_cycle(env)) {
        //    fprintf(stderr, "Undetected cycle\n");
        //    _tree_print("Undetected cycle");
        //}
//#endif
        //check_theorem(env);
        _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
        if (pc != _th_push_count(env)) {
            fprintf(stderr, "Push count error 13\n");
            exit(1);
        }
#endif
		//check_trail(env,p->next);
#ifndef FAST
        if (_tree_get_indent() != initial_indent) {
            fprintf(stderr, "Indents do not align 12 %d %d\n", _tree_get_indent(), initial_indent);
            exit(1);
        }
        _tree_print0("Inequalities");
        _tree_indent();
        pp = p;
        while (p) {
            struct _ex_intern *e = p->split;
            if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_EQUAL || e->u.appl.functor==INTERN_RAT_LESS)) {
                if (e->u.appl.functor != INTERN_RAT_LESS) goto pc_1;
                _tree_print_exp("cond", p->split);
                _tree_indent();
                e = _ex_intern_appl2_env(env,e->u.appl.functor,_th_simp(env,e->u.appl.args[0]),_th_simp(env,e->u.appl.args[1]));
            } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                struct _ex_intern *f = e->u.appl.args[0];
                if (f->type==EXP_APPL && (f->u.appl.functor==INTERN_EQUAL || f->u.appl.functor==INTERN_RAT_LESS)) {
                    if (f->u.appl.functor != INTERN_RAT_LESS) goto pc_1;
                    _tree_print_exp("cond", p->split);
                    _tree_indent();
                    f = _ex_intern_appl2_env(env,f->u.appl.functor,_th_simp(env,f->u.appl.args[0]),_th_simp(env,f->u.appl.args[1]));
                    e = _ex_intern_appl1_env(env,INTERN_NOT,f);
                } else {
                    _tree_print_exp("cond", p->split);
                    _tree_indent();
                }
            } else {
                goto pc_1;
                _tree_print_exp("cond", p->split);
                _tree_indent();
            }
            _tree_undent();
            _tree_print_exp("reduced", e);
pc_1:
            p = p->next;
        }
        _tree_undent();
        _tree_print0("Negations");
        _tree_indent();
        p = pp;
        while (p) {
            struct _ex_intern *e = p->split;
            if (e->type != EXP_APPL || e->u.appl.functor != INTERN_NOT ||
                e->u.appl.args[0]->type != EXP_APPL || e->u.appl.args[0]->u.appl.functor != INTERN_EQUAL) goto pc_2;
            _tree_print_exp("cond", p->split);
            _tree_indent();
            if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_EQUAL || e->u.appl.functor==INTERN_RAT_LESS)) {
                e = _ex_intern_appl2_env(env,e->u.appl.functor,_th_simp(env,e->u.appl.args[0]),_th_simp(env,e->u.appl.args[1]));
            } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                struct _ex_intern *f = e->u.appl.args[0];
                if (f->type==EXP_APPL && (f->u.appl.functor==INTERN_EQUAL || f->u.appl.functor==INTERN_RAT_LESS)) {
                    f = _ex_intern_appl2_equal_env(env,f->u.appl.functor,_th_simp(env,f->u.appl.args[0]),_th_simp(env,f->u.appl.args[1]),f->type_inst);
                    e = _ex_intern_appl1_env(env,INTERN_NOT,f);
                }
            }
            _tree_undent();
            _tree_print_exp("reduced", e);
            if (e->u.appl.args[0]->u.appl.args[0]==e->u.appl.args[0]->u.appl.args[1]) {
                _tree_print0("*** SAME ***");
            }
pc_2:
            p = p->next;
        }
        _tree_undent();
        _tree_print0("All");
        _tree_indent();
        p = pp;
        while (p) {
            struct _ex_intern *e = p->split;
            _tree_print_exp("cond", p->split);
            _tree_indent();
#ifdef XX
            if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_EQUAL || e->u.appl.functor==INTERN_RAT_LESS)) {
                e = _ex_intern_appl2_equal_env(env,e->u.appl.functor,_th_simp(env,e->u.appl.args[0]),_th_simp(env,e->u.appl.args[1]),e->type_inst);
                if (e->u.appl.functor==INTERN_EQUAL && e->u.appl.args[0] != e->u.appl.args[1]) {
                    _tree_print0("Error");
                    fprintf(stderr, "Equality not properly working\n");
                    exit(1);
                }
            } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                struct _ex_intern *f = e->u.appl.args[0];
                if (f->type==EXP_APPL && (f->u.appl.functor==INTERN_EQUAL || f->u.appl.functor==INTERN_RAT_LESS)) {
                    f = _ex_intern_appl2_env(env,f->u.appl.functor,_th_simp(env,f->u.appl.args[0]),_th_simp(env,f->u.appl.args[1]));
                    e = _ex_intern_appl1_env(env,INTERN_NOT,f);
                    if (e->u.appl.functor==INTERN_EQUAL && e->u.appl.args[0] == e->u.appl.args[1]) {
                        _tree_print0("Error");
                        fprintf(stderr, "Inequality not properly working\n");
                        exit(1);
                    }
                }
            }
#endif
			_tree_undent();
            _tree_print_exp("reduced", e);
            p = p->next;
        }
        _tree_undent();
#endif
		//printf("End prove 12\n");
		return f;
    } else {
        ++split_count;
		if (split->type==EXP_APPL && split->u.appl.functor==INTERN_NOT) {
			neg_split = split = split->u.appl.args[0];
			split_sign = 1;
		} else {
			neg_split = _ex_intern_appl1_env(env,INTERN_NOT,split);
			split_sign = 0;
		}
    }

    _tree_print_exp("Split", split);

    at = (struct parent_list *)_th_alloc(CHECK_SPACE,sizeof(struct parent_list));
    at->next = p;
    at->split = pos_split;
    at->used_in_learn= 0;
    at->exp = _ex_true;
    af = (struct parent_list *)_th_alloc(CHECK_SPACE,sizeof(struct parent_list));
    af->next = p;
    af->split = neg_split;
    af->used_in_learn= 0;
    af->exp = _ex_true;
#ifdef XX
	p2 = p;
	while (p2) {
		if (p2->split==pos_split || p2->split==neg_split) {
			fprintf(stderr, "Duplicate split %s\n", _th_print_exp(split));
			exit(1);
		}
		p2 = p2->next;
	}
#endif

    at->unate = 0;
	at->rhs = 0;
    af->unate = 0;
	af->rhs = 0;
	emark = _th_alloc_mark(ENVIRONMENT_SPACE);
	rmark = _th_alloc_mark(REWRITE_SPACE);
	_th_derive_push(env);
	++decision_level;
	rt = NULL;
	//if (split->u.case_stmt.exp->type != EXP_VAR) {
	//_th_collect_and_print_classes(env,0);
	if ((_th_do_learn?(learn_domain = _th_add_assignment(env,learn,pos_split,decision_level)):0) || _th_add_predicate(env,pos_split,NULL)) {
		rt = _ex_true;
#ifdef MATCH_YICES
		if (_th_matches_yices_ce(env,at,NULL)) {
            FILE *file = fopen("dump.smt","w");
			fprintf(stderr, "_th_matches_yices_ce 3\n");
			_th_print_state(env,at,NULL,_ex_true,file,"dump.smt","unknown","any");
			exit(1);
		}
#endif
		_tree_print1("Assert contradiction %d", learn_domain);
	} else {
		learn_domain = 2;
	}
	//_th_collect_and_print_classes(env,rt != _ex_true);
	//}
	_tree_print_exp("case 1", pos_split);
	if (!rt) {
		//check_trail(env,p);
		//check_trail(env,p);
		//check_env(env, "4");
		fl1 = sat_prove(env, at, fl, learn, list, learn_domain);
	} else {
		fl1 = fl;
	}
	if (fl1 != fl) {
		_tree_print0("BAD Branch");
#ifndef FAST
		//add_state(env,p,_ex_intern_appl1_env(env,INTERN_NOT,e),NULL);
#endif
		fl = fl1;
		//} else {
		//    _th_add_list(env,learn,at);
	}
	--decision_level;
	if (_th_do_learn) _th_delete_assignment(env,learn,split);
	_th_derive_pop(env);
	_th_alloc_release(ENVIRONMENT_SPACE,emark);
	_th_alloc_release(REWRITE_SPACE,rmark);
	_tree_print2("do_backjump, do_restart %d %d", do_backjump, do_restart);
	if (do_backjump && !do_restart && backjump_place(env,learn,at)) {
		//check_cycle(env, "backjump 4");
		_tree_print0("BACKJUMP");
		do_backjump = 0;
		//exit(1);
		goto backjump_start;
	}
	if (!do_restart && !do_backjump && (_th_find_all_fails || fl==NULL)) {
		//fprintf(stderr, "Should not reach this point\n");
		//while (p) {
		//	printf("p->split = %s\n", _th_print_exp(p->split));
		//	p = p->next;
		//}
		//exit(1);
		emark = _th_alloc_mark(ENVIRONMENT_SPACE);
		rmark = _th_alloc_mark(REWRITE_SPACE);
		_th_derive_push(env);
		++decision_level;
		rt = NULL;
		//if (split->u.case_stmt.exp->type != EXP_VAR) {
		//struct _ex_intern *e = _th_abstract_condition(env,split->u.case_stmt.exp);
		//_th_collect_and_print_classes(env,0);
		if ((_th_do_learn?(learn_domain = _th_add_assignment(env,learn,neg_split,decision_level)):0) ||
			_th_add_predicate(env,neg_split,NULL)) {
#ifdef MATCH_YICES
				if (_th_matches_yices_ce(env,af,NULL)) {
                    FILE *file = fopen("dump.smt","w");
					fprintf(stderr, "_th_matches_yices_ce 4\n");
					_th_print_state(env,af,NULL,_ex_true,file,"dump.smt","unknown","any");
					exit(1);
				}
#endif
				rt = _ex_true;
				_tree_print1("Deny contradiction %d", learn_domain);
		} else {
			learn_domain = 2;
		}
		//_th_collect_and_print_classes(env,rt != _ex_true);
		//}
		_tree_print_exp("case 2", neg_split);
		if (!rt) {
			//check_trail(env,p);
			//check_trail(env,p);
			//check_env(env, "5");
			fl1 = sat_prove(env, af, fl, learn, list, learn_domain);
		} else {
			fl1 = fl;
		}
		--decision_level;
		if (_th_do_learn) _th_delete_assignment(env,learn,neg_split);
		_th_derive_pop(env);
		_th_alloc_release(ENVIRONMENT_SPACE,emark);
		_th_alloc_release(REWRITE_SPACE,rmark);
		if (do_backjump && !do_restart && backjump_place(env,learn,af)) {
			//check_cycle(env, "backjump 4");
			_tree_print0("BACKJUMP");
			do_backjump = 0;
			//exit(1);
			goto backjump_start;
		}
		if (fl1 != fl) {
			_tree_print0("BAD Branch");
			//add_state(env,p,_ex_intern_appl1_env(env,INTERN_NOT,e),NULL);
			fl = fl1;
		}
	}

  	_tree_undent();
    _th_alloc_release(REWRITE_SPACE,mark);
#ifdef PUSH_COUNT
    if (pc != _th_push_count(env)) {
        fprintf(stderr, "Push count error 15\n");
        exit(1);
    }
#endif
#ifndef FAST
    if (_tree_get_indent() != initial_indent) {
        fprintf(stderr, "Indents do not align 14\n");
        exit(1);
    }
#endif
    //printf("End prove\n");
	return fl;
}

struct fail_list *sat_prove_front(struct env *env, struct parent_list *p, struct learn_info *learn, struct term_list *list, int ld)
{
	struct fail_list *fl;
    conflict_limit = _th_initial_conflict_limit;
	_tree_print0("Proving");
	_tree_indent();
	do {
        conflict_count = 0;
		do_restart = 0;
		fl = sat_prove(env, p, NULL, learn, list, 1);
		conflict_limit *= _th_conflict_factor;
		if (do_restart) {
			_tree_undent();
			_tree_print0("Restarting");
			_tree_indent();
    		++restart_count;
		}
	} while (do_restart);
	_tree_undent();

	return fl;
}

static struct _ex_intern *rewrite_leaves(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern **args;
    int i;

    if (e->type==EXP_APPL) {
        if (e->u.appl.functor==INTERN_AND || e->u.appl.functor==INTERN_OR || e->u.appl.functor==INTERN_NOT ||
            e->u.appl.functor==INTERN_ITE) {
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = rewrite_leaves(env,e->u.appl.args[i]);
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
        } else {
            return _th_nc_rewrite(env,e);
        }
    } else {
        return _th_nc_rewrite(env,e);
    }
}

static struct _ex_intern *rewrite_leaves_ite(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern **args;
    int i;

    if (e->type==EXP_APPL) {
        if (e->u.appl.functor==INTERN_AND || e->u.appl.functor==INTERN_OR || e->u.appl.functor==INTERN_NOT) {
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = rewrite_leaves_ite(env,e->u.appl.args[i]);
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
        } else {
            return _th_nc_rewrite(env,e);
        }
    } else {
        return _th_nc_rewrite(env,e);
    }
}

static int invalid;

static struct _ex_intern *do_a_rewrite(int levels, int *places, struct env *env, struct _ex_intern *e)
{
    struct _ex_intern **args;
    int i;

    invalid = 0;

    if (levels==0 || e->type != EXP_APPL || e->u.appl.count==0) {
        return _th_nc_rewrite(env,e);
    }

    if (e->u.appl.count==1) {
        return _ex_intern_appl1_env(env,e->u.appl.functor,do_a_rewrite(levels,places,env,e->u.appl.args[0]));
    }

    if (e->u.appl.functor != INTERN_AND && e->u.appl.functor != INTERN_OR) {
        return _th_nc_rewrite(env,e);
    }

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
    for (i = 0; i < e->u.appl.count; ++i) {
        if (i==places[0]) {
            args[i] = do_a_rewrite(levels-1,places+1,env,e->u.appl.args[i]);
            if (invalid || (args[i]==rewrite_leaves_ite(env,e->u.appl.args[i]))) invalid = 1;
        } else {
            args[i] = rewrite_leaves_ite(env,e->u.appl.args[i]);
        }
    }
    return _ex_intern_appl_env(env, e->u.appl.functor,e->u.appl.count,args);
}

static int do_an_increment(int levels, int *places, struct _ex_intern *e)
{
    if (levels==0 || e->type != EXP_APPL || e->u.appl.count==0) {
        return 1;
    }

    if (e->u.appl.count==1) {
        return do_an_increment(levels,places,e->u.appl.args[0]);
    }

    if (e->u.appl.functor != INTERN_AND && e->u.appl.functor != INTERN_OR) {
        return 1;
    }

    if (do_an_increment(levels-1,places+1,e->u.appl.args[places[0]])) {
        ++places[0];
        if (places[0]==e->u.appl.count) {
            places[0] = 0;
            return 1;
        } else {
            return 0;
        }
    }
    return 0;
}

struct _ex_intern *propagate_nots(struct env *env, struct _ex_intern *e, int invert)
{
    struct _ex_intern **args;
    int i;

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        return propagate_nots(env,e->u.appl.args[0],!invert);
    }

    if (!invert) return e;

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_AND) {
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = propagate_nots(env,e->u.appl.args[i],invert);
        }
        return _ex_intern_appl_env(env,INTERN_OR,e->u.appl.count,args);
    }

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_OR) {
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = propagate_nots(env,e->u.appl.args[i],invert);
        }
        return _ex_intern_appl_env(env,INTERN_AND,e->u.appl.count,args);
    }

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_ITE) {
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
        args[0] = e->u.appl.args[0];
        for (i = 1; i < e->u.appl.count; ++i) {
            args[i] = propagate_nots(env,e->u.appl.args[i],invert);
        }
        return _ex_intern_appl_env(env,INTERN_ITE,e->u.appl.count,args);
    }

    return _ex_intern_appl1_env(env,INTERN_NOT,e);
}

void print_differences(int indent, struct _ex_intern *e1, struct _ex_intern *e2)
{
    int i;

    if (e1==e2) return;

    if (!e1 || !e2 || e1->type != EXP_APPL || e2->type != EXP_APPL || e1->u.appl.functor != e2->u.appl.functor ||
        e1->u.appl.count != e2->u.appl.count) {
        printf("%*sDifference:\n", indent, "");
        printf("%*s    %s\n", indent, "", _th_print_exp(e1));
        printf("%*s    %s\n", indent, "", _th_print_exp(e2));
        return;
    }

    for (i = 0; i < e1->u.appl.count; ++i) {
        printf("%*sTesting subterm %d\n", indent, "", i);
        print_differences(indent+4,e1->u.appl.args[i],e2->u.appl.args[i]);
    }
}

int find_difference(int level, struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *f, *g;

    printf("Trying %d\n", level);
    f = _th_nc_rewrite(env,e);
    g = propagate_nots(env,e,0);
    g = _th_nc_rewrite(env,g);

    if (f==g) return 0;

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        e = e->u.appl.args[0];
        if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_AND || e->u.appl.functor==INTERN_OR || e->u.appl.functor==INTERN_NOT)) {
            int fd = 0;
            int i;
            for (i = 0; i < e->u.appl.count; ++i) {
                fd = (find_difference(level+1,env,_ex_intern_appl1_env(env,INTERN_NOT,e->u.appl.args[i])) || fd);
            } 
            if (fd) return 1;
        }
    }

    printf("Difference: (%d)\n", level);
    printf("    %s\n", _th_print_exp(f));
    printf("    %s\n", _th_print_exp(g));

    return 1;
}

int _th_do_symmetry = 0;
int _th_do_grouping = 0;
int _th_do_break_flower = 0;

static struct parent_list *eliminate_booleans(struct env *env, struct learn_info *info, struct parent_list *list)
{
    struct parent_list *l = list;
    struct parent_list *p = NULL;

    while (l) {
        if (l->split->type==EXP_VAR ||
            (l->split->type==EXP_APPL && l->split->u.appl.functor==INTERN_NOT &&
            l->split->u.appl.args[0]->type==EXP_VAR)) {
            //_tree_print_exp("Removing unate", l->split);
            //_th_transfer_to_learn(env,info,NULL,_ex_intern_appl1_env(env,INTERN_AND,l->split));
            if (l->split->type==EXP_APPL) {
                _th_transfer_to_learn(env,info,NULL,_ex_intern_appl1_env(env,INTERN_AND,l->split->u.appl.args[0]));
            } else {
                _th_transfer_to_learn(env,info,NULL,_ex_intern_appl1_env(env,INTERN_AND,_ex_intern_appl1_env(env,INTERN_NOT,l->split)));
            }
            if (p==NULL) {
                list = l->next;
            } else {
                p->next = l->next;
            }
        } else {
            p = l;
        }
        l = l->next;
    }
    return list;
}

static int is_equation(struct _ex_intern *e)
{
    if (e->type==EXP_VAR || e->type==EXP_INTEGER || e->type==EXP_RATIONAL) return 1;

    if (e->type==EXP_APPL) {
        if (e->u.appl.functor==INTERN_NAT_PLUS || e->u.appl.functor==INTERN_RAT_PLUS ||
            e->u.appl.functor==INTERN_NAT_TIMES || e->u.appl.functor==INTERN_RAT_TIMES) return 1;
    }

    return 0;
}

static struct parent_list *remove_equalities(struct env *env, struct parent_list *list)
{
    struct parent_list *l = list;
    struct parent_list *p = NULL;

    _th_derive_push(env);

    while (l) {
        if (l->split->type==EXP_APPL && l->split->u.appl.functor==INTERN_EQUAL &&
            ((l->split->u.appl.args[0]->type==EXP_VAR &&
              is_equation(l->split->u.appl.args[1])) || (l->split->u.appl.args[1]->type==EXP_VAR &&
              is_equation(l->split->u.appl.args[0])))) {
            //printf("Asserting %s\n", _th_print_exp(l->split));
            _th_assert_predicate(env,_th_simp(env,l->split));
            _th_elim_simp_var(env,info);
        }
        l = l->next;
    }
    l = list;
    while (l) {
        l->split = _th_simp(env,l->split);
        if (l->split==_ex_true) {
            if (p==NULL) {
                list = l->next;
            } else {
                p->next = l->next;
            }
        } else {
            p = l;
        }
        l = l->next;
    }

    _th_derive_pop(env);

    return list;
}

static void test_simplex(struct env *env)
{
//    _th_derive_push(env);
//    _th_assert_predicate(env,_th_parse(env,"(rless (rplus x a) y)"));
//    _th_assert_predicate(env,_th_parse(env,"(rless y (rplus x a))"));
//    _th_derive_pop(env);
//    _th_derive_push(env);
//    _th_assert_predicate(env,_th_parse(env,"(rless (rplus x a b) y)"));
//    _th_assert_predicate(env,_th_parse(env,"(rless y (rplus x a (rtimes #-1/1 b)))"));
//    _th_assert_predicate(env,_th_parse(env,"(== b #0/1)"));
//    _th_derive_pop(env);
//    _th_derive_push(env);
//    _th_assert_predicate(env,_th_parse(env,"(rless x a)"));
//    _th_assert_predicate(env,_th_parse(env,"(rless y b)"));
//    _th_assert_predicate(env,_th_parse(env,"(rless (rplus a b) (rplus x y))"));
//    _th_derive_pop(env);
    _th_derive_push(env);
    _th_assert_predicate(env,_th_parse(env,"(rless a b)"));
    _th_assert_predicate(env,_th_parse(env,"(rless b (rtimes #2/1 c))"));
    _th_assert_predicate(env,_th_parse(env,"(rless (rtimes #2/1 c) a)"));
    _th_derive_pop(env);
    exit(1);
}

void ne_test1(struct env *env)
{
	_th_add_predicate(env,
		_ex_intern_equal(env,_ex_real,_ex_intern_var(50),_ex_intern_var(51)),NULL);
	_th_add_predicate(env,
		_ex_intern_equal(env,_ex_real,_ex_intern_var(51),_ex_intern_var(52)),NULL);
	_th_add_predicate(env,
		_ex_intern_equal(env,_ex_real,_ex_intern_var(52),_ex_intern_var(53)),NULL);
	_th_add_predicate(env,
		_ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_equal(env,_ex_real,_ex_intern_var(50),_ex_intern_var(53))),NULL);
}

void ne_test2(struct env *env)
{
	_th_add_predicate(env,
		_ex_intern_appl1_env(env,INTERN_NOT,
		    _ex_intern_equal(env,_ex_real,_ex_intern_var(50),_ex_intern_var(51))),NULL);
	_th_add_predicate(env,
		_ex_intern_appl1_env(env,INTERN_NOT,
		    _ex_intern_appl2_env(env,INTERN_RAT_LESS,_ex_intern_var(50),_ex_intern_var(51))),NULL);
	_th_add_predicate(env,
		_ex_intern_appl1_env(env,INTERN_NOT,
		    _ex_intern_appl2_env(env,INTERN_RAT_LESS,_ex_intern_var(51),_ex_intern_var(52))),NULL);
	_th_add_predicate(env,
		_ex_intern_appl1_env(env,INTERN_NOT,
		    _ex_intern_appl2_env(env,INTERN_RAT_LESS,_ex_intern_var(52),_ex_intern_var(50))),NULL);
	exit(1);
}

void ne_test3(struct env *env)
{
	_th_add_predicate(env,
		_ex_intern_appl1_env(env,INTERN_NOT,
		    _ex_intern_appl2_env(env,INTERN_RAT_LESS,_ex_intern_var(50),_ex_intern_var(51))),NULL);
	_th_add_predicate(env,
		_ex_intern_appl1_env(env,INTERN_NOT,
		    _ex_intern_appl2_env(env,INTERN_RAT_LESS,_ex_intern_var(51),_ex_intern_var(52))),NULL);
	_th_add_predicate(env,
		_ex_intern_appl1_env(env,INTERN_NOT,
		    _ex_intern_appl2_env(env,INTERN_RAT_LESS,_ex_intern_var(52),_ex_intern_var(50))),NULL);
	_th_add_predicate(env,
		_ex_intern_appl1_env(env,INTERN_NOT,
		    _ex_intern_equal(env,_ex_real,_ex_intern_var(50),_ex_intern_var(51))),NULL);
	exit(1);
}

struct fail_list *_th_prove(struct env *env, struct _ex_intern *e)
{
    struct fail_list *res;
    //char *mark;
    struct parent_list *p;
    char *mark;

    //struct _ex_intern *orig = e;
    //struct _ex_intern *xx;
    //int places[2];
    //system("erase states");
    //e = _th_nc_rewrite(env,e);
    //e = _th_bit_blast(env,e);
    //_th_yices_ce_value(env,_ex_true);

#ifdef PARENT_LIST_CHECK
	the_theorem = e;
#endif
	_th_initialize_simplex(env);
    //_th_initialize_difference_table(env);
    //test_simplex(env);
    do_backjump = 0;
    _th_clear_dependency_cache();
    mark = _th_alloc_mark(REWRITE_SPACE);

	if (_th_do_symmetry) e = _th_augment_with_symmetries(env,e);
	e = _th_nc_rewrite(env,e);
    if (!strcmp(_th_get_logic_name(),"QF_UFLIA")) e = _th_variablize_functions(env,e);
	e = _th_simp(env,e);
	split_count = 0;
    unate_count = 0;
	backjump_count = 0;
	restart_count = 0;
    elimination_count = 0;
    solved_cases = 0;
    learned_unates = 0;
    info = _th_new_learn_info(env);
    e = _th_remove_nested_ite(env,info,e,NULL);
	e = _th_nc_rewrite(env,e);
	theorem = e;
	if (_th_do_unate) {
    	_th_derive_push(env);
        e = preprocess(env,e,NULL,NULL, info, NULL, 1);
        _th_derive_pop(env);
		e = _th_nc_rewrite(env,e);
	}

    if (e != _ex_true && strcmp(_th_get_logic_name(),"QF_UF")) {
        if (_th_do_break_flower && _th_is_difference_logic()) {
            e = _th_break_flower(env,e,trail,info);
        }
        if (_th_do_grouping) e = _th_simplify_groupings(env,e,trail,info);
    }
    //_tree_print_exp("yices ce value(res) 2", _th_yices_ce_value(env,res));
    ///_tree_print_exp("yices ce value(res) again", _th_yices_ce_value(env,res));
    if (e==_ex_false) {
        return NULL;
    } else {
        trail = eliminate_booleans(env,info,trail);
        //trail = remove_equalities(env,trail);
    }
	p = trail;
	while (p) {
		p->split = _th_simp(env,p->split);
		p = p->next;
	}
    p = trail;
    _tree_print0("Trail");
    _tree_indent();
    while (p) {
        //_tree_print1("unate %d", p->unate);
        _tree_print_exp("term", p->split);
        _th_assert_predicate(env,p->split);
		//printf("p->split = %s\n", _th_print_exp(p->split));
        p = p->next;
    }
    _tree_undent();
    e = _th_nc_rewrite(env,e);
    e = _th_simp(env,e);
	if (e==_ex_true) {
		return NULL;
	}
    _th_add_to_learn(env,info,e,trail);
	e = _ex_false;
    _th_derive_push(env);
	//ne_test3(env);
    res = sat_prove_front(env,trail,info,NULL,1);
    _th_derive_pop(env);
#ifdef XX
	do {
        do_restart = 0;
        _th_derive_push(env);
        res = prove(env,e,trail,NULL, info, NULL, 1);
        _th_derive_pop(env);
        if (do_restart) {
			printf("Restarting\n");
            _tree_print0("*** Restarting ***");
            //_tree_start = 0;
            //_tree_end = 200000;
            //_tree_sub = -1;
            //_tree_sub2 = -1;
            //_tree_core = 1;
        }
        new_learn = 0;
        //if (_th_do_learn) {
        //    _tree_print1("Solved cases: %d", solved_cases);
        //    _tree_print1("Learned unates: %d", learned_unates);
            _th_dump_learn(info);
        //}
    } while (do_restart);
#endif
	_tree_print1("Total splits: %d", split_count);
    _tree_print1("Unate splits: %d", unate_count);
	_tree_print1("Total backjumps: %d", backjump_count);
    _tree_print1("Total restarts: %d", restart_count);
    //_tree_print1("Elimination splits: %d", elimination_count);
//#ifndef FAST
    printf("Total splits: %d\n", split_count);
    printf("Unate splits: %d\n", unate_count);
    printf("Total backjumps: %d\n", backjump_count);
    printf("Total restarts: %d\n", restart_count);
    //printf("Other unate splits: %d\n", elimination_count);
    //if (_th_do_learn) {
        //printf("Solved cases: %d\n", solved_cases);
        //printf("Learned unates: %d\n", learned_unates);
    //}
//#endif
    return res;
}

int _th_encoding_only = 0;

//struct _ex_intern *xx;

static struct _ex_intern *tt;

static void _has_bad_equal(struct _ex_intern *e)
{
    int i;

    if (e->type != EXP_APPL) return;
    if (e->user2) return;

    e->user2 = tt;
    tt = e;

    if (e->u.appl.functor==INTERN_EQUAL) {
        if (e->type_inst==NULL) {
            if (e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_RAT_PLUS) {
                fprintf(stderr, "Bad equality %s\n", _th_print_exp(e));
                exit(1);
            }
            if (e->u.appl.args[1]->type==EXP_APPL && e->u.appl.args[1]->u.appl.functor==INTERN_RAT_PLUS) {
                fprintf(stderr, "Bad equality %s\n", _th_print_exp(e));
                exit(1);
            }
        }
    }

    for (i = 0; i < e->u.appl.count; ++i) {
        _has_bad_equal(e->u.appl.args[i]);
    }
}

static void has_bad_equal(struct _ex_intern *e)
{
    tt = _ex_true;
    _ex_true->user2 = NULL;
    _has_bad_equal(e);
    while (tt) {
        struct _ex_intern *n = tt->user2;
        tt->user2 = NULL;
        tt = n;
    }
}

struct parent_list *remove_bools(struct env *env, struct learn_info *info, struct parent_list *t)
{
    struct parent_list *ret = t;
    struct parent_list *p = NULL;

    while (t) {
        _tree_print_exp("testing unate", t->split);
        if (t->split->type==EXP_VAR ||
            (t->split->type==EXP_APPL && t->split->u.appl.functor==INTERN_NOT &&
             t->split->u.appl.args[0]->type==EXP_VAR)) {
            _tree_print_exp("Removing unate", t->split);
            if (t->split->type==EXP_APPL) {
                _th_transfer_to_learn(env,info,NULL,t->split->u.appl.args[0]);
            } else {
                _th_transfer_to_learn(env,info,NULL,_ex_intern_appl1_env(env,INTERN_NOT,t->split));
            }
            if (p) {
                p->next = t->next;
            } else {
                ret = t->next;
            }
        } else {
            p = t;
        }
        t = t->next;
    }

    return ret;
}

int is_bool_expression(struct _ex_intern *e)
{
	int i;

	if (e->user2) return 1;

	e->user2 = _ex_false;
	e->next_cache = term_trail;
	term_trail = e;

	if (e->type==EXP_VAR) return 1;

	if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_AND || e->u.appl.functor==INTERN_OR || e->u.appl.functor==INTERN_NOT ||
		e->u.appl.functor==INTERN_ITE)) {
			for (i = 0; i < e->u.appl.count; ++i) {
				if (!is_bool_expression(e->u.appl.args[i])) return 0;
			}
        	return 1;
	}

	return 0;
}

int is_boolean_expression(struct _ex_intern *e)
{
	int res;
	
	res = is_bool_expression(e);

	while (term_trail) {
		term_trail->user2 = NULL;
		term_trail = term_trail->next_cache;
	}

	return res;
}

int _th_preprocess(struct env *env, struct _ex_intern *e, char *write_file, char *write_d_file)
{
    struct _ex_intern *res;
    char *mark;
    FILE *f;
    struct _ex_intern *orig = e;
    int state = PREPROCESS_DEFAULT;

    //if (xx==NULL) xx = _th_parse(env,"(|| (BmainB_46_f_lt_4 cnf_140 (rplus #2/1 BmainB_46_iBOT)) cnf_131 (BmainB_46_f_lt_3 (rplus #29/1 BmainB_46_iBOT) cnf_48) (not cnf_61))");

    _th_initialize_difference_table(env);
    //setup_check(env);
    _th_clear_dependency_cache();

    if (_th_do_symmetry) {
        e = _th_augment_with_symmetries(env,e);
    }

    mark = _th_alloc_mark(REWRITE_SPACE);
    _tree_print_exp("e", e);
    //_tree_print_exp("yices ce value(e) 1", _th_yices_ce_value(env,e));
    //printf("Here0\n");
    //fflush(stdout);
    e = _th_nc_rewrite(env,e);
    //printf("Here0a\n");
    //fflush(stdout);
    //_tree_print0("Variablize function");
    //_tree_indent();
    if (!strcmp(_th_get_logic_name(),"QF_UFLIA")) e = _th_variablize_functions(env,e);
    //_tree_undent();
    //printf("Here1\n");
    //fflush(stdout);
    //e = _th_nc_rewrite(env,e);
    info = _th_new_learn_info(env);
    //printf("Here1a\n");
    //fflush(stdout);
    //_tree_print0("Remove nested ite");
    //_tree_indent();
    e = _th_remove_nested_ite(env,info,e,NULL);
    //_tree_undent();
    //printf("Here1b\n");
    //fflush(stdout);
    e = _th_nc_rewrite(env,e);
    //printf("Here1c\n");
    //fflush(stdout);
    //_th_print_state(env,NULL,_ex_intern_appl1_env(env,INTERN_NOT,e),fopen("state1.out","w"),_th_get_name(),_th_get_status_name(),_th_get_logic_name());
    //_tree_print_exp("yices ce value(e) 2", _th_yices_ce_value(env,e));
    //_zone_increment();
    //e = _th_simp(env,e);
    //printf("Here2\n");
    //fflush(stdout);
    //if (_th_do_break_flower) e = _th_break_flower(env,e,NULL);
    //if (_th_do_grouping) e = _th_simplify_groupings(env,e,NULL);
    //_th_print_state(env,NULL,_ex_intern_appl1_env(env,INTERN_NOT,e),fopen("state2.out","w"),_th_get_name(),_th_get_status_name(),_th_get_logic_name());
    //_th_print_state(env,NULL,_ex_intern_appl1_env(env,INTERN_NOT,e),fopen("neq048a.smt","w"),_th_get_name(),_th_get_status_name(),_th_get_logic_name());
    //exit(1);
    //_th_alloc_release(REWRITE_SPACE,mark);
    split_count = 0;
    unate_count = 0;
    elimination_count = 0;
    solved_cases = 0;
    learned_unates = 0;
    theorem = e;
    //check_explanations(env);
    //f = fopen("yices.ce","r");
    //_th_parse_yices_ce(env,f);
    //fclose(f);
    //_tree_print_exp("yices ce value(e) 3", _th_yices_ce_value(env,e));
    //printf("Here3\n");
    //fflush(stdout);
    if (_th_do_unate) {
        //printf("This is a test\n");
        _th_derive_push(env);
        res = preprocess(env,e,NULL,NULL, info, NULL, 1);
        _th_derive_pop(env);
    } else {
        res = e;
    }
    //printf("Here4\n");
    //fflush(stdout);
    //_tree_print_exp("yices ce value(res)", _th_yices_ce_value(env,res));
    //_tree_print1("Elimination splits: %d", elimination_count);
    if (_th_encoding_only) {
        res = orig;
    } else {
        res = _th_nc_rewrite(env,res);
    }
    if (res != _ex_true && strcmp(_th_get_logic_name(),"QF_UF")) {
        if (_th_do_break_flower && _th_is_difference_logic()) {
            res = _th_break_flower(env,res,trail,info);
        }
        if (_th_do_grouping) res = _th_simplify_groupings(env,res,trail,info);
    }
    //printf("Adding to learn %s\n", _th_print_exp(res));
    //printf("Here5\n");
    //fflush(stdout);
    //_tree_print_exp("yices ce value(res) 2", _th_yices_ce_value(env,res));
    ///_tree_print_exp("yices ce value(res) again", _th_yices_ce_value(env,res));
    _tree_print1("Unate split count: %d", unate_count);
	_tree_print1("res %s", _th_print_exp(res));
    if (res==_ex_true) {
        state = PREPROCESS_UNSAT;
        trail = NULL;
    } else if (!_th_encoding_only) {
        trail = eliminate_booleans(env,info,trail);
        //trail = remove_equalities(env,trail);
    }
	//_tree_print("Here1");
    if (_th_encoding_only) {
        trail = NULL;
    }
	//_tree_print("Here2");
    if (res != _ex_true && res != _ex_false && is_boolean_expression(res) && _th_is_sat(info) && trail==NULL) {
        //_tree_print0("add to learn");
		//_tree_print("Here3");
        _tree_indent();
        _th_add_to_learn(env,info,res,trail);
        _tree_undent();
        res = _ex_false;
		state = PREPROCESS_CNF;
    }
    if (_th_encoding_only) {
        res = _ex_intern_appl1_env(env,INTERN_NOT,res);
    } else {
        res = _th_nc_rewrite(env,_ex_intern_appl1_env(env,INTERN_NOT,res));
    }
    //res = _ex_true;
    //printf("res = %s\n", _th_print_exp(res));
    //trail = remove_bools(env,info,trail);
    if (state==PREPROCESS_CNF) {
        if (write_d_file) {
            f = fopen(write_d_file, "w");
        } else {
            f = stdout;
        }
        _th_print_dimacs(info,f);
        if (write_d_file) fclose(f);
    } else {
        if (write_file) {
            f = fopen(write_file, "w");
        } else {
            f = stdout;
        }
        _th_print_state(env,trail,info,res,f,_th_get_name(),_th_get_status_name(),_th_get_logic_name());
        if (write_file) fclose(f);
    }
    if (state==PREPROCESS_DEFAULT && (!strcmp(_th_get_logic_name(),"QF_LIA") || !strcmp(_th_get_logic_name(),"QF_UFLIA"))) {
        if (_th_learn_has_non_unity(env,info)) {
            state = PREPROCESS_NORUN;
        } else {
            while (trail) {
                if (_th_has_non_unity(env,trail->split)) {
                    state = PREPROCESS_NORUN;
                    goto cont;
                }
                trail = trail->next;
            }
        }
    }
cont:
#ifndef FAST
    fprintf(stderr, "Total splits: %d\n", split_count);
    fprintf(stderr, "Unate splits: %d\n", unate_count);
    //printf("Other unate splits: %d\n", elimination_count);
#endif
    _th_alloc_release(REWRITE_SPACE,mark);

    return state;
}
