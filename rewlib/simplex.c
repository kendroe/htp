/*
 * simplex.c
 *
 * Simplex like decision procedure for linear arithmetic
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>

#include "Intern.h"
#include "Globals.h"

struct var_map {
    struct var_map *next;
    struct _ex_intern *var;
    struct _ex_intern *e;
};

struct simplex {
    struct env *env;
    struct var_map *T, *R, *Z;
    struct add_list *D;
    struct var_map *W;
    struct var_map *mapping;
    struct simplex *push;
};

struct var_map *copy_var_map(int space, struct var_map *map)
{
    struct var_map *p, *n, *ret;

    p = NULL;
    while (map) {
        n = (struct var_map *)_th_alloc(space,sizeof(struct var_map));
        if (p) {
            p->next = n;
        } else {
            ret = n;
        }
        p = n;
        n->e = map->e;
        n->var = map->var;
        map = map->next;
    }
    if (p) {
        p->next = NULL;
    } else {
        ret = NULL;
    }

    return ret;
}

static void print_var_map(struct var_map *map)
{
    while (map) {
        printf("    %s =>", _th_print_exp(map->var));
        printf(" %s\n", _th_print_exp(map->e));
        map = map->next;
    }
}

static void print_add_list(struct add_list *map)
{
    while (map) {
        printf("    %s\n", _th_print_exp(map->e));
        map = map->next;
    }
}

void _th_print_simplex(struct simplex *simplex)
{
    printf("Simplex data structure\n");
    printf("T:\n");
    print_var_map(simplex->T);
    printf("Z:\n");
    print_var_map(simplex->Z);
    printf("R:\n");
    print_var_map(simplex->R);
    printf("D:\n");
    print_add_list(simplex->D);
    printf("W:\n");
    print_var_map(simplex->W);
	printf("Explanation mapping:\n");
	print_var_map(simplex->mapping);
}

struct simplex *_th_new_simplex(struct env *env)
{
    struct simplex *s = (struct simplex *)_th_alloc(_th_get_space(env),sizeof(struct simplex));
    s->T = NULL;
    s->R = NULL;
    s->D = NULL;
    s->Z = NULL;
    s->W = NULL;
    s->push = NULL;
    s->env = env;
    s->mapping = NULL;

    return s;
}

static struct _ex_intern *get_r_coef(struct env *env, struct _ex_intern *exp)
{
	if (exp->type==EXP_APPL && exp->u.appl.functor==INTERN_RAT_TIMES) {
		int i;
		for (i = 0; i < exp->u.appl.count; ++i) {
			if (exp->u.appl.args[i]->type==EXP_RATIONAL) return exp->u.appl.args[i];
		}
	}
	return _ex_intern_small_rational(1,1) ;
}

static struct _ex_intern *strip_r_coef(struct env *env, struct _ex_intern *exp)
{
	if (exp->type==EXP_APPL && exp->u.appl.functor==INTERN_RAT_TIMES) {
		int i;
		for (i = 0; i < exp->u.appl.count; ++i) {
			if (exp->u.appl.args[i]->type==EXP_RATIONAL) {
				int j, k;
				struct _ex_intern **args;
				args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count);
				for (j = 0, k = 0; j < exp->u.appl.count; ++j) {
					if (j != i) {
						args[k++] = exp->u.appl.args[j];
					}
				}
                if (k==1) {
                    return args[0];
                } else {
				    return _ex_intern_appl_env(env,INTERN_RAT_TIMES,k,args);
                }
			}
		}
	}
	return exp;
}

static struct _ex_intern *solve(struct env *env, struct _ex_intern *v, struct _ex_intern *u, struct _ex_intern *e)
{
    int i;

    if (e==v) {
        return u;
    } else if (e->type != EXP_APPL) {
        if (u==v) {
            return e;
        } else {
            return NULL;
        }
    }
    e = _th_nc_rewrite(env,_ex_intern_appl2_env(env,INTERN_RAT_MINUS,e,u));
    printf("Solving %s\n", _th_print_exp(e));
    printf("var %s\n", _th_print_exp(v));
    fflush(stdout);
    if (e->u.appl.functor==INTERN_RAT_PLUS) {
        struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
        int pos = 0;
        struct _ex_intern *coef = NULL;
        for (i = 0; i < e->u.appl.count; ++i) {
            struct _ex_intern *var = strip_r_coef(env,e->u.appl.args[i]);
            if (v==var) {
                coef = get_r_coef(env,e->u.appl.args[i]);
                coef = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(coef->u.rational.numerator)),
                                           coef->u.rational.denominator);
            } else {
                args[pos++] = e->u.appl.args[i];
            }
        }
        if (coef==NULL) return NULL;
        e = _ex_intern_appl2_env(env,INTERN_RAT_DIVIDE,_ex_intern_appl_env(env,INTERN_RAT_PLUS,pos,args),coef);
        e = _th_nc_rewrite(env,e);
        return e;
    }
    if (e->u.appl.functor==INTERN_RAT_TIMES) {
        struct _ex_intern *coef;
        struct _ex_intern *var = strip_r_coef(env,e);
        if (v==var) {
            coef = get_r_coef(env,e);
        } else {
            return NULL;
        }
        e = _ex_intern_appl2_env(env,INTERN_RAT_DIVIDE,u,coef);
        e = _th_nc_rewrite(env,e);
        return e;
    }
    if (u==v) {
        return e;
    } else {
        return NULL;
    }
}

static struct _ex_intern *find_coef(struct env *env, struct _ex_intern *exp, struct _ex_intern *v)
{
    if (exp==v) {
        return _ex_intern_small_rational(0,1);
    }
    if (exp->type != EXP_APPL) return NULL;
    if (exp->u.appl.functor==INTERN_RAT_TIMES) {
        if (strip_r_coef(env,exp)==v) {
            return get_r_coef(env,exp);
        }
        return NULL;
    }
    if (exp->u.appl.functor==INTERN_RAT_PLUS) {
        int i;
        for (i = 0; i < exp->u.appl.count; ++i) {
            struct _ex_intern *e = exp->u.appl.args[i];
            if (strip_r_coef(env,e)==v) {
                return get_r_coef(env,e);
            }
        }
    }
    return NULL;
}

static struct _ex_intern *find_coef_vm(struct env *env, struct var_map *vm, struct var_map *vm2, struct _ex_intern *u, struct _ex_intern *v)
{
    while (vm) {
        if (vm->var==u) return find_coef(env,vm->e,v);
        vm = vm->next;
    }
    while (vm2) {
        if (vm2->var==u) return find_coef(env,vm2->e,v);
        vm2 = vm2->next;
    }
    return NULL;
}

static struct _ex_intern *replace_subterm(struct env *env, struct _ex_intern *e, struct _ex_intern *v, struct _ex_intern *t)
{
    struct _ex_intern **args;
    int i;

    if (e==v) return t;

    if (e->type != EXP_APPL) return e;

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
    for (i = 0; i < e->u.appl.count; ++i) {
        args[i] = replace_subterm(env,e->u.appl.args[i],v,t);
    }

    return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
}

static struct _ex_intern *sub_var_map(struct env *env, struct var_map *vm, struct _ex_intern *e)
{
    while (vm) {
        e = replace_subterm(env,e,vm->var,vm->e);
        vm = vm->next;
    }
    return e;
}

static struct var_map *fusion(struct env *env, struct var_map *v1, struct var_map *v2)
{
    struct var_map *n, *p, *r;

    p = NULL;
    r = NULL;

    while (v1) {
        n = (struct var_map *)_th_alloc(_th_get_space(env),sizeof(struct var_map));
        if (p) {
            p->next = n;
        } else {
            r = n;
        }
        n->next = NULL;
        n->var = v1->var;
        n->e = sub_var_map(env,v2,v1->e);
        p = n;
        v1 = v1->next;
    }

    return r;
}

static struct var_map *fusion2(struct env *env, struct var_map *v1, struct var_map *v2, struct var_map *v3)
{
    struct var_map *n, *p, *r;

    p = NULL;
    r = NULL;

    while (v1) {
        n = (struct var_map *)_th_alloc(_th_get_space(env),sizeof(struct var_map));
        if (p) {
            p->next = n;
        } else {
            r = n;
        }
        n->next = NULL;
        n->var = v1->var;
        n->e = sub_var_map(env,v2,v1->e);
        n->e = sub_var_map(env,v3,n->e);
        p = n;
        v1 = v1->next;
    }

    return r;
}

static struct var_map *compose(struct env *env, struct var_map *v1, struct var_map *v2)
{
    struct var_map *n, *p, *r;

    p = NULL;
    r = NULL;

    while (v1) {
        n = (struct var_map *)_th_alloc(_th_get_space(env),sizeof(struct var_map));
        if (p) {
            p->next = n;
        } else {
            r = n;
        }
        n->next = NULL;
        n->var = v1->var;
        n->e = sub_var_map(env,v2,v1->e);
        p = n;
        v1 = v1->next;
    }

    if (p) {
        p->next = v2;
    } else {
        r = v2;
    }

    return r;
}

static struct var_map *pivot(struct env *env, struct var_map *orig, struct _ex_intern *u, struct _ex_intern *v)
{
    struct var_map *vm = orig, *ret, *t;
    struct _ex_intern *e;

    while (vm) {
        if (vm->var==u) goto cont;
        vm = vm->next;
    }
    return NULL;
cont:
    e = solve(env,v,u,vm->e);
    if (e==NULL) return NULL;

    ret = NULL;
    while (orig) {
        t = (struct var_map *)_th_alloc(_th_get_space(env),sizeof(struct var_map));
        t->next = ret;
        ret = t;
        if (orig==vm) {
            t->var = v;
            t->e = e;
        } else {
            t->var = orig->var;
            t->e = _th_nc_rewrite(env,replace_subterm(env,orig->e,v,e));
        }
        orig = orig->next;
    }
    return ret;
}

static struct _ex_intern *abs_e(struct _ex_intern *e)
{
    if (e->type==EXP_RATIONAL) return e;

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_PLUS) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type==EXP_RATIONAL) return e->u.appl.args[i];
        }
    }
    return _ex_intern_small_rational(0,1);
}

static struct _ex_intern *abs_vm(struct var_map *vm, struct var_map *vm2, struct _ex_intern *u)
{
    while (vm) {
        if (vm->var==u) return abs_e(vm->e);
        vm = vm->next;
    }
    while (vm2) {
        if (vm2->var==u) return abs_e(vm2->e);
        vm2 = vm2->next;
    }
    return _ex_intern_small_rational(0,1);
}

static struct _ex_intern *gain(struct env *env, struct var_map *vm, struct var_map *vm2, struct _ex_intern *u, struct _ex_intern *v)
{
    struct _ex_intern *a_vm = abs_vm(vm, vm2, u);
    struct _ex_intern *fc_vm = find_coef_vm(env,vm,vm2, u,v);
    struct _ex_intern *r;
    if (a_vm==NULL || fc_vm==NULL) return NULL;
    r = _th_divide_rationals(a_vm,fc_vm);
    r = _ex_intern_rational(
            _th_big_copy(REWRITE_SPACE,_th_complement(r->u.rational.numerator)),r->u.rational.denominator);
    return r;
}

static struct _ex_intern *get_pivotable(struct env *env, struct var_map *vm, struct var_map *vm2, struct _ex_intern *v)
{
    struct _ex_intern *u, *max;
    struct var_map *vml;
    max = NULL;
    vml = vm;
    u = NULL;
    while (vml) {
        struct _ex_intern *m = gain(env,vm,vm2,vml->var,v);
        if (m) {
            if (max==NULL || _th_rational_less(max,m) || (max==m && vml->var < u)) {
                max = m;
                u = vml->var;
            }
        }
        vml = vml->next;
    }
    vml = vm2;
    u = NULL;
    while (vml) {
        struct _ex_intern *m = gain(env,vm,vm2,vml->var,v);
        if (m) {
            if (max==NULL || _th_rational_less(max,m) || (max==m && vml->var < u)) {
                max = m;
                u = vml->var;
            }
        }
        vml = vml->next;
    }

    return u;
}

static struct _ex_intern *G(struct env *env, struct var_map *vm, struct var_map *vm2, struct _ex_intern *v)
{
    struct _ex_intern *u = get_pivotable(env,vm,vm2,v);

    if (u) {
        return gain(env,vm,vm2,u,v);
    } else {
        return NULL;
    }
}

static struct _ex_intern *get_bland_var(struct env *env, struct var_map *vm, struct _ex_intern *a)
{
    int count;
    int i;
    unsigned *fv = _th_get_free_vars(a,&count);
    struct _ex_intern *rv = NULL;

    for (i = 0; i < count; ++i) {
        struct _ex_intern *v = _ex_intern_var(fv[i]);
        struct _ex_intern *c = find_coef(env,a,v);
        struct _ex_intern *u = get_pivotable(env,vm,NULL,v);
        struct var_map *vm1 = vm;
        if (u==NULL) goto skip;
        while (vm1) {
            if (vm1->var==v) goto cont;
            vm1 = vm1->next;
        }
        goto skip;
cont:
        if (!_th_big_is_negative(c->u.rational.numerator)) {
            if (rv==NULL || v < rv) rv = v;
        }
skip:;
    }

    return rv;
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

static int vn = 1;

static struct _ex_intern *get_var(struct env *env, struct _ex_intern *type)
{
    char name[20];

    sprintf(name, "@slack_%d", vn++);
    _th_set_var_type(env,_th_intern(name),type);
    return _ex_intern_var(_th_intern(name));
}

static struct _ex_intern *get_zvar(struct env *env, struct _ex_intern *type)
{
    char name[20];

    sprintf(name, "@zslack_%d", vn++);
    _th_set_var_type(env,_th_intern(name),type);
    return _ex_intern_var(_th_intern(name));
}

int _th_is_linear_equation(struct _ex_intern *e)
{
}

static int is_slack(struct _ex_intern *var)
{
    char *c;

    if (var->type != EXP_VAR) return 0;
    c = _th_intern_decode(var->u.var);
    return c[0]=='@' && ((c[1]=='s' && c[2]=='l' && c[3]=='a' && c[4]=='c' && c[5]=='k') ||
                         (c[1]=='z' && c[2]=='s' && c[3]=='l' && c[4]=='a' && c[5]=='c' && c[6]=='k'));
}

static int var_is_present(struct _ex_intern *var, struct _ex_intern *e)
{
    int i;

    if (e==var) return 1;

    if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_RAT_PLUS || e->u.appl.functor==INTERN_RAT_TIMES)) {
        for (i = 0; i < e->u.appl.count; ++i) {
            if (var_is_present(var,e->u.appl.args[i])) return 1;
        }
    }

    return 0;
}

static int is_zero(struct _ex_intern *var, struct var_map *Z)
{
    char *c;

    while (Z) {
        if (Z->var==var || var_is_present(var,Z->e)) return 1;
        Z = Z->next;
    }
    if (var->type != EXP_VAR) return 0;
    c = _th_intern_decode(var->u.var);
    return c[0]=='@' && c[1]=='z' && c[2]=='s' && c[3]=='l' && c[4]=='a' && c[5]=='c' && c[6]=='k';
}

static struct _ex_intern *maximized(struct env *env, struct _ex_intern *e, struct var_map *Z)
{
    struct _ex_intern *max;

    if (e->type==EXP_RATIONAL) return e;

    max = NULL;
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_TIMES) {
        struct _ex_intern *coef = get_r_coef(env,e);
        struct _ex_intern *core = strip_r_coef(env,e);
        if (!is_slack(core) && !is_zero(core,Z)) return NULL;
        if (!is_zero(core,Z) && !_th_big_is_negative(coef->u.rational.numerator)) return NULL;
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_PLUS) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type==EXP_RATIONAL) {
                max = e->u.appl.args[i];
            } else {
                struct _ex_intern *coef = get_r_coef(env,e->u.appl.args[i]);
                struct _ex_intern *core = strip_r_coef(env,e->u.appl.args[i]);
                if (!is_slack(core) && !is_zero(core,Z)) return NULL;
                if (!is_zero(core,Z) && !_th_big_is_negative(coef->u.rational.numerator)) return NULL;
            }
        }
    }
    if (max==NULL) max = _ex_intern_small_rational(0,1);

    return max;
}

static struct _ex_intern *minimized(struct env *env, struct _ex_intern *e, struct var_map *Z)
{
    struct _ex_intern *min;

    if (e->type==EXP_RATIONAL) return e;

    min = NULL;
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_TIMES) {
        struct _ex_intern *coef = get_r_coef(env,e);
        struct _ex_intern *core = strip_r_coef(env,e);
        if (!is_slack(core) && !is_zero(core,Z)) return NULL;
        if (!is_zero(core,Z) && _th_big_is_negative(coef->u.rational.numerator)) return NULL;
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_PLUS) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type==EXP_RATIONAL) {
                min = e->u.appl.args[i];
            } else {
                struct _ex_intern *coef = get_r_coef(env,e->u.appl.args[i]);
                struct _ex_intern *core = strip_r_coef(env,e->u.appl.args[i]);
                if (!is_slack(core) && !is_zero(core,Z)) return NULL;
                if (!is_zero(core,Z) && _th_big_is_negative(coef->u.rational.numerator)) return NULL;
            }
        }
    }
    if (min==NULL) min = _ex_intern_small_rational(0,1);

    return min;
}

static int is_zero_term(struct env *env, struct _ex_intern *e, struct var_map *Z)
{
    if (e->type==EXP_RATIONAL) return e->u.rational.numerator[0]==1 && e->u.rational.numerator[1]==0;

    printf("Zero term %s\n", _th_print_exp(e));

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_TIMES) {
        struct _ex_intern *core = strip_r_coef(env,e);
        if (!is_zero(core,Z)) return 0;
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_PLUS) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type==EXP_RATIONAL) {
              if (e->u.appl.args[i]->u.rational.numerator[0]!=1 ||
                  e->u.appl.args[i]->u.rational.numerator[1]!=0) return 0;
           } else {
                struct _ex_intern *core = strip_r_coef(env,e->u.appl.args[i]);
                if (!is_zero(core,Z)) return 0;
            }
        }
    } else {
        if (!is_zero(e,Z)) return 0;
    }

    return 1;
}

static int used_in_exp(struct _ex_intern *v, struct _ex_intern *e)
{
    int i;

    if (v==e) return 1;

    if (e->type==EXP_APPL) {
        for (i = 0; i < e->u.appl.count; ++i) {
            if (used_in_exp(v,e->u.appl.args[i])) return 1;
        }
    }

    return 0;
}

static int used_in_map(struct _ex_intern *e, struct var_map *map)
{
    while (map) {
        if (used_in_exp(e,map->e)) return 1;
        map = map->next;
    }
    return 0;
}

static struct add_list *get_non_slack_positives(struct env *env, struct _ex_intern *e, struct var_map *t, struct var_map *z)
{
    struct add_list *vl = NULL, *v;
    if (e->type==EXP_RATIONAL) return NULL;

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_TIMES) {
        struct _ex_intern *core = strip_r_coef(env,e);
        struct _ex_intern *coef = get_r_coef(env,e);
        if (!_th_big_is_negative(coef->u.rational.numerator) && !is_zero(core,z) && !used_in_map(core,t) &&
            !used_in_map(core,z)) {
            v = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            v->next = vl;
            vl = v;
            v->e = core;
        }
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_PLUS) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type!=EXP_RATIONAL) {
                struct _ex_intern *core = strip_r_coef(env,e->u.appl.args[i]);
                struct _ex_intern *coef = get_r_coef(env,e->u.appl.args[i]);
                if (!_th_big_is_negative(coef->u.rational.numerator) && !is_zero(core,z) && !used_in_map(core,t) &&
                    !used_in_map(core,z)) {
                    v = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                    v->next = vl;
                    vl = v;
                    v->e = core;
                }
            }
        }
    }

    return vl;
}

static struct add_list *get_non_slack_all(struct env *env, struct _ex_intern *e, struct var_map *z)
{
    struct add_list *vl = NULL, *v;
    if (e->type==EXP_RATIONAL) return NULL;

    printf("e = %s\n", _th_print_exp(e));
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_TIMES) {
        struct _ex_intern *core = strip_r_coef(env,e);
        printf("core = %s\n", _th_print_exp(core));
        //struct _ex_intern *coef = get_r_coef(env,e);
        if (!is_zero(core,z) && !used_in_map(core,z)) {
            v = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            v->next = vl;
            vl = v;
            v->e = core;
        }
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_PLUS) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            if (e->u.appl.args[i]->type!=EXP_RATIONAL) {
                struct _ex_intern *core = strip_r_coef(env,e->u.appl.args[i]);
                printf("core[%d] = %s\n", i, _th_print_exp(core));
                //struct _ex_intern *coef = get_r_coef(env,e->u.appl.args[i]);
                if (!is_zero(core,z) && !used_in_map(core,z)) {
                    v = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                    v->next = vl;
                    vl = v;
                    v->e = core;
                }
            }
        }
    }

    return vl;
}

struct _ex_intern *get_non_slack(struct _ex_intern *e, struct var_map *Z)
{
    if (e->type == EXP_RATIONAL) return NULL;
    if (e->type != EXP_APPL) {
        if (is_slack(e) || is_zero(e,Z)) {
            return NULL;
        } else {
            return e;
        }
    }

    if (e->u.appl.functor==INTERN_RAT_PLUS || e->u.appl.functor==INTERN_RAT_TIMES ||
        e->u.appl.functor==INTERN_RAT_DIVIDE || e->u.appl.functor==INTERN_RAT_MINUS ||
        e->u.appl.functor==INTERN_EQUAL || e->u.appl.functor==INTERN_RAT_LESS ||
        e->u.appl.functor==INTERN_NOT) {
        int i;
        struct _ex_intern *f;
        for (i = 0; i < e->u.appl.count; ++i) {
            if (f = get_non_slack(e->u.appl.args[i],Z)) return f;
        }
        return NULL;
    }

    if (is_slack(e) || is_zero(e,Z)) {
        return NULL;
    } else {
        return e;
    }
}

static void add_eq_r(struct simplex *simplex, struct _ex_intern *v, struct _ex_intern *e)
{
    struct var_map *l = simplex->R, *n, *nn;
    struct env *env = simplex->env;

    printf("add_eq_r\n");

    n = NULL;
    while (l) {
        nn = (struct var_map *)_th_alloc(_th_get_space(env),sizeof(struct var_map));
        nn->next = n;
        n = nn;
        n->e = _th_nc_rewrite(simplex->env,replace_subterm(env,l->e,v,e));
        n->var = l->var;
        l = l->next;
    }
    nn = (struct var_map *)_th_alloc(_th_get_space(env),sizeof(struct var_map));
    nn->next = n;
    n = nn;
    n->var = v;
    n->e = e;
    simplex->R = n;
}

static int is_negative(struct simplex *simplex, struct _ex_intern *e)
{
    if (e->type==EXP_RATIONAL) {
        return _th_big_is_negative(e->u.rational.numerator);
    }
    if (e->type!=EXP_APPL) return 0;
    if (e->u.appl.functor==INTERN_RAT_PLUS) {
        int i;
        int negative = 0;
        int positive = 0;
        int sign = 0;
        for (i = 0; i < e->u.appl.count; ++i) {
            struct _ex_intern *coef = get_r_coef(simplex->env,e->u.appl.args[i]);
            struct _ex_intern *core = strip_r_coef(simplex->env,e->u.appl.args[i]);
            if (!is_zero(core,simplex->Z) && is_slack(core)) {
                if (_th_big_is_negative(coef->u.rational.numerator)) {
                    negative = 1;
                } else {
                    positive = 1;
                }
            }
            if (core->type==EXP_RATIONAL) {
                if (_th_big_is_negative(coef->u.rational.numerator)) {
                    sign = -1;
                } else {
                    sign = 1;
                }
            }
        }
        return (sign < 0 && positive==0);
    } else if (e->u.appl.functor==INTERN_RAT_TIMES) {
        struct _ex_intern *coef = get_r_coef(simplex->env,e);
        struct _ex_intern *core = strip_r_coef(simplex->env,e);
        if (core->type==EXP_RATIONAL) {
            if (_th_big_is_negative(coef->u.rational.numerator)) {
                return 1;
            }
        }
        return 0;
    } else {
        return 0;
    }
}

static int is_negative_in(struct env *env, struct _ex_intern *v, struct _ex_intern *e)
{
    if (e->type!=EXP_APPL) return 0;
    if (e->u.appl.functor==INTERN_RAT_PLUS) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            struct _ex_intern *coef = get_r_coef(env,e->u.appl.args[i]);
            struct _ex_intern *core = strip_r_coef(env,e->u.appl.args[i]);
            if (core == v && _th_big_is_negative(coef->u.rational.numerator)) {
                return 1;
            }
        }
        return 0;
    } else if (e->u.appl.functor==INTERN_RAT_TIMES) {
        struct _ex_intern *coef = get_r_coef(env,e);
        struct _ex_intern *core = strip_r_coef(env,e);
        if (core == v && _th_big_is_negative(coef->u.rational.numerator)) {
            return 1;
        }
        return 0;
    }
    return 0;
}

struct var_map *add_mapping(struct env *env, struct var_map *map, struct _ex_intern *v, struct _ex_intern *e)
{
    struct var_map *m;

    printf("Add mapping\n");

    e = sub_var_map(env,map,e);
    e = _th_nc_rewrite(env,e);

    m = map;
    while (m) {
        m->e = solve(env,m->var,m->var,replace_subterm(env,m->e,v,e));
        m->e = _th_nc_rewrite(env ,m->e);
        m = m->next;
    }

    m = (struct var_map *)_th_alloc(_th_get_space(env),sizeof(struct var_map));
    m->next = map;
    m->var = v;
    m->e = e;
    m->next = map;

    return m;
}

static int bound_in_exp(struct env *env, struct _ex_intern *v, struct _ex_intern *e)
{
    if (e->type==EXP_APPL) {
        if (e->u.appl.functor==INTERN_RAT_PLUS) {
            int i;
            for (i = 0; i < e->u.appl.count; ++i) {
                if (e->u.appl.args[i]->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_TIMES) {
                    struct _ex_intern *core = strip_r_coef(env,e->u.appl.args[i]);
                    struct _ex_intern *coef = get_r_coef(env,e->u.appl.args[i]);
                    if (core==e && (!core->u.rational.numerator[0]==1 || !core->u.rational.numerator[1]==0) && _th_big_is_negative(core->u.rational.numerator)) return 1;
                }
            }
        } else if (e->u.appl.functor==INTERN_RAT_TIMES) {
            struct _ex_intern *core = strip_r_coef(env,e);
            struct _ex_intern *coef = get_r_coef(env,e);
            if (core==e && (!core->u.rational.numerator[0]==1 || !core->u.rational.numerator[1]==0) && _th_big_is_negative(core->u.rational.numerator)) return 1;
        }
    }
    return 0;
}

static int unbound(struct env *env, struct var_map *map, struct _ex_intern *e)
{
    while (map) {
        if (bound_in_exp(env,e,map->e)) return 0;
        map = map->next;
    }
    return 1;
}

static int unbound_exp(struct env *env, struct var_map *map, struct _ex_intern *e)
{
    if (e->type != EXP_APPL) {
        return unbound(env,map,e);
    }

    if (e->u.appl.functor==INTERN_RAT_TIMES) {
        struct _ex_intern *core = strip_r_coef(env,e);
        return unbound(env,map,core);
    } else if (e->u.appl.functor==INTERN_RAT_PLUS) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            struct _ex_intern *core = strip_r_coef(env,e->u.appl.args[i]);
            if (unbound(env,map,core)) return 1;
        }
        return 0;
    } else {
        return unbound(env,map,e);
    }
}

static int unbound2_exp(struct env *env, struct var_map *map, struct var_map *map2, struct _ex_intern *e)
{
    if (e->type != EXP_APPL) {
        return unbound(env,map,e);
    }

    if (e->u.appl.functor==INTERN_RAT_TIMES) {
        struct _ex_intern *core = strip_r_coef(env,e);
        return unbound(env,map,core) && unbound(env,map2,core);
    } else if (e->u.appl.functor==INTERN_RAT_PLUS) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            struct _ex_intern *core = strip_r_coef(env,e->u.appl.args[i]);
            if (unbound(env,map,core) && unbound(env,map2,core)) return 1;
        }
        return 0;
    } else {
        return unbound(env,map,e) && unbound(env,map2,e);
    }
}

static struct _ex_intern *ret_a;

static struct var_map *s_max(struct env *env, struct var_map *vm, struct _ex_intern *a)
{
    while (1) {
        struct _ex_intern *v;
        struct _ex_intern *u;
        if (unbound_exp(env,vm,a)) return vm;
        v = get_bland_var(env,vm,a);
        if (v) {
            u = get_pivotable(env,vm,NULL,v);
            vm = pivot(env,vm,u,v);
            a = _th_nc_rewrite(env,sub_var_map(env,vm,a));
        } else {
            ret_a = a;
            return vm;
        }
    }
}

static struct var_map *s_max0(struct env *env, struct var_map *vm, struct _ex_intern *a)
{
    while (1) {
        struct _ex_intern *v;
        struct _ex_intern *u;
        struct _ex_intern *ab;
        if (unbound_exp(env,vm,a)) {
            ret_a = a;
            return vm;
        }
        ab = abs_e(a);
        if (!_th_big_is_negative(ab->u.rational.numerator) &&
            (ab->u.rational.numerator[0] != 1 || ab->u.rational.numerator[1] != 0)) {
            ret_a = a;
            return vm;
        }
        v = get_bland_var(env,vm,a);
        if (v) {
            u = get_pivotable(env,vm,NULL,v);
            vm = pivot(env,vm,u,v);
            a = _th_nc_rewrite(env,sub_var_map(env,vm,a));
        } else {
            ret_a = a;
            return vm;
        }
    }
}

static struct var_map *nzbnd;

struct var_map *zbnd_star(struct env *env, struct  var_map *T, struct var_map *Z)
{
    int change = 1;
    struct var_map *v, *p, *retT, *n;

    v = T;
    p = NULL;
    while (v) {
        n = (struct var_map *)_th_alloc(_th_get_space(env),sizeof(struct var_map));
        if (p) {
            p->next = n;
        } else {
            T = n;
        }
        n->e = v->e;
        n->var = v->var;
        p = n;
        v = v->next;
    }
    if (p) {
        p->next = NULL;
    } else {
        T = NULL;
    }

    nzbnd = NULL;

    retT = T;
    while (change) {
        change = 0;
        v = retT;
        p = NULL;
        while (v) {
            struct _ex_intern *e = abs_e(v->e);
            struct var_map *vn = v->next;
            int skip = 0;
            if (e->u.rational.numerator[0]==1 && e->u.rational.numerator[1]==0) {
                if (!unbound_exp(env,T,v->e)) {
                    skip = 1;
                }
            } else {
                skip = 1;
            }
            if (skip) {
                change = 1;
                if (p) {
                    p->next = v->next;
                } else {
                    retT = v->next;
                }
                v->next = nzbnd;
                nzbnd = v;
            } else {
                p = v;
            }
            v = vn;
        }
    }

    return retT;
}

static int has_the_term(struct add_list *l, struct _ex_intern *v)
{
    while (l) {
        if (l->e==v) return 1;
        l = l->next;
    }

    return 0;
}

static struct add_list *get_nz_pos_vars(struct env *env, struct _ex_intern *e, struct var_map *Z, struct add_list *res)
{
    struct add_list *n;

    if (e->type == EXP_RATIONAL) return res;
    if (e->type != EXP_APPL) {
        if (!is_zero(e,Z) && !has_the_term(res,e)) {
            n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            n->next = res;
            res = n;
            n->e = e;
        }
        return res;
    }

    if (e->u.appl.functor==INTERN_RAT_PLUS) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            res = get_nz_pos_vars(env,e->u.appl.args[i],Z,res);
        }
        return res;
    }

    if (e->u.appl.functor==INTERN_RAT_TIMES) {
        struct _ex_intern *var = strip_r_coef(env,e);
        struct _ex_intern *coef = get_r_coef(env,e);

        if (!is_zero(var,Z) && !_th_big_is_negative(coef->u.rational.numerator) && !has_the_term(res,var)) {
            n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            n->next = res;
            res = n;
            n->e = var;
        }
        return res;
    }

    if (!is_zero(e,Z) && !has_the_term(res,e)) {
        n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        n->next = res;
        res = n;
        n->e = e;
        return res;
    }

    return res;
}

static struct add_list *get_nz_all_vars(struct env *env, struct _ex_intern *e, struct var_map *Z, struct add_list *res)
{
    struct add_list *n;

    if (e->type == EXP_RATIONAL) return res;
    if (e->type != EXP_APPL) {
        if (!is_zero(e,Z) && !has_the_term(res,e)) {
            n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            n->next = res;
            res = n;
            n->e = e;
        }
        return res;
    }

    if (e->u.appl.functor==INTERN_RAT_PLUS) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            res = get_nz_pos_vars(env,e->u.appl.args[i],Z,res);
        }
        return res;
    }

    if (e->u.appl.functor==INTERN_RAT_TIMES) {
        struct _ex_intern *var = strip_r_coef(env,e);
        struct _ex_intern *coef = get_r_coef(env,e);

        if (!is_zero(var,Z) && !has_the_term(res,var)) {
            n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            n->next = res;
            res = n;
            n->e = var;
        }
        return res;
    }

    if (!is_zero(e,Z) && !has_the_term(res,e)) {
        n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        n->next = res;
        res = n;
        n->e = e;
        return res;
    }

    return res;
}

static struct add_list *get_nz_neg_vars(struct env *env, struct _ex_intern *e, struct var_map *Z, struct add_list *res)
{
    struct add_list *n;

    if (e->type != EXP_APPL) {
        return res;
    }

    if (e->u.appl.functor==INTERN_RAT_PLUS) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            res = get_nz_neg_vars(env,e->u.appl.args[i],Z,res);
        }
        return res;
    }

    if (e->u.appl.functor==INTERN_RAT_TIMES) {
        struct _ex_intern *var = strip_r_coef(env,e);
        struct _ex_intern *coef = get_r_coef(env,e);

        if (!is_zero(var,Z) && _th_big_is_negative(coef->u.rational.numerator) && !has_the_term(res,var)) {
            n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            n->next = res;
            res = n;
            n->e = var;
        }
        return res;
    }

    return res;
}

static struct var_map *add_map(struct var_map *vm, struct _ex_intern *v, struct _ex_intern *e)
{
    struct var_map *n = vm;

    while (n) {
        if (n->var==v && n->e==e) return vm;
        n = n->next;
    }

    n = (struct var_map *)_th_alloc(REWRITE_SPACE,sizeof(struct var_map));
    n->next = vm;
    n->var = v;
    n->e = e;

    return n;
}

struct var_map *tc(struct var_map *vm)
{
    int added;
    struct var_map *n, *p1, *p2;

    added = 1;
    while (added) {
        added = 0;
        p1 = vm;
        while (p1) {
            p2 = vm;
            while (p2) {
                if (p1->e==p2->var) {
                    n = add_map(vm,p1->var,p2->e);
                    if (n != vm) {
                        vm = n;
                        added = 1;
                    }
                }
                p2 = p2->next;
            }
            p1 = p1->next;
        }
    }

    return vm;
}

static struct var_map *build_llcompare(struct simplex *simplex, struct var_map *Tp, struct var_map *Zp)
{
    struct var_map *Tpp, *vm, *res;
    struct add_list *vl = NULL, *v;

    vm = Tp;
    while (Tp) {
        vl = get_nz_all_vars(simplex->env,vm->e,Zp,vl);
        if (!has_the_term(vl,vm->var)) {
            v = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            v->next = vl;
            vl = v;
            v->e = vm->var;
        }
        vm = vm->next;
    }

    Tpp = zbnd_star(simplex->env,simplex->T,simplex->Z);

    vm = Tpp;

    res = NULL;

    while (vm) {
        struct add_list *pvars = get_nz_pos_vars(simplex->env,vm->e,simplex->Z,NULL);
        struct add_list *nvars = get_nz_neg_vars(simplex->env,vm->e,simplex->Z,NULL);
        struct add_list *nv;

        while (pvars) {
            if (!has_the_term(vl,pvars->e)) {
                nv = nvars;
                while (nv) {
                    if (!has_the_term(vl,nv->e)) {
                        res = add_map(res,pvars->e,nvars->e);
                    }
                    nv = nv->next;
                }
            }
            pvars = pvars->next;
        }
        vm = vm->next;
    }

    vm = Tp;

    while (vm) {
        struct add_list *pvars = get_nz_pos_vars(simplex->env,vm->e,simplex->Z,NULL);
        struct add_list *nvars = get_nz_neg_vars(simplex->env,vm->e,simplex->Z,NULL);
        struct add_list *nv;

        while (pvars) {
            nv = nvars;
            while (nv) {
                res = add_map(res,pvars->e,nvars->e);
                nv = nv->next;
            }
            pvars = pvars->next;
        }
        vm = vm->next;
    }

    vm = Tpp;

    while (vm) {
        struct add_list *vars = get_nz_all_vars(simplex->env,vm->e,simplex->Z,NULL);
        if (!has_the_term(vars,vm->var)) {
            v = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
            v->next = vars;
            vars = v;
            v->e = vm->var;
        }

        while (vars) {
            if (!has_the_term(vl,vars->e)) {
                v = vl;
                while (v) {
                    res = add_map(res,vars->e,v->e);
                    v = v->next;
                }
            }
            vars = vars->next;
        }
        vm = vm->next;
    }
    res = tc(res);

    return res;
}

static struct var_map *ret_z;

static struct var_map *maxentries(struct env *env, struct var_map *T, struct var_map *Z);

static struct var_map *FindZeros(struct env *env, struct var_map *T, struct var_map *Z)
{
    struct var_map *Zp, *Tp, *Tpp;

    if (T==NULL) {
        ret_z = Z;
        return T;
    }

    Tpp = zbnd_star(env,T,Z);
    printf("zbnd_star\n");
    print_var_map(Tpp);
    fflush(stdout);
    Tpp = maxentries(env, Tpp, Z);
    Zp = ret_z;

    Tp = compose(env,fusion(env,nzbnd,Zp),Tpp);

    return Tp;
}

static struct var_map *move(struct env *env, struct var_map *T, struct var_map *Z)
{
    struct _ex_intern *e_p;
    struct var_map *Tp;

    struct _ex_intern *e = T->e;
    struct _ex_intern *u = T->var;

    struct _ex_intern *m;

    T = T->next;

    printf("Move\n");
    fflush(stdout);

    Tp = s_max0(env,T,e);
    e_p = ret_a;

    m = maximized(env,e,Z);
    if (m != NULL && m->u.rational.numerator[0]==1 && m->u.rational.numerator[1]==0) {
        struct var_map *vm = (struct var_map *)_th_alloc(_th_get_space(env),sizeof(struct var_map));
        printf("case 2\n");
        fflush(stdout);
        vm->next = Z;
        vm->var = u;
        vm->e = e_p;
        ret_z =vm;
        return Tp;
    }

    if (unbound_exp(env,Tp,e)) {
        struct var_map *vm = (struct var_map *)_th_alloc(_th_get_space(env),sizeof(struct var_map));
        printf("case 1\n");
        fflush(stdout);
        vm->next = Tp;
        vm->var = u;
        vm->e = e_p;
        ret_z = Z;
        return vm;
    }

    fprintf(stderr, "Illegal move operation\n");
    exit(1);
}

static struct var_map *maxentries(struct env *env, struct var_map *T, struct var_map *Z)
{
    struct var_map *Tp;

    if (T==NULL) {
        ret_z = Z;
        return T;
    }

    printf("Here1\n");
    fflush(stdout);
    Tp = move(env,T,Z);
    printf("Here2\n");
    fflush(stdout);

    Tp = FindZeros(env,Tp,ret_z);

    return Tp;
}

//static struct var_map *npf;

static struct var_map *posvar_filter(struct env *env, struct var_map *T, struct var_map *Z, struct var_map *Tp)
{
    struct var_map *n, *pf, *v, *v2;
    struct add_list *p, *pp;
    int skip;

    pf = NULL;
    v = T;

    while (v) {
        struct _ex_intern *abse = abs_e(v->e);
        if (abse->u.rational.numerator[0]==1 && abse->u.rational.numerator[1]==0) {
            p = get_non_slack_positives(env,v->e,NULL,NULL);
            v2 = Tp;
            while (v2) {
                pp = p;
                while (pp) {
                    if (is_negative_in(env,pp->e,v2->e)) {
                        skip = 0;
                        goto cont;
                    }
                    pp = pp->next;
                }
                v2 = v2->next;
            }
            skip = 1;
        } else {
            skip = 1;
        }
cont:
        if (!skip) {
            n = (struct var_map *)_th_alloc(_th_get_space(env),sizeof(struct var_map));
            n->e = v->e;
            n->var = v->var;
            n->next = pf;
            pf = n;
        }
        v = v->next;
    }

    return pf;
}

static struct var_map *union_maps(struct env *env, struct var_map *m1, struct var_map *m2)
{
    struct var_map *n;

    while (m1) {
        n = m2;
        while (n) {
            if (n->e==m1->e && n->var==m1->var) goto cont;
            n = n->next;
        }
        n = (struct var_map *)_th_alloc(_th_get_space(env),sizeof(struct var_map));
        n->next = m2;
        n->e = m1->e;
        n->var = m1->var;
        m2 = n;
cont:
        m1 = m1->next;
    }

    return m2;
}

static struct var_map *diff_maps(struct env *env, struct var_map *m1, struct var_map *m2)
{
    struct var_map *n, *ret;

    ret = NULL;

    while (m1) {
        n = m2;
        while (n) {
            if (n->e==m1->e && n->var==m1->var) goto cont;
            n = n->next;
        }
        n = (struct var_map *)_th_alloc(_th_get_space(env),sizeof(struct var_map));
        n->next = ret;
        n->e = m1->e;
        n->var = m1->var;
        ret = n;
cont:
        m1 = m1->next;
    }

    return ret;
}

static struct var_map *incbounded(struct env *env, struct var_map *T, struct var_map *Z, struct var_map *Tp)
{
    struct var_map *R = posvar_filter(env,T,Z,Tp);

    printf("Here1\n");
    fflush(stdout);

    if (R==NULL) return Tp;

    return incbounded(env,T,Z,union_maps(env,R,Tp));
}

static struct var_map *zero(struct env *env, struct var_map *m)
{
    struct var_map *n, *ret;

    ret = NULL;

    while (m) {
        struct _ex_intern *abse = abs_e(m->e);
        if (abse->u.rational.numerator[0]==1 && abse->u.rational.numerator[1]==0) {
            n = (struct var_map *)_th_alloc(_th_get_space(env),sizeof(struct var_map));
            n->next = ret;
            ret = n;
            n->e = m->e;
            n->var = m->var;
        }
        m = m->next;
    }

    return ret;
}

static inc_zeros(struct simplex *simplex, struct _ex_intern *u, struct _ex_intern *e)
{
    struct var_map ue, *Tp, *Tpp, *Tplus, *That;

    printf("inc zeros %s\n", _th_print_exp(e));

    ue.var = u;
    ue.e = e;
    ue.next = NULL;

    Tp = compose(simplex->env,simplex->T,copy_var_map(_th_get_space(simplex->env),&ue));
    printf("Tp\n");
    print_var_map(Tp);
    fflush(stdout);
    Tpp = incbounded(simplex->env,simplex->T,simplex->Z,zero(simplex->env,diff_maps(simplex->env,Tp,simplex->T)));
    printf("Tpp\n");
    print_var_map(Tpp);
    fflush(stdout);
    Tplus = diff_maps(simplex->env,simplex->T,Tpp);
    printf("Tplus\n");
    print_var_map(Tplus);
    That = FindZeros(simplex->env,Tpp,simplex->Z);
    printf("That\n");
    print_var_map(That);
    printf("ret_z\n");
    print_var_map(ret_z);

    simplex->Z = ret_z;
    simplex->T = fusion(simplex->env,compose(simplex->env,Tplus,That),simplex->Z);
}

static struct add_list *add_sl(struct add_list *list, struct _ex_intern *s)
{
    struct add_list *l = list;

    while (l) {
        if (l->e==s) return list;
        l = l->next;
    }

    l = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
    l->next = list;
    l->e = s;

    return l;
}

static struct add_list *add_sl_exp(struct add_list *list, struct _ex_intern *s)
{
    int i;

    if (s->type != EXP_APPL) return add_sl(list,s);

    if (s->u.appl.functor != INTERN_RAT_TIMES && s->u.appl.functor != INTERN_RAT_PLUS) {
        return add_sl(list,s);
    }

    for (i = 0; i < s->u.appl.count; ++i) {
        list = add_sl_exp(list,s);
    }

    return list;
}

static int appears_in_map(struct _ex_intern *e, struct var_map *map)
{
    while (map) {
        if (e==map->var) return 1;
        if (used_in_exp(e,map->e)) return 1;
        map = map->next;
    }
    return 0;
}

static int appears_in_map_except(struct _ex_intern *e, struct var_map *map, struct var_map *node)
{
    while (map) {
        if (map != node) {
            if (e==map->var) return 1;
            if (used_in_exp(e,map->e)) return 1;
        }
        map = map->next;
    }
    return 0;
}

static struct add_list *max_proof(struct env *env, struct var_map *Z, struct var_map *W, struct _ex_intern *e,struct add_list *tail);

static struct add_list *zero_proof(struct env *env, struct var_map *Z, struct var_map *W, struct _ex_intern *v, struct add_list *tail)
{
    struct var_map *z = Z;
    struct _ex_intern *e;
    struct var_map *n, *p, *l;

    while (z) {
        if (appears_in_map_except(v,Z,z)) {
            l = Z;
            p = NULL;
            while (l && l != z) {
                n = (struct var_map *)ALLOCA(sizeof(struct var_map));
                if (p) {
                    p->next = n;
                } else {
                    Z = n;
                }
                p = n;
                l = l->next;
            }
            if (p) {
                p->next = z->next;
            } else {
                Z = z->next;
            }
            return zero_proof(env,Z,W,v,tail);
        }
        z = z->next;
    }

    e = sub_var_map(env,Z,v);
    if (e != v && !appears_in_map(v,Z)) {
        l = Z;
        p = NULL;
        while (l && l->var != v) {
            n = (struct var_map *)ALLOCA(sizeof(struct var_map));
            if (p) {
                p->next = n;
            } else {
                Z = n;
            }
            p = n;
            l = l->next;
        }
        if (p) {
            p->next = l->next;
        } else {
            Z = z->next;
        }
        tail = add_sl_exp(tail,sub_var_map(env,W,v));
        return max_proof(env,Z,W,_th_int_rewrite(env,e,0),tail);
    }
    z = Z;
    while (z) {
        if (z->var != v) {
            struct _ex_intern *eprime = solve(env,v,z->var,z->e);
            l = Z;
            p = NULL;
            while (l && l != z) {
                n = (struct var_map *)ALLOCA(sizeof(struct var_map));
                if (p) {
                    p->next = n;
                } else {
                    Z = n;
                }
                p = n;
                l = l->next;
            }
            if (p) {
                p->next = z->next;
            } else {
                Z = z->next;
            }
            z = (struct var_map *)ALLOCA(sizeof(struct var_map));
            z->next = Z;
            Z = z;
            z->e = eprime;
            z->var = v;
            return zero_proof(env,Z,W,v,tail);
        }
        z = z->next;
    }
    fprintf(stderr, "Error in zero\n");
    exit(1);
    return tail;
}

static struct add_list *max_proof(struct env *env, struct var_map *Z, struct var_map *W, struct _ex_intern *e,struct add_list *tail)
{
	//int i = 0;
	printf("Max proof of %s\n", _th_print_exp(e));
    if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_RAT_TIMES || e->u.appl.functor==INTERN_RAT_PLUS)) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
			if (e->u.appl.args[i]==EXP_RATIONAL) {
				if (!_th_big_is_negative(e->u.appl.args[i]->u.rational.numerator)) {
					if (e->u.appl.functor==INTERN_RAT_TIMES && e->u.appl.count==2) {
						if (i==0) {
							if (!appears_in_map(e->u.appl.args[1],Z)) {
								fprintf(stderr, "Illegal positive coefficient in %s\n", _th_print_exp(e));
								exit(1);
							}
						} else {
							if (!appears_in_map(e->u.appl.args[0],Z)) {
								fprintf(stderr, "Illegal positive coefficient in %s\n", _th_print_exp(e));
								exit(1);
							}
						}
					}
				}
			} else {
				tail = max_proof(env,Z,W,e->u.appl.args[i],tail);
			}
        }
    }
    if (e->type != EXP_RATIONAL) {
        struct _ex_intern *f = sub_var_map(env,W,e);
        if (e != f) {
            return add_sl_exp(tail,f);
        } else if (appears_in_map(e,Z)) {
            return zero_proof(env,Z,W,e,tail);
        } else {
            fprintf(stderr, "Cannot construct proof in max_proof\n");
            exit(1);
        }
    }
    fprintf(stderr, "Error in maxproof %s\n", _th_print_exp(e));
	printf("Z:\n");
	print_var_map(Z);
	printf("W:\n");
	print_var_map(W);
	//i = 1 / i;
    //exit(1);
    return tail;
}

static struct add_list *ineqproof(struct simplex *simplex, struct _ex_intern *var, struct _ex_intern *e, struct add_list *tail)
{
    tail = add_sl_exp(tail,sub_var_map(simplex->env,simplex->W,var));

    return max_proof(simplex->env,simplex->Z,simplex->W,_th_int_rewrite(simplex->env,e,0),tail);
}

static struct add_list *diseqproof(struct simplex *simplex, struct _ex_intern *e, struct add_list *tail)
{
    tail = add_sl(tail,_ex_intern_appl1_env(simplex->env,INTERN_NOT,_ex_intern_equal(simplex->env,_ex_real,e,_ex_intern_small_rational(0,1))));

    e= sub_var_map(simplex->env,simplex->R,e);
    e= sub_var_map(simplex->env,simplex->T,e);
    e= sub_var_map(simplex->env,simplex->Z,e);

    return max_proof(simplex->env,simplex->Z,simplex->W,_th_int_rewrite(simplex->env,e,0),tail);
}

static struct add_list *eqproof(struct simplex *simplex, struct _ex_intern *v, struct _ex_intern *e, struct add_list *tail)
{
    tail = add_sl_exp(tail,sub_var_map(simplex->env,simplex->W,v));

    return max_proof(simplex->env,simplex->Z,simplex->W,_th_int_rewrite(simplex->env,e,0),tail);
}

static struct _ex_intern *orig;

static void add_expl_mapping(struct simplex *simplex, struct _ex_intern *e)
{
    struct var_map *vm = (struct var_map *)_th_alloc(_th_get_space(simplex->env),sizeof(struct var_map));

    vm->next = simplex->mapping;
    simplex->mapping = vm;
    vm->e = orig;
    vm->var = e;
}

static struct add_list *addeq(struct simplex *simplex, struct _ex_intern *e)
{
    struct _ex_intern *var = get_zvar(simplex->env,_ex_real);
    struct add_list *vl;
    struct _ex_intern *v;
    add_expl_mapping(simplex,var);

    //struct var_map *n = (struct var_map *)_th_alloc(_th_get_space(simplex->env),sizeof(struct var_map));

    //n->next = simplex->W;
    //simplex->W = n;

    //n->var = var;
    //n->e = e;

    while (1) {
        struct _ex_intern *m = maximized(simplex->env,e,simplex->Z);
        if (m != NULL && _th_big_is_negative(m->u.rational.numerator)) {
            return eqproof(simplex,v,e,NULL);
        }
        if (is_zero_term(simplex->env,e,simplex->Z)) return NULL;
        m = abs_e(e);
        if (_th_big_is_negative(m->u.rational.numerator)) {
            vl = get_non_slack_positives(simplex->env,e,simplex->Z,NULL);
            while (vl) {
                struct _ex_intern *g, *cg;
                v = vl->e;
                g = G(simplex->env,simplex->T,simplex->Z,v);
                cg = _th_divide_rationals(m,find_coef(simplex->env,e,v));
                cg = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(cg->u.rational.numerator)),cg->u.rational.denominator);
                if (_th_rational_less(cg,g)) {
                    struct _ex_intern *eprime = solve(simplex->env,v,var,e);
                    simplex->T = add_mapping(simplex->env,simplex->T,v,eprime);
                    return NULL;
                } else if (cg==g) {
                    struct _ex_intern *eprime = solve(simplex->env,v,var,e);
                    inc_zeros(simplex,v,eprime);
                    return NULL;
                }
                vl = vl->next;
            }
        }
        vl = get_non_slack_all(simplex->env,e,simplex->Z);
        if (m->u.rational.numerator[0]==1 && m->u.rational.numerator[1]==0) {
            struct _ex_intern *eprime;
            printf("vl->e = %s\n", _th_print_exp(vl->e));
            eprime = solve(simplex->env,vl->e,var,e);
            v = vl->e;
            inc_zeros(simplex,v,eprime);
            return NULL;
        }
        while (vl) {
            if (unbound(simplex->env,simplex->T,vl->e)) break;
            vl = vl->next;
        }
        if (vl==NULL && _th_big_is_negative(m->u.rational.numerator)) {
            struct _ex_intern *v = get_bland_var(simplex->env,simplex->T,e);
            struct _ex_intern *u;
            if (v) {
                u = get_pivotable(simplex->env,simplex->T,NULL,v);
                simplex->T = pivot(simplex->env,simplex->T,u,v);
                e = _th_nc_rewrite(simplex->env,sub_var_map(simplex->env,simplex->T,e));
            } else {
                printf("Nothing done 1\n");
                //exit(1);
                return NULL;
            }
        } else {
            printf("Nothing done 2\n");
            //exit(1);
            return NULL;
        }
    }

}

static struct add_list *addineq(struct simplex *simplex, struct _ex_intern *var, struct _ex_intern *e)
{
    struct add_list *vl;
    //struct _ex_intern *v;
    //struct var_map *n = (struct var_map *)_th_alloc(_th_get_space(simplex->env),sizeof(struct var_map));

    //n->next = simplex->W;
    //simplex->W = n;

    //n->var = var;
    //n->e = e;

    printf("addineq %s ", _th_print_exp(e));
	printf(" (%s)\n", _th_print_exp(var));

    while (1) {
        struct _ex_intern *m = maximized(simplex->env,e,simplex->Z);
        struct _ex_intern *min, *abse;
        printf("Cycle\n");
        printf("m = %s\n", _th_print_exp(m));
        if (m != NULL && _th_big_is_negative(m->u.rational.numerator)) {
            return ineqproof(simplex,var,e,NULL);
        }
        min = minimized(simplex->env,e,simplex->Z);
        printf("min = %s\n", _th_print_exp(min));
        if (min != NULL && !_th_big_is_negative(min->u.rational.numerator)) {
            return NULL;
        }
        if (min==NULL &&
            m != NULL && m->u.rational.numerator[0]==1 && m->u.rational.numerator[1]==0) {
            inc_zeros(simplex,var,e);
            return NULL;
        }
        abse = abs_e(e);
        printf("abse = %s\n", _th_print_exp(abse));
        if (min==NULL && !_th_big_is_negative(abse->u.rational.numerator) && (abse->u.rational.numerator[0]!=1 || abse->u.rational.numerator[1]!=0)) {
            struct var_map ue;
            ue.next = NULL;
            ue.e = e;
            ue.var = var;
            simplex->T = compose(simplex->env,simplex->T,copy_var_map(_th_get_space(simplex->env),&ue));
            return NULL;
        }
        printf("Here1\n");
        if (min==NULL && !_th_big_is_negative(abse->u.rational.numerator) &&
            (abse->u.rational.numerator[0] != 1 || abse->u.rational.numerator[1] != 0) && 
            unbound2_exp(simplex->env,simplex->T,simplex->Z,e)) {
            struct var_map ue;
            printf("Adding to t %s =", _th_print_exp(e));
            printf(" %s\n", _th_print_exp(var));
            ue.next = NULL;
            ue.e = e;
            ue.var = var;
            simplex->T = compose(simplex->env,simplex->T,copy_var_map(_th_get_space(simplex->env),&ue));
            return NULL;
        }
        printf("Here2\n");
        if (min==NULL || _th_big_is_negative(abse->u.rational.numerator) &&
            unbound2_exp(simplex->env,simplex->T,simplex->Z,e)) {
            printf("Here unbound\n");
            vl = get_non_slack_positives(simplex->env,e,simplex->T,simplex->Z);
            while (vl) {
                if (unbound(simplex->env,simplex->T,vl->e) && unbound(simplex->env,simplex->Z,vl->e)) {
                    struct _ex_intern *eprime = solve(simplex->env,vl->e,var,e);
                    printf("Adding mapping %s =>", _th_print_exp(var));
                    printf(" %s\n", _th_print_exp(eprime));
                    simplex->T = add_mapping(simplex->env,simplex->T,vl->e,eprime);
                    return NULL;
                }
                vl = vl->next;
            }
        }
        printf("Here3\n");
        if (_th_big_is_negative(abse->u.rational.numerator) || (abse->u.rational.numerator[0]==1 && abse->u.rational.numerator[1]==0)) {
            struct _ex_intern *v = get_bland_var(simplex->env,simplex->T,e);
            struct _ex_intern *u;
            if (v) {
                u = get_pivotable(simplex->env,simplex->T,NULL,v);
                printf("Pivoting on %s and", _th_print_exp(u));
                printf(" %s\n", _th_print_exp(v));
                simplex->T = pivot(simplex->env,simplex->T,u,v);
                e = _th_nc_rewrite(simplex->env,sub_var_map(simplex->env,simplex->T,e));
            } else {
                _th_print_simplex(simplex);
                printf("Nothing done 3\n");
                //exit(1);
                return NULL;
            }
        } else {
            _th_print_simplex(simplex);
            printf("Nothing done 4\n");
            //exit(1);
            return NULL;
        }
    }

}

static struct add_list *add_eq_t(struct simplex *simplex, struct _ex_intern *e)
{
    printf("add_eq_t\n");

    if (is_negative(simplex,e)) {
        e = _ex_intern_appl2_env(simplex->env,INTERN_RAT_TIMES,_ex_intern_small_rational(-1,1),e);
        e = _th_rewrite(simplex->env,e);
    }
    return addeq(simplex,e);
}

static struct add_list *check_inequalities(struct simplex *simplex)
{
    struct add_list *d = simplex->D;

    while(d) {
        struct _ex_intern *e = d->e;
        e = sub_var_map(simplex->env,simplex->R,e);
        e = _th_nc_rewrite(simplex->env,e);
        printf("Checking %s\n", _th_print_exp(e));
        if (is_zero_term(simplex->env,e,simplex->Z)) {
            printf("*** check_inequalities failure %s\n", _th_print_exp(e));
            return diseqproof(simplex,d->e,NULL);
        }
        printf("Pass\n");
        d = d->next;
    }

    return NULL;
}

static struct add_list *add_eq(struct simplex *simplex, struct _ex_intern *e)
{
    struct _ex_intern *v;
    struct add_list *res;

    printf("add_eq %s\n", _th_print_exp(e));

    e = sub_var_map(simplex->env,simplex->R,e);
    printf("sub %s\n", _th_print_exp(e));
    if (is_zero_term(simplex->env,e,simplex->Z)) return NULL;
    e = _th_nc_rewrite(simplex->env,e);

    v = get_non_slack(e,NULL);

    if (v) {
        e = solve(simplex->env,v,_ex_intern_small_rational(0,1),e);
        add_eq_r(simplex,v,e);
        return check_inequalities(simplex);
    } else {
        res = add_eq_t(simplex,e);
        if (res==NULL) {
            return check_inequalities(simplex);
        } else {
            return res;
        }
    }
}

static struct add_list *add_neq(struct simplex *simplex, struct _ex_intern *e)
{
    struct add_list *d = (struct add_list *)_th_alloc(_th_get_space(simplex->env),sizeof(struct add_list));
    d->next = simplex->D;
    simplex->D = d;
    d->e = e;

    add_expl_mapping(simplex,e);

    return check_inequalities(simplex);
}

static struct add_list *add_ineq(struct simplex *simplex, struct _ex_intern *e)
{
    struct _ex_intern *v;
    printf("add_ineq %s\n", _th_print_exp(e));
    e = sub_var_map(simplex->env,simplex->R,e);
    //e = sub_var_map(simplex->env,simplex->T,e);
    //e = sub_var_map(simplex->env,simplex->Z,e);
    e = _th_nc_rewrite(simplex->env,e);
    printf("add_ineq simp %s\n", _th_print_exp(e));
    v = get_non_slack(e,NULL);
    printf("v = %s\n", _th_print_exp(v));

    fflush(stdout);

    if (v) {
        struct _ex_intern *w = get_var(simplex->env,_ex_real);
        struct var_map *vm = (struct var_map *)_th_alloc(_th_get_space(simplex->env),sizeof(struct var_map));
        struct _ex_intern *eprime = solve(simplex->env,v,w,e);
        add_expl_mapping(simplex,w);
        printf("AddineqR\n");
        printf("v = %s\n", _th_print_exp(v));
        printf("w = %s\n", _th_print_exp(w));
        printf("e = %s\n", _th_print_exp(e));
        printf("eprime = %s\n", _th_print_exp(eprime));
        fflush(stdout);
        simplex->R = add_mapping(simplex->env,simplex->R,v,eprime);
        simplex->W = add_mapping(simplex->env,simplex->W,w,e);
        fflush(stdout);
        return check_inequalities(simplex);
    } else {
        struct add_list *res;
        struct _ex_intern *w = get_var(simplex->env,_ex_real);
        struct var_map *vm = (struct var_map *)_th_alloc(_th_get_space(simplex->env),sizeof(struct var_map));
        add_expl_mapping(simplex,w);
        printf("AddineqT\n");
        vm->next = simplex->W;
        vm->e = e;
        vm->var = w;
        simplex->W = vm;
        res = addineq(simplex,w,e);
        fflush(stdout);
        simplex->R = fusion2(simplex->env,simplex->R,simplex->T,simplex->Z);
        if (res==NULL) {
            return check_inequalities(simplex);
        } else {
            return res;
        }
    }
}

struct add_list *map_expl(struct simplex *simplex, struct add_list *expl)
{
    struct add_list *l = expl;

    while (l) {
        struct var_map *vm = simplex->mapping;

        while (vm) {
            if (l->e==vm->var) {
                l->e = vm->e;
                break;
            }
            vm = vm->next;
        }
        l = l->next;
    }

    return expl;
}

static struct var_map *add_zero_map(struct var_map *m, struct _ex_intern *var)
{
    struct var_map *n;

    n = m;
    while (n) {
        if (n->var==var) return m;
        n = n->next;
    }

    n = (struct var_map *)_th_alloc(REWRITE_SPACE,sizeof(struct var_map));
    n->next = m;
    n->var = var;
    n->e = _ex_intern_small_rational(0,1);

    return n;
}

static struct var_map *collect_all_vars(struct env *env, struct _ex_intern *e, struct var_map *map)
{
    if (e->type != EXP_APPL) {
        if (e->type != EXP_RATIONAL) {
            return add_zero_map(map,e);
        } else {
            return map;
        }
    }

    if (e->u.appl.functor==INTERN_RAT_TIMES) {
        struct _ex_intern *core = strip_r_coef(env,e);
        return add_zero_map(map,core);
    } else if (e->u.appl.functor==INTERN_RAT_PLUS) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            struct _ex_intern *core = strip_r_coef(env,e->u.appl.args[i]);
            map = add_zero_map(map,core);
        }
        return 0;
    } else {
        map = add_zero_map(map,e);
    }
}

static struct var_map *collect_zero_vars(struct env *env, struct _ex_intern *e, struct var_map *map)
{
    if (e->type != EXP_APPL) {
        if (e->type != EXP_RATIONAL) {
            if (is_zero(e,NULL)) {
                return add_zero_map(map,e);
            } else {
                return map;
            }
        } else {
            return map;
        }
    }

    if (e->u.appl.functor==INTERN_RAT_TIMES) {
        struct _ex_intern *core = strip_r_coef(env,e);
        if (is_zero(core,NULL)) {
            return add_zero_map(map,core);
        } else {
            return map;
        }
    } else if (e->u.appl.functor==INTERN_RAT_PLUS) {
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            struct _ex_intern *core = strip_r_coef(env,e->u.appl.args[i]);
            if (is_zero(core,NULL)) {
                map = add_zero_map(map,core);
            } else {
                return map;
            }
        }
        return 0;
    } else {
        if (is_zero(e,NULL)) {
            map = add_zero_map(map,e);
        } else {
            return NULL;
        }
    }
}

static int is_bigger(struct var_map *map, struct _ex_intern *l, struct _ex_intern *r)
{
    while (map) {
        if (map->var==l && map->e==r) return 1;
        map = map->next;
    }

    return 0;
}

static struct var_map *build_simplex_mdl(struct env *env, struct var_map *R, struct var_map *T,
                                         struct add_list *D, struct add_list *Y, struct var_map *cmp,
                                         struct var_map *model)
{
    struct add_list *v = Y, *Dp;
    struct var_map *m, *Rp, *Tp;

    while (v) {
        if (is_slack(v->e)) {
            struct add_list *t = Y;
            while (t) {
                if (is_slack(t->e) && is_bigger(cmp,t->e,v->e)) {
                    goto cont1;
                }
                t = t->next;
            }
            goto cont;
        }
cont1:
        v = v->next;
    }
cont:
    if (v) {
        struct _ex_intern *g = G(env,T,NULL,v->e);
        struct _ex_intern *val = _ex_intern_small_rational(1,1);
        struct add_list *Ym;
        m = (struct var_map *)_th_alloc(REWRITE_SPACE,sizeof(struct var_map));
        m->next = model;
        model = m;
        while (_th_rational_less(val,g)) {
            struct var_map *res;
            struct add_list *p, *n, *t;
            m->var = v->e;
            m->e = val;
            Dp = NULL;
            t = D;
            while (res) {
                struct _ex_intern *e = sub_var_map(env,m,t->e);
                if (e==_ex_intern_small_rational(0,1)) goto cont2;
                n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                n->next = Dp;
                Dp = n;
                n->e = e;
                t = t->next;
            }
            p = NULL;
            t = Y;
            while (t != v) {
                n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                n->next = NULL;
                n->e = t->e;
                if (p) {
                    p->next = n;
                } else {
                    Ym = n;
                }
                p = n;
                t = t->next;
            }
            if (p) {
                p->next = v->next;
            } else {
                Ym = v->next;
            }
            if (Ym==NULL) {
                return model;
            } else {
                Tp = fusion(env,T,m);
                Rp = fusion(env,R,m);
                res = build_simplex_mdl(env,Rp,Tp,Dp,Ym,cmp,model);
                if (res) return res;
            }
cont2:
            val = _th_add_rationals(val,_ex_intern_small_rational(1,1));
        }
    }
}

static struct var_map *build_simplex_model(struct simplex *simplex)
{
    struct var_map *Tp, *Zp, *Rpp, *Tpp, *cmp;
    struct var_map *model, *m, *n;
    struct add_list *Y, *a, *an, *Dpp;

    Tp = FindZeros(simplex->env,simplex->T,simplex->Z);
    Zp = ret_z;

    m = Zp;
    model = NULL;
    while (m) {
        model = collect_all_vars(simplex->env,m->e,model);
        model = add_zero_map(model,m->var);
        m = m->next;
    }
    m = Tp;
    while (m) {
        model = collect_zero_vars(simplex->env,m->e,model);
        m = m->next;
    }

    m = Tp;
    Tpp = NULL;
    while (m) {
        n = (struct var_map *)ALLOCA(sizeof(struct var_map));
        n->next = Tpp;
        Tpp = n;
        n->var = m->var;
        n->e = _th_nc_rewrite(simplex->env,sub_var_map(simplex->env,model,m->e));
        m = m->next;
    }

    m = simplex->R;
    Rpp = NULL;
    while (m) {
        n = (struct var_map *)ALLOCA(sizeof(struct var_map));
        n->next = Rpp;
        Rpp = n;
        n->var = m->var;
        n->e = _th_nc_rewrite(simplex->env,sub_var_map(simplex->env,model,m->e));
        m = m->next;
    }

    a = simplex->D;
    Dpp = NULL;
    while (a) {
        an = (struct add_list *)ALLOCA(sizeof(struct add_list));
        an->next = Dpp;
        Dpp = an;
        an->e = _th_nc_rewrite(simplex->env,sub_var_map(simplex->env,Rpp,sub_var_map(simplex->env,Tpp,m->e)));
        a = a->next;
    }

    Y = NULL;

    a = Dpp;
    while (a) {
        Y = add_sl_exp(Y,a->e);
        a = a->next;
    }
    m = Rpp;
    while (m) {
        Y = add_sl_exp(Y,m->e);
        m = m->next;
    }
    m = Tpp;
    while (m) {
        Y = add_sl_exp(Y,m->e);
        m = m->next;
    }

    return build_simplex_mdl(simplex->env,Rpp,Tpp,Dpp,Y,cmp,model);
}

struct add_list *_th_add_equation(struct simplex *simplex, struct _ex_intern *e)
{
    struct env *env = simplex->env;
    struct _ex_intern *orig;

    if (e->type != EXP_VAR &&
		(e->type != EXP_APPL || e->u.appl.functor != INTERN_NOT && e->u.appl.args[0]->type != EXP_VAR)) {
			printf("*** SIMPLEX ADD %x %s ***\n", simplex, _th_print_exp(e));
	}
    _th_print_simplex(simplex);

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL &&
        get_type(env,e->u.appl.args[0])==_ex_real) {
        e = _th_nc_rewrite(env,_ex_intern_appl2_env(env,INTERN_RAT_MINUS,e->u.appl.args[0],e->u.appl.args[1]));
        return add_eq(simplex,e);
    }

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        e = e->u.appl.args[0];
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL) {
            e = _th_nc_rewrite(env,_ex_intern_appl2_env(env,INTERN_RAT_MINUS,e->u.appl.args[0],e->u.appl.args[1]));
            return map_expl(simplex,add_neq(simplex,e));
        }
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_LESS) {
            e = _th_nc_rewrite(env,_ex_intern_appl2_env(env,INTERN_RAT_MINUS,e->u.appl.args[0],e->u.appl.args[1]));
            return map_expl(simplex,add_ineq(simplex,e));
        }
        return NULL;
    }
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_LESS) {
        struct add_list *res;
        e = _th_nc_rewrite(env,_ex_intern_appl2_env(env,INTERN_RAT_MINUS,e->u.appl.args[1],e->u.appl.args[0]));
        res = map_expl(simplex,add_ineq(simplex,e));
        if (res) return res;
        return map_expl(simplex,add_neq(simplex,e));
    }
    return NULL;
}

void _th_simplex_push(struct simplex *simplex)
{
    struct simplex *s = (struct simplex *)_th_alloc(_th_get_space(simplex->env),sizeof(struct simplex));

    printf("*** SIMPLEX PUSH %x ***\n", simplex);
    _th_print_simplex(simplex);

    s->push = simplex->push;
    s->env = simplex->env;
    s->D = simplex->D;
    s->R = simplex->R;
    s->T = simplex->T;
    s->W = simplex->W;
    s->Z = simplex->Z;
    s->mapping = simplex->mapping;
    simplex->push = s;
}

void _th_simplex_pop(struct simplex *simplex)
{
    printf("*** SIMPLEX POP %x ***\n", simplex);
    _th_print_simplex(simplex);

    if (simplex->push==NULL) return;
    simplex->D = simplex->push->D;
    simplex->R = simplex->push->R;
    simplex->T = simplex->push->T;
    simplex->W = simplex->push->W;
    simplex->Z = simplex->push->Z;
    simplex->mapping = simplex->push->mapping;
    simplex->push = simplex->push->push;
}
