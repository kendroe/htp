/*#define DEBUG*/
/*
 * match.c
 *
 * Pattern matching routines
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"
#define MAX_UNIFIER_DEPTH 30

static int level ;
static int symbol_stack[MAX_UNIFIER_DEPTH] ;
static int position_stack[MAX_UNIFIER_DEPTH] ;
static struct _ex_unifier *unifier ;

static struct _ex_unifier *cu(struct _ex_intern *var, struct _ex_intern *e)
{
    int i ;

    /**********/

    switch (var->type) {

        case EXP_APPL:
            if (level >= MAX_UNIFIER_DEPTH-1) {
                printf("case pattern too deep\n") ;
                exit(1) ;
            }
            symbol_stack[level] = var->u.appl.functor ;
            ++level ;
            for (i = 0; i < var->u.appl.count; ++i) {
                position_stack[level-1] = i ;
                cu(var->u.appl.args[i],e) ;
            }
            --level ;
            break ;

        case EXP_VAR:
            for (i = level-1; i!=0xffffffff; --i) {
                e = _ex_intern_index(e,symbol_stack[i],position_stack[i]) ;
            }
            unifier = _th_add_pair(MATCH_SPACE,unifier,var->u.var,e) ;
            break ;

        default:
            printf("Illegal case matcher\n") ;
            exit(1) ;
    }
    return unifier ;
}

static struct _ex_unifier *create_unifier(struct _ex_intern *var, struct _ex_intern *e)
{
    level = 0 ;
    unifier = _th_new_unifier(MATCH_SPACE) ;

    return cu(var,e) ;
}

static struct _ex_intern *reduce_term(struct _ex_intern *term)
{
    int i ;
    struct _ex_intern *t ;

    while(1) {
        if (term->type == EXP_INDEX && term->u.index.exp->type == EXP_APPL &&
            term->u.index.functor == term->u.index.exp->u.appl.functor) {
            term = term->u.index.exp->u.appl.args[term->u.index.term] ;
        } else if (term->type == EXP_APPL && term->u.appl.count > 0 &&
                   term->u.appl.args[0]->type == EXP_INDEX &&
                   term->u.appl.args[0]->u.index.term==0) {
            t = term->u.appl.args[0]->u.index.exp ;
            for (i = 1; i < term->u.appl.count; ++i) {
                if (term->u.appl.args[i]->type != EXP_INDEX ||
                    term->u.appl.args[i]->u.index.functor != term->u.appl.functor ||
                    term->u.appl.args[i]->u.index.exp != t ||
                    term->u.appl.args[i]->u.index.term != i) {
                    return term ;
                }
            }
            return t ;
        } else {
            return term ;
        }
    }
}

#define MAX_QUANT_DEPTH 32
#define MAX_BACKUP 200
/* For testing purposes only */
#define BIT_MAX 2

static unsigned *quant_stack1[MAX_QUANT_DEPTH] ;
static unsigned *quant_stack2[MAX_QUANT_DEPTH] ;
static unsigned *quant_assigned[MAX_BACKUP][MAX_QUANT_DEPTH] ;
static int quant_count[MAX_QUANT_DEPTH] ;
static int quant_level ;
static int quant_save_count ;
static int quant_backup ;
static int quant_stop ;

static void push_assignment()
{
    int i, j ;

    ++quant_save_count ;

    if (quant_save_count % BIT_MAX == 0) {
        ++quant_backup ;
        if (quant_backup >= MAX_BACKUP) {
            printf("Too many nested quantifiers 1\n") ;
            i = 0 ;
            i = 1 / i ;
            exit(1) ;
        }
        for (i = quant_level-1; i != 0xffffffff; --i) {
            quant_assigned[quant_backup][i] = (unsigned *)_th_alloc(MATCH_SPACE,sizeof(unsigned) * quant_count[i]) ;
            for (j = 0; j < quant_count[i]; ++j) {
                quant_assigned[quant_backup][i][j] = quant_assigned[quant_backup-1][i][j]&1 ;
            }
        }
    } else {
        for (i = quant_level-1; i != 0xffffffff; --i) {
            for (j = 0; j < quant_count[i]; ++j) {
                quant_assigned[quant_backup][i][j] = (quant_assigned[quant_backup][i][j]<<1)+(quant_assigned[quant_backup][i][j]&1) ;
            }
        }
    }
}

static void pop_assignment()
{
    int i, j ;

    if (quant_save_count%BIT_MAX==0) {
        --quant_backup ;
    } else {
        for (i = quant_level-1; i != 0xffffffff; --i) {
            for (j = 0; j < quant_count[i]; ++j) {
                quant_assigned[quant_backup][i][j] = (quant_assigned[quant_backup][i][j]>>1) ;
            }
        }
    }
    --quant_save_count ;
}

static void pop_accept_assignment()
{
    int i, j ;

    if (quant_save_count%BIT_MAX==0) {
        --quant_backup ;
        for (i = quant_level-1; i != 0xffffffff; --i) {
            for (j = 0; j < quant_count[i]; ++j) {
                quant_assigned[quant_backup][i][j] =
                    (quant_assigned[quant_backup][i][j] |
                     (quant_assigned[quant_backup+1][i][j] & 1)) ;
            }
        }
    } else {
        for (i = quant_level-1; i != 0xffffffff; --i) {
            for (j = 0; j < quant_count[i]; ++j) {
                quant_assigned[quant_backup][i][j] =
                    ((quant_assigned[quant_backup][i][j]>>1) | (quant_assigned[quant_backup][i][j] & 1)) ;
            }
        }
    }
    --quant_save_count ;
}

static void get_depth1(unsigned var, int *d1, int *p1)
{
    int i ;
    int j ;
    
    for (i = quant_level-1; i >= (int)quant_stop; --i) {
        for (j = 0; j < quant_count[i]; ++j) {
            if (var == quant_stack1[i][j]) {
                *d1 = i ;
                *p1 = j ;
                return ;
            }
        }
    }
    
    *d1 = -1 ;
}

static void get_depth2(unsigned var, int *d2, int *p2)
{
    int i ;
    int j ;
    
    for (i = quant_level-1; i >= (int)quant_stop; --i) {
        for (j = 0; j < quant_count[i]; ++j) {
            if (var == quant_stack2[i][j]) {
                *d2 = i ;
                *p2 = j ;
                return ;
            }
        }
    }
    
    *d2 = -1 ;
}

static struct _ex_unifier *generate_map()
{
    struct _ex_unifier *u = _th_new_unifier(MATCH_SPACE) ;
    int i, j ;

    for (i = 0; i < quant_level; ++i) {
        for (j = 0; j < quant_count[i]; ++j) {
            u = _th_add_pair(MATCH_SPACE, u, quant_stack2[i][j], _ex_intern_var(quant_stack1[i][j])) ;
        }
    }

    return u ;
}

static struct _ex_unifier *map_patterns(struct _ex_unifier *u,
                                        struct _ex_intern *e1,
                                        struct _ex_intern *e2)
{
    int i ;

#ifdef DEBUG
    printf("Map patterns\n") ;
    printf("e1: %s\n", _th_print_exp(e1)) ;
    printf("e2: %s\n", _th_print_exp(e2)) ;
#endif

    if (e1->type == EXP_VAR && e2->type == EXP_VAR) {
        return _th_add_pair(MATCH_SPACE,u,e2->u.var,e1) ;
    } else if (e1->type == EXP_APPL && e2->type == EXP_APPL &&
               e1->u.appl.count == e2->u.appl.count &&
               e1->u.appl.functor == e2->u.appl.functor) {
        for (i = 0; i < e1->u.appl.count; ++i) {
            u = map_patterns(u,e1->u.appl.args[i],e2->u.appl.args[i]) ;
            if (u==NULL) return NULL ;
        }
        return u ;
    } else return NULL ;
}

static unsigned arg_start, arg_size ;
static struct _ex_intern **args, **all_args, **args2, **all_args2 ;
static int *match_used, *all_match_used, *match_value, *all_match_value ;
static int *matched_var, *all_matched_var ;
struct match_return **int_res, **all_int_res ;

#define ARG_INCREMENT 4000

static void set_start(unsigned x)
{
    arg_start += x ;
    args = all_args + arg_start ;
    args2 = all_args2 + arg_start ;
    match_used = all_match_used + arg_start ;
    match_value = all_match_value + arg_start ;
    matched_var = all_matched_var + arg_start ;
    int_res = all_int_res + arg_start ;
}

static void check_size(unsigned size)
{
    if (arg_start + size > arg_size) {
        arg_size = arg_start + size + ARG_INCREMENT ;
        all_args = (struct _ex_intern **)REALLOC(all_args,sizeof(struct _ex_intern *) * arg_size) ;
        all_args2 = (struct _ex_intern **)REALLOC(all_args2,sizeof(struct _ex_intern *) * arg_size) ;
        all_match_used = (int *)REALLOC(all_match_used,sizeof(int) * arg_size) ;
        all_match_value = (int *)REALLOC(all_match_value,sizeof(int) * arg_size) ;
        all_matched_var = (int *)REALLOC(all_matched_var,sizeof(int) * arg_size) ;
        all_int_res = (struct match_return **)REALLOC(all_int_res,sizeof(struct match_return *) * arg_size) ;
        set_start(0) ;
    }
}

static int _equal(struct env *env,struct _ex_intern *e1, struct _ex_intern *e2)
{
    int d1, d2, p1, p2 ;
    int v ;
    int i, j, k, count ;
    unsigned *fv ;
    struct _ex_unifier *u ;

    /**********/

    if (e1->has_special_term || e2->has_special_term || quant_level != quant_stop) {
        /*if (e2->type == EXP_CASE) {
            for (i = 0; i < e2->u.case.count; i += 2) {
                u = create_unifier(e2->u.case_stmt.args[i],
                                   e2->u.case_stmt.exp) ;
                e = _th_subst(env,u,e2->u.case_stmt.args[i+1]) ;
                if (!_equal(env,e2,e)) goto cont ;
            }
            return 1 ;
        }*/

        if (e1->type != e2->type) return 0 ;

        switch (e1->type) {

            case EXP_VAR:
#ifdef DEBUG
                printf("Comparing vars %s %s\n", _th_intern_decode(e1->u.var),
                       _th_intern_decode(e2->u.var)) ;
#endif
                get_depth1(e1->u.var, &d1, &p1) ;
                get_depth2(e2->u.var, &d2, &p2) ;
#ifdef DEBUG
                printf("comparing %d %d %d %d\n", d1, p1, d2, p2) ;
#endif
                if (d1 != d2) return 0 ;
                if (d1 == -1) return e1->u.var == e2->u.var ;
                if (quant_assigned[quant_backup][d1][p1] || quant_assigned[quant_backup][d2][p2]) return p1==p2 ;
                v = quant_stack2[d2][p2] ;
                quant_stack2[d2][p2] = quant_stack2[d2][p1] ;
                quant_stack2[d2][p1] = v ;
                quant_assigned[quant_backup][d1][p1] = 1 ;
                return 1 ;

            case EXP_MARKED_VAR:
                return e1->u.marked_var.var==e2->u.marked_var.var &&
                       e1->u.marked_var.quant_level==e2->u.marked_var.quant_level ;

            case EXP_CASE:
                /*for (i = 0; i < e1->u.case.count; i += 2) {
                    u = create_unifier(e1->u.case_stmt.args[i],
                                       e1->u.case_stmt.exp) ;
                    e = _th_subst(env,u,e1->u.case_stmt.args[i+1]) ;
                    if (!_equal(env,e,e2)) goto cont2 ;
                }
                return 1 ;*/
                if (e1->u.case_stmt.count != e2->u.case_stmt.count) return 0 ;
                if (!_equal(env, e1->u.case_stmt.exp, e2->u.case_stmt.exp)) return 0 ;
                check_size(e1->u.case_stmt.count*2) ;
                if (quant_level >= MAX_QUANT_DEPTH-1) {
                    printf("Too many nested quantifiers 2\n") ;
                    exit(1) ;
                }
                ++quant_level ;
                for (i = 0; i < e1->u.case_stmt.count; ++i) {
                    match_used[i] = 0 ;
                }
                for (i = 0; i < e1->u.case_stmt.count; ++i) {
                    fv = _th_get_free_vars(e1->u.case_stmt.args[i*2],&count) ;
                    quant_count[quant_level-1] = count ;
                    if (count > 0) {
                        quant_stack1[quant_level-1] = (unsigned *)_th_alloc(MATCH_SPACE,count * sizeof(unsigned)) ;
                        quant_stack2[quant_level-1] = (unsigned *)_th_alloc(MATCH_SPACE,count * sizeof(unsigned)) ;
                        quant_assigned[quant_backup][quant_level-1] = (int *)_th_alloc(MATCH_SPACE,count * sizeof(unsigned)) ;
                        for (k = 0; k < count; ++k) {
                            quant_stack1[quant_level-1][k] = fv[k] ;
                            quant_assigned[quant_backup][quant_level-1][k] = 1 ;
                        }
                    }
                    j = 0 ;
re_entryc:
                    while (j < e1->u.case_stmt.count) {
                        if (match_used[j]) {
                            ++j ;
                            continue ;
                        }
#ifdef DEBUG
                        printf("Testing %d %d\n", i, j) ;
#endif
                        if (e1->u.case_stmt.args[i*2]==e2->u.case_stmt.args[j*2]) {
                            fv = _th_get_free_vars(e2->u.case_stmt.args[j*2],&count) ;
                            if (count != quant_count[quant_level-1]) {
                                ++j ;
                                continue ;
                            }
                            for (k = 0; k < count; ++k) {
                                quant_stack2[quant_level-1][k] = fv[k] ;
                            }
                            push_assignment() ;
#ifdef DEBUG
                            printf("exp: %s\n",
                                   _th_print_exp(e1->u.case_stmt.args[i*2+1])) ;
                            printf("exp: %s\n",
                                   _th_print_exp(e2->u.case_stmt.args[j*2+1])) ;
#endif
                            set_start(e1->u.case_stmt.count*2) ;
                            if (_equal(env,e1->u.case_stmt.args[i*2+1],
                                       e2->u.case_stmt.args[j*2+1])) {
                                set_start(0-e1->u.case_stmt.count*2) ;
                                goto cont ;
                            }
                            set_start(0-e1->u.case_stmt.count*2) ;
                            pop_assignment() ;
                        } else if ((u = map_patterns(_th_new_unifier(MATCH_SPACE),
                                                    e1->u.case_stmt.args[i*2],
                                                    e2->u.case_stmt.args[j*2]))!=NULL) {
                            fv = _th_get_free_vars(e2->u.case_stmt.args[j*2],&count) ;
                            if (count != quant_count[quant_level-1]) {
                                ++j ;
                                continue ;
                            }
                            for (k = 0; k < count; ++k) {
                                quant_stack2[quant_level-1][k] = fv[k] ;
                            }
                            push_assignment() ;
#ifdef DEBUG
                            printf("exp: %s\n",
                                   _th_print_exp(e1->u.case_stmt.args[i*2+1])) ;
                            printf("exp: %s\n",
                                   _th_print_exp(e2->u.case_stmt.args[j*2+1])) ;
#endif
                            set_start(e1->u.case_stmt.count*2) ;
                            if (_equal(env,e1->u.case_stmt.args[i*2+1],e2->u.case_stmt.args[j*2+1])) {
                                set_start(0-e1->u.case_stmt.count*2) ;
                                goto cont ;
                            }
                            set_start(0-e1->u.case_stmt.count*2) ;
                            pop_assignment() ;
                        }
                        ++j ;
                    }
                    if (i > 0) {
                        --i ;
                        match_used[match_value[i]] = 0 ;
                        j = match_value[i]+1 ;
                        pop_assignment() ;
                        goto re_entryc ;
                    } else {
                        while(i > 0) {
                            pop_assignment () ;
                            --i ;
                        }
                        --quant_level ;
                        return 0 ;
                    }
cont:
                    match_used[j] = 1 ;
                    match_value[i] = j ;
                }
                --quant_level ;
                return 1 ;

            case EXP_QUANT:
                if (e1->u.quant.quant != e2->u.quant.quant) return 0 ;
                if (e1->u.quant.var_count != e2->u.quant.var_count) return 0 ;
                if (quant_level >= MAX_QUANT_DEPTH-1) {
                    printf("Too many nested quantifiers 3\n") ;
                    exit(1) ;
                }
                quant_stack1[quant_level] = (unsigned *)_th_alloc(MATCH_SPACE, e1->u.quant.var_count * sizeof(unsigned)) ;
                quant_stack2[quant_level] = (unsigned *)_th_alloc(MATCH_SPACE, e1->u.quant.var_count * sizeof(unsigned)) ;
                quant_assigned[quant_backup][quant_level] = (int *)_th_alloc(MATCH_SPACE, e1->u.quant.var_count * sizeof(unsigned)) ;
                quant_count[quant_level] = e1->u.quant.var_count ;
                for (i = 0; i < e1->u.quant.var_count; ++i) {
                    quant_stack1[quant_level][i] = e1->u.quant.vars[i] ;
                    quant_stack2[quant_level][i] = e2->u.quant.vars[i] ;
                    quant_assigned[quant_backup][quant_level][i] = 0 ;
                }
                ++quant_level ;
                i = (_equal(env,e1->u.quant.exp,e2->u.quant.exp) &&
                     _equal(env,e1->u.quant.cond,e2->u.quant.cond)) ;
                --quant_level ;
                return i ;
                break ;

            case EXP_APPL:
#ifdef DEBUG
                printf("Testing appl %d %d %s %s\n",
                       e1->u.appl.functor, e2->u.appl.functor,
                       _th_intern_decode(e1->u.appl.functor),
                       _th_intern_decode(e2->u.appl.functor)) ;
#endif
                if (e1->u.appl.functor != e2->u.appl.functor) return 0 ;
                if (e1->u.appl.count != e2->u.appl.count) return 0 ;
                if (_th_is_ac(env,e1->u.appl.functor) || _th_is_c(env,e1->u.appl.functor)) {
                    count = _th_ac_arity(env,e1->u.appl.functor) ;
                    for (i = 0; i < count; ++i) {
                        set_start(e1->u.appl.count) ;
                        if (!_equal(env,e1->u.appl.args[i],
                                    e2->u.appl.args[i])) {
                             set_start(0-e1->u.appl.count) ;
                             return 0 ;
                        }
                        set_start(0-e1->u.appl.count) ;
                    }
                    check_size(e1->u.appl.count) ;
                    for (i = count; i < e1->u.appl.count; ++i) {
                        match_used[i] = 0 ;
                    }
                    for (i = count; i < e1->u.appl.count; ++i) {
                        push_assignment() ;
                        j = count ;
re_entry:
                        while (j < e1->u.appl.count) {
                            if (match_used[j]) {
                                ++j ;
                                continue ;
                            }
                            set_start(e1->u.case_stmt.count*2) ;
                            if (_equal(env,e1->u.appl.args[i],e2->u.appl.args[j])) {
                                set_start(0-e1->u.case_stmt.count*2) ;
                                goto cont2 ;
                            }
                            set_start(0-e1->u.case_stmt.count*2) ;
                            ++j ;
                        }
                        pop_assignment() ;
                        --i ;
                        if (i != 0xffffffff) {
                            match_used[match_value[i]] = 0 ;
                            j = match_value[i]+1 ;
                            pop_assignment() ;
                            push_assignment() ;
                            goto re_entry ;
                        } else {
                            return 0 ;
                        }
cont2:
                        match_used[j] = 1 ;
                        match_value[i] = j ;
                    }
                    while(i > 0) {
                        pop_accept_assignment() ;
                        --i ;
                    }
                } else {
                    for (i = 0; i < e1->u.appl.count; ++i) {
                        if (!_equal(env,e1->u.appl.args[i],
                                    e2->u.appl.args[i])) return 0 ;
                    }
                }
                return 1 ;

            case EXP_INDEX:
                return e1->u.index.functor == e2->u.index.functor &&
                       e1->u.index.term == e2->u.index.term &&
                       _equal(env,e1->u.index.exp,e2->u.index.exp) ;

            default:
                return e1==e2 ;
        }
    } else {
        return e1==e2 ;
    }
}

int _th_equal(struct env *env, struct _ex_intern *exp1, struct _ex_intern *exp2)
{
    char *m ;
    int r ;

    if (exp1->has_special_term || exp2->has_special_term) {
        quant_level = 0 ;
        quant_backup = 0 ;
        quant_save_count = 0 ;
        quant_stop = 0 ;

        m = _th_alloc_mark(MATCH_SPACE) ;
        r = _equal(env, exp1, exp2) ;
        _th_alloc_release(MATCH_SPACE, m) ;
    } else {
        return exp1==exp2 ;
    }

    return r ;
}

static int has_bound_variables(struct _ex_intern *e)
{
    int i, j, c, res ;
    unsigned *fv ;

    if (quant_level == 0) return 0 ;
    fv = _th_get_free_vars_leave_marked(e, &c) ;

    res = 0 ;
    for (i = 0; i < quant_level; ++i) {
        for (j = 0; j < quant_count[i]; ++j) {
            if (_th_intern_get_data(quant_stack2[i][j])) {
                res = 1 ;
                goto cont ;
            }
        }
    }

cont:
    for (i = 0; i < c; ++i) {
        _th_intern_set_data(fv[i], 0) ;
    }

    return res ;
}

static struct match_return *last ;

static struct match_return *_match(struct env *env,
                                   struct _ex_intern *p, struct _ex_intern *e,
                                   struct _ex_unifier *theta) ;

static struct match_return *_m_match(struct env *env,
                                   struct _ex_intern *p, struct _ex_intern *e,
                                   struct match_return *mtheta)
{
    struct match_return *p_theta, *llast, *theta ;

    p_theta = NULL ;

    while(mtheta != NULL) {
        theta = _match(env, p, e, mtheta->theta) ;
        if (theta == NULL) {
            mtheta = mtheta->next ;
            continue ;
        }
        last->next = p_theta ;
        if (p_theta==NULL) llast = last ;
        p_theta = theta ;
        mtheta = mtheta->next ;
    }

    last = llast ;
    return p_theta ;
}

static struct match_return *_res_copy(struct match_return *r)
{
    struct match_return *n ;

    if (r==NULL) return NULL ;

    n = (struct match_return *)_th_alloc(MATCH_SPACE,sizeof(struct match_return)) ;
    n->next = _res_copy(r->next) ;
    n->theta = _th_shallow_copy_unifier(MATCH_SPACE,r->theta) ;

    return n ;
}

static int int_cmp(const int *x,const int *y)
{
    return *y-*x ;
}

static int next(elements, size)
int elements[] ;
int size ;
{
    int i, j, current, pos ;
    for (i = size-2; i >= 0; --i) {
         pos = i ;
         current = size ;
         for (j=i+1; j < size; ++j) {
             if (elements[j] < current && elements[j] > elements[i]) {
                 current = elements[j] ;
                 pos = j ;
             }
         }
         if (pos != i) {
             elements[pos] = elements[i] ;
             elements[i] = current ;
             qsort(elements+i+1,size-i-1,sizeof(int),int_cmp) ;
             return 1 ;
         }
    }
    return 0 ;
}

#ifdef DEBUG
static int space = 0 ;

static void _space()
{
    int i ;
    for (i = 0; i < space; ++i) printf(" ") ;
}
#endif

static struct match_return *_match(struct env *env,
                                   struct _ex_intern *p, struct _ex_intern *e,
                                   struct _ex_unifier *theta)
{
    int d1, p1, d2, p2 ;
    int i, j, k, l, m, n, multi_var, count ;
    struct match_return *res, *comp, *compl, *tr, *ir ;
    struct _ex_intern *t ;
    int used_vars, used_var_count, unused_vars ;
    unsigned *fv ;
    struct _ex_unifier *u ;
    int size, size1 ;
    
    /**********/
    
#ifdef DEBUG
    space += 2 ;
    _space() ;
    printf("Matching: ") ;
    printf("%s ", _th_print_exp(p)) ;
    printf("%s\n", _th_print_exp(e)) ;
#endif

    if (p->is_marked_term || p->marked_term==p) {
        if (_th_equal(env,_th_unmark_vars(env,p),e)) {
            res = (struct match_return *)_th_alloc(MATCH_SPACE,sizeof(struct match_return));
            res->theta = theta;
            res->next = NULL;
            last = res;
            return res;
        } else {
            last = NULL;
            return NULL;
        }
    }

    switch (p->type) {
        
    case EXP_VAR:
        get_depth1(p->u.var, &d1, &p1) ;
#ifdef DEBUG
        _space() ; printf("pos %d %d\n", d1, p1) ;
#endif
        if (d1 == -1) {
            struct _ex_intern *s = _th_apply(theta, p->u.var) ;
            if (s==NULL) {
                char *vv = _th_intern_decode(p->u.var) ;
#ifdef DEBUG
                _space() ; printf("NULL\n") ;
#endif
                if (vv[strlen(vv)-1] == '_') {

                    struct _ex_unifier *u = generate_map() ;

#ifdef DEBUG
                    _space() ; _th_print_unifier(u) ;
                    _space() ; printf("%d %s\n", s,_th_print_exp(s)) ;
                    _space() ; printf("%s\n", _th_print_exp(e)) ;
#endif
                    theta = _th_add_pair(MATCH_SPACE,theta,p->u.var,_th_subst(env,u,e)) ;
                } else if (has_bound_variables(e)) {
#ifdef DEBUG
                    _space() ; printf("bound vars\n") ;
                    space -= 2 ;
#endif
                    return NULL ;
                } else {
#ifdef DEBUG
                    _space() ; printf("%d %s\n", s,_th_print_exp(s)) ;
#endif
                    theta = _th_add_pair(MATCH_SPACE,theta,p->u.var,e) ;
                }
            } else {
                quant_stop = quant_level ;
                if (!_equal(env,s,e)) {
                    quant_stop = 0 ;
#ifdef DEBUG
                    space -= 2 ;
#endif
                    return NULL ;
                }
                quant_stop = 0 ;
            }
        } else if (e->type == EXP_VAR) {
            get_depth2(e->u.var, &d2, &p2) ;
#ifdef DEBUG
            _space() ; printf("pos2 %d %d\n", d2, p2) ;
#endif
            if (d1 != d2 || p1 != p2) {
#ifdef DEBUG
                space -= 2 ;
#endif
                return NULL ;
            }
        } else {
#ifdef DEBUG
            space -= 2 ;
#endif
            return NULL;
        }
        break ;
        
    case EXP_MARKED_VAR:
        if (e->type == EXP_MARKED_VAR) {
            if (p->u.marked_var.var != e->u.marked_var.var ||
                p->u.marked_var.quant_level != e->u.marked_var.quant_level) {
#ifdef DEBUG
                space -= 2 ;
#endif
                return NULL ;
            }
        } else if (e->type == EXP_VAR) {
            get_depth2(e->u.var, &d2, &p2) ;
            if (d2 != -1) {
#ifdef DEBUG
                space -= 2 ;
#endif
                return NULL ;
            }
            if (p->u.marked_var.var != e->u.var ||
                p->u.marked_var.quant_level != _th_intern_get_quant_level(e->u.var)) {
#ifdef DEBUG
                space -= 2 ;
#endif
                return NULL ;
            }
        } else {
#ifdef DEBUG
            space -= 2 ;
#endif
            return NULL ;
        }
        break ;
        
    case EXP_QUANT:
        if (p->u.quant.quant != e->u.quant.quant) {
#ifdef DEBUG
            space -= 2 ;
#endif
            return 0 ;
        }
        if (p->u.quant.var_count != e->u.quant.var_count) {
#ifdef DEBUG
            space -= 2 ;
#endif
            return 0 ;
        }
        if (quant_level >= MAX_QUANT_DEPTH-1) {
            printf("Too many nested quantifiers 4\n") ;
            exit(1) ;
        }
        comp = compl = NULL ;
        quant_stack1[quant_level] = (unsigned *)_th_alloc(MATCH_SPACE, p->u.quant.var_count * sizeof(unsigned)) ;
        quant_stack2[quant_level] = (unsigned *)_th_alloc(MATCH_SPACE, e->u.quant.var_count * sizeof(unsigned)) ;
        quant_assigned[quant_backup][quant_level] = (int *)_th_alloc(MATCH_SPACE, e->u.quant.var_count * sizeof(unsigned)) ;
        quant_count[quant_level] = e->u.quant.var_count ;
        for (i = 0; i < p->u.quant.var_count; ++i) {
            quant_stack1[quant_level][i] = p->u.quant.vars[i] ;
            quant_stack2[quant_level][i] = e->u.quant.vars[i] ;
            quant_assigned[quant_backup][quant_level][i] = i ;
        }
        ++quant_level ;
next_set:
        res = _match(env,p->u.quant.cond,e->u.quant.cond,theta) ;
        if (res != NULL) {
            res = _m_match(env,p->u.quant.exp,e->u.quant.exp,res) ;
        }
        if (res != NULL) {
            if (comp != NULL) {
                last->next = comp ;
                last = compl ;
            }
            comp = res ;
            compl = last ;
        }
        if (next(quant_assigned[quant_backup][quant_level-1], p->u.quant.var_count)) {
            for (i = 0; i < p->u.quant.var_count; ++i) {
                quant_stack2[quant_level-1][i] = e->u.quant.vars[quant_assigned[quant_backup][quant_level-1][i]] ;
            }
            goto next_set ;
        }
        --quant_level ;
#ifdef DEBUG
        space -= 2 ;
#endif
        res = comp ;
        last = compl ;
        return res ;
        break ;
        
    case EXP_APPL:
        if (e->type != EXP_APPL) {
#ifdef DEBUG
            printf("        fail1\n") ;
            space -= 2 ;
#endif
            return NULL ;
        }
        if (p->u.appl.functor==INTERN_EQUAL && e->u.appl.functor==INTERN_ORIENTED_RULE &&
            e->u.appl.args[2]==_ex_true) {
            e = _ex_intern_appl2_env(env,INTERN_EQUAL,e->u.appl.args[0],e->u.appl.args[1]);
        }
        if (e->u.appl.functor==INTERN_EQUAL && p->u.appl.functor==INTERN_ORIENTED_RULE &&
            p->u.appl.args[2]==_ex_true) {
            p = _ex_intern_appl2_env(env,INTERN_EQUAL,p->u.appl.args[0],p->u.appl.args[1]);
        }
        if (p->u.appl.functor != e->u.appl.functor) {
#ifdef DEBUG
            printf("        fail2\n") ;
            space -= 2 ;
#endif
            return NULL ;
        }
        if (_th_is_ac(env,p->u.appl.functor)) {
#ifdef DEBUG
            _space() ; printf("    AC match\n") ;
#endif
            if (p->u.appl.count > e->u.appl.count) {
#ifdef DEBUG
                space -= 2 ;
#endif
                return NULL ;
            }
            count = _th_ac_arity(env,p->u.appl.functor) ;
#ifdef DEBUG
            _space () ; printf("count = %d\n", count) ;
#endif
            res = (struct match_return *)_th_alloc(MATCH_SPACE,sizeof(struct match_return)) ;
            res->next =NULL;
            res->theta = theta;
            comp = compl = NULL ;
            for (i = 0; i < count; ++i) {
                res = _m_match(env,p->u.appl.args[i],
                    e->u.appl.args[i],res) ;
                if (res==NULL) {
#ifdef DEBUG
                    space -= 2 ;
#endif
                    return NULL ;
                }
            }
            if (p->u.appl.count==0 && e->u.appl.count==0 && count==0) {
                goto end_case ;
            }
            used_vars = 0 ;
            used_var_count = 0 ;
            unused_vars = 0 ;
            size = e->u.appl.count ;
            if (p->u.appl.count > e->u.appl.count) size = p->u.appl.count ;
            check_size(size) ;
            for (i = count; i < e->u.appl.count; ++i) {
                match_used[i] = 0 ;
            }
            for (i = count; i < p->u.appl.count; ++i) {
                if (p->u.appl.args[i]->type == EXP_VAR) {
                    get_depth1(p->u.appl.args[i]->u.var, &d1, &p1) ;
                    if (d1 == -1) {
                        if ((t = _th_apply(theta, p->u.appl.args[i]->u.var)) != NULL) {
                            matched_var[i] = 1 ;
                            if (t->type==EXP_APPL && t->u.appl.functor == p->u.appl.functor) {
                                for (j = 0; j < t->u.appl.count; ++j) {
                                    if (used_var_count >= MAX_ARGS) {
                                        printf("AC match generated too many terms\n") ;
                                        exit(1) ;
                                    }
                                    check_size(used_var_count+1);
                                    args[used_var_count++] = t->u.appl.args[j] ;
                                }
                            } else {
                                check_size(used_var_count+1);
                                args[used_var_count++] = t;
                            }
                            ++used_vars ;
                        } else {
                            matched_var[i] = 0 ;
                            ++unused_vars ;
                        }
                    } else {
                        matched_var[i] = 0 ;
                    }
                } else {
                    matched_var[i] = 0 ;
                }
            }
            size1 = size;
            if (used_var_count > size) size1 = used_var_count;
#ifdef DEBUG
            _space () ; printf("Step 1: %d\n", used_var_count) ;
#endif
            for (k = 0; k < used_var_count; ++k) {
                l = count ;
                while (l < e->u.appl.count) {
                    if (match_used[l]) {
                        ++l ;
                        continue ;
                    }
                    t = args[k] ;
                    set_start(size1) ;
                    if (_equal(env,t,e->u.appl.args[l])) {
                        set_start(0-size1) ;
                        goto cont2 ;
                    }
                    set_start(0-size1) ;
                    ++l ;
                }
#ifdef DEBUG
                _space () ; printf("Step 1 failed returning: %x %x\n", comp, compl) ;
                space -= 2 ;
#endif
                last = compl ;
                return comp ;
cont2:
                match_used[l] = 1 ;
            }
            
#ifdef DEBUG
            _space() ; printf("Step 2\n") ;
#endif
            for (i = count; i < p->u.appl.count; ++i) {
#ifdef DEBUG
                _space() ; printf("Processing %d\n", i) ;
#endif
                if (p->u.appl.args[i]->type==EXP_VAR) {
                    get_depth1(p->u.appl.args[i]->u.var, &d1, &p1) ;
                    if (d1 != -1) goto qvar ;
                } else {
qvar:
#ifdef DEBUG
                _space() ; printf("  legal arg %d\n", i) ;
#endif
                j = count ;
                int_res[i] = _res_copy(res) ;
re_entry:
                while (j < e->u.appl.count) {
#ifdef DEBUG
                    _space () ; printf("Sub processing %d %d\n", i, j) ;
#endif
                    if (match_used[j]) {
                        ++j ;
#ifdef DEBUG
                        _space() ; printf("  used\n") ;
#endif
                        continue ;
                    }
#ifdef DEBUG
                    _space() ; printf("Before match\n") ;
#endif
                    set_start(size1) ;
                    if (tr = _m_match(env,p->u.appl.args[i],e->u.appl.args[j],res)) {
                        set_start(0-size1) ;
                        res = tr ;
#ifdef DEBUG
                        _space() ; printf("  success\n") ;
#endif
                        goto cont ;
                    }
                    set_start(0-size1) ;
#ifdef DEBUG
                    _space() ; printf("  failure\n") ;
#endif
                    ++j ;
                }
fail_point1:
                while (--i != 0xffffffff) {
                    if (p->u.appl.args[i]->type != EXP_VAR) {
                        match_used[match_value[i]] = 0 ;
                        j = match_value[i]+1 ;
                        res = _res_copy(int_res[i]) ;
#ifdef DEBUG
                        _space() ; printf("Going to re_entry: %d\n", i) ;
#endif
                        goto re_entry ;
                    }
                }
                last = compl ;
#ifdef DEBUG
                _space() ; printf("returning %x\n", comp) ;
                space -= 2 ;
#endif
                return comp ;
cont:
                match_used[j] = 1 ;
                match_value[i] = j ;
                }
            }
#ifdef DEBUG
            _space() ; printf("Step 3: %d\n", unused_vars) ;
#endif
            if (unused_vars > 0) {
#ifdef DEBUG
                _space() ; printf("multivar test %d %d %d %d\n", p->u.appl.count,used_var_count,used_vars,e->u.appl.count) ;
#endif
                if (p->u.appl.count+used_var_count-used_vars<e->u.appl.count) {
                    multi_var = -1 ;
                    ir = res ;
fail_point3:
                    res = _res_copy(ir) ;
                    if (multi_var == -2) {
#ifdef DEBUG
                        _space() ; printf("going to fail_point 1\n") ;
#endif
                        goto fail_point1 ;
                    }
                    while (++multi_var < p->u.appl.count) {
                        if (p->u.appl.args[multi_var]->type==EXP_VAR &&
                            !matched_var[multi_var]) break ;
                    }
                    /*printf("multi_var = %d\n", multi_var) ;*/
                    if (multi_var == p->u.appl.count) goto fail_point1 ;
                } else {
                    multi_var = -2 ;
                    ir = NULL ;
                }
                for (m = count; m < p->u.appl.count; ++m) {
                    if (p->u.appl.args[m]->type == EXP_VAR &&
                        !matched_var[m] && m != multi_var) {
                        get_depth1(p->u.appl.args[m]->u.var, &d1, &p1) ;
                        if (d1 != -1) continue ;
                        /*printf("Processing var %d\n", m) ;*/
                        n = count ;
                        int_res[m] = _res_copy(res) ;
re_entry3:
                        while (n < e->u.appl.count) {
                            /*printf("Sub processing var %d %d\n", m,n) ;*/
                            if (match_used[n]) {
                                ++n ;
                                /*printf("  used\n") ;*/
                                continue ;
                            }
                            if (tr = _m_match(env,p->u.appl.args[m],e->u.appl.args[n],res)) {
                                res = tr ;
                                /*printf("  success\n") ;*/
                                goto cont3 ;
                            }
                            /*printf("  failure\n") ;*/
                            ++n ;
                        }
fail_point4:
                        while (m-- > 0) {
                            if (p->u.appl.args[m]->type == EXP_VAR &&
                                !matched_var[m] && m != multi_var) {
                                get_depth1(p->u.appl.args[m]->u.var, &d1, &p1) ;
                                if (d1 != -1) continue ;
                                match_used[match_value[m]] = 0 ;
                                n = match_value[m]+1 ;
                                res = _res_copy(int_res[m]) ;
                                goto re_entry3 ;
                            }
                        }
#ifdef DEBUG
                        _space() ; printf("Going to fail point 3\n") ;
#endif
                        goto fail_point3 ;
cont3:
                        match_used[n] = 1 ;
                        match_value[m] = n ;
                    }
                }
#ifdef DEBUG
                _space() ; printf("Done processing vars %d\n", multi_var) ;
#endif
                if (multi_var >= 0 && multi_var < 0x7fffffff) {
#ifdef DEBUG
                    _space() ; printf("Processing multivar\n") ;
#endif
                    p1 = used_var_count ;
                    for (d1 = count; d1 < e->u.appl.count; ++d1) {
#ifdef DEBUG
                        _space() ; printf("    %d - %d\n", d1, match_used[d1]) ;
#endif
                        if (!match_used[d1]) args[p1++] = e->u.appl.args[d1] ;
                    }
#ifdef DEBUG
                    _space() ; printf("p1, used_var_count %d %d\n", p1, used_var_count) ;
#endif
                    if (p1 <= used_var_count) {
                        goto fail_point4 ;
                    } else if (p1 == used_var_count+1) {
                        t = args[used_var_count] ;
                    } else {
                        t = _ex_intern_appl_env(env,p->u.appl.functor,p1-used_var_count,args+used_var_count) ;
                    }
                    set_start(size) ;
                    tr = _m_match(env,p->u.appl.args[multi_var],t,res) ;
                    set_start(0-size) ;
                    if (tr == NULL) {
                        goto fail_point4 ;
                    }
                    res = tr ;
                }
                }
#ifdef DEBUG
                _space() ; printf("Wrap up %x %x\n", res, comp) ;
#endif
                if (res != NULL) {
                    if (comp == NULL) {
                        compl = last ;
                    } else {
                        last->next = comp ;
                    }
                    comp = res ;
                }
                if (unused_vars > 0) {
#ifdef DEBUG
                    _space() ; printf("Going to 4\n", res, comp) ;
#endif
                    goto fail_point4 ;
                } else {
#ifdef DEBUG
                    _space() ; printf("Going to 1\n", res, comp) ;
#endif
                    goto fail_point1 ;
                }
            } else if (_th_is_c(env,p->u.appl.functor)) {
#ifdef DEBUG
                _space() ; printf("c match\n") ;
#endif
                if (p->u.appl.count != e->u.appl.count) {
#ifdef DEBUG
                    space -= 2 ;
                    printf("        fail3\n") ;
#endif
                    return NULL ;
                }
                count = _th_ac_arity(env,p->u.appl.functor) ;
                res = (struct match_return *)_th_alloc(MATCH_SPACE,sizeof(struct match_return)) ;
                res->next = NULL ;
                res->theta = theta ;
                comp = compl = NULL ;
                for (i = 0; i < count; ++i) {
                    res = _m_match(env,p->u.appl.args[i],
                        e->u.appl.args[i],res) ;
                    if (res==NULL) {
#ifdef DEBUG
                        space -= 2 ;
#endif
                        return NULL ;
                    }
                }
                if (count==0 && p->u.appl.count==0 && e->u.appl.count==0) goto end_case ;

                if (p->u.appl.count==count) {
#ifdef DEBUG
                    space -= 2 ;
#endif
                    return res ;
                }
                
                check_size(p->u.appl.count) ;
                for (i = count; i < p->u.appl.count; ++i) {
                    match_used[i] = 0 ;
                }
                for (i = count; i < p->u.appl.count; ++i) {
                    j = count ;
                    int_res[i] = _res_copy(res) ;
re_entryc:
                    while (j < p->u.appl.count) {
                        if (match_used[j]) {
                            ++j ;
                            continue ;
                        }
                        set_start(p->u.appl.count) ;
                        if (tr = _m_match(env,p->u.appl.args[i],e->u.appl.args[j],res)) {
                            set_start(0-p->u.appl.count) ;
                            res = tr ;
                            goto contc ;
                        }
                        set_start(0-p->u.appl.count) ;
                        ++j ;
                    }
                    --i ;
                    if (i != 0xffffffff) {
                        match_used[match_value[i]] = 0 ;
                        j = match_value[i]+1 ;
                        res = _res_copy(int_res[i]) ;
                        goto re_entryc ;
                    } else {
#ifdef DEBUG
                        space -= 2 ;
#endif
                        last = compl ;
                        return comp ;
                    }
contc:
                    match_used[j] = 1 ;
                    match_value[i] = j ;
                }
                if (comp == NULL) {
                    compl = last ;
                } else {
                    last->next = comp ;
                }
                comp = res ;
                match_used[j] = 0 ;
                --i ;
                ++j ;
                res = _res_copy(int_res[i]) ;
                goto re_entryc ;
            } else {
#ifdef DEBUG
                _space() ; printf("normal match\n") ;
#endif
                if (p->u.appl.count != e->u.appl.count) {
#ifdef DEBUG
                    _space() ; printf("fail4 %d %d\n", p->u.appl.count,e->u.appl.count) ;
                    space -= 2 ;
#endif
                    return NULL ;
                }
                if (p->u.appl.count > 0) {
                    set_start(p->u.appl.count) ;
                    res = _match(env,p->u.appl.args[0],e->u.appl.args[0],theta) ;
                    set_start(0-p->u.appl.count) ;
#ifdef DEBUG
                    _space() ; printf("res = %d\n", res) ;
#endif
                    for (i = 1; i < p->u.appl.count; ++i) {
                        if (res==NULL) {
#ifdef DEBUG
                            space -= 2 ;
#endif
                            return NULL ;
                        }
                        set_start(p->u.appl.count) ;
                        res = _m_match(env,p->u.appl.args[i],e->u.appl.args[i],res) ;
                        set_start(0-p->u.appl.count) ;
#ifdef DEBUG
                        _space() ; printf("res = %d\n", res) ;
#endif
                    }
#ifdef DEBUG
                    space -= 2 ;
#endif
                    return res ;
                }
            }
            break ;
            
        case EXP_INDEX:
            if (e->type != EXP_INDEX) {
#ifdef DEBUG
                space -= 2 ;
#endif
                return NULL ;
            }
            if (p->u.index.functor != e->u.index.functor ||
                p->u.index.term != e->u.index.term) {
#ifdef DEBUG
                space -= 2 ;
#endif
                return NULL ;
            }
#ifdef DEBUG
            space -= 2 ;
#endif
            return _match(env,p->u.index.exp, e->u.index.exp, theta) ;
            
        case EXP_CASE:
            if (e->type != EXP_CASE) {
#ifdef DEBUG
                space -= 2 ;
#endif
                return NULL ;
            }
            if (p->u.case_stmt.count != e->u.case_stmt.count) {
#ifdef DEBUG
                space -= 2 ;
#endif
                return NULL ;
            }
            res = _match(env, p->u.case_stmt.exp, e->u.case_stmt.exp, theta) ;
            if (res == NULL) {
#ifdef DEBUG
                space -= 2 ;
#endif
                return NULL ;
            }
            for (i = 0; i < p->u.case_stmt.count; ++i) match_used[i] = 0 ;
            if (quant_level >= MAX_QUANT_DEPTH-1) {
                printf("Too many nested quantifiers 5\n") ;
                exit(1) ;
            }
            ++quant_level ;
            check_size(p->u.case_stmt.count*2) ;
            for (i = 0; i < p->u.case_stmt.count; ++i) {
                fv = _th_get_free_vars(p->u.case_stmt.args[i*2],&count) ;
                quant_count[quant_level-1] = count ;
                if (count > 0) {
                    quant_stack1[quant_level-1] = (unsigned *)_th_alloc(MATCH_SPACE,count * sizeof(unsigned)) ;
                    quant_stack2[quant_level-1] = (unsigned *)_th_alloc(MATCH_SPACE,count * sizeof(unsigned)) ;
                    quant_assigned[quant_backup][quant_level-1] = (int *)_th_alloc(MATCH_SPACE,count * sizeof(unsigned)) ;
                    for (k = 0; k < count; ++k) {
                        quant_stack1[quant_level-1][k] = fv[k] ;
                        quant_assigned[quant_backup][quant_level-1][k] = 1 ;
                    }
                }
                j = 0 ;
                int_res[i] = _res_copy(res) ;
re_entryca:
                while (j < p->u.case_stmt.count) {
                    if (match_used[j]) {
                        ++j ;
                        continue ;
                    }
#ifdef DEBUG
                    _space() ; printf("Testing %d %d\n", i, j) ;
#endif
                    if (p->u.case_stmt.args[i*2]==e->u.case_stmt.args[j*2]) {
                        fv = _th_get_free_vars(e->u.case_stmt.args[j*2],&count) ;
                        if (count != quant_count[quant_level-1]) {
                            ++j ;
                            continue ;
                        }
                        for (k = 0; k < count; ++k) {
                            quant_stack2[quant_level-1][k] = fv[k] ;
                        }
#ifdef DEBUG
                        _space() ; printf("exp: %s\n",
                            _th_print_exp(p->u.case_stmt.args[i*2+1])) ;
                        printf("exp: %s\n",
                            _th_print_exp(e->u.case_stmt.args[j*2+1])) ;
#endif
                        set_start(p->u.case_stmt.count*2) ;
                        tr = _m_match(env,p->u.case_stmt.args[i*2+1],
                            e->u.case_stmt.args[j*2+1],res) ;
                        set_start(0-p->u.case_stmt.count*2) ;
                        if (tr != NULL) {
                            res = tr ;
                            goto contca ;
                        }
                    } else if ((u = map_patterns(_th_new_unifier(MATCH_SPACE),
                        p->u.case_stmt.args[i*2],
                        e->u.case_stmt.args[j*2]))!=NULL) {
                        fv = _th_get_free_vars(e->u.case_stmt.args[j*2],&count) ;
                        if (count != quant_count[quant_level-1]) {
                            ++j ;
                            continue ;
                        }
                        for (k = 0; k < count; ++k) {
                            quant_stack2[quant_level-1][k] = fv[k] ;
                        }
#ifdef DEBUG
                        _space () ;
                        printf("exp: %s\n",
                            _th_print_exp(p->u.case_stmt.args[i*2+1])) ;
                        printf("exp: %s\n",
                            _th_print_exp(e->u.case_stmt.args[j*2+1])) ;
#endif
                        set_start(p->u.case_stmt.count*2) ;
                        tr = _m_match(env,p->u.case_stmt.args[i*2+1],e->u.case_stmt.args[j*2+1],res) ;
                        set_start(0-p->u.case_stmt.count*2) ;
                        if (tr!=NULL) {
                            res = tr ;
                            goto contca ;
                        }
                    }
                    ++j ;
                }
                if (i > 0) {
                    --i ;
                    match_used[match_value[i]] = 0 ;
                    j = match_value[i]+1 ;
                    goto re_entryca ;
                } else {
                    --quant_level ;
#ifdef DEBUG
                    space -= 2 ;
#endif
                    return NULL ;
                }
contca:
                match_used[j] = 1 ;
                match_value[i] = j ;
            }
            --quant_level ;
#ifdef DEBUG
            space -= 2 ;
#endif
            return res ;
            
        default:
            if (e!=p) {
#ifdef DEBUG
                space -= 2 ;
#endif
                return NULL ;
            }
            
    }
end_case:
    last = (struct match_return *)_th_alloc(MATCH_SPACE, sizeof(struct match_return)) ;
    last->next = NULL ;
    last->theta = theta ;
    
#ifdef DEBUG
    space -= 2 ;
#endif
    return last ;
}

struct match_return *_th_match(struct env *env,
                               struct _ex_intern *p, struct _ex_intern *e)
{
    quant_level = 0 ;
    quant_backup = 0 ;
    quant_save_count = 0 ;
    quant_stop = 0 ;
#ifdef DEBUG
    space = 0 ;
#endif
    return _match (env, p, e, _th_new_unifier(MATCH_SPACE)) ;
}

static void unmark1_expression(struct _ex_intern *e)
{
    int i ;

    if (e->mark1==0) return ;

    e->mark1 = 0 ;

    switch(e->type) {

        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                unmark1_expression(e->u.appl.args[i]) ;
            }
            break ;

        case EXP_CASE:
            unmark1_expression(e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count*2; ++i) {
                unmark1_expression(e->u.case_stmt.args[i]) ;
            }
            break ;

        case EXP_QUANT:
            unmark1_expression(e->u.quant.exp) ;
            unmark1_expression(e->u.quant.cond) ;
            break ;

        case EXP_INDEX:
            unmark1_expression(e->u.index.exp) ;
            break ;
    }
}

static void unmark2_expression(struct _ex_intern *e)
{
    int i ;

    if (e->mark2==0) return ;

    e->mark2 = 0 ;

    switch(e->type) {

        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                unmark2_expression(e->u.appl.args[i]) ;
            }
            break ;

        case EXP_CASE:
            unmark2_expression(e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count*2; ++i) {
                unmark2_expression(e->u.case_stmt.args[i]) ;
            }
            break ;

        case EXP_QUANT:
            unmark2_expression(e->u.quant.exp) ;
            unmark2_expression(e->u.quant.cond) ;
            break ;

        case EXP_INDEX:
            unmark2_expression(e->u.index.exp) ;
            break ;
    }
}

int _th_all_symbols_smaller(struct env *env,struct _ex_intern *e,unsigned s)
{
    int i ;

    switch(e->type) {

        case EXP_APPL:
            if (!_th_has_smaller_precedence(env, e->u.appl.functor, s)) {
                _zone_print2("Failure %s %s", _th_intern_decode(e->u.appl.functor), _th_intern_decode(s)) ;
                return 0 ;
            }
            for (i = 0; i < e->u.appl.count; ++i) {
                if (!_th_all_symbols_smaller(env,e->u.appl.args[i],s)) return 0 ;
            }
            return 1 ;

        case EXP_CASE:
            if (!_th_all_symbols_smaller(env,e->u.case_stmt.exp,s)) return 0 ;
            for (i = 0; i < e->u.case_stmt.count*2; ++i) {
                if (!_th_all_symbols_smaller(env,e->u.case_stmt.args[i],s)) return 0 ;
            }
            return 1 ;

        case EXP_QUANT:
            return _th_all_symbols_smaller(env,e->u.quant.exp,s) &&
                   _th_all_symbols_smaller(env,e->u.quant.cond,s) ;

        case EXP_INDEX:
            return _th_all_symbols_smaller(env,e->u.index.exp,s) ;

        default:
			return 1 ;
    }
}

static int _much_smaller(struct env *env,struct _ex_intern *e1,struct _ex_intern *e2)
{
    int i ;

    if (e2->mark2) return 1 ;

    e2->mark2 = 2 ;

    switch(e2->type) {

        case EXP_APPL:
            if (!_th_all_symbols_smaller(env, e1, e2->u.appl.functor)) {
                unmark1_expression(e1) ;
                return 0 ;
            }
            unmark1_expression(e1) ;
            for (i = 0; i < e2->u.appl.count; ++i) {
                if (!_much_smaller(env,e1,e2->u.appl.args[i])) return 0 ;
            }
            return 1 ;

        case EXP_CASE:
            if (!_much_smaller(env,e1,e2->u.case_stmt.exp)) return 0 ;
            for (i = 0; i < e2->u.case_stmt.count*2; ++i) {
                if (!_much_smaller(env,e1,e2->u.case_stmt.args[i])) return 0 ;
            }
            return 1 ;

        case EXP_QUANT:
            return _much_smaller(env,e1,e2->u.quant.exp) &&
                   _much_smaller(env,e1,e2->u.quant.cond) ;
            break ;

        case EXP_INDEX:
            return _much_smaller(env,e1,e2->u.index.exp) ;
            break ;
		default:
			return 0 ;
    }
}

int _th_much_smaller(struct env *env, struct _ex_intern *e1, struct _ex_intern *e2)
{
    int r ;

    r = _much_smaller(env,e1,e2) ;
    unmark2_expression(e2) ;
    return r ;
}

static int arg_count ;

void _expand_parameter(struct env *env,struct prex_param_info *p,
                       struct _ex_intern *e)
{
    struct match_return *mr ;
    void *iterator ;
    unsigned var ;
    int i ;

    for (i = 0; i < p->count; ++i) {
        set_start(arg_count) ;
        mr = _th_match(env, p->exps[i], e) ;
        set_start(0-arg_count) ;
        if (mr != NULL) {
            iterator = _th_dom_init(MATCH_SPACE,mr->theta) ;
            while (var = _th_dom_next(iterator)) {
                _expand_parameter(env, p, _th_apply(mr->theta,var)) ;
            }
            return ;
        }
    }
    check_size(arg_count+1) ;
    args[arg_count++] = e ;
}

void _expand_arg_list(struct env *env, struct prex_info *p, struct _ex_intern *e)
{
    int i ;

    if (p == NULL) {
        check_size(e->u.appl.count) ;
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = e->u.appl.args[i] ;
        }
        arg_count = e->u.appl.count ;
    } else {
        arg_count = 0 ;
        for (i = 0; i < p->count; ++i) {
            _expand_parameter(env,p->info[i],e->u.appl.args[p->info[i]->param]) ;
        }
    }
}

static void reset_data(struct _ex_intern *e1, struct _ex_intern *e2)
{
    int i ;

    if (e1->type==EXP_QUANT) {
        for (i = 0; i < e1->u.quant.var_count; ++i) {
            _th_intern_set_data(e1->u.quant.vars[i],_th_intern_get_data(e1->u.quant.vars[i])-2) ;
        }
    }
    if (e2->type==EXP_QUANT) {
        for (i = 0; i < e2->u.quant.var_count; ++i) {
            _th_intern_set_data(e2->u.quant.vars[i],_th_intern_get_data(e2->u.quant.vars[i])-65536) ;
        }
    }
}

static int equal_to_subterm(struct env *env, struct _ex_intern *e1, struct _ex_intern *e2)
{
    int i ;
    switch (e2->type) {
        case EXP_APPL:
            for (i = 0; i < e2->u.appl.count; ++i) {
                if (_th_equal(env,e1,e2->u.appl.args[i])) return 1 ;
            }
            for (i = 0; i < e2->u.appl.count; ++i) {
                if (equal_to_subterm(env,e1,e2->u.appl.args[i])) return 1 ;
            }
            return 0 ;
        case EXP_QUANT:
            if (_th_equal(env,e1,e2->u.quant.exp)) return 1 ;
            if (_th_equal(env,e1,e2->u.quant.cond)) return 1 ;
            if (equal_to_subterm(env,e1,e2->u.quant.exp)) return 1 ;
            if (equal_to_subterm(env,e1,e2->u.quant.cond)) return 1 ;
            return 0 ;
        default:
            return 0 ;
    }
}

int _th_equal_smaller(struct env *env, struct _ex_intern *e1, struct _ex_intern *e2)
{
    int count, i, j, res ;
    int e1functor, e2functor ;
    int *free_vars ;
    int arg1_count, arg2_count ;
    int size ;

    _zone_print_exp("Equal Smaller term ordering of", e1) ;
    _zone_print_exp("and", e2) ;
    _tree_indent() ;
    switch(e1->type) {

        case EXP_VAR:
            if (_th_intern_get_data(e1->u.var)) {
                return 1 ;
            }
            free_vars = _th_get_free_vars_leave_marked(e2, &count);
            res = _th_intern_get_data(e1->u.var) ;
            for (i = 0; i < count; ++i) {
                _th_intern_set_data(free_vars[i], _th_intern_get_data(free_vars[i])&0xfffffffe) ;
            }
            _tree_undent() ;
            return res ;

        case EXP_MARKED_VAR:
            free_vars = _th_get_free_vars_leave_marked(e2, &count);
            res = _th_intern_get_data(e1->u.var) ;
            for (i = 0; i < count; ++i) {
                 _th_intern_set_data(free_vars[i], 0) ;
            }
            if (res) {
                _tree_undent() ;
                return 0 ;
            }
            free_vars = _th_get_marked_vars_leave_marked(e2, &count);
            res = _th_intern_get_data(e1->u.var) ;
            for (i = 0; i < count; ++i) {
                 _th_intern_set_data(free_vars[i], 0) ;
            }
            _tree_undent() ;
            return res ;

        case EXP_INTEGER:
            switch (e2->type) {
                case EXP_INTEGER:
                    _tree_undent() ;
                    return !_th_big_less(e2->u.integer,e1->u.integer) ;
                case EXP_APPL:
                    _tree_undent() ;
                    return 1 ;
                case EXP_VAR:
                    _tree_undent() ;
                    return 1;
                default:
                    _tree_undent() ;
                    return 0;
            }

        case EXP_RATIONAL:
            switch (e2->type) {
                case EXP_RATIONAL:
                    /*return (e1->u.rational.numerator * e2->u.rational.denominator <=
                            e2->u.rational.numerator * e1->u.rational.numerator) ;*/
                    _tree_undent() ;
                    return 0 ;
                case EXP_APPL:
                    _tree_undent() ;
                    return 1 ;
                case EXP_VAR:
                    _tree_undent() ;
                    return 1;
                default:
                    _tree_undent() ;
                    return 0;
            }

        case EXP_STRING:
            switch (e2->type) {
                case EXP_STRING:
                    _tree_undent() ;
                    return strcmp(e1->u.string, e2->u.string) >= -1 ;
                case EXP_APPL:
                    _tree_undent() ;
                    return 1 ;
                case EXP_VAR:
                    _tree_undent() ;
                    return 1;
                default:
                    _tree_undent() ;
                    return 0;
            }
        case EXP_QUANT:
            switch (e2->type) {
                case EXP_APPL:
                    _expand_arg_list(env,_th_get_prex_info(env,e2->u.appl.functor),e2) ;
                    e2functor = e2->u.appl.functor;
                    for (arg2_count = 0; arg2_count < arg_count; ++arg2_count) {
                        args2[arg2_count] = args[arg2_count] ;
                    }
                    break;
                case EXP_QUANT:
                    args2[0] = e2->u.quant.exp ;
                    args2[1] = e2->u.quant.cond ;
                    arg2_count = 2 ;
                    e2functor = e2->u.quant.quant ;
                    for (i = 0; i < e2->u.quant.var_count; ++i) {
                        _th_intern_set_data(e2->u.quant.vars[i],_th_intern_get_data(e2->u.quant.vars[i])+65536) ;
                    }
                    break ;
                default:
                    _tree_undent() ;
                    return 0 ;
            }
            for (i = 0; i < e1->u.quant.var_count; ++i) {
                _th_intern_set_data(e1->u.quant.vars[i],_th_intern_get_data(e1->u.quant.vars[i])+2) ;
            }
            e1functor = e1->u.quant.quant ;
            args[0] = e1->u.quant.exp ;
            args[1] = e1->u.quant.cond ;
            size = arg1_count = 2 ;
            if (size < arg2_count) size = arg2_count ;
            goto cont ;
        case EXP_APPL:
            switch (e2->type) {
                case EXP_APPL:
                    _expand_arg_list(env,_th_get_prex_info(env,e2->u.appl.functor),e2) ;
                    e2functor = e2->u.appl.functor;
                    for (arg2_count = 0; arg2_count < arg_count; ++arg2_count) {
                        args2[arg2_count] = args[arg2_count] ;
                    }
                    break;
                case EXP_QUANT:
                    args2[0] = e2->u.quant.exp ;
                    args2[1] = e2->u.quant.cond ;
                    arg2_count = 2 ;
                    e2functor = e2->u.quant.quant ;
                    for (i = 0; i < e2->u.quant.var_count; ++i) {
                        _th_intern_set_data(e2->u.quant.vars[i],_th_intern_get_data(e2->u.quant.vars[i])+65536) ;
                    }
                    break ;
                default:
                    _tree_undent() ;
                    return 0 ;
            }
            e1functor = e1->u.appl.functor;
            _expand_arg_list(env,_th_get_prex_info(env,e1->u.appl.functor),e1) ;
            size = arg1_count = arg_count ;
            if (size < arg2_count) size = arg2_count ;
cont:
            if (_th_has_equal_precedence(env,e1->u.appl.functor,e2->u.appl.functor)) {
                if (e1->u.appl.functor==e2->u.appl.functor) {
                    int *info = _th_get_lex_info(env,e1->u.appl.functor) ;
                    if (info && info[0]==arg1_count && arg1_count==arg2_count) {
                        _zone_print0("lex ordering") ;
                        for (i = 0; i < arg1_count; ++i) {
                            set_start(size) ;
                            if (!_th_equal_smaller(env,args[i-size],e2)) {
                                set_start(0-size) ;
                                _tree_undent() ;
                                reset_data(e1,e2) ;
                                return 0 ;
                            }
                            set_start(0-size) ;
                        }
                        for (i = 1; i <= info[0]; ++i) {
                            set_start(size) ;
                            if (!_th_equal_smaller(env,args[info[i]-size],args2[info[i]-size])) {
                                set_start(0-size) ;
                                _tree_undent() ;
                                reset_data(e1,e2) ;
                                return 0 ;
                            }
                            if (!_th_equal_smaller(env,args2[info[i]-size],args[info[i]-size])) {
                                set_start(0-size) ;
                                _tree_undent() ;
                                _zone_print0("good") ;
                                reset_data(e1,e2) ;
                                return 1 ;
                            }
                            set_start(0-size) ;
                        }
                        _zone_print0("good") ;
                        _tree_undent();
                        reset_data(e1,e2) ;
                        return 1 ;
                    }
                }
                _zone_print0("Equal functor prec") ;
                for (i = 0; i <arg1_count; ++i) {
                    for (j = 0; j < arg2_count; ++j) {
                        set_start(size) ;
                        if (_th_equal_smaller(env,args[i-size],args2[j-size])) {
                            set_start(0-size) ;
                            goto next ;
                        }
                        set_start(0-size) ;
                    }
                    _tree_undent() ;
                    reset_data(e1,e2) ;
                    return 0 ;
next: ;
                }
                _tree_undent() ;
                reset_data(e1,e2) ;
                return 1 ;
            } else if (_th_has_smaller_precedence(env,e1->u.appl.functor,e2->u.appl.functor)) {
                _zone_print0("Smaller functor prec") ;
                for (i = 0;i < arg1_count; ++i) {
                    set_start(size) ;
                    if (!_th_equal_smaller(env,args[i-size],e2)) {
                        set_start(0-size) ;
                        _tree_undent() ;
                        reset_data(e1,e2) ;
                        return 0 ;
                    }
                    set_start(0-size) ;
                }
                _tree_undent() ;
                reset_data(e1,e2) ;
                return 1 ;
            } else {
                _zone_print0("Larger or no functor prec") ;
                for (i = 0;i < arg2_count; ++i) {
                    set_start(size) ;
                    if (_th_equal_smaller(env,e1,args2[i-size])) {
                        set_start(0-size) ;
                        _tree_undent() ;
                        reset_data(e1,e2) ;
                        return 1 ;
                    }
                    set_start(0-size) ;
                }
                _tree_undent() ;
                reset_data(e1,e2) ;
                return 0 ;
            }

        default:
            _tree_undent() ;
            return 0 ;
    }
}

int _smaller(struct env *env, struct _ex_intern *e1, struct _ex_intern *e2)
{
    int count, i, j, res ;
    int e1functor, e2functor ;
    int *free_vars ;
    int arg1_count, arg2_count ;
    int size ;
    struct _ex_intern *term = _ex_intern_appl2_env(env,INTERN_SMALLER,e1,e2);

    _zone_print_exp("Smaller term ordering of", e1) ;
    _zone_print_exp("and", e2) ;
    _tree_indent() ;

    if (term->rewrite) {
        _tree_undent();
        return term->rewrite==_ex_true;
    }
    term->next_cache = _th_rewrite_next;
    _th_rewrite_next = term;

    switch(e1->type) {

        case EXP_VAR:
            if (_th_intern_get_data(e1->u.var) & 2) {
                _zone_print0("Special var") ;
                _tree_undent();
                if (e2->type != EXP_VAR) {
                    term->rewrite = _ex_true;
                    return 1 ;
                }
                if (_th_intern_get_data(e2->u.var) & 65536) {
                    term->rewrite = _ex_false;
                    return 0 ;
                }
                term->rewrite = _ex_true;
                return 1 ;
            }
            if (e2->type==EXP_VAR) {
                term->rewrite = _ex_false;
                _tree_undent();
                return 0;
            }
            free_vars = _th_get_free_vars_leave_marked(e2, &count);
            res = _th_intern_get_data(e1->u.var) & 1;
            for (i = 0; i < count; ++i) {
                _th_intern_set_data(free_vars[i], _th_intern_get_data(free_vars[i])&0xfffffffe) ;
            }
            term->rewrite = (res?_ex_true:_ex_false);
            _tree_undent() ;
            return res ;

        case EXP_MARKED_VAR:
            if (e2->type==EXP_MARKED_VAR) {
                _tree_undent() ;
                term->rewrite = _ex_false;
                return 0;
            }
            free_vars = _th_get_marked_vars_leave_marked(e2, &count);
            res = _th_intern_get_data(e1->u.var) & 1;
            for (i = 0; i < count; ++i) {
                 _th_intern_set_data(free_vars[i], 0) ;
            }
            _tree_undent() ;
            term->rewrite = (res?_ex_true:_ex_false);
            return res ;

        case EXP_INTEGER:
            switch (e2->type) {
                //case EXP_INTEGER:
                    //_tree_undent() ;
                    //return _th_big_less(e1->u.integer,e2->u.integer) ;
                case EXP_APPL:
                    _tree_undent() ;
                    term->rewrite = _ex_true;
                    return 1 ;
                case EXP_VAR:
                case EXP_MARKED_VAR:
                    _tree_undent() ;
                    if (_th_intern_get_data(e2->u.var) & 65536) {
                        term->rewrite = _ex_false;
                        return 0 ;
                    }
                    term->rewrite = _ex_true;
                    return 1;
                default:
                    _tree_undent() ;
                    term->rewrite = _ex_false;
                    return 0;
            }

        case EXP_RATIONAL:
            switch (e2->type) {
                //case EXP_RATIONAL:
                    /*return (e1->u.rational.numerator * e2->u.rational.denominator <=
                            e2->u.rational.numerator * e1->u.rational.numerator) ;*/
                    //_tree_undent() ;
                    //return 0 ;
                case EXP_APPL:
                    _tree_undent() ;
                    term->rewrite = _ex_true;
                    return 1 ;
                case EXP_VAR:
                case EXP_MARKED_VAR:
                    _tree_undent() ;
                    if (_th_intern_get_data(e2->u.var) & 65536) {
                        term->rewrite = _ex_false;
                        return 0 ;
                    }
                    term->rewrite = _ex_true;
                    return 1;
                default:
                    _tree_undent() ;
                    term->rewrite = _ex_false;
                    return 0;
            }

        case EXP_STRING:
            switch (e2->type) {
                //case EXP_STRING:
                    //_tree_undent() ;
                    //return strcmp(e1->u.string, e2->u.string) > -1 ;
                case EXP_APPL:
                    _tree_undent() ;
                    term->rewrite = _ex_true;
                    return 1 ;
                case EXP_VAR:
                case EXP_MARKED_VAR:
                    _tree_undent() ;
                    if (_th_intern_get_data(e2->u.var) & 65536) {
                        term->rewrite = _ex_false;
                        return 0 ;
                    }
                    term->rewrite = _ex_true;
                    return 1 ;
                default:
                    _tree_undent() ;
                    term->rewrite = _ex_false;
                    return 0 ;
            }
        case EXP_QUANT:
            check_size(2);
            switch (e2->type) {
                case EXP_APPL:
                    _expand_arg_list(env,_th_get_prex_info(env,e2->u.appl.functor),e2) ;
                    e2functor = e2->u.appl.functor;
                    for (arg2_count = 0; arg2_count < arg_count; ++arg2_count) {
                        args2[arg2_count] = args[arg2_count] ;
                    }
                    break;
                case EXP_QUANT:
                    args2[0] = e2->u.quant.exp ;
                    args2[1] = e2->u.quant.cond ;
                    arg2_count = 2 ;
                    e2functor = e2->u.quant.quant ;
                    for (i = 0; i < e2->u.quant.var_count; ++i) {
                        _th_intern_set_data(e2->u.quant.vars[i],_th_intern_get_data(e2->u.quant.vars[i])+65536) ;
                    }
                    break ;
                default:
                    _tree_undent() ;
                    term->rewrite = _ex_false;
                    return 0 ;
            }
            for (i = 0; i < e1->u.quant.var_count; ++i) {
                _th_intern_set_data(e1->u.quant.vars[i],_th_intern_get_data(e1->u.quant.vars[i])+2) ;
            }
            e1functor = e1->u.quant.quant ;
            args[0] = e1->u.quant.exp ;
            args[1] = e1->u.quant.cond ;
            size = arg1_count = 2 ;
            if (size < arg2_count) size = arg2_count ;
            goto cont ;
        case EXP_APPL:
            //if (e1 != e2 && (e1->u.appl.functor==INTERN_APPLY_CONTEXT || e1->u.appl.functor==INTERN_USE_CONTEXT)) {
                //_tree_undent() ;
                //return 1 ;
            //}
            switch (e2->type) {
                case EXP_APPL:
                    _expand_arg_list(env,_th_get_prex_info(env,e2->u.appl.functor),e2) ;
                    e2functor = e2->u.appl.functor;
                    for (arg2_count = 0; arg2_count < arg_count; ++arg2_count) {
                        args2[arg2_count] = args[arg2_count] ;
                    }
                    break;
                case EXP_QUANT:
                    check_size(2);
                    args2[0] = e2->u.quant.exp ;
                    args2[1] = e2->u.quant.cond ;
                    arg2_count = 2 ;
                    e2functor = e2->u.quant.quant ;
                    for (i = 0; i < e2->u.quant.var_count; ++i) {
                        _th_intern_set_data(e2->u.quant.vars[i],_th_intern_get_data(e2->u.quant.vars[i])+65536) ;
                    }
                    break ;
                case EXP_MARKED_VAR:
                    if (_th_intern_get_data(e2->u.var) & 65536) {
                        _tree_undent() ;
                        term->rewrite = _ex_false;
                        return 0 ;
                    }
                    for (i = 0; i < e1->u.appl.count; ++i) {
                        if (!_smaller(env,e1->u.appl.args[i],e2)) {
                            _tree_undent() ;
                            term->rewrite = _ex_false;
                            return 0 ;
                        }
                    }
                    _tree_undent() ;
                    term->rewrite = _ex_true;
                    return 1 ;
                default:
                    _tree_undent() ;
                    term->rewrite = _ex_false;
                    return 0 ;
            }
            e1functor = e1->u.appl.functor;
            _expand_arg_list(env,_th_get_prex_info(env,e1->u.appl.functor),e1) ;
            size = arg1_count = arg_count ;
            if (size < arg2_count) size = arg2_count ;
cont:
            if (_th_has_equal_precedence(env,e1->u.appl.functor,e2->u.appl.functor)) {
                char *marks1 = ALLOCA(arg1_count * sizeof(char)) ;
                char *marks2 = ALLOCA(arg2_count * sizeof(char)) ;
                int sm = 0 ;
                if (e1->u.appl.functor==e2->u.appl.functor) {
                    int *info = _th_get_lex_info(env,e1->u.appl.functor) ;
                    if (info && info[0]==arg1_count && arg1_count==arg2_count) {
                        _zone_print0("lex ordering") ;
                        for (i = 0; i < arg1_count; ++i) {
                            set_start(size) ;
                            if (!_smaller(env,args[i-size],e2)) {
                                set_start(0-size) ;
                                goto greater ;
                            }
                            set_start(0-size) ;
                        }
                        for (i = 1; i <= info[0]; ++i) {
                            set_start(size) ;
                            if (_smaller(env,args[info[i]-size],args2[info[i]-size])) {
                                set_start(0-size) ;
                                _tree_undent() ;
                                _zone_print0("good") ;
                                reset_data(e1,e2) ;
                                term->rewrite = _ex_true;
                                return 1 ;
                            } else if (!_th_equal(env,args[info[i]-size],args2[info[i]-size])) {
                                _zone_print0("bad") ;
                                set_start(0-size) ;
                                goto greater ;
                            }
                            set_start(0-size) ;
                        }
                        _zone_print0("bad") ;
                        goto greater ;
                    }
                }
                _zone_print0("Equal functor prec") ;
                for (i = 0; i < arg1_count; ++i) {
                    marks1[i] = 0 ;
                }
                for (i = 0; i < arg2_count; ++i) {
                    marks2[i] = 0 ;
                }
                for (i = 0; i < arg1_count; ++i) {
                    for (j = 0; j < arg2_count; ++j) {
                        if (!marks2[j]) {
                            if (_th_equal(env,args[i],args2[j])) {
                                marks1[i] = marks2[j] = 1 ;
                            }
                        }
                    }
                }
                for (i = 0; i < arg1_count; ++i) {
                    if (!marks1[i]) {
                        for (j = 0; j < arg2_count; ++j) {
                            if (!marks2[j]) {
                                set_start(size) ;
                                if (_smaller(env,args[i-size],args2[j-size])) {
                                    sm = 1 ;
                                    set_start(0-size) ;
                                    goto next ;
                                }
                                set_start(0-size) ;
                            }
                        }
                        goto greater ;
                    }
next: ;
                }
                if (!sm) goto greater;
                _tree_undent() ;
                reset_data(e1,e2) ;
                term->rewrite = _ex_true;
                return 1 ;
            } else if (_th_has_smaller_precedence(env,e1->u.appl.functor,e2->u.appl.functor)) {
                _zone_print0("Smaller functor prec") ;
                for (i = 0;i < arg1_count; ++i) {
                    set_start(size) ;
                    if (!_smaller(env,args[i-size],e2)) {
                        set_start(0-size) ;
                        _tree_undent() ;
                        reset_data(e1,e2) ;
                        _zone_print0("bad") ;
                        term->rewrite = _ex_false;
                        return 0 ;
                    }
                    set_start(0-size) ;
                }
                _tree_undent() ;
                reset_data(e1,e2) ;
                _zone_print0("good") ;
                term->rewrite = _ex_true;
                return 1 ;
            } else {
                _zone_print0("Larger or no functor prec") ;
greater:
                for (i = 0;i < arg2_count; ++i) {
                    set_start(size) ;
                    if (_smaller(env,e1,args2[i-size]) ||
                        _th_equal(env,e1,args2[i-size])) {
                        set_start(0-size) ;
                        _tree_undent() ;
                        reset_data(e1,e2) ;
                        term->rewrite = _ex_true;
                        return 1 ;
                    }
                    set_start(0-size) ;
                }
                _tree_undent() ;
                reset_data(e1,e2) ;
                term->rewrite = _ex_false;
                return 0 ;
            }

        default:
            _tree_undent() ;
            term->rewrite = _ex_false;
            return 0 ;
    }
}

int _th_smaller(struct env *env, struct _ex_intern *e1, struct _ex_intern *e2)
{
    return _smaller(env, e1, e2);
}

int _th_smaller2(struct env *env, struct _ex_intern *e1, struct _ex_intern *e2)
{
    int count, i, j, res ;
    int e1functor, e2functor ;
    int *free_vars ;
    int arg1_count, arg2_count ;
    int size ;

    switch(e1->type) {

        case EXP_VAR:
            if (_th_intern_get_data(e1->u.var) & 2) {
                //if (e2->type != EXP_VAR) return 1 ;
                //if (_th_intern_get_data(e2->u.var) & 65536) return 0 ;
                return 1 ;
            }
            if (e2->type==EXP_VAR) {
                return 0;
            }
            free_vars = _th_get_free_vars_leave_marked(e2, &count);
            res = _th_intern_get_data(e1->u.var) & 1;
            for (i = 0; i < count; ++i) {
                _th_intern_set_data(free_vars[i], _th_intern_get_data(free_vars[i])&0xfffffffe) ;
            }
            return res ;

        case EXP_MARKED_VAR:
            if (e2->type==EXP_MARKED_VAR) {
                return 0;
            }
            free_vars = _th_get_free_vars_leave_marked(e2, &count);
            res = _th_intern_get_data(e1->u.var) & 1;
            for (i = 0; i < count; ++i) {
                 _th_intern_set_data(free_vars[i], 0) ;
            }
            if (res) {
                return 1 ;
            }
            free_vars = _th_get_marked_vars_leave_marked(e2, &count);
            res = _th_intern_get_data(e1->u.var) & 1;
            for (i = 0; i < count; ++i) {
                 _th_intern_set_data(free_vars[i], 0) ;
            }
            return res ;

        case EXP_INTEGER:
            switch (e2->type) {
                //case EXP_INTEGER:
                    //return _th_big_less(e1->u.integer,e2->u.integer) ;
                case EXP_APPL:
                    return 1 ;
                case EXP_VAR:
                case EXP_MARKED_VAR:
                    return 1;
                default:
                    return 0;
            }

        case EXP_RATIONAL:
            switch (e2->type) {
                //case EXP_RATIONAL:
                    /*return (e1->u.rational.numerator * e2->u.rational.denominator <=
                            e2->u.rational.numerator * e1->u.rational.numerator) ;*/
                    //return 0 ;
                case EXP_APPL:
                    return 1 ;
                case EXP_VAR:
                case EXP_MARKED_VAR:
                    return 1;
                default:
                    return 0;
            }

        case EXP_STRING:
            switch (e2->type) {
                //case EXP_STRING:
                    //return strcmp(e1->u.string, e2->u.string) > -1 ;
                case EXP_APPL:
                    return 1 ;
                case EXP_VAR:
                case EXP_MARKED_VAR:
                    return 1 ;
                default:
                    return 0 ;
            }
        case EXP_QUANT:
            switch (e2->type) {
                case EXP_APPL:
                    _expand_arg_list(env,_th_get_prex_info(env,e2->u.appl.functor),e2) ;
                    e2functor = e2->u.appl.functor;
                    for (arg2_count = 0; arg2_count < arg_count; ++arg2_count) {
                        args2[arg2_count] = args[arg2_count] ;
                    }
                    break;
                case EXP_QUANT:
                    args2[0] = e2->u.quant.exp ;
                    args2[1] = e2->u.quant.cond ;
                    arg2_count = 2 ;
                    e2functor = e2->u.quant.quant ;
                    for (i = 0; i < e2->u.quant.var_count; ++i) {
                        _th_intern_set_data(e2->u.quant.vars[i],_th_intern_get_data(e2->u.quant.vars[i])+65536) ;
                    }
                    break ;
                default:
                    return 0 ;
            }
            for (i = 0; i < e1->u.quant.var_count; ++i) {
                _th_intern_set_data(e1->u.quant.vars[i],_th_intern_get_data(e1->u.quant.vars[i])+2) ;
            }
            e1functor = e1->u.quant.quant ;
            args[0] = e1->u.quant.exp ;
            args[1] = e1->u.quant.cond ;
            size = arg1_count = 2 ;
            if (size < arg2_count) size = arg2_count ;
            goto cont ;
        case EXP_APPL:
            switch (e2->type) {
                case EXP_APPL:
                    _expand_arg_list(env,_th_get_prex_info(env,e2->u.appl.functor),e2) ;
                    e2functor = e2->u.appl.functor;
                    for (arg2_count = 0; arg2_count < arg_count; ++arg2_count) {
                        args2[arg2_count] = args[arg2_count] ;
                    }
                    break;
                case EXP_QUANT:
                    args2[0] = e2->u.quant.exp ;
                    args2[1] = e2->u.quant.cond ;
                    arg2_count = 2 ;
                    e2functor = e2->u.quant.quant ;
                    for (i = 0; i < e2->u.quant.var_count; ++i) {
                        _th_intern_set_data(e2->u.quant.vars[i],_th_intern_get_data(e2->u.quant.vars[i])+65536) ;
                    }
                    break ;
                case EXP_MARKED_VAR:
                    for (i = 0; i < e1->u.appl.count; ++i) {
                        if (!_th_smaller2(env,e1->u.appl.args[i],e2)) {
                            return 0 ;
                        }
                    }
                    return 1 ;
                default:
                    return 0 ;
            }
            e1functor = e1->u.appl.functor;
            _expand_arg_list(env,_th_get_prex_info(env,e1->u.appl.functor),e1) ;
            size = arg1_count = arg_count ;
            if (size < arg2_count) size = arg2_count ;
cont:
            if (_th_has_equal_precedence(env,e1->u.appl.functor,e2->u.appl.functor)) {
                char *marks1 = ALLOCA(arg1_count * sizeof(char)) ;
                char *marks2 = ALLOCA(arg2_count * sizeof(char)) ;
                int sm = 0 ;
                if (e1->u.appl.functor==e2->u.appl.functor) {
                    int *info = _th_get_lex_info(env,e1->u.appl.functor) ;
                    if (info && info[0]==arg1_count && arg1_count==arg2_count) {
                        for (i = 0; i < arg1_count; ++i) {
                            set_start(size) ;
                            if (!_th_smaller2(env,args[i-size],e2)) {
                                set_start(0-size) ;
                                goto greater ;
                            }
                            set_start(0-size) ;
                        }
                        for (i = 1; i <= info[0]; ++i) {
                            set_start(size) ;
                            if (_th_smaller2(env,args[info[i]-size],args2[info[i]-size])) {
                                set_start(0-size) ;
                                reset_data(e1,e2) ;
                                return 1 ;
                            } else if (!_th_equal(env,args[info[i]-size],args2[info[i]-size])) {
                                set_start(0-size) ;
                                goto greater ;
                            }
                            set_start(0-size) ;
                        }
                        goto greater ;
                    }
                }
                for (i = 0; i < arg1_count; ++i) {
                    marks1[i] = 0 ;
                }
                for (i = 0; i < arg2_count; ++i) {
                    marks2[i] = 0 ;
                }
                for (i = 0; i < arg1_count; ++i) {
                    for (j = 0; j < arg2_count; ++j) {
                        if (!marks2[j]) {
                            if (_th_equal(env,args[i],args2[j])) {
                                marks1[i] = marks2[j] = 1 ;
                            }
                        }
                    }
                }
                for (i = 0; i < arg1_count; ++i) {
                    if (!marks1[i]) {
                        for (j = 0; j < arg2_count; ++j) {
                            if (!marks2[j]) {
                                set_start(size) ;
                                if (_th_smaller2(env,args[i-size],args2[j-size])) {
                                    sm = 1 ;
                                    set_start(0-size) ;
                                    goto next ;
                                }
                                set_start(0-size) ;
                            }
                        }
                        goto greater ;
                    }
next: ;
                }
                if (!sm) goto greater ;
                reset_data(e1,e2) ;
                return 1 ;
            } else if (_th_has_smaller_precedence(env,e1->u.appl.functor,e2->u.appl.functor)) {
                for (i = 0;i < arg1_count; ++i) {
                    set_start(size) ;
                    if (!_th_smaller2(env,args[i-size],e2)) {
                        set_start(0-size) ;
                        reset_data(e1,e2) ;
                        return 0 ;
                    }
                    set_start(0-size) ;
                }
                reset_data(e1,e2) ;
                return 1 ;
            } else {
greater:
                for (i = 0;i < arg2_count; ++i) {
                    set_start(size) ;
                    if (_th_smaller2(env,e1,args2[i-size]) ||
                        _th_equal(env,e1,args2[i-size])) {
                        set_start(0-size) ;
                        reset_data(e1,e2) ;
                        return 1 ;
                    }
                    set_start(0-size) ;
                }
                reset_data(e1,e2) ;
                return 0 ;
            }

        default:
            return 0 ;
    }
}

//#define SMALLER3_PRINT

int _th_smaller3(struct env *env, struct _ex_intern *e1, struct _ex_intern *e2)
{
    int count, i, j, res ;
    int e1functor, e2functor ;
    int *free_vars ;
    int arg1_count, arg2_count ;
    int size ;
#ifdef SMALLER3_PRINT
    _zone_print_exp("smaller3", e1) ;
    _zone_print_exp("and", e2) ;
#endif
    _tree_indent() ;
    switch(e1->type) {
        
    case EXP_VAR:
        _tree_undent() ;
        return 1 ;

    case EXP_MARKED_VAR:
        if (e2->type==EXP_MARKED_VAR) {
            _tree_undent() ;
            return 0;
        }
        free_vars = _th_get_free_vars_leave_marked(e2, &count);
        res = _th_intern_get_data(e1->u.var) & 1;
        for (i = 0; i < count; ++i) {
            _th_intern_set_data(free_vars[i], 0) ;
        }
        if (res) {
            _tree_undent() ;
            return 1 ;
        }
        free_vars = _th_get_marked_vars_leave_marked(e2, &count);
        res = _th_intern_get_data(e1->u.var) & 1;
        for (i = 0; i < count; ++i) {
            _th_intern_set_data(free_vars[i], 0) ;
        }
        _tree_undent() ;
        return res ;
        
    case EXP_INTEGER:
        switch (e2->type) {
            //case EXP_INTEGER:
            //return _th_big_less(e1->u.integer,e2->u.integer) ;
        case EXP_APPL:
            _tree_undent() ;
            return 1 ;
        case EXP_VAR:
            _tree_undent() ;
            return 0 ;
        case EXP_MARKED_VAR:
            _tree_undent() ;
            return 1;
        default:
            _tree_undent() ;
            return 0;
        }
        
    case EXP_RATIONAL:
        switch (e2->type) {
            //case EXP_RATIONAL:
            /*return (e1->u.rational.numerator * e2->u.rational.denominator <=
            e2->u.rational.numerator * e1->u.rational.numerator) ;*/
            //return 0 ;
        case EXP_APPL:
            _tree_undent() ;
            return 1 ;
        case EXP_VAR:
            _tree_undent() ;
            return 0 ;
        case EXP_MARKED_VAR:
            _tree_undent() ;
            return 1;
        default:
            _tree_undent() ;
            return 0;
        }
            
    case EXP_STRING:
        switch (e2->type) {
            //case EXP_STRING:
            //return strcmp(e1->u.string, e2->u.string) > -1 ;
        case EXP_APPL:
            _tree_undent() ;
            return 1 ;
        case EXP_VAR:
            _tree_undent() ;
            return 0 ;
        case EXP_MARKED_VAR:
            _tree_undent() ;
            return 1 ;
        default:
            _tree_undent() ;
            return 0 ;
        }
    case EXP_QUANT:
        switch (e2->type) {
        case EXP_APPL:
            _expand_arg_list(env,_th_get_prex_info(env,e2->u.appl.functor),e2) ;
            e2functor = e2->u.appl.functor;
            for (arg2_count = 0; arg2_count < arg_count; ++arg2_count) {
                args2[arg2_count] = args[arg2_count] ;
            }
            break;
        case EXP_QUANT:
            args2[0] = e2->u.quant.exp ;
            args2[1] = e2->u.quant.cond ;
            arg2_count = 2 ;
            e2functor = e2->u.quant.quant ;
            for (i = 0; i < e2->u.quant.var_count; ++i) {
                _th_intern_set_data(e2->u.quant.vars[i],_th_intern_get_data(e2->u.quant.vars[i])+65536) ;
            }
            break ;
        default:
            _tree_undent() ;
            return 0 ;
        }
        for (i = 0; i < e1->u.quant.var_count; ++i) {
            _th_intern_set_data(e1->u.quant.vars[i],_th_intern_get_data(e1->u.quant.vars[i])+2) ;
        }
        e1functor = e1->u.quant.quant ;
        args[0] = e1->u.quant.exp ;
        args[1] = e1->u.quant.cond ;
        size = arg1_count = 2 ;
        if (size < arg2_count) size = arg2_count ;
        goto cont ;
    case EXP_APPL:
        switch (e2->type) {
        case EXP_APPL:
            _expand_arg_list(env,_th_get_prex_info(env,e2->u.appl.functor),e2) ;
            e2functor = e2->u.appl.functor;
            for (arg2_count = 0; arg2_count < arg_count; ++arg2_count) {
                args2[arg2_count] = args[arg2_count] ;
            }
            break;
        case EXP_QUANT:
            args2[0] = e2->u.quant.exp ;
            args2[1] = e2->u.quant.cond ;
            arg2_count = 2 ;
            e2functor = e2->u.quant.quant ;
            for (i = 0; i < e2->u.quant.var_count; ++i) {
                 _th_intern_set_data(e2->u.quant.vars[i],_th_intern_get_data(e2->u.quant.vars[i])+65536) ;
            }
            break ;
        case EXP_MARKED_VAR:
            for (i = 0; i < e1->u.appl.count; ++i) {
                if (!_th_smaller3(env,e1->u.appl.args[i],e2)) {
                    _tree_undent() ;
                    return 0 ;
                }
            }
            _tree_undent() ;
            return 1 ;
        default:
            _tree_undent() ;
            return 0 ;
        }
        e1functor = e1->u.appl.functor;
        _expand_arg_list(env,_th_get_prex_info(env,e1->u.appl.functor),e1) ;
        size = arg1_count = arg_count ;
        if (size < arg2_count) size = arg2_count ;
cont:
        if (_th_has_equal_precedence(env,e1->u.appl.functor,e2->u.appl.functor)) {
            char *marks1 = ALLOCA(arg1_count * sizeof(char)) ;
            char *marks2 = ALLOCA(arg2_count * sizeof(char)) ;
            int sm = 0 ;
#ifdef SMALLER3_PRINT
            _zone_print0("equal") ;
#endif
            if (e1->u.appl.functor==e2->u.appl.functor) {
                int *info = _th_get_lex_info(env,e1->u.appl.functor) ;
                if (info && info[0]==arg1_count && arg1_count==arg2_count) {
#ifdef SMALLER3_PRINT
                    _zone_print0("lex");
#endif
                    for (i = 0; i < arg1_count; ++i) {
                        set_start(size) ;
                        if (!_th_smaller3(env,args[i-size],e2)) {
                            set_start(0-size) ;
                            goto greater ;
                        }
                        set_start(0-size) ;
                    }
                    for (i = 1; i <= info[0]; ++i) {
                        set_start(size) ;
                        if (_th_smaller3(env,args[info[i]-size],args2[info[i]-size])) {
                            set_start(0-size) ;
                            reset_data(e1,e2) ;
                            _tree_undent() ;
                            return 1 ;
                        } else if (!_th_equal(env,args[info[i]-size],args2[info[i]-size])) {
                            set_start(0-size) ;
                            goto greater ;
                        }
                        set_start(0-size) ;
                    }
                    goto greater ;
                }
            }
            for (i = 0; i < arg1_count; ++i) {
                marks1[i] = 0 ;
            }
            for (i = 0; i < arg2_count; ++i) {
                marks2[i] = 0 ;
            }
            for (i = 0; i < arg1_count; ++i) {
                for (j = 0; j < arg2_count; ++j) {
                    if (!marks2[j]) {
                        if (_th_equal(env,args[i],args2[j])) {
                            marks1[i] = marks2[j] = 1 ;
                        }
                    }
                }
            }

#ifdef SMALLER3_PRINT
            _zone_print2("comp %d %d", arg1_count, arg2_count) ;
#endif
            for (i = 0; i < arg1_count; ++i) {
                if (!marks1[i]) {
                    for (j = 0; j < arg2_count; ++j) {
                        if (!marks2[j]) {
                            set_start(size) ;
                            if (_th_smaller3(env,args[i-size],args2[j-size])) {
                                sm = 1 ;
                                set_start(0-size) ;
                                goto next ;
                            }
                            set_start(0-size) ;
                        }
                    }
                    goto greater ;
                }
next: ;
            }
            if (!sm) goto greater ;
            reset_data(e1,e2) ;
            _tree_undent() ;
            return 1 ;
        } else if (_th_has_smaller_precedence(env,e1->u.appl.functor,e2->u.appl.functor)) {
#ifdef SMALLER3_PRINT
            _zone_print0("smaller") ;
#endif
            for (i = 0;i < arg1_count; ++i) {
                set_start(size) ;
                if (!_th_smaller3(env,args[i-size],e2)) {
                    set_start(0-size) ;
                    goto greater ;
                }
                set_start(0-size) ;
            }
            reset_data(e1,e2) ;
            _tree_undent() ;
            return 1 ;
        } else {
greater:
#ifdef SMALLER3_PRINT
            _zone_print0("greater") ;
#endif
            for (i = 0;i < arg2_count; ++i) {
                set_start(size) ;
                if (_th_smaller3(env,e1,args2[i-size]) ||
                    _th_equal(env,e1,args2[i-size])) {
                    set_start(0-size) ;
                    reset_data(e1,e2) ;
                    _tree_undent() ;
                    return 1 ;
                }
                set_start(0-size) ;
            }
            reset_data(e1,e2) ;
            _tree_undent() ;
            return 0 ;
        }
                
    default:
        _tree_undent() ;
        return 0 ;
    }
}

#ifdef UNIFIER
static struct unify_return *u_last ;

static struct unify_return *_unify(struct env *env,
                                   struct _ex_intern *p, struct _ex_intern *e,
                                   struct _ex_unifier *theta1,
                                   struct _ex_unifier *theta2) ;

static struct unify_return *_m_unify(struct env *env,
                                     struct _ex_intern *p, struct _ex_intern *e,
                                     struct unify_return *mtheta)
{
    struct unify_return *p_theta, *llast, *theta ;

    p_theta = NULL ;

    while(mtheta != NULL) {
        theta = _unify(env, p, e, mtheta->theta1, mtheta->theta2) ;
        if (theta == NULL) {
            mtheta = mtheta->next ;
            continue ;
        }
        u_last->next = p_theta ;
        if (p_theta==NULL) llast = u_last ;
        p_theta = theta ;
        mtheta = mtheta->next ;
    }

    u_last = llast ;
    return theta ;
}

static struct unify_return *_unify_res_copy(struct unify_return *r)
{
    struct unify_return *n ;

    if (r==NULL) return NULL ;

    n = (struct unify_return *)_th_alloc(MATCH_SPACE,sizeof(struct unify_return)) ;
    n->next = _unify_res_copy(r->next) ;
    n->theta1 = _th_shallow_copy_unifier(MATCH_SPACE,r->theta1) ;
    n->theta2 = _th_shallow_copy_unifier(MATCH_SPACE,r->theta2) ;

    return n ;
}

static struct unify_return *_make_unify1(struct match_return *m, struct _ex_unifier *u)
{
    struct unify_return *ures ;

    if (m==NULL) return NULL ;

    ures = (struct unify_return *)_th_alloc(MATCH_SPACE, sizeof(struct unify_return)) ;
    ures->theta1 = m->theta ;
    ures->theta2 = u ;
    if (m->next == NULL) u_last = ures ;

    ures->next = _make_unify1(m->next, u) ;
	return ures ;
}

static struct unify_return *_make_unify2(struct match_return *m, struct _ex_unifier *u)
{
    struct unify_return *ures ;

    if (m==NULL) return NULL ;

    ures = (struct unify_return *)_th_alloc(MATCH_SPACE, sizeof(struct unify_return)) ;
    ures->theta1 = u ;
    ures->theta2 = m->theta ;
    if (m->next == NULL) u_last = ures ;

    ures->next = _make_unify2(m->next, u) ;
	return ures ;
}

static struct unify_return *_unify(struct env *env,
                                   struct _ex_intern *p, struct _ex_intern *e,
                                   struct _ex_unifier *theta1,
                                   struct _ex_unifier *theta2)
{
    int d1, p1, d2, p2 ;
    int i, j, k, count ;
    unsigned match_used[MAX_ARGS], match_value[MAX_ARGS] ;
    struct unify_return *int_res[MAX_ARGS] ;
    struct unify_return mr, *res, *comp, *compl, *tr ;
    unsigned *fv ;
    struct _ex_unifier *u ;
    struct match_return *mat ;
    struct _ex_intern *s1, *s2 ;

    /**********/

#ifdef DEBUG
    printf("Unifying: ") ;
    printf("%s ", _th_print_exp(p)) ;
    printf("%s\n", _th_print_exp(e)) ;
#endif

    if (e->type == EXP_VAR) {
        get_depth2(e->u.var, &d2, &p2) ;
        if (d2 == -1) {
            if (p->type == EXP_VAR) {
                get_depth1(p->u.var, &d1, &p1) ;
                if (d1 != -1) return NULL ;
                s2 = _th_apply(theta2, e->u.var) ;
                s1 = _th_apply(theta1, p->u.var) ;
                if (s1==NULL) {
                    if (s2==NULL) {
                        theta1 = _th_add_pair(MATCH_SPACE,theta1,p->u.var,e) ;
                        goto done ;
                    } else {
                        mat = _match(env,p,s2,theta1) ;
                        return _make_unify1(mat,theta2) ;
                    }
                } else {
                    if (s2==NULL) {
                        mat = _match(env,e,s1,theta2) ;
                        return _make_unify2(mat,theta1) ;
                    } else {
                        quant_stop = quant_level ;
                        if (_equal(env,s1,s2)) {
                            quant_stop = 0 ;
                            goto done ;
                        }
                        quant_stop = 0 ;
                        return NULL ;
                    }
                }
            } else {
                s2 = _th_apply(theta2, e->u.var) ;
                if (s2==NULL) {
                    theta2 = _th_add_pair(MATCH_SPACE,theta2,e->u.var,p) ;
                } else {
                    mat = _match(env,p,s2,theta1) ;
                    return _make_unify1(mat,theta2) ;
                }
            }
        } else if (p->type == EXP_VAR) {
            get_depth1(p->u.var, &d1, &p1) ;
            if (d1 != d2 || p1 != p2) return NULL ;
            goto done ;
        } else {
            return NULL ;
        }
    }

    switch (p->type) {

        case EXP_VAR:
            get_depth1(p->u.var, &d1, &p1) ;
            if (d1 == -1) {
                s1 = _th_apply(theta1, p->u.var) ;
                if (s1==NULL) {
                    theta1 = _th_add_pair(MATCH_SPACE,theta1,p->u.var,e) ;
                } else {
                    mat = _match(env,e,s1,theta2) ;
                    return _make_unify2(mat,theta1) ;
                }
            } else {
                return NULL;
            }
            break ;

        case EXP_MARKED_VAR:
            if (e->type == EXP_MARKED_VAR) {
                if (p->u.marked_var.var != e->u.marked_var.var ||
                    p->u.marked_var.quant_level != e->u.marked_var.quant_level) return NULL ;
            } else if (e->type == EXP_VAR) {
                get_depth2(e->u.var, &d2, &p2) ;
                if (d2 != -1) return NULL ;
                if (p->u.marked_var.var != e->u.var ||
                    p->u.marked_var.quant_level != _th_intern_get_quant_level(e->u.var)) return NULL ;
            } else return NULL ;
            break ;

        case EXP_QUANT:
            if (p->u.quant.quant != e->u.quant.quant) return 0 ;
            if (p->u.quant.var_count != e->u.quant.var_count) return 0 ;
            if (quant_level >= MAX_QUANT_DEPTH-1) {
                printf("Too many nested quantifiers 6\n") ;
                exit(1) ;
            }
            comp = compl = NULL ;
            quant_stack1[quant_level] = (unsigned *)_th_alloc(MATCH_SPACE, p->u.quant.var_count * sizeof(unsigned)) ;
            quant_stack2[quant_level] = (unsigned *)_th_alloc(MATCH_SPACE, e->u.quant.var_count * sizeof(unsigned)) ;
            quant_assigned[quant_backup][quant_level] = (int *)_th_alloc(MATCH_SPACE, e->u.quant.var_count * sizeof(unsigned)) ;
            quant_count[quant_level] = e->u.quant.var_count ;
            for (i = 0; i < p->u.quant.var_count; ++i) {
                quant_stack1[quant_level][i] = p->u.quant.vars[i] ;
                quant_stack2[quant_level][i] = e->u.quant.vars[i] ;
                quant_assigned[quant_backup][quant_level][i] = i ;
            }
            ++quant_level ;
next_set:
            res = _unify(env,p->u.quant.cond,e->u.quant.cond,theta1,theta2) ;
            if (res != NULL) {
                res = _m_unify(env,p->u.quant.exp,e->u.quant.exp,res) ;
            }
            if (res != NULL) {
                if (comp != NULL) {
                    u_last->next = comp ;
                } else {
                    compl = u_last ;
                }
                comp = res ;
            }
            if (next(quant_assigned[quant_backup][quant_level-1], p->u.quant.var_count)) {
                for (i = 0; i < p->u.quant.var_count; ++i) {
                    quant_stack2[quant_level-1][i] = e->u.quant.vars[quant_assigned[quant_backup][quant_level-1][i]] ;
                }
                goto next_set ;
            }
            --quant_level ;
            u_last = compl ;
            return res ;
            break ;

        case EXP_APPL:
            if (e->type != EXP_APPL) return NULL ;
            if (p->u.appl.functor != e->u.appl.functor) return NULL ;
            if (_th_is_c(env,p->u.appl.functor) || _th_is_ac(env,p->u.appl.functor)) {
                if (p->u.appl.count != e->u.appl.count) return NULL ;
                count = _th_ac_arity(env,p->u.appl.functor) ;
                mr.next = NULL ;
                mr.theta1 = theta1 ;
                mr.theta2 = theta2 ;
                res = &mr ;
                comp = compl = NULL ;
                for (i = 0; i < count; ++i) {
                    res = _m_unify(env,p->u.appl.args[i],
                                   e->u.appl.args[i],res) ;
                    if (res==NULL) return NULL ;
                }
                for (i = count; i < p->u.appl.count; ++i) {
                    match_used[i] = 0 ;
                }
                for (i = count; i < p->u.appl.count; ++i) {
                    j = count ;
                    int_res[i] = _unify_res_copy(res) ;
re_entryc:
                    while (j < p->u.appl.count) {
                        if (match_used[j]) {
                            ++j ;
                            continue ;
                        }
                        if (tr = _m_unify(env,p->u.appl.args[i],e->u.appl.args[j],res)) {
                            res = tr ;
                            goto contc ;
                        }
                        ++j ;
                    }
                    --i ;
                    if (i >= 0) {
                        match_used[match_value[i]] = 0 ;
                        j = match_value[i]+1 ;
                        res = _unify_res_copy(int_res[i]) ;
                        goto re_entryc ;
                    } else {
                        return comp ;
                    }
contc:
                    match_used[j] = 1 ;
                    match_value[i] = j ;
                }
                if (comp == NULL) {
                    compl = u_last ;
                } else {
                    u_last->next = comp ;
                }
                comp = res ;
                match_used[j] = 0 ;
                --i ;
                ++j ;
                res = _unify_res_copy(int_res[i]) ;
                goto re_entryc ;
            } else {
               if (p->u.appl.count != e->u.appl.count) return NULL ;
               if (p->u.appl.count > 0) {
                   res = _unify(env,p->u.appl.args[0],e->u.appl.args[0],theta1,theta2) ;
                   for (i = 1; i < p->u.appl.count; ++i) {
                       if (res==NULL) return NULL ;
                       res = _m_unify(env,p->u.appl.args[i],e->u.appl.args[i],res) ;
                   }
                   return res ;
               }
            }
            break ;

        case EXP_INDEX:
            if (e->type != EXP_INDEX) return NULL ;
            if (p->u.index.functor != e->u.index.functor ||
                p->u.index.term != e->u.index.term) return NULL ;
            return _unify(env,p->u.index.exp, e->u.index.exp, theta1, theta2) ;

        case EXP_CASE:
            if (e->type != EXP_CASE) return NULL ;
            if (p->u.case_stmt.count != e->u.case_stmt.count) return NULL ;
            res = _unify(env, p->u.case_stmt.exp, e->u.case_stmt.exp, theta1, theta2) ;
            if (res == NULL) return NULL ;
            for (i = 0; i < p->u.case_stmt.count; ++i) match_used[i] = 0 ;
            if (quant_level >= MAX_QUANT_DEPTH-1) {
                printf("Too many nested quantifiers 7\n") ;
                exit(1) ;
            }
            ++quant_level ;
            for (i = 0; i < p->u.case_stmt.count; ++i) {
                fv = _th_get_free_vars(p->u.case_stmt.args[i*2],&count) ;
                quant_count[quant_level-1] = count ;
                if (count > 0) {
                    quant_stack1[quant_level-1] = (unsigned *)_th_alloc(MATCH_SPACE,count * sizeof(unsigned)) ;
                    quant_stack2[quant_level-1] = (unsigned *)_th_alloc(MATCH_SPACE,count * sizeof(unsigned)) ;
                    quant_assigned[quant_backup][quant_level-1] = (int *)_th_alloc(MATCH_SPACE,count * sizeof(unsigned)) ;
                    for (k = 0; k < count; ++k) {
                        quant_stack1[quant_level-1][k] = fv[k] ;
                        quant_assigned[quant_backup][quant_level-1][k] = 1 ;
                    }
                }
                j = 0 ;
                int_res[i] = _unify_res_copy(res) ;
re_entryca:
                while (j < p->u.case_stmt.count) {
                    if (match_used[j]) {
                        ++j ;
                        continue ;
                    }
#ifdef DEBUG
                    printf("Testing %d %d\n", i, j) ;
#endif
                    if (p->u.case_stmt.args[i*2]==e->u.case_stmt.args[j*2]) {
                        fv = _th_get_free_vars(e->u.case_stmt.args[j*2],&count) ;
                        if (count != quant_count[quant_level-1]) {
                            ++j ;
                            continue ;
                        }
                        for (k = 0; k < count; ++k) {
                            quant_stack2[quant_level-1][k] = fv[k] ;
                        }
#ifdef DEBUG
                        printf("exp: %s\n",
                               _th_print_exp(p->u.case_stmt.args[i*2+1])) ;
                        printf("exp: %s\n",
                               _th_print_exp(e->u.case_stmt.args[j*2+1])) ;
#endif
                        tr = _m_unify(env,p->u.case_stmt.args[i*2+1],
                                      e->u.case_stmt.args[j*2+1],res) ;
                        if (tr != NULL) {
                            res = tr ;
                            goto contca ;
                        }
                    } else if ((u = map_patterns(_th_new_unifier(MATCH_SPACE),
                                                p->u.case_stmt.args[i*2],
                                                e->u.case_stmt.args[j*2]))!=NULL) {
                        fv = _th_get_free_vars(e->u.case_stmt.args[j*2],&count) ;
                        if (count != quant_count[quant_level-1]) {
                            ++j ;
                            continue ;
                        }
                        for (k = 0; k < count; ++k) {
                            quant_stack2[quant_level-1][k] = fv[k] ;
                        }
#ifdef DEBUG
                        printf("exp: %s\n",
                               _th_print_exp(p->u.case_stmt.args[i*2+1])) ;
                        printf("exp: %s\n",
                               _th_print_exp(e->u.case_stmt.args[j*2+1])) ;
#endif
                        tr = _m_unify(env,p->u.case_stmt.args[i*2+1],e->u.case_stmt.args[j*2+1],res) ;
                        if (tr!=NULL) {
                            res = tr ;
                            goto contca ;
                        }
                    }
                    ++j ;
                }
                if (i > 0) {
                    --i ;
                    match_used[match_value[i]] = 0 ;
                    j = match_value[i]+1 ;
                    goto re_entryca ;
                } else {
                    --quant_level ;
                    return NULL ;
                }
contca:
                match_used[j] = 1 ;
                match_value[i] = j ;
            }
            --quant_level ;
            return res ;

        default:
            if (e!=p) return NULL ;

    }
done:
    u_last = (struct unify_return *)_th_alloc(MATCH_SPACE, sizeof(struct unify_return)) ;
    u_last->next = NULL ;
    u_last->theta1 = theta1 ;
    u_last->theta2 = theta2 ;

    return u_last ;
}

struct unify_return *_th_unify(struct env *env,
                               struct _ex_intern *p, struct _ex_intern *e)
{
    quant_level = 0 ;
    quant_backup = 0 ;
    quant_save_count = 0 ;
    quant_stop = 0 ;

    return _unify (env, p, e, _th_new_unifier(MATCH_SPACE),
                              _th_new_unifier(MATCH_SPACE)) ;
}
#endif

struct _ex_unifier *_unify(struct env *env, struct _ex_intern *e1, struct _ex_intern *e2, struct _ex_unifier *u)
{
    struct _ex_intern *old;

    old = NULL;
    while (e1->type==EXP_VAR && e1 != old) {
        old = e1;
        e1 = _th_subst(env,u,e1);
    }
    old = NULL;
    while (e2->type==EXP_VAR && e2 != old) {
        old = e2;
        e2 = _th_subst(env,u,e2);
    }

    if (e1==e2) return u;

    if (e1->type==EXP_VAR) {
        return _th_add_pair(MATCH_SPACE,u,e1->u.var,e2);
    }

    if (e2->type==EXP_VAR) {
        return _th_add_pair(MATCH_SPACE,u,e2->u.var,e1);
    }

    if (e1->type==EXP_APPL && e2->type==EXP_APPL && e1->u.appl.functor==e2->u.appl.functor &&
        e1->u.appl.count==e2->u.appl.count) {

        int i;
        for (i = 0; i < e1->u.appl.count; ++i) {
            u = _unify(env,e1->u.appl.args[i],e2->u.appl.args[i],u);
            if (u==NULL) return NULL;
        }
        return u;
    }

    return NULL;
}

struct match_return *_th_unify(struct env *env, struct _ex_intern *p, struct _ex_intern *e)
{
    struct match_return *mr;
    struct _ex_unifier *theta;
    
    theta = _unify(env, p, e, _th_new_unifier(MATCH_SPACE));

    if (theta != NULL) {
       mr = (struct match_return *)_th_alloc(MATCH_SPACE,sizeof(struct match_return));
       mr->theta = theta;
       mr->next = NULL;
    } else {
       mr = NULL;
    }

    return mr;
}

int _th_more_general(struct _ex_intern *e1, struct _ex_intern *e2)
{
    int i ;
    switch (e1->type) {
        case EXP_VAR:
            return 1 ;
        case EXP_APPL:
            switch (e2->type) {
                case EXP_VAR:
                    return 0 ;
                case EXP_APPL:
                    if (e1->u.appl.functor != e2->u.appl.functor) return 0 ;
                    for (i = 0; i < e1->u.appl.count; ++i) {
                        if (!_th_more_general(e1->u.appl.args[i], e2->u.appl.args[i]))
                            return 0 ;
                    }
                    return 1 ;
                default:
                    return 0 ;
            }
        default:
            return 0;
    }
}

int _th_has_unifier(struct _ex_intern *e1, struct _ex_intern *e2)
{
    int i ;
    switch (e1->type) {
        case EXP_VAR:
            return 1 ;
        case EXP_APPL:
            switch (e2->type) {
                case EXP_VAR:
                    return 1 ;
                case EXP_APPL:
                    if (e1->u.appl.functor != e2->u.appl.functor) return 0 ;
                    for (i = 0; i < e1->u.appl.count; ++i) {
                        if (!_th_has_unifier(e1->u.appl.args[i], e2->u.appl.args[i]))
                            return 0 ;
                    }
                default:
                    return 0 ;
            }
        default:
            return 0;
    }
}

