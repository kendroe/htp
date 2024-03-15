/*
 * search_utils.c
 *
 * Search routines
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
//#include <malloc.h>
#include "Globalsp.h"

static int node_count(struct _ex_intern *e)
{
    int i;
    int count ;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor==INTERN_QUESTION_MARK) return 0 ;
            count = 1 ;
            for (i = 0; i < e->u.appl.count; ++i) {
                count += node_count(e->u.appl.args[i]) ;
            }
            return count ;
        case EXP_QUANT:
            return 1 + node_count(e->u.quant.exp) + node_count(e->u.quant.cond) ;
        case EXP_CASE:
            count = 1 + node_count(e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
                count += node_count(e->u.case_stmt.args[i]) ;
            }
            return count ;
        default:
            return 1 ;
    }
}

int _th_bad_term_count(struct env *env, struct _ex_intern *e, int c, struct _ex_intern **args)
{
    int i;
    int count ;

    _zone_print1("Bad term count %s", _th_print_exp(e)) ;
    _tree_indent() ;
    for (i = 0; i < c; ++i) {
        _zone_print2("args[%d] = %s", i, _th_print_exp(args[i])) ;
        if (e==args[i]) {
            _tree_undent() ;
            return 0 ;
        }
    }

    switch (e->type) {
        case EXP_APPL:
            count = 1 ;
            for (i = 0; i < c; ++i) {
                if (args[i]->type==EXP_APPL && (args[i]->u.appl.functor==e->u.appl.functor || _th_has_smaller_precedence(env,e->u.appl.functor,args[i]->u.appl.functor))) {
                    count = 0 ;
                    break ;
                }
            }
            if (count) _zone_print1("Incrementing for functor %s", _th_intern_decode(e->u.appl.functor)) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                count += _th_bad_term_count(env,e->u.appl.args[i],c,args) ;
            }
            _tree_undent() ;
            return count ;
        case EXP_QUANT:
            count = _th_bad_term_count(env,e->u.quant.exp,c,args) + _th_bad_term_count(env,e->u.quant.cond,c,args) ;
            _tree_undent() ;
            return count ;
        case EXP_CASE:
            count = _th_bad_term_count(env,e->u.case_stmt.exp,c,args) ;
            for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
                count += _th_bad_term_count(env,e->u.case_stmt.args[i],c,args) ;
            }
            _tree_undent() ;
            return count ;
        case EXP_VAR:
            _tree_undent() ;
            return 1 ;
        default:
            _tree_undent() ;
            return 0 ;
    }
}

int _th_all_bad_term_count(struct env *env, struct _ex_intern *p, struct _ex_intern *e)
{
    int i;
    int res ;

    _zone_print1("all bad term count %s", _th_print_exp(p)) ;
    _zone_print1("for expression %s", _th_print_exp(e)) ;
    _tree_indent() ;

    switch (p->type) {
        case EXP_APPL:
            if (p->u.appl.functor==INTERN_QUESTION_MARK) return _th_bad_term_count(env,e, p->u.appl.count, p->u.appl.args) ;
            res = 0 ;
            for (i = 0; i < p->u.appl.count; ++i) {
                res += _th_all_bad_term_count(env,p->u.appl.args[i],e) ;
            }
            _tree_undent() ;
            return res ;
        case EXP_QUANT:
            res = _th_all_bad_term_count(env,p->u.quant.exp,e) + _th_all_bad_term_count(env,p->u.quant.cond,e) ;
            _tree_undent () ;
            return res ;
        case EXP_CASE:
            res = _th_all_bad_term_count(env,p->u.case_stmt.exp, e) ;
            for (i = 0; i < p->u.case_stmt.count * 2; ++i) {
                res += _th_all_bad_term_count(env,p->u.case_stmt.args[i], e) ;
            }
            _tree_undent() ;
            return res ;
        default:
            _tree_undent() ;
            return 0 ;
    }
}

static struct _ex_intern *find_question_mark(struct _ex_intern *e)
{
    int i ;
    struct _ex_intern *r ;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor==INTERN_QUESTION_MARK) return e ;
            for (i = 0; i < e->u.appl.count; ++i) {
                r = find_question_mark(e->u.appl.args[i]) ;
                if (r != NULL) return r ;
            }
            return NULL ;
        case EXP_QUANT:
            r = find_question_mark(e->u.quant.exp) ;
            if (r != NULL) return r ;
            return find_question_mark(e->u.quant.cond) ;
        case EXP_CASE:
            r = find_question_mark(e->u.case_stmt.exp) ;
            if (r != NULL) return r ;
            for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
                r = find_question_mark(e->u.case_stmt.args[i]) ;
                if (r != NULL) return r ;
            }
            /* Fall to default case */
        default:
            return NULL ;
    }
}

int _th_distance(struct env *env, struct _ex_intern *pat, struct _ex_intern *exp)
{
    int i;
    int res ;

    if (pat->type==EXP_APPL && pat->u.appl.functor == INTERN_QUESTION_MARK) return _th_bad_term_count(env,exp, pat->u.appl.count, pat->u.appl.args) ;
    if (pat->type != exp->type) return node_count(pat) + _th_all_bad_term_count(env, pat, exp) ;

    switch (pat->type) {
        case EXP_APPL:
            if (exp->u.appl.functor != pat->u.appl.functor || exp->u.appl.count != pat->u.appl.count) return node_count(pat) + _th_all_bad_term_count(env, pat, exp) ;
            res = 0 ;
            for (i = 0; i < exp->u.appl.count; ++i) {
                res += _th_distance(env, pat->u.appl.args[i], exp->u.appl.args[i]) ;
            }
            return res ;
        case EXP_QUANT:
            if (exp->u.quant.quant != pat->u.quant.quant) return node_count(pat) + _th_all_bad_term_count(env, pat, exp) ;
            return _th_distance(env, pat->u.quant.exp, exp->u.quant.exp) +
                   _th_distance(env, pat->u.quant.cond, exp->u.quant.cond) ;
        case EXP_CASE:
            if (exp->u.case_stmt.count != pat->u.case_stmt.count) return node_count(pat) + _th_all_bad_term_count(env, pat, exp) ;
            res = _th_distance(env, pat->u.case_stmt.exp, exp->u.case_stmt.exp) ;
            for (i = 0; i < exp->u.case_stmt.count*2; ++i) {
                res += _th_distance(env, pat->u.case_stmt.args[i], exp->u.case_stmt.args[i]) ;
            }
            return res ;
        default:
            return (exp==pat)?0:1 ;
    }
}

void _th_best_order(struct env *env, int functor, int count, struct _ex_intern **pargs, struct _ex_intern **args, int *order)
{
    int i, j, x ;

    for (i = 0; i < count; ++i) order[i] = i ;

    if (!_th_is_ac(env,functor) && !_th_is_c(env,functor)) return ;

    for (i = 0; i < count; ++i) {
        for (j = i+1; j < count; ++j) {
            if (_th_compare_match(env,pargs[i],args[order[i]],args[order[j]])==1) {
                x = order[i] ;
                order[i] = order[j] ;
                order[j] = x ;
            }
        }
    }
}

int _th_compare_match(struct env *env, struct _ex_intern *pat, struct _ex_intern *exp1, struct _ex_intern *exp2)
{
    int i;
    int res, res1 ;
    int *order1, *order2 ;

    if (pat->type==EXP_APPL && pat->u.appl.functor == INTERN_QUESTION_MARK) return 0 ;

    if (pat->type != exp1->type && pat->type != exp2->type) return 0 ;

    if (pat->type != exp1->type) {
        switch (pat->type) {
            case EXP_APPL:
                if (pat->u.appl.functor != exp2->u.appl.functor || pat->u.appl.count != exp2->u.appl.count) {
                    return 0 ;
                } else {
                    return 1 ;
                }
            case EXP_QUANT:
                if (pat->u.quant.quant != exp2->u.quant.quant) {
                    return 0 ;
                } else {
                    return 1 ;
                }
            case EXP_CASE:
                if (pat->u.case_stmt.count != exp2->u.case_stmt.count) {
                    return 0 ;
                } else {
                    return 1 ;
                }
            default:
                return 1 ;
        }
    }

    if (pat->type != exp2->type) {
        switch (pat->type) {
            case EXP_APPL:
                if (pat->u.appl.functor != exp1->u.appl.functor || pat->u.appl.count != exp1->u.appl.count) {
                    return 0 ;
                } else {
                    return -1 ;
                }
            case EXP_QUANT:
                if (pat->u.quant.quant != exp1->u.quant.quant) {
                    return 0 ;
                } else {
                    return -1 ;
                }
            case EXP_CASE:
                if (pat->u.case_stmt.count != exp1->u.case_stmt.count) {
                    return 0 ;
                } else {
                    return -1 ;
                }
            default:
                return -1 ;
        }
    }

    switch (pat->type) {

        case EXP_APPL:
            if (exp1->u.appl.functor != pat->u.appl.functor || exp1->u.appl.count != pat->u.appl.count) {
                if (exp2->u.appl.functor != pat->u.appl.functor || exp2->u.appl.count != pat->u.appl.count) {
                    return 0 ;
                } else {
                    return 1 ;
                }
            } else {
                if (exp2->u.appl.functor != pat->u.appl.functor || exp2->u.appl.count != pat->u.appl.count) {
                    return -1 ;
                } else {
                    return 0 ;
                }
            }
            res = 0 ;
            order1 = (int *)ALLOCA(sizeof(int) * pat->u.appl.count) ;
            order2 = (int *)ALLOCA(sizeof(int) * pat->u.appl.count) ;
            _th_best_order(env,pat->u.appl.functor,pat->u.appl.count,pat->u.appl.args,exp1->u.appl.args,order1) ;
            _th_best_order(env,pat->u.appl.functor,pat->u.appl.count,pat->u.appl.args,exp2->u.appl.args,order2) ;
            for (i = 0; i < pat->u.appl.count; ++i) {
                res1 = _th_compare_match(env, pat->u.appl.args[i], exp1->u.appl.args[order1[i]], exp2->u.appl.args[order2[i]]) ;
                if (res1==0x80000000) {
                    return 0x80000000 ;
                } else if (res==0) {
                    res = res1 ;
                } else if (res1 != 0 && res != res1) {
                    return 0x80000000 ;
                }
            }
            return res ;

        case EXP_QUANT:
            if (exp1->u.quant.quant != pat->u.quant.quant) {
                if (exp2->u.quant.quant != pat->u.quant.quant) {
                    return 0 ;
                } else {
                    return 1 ;
                }
            } else {
                if (exp2->u.quant.quant != pat->u.quant.quant) {
                    return -1 ;
                } else {
                    return 0 ;
                }
            }
            res = _th_compare_match(env, pat->u.quant.exp, exp1->u.quant.exp, exp2->u.quant.exp) ;
            res1 = _th_compare_match(env, pat->u.quant.cond, exp1->u.quant.cond, exp2->u.quant.cond) ;
            if (res1==0x80000000 || res==0 ) {
                return res1 ;
            } else if (res1 != 0 && res != res1) {
                return 0x80000000 ;
            }
            return res ;

        case EXP_CASE:
            if (exp1->u.case_stmt.count != pat->u.case_stmt.count) {
                if (exp2->u.case_stmt.count != pat->u.case_stmt.count) {
                    return 0 ;
                } else {
                    return 1 ;
                }
            } else {
                if (exp2->u.case_stmt.count != pat->u.case_stmt.count) {
                    return -1 ;
                } else {
                    return 0 ;
                }
            }

            res = _th_compare_match(env, pat->u.case_stmt.exp, exp1->u.case_stmt.exp, exp2->u.case_stmt.exp) ;
            for (i = 0; i < pat->u.case_stmt.count*2; ++i) {
                res1 = _th_compare_match(env, pat->u.case_stmt.args[i], exp1->u.case_stmt.args[i], exp2->u.case_stmt.args[i]) ;
                if (res1==0x80000000) {
                    return 0x80000000 ;
                } else if (res==0) {
                    res = res1 ;
                } else if (res1 != 0 && res != res1) {
                    return 0x80000000 ;
                }
            }
            return res ;

        default:
            if (pat != exp1 && pat != exp2) return 0 ;
            if (pat != exp1) return 1 ;
            if (pat != exp2) return -1 ;
            return 0 ;
    }
}

