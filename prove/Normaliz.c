/*
 * normalize.c
 *
 * Search routines
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include "Globalsp.h"

struct _ex_intern *top_step(struct env *env, struct _ex_intern *pat, struct _ex_intern *exp)
{
    int i ;
    struct _ex_intern **args ;
    struct _ex_intern *e ;
    int *order ;

    _zone_print1("Top step %s", _th_print_exp(exp)) ;
    _tree_indent() ;
    _zone_print1("pat %s", _th_print_exp(pat)) ;
    if (pat->type==EXP_APPL && pat->u.appl.functor==INTERN_QUESTION_MARK || exp==pat) {
        _tree_undent() ;
        return exp ;
    }

    switch (pat->type) {

        case EXP_APPL:
            if (exp->type != EXP_APPL ||
                exp->u.appl.functor != pat->u.appl.functor ||
                exp->u.appl.count != pat->u.appl.count) goto try_to_improve ;
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count) ;
            order = (int *)ALLOCA(sizeof(int) * exp->u.appl.count) ;
            _th_best_order(env, pat->u.appl.functor, pat->u.appl.count, pat->u.appl.args,exp->u.appl.args,order) ;
            for (i = 0; i < exp->u.appl.count; ++i) {
                args[i] = top_step(env, pat->u.appl.args[i], exp->u.appl.args[order[i]]) ;
                if (args[i]==NULL) goto try_to_improve ;
                if (args[i] != exp->u.appl.args[order[i]]) {
                    while (++i < exp->u.appl.count) {
                        args[i] = exp->u.appl.args[order[i]] ;
                    }
                    exp = _ex_intern_appl_env(env,exp->u.appl.functor,exp->u.appl.count,args) ;
                    _tree_undent() ;
                    _zone_print1("Result = %s", _th_print_exp(exp)) ;
                    return exp ;
                }
            }
            _tree_undent() ;
            return exp ;

        case EXP_QUANT:
            if (exp->u.quant.quant != pat->u.quant.quant) goto try_to_improve ;
            e = top_step(env, pat->u.quant.exp, exp->u.quant.exp) ;
            if (e==NULL) goto try_to_improve ;
            if (e != exp->u.quant.exp) {
                exp = _ex_intern_quant(exp->u.quant.quant,exp->u.quant.var_count,exp->u.quant.vars,e,exp->u.quant.cond) ;
                _tree_undent() ;
                _zone_print1("Result %s", _th_print_exp(exp)) ;
                return exp ;
            }
            e = top_step(env, pat->u.quant.cond, exp->u.quant.cond) ;
            if (e==NULL) goto try_to_improve ;
            if (e != exp->u.quant.cond) {
                exp = _ex_intern_quant(exp->u.quant.quant,exp->u.quant.var_count,exp->u.quant.vars,exp->u.quant.exp,e) ;
                _tree_undent() ;
                _zone_print1("Result %s", _th_print_exp(exp)) ;
                return exp ;
            }
            _tree_undent() ;
            return exp ;

        case EXP_CASE:
            if (exp->u.case_stmt.count != pat->u.case_stmt.count) goto try_to_improve ;
            e = top_step(env, pat->u.case_stmt.exp, exp->u.case_stmt.exp) ;
            if (e==NULL) goto try_to_improve ;
            if (e != exp->u.case_stmt.exp) {
                exp = _ex_intern_case(e,exp->u.case_stmt.count,exp->u.case_stmt.args) ;
                _tree_undent() ;
                _zone_print1("Result %s", _th_print_exp(exp)) ;
                return exp ;
            }
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.case_stmt.count*2) ;
            for (i = 0; i < exp->u.case_stmt.count*2; ++i) {
                args[i] = top_step(env, pat->u.case_stmt.args[i], exp->u.case_stmt.args[i]) ;
                if (args[i]==NULL) goto try_to_improve ;
                if (args[i] != exp->u.case_stmt.args[i]) {
                    while (++i < exp->u.case_stmt.count) {
                        args[i] = exp->u.case_stmt.args[i] ;
                    }
                    exp = _ex_intern_case(exp->u.case_stmt.exp,exp->u.case_stmt.count,args) ;
                    _tree_undent() ;
                    _zone_print1("Result %s", _th_print_exp(exp)) ;
                    return exp ;
                }
            }
            _tree_undent() ;
            return exp ;
    }

try_to_improve:
    _th_special_rewrite_rule(SEARCH_SPACE, env, exp, 0, NULL) ;
    for (i = 0; i < _th_possibility_count; ++i) {
        if (_th_compare_match(env,pat,exp,_th_possible_rewrites[i])==1) {
            exp = _th_possible_rewrites[i] ;
            _tree_undent() ;
            _zone_print1("Result %s", _th_print_exp(exp)) ;
            return exp ;
        }
    }
    _tree_undent() ;
    return NULL ;

}

struct _ex_intern *bottom_fix(struct env *env, struct _ex_intern *exp, int count, struct _ex_intern **parms)
{
    int i, c, c2 ;
    struct _ex_intern **args ;
    struct _ex_intern *e, *f ;

    _zone_print1("Bottom fix %s", _th_print_exp(exp)) ;
    _tree_indent() ;
    for (i = 0; i < count; ++i) {
        _zone_print2("parameter %d %s", i, _th_print_exp(parms[i])) ;
        if (exp==parms[i]) {
            _tree_undent() ;
            return exp ;
        }
    }

    c = _th_bad_term_count(env,exp,count,parms) ;
    if (c==0) {
        _tree_undent() ;
        return exp ;
    }

    switch (exp->type) {
        
    case EXP_APPL:
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count) ;
        for (i = 0; i < exp->u.appl.count; ++i) {
            args[i] = bottom_fix(env, exp->u.appl.args[i], count, parms) ;
        }
        exp = _ex_intern_appl_env(env,exp->u.appl.functor,exp->u.appl.count,args) ;
        break ;
        
    case EXP_QUANT:
        e = bottom_fix(env, exp->u.quant.exp, count, parms) ;
        f = bottom_fix(env, exp->u.quant.cond, count, parms) ;
        exp = _ex_intern_quant(exp->u.quant.quant,exp->u.quant.var_count,exp->u.quant.vars,exp->u.quant.exp,e) ;
        break ;
        
    case EXP_CASE:
        e = bottom_fix(env, exp->u.case_stmt.exp, count, parms) ;
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.case_stmt.count*2) ;
        for (i = 0; i < exp->u.case_stmt.count*2; ++i) {
            args[i] = bottom_fix(env, exp->u.case_stmt.args[i], count, parms) ;
        }
        exp = _ex_intern_case(exp->u.case_stmt.exp,exp->u.case_stmt.count,args) ;
        break ;
    }

    _zone_print1("Subterm rewrites %s", _th_print_exp(exp)) ;

    c = _th_bad_term_count(env,exp,count,parms) ;
    if (c==0) {
        _tree_undent() ;
        return exp ;
    }

    _th_special_rewrite_rule(SEARCH_SPACE, env, exp, 0, NULL) ;

    for (i = 0; i < _th_possibility_count; ++i) {
        c2 = _th_bad_term_count(env,_th_possible_rewrites[i],count,parms) ;
        if (c > c2) {
            _zone_print1("Rewrite to %s", _th_print_exp(_th_possible_rewrites[i])) ;
            exp = _th_possible_rewrites[i] ;
            _tree_undent() ;
            return exp ;
        }
    }

    _tree_undent() ;
    return exp ;
}

struct _ex_intern *bottom_step(struct env *env, struct _ex_intern *pat, struct _ex_intern *exp)
{
    int i ;
    struct _ex_intern **args ;
    struct _ex_intern *e ;
    int *order ;

    if (pat->type==EXP_APPL && pat->u.appl.functor==INTERN_QUESTION_MARK) return bottom_fix(env, exp, pat->u.appl.count, pat->u.appl.args) ;

    switch (pat->type) {

        case EXP_APPL:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.appl.count) ;
            order = (int *)ALLOCA(sizeof(int) * exp->u.appl.count) ;
            _th_best_order(env, pat->u.appl.functor, pat->u.appl.count, pat->u.appl.args,exp->u.appl.args,order) ;
            for (i = 0; i < exp->u.appl.count; ++i) {
                args[i] = bottom_step(env, pat->u.appl.args[i], exp->u.appl.args[order[i]]) ;
                if (args[i]==NULL) goto try_to_improve ;
                if (args[i] != exp->u.appl.args[order[i]]) {
                    while (++i < exp->u.appl.count) {
                        args[i] = exp->u.appl.args[order[i]] ;
                    }
                    return _ex_intern_appl_env(env,exp->u.appl.functor,exp->u.appl.count,args) ;
                }
            }
            return exp ;

        case EXP_QUANT:
            e = bottom_step(env, pat->u.quant.exp, exp->u.quant.exp) ;
            if (e==NULL) goto try_to_improve ;
            if (e != exp->u.quant.exp) {
                return _ex_intern_quant(exp->u.quant.quant,exp->u.quant.var_count,exp->u.quant.vars,e,exp->u.quant.cond) ;
            }
            e = bottom_step(env, pat->u.quant.cond, exp->u.quant.cond) ;
            if (e==NULL) goto try_to_improve ;
            if (e != exp->u.quant.cond) {
                return _ex_intern_quant(exp->u.quant.quant,exp->u.quant.var_count,exp->u.quant.vars,exp->u.quant.exp,e) ;
            }
            return exp ;

        case EXP_CASE:
            e = bottom_step(env, pat->u.case_stmt.exp, exp->u.case_stmt.exp) ;
            if (e==NULL) goto try_to_improve ;
            if (e != exp->u.case_stmt.exp) {
                return _ex_intern_case(e,exp->u.case_stmt.count,exp->u.case_stmt.args) ;
            }
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * exp->u.case_stmt.count*2) ;
            for (i = 0; i < exp->u.case_stmt.count*2; ++i) {
                args[i] = bottom_step(env, pat->u.case_stmt.args[i], exp->u.case_stmt.args[i]) ;
                if (args[i]==NULL) goto try_to_improve ;
                if (args[i] != exp->u.case_stmt.args[i]) {
                    while (++i < exp->u.case_stmt.count) {
                        args[i] = exp->u.case_stmt.args[i] ;
                    }
                    return _ex_intern_case(exp->u.case_stmt.exp,exp->u.case_stmt.count,args) ;
                }
            }
            /* Fall through */
        default:
            return exp ;
    }

try_to_improve:
    _th_special_rewrite_rule(SEARCH_SPACE, env, exp, 0, NULL) ;
    for (i = 0; i < _th_possibility_count; ++i) {
        if (_th_all_bad_term_count(env,pat,exp) > _th_all_bad_term_count(env, pat,_th_possible_rewrites[i])) return _th_possible_rewrites[i] ;
    }
    return NULL ;

}

int _th_complete_solution ;

struct _ex_intern *_th_normalize(struct env *env, struct _ex_intern *pat, struct _ex_intern *exp)
{
    struct _ex_intern *e ;
    int cm ;

    _zone_print1("Normalizing %s", _th_print_exp(exp)) ;
    _zone_print1("with pattern %s", _th_print_exp(pat)) ;
    _tree_indent() ;
    _th_complete_solution = 1 ;
    if (_th_distance(env,pat,exp)==0) {
        _tree_undent() ;
        _zone_print1("Result %s", _th_print_exp(exp)) ;
        return exp ;
    }
    e = top_step(env, pat, exp) ;
    if (e != NULL && _th_distance(env,pat,e)==0) {
        _tree_undent() ;
        _zone_print1("Result %s", _th_print_exp(e)) ;
        return e;
    }
    while (e != NULL && e != exp) {
        exp = e ;
        e = _th_rewrite(env, exp) ;
        if (e==NULL) {
            e = exp ;
        } else {
            if (_th_distance(env,pat,e)==0) {
                _tree_undent() ;
                _zone_print1("Result %s", _th_print_exp(e)) ;
                return e;
            }
            cm = _th_compare_match(env, pat, exp, e) ;
            if (cm==-1 || cm==0x80000000) e = exp ;
        }
        e = top_step(env, pat, exp) ;
        if (e != NULL && _th_distance(env,pat,e)==0) {
            _tree_undent() ;
            _zone_print1("Result %s", _th_print_exp(e)) ;
            return e;
        }
    }
    if (e==NULL) {
        _th_complete_solution = !_th_distance(env,pat,exp) ;
        _tree_undent() ;
        if (_th_complete_solution) {
            _zone_print1("Result %s", _th_print_exp(exp)) ;
        } else {
            _zone_print1("Incomplete result %s", _th_print_exp(exp)) ;
        }
        return exp ;
    }
    e = _th_rewrite(env, exp) ;
    if (e==NULL) {
        e = exp ;
    } else {
        if (_th_distance(env,pat,e)==0) {
            _tree_undent() ;
            _zone_print1("Result %s", _th_print_exp(e)) ;
            return e;
        }
        cm = _th_compare_match(env, pat, exp, e) ;
        if (cm!=-1 && cm!=0x80000000) exp = e ;
    }

    e = bottom_step(env, pat, exp) ;
    if (e != NULL && _th_distance(env,pat,e)==0) {
        _tree_undent() ;
        _zone_print1("Result %s", _th_print_exp(e)) ;
        return e;
    }
    while (e != NULL && e != exp) {
        exp = e ;
        e = _th_rewrite(env, exp) ;
        if (e==NULL) {
            e = exp ;
        } else {
            int x, y ;
            if ((x = _th_distance(env, pat, exp)) < (y = _th_distance(env, pat, e))) {
                e = exp ;
                y = x ;
            }
            if (x==0) {
                _tree_undent() ;
                _zone_print1("Result %s", _th_print_exp(e)) ;
                return e;
            }
        }
        e = bottom_step(env, pat, exp) ;
        if (e != NULL && _th_distance(env,pat,e)==0) {
            _tree_undent() ;
            _zone_print1("Result %s", _th_print_exp(e)) ;
            return e;
        }
    }
    if (e==NULL) {
        _th_complete_solution = !_th_distance(env,pat,exp) ;
        _tree_undent() ;
        if (_th_complete_solution) {
            _zone_print1("Result %s", _th_print_exp(exp)) ;
        } else {
            _zone_print1("Incomplete result %s", _th_print_exp(exp)) ;
        }
        return exp ;
    }
    e = _th_rewrite(env, exp) ;
    if (e==NULL) {
        e = exp ;
    } else if (_th_distance(env, pat, exp) >= _th_distance(env, pat, e)) {
        exp = e ;
    }

    _th_complete_solution = !_th_distance(env, pat, exp) ;
    _tree_undent() ;
    if (_th_complete_solution) {
        _zone_print1("Result %s", _th_print_exp(exp)) ;
    } else {
        _zone_print1("Incomplete result %s", _th_print_exp(exp)) ;
    }
    return exp ;
}

