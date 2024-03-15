/*
 * builtin.c
 *
 * Special handling for builtin operators
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"

struct rule {
    struct rule *next ;
    struct _ex_intern *rule ;
} ;

#define MAX_NESTING_LEVELS 20

static int has_bound_var(struct _ex_intern *m_rule)
{
   int count ;
   unsigned *fv = _th_get_marked_vars(m_rule->u.appl.args[0],&count) ;
   int i ;

   for (i = 0; i < count; ++i) {
       if (_th_intern_get_data2(fv[i])) return 1 ;
   }

   return 0 ;
}

static int is_header_term(struct _ex_intern *t)
{
    if (t->type != EXP_APPL) return 0 ;
    if (t->u.appl.count != 1) return 0 ;
    return t->u.appl.functor==INTERN_IN_CONTEXT ||
           t->u.appl.functor==INTERN_BLOCK_CONTEXT ||
           t->u.appl.functor==INTERN_USE_CONTEXT ||
           t->u.appl.functor==INTERN_APPLY_CONTEXT ||
           t->u.appl.functor==INTERN_EXCLUDE_SET ;
}

static struct _ex_intern *combine_conditions(struct env *env, struct _ex_intern *e1, struct _ex_intern *e2)
{
    int i, j, k ;

    if (e1->type==EXP_APPL && (e1->u.appl.functor==INTERN_NC_AND || e1->u.appl.functor==INTERN_ANDQ)) {
        if (e2->type==EXP_APPL && (e2->u.appl.functor==INTERN_NC_AND || e2->u.appl.functor==INTERN_ANDQ)) {
            struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern **) * (e1->u.appl.count+e2->u.appl.count)) ;
            k = 0 ;
            for (i = 0; i < e1->u.appl.count; ++i) {
                if (!is_header_term(e1->u.appl.args[i])) break ;
                args[k++] = e1->u.appl.args[i] ;
            }
            for (j = 0; j < e2->u.appl.count; ++j) {
                if (!is_header_term(e1->u.appl.args[j])) break ;
                args[k++] = e2->u.appl.args[j] ;
            }
            while (i < e1->u.appl.count) {
                args[k++] = e1->u.appl.args[i] ;
                ++i ;
            }
            while (j < e2->u.appl.count) {
                args[k++] = e2->u.appl.args[j] ;
                ++i ;
            }
            if (e1->u.appl.functor==INTERN_NC_AND && e2->u.appl.functor==INTERN_NC_AND) {
                return _ex_intern_appl_env(env,INTERN_NC_AND,e1->u.appl.count+e2->u.appl.count,args) ;
            } else {
                return _ex_intern_appl_env(env,INTERN_ANDQ,e1->u.appl.count+e2->u.appl.count,args) ;
            }
        } else {
            struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern **) * (e1->u.appl.count+1)) ;
            for (i = 0; i < e1->u.appl.count; ++i) {
                args[i] = e1->u.appl.args[i] ;
            }
            args[i++] = e2 ;
            return _ex_intern_appl_env(env,e1->u.appl.functor,i,args) ;
        }
    } else {
        if (e2->type==EXP_APPL && (e2->u.appl.functor==INTERN_NC_AND || e2->u.appl.functor==INTERN_ANDQ)) {
            struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern **) * (e2->u.appl.count+1)) ;
            for (i = 0; i < e2->u.appl.count; ++i) {
                args[i] = e2->u.appl.args[i] ;
            }
            args[i++] = e1 ;
            return _ex_intern_appl_env(env,e2->u.appl.functor,i,args) ;
        } else {
            return _ex_intern_appl2_env(env,INTERN_AND,e1,e2) ;
        }
    }
}

static struct rule *add_matches(struct env *env, struct rule *rules, struct _ex_intern *lhs, struct _ex_intern *c_rule, struct _ex_intern *m_rule, unsigned count, unsigned *subterm)
{
    char *mark = _th_alloc_mark(MATCH_SPACE) ;
    struct match_return *match ;
    int i ;

    if (lhs->type==EXP_VAR) return rules ;

    match = _th_match(env, lhs, m_rule->u.appl.args[0]) ;
    while (match) {
        struct _ex_intern *e = _th_subst(env,match->theta,c_rule) ;
        //struct _ex_intern *cond ;
        struct rule *new_rule ;
        e = _th_replace_term(env,e,count,subterm,m_rule->u.appl.args[1]) ;
        //cond = combine_conditions(env,m_rule->u.appl.args[2],e->u.appl.args[2]) ;
        new_rule = (struct rule *)_th_alloc(REWRITE_SPACE,sizeof(struct rule)) ;
        new_rule->next = rules ;
        new_rule->rule = e ;
        rules = new_rule ;
        match = match->next ;
    }

    _th_alloc_release(MATCH_SPACE,mark) ;

    if (count >= MAX_NESTING_LEVELS) return rules ;

    switch (lhs->type) {
    case EXP_APPL:
        for (i = 0; i < lhs->u.appl.count; ++i) {
            subterm[count] = i ;
            rules = add_matches(env,rules,lhs->u.appl.args[i],c_rule,m_rule,count+1,subterm) ;
        }
        break ;
    case EXP_QUANT:
        for (i = 0; i < lhs->u.quant.var_count; ++i) {
            _th_intern_set_data2(lhs->u.quant.vars[i],_th_intern_get_data2(lhs->u.quant.vars[i])+1) ;
        }
        if (!has_bound_var(m_rule)) {
            subterm[count] = 0 ;
            rules = add_matches(env,rules,lhs->u.quant.exp,c_rule,m_rule,count+1,subterm) ;
            subterm[count] = 1 ;
            rules = add_matches(env,rules,lhs->u.quant.cond,c_rule,m_rule,count+1,subterm) ;
        }
        for (i = 0; i < lhs->u.quant.var_count; ++i) {
            _th_intern_set_data2(lhs->u.quant.vars[i],_th_intern_get_data2(lhs->u.quant.vars[i])-1) ;
        }
        break ;
    case EXP_CASE:
        subterm[count] = 0 ;
        rules = add_matches(env,rules,lhs->u.case_stmt.exp,c_rule,m_rule,count+1,subterm) ;
        for (i = 1; i < lhs->u.case_stmt.count * 2; i += 2) {
            _th_increment_var_data2(lhs->u.case_stmt.args[i-1]) ;
            if (!has_bound_var(m_rule)) {
                subterm[count] = i ;
                rules = add_matches(env,rules,lhs->u.case_stmt.args[i],c_rule,m_rule,count+1,subterm) ;
            }
            _th_decrement_var_data2(lhs->u.case_stmt.args[i-1]) ;
        }
        break ;
    }

    return rules ;

}

static struct _ex_intern *kb_set(struct env *env, struct _ex_intern *rule)
{
    struct rule *rules = NULL, *r ;
    char *c = _th_alloc_mark(REWRITE_SPACE) ;
    struct _ex_intern **args ;
	struct rule *cr;
    struct _ex_intern *e = _th_get_first_rule(env, &cr) ;
    unsigned subterm[MAX_NESTING_LEVELS] ;
    int i ;

    while (e) {
        if (e != rule) {
            rules = add_matches(env,rules,e->u.appl.args[0],rule,e,0,subterm) ;
        }
        e = _th_get_next_rule(env, &cr) ;
    }

    i = 0 ;
    r = rules ;
    while (r) {
        ++i ;
        r = r->next ;
    }

    args = ALLOCA(i * sizeof(struct _ex_intern *)) ;

    i = 0 ;
    r = rules ;
    while (r) {
        args[i++] = r->rule ;
        r = r->next ;
    }

    e =  _ex_intern_appl_env(env,INTERN_SET,i,args) ;
    _th_alloc_release(REWRITE_SPACE,c) ;
    return e ;
}

static int _find_integer(struct env *env, struct _ex_intern *e)
{
    int i ;

    for (i = 0; i < e->u.appl.count; ++i) {
        if (e->u.appl.args[i]->type == EXP_INTEGER) return i ;
    }
    return -1 ;
}

static struct _ex_intern *unc(struct env *env, unsigned v, struct _ex_intern *l1, struct _ex_intern *l2)
{
    int i ;
    struct _ex_intern **args, *e, *f ;

    if (_th_equal(env,l1,l2)) return _ex_intern_var(v) ;

    switch (l1->type) {
    case EXP_VAR:
        if (l1->u.var==v) return NULL ;
        return l1 ;
    case EXP_QUANT:
        for (i = 0; i < l1->u.quant.var_count; ++i) {
            if (l1->u.quant.vars[i]==v) return l1 ;
        }
        e = unc(env,v,l1->u.quant.exp,l2) ;
        f = unc(env,v,l1->u.quant.cond,l2) ;
        if (e==NULL || f==NULL) return NULL ;
        return _ex_intern_quant(l1->u.quant.quant,l1->u.quant.var_count,l1->u.quant.vars,e,f) ;
    case EXP_APPL:
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * l1->u.appl.count) ;
        for (i = 0; i < l1->u.appl.count; ++i) {
            e = unc(env,v,l1->u.appl.args[i],l2) ;
            if (e==NULL) return NULL ;
            args[i] = e ;
        }
        return _ex_intern_appl_env(env,l1->u.appl.functor,l1->u.appl.count,args) ;
    case EXP_CASE:
        e = unc(env,v,l1->u.case_stmt.exp,l2) ;
        if (e==NULL) return NULL ;
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * l1->u.case_stmt.count * 2) ;
        for (i = 0; i < l1->u.case_stmt.count; ++i) {
            if (_th_is_free_in(l1->u.case_stmt.args[i],v)) {
                args[i*2] = l1->u.case_stmt.args[i*2] ;
                args[i*2+1] = l1->u.case_stmt.args[i*2+1] ;
            } else {
                args[i*2] = l1->u.case_stmt.args[i*2] ;
                e = unc(env,v,l1->u.case_stmt.args[i*2+1],l2) ;
                if (e==NULL) return NULL ;
                args[i*2+1] = e ;
            }
        }
        return _ex_intern_case(e,l1->u.case_stmt.count,args) ;
    default:
        return l1 ;
    }
}

static struct _ex_intern *uncompose(struct env *env, unsigned v1, struct _ex_intern *l1, unsigned v2, struct _ex_intern *l2)
{
    char *mark = _th_alloc_mark(MATCH_SPACE) ;
    struct _ex_unifier *u = _th_new_unifier(MATCH_SPACE) ;
    u = _th_add_pair(MATCH_SPACE,u,v2,_ex_intern_var(v1)) ;
    l2 = _th_subst(env,u,l2) ;
    
    l1 = unc(env,v1,l1,l2) ;

    _th_alloc_release(MATCH_SPACE, mark) ;

    return l1 ;
}

static int subterm_member(struct env *env, struct _ex_intern *e, struct _ex_intern *f)
{
    if (_th_equal(env,e,f)) return 1 ;
    if (f->type == EXP_APPL && _th_is_constructor(env,f->u.appl.functor)) {
        int i ;
        for (i = 0; i < f->u.appl.count; ++i) {
            if (subterm_member(env,e,f->u.appl.args[i])) return 1 ;
        }
    }
    return 0 ;
}

#ifdef XX
static struct _ex_intern **args = NULL, **args2 = NULL;
static struct _ex_unifier **unifiers = NULL ;
static unsigned arg_size = 0 ;

#define ARG_INCREMENT 4000

static void check_size(unsigned size)
{
    if (size > arg_size) {
        arg_size = size + ARG_INCREMENT ;
        args = (struct _ex_intern **)REALLOC(args,sizeof(struct _ex_intern *) * arg_size) ;
        args2 = (struct _ex_intern **)REALLOC(args2,sizeof(struct _ex_intern *) * arg_size) ;
        unifiers = (struct _ex_unifier **)REALLOC(unifiers,sizeof(struct _ex_unifier *) * arg_size) ;
    }
}
#endif

int test_match_closure(struct env *env, struct _ex_intern *e, int pat_count, struct _ex_intern **patterns)
{
    int i ;
    char *mark = _th_alloc_mark(MATCH_SPACE) ;
    for (i = 0; i < pat_count; ++i) {
        if (_th_match(env, patterns[i], e) != NULL) goto true_return ;
    }

    switch(e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                if (test_match_closure(env,e->u.appl.args[i],pat_count,patterns)) goto true_return ;
            }
            break ;
        case EXP_CASE:
            if (test_match_closure(env,e->u.case_stmt.exp,pat_count,patterns)) goto true_return ;
            for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
                if (test_match_closure(env,e->u.case_stmt.exp,pat_count,patterns)) goto true_return ;
            }
            break ;
        case EXP_QUANT:
            if (test_match_closure(env,e->u.quant.exp,pat_count,patterns)) goto true_return ;
            if (test_match_closure(env,e->u.quant.cond,pat_count,patterns)) goto true_return ;
            break ;
        case EXP_INDEX:
            if (test_match_closure(env,e->u.index.exp,pat_count,patterns)) goto true_return ;
            break ;
    }
    _th_alloc_release(MATCH_SPACE,mark) ;
    return 0 ;
true_return:
    _th_alloc_release(MATCH_SPACE,mark) ;
    return 1 ;
}

struct _ex_intern *first_match_closure(struct env *env, struct _ex_intern *e, int pat_count, struct _ex_intern **patterns)
{
    int i ;
    char *mark = _th_alloc_mark(MATCH_SPACE) ;
    for (i = 0; i < pat_count; ++i) {
        if (_th_match(env, patterns[i], e) != NULL) goto true_return ;
    }

    switch(e->type) {
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                if (test_match_closure(env,e->u.appl.args[i],pat_count,patterns)) goto true_return ;
            }
            break ;
        case EXP_CASE:
            if (test_match_closure(env,e->u.case_stmt.exp,pat_count,patterns)) goto true_return ;
            for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
                if (test_match_closure(env,e->u.case_stmt.exp,pat_count,patterns)) goto true_return ;
            }
            break ;
        case EXP_QUANT:
            if (test_match_closure(env,e->u.quant.exp,pat_count,patterns)) goto true_return ;
            if (test_match_closure(env,e->u.quant.cond,pat_count,patterns)) goto true_return ;
            break ;
        case EXP_INDEX:
            if (test_match_closure(env,e->u.index.exp,pat_count,patterns)) goto true_return ;
            break ;
    }
    _th_alloc_release(MATCH_SPACE,mark) ;
    return NULL ;
true_return:
    _th_alloc_release(MATCH_SPACE,mark) ;
    return e ;
}

struct _ex_intern *match_closure(struct env *env, struct _ex_intern *e, int pat_count, struct _ex_intern **patterns)
{
    int i ;
    char *mark = _th_alloc_mark(MATCH_SPACE) ;
	struct _ex_intern *r, *s ;

    for (i = 0; i < pat_count; ++i) {
        if (_th_match(env, patterns[i], e) != NULL) {
			_th_alloc_release(MATCH_SPACE,mark) ;
			return _ex_intern_appl1_env(env,INTERN_SET, e) ;
		}
    }
    _th_alloc_release(MATCH_SPACE,mark) ;

    switch(e->type) {
        case EXP_APPL:
        	r = _ex_intern_appl_env(env,INTERN_SET,0,NULL) ;
            for (i = 0; i < e->u.appl.count; ++i) {
				struct _ex_intern *s = match_closure(env,e->u.appl.args[i],pat_count,patterns) ;
				if (s->u.appl.count > 0) {
					r = _ex_intern_appl2_env(env,INTERN_UNION,r,s) ;
				}
            }
            return r ;
        case EXP_CASE:
            r = match_closure(env,e->u.case_stmt.exp,pat_count,patterns) ;
            for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
                struct _ex_intern *s = match_closure(env,e->u.case_stmt.exp,pat_count,patterns) ;
				if (s->u.appl.count > 0) {
					r = _ex_intern_appl2_env(env,INTERN_UNION,r,s) ;
				}
            }
            return r ;
        case EXP_QUANT:
            r = match_closure(env,e->u.quant.exp,pat_count,patterns) ;
            s = match_closure(env,e->u.quant.cond,pat_count,patterns) ;
			if (s->u.appl.count > 0) {
     			r = _ex_intern_appl2_env(env,INTERN_UNION,r,s) ;
			}
			return r ;
        case EXP_INDEX:
            return match_closure(env,e->u.index.exp,pat_count,patterns) ;
    }
    return _ex_intern_appl_env(env, INTERN_SET, 0, NULL) ;
}

struct _ex_intern *match_replace(struct env *env, struct _ex_intern *e, struct _ex_intern *pat, struct _ex_intern *result)
{
    int i ;
    struct _ex_intern *r, *s ;
    struct _ex_intern **args ;
    
    if (_th_equal(env,e,pat)) {
        return result ;
        return r ;
    }
    
    switch(e->type) {
    case EXP_APPL:
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
        r = _ex_intern_appl_env(env,INTERN_SET,0,NULL) ;
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = match_replace(env,e->u.appl.args[i],pat,result) ;
        }
        return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args) ;
    case EXP_CASE:
        args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.case_stmt.count*2) ;
        r = match_replace(env,e->u.case_stmt.exp,pat,result) ;
        for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
            args[i] = match_replace(env,e->u.case_stmt.exp, pat, result) ;
        }
        return _ex_intern_case(r, e->u.case_stmt.count, args) ;
    case EXP_QUANT:
        r = match_replace(env,e->u.quant.exp,pat,result) ;
        s = match_replace(env,e->u.quant.cond,pat,result) ;
        return _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,e->u.quant.vars,r,s) ;
    case EXP_INDEX:
        return _ex_intern_index(match_replace(env,e->u.index.exp,pat,result), e->u.index.functor, e->u.index.term) ;
    }
    return e ;
}

int illegal_term(struct env *env, struct _ex_intern *e)
{
    int i ;

    switch (e->type) {

    case EXP_APPL:
        if (e->u.appl.functor==INTERN_STATE1 || e->u.appl.functor==INTERN_STACK1) return 1 ;

        for (i = 0; i < e->u.appl.count; ++i) {
            if (illegal_term(env,e->u.appl.args[i])) return 1 ;
        }
        return 0 ;

    case EXP_CASE:
        if (illegal_term(env,e->u.case_stmt.exp)) return 1 ;

        for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
            if (illegal_term(env,e->u.case_stmt.args[i])) return 1 ;
        }
        return 0 ;

    case EXP_INDEX:
        return illegal_term(env,e->u.index.exp) ;

    default:
        return 0 ;

    }
}

int normal_condition(struct env *env, struct _ex_intern *e)
{
    int i ;

    switch (e->type) {

    case EXP_APPL:
        if (e->u.appl.functor==INTERN_COMPATIBLE_PREC || e->u.appl.functor==INTERN_REWRITABLE ||
            e->u.appl.functor==INTERN_Q_NAT || e->u.appl.functor==INTERN_Q_RAT ||
            e->u.appl.functor==INTERN_Q_VAR) return 0 ;

        for (i = 0; i < e->u.appl.count; ++i) {
            if (!normal_condition(env,e->u.appl.args[i])) return 0 ;
        }
        return 1 ;

    case EXP_CASE:
        if (!normal_condition(env,e->u.case_stmt.exp)) return 0 ;

        for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
            if (!normal_condition(env,e->u.case_stmt.args[i])) return 0 ;
        }
        return 1 ;

    case EXP_INDEX:
        return normal_condition(env,e->u.index.exp) ;

    default:
        return 1 ;

    }
}

int _th_is_constant(struct env *env, struct _ex_intern *e)
{
    int i ;

    switch (e->type) {
        case EXP_APPL:
            if (!_th_is_constructor(env,e->u.appl.functor)) return 0 ;
            for (i = 0; i < e->u.appl.count; ++i) {
                if (!_th_is_constant(env,e->u.appl.args[i])) return 0 ;
            }
            return 1 ;
        case EXP_STRING:
        case EXP_INTEGER:
        case EXP_RATIONAL:
        case EXP_VAR:
            return 1 ;
        default:
            return 0 ;
    }
}

static struct _ex_intern *distribute_or(struct env *env, struct _ex_intern *rule)
{
    struct _ex_intern **args, *cond, *t, **acc ;
    int i, term ;

    if (rule->u.appl.args[2]->type==EXP_APPL &&
        (rule->u.appl.args[2]->u.appl.functor==INTERN_AND ||
         rule->u.appl.args[2]->u.appl.functor==INTERN_NC_AND)) {
        cond = rule->u.appl.args[2] ;
        t = NULL ;
        for (i = 0; i < cond->u.appl.count; ++i) {
            if (cond->u.appl.args[i]->type==EXP_APPL && cond->u.appl.args[i]->u.appl.functor==INTERN_OR) {
                term = i ;
                t = cond->u.appl.args[i] ;
                break ;
            }
        }
        if (!t) return NULL ;
        args = ALLOCA(sizeof(struct _ex_intern *) * cond->u.appl.count) ;
        for (i = 0; i < cond->u.appl.count; ++i) {
            args[i] = cond->u.appl.args[i] ;
        }
        acc = ALLOCA(sizeof(struct _ex_intern *) * t->u.appl.count) ;
        for (i = 0; i <t->u.appl.count; ++i) {
            args[term] = t->u.appl.args[i] ;
            acc[i] = _ex_intern_appl_env(env,cond->u.appl.functor,cond->u.appl.count,args) ;
        }
        return _ex_intern_appl3_env(env, rule->u.appl.functor, rule->u.appl.args[0], rule->u.appl.args[1],
            _ex_intern_appl_env(env,INTERN_OR,t->u.appl.count,acc)) ;
    }
    return NULL ;
}

static int equal_except_condition(struct env *env, struct _ex_intern *set1, struct _ex_intern *set2)
{
    int i;

    if (set1->type != EXP_QUANT || set2->type != EXP_QUANT ||
        set1->u.quant.quant != INTERN_SETQ || set2->u.quant.quant != INTERN_SETQ) return 0;
    if (!_th_is_constant(env,set1->u.quant.exp) || !_th_is_constant(env,set2->u.quant.exp)) return 0;
    if (set1->u.quant.var_count != set2->u.quant.var_count) return 0;

    for (i =0; i < set1->u.quant.var_count; ++i) {
        if (set1->u.quant.vars[i] != set2->u.quant.vars[i]) return 0;
    }

    return 1;
}

struct _ex_intern *_th_simplify_defined(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern **args, *f, *h;
    int i;
	struct match_return *m;
    char *mark;

	e = e->u.appl.args[0] ;
	switch (e->type) {
	case EXP_VAR:
		return _ex_true ;
	case EXP_APPL:
		if (e->u.appl.functor==INTERN_DEFINED) return _ex_true ;
		if (_th_is_ac(env,e->u.appl.functor) && e->u.appl.count > 2) {
			//check_size(2) ;
			args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * 2);
			args[0] = e->u.appl.args[0] ;
			args[1] = _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count-1,e->u.appl.args+1) ;
			e = _ex_intern_appl_env(env,e->u.appl.functor,2,args) ;
			goto cont_defined ;
		} else if (_th_is_constructor(env,e->u.appl.functor)) {
			//check_size(e->u.appl.count) ;
			args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
			for (i = 0; i < e->u.appl.count; ++i) {
				args[i] = _ex_intern_appl_env(env,INTERN_DEFINED,1,e->u.appl.args+i) ;
			}
			return _ex_intern_appl_env(env,INTERN_AND,e->u.appl.count,args) ;
		} else {
cont_defined:
		//check_size(e->u.appl.count) ;
		args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (e->u.appl.count+2));
		for (i = 0; i < e->u.appl.count; ++i) {
			args[i] = _ex_intern_appl_env(env,INTERN_DEFINED,1,e->u.appl.args+i) ;
		}
		//check_size(2) ;
		args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * 2);
		args[0] = _ex_intern_appl_env(env,INTERN_AND,e->u.appl.count,args) ;
		f = _th_get_function_precondition(env,e->u.appl.functor) ;
		h = _th_get_function_prototype(env,e->u.appl.functor) ;
		mark = _th_alloc_mark(MATCH_SPACE) ;
		m = _th_match(env, h, e) ;
		args[1] = _th_subst(env,m->theta,f) ;
		_th_alloc_release(MATCH_SPACE,mark) ;
		return _ex_intern_appl_env(env,INTERN_AND,2,args) ;
		}
	}
	return NULL ;
}

struct _ex_intern *_th_simplify_preceq(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern *f, **args;
	int i, c;
    unsigned *tmp1, *tmp2, *vars;

	f = e->u.appl.args[1] ;
    e = e->u.appl.args[0] ;
	if (_th_equal(env,e,f)) return _ex_true ;
	switch (e->type) {
		case EXP_APPL:
			if (_th_is_constructor(env,e->u.appl.functor)) {
				if (f->type == EXP_APPL &&
					_th_is_constructor(env,f->u.appl.functor)) {
					if (e->u.appl.functor==f->u.appl.functor) {
						//check_size(e->u.appl.count) ;
						args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
						for (i = 0; i < e->u.appl.count; ++i) {
							args[i] = _ex_intern_appl2_env(env,INTERN_PRECEQ,e->u.appl.args[i],f->u.appl.args[i]) ;
						}
						return _ex_intern_appl_env(env,INTERN_AND,e->u.appl.count,args) ;
					} else if (_th_smallest_symbol_of_type(env,e->u.appl.functor)) {
						return _ex_true ;
					}
				}
			}
			if (f->type == EXP_MARKED_VAR) return _ex_false ;
			break ;
		case EXP_INTEGER:
			if (f->type == EXP_INTEGER) {
				(e->u.integer<=f->u.integer)?_ex_true:_ex_false ;
			}
			break ;
		case EXP_RATIONAL:
			if (f->type == EXP_RATIONAL) {
				tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(e->u.rational.numerator,f->u.rational.denominator)) ;
				tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(f->u.rational.numerator,e->u.rational.denominator)) ;
				if (_th_big_less(tmp1,tmp2)) {
					return _ex_true ;
				} else {
					return _ex_false ;
				}
			}
			break ;
		case EXP_STRING:
			if (f->type == EXP_STRING) {
				int se = strlen(e->u.string) ;
				int sf = strlen(f->u.string) ;
				((se<sf)||(se==sf&&strcmp(e->u.string,f->u.string) <= 0))?_ex_true:_ex_false;
			}
			break ;
		case EXP_MARKED_VAR:
			vars = _th_get_marked_vars_leave_marked(f,&c) ;
			if (_th_intern_get_data(e->u.marked_var.var)) {
				e = _ex_true ;
			} else {
				e = _ex_false ;
			}
			for (i = 0; i < c; ++i) {
				_th_intern_set_data(vars[i],0) ;
			}
			if (e != NULL) return e ;
			break ;
	}
	if (subterm_member(env,e,f)) return _ex_true ;
	return NULL;
}

struct _ex_intern *_th_builtin(struct env *env, struct _ex_intern *e)
{
    //unsigned qvars[MAX_ARGS] ;
    int i, j, k, l, c ;
    unsigned *fv ;
    struct _ex_intern *f, *h ;
    static char *strbuf = NULL ;
    static int strbuflen = 0 ;
    //struct _ex_unifier *u ;
    char *mark ;
    struct match_return *m ;
    //char var_name[20] ;
    unsigned zero[] = { 1, 0 }, one[] = { 1, 1 } ;
    unsigned *tmp1, *tmp2 ;
    int count ;
    struct _ex_intern **args;
    //struct _ex_unifier **unifiers;

    switch (e->type) {

	case EXP_APPL:
        if (e->u.appl.functor==INTERN_NAT_PLUS ||
            e->u.appl.functor==INTERN_NAT_MINUS || e->u.appl.functor==INTERN_NAT_TIMES ||
            e->u.appl.functor==INTERN_NAT_DIVIDE || e->u.appl.functor==INTERN_NAT_MOD) {
            for (i = 0; i < e->u.appl.count; ++i) {
                if (e->u.appl.args[i]->type==EXP_APPL &&
                    e->u.appl.args[i]->u.appl.functor==INTERN_ITE) {
                    for (j = 0; j < e->u.appl.count; ++j) {
                        if (i != j && !_th_is_constant(env,e->u.appl.args[j])) goto cont_appl;
                    }
                    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
                    for (j = 0; j < e->u.appl.count; ++j) {
                        args[j] = e->u.appl.args[j];
                    }
                    args[i] = e->u.appl.args[i]->u.appl.args[1];
                    f = _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
                    for (j = 0; j < e->u.appl.count; ++j) {
                        args[j] = e->u.appl.args[j];
                    }
                    args[i] = e->u.appl.args[i]->u.appl.args[2];
                    h = _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
                    return _ex_intern_appl3_env(env,INTERN_ITE,e->u.appl.args[i]->u.appl.args[0],f,h);
                }
            }
        }

cont_appl:
        switch (e->u.appl.functor) {
			
		case INTERN_ITE:
			return _th_simplify_ite(env,e);
			
		case INTERN_NAT_INTEGRATE:
			return _th_simplify_nat_integrate(env,e);
			
		case INTERN_NAT_SOLVE_INTEGRATE:
			return _th_simplify_nat_solve_integrate(env,e);
			
		case INTERN_NAT_INTEGRATE_SET:
			return _th_simplify_nat_integrate_set(env,e);
			
		case INTERN_NAT_MIN:
			return _th_simplify_nat_min(env,e);
			
		case INTERN_NAT_MAX:
			return _th_simplify_nat_max(env,e);
			
		case INTERN_GCD:
			if (e->u.appl.count==2 && e->u.appl.args[0]->type==EXP_INTEGER &&
				e->u.appl.args[1]->type==EXP_INTEGER) {
				return _ex_intern_integer(_th_big_gcd(e->u.appl.args[0]->u.integer,e->u.appl.args[1]->u.integer));
			}
			return NULL;
			
		case INTERN_SETSIZE:
			return _th_simplify_setsize(env,e);
			
        case INTERN_SELECT:
            return _th_simplify_select(env,e);

        case INTERN_STORE:
            return _th_simplify_store(env,e);

        case INTERN_EE:
            return _th_simplify_ee(env,e);

		case INTERN_SOLVE_FOR:
			if (e->u.appl.count <= 3 && e->u.appl.args[0]->type==EXP_VAR &&
				e->u.appl.args[1]->type==EXP_APPL) {
				
				switch (e->u.appl.args[1]->u.appl.functor) {
				case INTERN_ORIENTED_RULE:
					if (e->u.appl.args[1]->u.appl.args[2] != _ex_true) return NULL;
				case INTERN_EQUAL:
					if (e->u.appl.args[0]==e->u.appl.args[1]->u.appl.args[0] ||
						e->u.appl.args[0]==e->u.appl.args[1]->u.appl.args[1]) return e->u.appl.args[1];
					f = _th_nat_equal_linear_solve(env, e->u.appl.args[0]->u.var,e->u.appl.args[1]);
					return f;
				case INTERN_NAT_LESS:
					if (e->u.appl.args[0]==e->u.appl.args[1]->u.appl.args[0] ||
						e->u.appl.args[0]==e->u.appl.args[1]->u.appl.args[1]) return e->u.appl.args[1];
					f = _th_nat_less_linear_solve(env, e->u.appl.args[0]->u.var,e->u.appl.args[1]);
					return f;
				case INTERN_NOT:
					h = e->u.appl.args[1]->u.appl.args[0];
					if (h->type==EXP_APPL && h->u.appl.count <= 3) {
						
						switch (h->u.appl.functor) {
						case INTERN_ORIENTED_RULE:
							if (h->u.appl.args[2] != _ex_true) return NULL;
						case INTERN_EQUAL:
							if (e->u.appl.args[0]==h->u.appl.args[0] ||
								e->u.appl.args[0]==h->u.appl.args[1]) return e->u.appl.args[1];
							f = _th_nat_equal_linear_solve(env, e->u.appl.args[0]->u.var,h);
							if (f) {
								return _ex_intern_appl1_env(env,INTERN_NOT,f);
							} else {
								return NULL;
							}
							
						case INTERN_NAT_LESS:
							if (e->u.appl.args[0]==h->u.appl.args[0] ||
								e->u.appl.args[0]==h->u.appl.args[1]) return e->u.appl.args[1];
							f = _th_nat_less_linear_solve(env, e->u.appl.args[0]->u.var,h);
							if (f) {
								return _ex_intern_appl1_env(env,INTERN_NOT,f);
							} else {
								return NULL;
							}
						}
					}
					return NULL;
				}
			}
			return NULL;
			
		case INTERN_TYPE_OF:
			if (e->u.appl.count==1) {
				return _th_return_type(env,e->u.appl.args[0]);
			}
			return NULL;
			
		case INTERN_VAR_AS_STRING:
			if (e->u.appl.count==1 && e->u.appl.args[0]->type==EXP_VAR) {
				return _ex_intern_string(_th_intern_decode(e->u.appl.args[0]->u.var)) ;
			}
			return NULL;
			
		case INTERN_EXCLUDE_SET:
		case INTERN_USE_CONTEXT:
		case INTERN_APPLY_CONTEXT:
		case INTERN_IN_CONTEXT:
		case INTERN_BLOCK_CONTEXT:
			if (_th_test_mode) {
				return _ex_true ;
			}
			return NULL ;
			
		case INTERN_REMOVE_AND:
			e = e->u.appl.args[0] ;
			if (e->u.appl.args[0]->type==EXP_VAR) return NULL;
			if (e->u.appl.functor==INTERN_NC_AND || e->u.appl.functor==INTERN_ANDQ) {
				return _ex_intern_appl_env(env, INTERN_AND,e->u.appl.count,e->u.appl.args);
			}
			return e;
			
		case INTERN_IS_APPL:
			if (e->u.appl.count==1) {
				if (e->u.appl.args[0]->type==EXP_APPL) {
					return _ex_true ;
				} else {
					return _ex_false ;
				}
			} else {
				return NULL ;
			}
			
		case INTERN_ARG_COUNT:
			if (e->u.appl.count==1 && e->u.appl.args[0]->type==EXP_APPL) {
				return _ex_intern_small_integer(e->u.appl.args[0]->u.appl.count) ;
			} else {
				return NULL ;
			}
			
		case INTERN_FUNCTOR_ARGS:
			if (e->u.appl.count==1 && e->u.appl.args[0]->type==EXP_APPL) {
				e = e->u.appl.args[0] ;
				f = _ex_intern_appl_env(env,INTERN_NIL,0,NULL) ;
				for (i = e->u.appl.count-1; i >= 0; --i) {
					f = _ex_intern_appl2_env(env,INTERN_CONS,e->u.appl.args[i],f) ;
				}
				return f ;
			} else {
				return NULL ;
			}
			
		case INTERN_KB_RULES:
			if (e->u.appl.count != 1) return NULL ;
			e = e->u.appl.args[0] ;
			if (e->type != EXP_APPL || e->u.appl.count != 3) return NULL ;
			if (e->u.appl.functor != INTERN_ORIENTED_RULE && e->u.appl.functor != INTERN_FORCE_ORIENTED) return NULL ;
			return kb_set(env,e) ;
			
		case INTERN_UNCOMPOSE:
			if (e->u.appl.count != 2) return NULL ;
			f = e->u.appl.args[0] ;
			h = e->u.appl.args[1] ;
			if (f->type != EXP_QUANT || h->type != EXP_QUANT) return NULL ;
			if (f->u.quant.quant != INTERN_LAMBDA || h->u.quant.quant != INTERN_LAMBDA) return NULL ;
			if (f->u.quant.var_count != 1 || h->u.quant.var_count != 1) return NULL ;
			h = uncompose(env,f->u.quant.vars[0],f->u.quant.exp,h->u.quant.vars[0],h->u.quant.exp) ;
			if (h != NULL) return _ex_intern_quant(INTERN_LAMBDA,1,f->u.quant.vars,h,_ex_true) ;
			return NULL ;
			
		case INTERN_SET:
			{
				struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern)) ;
				for (i = 0, j = 0; i < e->u.appl.count; ++i) {
					for (k = 0; k < j; ++k) {
						if (_th_equal(env,e->u.appl.args[i],args[k])) goto set_cont ;
					}
					args[j++] = e->u.appl.args[i] ;
set_cont: ;
				}
				if (i != j) return _ex_intern_appl_env(env,INTERN_SET,j,args) ;
				return NULL ;
			}
			
		case INTERN_UNION_SET:
			if (e->u.appl.count==1 && e->u.appl.args[0]->type==EXP_APPL &&
				e->u.appl.args[0]->u.appl.functor==INTERN_SET) {
				return _ex_intern_appl_env(env,INTERN_UNION,e->u.appl.args[0]->u.appl.count, e->u.appl.args[0]->u.appl.args) ;
			}
			return NULL ;
			
		case INTERN_AND_SET:
			if (e->u.appl.count==1 && e->u.appl.args[0]->type==EXP_APPL &&
				e->u.appl.args[0]->u.appl.functor==INTERN_SET) {
				return _ex_intern_appl_env(env,INTERN_AND,e->u.appl.args[0]->u.appl.count, e->u.appl.args[0]->u.appl.args) ;
			}
			return NULL ;
			
		case INTERN_OR_SET:
			if (e->u.appl.count==1 && e->u.appl.args[0]->type==EXP_APPL &&
				e->u.appl.args[0]->u.appl.functor==INTERN_SET) {
				return _ex_intern_appl_env(env,INTERN_OR,e->u.appl.args[0]->u.appl.count, e->u.appl.args[0]->u.appl.args) ;
			}
			return NULL ;
			
		case INTERN_MAP_SET:
			if (e->u.appl.count==2 && e->u.appl.args[1]->type==EXP_APPL &&
				e->u.appl.args[1]->u.appl.functor==INTERN_SET) {
				
				struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.args[1]->u.appl.count) ;
				f = e->u.appl.args[1] ;
				
				for (i = 0; i < f->u.appl.count; ++i) {
					args[i] = _ex_intern_appl2_env(env,INTERN_APPLY,e->u.appl.args[0],f->u.appl.args[i]) ;
				}
				return _ex_intern_appl_env(env,INTERN_SET, i, args) ;
			}
			return NULL ;
			
		case INTERN_FILTER_SET:
			if (e->u.appl.count==2 && e->u.appl.args[1]->type==EXP_APPL &&
				e->u.appl.args[1]->u.appl.functor==INTERN_SET) {
				
				struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.args[1]->u.appl.count) ;
				f = e->u.appl.args[1] ;
				
				for (i = 0; i < f->u.appl.count; ++i) {
					struct _ex_intern *cargs[4] ;
					cargs[0] = _ex_true ;
					cargs[1] = _ex_intern_appl1_env(env,INTERN_SET,f->u.appl.args[i]) ;
					cargs[2] = _ex_false ;
					cargs[3] = _ex_intern_appl_env(env,INTERN_SET,0,NULL) ;
					args[i] = _ex_intern_case(_ex_intern_appl2_env(env,INTERN_APPLY,e->u.appl.args[0],f->u.appl.args[i]),2,cargs) ;
				}
				return _ex_intern_appl_env(env,INTERN_UNION, i, args) ;
			}
			return NULL ;
			
		case INTERN_SET_LIST:
			if (e->u.appl.count==1 && e->u.appl.args[0]->type==EXP_APPL &&
				e->u.appl.args[0]->u.appl.functor==INTERN_SET) {
				
				f = _ex_intern_appl_env(env,INTERN_NIL,0,NULL) ;
				
				for (i = e->u.appl.args[0]->u.appl.count-1; i != 0xffffffff; --i) {
					f = _ex_intern_appl2_env(env,INTERN_CONS, e->u.appl.args[0]->u.appl.args[i], f) ;
				}
				
				return f ;
			}
			return NULL ;
			
		case INTERN_NAT_TO_STRING:
			if (e->u.appl.count==1 && e->u.appl.args[0]->type==EXP_INTEGER &&
				e->u.appl.args[0]->u.integer[0]==1) {
				char buf[80] ;
				sprintf(buf, "%d", e->u.appl.args[0]->u.integer[1]) ;
				e = _ex_intern_string(buf) ;
				return e ;
			}
			return NULL ;
			
		case INTERN_SIMPLIFY_COND:
			if (e->u.appl.count==1 && e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_ANDQ) {
				struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.args[0]->u.appl.count) ;
				f = e->u.appl.args[0] ;
				for (i = 0; i < f->u.appl.count; ++i) {
					h = f->u.appl.args[i] ;
					if (h->type==EXP_APPL && (h->u.appl.functor==INTERN_APPLY_CONTEXT || h->u.appl.functor==INTERN_USE_CONTEXT)) {
						args[i] = h ;
					} else {
						args[i] = _th_int_rewrite(env, h, 0) ;
					}
				}
				return _ex_intern_appl_env(env, INTERN_ANDQ, f->u.appl.count, args) ;
			}
			return NULL ;
			
#ifdef XX
		case INTERN_APPLY_CONTEXT:
		case INTERN_USE_CONTEXT:
		case INTERN_IN_CONTEXT:
		case INTERN_BLOCK_CONTEXT:
			if (e->u.appl.count==1) return _ex_true ;
			return NULL ;
#endif
			
		case INTERN_MARK_VARS:
			if (e->u.appl.count==1) {
				return _th_mark_vars(env,e->u.appl.args[0]) ;
			}
			return NULL ;
			
		case INTERN_EVAL_COND:
			if (e->u.appl.count==1 && e->u.appl.args[0]->type==EXP_APPL &&
				e->u.appl.args[0]->u.appl.functor==INTERN_ANDQ) {
				struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.args[0]->u.appl.count) ;
				f = e->u.appl.args[0] ;
				for (i = 0, j = 0; i < f->u.appl.count; ++i) {
					if (f->u.appl.args[i]->type != EXP_APPL ||
						(f->u.appl.args[i]->u.appl.functor != INTERN_APPLY_CONTEXT &&
						f->u.appl.args[i]->u.appl.functor != INTERN_USE_CONTEXT &&
						f->u.appl.args[i]->u.appl.functor != INTERN_BLOCK_CONTEXT &&
						f->u.appl.args[i]->u.appl.functor != INTERN_IN_CONTEXT)) {
						args[j++] = f->u.appl.args[i] ;
					}
				}
				return _ex_intern_appl_env(env,INTERN_NC_AND,j,args) ;
			} else if (e->u.appl.count==1) {
				return e->u.appl.args[0] ;
			}
			return NULL ;
			
				case INTERN_ILLEGAL_TERM:
					if (e->u.appl.count==1 && illegal_term(env,e->u.appl.args[0])) return _ex_true ;
					return NULL ;
					
				case INTERN_REWRITABLE:
					if (e->u.appl.count==1 &&
						e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.count==1 &&
						e->u.appl.args[0]->u.appl.functor==INTERN_QUOTE &&
						!_th_in_context(INTERN_MACRO_CONTEXT) &&
						_th_cond_level() > 0) {
						f = e->u.appl.args[0]->u.appl.args[0] ;
						if (f != _th_int_rewrite(env,f,1)) return _ex_true ;
					}
					return NULL ;
					
				case INTERN_HAS_FREE_VARS:
					if (e->u.appl.count==1) {
						_th_get_free_vars(e->u.appl.args[0], &c) ;
						if (c > 0) {
							return _ex_true ;
						} else {
							return _ex_false ;
						}
					}
					return NULL ;
					
				case INTERN_IS_FREE_IN:
					if (e->u.appl.count==2 && e->u.appl.args[0]->type==EXP_VAR) {
						int *free_vars = _th_get_free_vars_leave_marked(e->u.appl.args[1], &c) ;
						if (_th_intern_get_data(e->u.appl.args[0]->u.var)&1) {
							e = _ex_true ;
						} else {
							e = _ex_false ;
						}
						for (i = 0; i < c; ++i) {
							_th_intern_set_data(free_vars[i], 0) ;
						}
						return e ;
					}
					return NULL ;
					
				case INTERN_NORMAL_CONDITION:
					if (e->u.appl.count==1 && normal_condition(env,e->u.appl.args[0])) return _ex_true ;
					return NULL ;
					
				case INTERN_UNQUOTE:
					if (e->u.appl.count==1 && e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.count==1 &&
						e->u.appl.args[0]->u.appl.functor == INTERN_QUOTE) {
						return e->u.appl.args[0]->u.appl.args[0] ;
					}
					return NULL ;
					
				case INTERN_QUANTIFY:
					if (e->u.appl.count==1) {
						fv = _th_get_free_vars(e->u.appl.args[0], &count) ;
						return _ex_intern_appl1_env(env,INTERN_QUOTE,_ex_intern_quant(INTERN_ALL,count,fv,e->u.appl.args[0],_ex_true)) ;
					}
					return NULL ;
					
				case INTERN_UNQUANTIFY:
					e = e->u.appl.args[0] ;
					if (e->type==EXP_QUANT && e->u.quant.cond==_ex_true) return _ex_intern_appl1_env(env,INTERN_QUOTE,e->u.quant.exp) ;
					return _ex_intern_appl1_env(env,INTERN_QUOTE,e) ;
					
					/*case INTERN_CUT:
					if (e->u.appl.count==0) {
					return _ex_true ;
					} else {
					return NULL ;
            }*/
					
			/*case INTERN_CHOOSE:
            if (e->u.appl.count==2) {
			return _ex_true ;
            } else {
			return NULL ;
            }*/
					
				case INTERN_GET_TERMS:
					if (!_th_do_context_rewrites) return NULL ;
					if (_th_gargs==NULL) return NULL ;
					return _ex_intern_appl1_env(env, INTERN_QUOTE, _th_gargs) ;
					
				case INTERN_GET_LIMIT_TERM:
					if (_th_limit_term==NULL) return NULL ;
					return _ex_intern_appl1_env(env, INTERN_QUOTE, _th_limit_term) ;
					
				case INTERN_GET_CURRENT_TERM:
					if (!_th_do_context_rewrites) return NULL ;
					if (_th_current_exp==NULL) return NULL ;
					return _ex_intern_appl1_env(env, INTERN_QUOTE, _th_current_exp) ;
					
				case INTERN_GET_CONTEXT_RULES:
					if (!_th_do_context_rewrites) return NULL ;
					if (e->u.appl.count==0) {
						return _ex_intern_appl1_env(env,INTERN_QUOTE,_th_get_context_rule_set(env)) ;
					} else {
						return NULL ;
					}
					
				case INTERN_SPECIAL_REWRITES:
					if (!_th_do_context_rewrites) return NULL ;
					if (e->u.appl.count==1) {
						mark = _th_alloc_mark(MATCH_SPACE) ;
						_th_special_rewrite_rule_no_var(MATCH_SPACE, env, e->u.appl.args[0], 0, NULL) ;
						e = _ex_intern_appl_env(env, INTERN_SET, _th_possibility_count, _th_possible_rewrites) ;
						_th_alloc_release(MATCH_SPACE, mark) ;
						return e ;
					} else {
						return NULL ;
					}
					
				case INTERN_SPECIAL_REWRITES_USING:
					if (!_th_do_context_rewrites) return NULL ;
					if (e->u.appl.count==2) {
						_th_derive_push(env) ;
						f = e->u.appl.args[1] ;
						//_zone_print1("rule %s", _th_print_exp(f)) ;
						if (f->type==EXP_APPL && f->u.appl.functor==INTERN_QUOTE && f->u.appl.count==1) f = f->u.appl.args[0] ;
						_th_derive_add_prepared(env,f = _th_derive_prepare(env,f)) ;
						//_zone_print1("prepared rule %s", _th_print_exp(f)) ;
						mark = _th_alloc_mark(MATCH_SPACE) ;
						_th_special_rewrite_rule_no_var(MATCH_SPACE, env, e->u.appl.args[0], 0, NULL) ;
						e = _ex_intern_appl_env(env, INTERN_SET, _th_possibility_count, _th_possible_rewrites) ;
						_th_derive_pop(env) ;
						_th_alloc_release(MATCH_SPACE, mark) ;
						return e ;
					} else {
						return NULL ;
					}
					
				case INTERN_TEST_MATCH_CLOSURE:
					if (e->u.appl.count > 1) {
						if (test_match_closure(env,e->u.appl.args[0],e->u.appl.count-1,e->u.appl.args+1)) {
							return _ex_true ;
						} else {
							return _ex_false ;
						}
					} else {
						return NULL ;
					}
					
				case INTERN_FIRST_MATCH_CLOSURE:
					if (e->u.appl.count > 1) {
						return first_match_closure(env,e->u.appl.args[0],e->u.appl.count-1,e->u.appl.args+1) ;
					} else {
						return NULL ;
					}
					
				case INTERN_MATCH_CLOSURE:
					if (e->u.appl.count > 1) {
						return match_closure(env,e->u.appl.args[0],e->u.appl.count-1,e->u.appl.args+1) ;
					} else {
						return NULL ;
					}
				case INTERN_REPLACE:
					if (e->u.appl.count == 3) {
						return match_replace(env,e->u.appl.args[0],e->u.appl.args[1],e->u.appl.args[2]) ;
					} else {
						return NULL ;
					}
					
				case INTERN_SUBST:
					if (e->u.appl.count == 3) {
						char *mark = _th_alloc_mark(MATCH_SPACE) ;
						if ((m = _th_match(env, e->u.appl.args[1], e->u.appl.args[0])) != NULL) {
							f = _th_subst(env,m->theta,e->u.appl.args[2]) ;
							_th_alloc_release(MATCH_SPACE,mark) ;
							return f ;
						}
						_th_alloc_release(MATCH_SPACE,mark) ;
						return NULL ;
					} else {
						return NULL ;
					}
					
				case INTERN_MATCH:
					if (e->u.appl.count == 2) {
						char *mark = _th_alloc_mark(MATCH_SPACE) ;
						if ((m = _th_match(env, e->u.appl.args[1], e->u.appl.args[0])) != NULL) {
							_th_alloc_release(MATCH_SPACE,mark) ;
							return _ex_true ;
						}
						_th_alloc_release(MATCH_SPACE,mark) ;
						return NULL ;
					} else {
						return NULL ;
					}
					
				case INTERN_XOR:
					return _th_simplify_xor(env, e);
				case INTERN_NC_AND:
					//_zone_print1("Here0 %d", e->u.appl.count) ;
					if (_th_test_mode) goto cont_nc_and;
					for (i = 0; i < e->u.appl.count; ++i) {
						//_zone_print1("Here1 %d", i) ;
						if (e->u.appl.args[i]->type!=EXP_APPL) goto cont_nc_and ;
						//_zone_print1("Here2 %d", e->u.appl.args[i]->u.appl.functor) ;
						if (e->u.appl.args[i]->u.appl.functor!=INTERN_USE_CONTEXT &&
							e->u.appl.args[i]->u.appl.functor!=INTERN_IN_CONTEXT &&
							e->u.appl.args[i]->u.appl.functor!=INTERN_BLOCK_CONTEXT &&
							e->u.appl.args[i]->u.appl.functor!=INTERN_APPLY_CONTEXT &&
							e->u.appl.args[i]->u.appl.functor!=INTERN_EXCLUDE_SET) goto cont_nc_and ;
						//_zone_print("Here3") ;
					}
					return _ex_true ;
cont_nc_and: ;
				case INTERN_AND:
					return _th_simplify_and(env,e);
				case INTERN_OR:
				case INTERN_NC_OR:
					return _th_simplify_or(env,e);
				case INTERN_NOT:
					return _th_simplify_not(env,e);
				case INTERN_ORIENTED_RULE:
				case INTERN_UNORIENTED_RULE:
				case INTERN_FORCE_ORIENTED:
					if (e->u.appl.count != 3) return NULL ;
					if (e->u.appl.args[2]==_ex_false) return _ex_true;
					if (e->u.appl.args[1]==_ex_true && e->u.appl.args[2]==_ex_true) return e->u.appl.args[0];
					if (e->u.appl.args[1]==_ex_false && e->u.appl.args[2]==_ex_true) return _ex_intern_appl1_env(env,INTERN_NOT,e->u.appl.args[0]);
				case INTERN_EQUAL:
					if (e->u.appl.functor==INTERN_EQUAL && e->u.appl.count != 2) return NULL ;
					return _th_simplify_equality(env,e);    
				case INTERN_NAT_PLUS:
					return _th_simplify_nat_plus(env,e);
				case INTERN_NAT_POWER:
					if (e->u.appl.args[0]->type == EXP_INTEGER &&
						e->u.appl.args[1]->type == EXP_INTEGER) {
						return _ex_intern_integer(_th_big_power(e->u.appl.args[0]->u.integer,e->u.appl.args[1]->u.integer)) ;
					}
					return NULL ;
				case INTERN_NAT_MINUS:
                    return _th_simplify_nat_minus(env,e);
				case INTERN_NAT_TIMES:
					return _th_simplify_nat_times(env,e);
				case INTERN_NAT_DIVIDE:
                    return _th_simplify_nat_divide(env,e);
				case INTERN_NAT_MOD:
					if (e->u.appl.args[0]->type == EXP_INTEGER &&
						e->u.appl.args[1]->type == EXP_INTEGER &&
						(!_th_big_is_zero(e->u.appl.args[1]->u.integer))) {
						return _ex_intern_integer(_th_big_mod(e->u.appl.args[0]->u.integer,e->u.appl.args[1]->u.integer)) ;
					}
					return _th_process_mod(env,e);            
				case INTERN_NAT_LESS:
					return _th_simplify_nat_less(env,e);
				
                case INTERN_NAT_TO_RAT:
                    return _th_simplify_nat_rat(env,e);

				case INTERN_RAT_PLUS:
					return _th_simplify_rat_plus(env,e);
					
				case INTERN_RAT_MINUS:
					return _th_simplify_rat_minus(env,e);
					
				case INTERN_RAT_TIMES:
					return _th_simplify_rat_times(env,e);
					
				case INTERN_RAT_DIVIDE:
					return _th_simplify_rat_divide(env,e);
					
				case INTERN_RAT_LESS:
					return _th_simplify_rat_less(env,e);
					
				case INTERN_SIZE:
					if (e->u.appl.args[0]->type == EXP_STRING) {
						return _ex_intern_small_integer(strlen(e->u.appl.args[0]->u.string)) ;
					} else {
						return NULL ;
					}
				case INTERN_CHAR:
					if (e->u.appl.args[0]->type == EXP_STRING &&
						e->u.appl.args[1]->type == EXP_INTEGER) {
						if (e->u.appl.args[1]->u.integer[0]==1 && e->u.appl.args[1]->u.integer[1] < (unsigned)strlen(e->u.appl.args[0]->u.string)) {
							return _ex_intern_small_integer(e->u.appl.args[0]->u.string[e->u.appl.args[1]->u.integer[1]]) ;
						}
					}
					return NULL ;
					
				case INTERN_BUILD_FUNCTOR:
					if (e->u.appl.count == 2 &&
						e->u.appl.args[0]->type==EXP_STRING &&
						e->u.appl.args[1]->type==EXP_APPL) {
						return _ex_intern_appl_env(env,_th_intern(e->u.appl.args[0]->u.string),
							e->u.appl.args[1]->u.appl.count,
							e->u.appl.args[1]->u.appl.args) ;
					}
					return NULL ;
				case INTERN_CONCAT:
#ifdef XX
					if (e->u.appl.args[1]->type == EXP_STRING &&
						e->u.appl.args[0]->type == EXP_INTEGER) {
						if (e->u.appl.args[0]->u.integer[0]==1 && e->u.appl.args[0]->u.integer[1] < 256 &&
							e->u.appl.args[0]->u.integer[1] >= 0) {
							if (strbuflen < (int)strlen(e->u.appl.args[1]->u.string)+2) {
								strbuflen = (int)strlen(e->u.appl.args[1]->u.string)+2 ;
								if (strbuf==NULL) {
									strbuf = MALLOC(strbuflen) ;
								} else {
									strbuf = REALLOC(strbuf,strbuflen) ;
								}
							}
							strbuf[0] = e->u.appl.args[0]->u.integer[1] ;
							strcpy(strbuf+1, e->u.appl.args[1]->u.string) ;
							return _ex_intern_string(strbuf) ;
						}
					}
#endif
					j = 0 ;
					for (i = 0; i < e->u.appl.count; ++i) {
						if (e->u.appl.args[i]->type != EXP_STRING) return NULL ;
						j += strlen(e->u.appl.args[i]->u.string) + 1 ;
					}
					{
						char *res = (char *)ALLOCA(j) ;
						res[0] = 0 ;
						for (i = 0; i < e->u.appl.count; ++i) {
							strcat(res, e->u.appl.args[i]->u.string) ;
						}
						return _ex_intern_string(res) ;
					}
					
				case INTERN_PRECEQ:
					return _th_simplify_preceq(env,e);
					
				case INTERN_APPLY:
					return _th_simplify_apply(env,e);
					
				case INTERN_DEFINED:
					return _th_simplify_defined(env,e);
					
				case INTERN_DIFFERENCE:
					return _th_simplify_difference(env,e);
					
				case INTERN_UNION:
					return _th_simplify_union(env,e);
					
				case INTERN_SUBSET:
					return _th_simplify_subset(env,e);
					
				case INTERN_SEPARATE:
					return _th_simplify_separate(env,e);
					
				case INTERN_MEMBER:
					return _th_simplify_member(env,e);
					
				case INTERN_INTERSECT:
					return _th_simplify_intersect(env,e);
					
				case INTERN_Q_NAT:
					if (e->u.appl.args[0]->type==EXP_INTEGER) return _ex_true ;
					return NULL ;
					
				case INTERN_Q_RAT:
					if (e->u.appl.args[0]->type==EXP_RATIONAL) return _ex_true ;
					return NULL ;
					
				case INTERN_Q_VAR:
					if (e->u.appl.args[0]->type==EXP_VAR) return _ex_true ;
					return NULL ;
					
				case INTERN_Q_UNUSED_VAR:
					if (e->u.appl.args[0]->type==EXP_VAR &&
						!_th_used_var(env,e->u.appl.args[0]->u.var)) return _ex_true ;
					return NULL ;
					
				case INTERN_COMPATIBLE_PREC:
				/*                    tmp1 = _th_get_free_vars(e->u.appl.args[0],&k) ;
				tmp2 = _th_get_free_vars(e->u.appl.args[1],&l) ;
				for (i = 0; i < l; ++i) {
				for (j = 0; j < k; ++j) {
				if (tmp2[i]==tmp1[j]) goto cp_cont ;
				}
				return NULL ;
				cp_cont: ;
				}
				tmp1 = _th_get_marked_vars(e->u.appl.args[0],&k) ;
				tmp2 = _th_get_marked_vars(e->u.appl.args[1],&l) ;
				for (i = 0; i < k; ++i) {
				for (j = 0; j < l; ++j) {
				if (tmp1[i]==tmp2[j]) goto cp_cont2 ;
				}
				return _ex_true ;
				cp_cont2: ;
                    }*/
					if (_th_smaller(env,e->u.appl.args[1],e->u.appl.args[0])) {
						return _ex_true ;
					} else {
						return NULL ;
					}
					
				case INTERN_MARKED_SUBSET:
					tmp1 = _th_get_free_vars(e->u.appl.args[0],&k) ;
					tmp2 = _th_get_free_vars(e->u.appl.args[1],&l) ;
					for (i = 0; i < k; ++i) {
						for (j = 0; j < l; ++j) {
							if (tmp1[i]==tmp2[j]) goto ms_cont ;
						}
						return NULL ;
ms_cont: ;
					}
					return _ex_true ;
					
				default:
					return NULL ;
            }
            
        case EXP_QUANT:
            switch (e->u.quant.quant) {
                case INTERN_ALL:
	    			return _th_simplify_all(env,e);
                case INTERN_EXISTS:
			    	return _th_simplify_exists(env,e);
                case INTERN_SETQ:
				    return _th_simplify_setq(env,e);
                case INTERN_LAMBDA:
				     return _th_simplify_lambda(env,e);
                default:
                    return NULL ;
            }
            
        case EXP_CASE:
			return _th_simplify_case(env,e);
    }
    
    return NULL ;
}
