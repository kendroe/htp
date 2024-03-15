/*
 * ex_intern.c
 *
 * Expression intern code
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"
#include "Doc.h"

static int integer_parent_size = 4001 ;
static int rational_parent_size = 4001 ;
static int appl_parent_size = 249989 ;
static int case_parent_size = 249989 ;
static int quant_parent_size = 4001 ;
static int var_parent_size = 4001 ;
static int marked_var_parent_size = 4001 ;
static int index_parent_size = 1009 ;
static int string_parent_size = 4001 ;

GDEF("struct_primary_pointer_array main _exp_record integer_parent[0..integer_parent_size] (main | second) _ex_intern");
GDEF("struct_primary_pointer_array main _exp_record rational_parent[0..rational_parent_size] (main | second) _ex_intern");
GDEF("struct_primary_pointer_array main _exp_record appl_parent[0..appl_parent_size] (main | second) _ex_intern");
GDEF("struct_primary_pointer_array main _exp_record case_parent[0..case_parent_size] (main | second) _ex_intern");
GDEF("struct_primary_pointer_array main _exp_record quant_parent[0..quant_parent_size] (main | second) _ex_intern");
GDEF("struct_primary_pointer_array main _exp_record var_parent[0..var_parent_size] (main | second) _ex_intern");
GDEF("struct_primary_pointer_array main _exp_record marked_var_parent[0..marked_var_parent_size] (main | second) _ex_intern");
GDEF("struct_primary_pointer_array main _exp_record index_parent[0..index_parent_size] (main | second) _ex_intern");
GDEF("struct_primary_pointer_array main _exp_record string_parent[0..string_parent_size] (main | second) _ex_intern");

GDEF("struct_primary_pointer main _ex_intern next main _ex_intern");
GDEF("struct_primary_pointer second _ex_intern next (main | second) _ex_intern");
GDEF("struct_space main _ex_intern space[INTERN_SPACE]");
GDEF("struct_space second _ex_intern space[INTERN_TEMP_SPACE]");

struct _exp_record {
    struct _ex_intern **integer_parent ;
    struct _ex_intern **rational_parent ;
    struct _ex_intern **appl_parent ;
    struct _ex_intern **case_parent ;
    struct _ex_intern **quant_parent ;
    struct _ex_intern **var_parent ;
    struct _ex_intern **marked_var_parent ;
    struct _ex_intern **index_parent ;
    struct _ex_intern **string_parent ;
    struct _ex_intern *first_term, *last_term;
#ifdef _DEBUG
    int integer_count ;
    int rational_count ;
    int appl_count, appl_arg_count ;
    int case_count ;
    int quant_count ;
    int var_count ;
    int marked_var_count ;
    int index_count ;
    int string_count ;
#endif
} ;

GDEF("define _ex_set current->integer_parent[0..integer_parent_size] next * | \
                     current->rational_parent[0..rational_parent_size] next * | \
                     current->appl_parent[0..appl_parent_size] next * | \
                     current->case_parent[0..case_parent_size] next * | \
                     current->quant_parent[0..quant_parent_size] next * | \
                     current->var_parent[0..var_parent_size] next * | \
                     current->marked_var_parent[0..marked_var_parent_size] next * | \
                     current->index_parent[0..index_parent_size] next * | \
                     current->string_parent[0..string_parent_size] next *");

GDEF("define _ex_save_set current->integer_parent[0..integer_parent_size] next * | \
                          current->rational_parent[0..rational_parent_size] next * | \
                          current->appl_parent[0..appl_parent_size] next * | \
                          current->case_parent[0..case_parent_size] next * | \
                          current->quant_parent[0..quant_parent_size] next * | \
                          current->var_parent[0..var_parent_size] next * | \
                          current->marked_var_parent[0..marked_var_parent_size] next * | \
                          current->index_parent[0..index_parent_size] next * | \
                          current->string_parent[0..string_parent_size] next *");

GDEF("invariant _ex_push != 0 || ALL(x in _ex_set) alloc_mode(x)==main");
GDEF("invariant _ex_push_level==0 || ALL(x in _ex_save_set) alloc_mode(x)==main");

struct parent_updates {
    struct parent_updates *next;
    struct _ex_intern *e;
    int old_parent_level;
    struct add_list *old_adds;
};

static struct parent_updates *parent_updates = NULL;

struct parent_stack {
    struct parent_stack *next;
    struct parent_updates *list;
    char *mark;
};

static struct parent_stack *parent_stack = NULL;
static int parent_level = 0;


#ifdef _DEBUG
static int integer_count ;
static int rational_count ;
static int appl_count, appl_arg_count ;
static int case_count ;
static int quant_count ;
static int var_count ;
static int marked_var_count ;
static int index_count ;
static int string_count ;
#endif

static struct _exp_record current, save, deleted ;
static int push_level = 0;
static char *temp_space_mark ;
static int space ;

struct _ex_intern *_ex_true ;
struct _ex_intern *_ex_false ;
struct _ex_intern *_ex_nil ;
struct _ex_intern *_ex_bool ;
struct _ex_intern *_ex_int ;
struct _ex_intern *_ex_real ;
struct _ex_intern *_ex_array ;
struct _ex_intern *_ex_one ;
struct _ex_intern *_ex_r_one ;

int has_marked_var(struct _ex_intern *e)
{
    int i;

    if (e->type==EXP_MARKED_VAR) return 1;

    if (e->type==EXP_APPL) {
        for (i = 0; i < e->u.appl.count; ++i) {
            if (has_marked_var(e->u.appl.args[i])) return 1;
        }
    }

    return 0;
}

struct equiv_class {
    struct equiv_class *next;
    struct _ex_intern *id;
    struct add_list *terms;
};

static struct equiv_class *add_exp(struct equiv_class *ec, struct _ex_intern *e)
{
    struct equiv_class *ec1;
    struct _ex_intern *c;
    struct add_list *a;

    c = e;
    while (c->rewrite != NULL && c->rewrite != c) {
        c = c->rewrite;
    }
    while (c->find != NULL && c->find != c) {
        c = c->find;
    }

    ec1 = ec;
    while (ec1) {
        if (ec1->id==c) {
            break;
        }
        ec1 = ec1->next;
    }

    if (ec1==NULL) {
        ec1 = (struct equiv_class *)_th_alloc(HEURISTIC_SPACE,sizeof(struct equiv_class));
        ec1->next = ec;
        ec1->id = c;
        ec1->terms = NULL;
        ec = ec1;
    }

    a = (struct add_list *)_th_alloc(HEURISTIC_SPACE,sizeof(struct add_list));
    a->next = ec1->terms;
    ec1->terms = a;
    a->e = e;

    return ec;
}

static struct _ex_intern *build_canonical(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *r;
    int i;
    struct _ex_intern **args;

    if (e->type != EXP_APPL) {
        r = e;
        while (r->rewrite != NULL && r->rewrite != r) {
            r = r->rewrite;
        }
        while (r->find != NULL && r->find != r) {
            r = r->find;
        }
        return r;
    }

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
    for (i = 0; i < e->u.appl.count; ++i) {
        args[i] = build_canonical(env,e->u.appl.args[i]);
    }

    r = _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
    if (!r->in_hash) {
        //_tree_print0("Not in hash");
        _tree_indent();
        _th_int_rewrite(env,r,0);
        _tree_undent();
    }
    while (r->rewrite && r->rewrite != r) r = r->rewrite;
    while (r->find && r->find != r) r = r->find;

    return r;
}

static void print_rewrite_info(struct env *env, struct _ex_intern *t)
{
    struct _ex_intern *r;
    int i;
    _tree_print_exp("term", t);
    r = t;
    _tree_indent();
    _tree_print_exp("Canonical", build_canonical(env, t));
    while (r->rewrite && r->rewrite != r) {
        r = r->rewrite;
        _tree_print_exp("rew", r);
    }
    do {
        r = r->find;
        if (r) _tree_print_exp("find", r);
    } while (r && r != r->find);
    _tree_undent();
    if (t->type==EXP_APPL) {
        for (i = 0; i < t->u.appl.count; ++i) {
            print_rewrite_info(env, t->u.appl.args[i]);
        }
    }
}

void _th_collect_and_print_classes(struct env *env, int stop_on_errors)
{
#ifndef FAST
    int i;
    struct equiv_class *ec = NULL, *etemp, *etemp2;
    struct add_list *a;
    char *mark = _th_alloc_mark(HEURISTIC_SPACE);

    int errors = 0;

    _tree_print0("Equivalence classes");
    _tree_indent();

    if (_zone_active() || (stop_on_errors&1)) {
        _tree_print0("Errors");
        _tree_indent();
    }

    for (i = 0; i < appl_parent_size; ++i) {
        struct _ex_intern *t = current.appl_parent[i];
        struct _ex_intern *r;
        while (t) {
            if (t->u.appl.functor!=INTERN_AND && t->u.appl.functor!=INTERN_OR &&
                t->u.appl.functor!=INTERN_NOT && t->u.appl.functor!=INTERN_ITE &&
                !has_marked_var(t) && t->u.appl.functor != INTERN_ORIENTED_RULE) {
                if (t->in_hash) {
                    r = t;
                    while (r->rewrite && r != r->rewrite) {
                        r = r->rewrite;
                    }
                    while (r->find && r != r->find) {
                        r = r->find;
                    }
                    if (_zone_active() || (stop_on_errors & 1)) {
                        if (r->rewrite && (r->type != EXP_APPL || r->u.appl.functor != INTERN_EQUAL) && r != build_canonical(env,t)) {
                            _tree_print_exp("Error (rewrite not to canonical)", t);
                            //_tree_print_exp("r", r);
                            //_tree_print_exp("bc", build_canonical(env,t));
                            _tree_indent();
                            print_rewrite_info(env, t);
                            if (t->in_hash) {
                                errors = 1;
                            } else {
                                _tree_print("but not in hash");
                            }
                            _tree_undent();
                        }
                    }
                }
                ec = add_exp(ec,t);
            }
            t = t->next;
        }
    }
    for (i = 0; i < var_parent_size; ++i) {
        struct _ex_intern *t = current.var_parent[i];
        while (t) {
            ec = add_exp(ec,t);
            t = t->next;
        }
    }
    
    if (_zone_active() || (stop_on_errors & 1)) {
        if (stop_on_errors >= 2) {
            etemp = ec;
            while (etemp) {
                struct _ex_intern *type;
                if (etemp->id->type==EXP_VAR) {
                    type = _th_get_var_type(env,etemp->id->u.var);
                } else if (etemp->id->type==EXP_APPL) {
                    type = _th_get_type(env,etemp->id->u.appl.functor);
                    if (type) type = type->u.appl.args[1];
                } else {
                    type=NULL;
                }
                etemp2 = etemp->next;
                while (etemp2) {
                    struct _ex_intern *type2;
                    if (etemp->id->type==EXP_VAR) {
                        type2 = _th_get_var_type(env,etemp2->id->u.var);
                    } else if (etemp->id->type==EXP_APPL) {
                        type2 = _th_get_type(env,etemp2->id->u.appl.functor);
                        if (type2) type2 = type2->u.appl.args[1];
                    } else {
                        type2=NULL;
                    }
                    if ((etemp->id->type!=EXP_APPL || etemp->id->u.appl.functor >= INTERN_EE) &&
                        type &&
                        (etemp2->id->type!=EXP_APPL || etemp2->id->u.appl.functor >= INTERN_EE) &&
                        type2==type) {
                        struct _ex_intern *eq = _ex_intern_appl2_env(env,INTERN_EQUAL,etemp->id,etemp2->id);
                        if (eq->rewrite != _ex_false) {
                            _tree_print_exp("Completeness error", eq);
                        }
                    }
                    etemp2 = etemp2->next;
                }
                etemp = etemp->next;
            }
        }
        
        etemp = ec;
        while (etemp) {
            struct add_list *a1, *a2;
            a1 = etemp->terms;
            while (a1) {
                a2 = a1->next;
                while (a2) {
                    struct _ex_intern *x = _ex_intern_appl2_env(env,INTERN_EQUAL,a1->e,a2->e);
                    while (x->rewrite && x->rewrite != x) x = x->rewrite;
                    if (x->rewrite==_ex_false) {
                        _tree_print_exp("Disjoint members", a1->e);
                        _tree_print_exp("and",a2->e);
                    }
                    a2 = a2->next;
                }
                a1 = a1->next;
            }
            etemp = etemp->next;
        }
        
        _tree_undent();
    }

    if ((stop_on_errors & 1)==0 || errors) {
        _tree_print0("From builtins");
        _tree_indent();
        etemp = ec;
        while (etemp) {
            struct _ex_intern *type;
            if (etemp->id->type==EXP_VAR) {
                type = _th_get_var_type(env,etemp->id->u.var);
            } else if (etemp->id->type==EXP_APPL) {
                type = _th_get_type(env,etemp->id->u.appl.functor);
                if (type) type = type->u.appl.args[1];
            } else {
                type=NULL;
            }
            //if (etemp->id->type==EXP_APPL && etemp->id->u.appl.functor < INTERN_EE) {
            if (!etemp->id->in_hash) {
                _tree_print_exp("class",etemp->id);
                a = etemp->terms;
                _tree_indent();
                if (type) _tree_print_exp("type", type);
                while (a) {
                    _tree_print_exp("term", a->e);
                    a = a->next;
                }
                _tree_undent();
            }
            etemp = etemp->next;
        }
        _tree_undent();
        
        _tree_print0("From user");
        _tree_indent();
        etemp = ec;
        while (etemp) {
            struct _ex_intern *type;
            if (etemp->id->type==EXP_VAR) {
                type = _th_get_var_type(env,etemp->id->u.var);
            } else if (etemp->id->type==EXP_APPL) {
                type = _th_get_type(env,etemp->id->u.appl.functor);
                if (type) type = type->u.appl.args[1];
            } else {
                type=NULL;
            }
            //if (etemp->id->type!=EXP_APPL || etemp->id->u.appl.functor >= INTERN_EE) {
            if (etemp->id->in_hash) {
                _tree_print_exp("class",etemp->id);
                a = etemp->terms;
                _tree_indent();
                if (type) _tree_print_exp("type", type);
                while (a) {
                    _tree_print_exp("term", a->e);
                    a = a->next;
                }
                _tree_undent();
            }
            etemp = etemp->next;
        }
        
        _tree_undent();
    }
    _tree_undent();
    _th_alloc_release(HEURISTIC_SPACE,mark);

    if ((stop_on_errors & 1) && errors) {
        printf("Exiting due to errors\n");
        exit(1);
    }
#endif
}

void _ex_used_in_push()
{
    char *mark = _th_alloc_mark(INTERN_TEMP_SPACE);
    struct parent_stack *ps = (struct parent_stack *)_th_alloc(INTERN_TEMP_SPACE,sizeof(struct parent_stack));

    ps->next = parent_stack;
    ps->list = parent_updates;
    ps->mark = mark;

    parent_stack = ps;
    parent_updates = NULL;

    ++parent_level;
}

void _ex_used_in_pop()
{
    char *mark;
    --parent_level;

    while (parent_updates) {
        struct add_list *a = parent_updates->e->used_in;
        parent_updates->e->used_in = parent_updates->old_adds;
        //if (parent_updates->e->used_level <= parent_updates->old_parent_level) {
        //    fprintf(stderr, "Illegal parent level\n");
        //    exit(1);
        //}
        parent_updates->e->used_level = parent_updates->old_parent_level;
        parent_updates = parent_updates->next;
    }

    parent_updates = parent_stack->list;
    mark = parent_stack->mark;
    parent_stack = parent_stack->next;

    //printf("exiting\n");

    _th_alloc_release(INTERN_TEMP_SPACE, mark);
}

struct _ex_intern *_ex_intern_integer(unsigned *x)
{
    unsigned hash = 0 ;
    unsigned i ;
    struct _ex_intern *e ;

    /* Generate the hash value */
    for (i = 0; i <= *x; ++i) hash += x[i] ;
    hash %= integer_parent_size ;

    /* First, try and find the value */
    e = current.integer_parent[hash] ;
    while (e!= NULL) {
        if (_th_big_equal(x, e->u.integer)) return e ;
        e = e->next ;
    }

    /* Create a new entry if none exists */
    e = (struct _ex_intern *)_th_alloc(space, sizeof(struct _ex_base) + sizeof(unsigned) * (*x + 1)) ;
    e->next = current.integer_parent[hash] ;
    current.integer_parent[hash] = e ;

    e->next_cache = e->rewrite = NULL ;
    e->find = e;
    e->type = EXP_INTEGER ;
    e->has_special_term = 0 ;
    e->no_top_var = 0 ;
    e->mark1 = 0 ;
    e->mark2 = 0 ;
    e->in_rewrite = e->in_backchain = 0 ;
    e->unmarked_term = NULL;
    e->marked_term = NULL;
    e->term_cache = NULL;
    e->is_marked_term = 0;
    e->rule_simplified = 0;
    e->rule_blocked = 0;
    e->user1 = NULL;
    e->user2 = e->user3 = NULL;
    e->unate_processed = e->unate_false = e->unate_true = 0 ;
	e->print_line = 0 ;
	e->used_level = 0 ;
    e->can_cache = 1 ;
    e->type_inst = NULL;
    e->prepare = NULL;
    e->used_in = NULL;
    e->cache_bad = 0;
    e->cached_in = NULL;
    e->height = 0;
    e->sig = NULL;
    e->prev_term = current.last_term;
    e->next_term = NULL;
    e->explanation = NULL;
    e->merge = NULL;
    e->original = NULL;
    e->in_hash = 0;
    if (current.last_term) {
        current.last_term->next_term = e;
        current.last_term = e;
    } else {
        current.first_term = current.last_term = e;
    }
    for (i = 0; i <= *x; ++i) e->u.integer[i] = x[i] ;

#ifdef _DEBUG
    ++current.integer_count ;
#endif

    return e ;
}

struct _ex_intern *_ex_intern_small_integer(int x)
{
    unsigned i[2] = { 1, 0 } ;

    i[1] = x ;
    return _ex_intern_integer(i) ;
}

struct _ex_intern *_ex_intern_small_rational(int x, int y)
{
    unsigned n[2] = { 1, 0 } ;
    unsigned d[2] = { 1, 1 } ;

    n[1] = x ;
    d[1] = y ;
    return _ex_intern_rational(n,d) ;
}

struct _ex_intern *_ex_intern_var(unsigned x)
{
    unsigned hash = 0 ;
    struct _ex_intern *e ;

    /* Generate the hash value */
    hash = x%var_parent_size ;

    /* First, try and find the value */
    e = current.var_parent[hash] ;
    while (e!= NULL) {
        if (x==e->u.var) return e ;
        e = e->next ;
    }

    /* Create a new entry if none exists */
    e = (struct _ex_intern *)_th_alloc(space, sizeof(struct _ex_base) + sizeof(unsigned)) ;
    e->next = current.var_parent[hash] ;
    current.var_parent[hash] = e ;

    e->next_cache = e->rewrite = NULL ;
    e->find = e;
    e->type = EXP_VAR ;
    e->has_special_term = 0 ;
    e->no_top_var = 0 ;
    e->mark1 = 0 ;
    e->mark2 = 0 ;
    e->in_rewrite = e->in_backchain = 0 ;
    e->unmarked_term = NULL;
    e->marked_term = NULL;
    e->term_cache = NULL;
    e->is_marked_term = 0;
    e->rule_simplified = 0;
    e->rule_blocked = 0;
    e->user1 = NULL;
    e->user2 = e->user3 = NULL;
    e->unate_processed = e->unate_false = e->unate_true = 0 ;
	e->print_line = 0 ;
	e->used_level = 0 ;
    e->can_cache = 1 ;
    e->type_inst = NULL;
    e->prepare = NULL;
    e->u.var = x ;
    e->used_in = NULL;
    e->cache_bad = 0;
    e->cached_in = NULL;
    e->height = 0;
    e->sig = NULL;
    e->prev_term = current.last_term;
    e->next_term = NULL;
    e->explanation = NULL;
    e->merge = NULL;
    e->original = NULL;
    e->in_hash = 0;
    if (current.last_term) {
        current.last_term->next_term = e;
        current.last_term = e;
    } else {
        current.first_term = current.last_term = e;
    }

#ifdef _DEBUG
    ++current.var_count ;
#endif

    return e ;
}

struct _ex_intern *_ex_intern_marked_var(unsigned x, int y)
{
    unsigned hash = 0 ;
    struct _ex_intern *e ;

    /* Generate the hash value */
    hash = (x+((unsigned)y))%marked_var_parent_size ;

    /* First, try and find the value */
    e = current.marked_var_parent[hash] ;
    while (e != NULL) {
        if (x==e->u.marked_var.var && y==e->u.marked_var.quant_level) return e ;
        e = e->next ;
    }

    /* Create a new entry if none exists */
    e = (struct _ex_intern *)_th_alloc(space, sizeof(struct _ex_base) + sizeof(unsigned) * 2) ;
    e->next = current.marked_var_parent[hash] ;
    current.marked_var_parent[hash] = e ;

    e->next_cache = e->rewrite = NULL ;
    e->find = e;
    e->type = EXP_MARKED_VAR ;
    e->has_special_term = 0 ;
    e->no_top_var = 0 ;
    e->mark1 = 0 ;
    e->mark2 = 0 ;
    e->in_rewrite = e->in_backchain = 0 ;
    e->unmarked_term = NULL;
    e->marked_term = NULL;
    e->term_cache = NULL;
    e->is_marked_term = 0;
    e->rule_simplified = 0;
    e->rule_blocked = 0;
    e->user1 = NULL;
    e->user2 = e->user3 = NULL;
    e->unate_processed = e->unate_false = e->unate_true = 0 ;
	e->print_line = 0 ;
	e->used_level = 0 ;
    e->can_cache = 1 ;
    e->type_inst = NULL;
    e->prepare = NULL;
    e->u.marked_var.var = x ;
    e->u.marked_var.quant_level = y ;
    e->used_in = NULL;
    e->cache_bad = 0;
    e->cached_in = NULL;
    e->height = 0;
    e->sig = NULL;
    e->in_hash = 0;
    e->prev_term = e->next_term = NULL;
    e->explanation = NULL;
    e->merge = NULL;
    e->original = NULL;

#ifdef _DEBUG
    ++current.marked_var_count ;
#endif

    return e ;
}

struct _ex_intern *_ex_intern_index(struct _ex_intern *ex, unsigned f, int t)
{
    unsigned hash = 0 ;
    struct _ex_intern *e ;

    /* Generate the hash value */
    hash %= (((unsigned) ex)/4+f+t)%index_parent_size ;

    /* First, try and find the value */
    e = current.index_parent[hash] ;
    while (e != NULL) {
        if (ex==e->u.index.exp && f==e->u.index.functor && t==e->u.index.term) return e ;
        e = e->next ;
    }

    /* Create a new entry if none exists */
    e = (struct _ex_intern *)_th_alloc(space, sizeof(struct _ex_base) + sizeof(unsigned) * 3) ;
    e->next = current.index_parent[hash] ;
    current.index_parent[hash] = e ;

    e->next_cache = e->rewrite = NULL ;
    e->find = e;
    e->type = EXP_INDEX ;
    e->has_special_term = ex->has_special_term ;
    e->no_top_var = 0 ;
    e->mark1 = 0 ;
    e->mark2 = 0 ;
    e->in_rewrite = e->in_backchain = 0 ;
    e->unmarked_term = NULL;
    e->marked_term = NULL;
    e->term_cache = NULL;
    e->is_marked_term = 0;
    e->rule_simplified = 0;
    e->rule_blocked = 0;
    e->user1 = NULL;
    e->user2 = e->user3 = NULL;
    e->unate_processed = e->unate_false = e->unate_true = 0 ;
	e->print_line = 0 ;
	e->used_level = 0 ;
    e->can_cache = ex->can_cache ;
    e->type_inst = ex->type_inst;
    e->prepare = ex->prepare;
    e->u.index.exp = ex ;
    e->u.index.functor = f ;
    e->u.index.term = t ;
    e->used_in = NULL;
    e->cache_bad = 0;
    e->cached_in = NULL;
    e->height = 0;
    e->sig = NULL;
    e->in_hash = 0;
    e->prev_term = e->next_term = NULL;
    e->explanation = NULL;
    e->merge = NULL;
    e->original = NULL;

#ifdef _DEBUG
    ++current.index_count ;
#endif

    return e ;
}

struct _ex_intern *_ex_intern_rational(unsigned *n, unsigned *d)
{
    unsigned hash = 0 ;
    unsigned i ;
    struct _ex_intern *e ;
    unsigned *accumulate;
    static unsigned one[2] = { 1, 1 };

    if (d[0]!=1 || d[1]!=1) {
        if (_th_big_is_negative(d)) {
            d = _th_big_copy(REWRITE_SPACE,_th_complement(d));
            n = _th_big_copy(REWRITE_SPACE,_th_complement(n));
        }
        if (n[0] != 1 || n[1] != 0) {
            accumulate = _th_big_gcd(n,d) ;
            n = _th_big_copy(REWRITE_SPACE,_th_big_divide(n,accumulate)) ;
            d = _th_big_copy(REWRITE_SPACE,_th_big_divide(d,accumulate)) ;
        } else {
            d = one;
        }
    }

    /* Generate the hash value */
    for (i = 0; i <= *n; ++i) hash += n[i] ;
    for (i = 0; i <= *d; ++i) hash += d[i] ;
    hash %= rational_parent_size ;

    /* First, try and find the value */
    e = current.rational_parent[hash] ;
    while (e!= NULL) {
        if (_th_big_equal(n, e->u.rational.numerator) &&
            _th_big_equal(d, e->u.rational.denominator)) return e ;
        e = e->next ;
    }

    /* Create a new entry if none exists */
    e = (struct _ex_intern *)_th_alloc(space, sizeof(struct _ex_base) + sizeof(unsigned) * 2) ;
    e->next = current.rational_parent[hash] ;
    current.rational_parent[hash] = e ;

    e->next_cache = e->rewrite = NULL ;
    e->find = e;
    e->type = EXP_RATIONAL ;
    e->has_special_term = 0 ;
    e->no_top_var = 0 ;
    e->mark1 = 0 ;
    e->mark2 = 0 ;
    e->in_rewrite = e->in_backchain = 0 ;
    e->unmarked_term = NULL;
    e->marked_term = NULL;
    e->term_cache = NULL;
    e->is_marked_term = 0;
    e->rule_simplified = 0;
    e->rule_blocked = 0;
    e->user1 = NULL;
    e->user2 = e->user3 = NULL;
    e->unate_processed = e->unate_false = e->unate_true = 0 ;
	e->print_line = 0 ;
	e->used_level = 0 ;
    e->can_cache = 1 ;
    e->u.rational.numerator = _th_big_copy(INTERN_SPACE,n) ;
    e->u.rational.denominator = _th_big_copy(INTERN_SPACE,d) ;
    e->type_inst = NULL;
    e->prepare = NULL;
    e->used_in = NULL;
    e->cache_bad = 0;
    e->cached_in = NULL;
    e->height = 0;
    e->sig = NULL;
    e->in_hash = 0;
    e->prev_term = current.last_term;
    e->next_term = NULL;
    e->explanation = NULL;
    e->merge = NULL;
    e->original = NULL;
    if (current.last_term) {
        current.last_term->next_term = e;
        current.last_term = e;
    } else {
        current.first_term = current.last_term = e;
    }

#ifdef _DEBUG
    ++current.rational_count ;
#endif

    return e ;
}

int is_not_side_effect_functor(unsigned f)
{
    if (!_th_do_context_rewrites) return 1 ;

    if (f==INTERN_GET_TERMS) return 0 ;
    if (f==INTERN_GET_CURRENT_TERM) return 0 ;
    if (f==INTERN_SPECIAL_REWRITES) return 0 ;
    if (f==INTERN_SPECIAL_REWRITES_USING) return 0 ;
    if (f==INTERN_GET_CONTEXT_RULES) return 0 ;

    return 1 ;
}

//int _ex_is_new;
struct _ex_intern *_ex_intern_appl(unsigned f,int count,struct _ex_intern **args)
{
    unsigned hash = f ;
    int i ;
    struct _ex_intern *e ;

#ifdef _DEBUG
    if (f==0 || f > ((unsigned)_th_intern_count())) {
        printf("Illegal constructor") ;
        f = 0 ;
        f = 1 / f ;
        exit(1) ;
    }
#endif

    /* Generate the hash value */
    for (i = 0; i < count; ++i) hash += ((unsigned)args[i])/4 ;
    hash %= appl_parent_size ;

    //_ex_is_new = 0;

    /* First, try and find the value */
    e = current.appl_parent[hash] ;
    while (e != NULL) {
        if (e->u.appl.count==count && e->u.appl.functor==f) {
            for (i = 0; i < count; ++i) {
                 if (e->u.appl.args[i]!=args[i]) goto cont ;
            }
            return e ;
        }
cont:
        e = e->next ;
    }

    /* Create a new entry if none exists */
    //_ex_is_new = 1;

    e = (struct _ex_intern *)_th_alloc(space, sizeof(struct _ex_base) + sizeof(unsigned *) * (2+count)) ;
    e->next = current.appl_parent[hash] ;
    current.appl_parent[hash] = e ;

    e->next_cache = e->rewrite = NULL ;
    e->find = e;
    e->type = EXP_APPL ;
    e->u.appl.functor = f ;
    e->u.appl.count = count ;
    e->has_special_term = 0 ;
    e->mark1 = 0 ;
    e->mark2 = 0 ;
    e->in_rewrite = e->in_backchain = 0 ;
    e->unmarked_term = 0;
    e->marked_term = NULL;
    e->term_cache = NULL;
    e->is_marked_term = 0;
    e->rule_simplified = 0;
    e->rule_blocked = 0;
    e->user1 = NULL;
    e->user2 = e->user3 = NULL;
    e->unate_processed = e->unate_false = e->unate_true = 0 ;
	e->print_line = 0 ;
	e->used_level = 0 ;
    e->can_cache = is_not_side_effect_functor(f) ;
    e->type_inst = NULL;
    e->prepare = NULL;
    e->rule_in_use = 0 ;
    e->used_in = NULL;
    e->cache_bad = 0;
    e->cached_in = NULL;
    e->height = 0;
    e->sig = NULL;
    e->in_hash = 0;
#ifdef _DEBUG
    e->rule_try_count = e->rule_use_count = 0 ;
#endif
    e->prev_term = current.last_term;
    e->next_term = NULL;
    e->explanation = NULL;
    e->merge = NULL;
    e->original = NULL;
    if (current.last_term) {
        current.last_term->next_term = e;
        current.last_term = e;
    } else {
        current.first_term = current.last_term = e;
    }
    for (i = 0; i < count; ++i) {
        if (args[i]->height+1 > e->height) {
            e->height = args[i]->height+1;
        }
        e->u.appl.args[i] = args[i] ;
        e->has_special_term = (e->has_special_term || args[i]->has_special_term) ;
        if (!args[i]->can_cache) e->can_cache = 0 ;
    }
    if (e->u.appl.functor==INTERN_NAT_PLUS || e->u.appl.functor==INTERN_RAT_PLUS ||
        e->u.appl.functor==INTERN_NAT_TIMES || e->u.appl.functor==INTERN_RAT_TIMES ||
        e->u.appl.functor==INTERN_NAT_DIVIDE || e->u.appl.functor==INTERN_RAT_DIVIDE) {
        --e->height;
    }
#ifdef _DEBUG
    ++current.appl_count ;
    current.appl_arg_count += count ;
#endif

    //printf("creating %s\n", _th_print_exp(e));

    return e ;
}

struct _ex_intern *_ex_find_equality(struct _ex_intern *left, struct _ex_intern *right)
{
    unsigned hash;
    //int i ;
    struct _ex_intern *e ;

    hash = (INTERN_EQUAL + (((unsigned)left)/4) + (((unsigned)right)/4))%appl_parent_size;

    e = current.appl_parent[hash] ;
    while (e != NULL) {
        if (e->u.appl.count==2 && e->u.appl.functor==INTERN_EQUAL) {
            if ((e->u.appl.args[0]==left && e->u.appl.args[1]==right) ||
                (e->u.appl.args[1]==left && e->u.appl.args[0]==right)) return e;
        }
        e = e->next ;
    }

    return NULL;
}

void _ex_add_used_in(struct _ex_intern *e)
{
    int i;

    //printf("Adding used in for %s\n", _th_print_exp(e));

    for (i = 0; i < e->u.appl.count; ++i) {
        struct add_list *al;
        //printf("parent_level = %d\n", parent_level);
        //printf("e->u.appl.args[%d] = %s\n", i, _th_print_exp(e->u.appl.args[i]));
        //printf("    used level %d\n", e->u.appl.args[i]->used_level);
        if (e->u.appl.args[i]->used_level < parent_level) {
            struct parent_updates *u = (struct parent_updates *)_th_alloc(INTERN_TEMP_SPACE,sizeof(struct parent_updates));
            u->next = parent_updates;
            parent_updates = u;
            u->e = e->u.appl.args[i];
            u->old_adds = e->u.appl.args[i]->used_in;
            u->old_parent_level = e->u.appl.args[i]->used_level;
            e->u.appl.args[i]->used_level = parent_level;
        }
        al = (struct add_list *)_th_alloc(INTERN_TEMP_SPACE,sizeof(struct add_list));
        al->next = e->u.appl.args[i]->used_in;
        e->u.appl.args[i]->used_in = al;
        al->e = e;
    }
}

struct _ex_intern *_ex_intern_string(char *s)
{
    unsigned hash = 0 ;
    struct _ex_intern *e ;
    char *t = s ;

    /* Generate the hash value */
    while (*t) {
        hash = hash + *t++ ;
        if (*t) hash = hash + ((*t++)<<8) ;
        if (*t) hash = hash + ((*t++)<<16) ;
        if (*t) hash = hash + ((*t++)<<24) ;
    }
    hash %= string_parent_size ;

    /* First, try and find the value */
    e = current.string_parent[hash] ;
    while (e!= NULL) {
        if (!strcmp(s,e->u.string)) return e ;
        e = e->next ;
    }

    /* Create a new entry if none exists */
    e = (struct _ex_intern *)_th_alloc(space, sizeof(struct _ex_base) + 1 + strlen(s)) ;
    e->next = current.string_parent[hash] ;
    current.string_parent[hash] = e ;

    e->next_cache = e->rewrite = NULL ;
    e->find = e;
    e->type = EXP_STRING ;
    e->has_special_term = 0 ;
    e->no_top_var = 0 ;
    e->mark1 = 0 ;
    e->mark2 = 0 ;
    e->in_rewrite = e->in_backchain = 0 ;
    e->unmarked_term = NULL;
    e->marked_term = NULL;
    e->term_cache = NULL;
    e->is_marked_term = 0;
    e->rule_simplified = 0;
    e->rule_blocked = 0;
    e->user1 = NULL;
    e->user2 = e->user3 = NULL;
    e->unate_processed = e->unate_false = e->unate_true = 0 ;
	e->print_line = 0 ;
	e->used_level = 0 ;
    e->can_cache = 1 ;
    e->type_inst = NULL;
    e->prepare = NULL;
    strcpy(e->u.string, s) ;
    e->used_in = NULL;
    e->cache_bad = 0;
    e->cached_in = NULL;
    e->height = 0;
    e->sig = NULL;
    e->in_hash = 0;
    e->prev_term = e->next_term = NULL;
    e->explanation = NULL;
    e->merge = NULL;
    e->original = NULL;

#ifdef _DEBUG
    ++current.string_count ;
#endif

    return e ;
}

static int cmp(const void *i1,const void *i2)
{
    return *((const int *)i2)-*((const int *)i1) ;
}

struct _ex_intern *_ex_intern_case(struct _ex_intern *exp,int count,struct _ex_intern **args)
{
    unsigned hash = 0 ;
    int i, j ;
    struct _ex_intern *e ;

    for (i = 0; i < count; ++i) {
         if (args[i*2]->type != EXP_APPL || args[i*2]->u.appl.count != 0) goto cont ;
    }
    for (i = 0; i < count; ++i) {
        for (j = 0; j < i; ++j) {
            if (args[i*2]->u.appl.functor==args[j*2]->u.appl.functor) goto cont ;
        }
    }
    qsort(args,count,sizeof(struct _ex_intern *)*2,cmp) ;
cont:

    /* Generate the hash value */
    for (i = 0; i < count*2; ++i) {
        _zone_print2("%d %d", i, args[i]) ;
        hash += ((unsigned)args[i])/4 ;
    }
    hash += ((unsigned)exp)/4;
    hash %= case_parent_size ;
    /* First, try and find the value */
    e = current.case_parent[hash] ;
    while (e != NULL) {
        if (e->u.case_stmt.count==count && e->u.case_stmt.exp==exp){
            for (i = 0; i < count*2; ++i) {
                if (e->u.case_stmt.args[i]!=args[i]) goto cont2 ;
            }
            return e ;
        }
cont2:
        e = e->next ;
    }

    e = (struct _ex_intern *)_th_alloc(space, sizeof(struct _ex_base) + sizeof(struct _ex_intern *) * (count*2+1)+sizeof(unsigned)) ;
    e->next = current.case_parent[hash] ;
    current.case_parent[hash] = e ;
    e->next_cache = e->rewrite = NULL ;
    e->find = e;
    e->type = EXP_CASE ;
    e->u.case_stmt.exp = exp ;
    e->u.case_stmt.count = count ;
    e->has_special_term = 0 ;
    e->no_top_var = 0 ;
    e->mark1 = 0 ;
    e->mark2 = 0 ;
    e->in_rewrite = e->in_backchain = 0 ;
    e->unmarked_term = 0;
    e->marked_term = NULL;
    e->term_cache = NULL;
    e->is_marked_term = 0;
    e->rule_simplified = 0;
    e->rule_blocked = 0;
    e->user1 = NULL;
    e->user2 = e->user3 = NULL;
    e->unate_processed = e->unate_false = e->unate_true = 0 ;
	e->print_line = 0 ;
	e->used_level = 0 ;
    e->can_cache = 1 ;
    e->type_inst = NULL;
    e->prepare = NULL;
    e->used_in = NULL;
    e->cache_bad = 0;
    e->cached_in = NULL;
    e->height = 0;
    e->sig = NULL;
    e->in_hash = 0;
    e->prev_term = e->next_term = NULL;
    e->explanation = NULL;
    e->merge = NULL;
    e->original = NULL;

    for (i = 0; i < count*2; ++i) {
        e->u.case_stmt.args[i] = args[i] ;
        if (!args[i]->can_cache) e->can_cache = 0 ;
        if (i%2==0 && e->has_special_term==0) {
            e->has_special_term = (args[i]->type != EXP_APPL || args[i]->u.appl.count != 0) ;
        }
    }

#ifdef _DEBUG
    ++current.case_count ;
#endif

    return e ;
}

struct _ex_intern *_ex_intern_quant(unsigned quant,int count,unsigned *args,struct _ex_intern *exp,struct _ex_intern *cond)
{
    int i ;
    unsigned hash ;
    struct _ex_intern *e ;

    /**********/

    /* Generate the hash value */
    hash = ((unsigned)exp)/4+((unsigned)cond)/4 ;
    for (i = 0; i < count; ++i) hash += args[i] ;
    hash %= quant_parent_size ;

    //for (i = 0; i < count; ++i) {
    //    if (args[i]==0) {
    //        i = i+1/args[i] ;
    //    }
    //}

    /* First, try and find the value */
    e = current.quant_parent[hash] ;
    while (e != NULL) {
        if (e->u.quant.quant==quant && e->u.quant.var_count==count && e->u.quant.exp==exp && e->u.quant.cond==cond){
            for (i = 0; i < count; ++i) {
                if (e->u.quant.vars[i]!=args[i]) goto cont ;
            }
            return e ;
        }
cont:
        e = e->next ;
    }

    e = (struct _ex_intern *)_th_alloc(space, sizeof(struct _ex_base) + sizeof(struct _ex_intern *)*2 + sizeof(unsigned)*(2+count)) ;
    e->next = current.quant_parent[hash] ;
    current.quant_parent[hash] = e ;

    e->next_cache = e->rewrite = NULL ;
    e->find = e;
    e->type = EXP_QUANT ;
    e->has_special_term = 1 ;
    e->no_top_var = 0 ;
    e->mark1 = 0 ;
    e->mark2 = 0 ;
    e->in_rewrite = e->in_backchain = 0 ;
    e->unmarked_term = NULL;
    e->marked_term = NULL;
    e->term_cache = NULL;
    e->is_marked_term = 0;
    e->rule_simplified = 0;
    e->rule_blocked = 0;
    e->user1 = NULL;
    e->user2 = e->user3 = NULL;
    e->unate_processed = e->unate_false = e->unate_true = 0 ;
	e->print_line = 0 ;
	e->used_level = 0 ;
    e->can_cache = 1 ;
    e->type_inst = NULL;
    e->prepare = NULL;
    if (!exp->can_cache) e->can_cache = 0 ;
    if (!cond->can_cache) e->can_cache = 0 ;
    e->u.quant.quant = quant ;
    e->u.quant.exp = exp ;
    e->u.quant.cond = cond ;
    e->u.quant.var_count = count ;
    e->used_in = NULL;
    e->cache_bad = 0;
    e->cached_in = NULL;
    e->height = 0;
    e->sig = NULL;
    e->prev_term = current.last_term;
    e->next_term = NULL;
    e->explanation = NULL;
    e->merge = NULL;
    e->original = NULL;
    e->in_hash = 0;
    if (current.last_term) {
        current.last_term->next_term = e;
        current.last_term = e;
    } else {
        current.first_term = current.last_term = e;
    }
    for (i = 0; i < count; ++i) {
        e->u.quant.vars[i] = args[i] ;
    }

#ifdef _DEBUG
    ++current.quant_count ;
#endif

    return e ;
}

GDEF("modifies _ex_push push_level");
GDEF("modifies _ex_push save");
GDEF("modifies _ex_push current");
GDEF("modifies _ex_push space");
GDEF("post _ex_push save==current@pre");
GDEF("post _ex_push _ex_set==_ex_set@pre");

void _ex_push()
{
    int i ;

    ++push_level ;
    if (push_level==1) {
        space = INTERN_TEMP_SPACE ;
        save = current ;
        temp_space_mark = _th_alloc_mark(INTERN_TEMP_SPACE) ;
        current.integer_parent = (struct _ex_intern **)MALLOC(integer_parent_size * sizeof(struct _ex_intern *)) ;
        for (i = 0; i < integer_parent_size; ++i) current.integer_parent[i] = save.integer_parent[i] ;
        current.string_parent = (struct _ex_intern **)MALLOC(string_parent_size * sizeof(struct _ex_intern *)) ;
        for (i = 0; i < string_parent_size; ++i) current.string_parent[i] = save.string_parent[i] ;
        current.rational_parent = (struct _ex_intern **)MALLOC(rational_parent_size * sizeof(struct _ex_intern *)) ;
        for (i = 0; i < rational_parent_size; ++i) current.rational_parent[i] = save.rational_parent[i] ;
        current.appl_parent = (struct _ex_intern **)MALLOC(appl_parent_size * sizeof(struct _ex_intern **)) ;
        for (i = 0; i < appl_parent_size; ++i) current.appl_parent[i] = save.appl_parent[i] ;
        current.case_parent = (struct _ex_intern **)MALLOC(case_parent_size * sizeof(struct _ex_intern **)) ;
        for (i = 0; i < case_parent_size; ++i) current.case_parent[i] = save.case_parent[i] ;
        current.quant_parent = (struct _ex_intern **)MALLOC(quant_parent_size * sizeof(struct _ex_intern **)) ;
        for (i = 0; i < quant_parent_size; ++i) current.quant_parent[i] = save.quant_parent[i] ;
        current.var_parent = (struct _ex_intern **)MALLOC(var_parent_size * sizeof(struct _ex_intern **)) ;
        for (i = 0; i < var_parent_size; ++i) current.var_parent[i] = save.var_parent[i] ;
        current.marked_var_parent = (struct _ex_intern **)MALLOC(marked_var_parent_size * sizeof(struct _ex_intern **)) ;
        for (i = 0; i < marked_var_parent_size; ++i) current.marked_var_parent[i] = save.marked_var_parent[i] ;
        current.index_parent = (struct _ex_intern **)MALLOC(index_parent_size * sizeof(struct _ex_intern **)) ;
        for (i = 0; i < index_parent_size; ++i) current.index_parent[i] = save.index_parent[i] ;
    }
}

void _ex_pop()
{
    --push_level ;
    if (push_level==0) {
        space = INTERN_SPACE ;
        deleted = current ;
        current = save ;

#ifdef _DEBUG
        if (deleted.appl_arg_count > appl_arg_count) appl_arg_count = deleted.appl_arg_count ;
        if (deleted.appl_count > appl_count) appl_count = deleted.appl_count ;
        if (deleted.case_count > case_count) case_count = deleted.case_count ;
        if (deleted.index_count > index_count) index_count = deleted.index_count ;
        if (deleted.integer_count > integer_count) integer_count = deleted.integer_count ;
        if (deleted.marked_var_count > marked_var_count) marked_var_count = deleted.marked_var_count ;
        if (deleted.quant_count > quant_count) quant_count = deleted.quant_count ;
        if (deleted.rational_count > rational_count) rational_count = deleted.rational_count ;
        if (deleted.string_count > string_count) string_count = deleted.string_count ;
        if (deleted.var_count > var_count) var_count = deleted.var_count ;
#endif
    }
}

void _ex_release()
{
    _th_alloc_release(INTERN_TEMP_SPACE,temp_space_mark) ;
    FREE(deleted.appl_parent) ;
    FREE(deleted.case_parent) ;
    FREE(deleted.index_parent) ;
    FREE(deleted.integer_parent) ;
    FREE(deleted.marked_var_parent) ;
    FREE(deleted.quant_parent) ;
    FREE(deleted.rational_parent) ;
    FREE(deleted.string_parent) ;
    FREE(deleted.var_parent) ;
}

struct _ex_intern *_ex_reintern(struct env *env, struct _ex_intern *e)
{
    int i ;
    struct _ex_intern *cond, *exp ;
    struct _ex_intern **args ;

    switch (e->type) {
        case EXP_INTEGER:
            return _ex_intern_integer(e->u.integer) ;
        case EXP_VAR:
            return _ex_intern_var(e->u.var) ;
        case EXP_MARKED_VAR:
            return _ex_intern_marked_var(e->u.marked_var.var,e->u.marked_var.quant_level) ;
        case EXP_STRING:
            return _ex_intern_string(e->u.string) ;
        case EXP_RATIONAL:
            return _ex_intern_rational(e->u.rational.numerator,e->u.rational.denominator) ;
        case EXP_QUANT:
            exp = _ex_reintern(env, e->u.quant.exp) ;
            cond = _ex_reintern(env, e->u.quant.cond) ;
            return _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,e->u.quant.vars,exp,cond) ;
        case EXP_INDEX:
            exp = _ex_reintern(env,e->u.index.exp) ;
            return _ex_intern_index(exp,e->u.index.functor,e->u.index.term) ;
        case EXP_APPL:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = _ex_reintern(env,e->u.appl.args[i]) ;
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args) ;
        case EXP_CASE:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.case_stmt.count * 2) ;
            exp = _ex_reintern(env,e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
                args[i] = _ex_reintern(env,e->u.case_stmt.args[i]) ;
            }
            return _ex_intern_case(exp,e->u.case_stmt.count,args) ;
    }
    return NULL ;
}

void _ex_init()
{
    int i ;

    space = INTERN_SPACE ;
    push_level = 0 ;

    parent_stack = NULL;
    parent_level = 1;

    current.integer_parent = (struct _ex_intern **)MALLOC(integer_parent_size * sizeof(struct _ex_intern *)) ;
    for (i = 0; i < integer_parent_size; ++i) current.integer_parent[i] = NULL ;
    current.string_parent = (struct _ex_intern **)MALLOC(string_parent_size * sizeof(struct _ex_intern *)) ;
    for (i = 0; i < string_parent_size; ++i) current.string_parent[i] = NULL ;
    current.rational_parent = (struct _ex_intern **)MALLOC(rational_parent_size * sizeof(struct _ex_intern *)) ;
    for (i = 0; i < rational_parent_size; ++i) current.rational_parent[i] = NULL ;
    current.appl_parent = (struct _ex_intern **)MALLOC(appl_parent_size * sizeof(struct _ex_intern **)) ;
    for (i = 0; i < appl_parent_size; ++i) current.appl_parent[i] = NULL ;
    current.case_parent = (struct _ex_intern **)MALLOC(case_parent_size * sizeof(struct _ex_intern **)) ;
    for (i = 0; i < case_parent_size; ++i) current.case_parent[i] = NULL ;
    current.quant_parent = (struct _ex_intern **)MALLOC(quant_parent_size * sizeof(struct _ex_intern **)) ;
    for (i = 0; i < quant_parent_size; ++i) current.quant_parent[i] = NULL ;
    current.var_parent = (struct _ex_intern **)MALLOC(var_parent_size * sizeof(struct _ex_intern **)) ;
    for (i = 0; i < var_parent_size; ++i) current.var_parent[i] = NULL ;
    current.marked_var_parent = (struct _ex_intern **)MALLOC(marked_var_parent_size * sizeof(struct _ex_intern **)) ;
    for (i = 0; i < marked_var_parent_size; ++i) current.marked_var_parent[i] = NULL ;
    current.index_parent = (struct _ex_intern **)MALLOC(index_parent_size * sizeof(struct _ex_intern **)) ;
    for (i = 0; i < index_parent_size; ++i) current.index_parent[i] = NULL ;
    current.first_term = current.last_term = NULL;

#ifdef DEBUG
    current.integer_count = 0 ;
    current.rational_count = 0 ;
    current.appl_count = 0 ;
    current.appl_arg_count = 0;
    current.case_count = 0 ;
    current.quant_count = 0 ;
    current.var_count = 0 ;
    current.marked_var_count = 0 ;
    current.index_count = 0 ;
    current.string_count = 0 ;
    integer_count = 0 ;
    rational_count = 0 ;
    appl_count = 0 ;
    appl_arg_count = 0;
    case_count = 0 ;
    quant_count = 0 ;
    var_count = 0 ;
    marked_var_count = 0 ;
    index_count = 0 ;
    string_count = 0 ;
#endif

    _ex_true = _ex_intern_appl(INTERN_TRUE,0,NULL) ;
    _ex_false = _ex_intern_appl(INTERN_FALSE,0,NULL) ;
    _ex_nil = _ex_intern_appl(INTERN_NIL,0,NULL) ;
    _ex_bool = _ex_intern_appl(INTERN_BOOL,0,NULL) ;
    _ex_int = _ex_intern_appl(INTERN_INT,0,NULL) ;
    _ex_real = _ex_intern_appl(INTERN_REAL,0,NULL) ;
    _ex_array = _ex_intern_appl(INTERN_CAP_ARRAY,0,NULL) ;
    _ex_one = _ex_intern_small_integer(1);
    _ex_r_one = _ex_intern_small_rational(1,1);
}

void _ex_shutdown()
{
#ifdef _DEBUG
    printf("\nExpression allocation statistics:\n\n") ;
    printf("    integers:                  %d (%d)\n", current.integer_count, integer_count) ;
    printf("    rationals:                 %d (%d)\n", current.rational_count, rational_count) ;
    printf("    Function applications:     %d (%d)\n", current.appl_count, appl_count) ;
    printf("    Function application args: %d (%d)\n", current.appl_arg_count, appl_arg_count) ;
    printf("    Case statements:           %d (%d)\n", current.case_count, case_count) ;
    printf("    Quantifier expressions:    %d (%d)\n", current.quant_count, quant_count) ;
    printf("    Variables:                 %d (%d)\n", current.var_count, var_count) ;
    printf("    Marked variables:          %d (%d)\n", current.marked_var_count, marked_var_count) ;
    printf("    Index count:               %d (%d)\n", current.index_count, index_count) ;
    printf("    String count:              %d (%d)\n", current.string_count, string_count) ;
#endif
}

void _ex_add_term(struct _ex_intern *e)
{
    if (current.first_term==e || e->prev_term) return;

    e->prev_term = current.last_term;
    e->next_term = NULL;
    if (current.last_term) {
        current.last_term->next_term = e;
        current.last_term = e;
    } else {
        current.first_term = current.last_term = e;
    }
}

void _ex_delete_term(struct _ex_intern *e)
{
    if (current.first_term!=e && !e->prev_term) return;

    if (e->prev_term) {
        e->prev_term->next_term = e->next_term;
    } else {
        current.first_term = e->next_term;
    }
    if (e->next_term) {
        e->next_term->prev_term = e->prev_term;
    } else {
        current.last_term = e->prev_term;
    }
    e->prev_term = e->next_term = NULL;
}

struct _ex_intern *_ex_get_first_term()
{
    return current.first_term;
}

int _ex_valid_expression(struct _ex_intern *e)
{
    int i ;
    struct _ex_intern *exp ;
    struct _ex_intern **args ;

    switch (e->type) {
        case EXP_INTEGER:
            return _ex_intern_integer(e->u.integer)==e ;
        case EXP_VAR:
            return _ex_intern_var(e->u.var)==e ;
        case EXP_MARKED_VAR:
            return _ex_intern_marked_var(e->u.marked_var.var,e->u.marked_var.quant_level)==e ;
        case EXP_STRING:
            return _ex_intern_string(e->u.string)==e ;
        case EXP_RATIONAL:
            return _ex_intern_rational(e->u.rational.numerator,e->u.rational.denominator)==e ;
        case EXP_QUANT:
            return _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,e->u.quant.vars,e->u.quant.exp,e->u.quant.cond)==e ;
        case EXP_INDEX:
            return _ex_intern_index(e->u.index.exp,e->u.index.functor,e->u.index.term)==e ;
        case EXP_APPL:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = e->u.appl.args[i] ;
            }
            return _ex_intern_appl(e->u.appl.functor,e->u.appl.count,args)==e ;
        case EXP_CASE:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.case_stmt.count * 2) ;
            exp = e->u.case_stmt.exp ;
            for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
                args[i] = e->u.case_stmt.args[i] ;
            }
            return _ex_intern_case(exp,e->u.case_stmt.count,args)==e ;
    }
    return 0 ;
}
