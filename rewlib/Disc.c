/*
 * disc.c
 *
 * Discrimination net utilities.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include "Globals.h"
#include "Intern.h"

#define SMALL_HASH 251

struct small_disc {
        struct small_rule *rules[SMALL_HASH] ;
    } ;

struct small_rule {
        struct small_rule *next ;
        struct _ex_intern *rule ;
        unsigned tested_cycle ;
        unsigned used_cycle ;
        unsigned level ;
        int priority ;
    } ;

struct small_disc *_th_new_small(int s)
{
    struct small_disc *d = (struct small_disc *)_th_alloc(s,sizeof(struct small_disc)) ;
    int i ;

    for (i = 0; i < SMALL_HASH; ++i) {
        d->rules[i] = NULL ;
    }

    return d ;
}

static struct small_rule *_copy_rules(int s,struct small_rule *r)
{
    struct small_rule *res ;

    if (r==NULL) return NULL ;

    res = (struct small_rule *)_th_alloc(s,sizeof(struct small_rule)) ;
    res->next = _copy_rules(s,r->next) ;
    res->rule = r->rule ;
    res->priority = r->priority ;

    return res ;
}

struct small_disc *_th_copy_small(int s, struct small_disc *d)
{
    struct small_disc *n = (struct small_disc *)_th_alloc(s,sizeof(struct small_disc)) ;
    int i ;

    for (i = 0; i < SMALL_HASH; ++i) {
        n->rules[i] = _copy_rules(s,d->rules[i]) ;
    }

    return n ;
}

struct small_disc *_th_push_small(int s, struct small_disc *d)
{
    struct small_disc *n = (struct small_disc *)_th_alloc(s,sizeof(struct small_disc)) ;
    int i ;

    for (i = 0; i < SMALL_HASH; ++i) {
        n->rules[i] = d->rules[i] ;
    }

    return n ;
}

static unsigned _get_hash(struct _ex_intern *e)
{
    unsigned v ;
    char *c ;
    switch (e->type) {
        case EXP_INTEGER:
            v = e->u.integer[1] ;
            break ;
        case EXP_RATIONAL:
            v = e->u.rational.numerator[1] + e->u.rational.denominator[1] ;
            break ;
        case EXP_STRING:
            c = e->u.string ;
            v = 0 ;
            while (*c) {
                v += *c ;
                ++c ;
            }
            break ;
        case EXP_APPL:
            v = e->u.appl.functor ;
            break ;
        case EXP_CASE:
            v = 0 ;
            break ;
        case EXP_QUANT:
            v = e->u.quant.quant ;
            break ;
        case EXP_VAR:
            v = e->u.var ;
            break ;
        case EXP_MARKED_VAR:
            v = e->u.marked_var.var ;
            break ;
        case EXP_INDEX:
            v = 1 ;
            break ;
    }
    return v%SMALL_HASH;
}

int _th_add_small(int s,struct env *env,struct small_disc *d,struct _ex_intern *e, int priority)
{
    int h ;
    struct small_rule *r ;

#ifdef _DEBUG
    if (e->type != EXP_APPL || e->u.appl.count != 3) {
        printf("Illegal rule\n") ;
        exit(1) ;
    }
#endif
    h = _get_hash(e->u.appl.args[0]) ;
    r = d->rules[h] ;
    while (r != NULL) {
        if (r->rule==e && priority >= r->priority) {
            return 0 ;
        }
        r = r->next ;
    }
    r = (struct small_rule *)_th_alloc(s,sizeof(struct small_rule)) ;
    r->next = d->rules[h] ;
    d->rules[h] = r ;
    r->rule = e ;
    r->priority = priority ;
    r->level = _th_context_level ;

    return 1 ;
}

struct _ex_intern *_th_get_small_set(struct env *env, struct small_disc *d)
{
    int count, i ;
    struct small_rule *r ;
    struct _ex_intern **args ;

    count = 0 ;
    for (i = 0; i < SMALL_HASH; ++i) {
        r = d->rules[i] ;
        while (r) {
            ++count ;
            r = r->next ;
        }
    }

    args = ALLOCA(sizeof(struct _ex_intern *) * count) ;
    count = 0 ;
    for (i = 0; i < SMALL_HASH; ++i) {
        r = d->rules[i] ;
        while (r) {
            args[count++] =  r->rule ;
            r = r->next ;
        }
    }

    return _ex_intern_appl_env(env,INTERN_SET,count,args) ;
}

void _th_init_find_small(struct small_disc *d,struct _ex_intern *e,void **r)
{
    *r = d->rules[_get_hash(e)] ;
}

struct _ex_intern *_th_next_find_small(void **r, int *p)
{
    struct small_rule *n ;

    if (*r == NULL) return NULL ;

    n = (struct small_rule *)*r ;
    *r = (void *)((struct small_rule *)*r)->next ;

    if (p != NULL) *p = n->priority ;
    return n->rule ;
}

void _th_disc_mark_tested(struct small_disc *d, struct _ex_intern *rule)
{
    int h = _get_hash(rule->u.appl.args[0]) ;

    struct small_rule *r = d->rules[h] ;

    while (r != NULL) {
        if (r->rule==rule) {
            int l = _th_context_level ;
            if (l >= MAX_LEVELS) l = MAX_LEVELS-1 ;
            _th_context_any_tested = _th_cycle ;
            _th_context_tested[l] = _th_cycle ;
            r->tested_cycle = _th_cycle ;
            return ;
        }
        r = r->next ;
    }

    printf("Illegal test mark %s\n", _th_print_exp(rule)) ;
    exit(1) ;
}

void _th_disc_mark_used(struct small_disc *d, struct _ex_intern *rule)
{
    int h = _get_hash(rule->u.appl.args[0]) ;

    struct small_rule *r = d->rules[h] ;

    while (r != NULL) {
        if (r->rule==rule) {
            int l = _th_context_level ;
            if (l >= MAX_LEVELS) l = MAX_LEVELS-1 ;
            _th_context_any_used = _th_cycle ;
            _th_context_used[l] = _th_cycle ;
            r->used_cycle = _th_cycle ;
            return ;
        }
        r = r->next ;
    }

    printf("Illegal use mark %s\n", _th_print_exp(rule)) ;
    exit(1) ;
}

#define MAX_TRACE MAX_ARGS+1

static unsigned *trace = NULL ;
static int trace_alloc_size = 0 ;
static int trace_size ;

static void check_trace_size(int size)
{
    if (size > trace_alloc_size) {
        trace_alloc_size = size + 500 ;
        if (trace ==NULL) {
            trace = (unsigned *)MALLOC(sizeof(unsigned) * trace_alloc_size) ;
        } else {
            trace = (unsigned *)REALLOC(trace, sizeof(unsigned) * trace_alloc_size) ;
        }
    }
}

/*static int _th_is_ac(unsigned s)
{
    return s==INTERN_AND||s==INTERN_OR||s==INTERN_NAT_PLUS||s==INTERN_RAT_PLUS||
           s==INTERN_NAT_TIMES||s==INTERN_RAT_TIMES;
}*/

static unsigned _make_item(struct _ex_intern *e)
{
    int v ;

    /**********/

    v = (e->type<<16) ;
    switch (e->type) {
        case EXP_APPL:
            if (e==_ex_true || e==_ex_false) return 0;
            if (e->u.appl.functor==INTERN_UNORIENTED_RULE)
            {
                v += INTERN_ORIENTED_RULE ;
            }
            else
            {
                v += e->u.appl.functor ;
            }
            break ;
        case EXP_QUANT:
            v += e->u.quant.quant ;
            break ;
        case EXP_MARKED_VAR:
        case EXP_VAR:
            v = 0 ;
            break ;
    }
    return v ;
}

static void _make_trace(struct _ex_intern *e)
{
    int i ;
    unsigned v,s ;

    /**********/

    check_trace_size(5) ;
    trace[0] = _make_item(e) ;
    trace_size = 1 ;
    switch (e->type) {
        case EXP_APPL:
            s = 0 ;
            check_trace_size(5+e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                v = _make_item(e->u.appl.args[i]) ;
                if (v != 0) {
                    if (s==0 || v < s) {
                        s = v ;
                    }
                }
            }
            if (s != 0) trace[trace_size++] = s ;
            break ;
        case EXP_QUANT:
            v = _make_item(e->u.quant.exp) ;
            s = _make_item(e->u.quant.cond) ;
            if (v == 0) {
                if (s != 0) trace[trace_size++] = s ;
            } else {
                if (s != 0 && s < v) {
                    trace[trace_size++] = s ;
                } else {
                    trace[trace_size++] = v ;
                }
            }
            break ;
        case EXP_VAR:
        case EXP_MARKED_VAR:
            trace_size = 0 ;
            break ;
    }
}

static void _make_find_trace(struct _ex_intern *e)
{
    int i ;
    unsigned v ;

    /**********/

    check_trace_size(5) ;
    trace[0] = _make_item(e) ;
    trace_size = 1 ;
    switch (e->type) {
        case EXP_APPL:
            check_trace_size(e->u.appl.count + 3) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                v = _make_item(e->u.appl.args[i]) ;
                if (v != 0) trace[trace_size++] = v ;
            }
            break ;
        case EXP_QUANT:
            v = _make_item(e->u.quant.exp) ;
            if (v != 0) trace[trace_size++] = v ;
            v = _make_item(e->u.quant.cond) ;
            if (v != 0) trace[trace_size++] = v ;
            break ;
        case EXP_VAR:
        case EXP_MARKED_VAR:
            trace_size = 0 ;
            break ;
    }
}

#define MAJOR_TABLE_SIZE 997
#define MINOR_TABLE_SIZE 23

struct rest_disc {
        unsigned symbol ;
        struct rest_disc *next ;
        struct small_rule *rules ;
        struct rest_disc *rest_discs[MINOR_TABLE_SIZE] ;
    } ;

struct disc {
        struct small_rule *rules ;
        struct rest_disc *rest_discs[MAJOR_TABLE_SIZE] ;
    } ;

void _priority_range(struct rest_disc *d, int *min, int *max)
{
    int i ;
    struct small_rule *r ;

    if (d==NULL) return ;

    r = d->rules ;
    while (r != NULL) {
        if (r->priority < *min) *min = r->priority ;
        if (r->priority > *max) *max = r->priority ;
        r = r->next ;
    }

    for (i = 0; i < MINOR_TABLE_SIZE; ++i) {
        _priority_range(d->rest_discs[i], min, max) ;
    }
}

void _th_priority_range(struct disc *d, int *min, int *max)
{
    int i ;
    struct small_rule *r ;

    *min = *max = 0;

    if (d==NULL) return ;

    r = d->rules ;
    while (r != NULL) {
        if (r->priority < *min) *min = r->priority ;
        if (r->priority > *max) *max = r->priority ;
        r = r->next ;
    }

    for (i = 0; i < MAJOR_TABLE_SIZE; ++i) {
        _priority_range(d->rest_discs[i], min, max) ;
    }
}

_th_print_disc(struct disc *d)
{
    int i, j ;
    struct small_rule *r ;
    struct rest_disc *rd, *rd1 ;
    printf("Discrimination net:\n") ;
    printf("    Rules:\n") ;
    r = d->rules ;
    while(r != NULL) {
        printf("        %d %s\n", r->priority, _th_print_exp(r->rule)) ;
        r = r->next ;
    }
    for (i = 0; i < MAJOR_TABLE_SIZE; ++i) {
        if (d->rest_discs[i] != NULL) {
            printf("    Bin %d\n", i) ;
            rd = d->rest_discs[i] ;
            while(rd != NULL) {
                printf("        Disc: %s\n", _th_intern_decode(rd->symbol & 0xffff)) ;
                printf("        Rules:\n") ;
                r = rd->rules ;
                while(r != NULL) {
                    printf("            %s\n", _th_print_exp(r->rule)) ;
                    r = r->next ;
                }
                for (j = 0; j < MINOR_TABLE_SIZE; ++j) {
                    if (rd->rest_discs[j] != NULL) {
                        printf("            Bin %d\n", j) ;
                        rd1 = rd->rest_discs[j] ;
                        while(rd1 != NULL) {
                            printf("                Disc: %s\n", _th_intern_decode(rd1->symbol & 0xffff)) ;
                            printf("                Rules:\n") ;
                            r = rd1->rules ;
                            while(r != NULL) {
                                printf("                    %d %s\n", r->priority, _th_print_exp(r->rule)) ;
                                r = r->next ;
                            }
                            rd1 = rd1->next ;
                        }
                    }
                }
                rd = rd->next ;
            }
        }
    }
}

_th_tree_print_disc(struct disc *d)
{
    int i, j ;
    struct small_rule *r ;
    struct rest_disc *rd, *rd1 ;
    _zone_print0("Discrimination net:") ;
    _tree_indent();
    _zone_print0("Rules:") ;
    r = d->rules ;
    _tree_indent();
    while(r != NULL) {
        _zone_print2("%d %s", r->priority, _th_print_exp(r->rule)) ;
        r = r->next ;
    }
    _tree_undent();
    for (i = 0; i < MAJOR_TABLE_SIZE; ++i) {
        if (d->rest_discs[i] != NULL) {
            _zone_print1("Bin %d", i) ;
            rd = d->rest_discs[i] ;
            _tree_indent();
            while(rd != NULL) {
                _zone_print1("Disc: %s", _th_intern_decode(rd->symbol & 0xffff)) ;
                _zone_print0("Rules:") ;
                r = rd->rules ;
                _tree_indent();
                while(r != NULL) {
                    _zone_print_exp("r->rule", r->rule) ;
                    r = r->next ;
                }
                for (j = 0; j < MINOR_TABLE_SIZE; ++j) {
                    if (rd->rest_discs[j] != NULL) {
                        _zone_print1("Bin %d\n", j) ;
                        rd1 = rd->rest_discs[j] ;
                        _tree_indent();
                        while(rd1 != NULL) {
                            _zone_print1("Disc: %s", _th_intern_decode(rd1->symbol & 0xffff)) ;
                            _zone_print0("Rules:") ;
                            r = rd1->rules ;
                            _tree_indent();
                            while(r != NULL) {
                                _zone_print2("%d %s", r->priority, _th_print_exp(r->rule)) ;
                                r = r->next ;
                            }
                            _tree_undent();
                            rd1 = rd1->next ;
                        }
                        _tree_undent();
                    }
                }
                _tree_undent();
                rd = rd->next ;
            }
            _tree_undent();
        }
    }
    _tree_undent();
}

static struct rest_disc *_copy_rest_disc(int s, struct rest_disc *d)
{
    struct rest_disc *n ;
    int i ;

    if (d == NULL) return NULL ;

    n = (struct rest_disc *)_th_alloc(s, sizeof(struct rest_disc)) ;

    n->symbol = d->symbol ;
    n->next = _copy_rest_disc(s, d->next) ;
    n->rules = _copy_rules(s, d->rules) ;

    for (i = 0; i < MINOR_TABLE_SIZE; ++i) {
        n->rest_discs[i] = _copy_rest_disc(s, d->rest_discs[i]) ;
    }

    return n ;
}

struct disc *_th_copy_disc(int s, struct disc *d)
{
    struct disc *n ;
    int i ;

    if (d == NULL) return NULL ;

    n = (struct disc *)_th_alloc(s, sizeof(struct disc)) ;
    n->rules = _copy_rules(s, d->rules) ;

    for (i = 0; i < MAJOR_TABLE_SIZE; ++i) {
        n->rest_discs[i] = _copy_rest_disc(s, d->rest_discs[i]) ;
    }

    return n ;
}

struct rest_disc *_new_rest_disc(int s)
{
    struct rest_disc *d = (struct rest_disc *)_th_alloc(s, sizeof(struct rest_disc)) ;
    int i ;

    d->next = NULL ;
    d->rules = NULL ;
    for (i = 0; i < MINOR_TABLE_SIZE; ++i) d->rest_discs[i] = 0 ;

    return d ;
}

struct disc *_th_new_disc(int s)
{
    struct disc *d = (struct disc *)_th_alloc(s, sizeof(struct disc)) ;
    int i ;

    d->rules = NULL ;
    for (i = 0; i < MAJOR_TABLE_SIZE; ++i) d->rest_discs[i] = 0 ;

    return d ;
}

void _th_add_disc(int s,struct disc *disc, struct _ex_intern *e, int priority)
{
    struct rest_disc *rd, *rd1 ;
    struct small_rule *r ;
    int i ;

    if (e->type != EXP_APPL || e->u.appl.count != 3) {
        printf("Illegal rule format 1 %s\n", _th_print_exp(e)) ;
        exit(1) ;
    }
    _make_trace(e->u.appl.args[0]) ;

    if (trace_size==0) {
        r = (struct small_rule *)_th_alloc(s,sizeof(struct small_rule)) ;
        r->next = disc->rules ;
        disc->rules = r ;
        r->rule = e ;
        r->priority = priority ;
        return ;
    }
    rd = disc->rest_discs[trace[0]%MAJOR_TABLE_SIZE] ;
    while (rd && rd->symbol != trace[0]) rd = rd->next ;

    if (rd == NULL) {
        rd = _new_rest_disc(s) ;
        rd->next = disc->rest_discs[trace[0]%MAJOR_TABLE_SIZE] ;
        disc->rest_discs[trace[0]%MAJOR_TABLE_SIZE] = rd ;
        rd->symbol = trace[0] ;
    }

    if (trace_size==1) {
        r = (struct small_rule *)_th_alloc(s,sizeof(struct small_rule)) ;
        r->next = rd->rules ;
        rd->rules = r ;
        r->rule = e ;
        r->priority = priority ;
    }

    for (i = 1; i < trace_size; ++i) {
        rd1 = rd->rest_discs[trace[i]%MINOR_TABLE_SIZE] ;
        while (rd1 && rd1->symbol != trace[i]) rd1 = rd1->next ;
        if (rd1 == NULL) {
            rd1 = _new_rest_disc(s) ;
            rd1->next = rd->rest_discs[trace[i]%MINOR_TABLE_SIZE] ;
            rd->rest_discs[trace[i]%MINOR_TABLE_SIZE] = rd1 ;
            rd1->symbol = trace[i] ;
        }
        r = (struct small_rule *)_th_alloc(s,sizeof(struct small_rule)) ;
        r->next = rd1->rules ;
        rd1->rules = r ;
        r->rule = e ;
        r->priority = priority ;
    }
}

void _th_init_find(struct disc_iterator *iterator, struct disc *d, struct _ex_intern *e)
{
    int i ;
    struct rest_disc *rd, *rd1 ;

/*#ifdef DEBUG
    _th_print_disc(d) ;
#endif*/
    _make_find_trace(e) ;
    iterator->result_count = 0 ;

    if (d->rules != NULL) {
        iterator->results[iterator->result_count++] = d->rules ;
    }

    if (trace_size == 0) return ;

    rd = d->rest_discs[trace[0]%MAJOR_TABLE_SIZE] ;
    while (rd != NULL && rd->symbol != trace[0]) {
        rd = rd->next ;
    }

    if (rd==NULL) return ;

    if (rd->rules != NULL) {
        iterator->results[iterator->result_count++] = rd->rules ;
    }

    for (i = 1; i < trace_size; ++i) {
        rd1 = rd->rest_discs[trace[i]%MINOR_TABLE_SIZE] ;
        while (rd1 != NULL && rd1->symbol != trace[i]) rd1 = rd1->next ;
        if (rd1 != NULL && rd1->rules != NULL) {
#ifdef _DEBUG
            if (iterator->result_count >= MAX_ARGS) {
                printf("_th_init_find: iterator->result_count >= MAX_ARGS\n");
                exit(1);
            }
#endif
            iterator->results[iterator->result_count++] = rd1->rules ;
        }
    }
}

struct _ex_intern *_th_next_find(struct disc_iterator *iterator, int *p)
{
    struct _ex_intern *res ;

    if (iterator->result_count == 0) return NULL ;

    res = iterator->results[iterator->result_count-1]->rule ;
    if (p != NULL) *p = iterator->results[iterator->result_count-1]->priority ;
    iterator->results[iterator->result_count-1] = iterator->results[iterator->result_count-1]->next ;
    if (iterator->results[iterator->result_count-1]==NULL) --iterator->result_count ;

    return res ;
}

