/*
 * term_cache.c
 *
 * Routines for maintaining term information for each subterm in an
 * expression.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdio.h>
#include <stdlib.h>
#include "Globals.h"
#include "Intern.h"

static int push_level = 0;

static int lock_table = 0;

void _th_lock_table()
{
    lock_table = 1;
}

struct term_lookup {
    struct term_lookup *next;
    int position;
    struct _ex_intern *term;
};

#define TERM_HASH 2047

static struct term_lookup *table[TERM_HASH];

struct t_by_var {
    struct t_by_var *next;
    struct term_list *terms;
};

struct term_by_var {
    struct term_by_var *next;
    unsigned var;
    struct t_by_var *terms;
};

static struct term_by_var *term_by_var[TERM_HASH];

static int table_size, table_alloc_size;

int _th_get_table_size()
{
    return table_size;
}

int _th_get_term_position(struct _ex_intern *e)
{
    int hash = (((int)e)/4)%TERM_HASH;
    struct term_lookup *t = table[hash];
    //_tree_print2("hash = %d, table = %x", hash, table);

    while (t) {
        //_tree_print2("cycle %s %d\n", _th_print_exp(t->term), t->position);
        if (t->term==e) {
            //_tree_print1("Found position %d", t->position);
            return t->position;
        }
        t = t->next;
    }

    return -1;
}

static struct _ex_intern **lookup_table;

struct _ex_intern *_th_lookup_term(int index)
{
    //if (_th_check_alloc_block(TERM_CACHE_SPACE,(char *)lookup_table)) {
    //    fprintf(stderr, "Lookup table not properly allocated %x\n", lookup_table);
    //    fflush(stderr);
    //    exit(1);
    //}
    //if (lookup_table[index]->type > 9) {
    //    printf("table_size, index = %d %d\n", table_size, index);
    //    fflush(stdout);
    //    index = 0;
    //    index = 1/index;
    //    exit(1);
    //}

    if (index >= table_size) return NULL;
    return lookup_table[index];
#ifdef XX
    int i;

    //_tree_print1("Looking up %d\n", index);
    for (i = 0; i < TERM_HASH; ++i) {
        struct term_lookup *t = table[i];
        while (t != NULL) {
            //_tree_print2("Testing %d %s", t->position, _th_print_exp(t->term));
            if (t->position==index) return t->term;
            t = t->next;
        }
    }
    return NULL;
#endif
}

int is_var_assign(struct _ex_intern *e)
{
    return (e->u.appl.args[0]->type==EXP_VAR &&
            (e->u.appl.args[1]->type==EXP_RATIONAL || e->u.appl.args[1]->type==EXP_INTEGER)) ||
           (e->u.appl.args[1]->type==EXP_VAR &&
            (e->u.appl.args[0]->type==EXP_RATIONAL || e->u.appl.args[0]->type==EXP_INTEGER));
}

int is_var_equality(struct _ex_intern *e)
{
    return e->u.appl.args[0]->type==EXP_VAR && e->u.appl.args[1]->type==EXP_VAR;
}

void print_term_indices()
{
    int i;

    _zone_print0("All terms");
    _tree_indent();
    _zone_print0("Equality to constants");
    _tree_indent();
    for (i = 0; i < TERM_HASH; ++i) {
        struct term_lookup *t = table[i];
        while (t != NULL) {
            if (t->term->type==EXP_APPL && t->term->u.appl.functor==INTERN_EQUAL &&
                is_var_assign(t->term)) {
                _zone_print2("term %d %s", t->position, _th_print_exp(t->term));
            }
            t = t->next;
        }
    }
    _tree_undent();
    _zone_print0("Equality between variables");
    _tree_indent();
    for (i = 0; i < TERM_HASH; ++i) {
        struct term_lookup *t = table[i];
        while (t != NULL) {
            if (t->term->type==EXP_APPL && t->term->u.appl.functor==INTERN_EQUAL &&
                is_var_equality(t->term)) {
                _zone_print2("term %d %s", t->position, _th_print_exp(t->term));
            }
            t = t->next;
        }
    }
    _tree_undent();
    _zone_print0("Other equalities");
    _tree_indent();
    for (i = 0; i < TERM_HASH; ++i) {
        struct term_lookup *t = table[i];
        while (t != NULL) {
            if (t->term->type==EXP_APPL && t->term->u.appl.functor==INTERN_EQUAL &&
                !is_var_equality(t->term) && !is_var_assign(t->term)) {
                _zone_print2("term %d %s", t->position, _th_print_exp(t->term));
            }
            t = t->next;
        }
    }
    _tree_undent();
    _zone_print0("Other terms");
    _tree_indent();
    for (i = 0; i < TERM_HASH; ++i) {
        struct term_lookup *t = table[i];
        while (t != NULL) {
            if (t->term->type!=EXP_APPL || t->term->u.appl.functor!=INTERN_EQUAL) {
                _zone_print2("term %d %s", t->position, _th_print_exp(t->term));
            }
            t = t->next;
        }
    }
    _tree_undent();
    _tree_undent();
}

int new_term(struct _ex_intern *term)
{
    int hash = (((int)term)/4)%TERM_HASH;
    struct term_lookup *t = (struct term_lookup *)_th_alloc(TERM_CACHE_SPACE,sizeof(struct term_lookup));
    //printf("m alloc %d\n", sizeof(struct term_lookup));
    //printf("Adding term %s\n", _th_print_exp(term));
    //_tree_print2("ADDING TERM %s %d", _th_print_exp(term), table_size);
    t->next = table[hash];
    table[hash] = t;
    t->position = table_size++;
    t->term = term;
    return t->position;
}

#define TERM_INFO_HASH 249989

static struct term_data_info {
    struct term_data_info *next;
    struct _ex_intern *e, *term;
    struct term_data data;
} *term_info[TERM_INFO_HASH];

struct term_detail {
    struct term_detail *next;
    struct _ex_intern *term;
    int pos;
    unsigned *count;
    unsigned *pos_score;
    unsigned *neg_score;
    struct _ex_intern *pos_exp;
    struct _ex_intern *neg_exp;
};

#define TERM_DETAIL_SIZE 1023

struct term_detail *term_details[TERM_DETAIL_SIZE];

struct term_cache {
    struct term_cache *next;
    struct _ex_intern *term;
    int word_count;
    int term_count;
    int detail_max;
    unsigned *terms;
    unsigned *elimination_score;
};

static struct term_cache *root;

static struct term_detail *get_detail(struct _ex_intern *term, int pos)
{
    int hash = (((int)term)+pos)%TERM_DETAIL_SIZE;
    struct term_detail *d = term_details[hash];
    static unsigned zero[2] = { 1, 0 };
    static struct term_detail def = { NULL, NULL, 0, zero, zero, zero, NULL, NULL };
    while (d != NULL) {
        if (d->term==term && d->pos == pos) return d;
        d = d->next;
    }

    def.pos_exp = def.neg_exp = def.term = term;
    def.pos = pos;

    return &def;
}

static struct term_detail *has_detail(struct _ex_intern *term, int pos)
{
    int hash = (((int)term)+pos)%TERM_DETAIL_SIZE;
    struct term_detail *d = term_details[hash];

    while (d != NULL) {
        if (d->term==term && d->pos == pos) return d;
        d = d->next;
    }

    return NULL;
}

static struct term_detail *create_term_detail(struct _ex_intern *term, int pos)
{
    int hash = (((int)term)+pos)%TERM_DETAIL_SIZE;
    struct term_detail *d = (struct term_detail *)_th_alloc(TERM_CACHE_SPACE,sizeof(struct term_detail));
    //printf("n alloc %d\n", sizeof(struct term_detail));

    d->next = term_details[hash];
    term_details[hash] = d;
    d->term = term;
    d->pos = pos;

    return d;
}

int bit_count[256] = {
    0,
    1,
    1,
    2,
    1,
    2,
    2,
    3,
    1,
    2,
    2,
    3,
    2,
    3,
    3,
    4,
    1,
    2,
    2,
    3,
    2,
    3,
    3,
    4,
    2,
    3,
    3,
    4,
    3,
    4,
    4,
    5,
    1,
    2,
    2,
    3,
    2,
    3,
    3,
    4,
    2,
    3,
    3,
    4,
    3,
    4,
    4,
    5,
    2,
    3,
    3,
    4,
    3,
    4,
    4,
    5,
    3,
    4,
    4,
    5,
    4,
    5,
    5,
    6,
    1,
    2,
    2,
    3,
    2,
    3,
    3,
    4,
    2,
    3,
    3,
    4,
    3,
    4,
    4,
    5,
    2,
    3,
    3,
    4,
    3,
    4,
    4,
    5,
    3,
    4,
    4,
    5,
    4,
    5,
    5,
    6,
    2,
    3,
    3,
    4,
    3,
    4,
    4,
    5,
    3,
    4,
    4,
    5,
    4,
    5,
    5,
    6,
    3,
    4,
    4,
    5,
    4,
    5,
    5,
    6,
    4,
    5,
    5,
    6,
    5,
    6,
    6,
    7,
    1,
    2,
    2,
    3,
    2,
    3,
    3,
    4,
    2,
    3,
    3,
    4,
    3,
    4,
    4,
    5,
    2,
    3,
    3,
    4,
    3,
    4,
    4,
    5,
    3,
    4,
    4,
    5,
    4,
    5,
    5,
    6,
    2,
    3,
    3,
    4,
    3,
    4,
    4,
    5,
    3,
    4,
    4,
    5,
    4,
    5,
    5,
    6,
    3,
    4,
    4,
    5,
    4,
    5,
    5,
    6,
    4,
    5,
    5,
    6,
    5,
    6,
    6,
    7,
    2,
    3,
    3,
    4,
    3,
    4,
    4,
    5,
    3,
    4,
    4,
    5,
    4,
    5,
    5,
    6,
    3,
    4,
    4,
    5,
    4,
    5,
    5,
    6,
    4,
    5,
    5,
    6,
    5,
    6,
    6,
    7,
    3,
    4,
    4,
    5,
    4,
    5,
    5,
    6,
    4,
    5,
    5,
    6,
    5,
    6,
    6,
    7,
    4,
    5,
    5,
    6,
    5,
    6,
    6,
    7,
    5,
    6,
    6,
    7,
    6,
    7,
    7,
    8
};

static int term_count(struct term_cache *cache)
{
    int wc = cache->word_count;
    int i;
    int count = 0;
    unsigned w;

    for (i = 0; i < wc; ++i) {
        w = cache->terms[i];
        count += bit_count[w & 0xff];
        w >>= 8;
        count += bit_count[w & 0xff];
        w >>= 8;
        count += bit_count[w & 0xff];
        w >>= 8;
        count += bit_count[w & 0xff];
    }

    return count;
}

static int first_position(unsigned *terms, int word_count)
{
    int i;
    int pos;
    unsigned w;

    pos = 0;
    for (i = 0; i < word_count; ++i) {
        w = terms[i];
        if (w) {
            goto cont;
        }
        pos +=32;
    }
    return -1;
cont:
    while (!(w & 0xff)) {
        pos += 8;
        w >>= 8;
    }
    while (!(w&1)) {
        ++pos;
        w >>= 1;
    }
    return pos;
}

static int next_position(unsigned *terms, int word_count, int pos)
{
    unsigned w;
    int i;
    ++pos;
    i = pos/32;
    if (i>=word_count) return -1;
    w = terms[i];
    w >>= (pos&0x1f);
    if (w) {
        while (!(w&1)) {
            ++pos;
            w >>= 1;
        }
        return pos;
    }
    ++i;
    while (i < word_count) {
        w = terms[i];
        if (w) goto cont;
        ++i;
    }
    return -1;
cont:
    pos = i*32;
    while (!(w & 0xff)) {
        pos += 8;
        w >>= 8;
    }
    while (!(w&1)) {
        ++pos;
        w >>= 1;
    }
    if (pos>=table_size) {
        //return -1;
        int i;
        printf("word count = %d\n", word_count);
        for (i = 0; i < (table_size+31)/32; ++i) {
            printf("terms[%d] = %x\n", i, terms[i]);
        }
        exit(1);
    }
    return pos;
}

static int get_position(struct term_cache *cache, int term)
{
    int i;
    int count = 0;
    unsigned w;

    for (i = 0; i < term/32; ++i) {
        w = cache->terms[i];
        count += bit_count[w & 0xff];
        w >>= 8;
        count += bit_count[w & 0xff];
        w >>= 8;
        count += bit_count[w & 0xff];
        w >>= 8;
        count += bit_count[w & 0xff];
    }
    term = term%32;
    w = cache->terms[i];
    while (term > 8) {
        count += bit_count[w & 0xff];
        w = w>>8;
        term -= 8;
    }
    while (term) {
        if (w&1) ++count;
        w = w>>1;
        --term;
    }

    return count;
}

unsigned **dependency_table;
struct dependencies **pos_dependency_list;
struct dependencies **neg_dependency_list;

static void check_dependency_table()
{
    int i;

    for (i = 0; i < table_size; ++i) {
        int j = -1;
        if (table_size > 0) {
            unsigned x;
            j = (table_size-1)/32;
            x = dependency_table[i][j];
            if (table_size%32 != 0 && x>>(table_size%32)) {
                fprintf(stderr, "table size = %d\n", table_size);
                fprintf(stderr, "Error in dependency table %x %d %d\n", x, i, j);
                exit(1);
            }
        }
        while (++j < ((table_alloc_size+31)/32)) {
            if (dependency_table[i][j]) {
                fprintf(stderr, "Error in dependency table 0 %d %d\n", i, j);
                exit(1);
            }
        }
    }
}

int cd = 0;

void check_dependency_list()
{
    int i;

    return;
    if (!cd) return;

    //if (table_size > 391) {
    //    fprintf(stderr, "Table size too big\n");
    //    exit(1);
    //}
    if (pos_dependency_list==NULL) return;

    for (i = 0; i < table_size; ++i) {
        struct dependencies *d = pos_dependency_list[i];
        while (d) {
            if (d->term==NULL) {
                fprintf(stderr, "Error in dependency list\n");
                exit(1);
            }
            d = d->next;
        }
    }
}

struct update_list {
    struct update_list *next;
    struct term_cache *cache;
    int detail_max;
} *update_list;

unsigned *_th_get_active_terms(struct _ex_intern *term);

int _th_score_precision = 5;

void update_score_info(struct _ex_intern *term)
{
    int i, j, p;
    int *pos;
    struct term_detail *d, *sd;
    struct _ex_intern *p1, *p2, *n1, *n2;
    unsigned *terms, **sterms;
    int word_count = (table_size+31)/32;

    //printf("Updating score info for %d %s\n", _tree_zone, _th_print_exp(term));
    //printf("Term is %s\n", _th_print_exp(term));
    //printf("Term is %x\n", term);
    //printf("term->term_cache->term_count = %d\n", term->term_cache->term_count);
    //printf("term->term_cache->word_count = %d\n", term->term_cache->word_count);
    //printf("term->term_cache->detail_max = %d\n", term->term_cache->detail_max);
    //printf("table_size = %d\n", table_size);
    //fflush(stdout);

#ifdef SHOW_ACTIVE
    _tree_print_exp("update_score_info", term);
    _tree_indent();
#endif
    //if (term->u.appl.functor==INTERN_NOT && term->term_cache->detail_max > 0) {
    //    printf("testing whether to update %s %d %d\n", _th_print_exp(term), term->term_cache->detail_max, table_size);
    //}

    if (term->term_cache->detail_max>=table_size) {
#ifdef SHOW_ACTIVE
        _tree_print2("exit table_size %d %d", term->term_cache->detail_max, table_size);
        _tree_undent();
#endif
        return;
    }

    if (term->term_cache->detail_max > 0) {
        struct update_list *u = (struct update_list *)_th_alloc(TERM_CACHE_SPACE,sizeof(struct update_list));
        u->next = update_list;
        update_list = u;
        u->cache = term->term_cache;
        u->detail_max = term->term_cache->detail_max;
    }

    //printf("Updating score for %s\n", _th_print_exp(term));

    terms = (unsigned *)ALLOCA(sizeof(unsigned) * word_count);
    p = first_position(term->term_cache->terms,term->term_cache->word_count);
    if (p==-1) {
#ifdef SHOW_ACTIVE
        _tree_print("exit 2");
        _tree_undent();
#endif
        return;
    }
    //printf("pos %d\n", p);
    //printf("score info\n");
    for (i = 0; i < word_count; ++i) {
       terms[i] = dependency_table[p][i];
       //printf("terms[%d] = %x\n", i, terms[i]);
    }
    p = next_position(term->term_cache->terms,term->term_cache->word_count,p);
    while (p >= 0) {
        //printf("pos %d\n", p);
        for (i = 0; i < word_count; ++i) {
           terms[i] |= dependency_table[p][i];
           //printf("terms[%d] = %x\n", i, terms[i]);
        }
        p = next_position(term->term_cache->terms,term->term_cache->word_count,p);
    }
    //fflush(stdout);
#ifdef SHOW_ACTIVE
    for (i = 0; i < word_count; ++i) {
        _tree_print("terms[%d] = %x\n", i, terms[i]);
    }
#endif

    term->term_cache->detail_max = table_size;

    switch (term->type) {
        case EXP_APPL:
            pos = (int *)ALLOCA(sizeof(int) * term->u.appl.count);
            sterms = (unsigned **)ALLOCA(sizeof(unsigned *) * term->u.appl.count);
            for (i = 0; i < term->u.appl.count; ++i) {
                update_score_info(term->u.appl.args[i]);
                sterms[i] = (unsigned *)ALLOCA(sizeof(unsigned) * word_count);
                p = first_position(term->u.appl.args[i]->term_cache->terms,term->u.appl.args[i]->term_cache->word_count);
                if (p==-1) {
                    for (j = 0; j < word_count; ++j) {
                        sterms[i][j] = 0;
                    }
                    pos[i] = -1;
                } else {
                    for (j = 0; j < word_count; ++j) {
                        sterms[i][j] = dependency_table[p][j];
                    }
                    p = next_position(term->u.appl.args[i]->term_cache->terms,term->u.appl.args[i]->term_cache->word_count,p);
                    while (p >= 0) {
                        for (j = 0; j < word_count; ++j) {
                            sterms[i][j] |= dependency_table[p][j];
                        }
                        p = next_position(term->u.appl.args[i]->term_cache->terms,term->u.appl.args[i]->term_cache->word_count,p);
                    }
                    //for (j = 0; j < word_count; ++j) {
                    //    printf("sterms[%d][%d] = %x\n", i, j, sterms[i][j]);
                    //}
                    pos[i] = first_position(sterms[i], term->u.appl.args[i]->term_cache->word_count);
                }
            }
            //printf("Appl updating score for %s\n", _th_print_exp(term));
            p = first_position(terms, word_count);
#ifdef SHOW_ACTIVE
            _tree_print1("p %d", p);
#endif
            while (p >= 0) {
                struct _ex_intern *t;
                struct dependencies *dep;
                //printf("   processing position1 %d\n", p);
                //printf("p = %d\n", p);
                //fflush(stdout);
                if (has_detail(term,p)) goto next_cycle;
                t = _th_lookup_term(p);
                //if (i >= term_n) {
                //    fprintf(stderr, "_th_get_active_terms: position out of bounds %d %d %d\n", i, term_n, term->term_cache->word_count);
                //    exit(1);
                //}
#ifdef SHOW_ACTIVE
                _tree_print1("Pos %d", p);
                _tree_print_exp("Checking subterm", t);
                _tree_indent();
                _tree_print1("i = %d", i);
#endif
                d = create_term_detail(term,p);
#ifdef SHOW_ACTIVE
                _tree_print1("d = %x", d);
#endif
                d->count = (unsigned *)_th_alloc(TERM_CACHE_SPACE,sizeof(unsigned) * _th_score_precision);
                d->neg_score = (unsigned *)_th_alloc(TERM_CACHE_SPACE,sizeof(unsigned) * _th_score_precision);
                d->pos_score = (unsigned *)_th_alloc(TERM_CACHE_SPACE,sizeof(unsigned) * _th_score_precision);
                d->count[0] = d->neg_score[0] = d->pos_score[0] = 1;
                d->count[1] = d->neg_score[1] = d->pos_score[1] = 0;
                if (term==t) {
                    d->neg_score[1] = d->pos_score[1] = 4;
                    d->neg_score[0] = d->pos_score[0] = 1;
                    d->count[0] = 1;
                    d->count[1] = 1;
                    d->neg_exp = _ex_false;
                    d->pos_exp = _ex_true;
#ifdef SHOW_ACTIVE
                    _tree_print("Here 1");
#endif
                    goto cont;
                }
                d->neg_exp = d->pos_exp = term;
                switch (term->u.appl.functor) {
                    case INTERN_AND:
                        p1 = p2 = n1 = n2 = NULL;
                        for (j = 0; j < term->u.appl.count; ++j) {
#ifdef SHOW_ACTIVE
                            _tree_print2("Term check %d %s", j, _th_print_exp(term->u.appl.args[j]));
                            _tree_indent();
                            _tree_print1("sd = %x", sd);
#endif
                            if (pos[j]==p) {
                                sd = get_detail(term->u.appl.args[j],pos[j]);
#ifdef SHOW_ACTIVE
                                _tree_print0("Checking");
                                _tree_print_exp("p_reduce", sd->pos_exp);
                                _tree_print_exp("n_reduce", sd->neg_exp);
#endif
                                _th_big_accumulate(d->count,sd->count);
                                //if (d->count < 0) d->count = 0x7fffffff;
                                if (d->pos_exp==term) {
                                    if (sd->pos_exp==_ex_false) {
#ifdef SHOW_ACTIVE
                                        _tree_print1("Here1 %d", term->term_cache->elimination_score[1]);
#endif
                                        d->pos_exp = _ex_false;
                                        d->pos_score = term->term_cache->elimination_score;
                                    } else {
#ifdef SHOW_ACTIVE
                                        _tree_print1("Here2 %d", sd->pos_score);
#endif
                                        _th_big_accumulate(d->pos_score, sd->pos_score);
                                        //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                                        if (sd->pos_exp != _ex_true) {
                                            if (p1==NULL) {
                                                p1 = sd->pos_exp;
                                            } else if (p2==NULL) {
                                                p2 = sd->pos_exp;
                                            }
                                        }
                                    }
                                }
                                if (d->neg_exp==term) {
                                    if (sd->neg_exp==_ex_false) {
#ifdef SHOW_ACTIVE
                                        _tree_print1("Here3 %d", term->term_cache->elimination_score[1]);
#endif
                                        d->neg_exp = _ex_false;
                                        d->neg_score = term->term_cache->elimination_score;
                                    } else {
#ifdef SHOW_ACTIVE
                                        _tree_print1("Here4 %d", sd->neg_score);
#endif
                                        _th_big_accumulate(d->neg_score, sd->neg_score);
                                        //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                                        if (sd->neg_exp != _ex_true) {
                                            if (n1==NULL) {
                                                n1 = sd->neg_exp;
                                            } else if (n2==NULL) {
                                                n2 = sd->neg_exp;
                                            }
                                        }
                                    }
                                }
                                pos[j] = next_position(sterms[j], term->u.appl.args[j]->term_cache->word_count,pos[j]);
                            } else {
                                if (p1==NULL) {
                                    p1 = term->u.appl.args[j];
                                } else if (p2==NULL) {
                                    p2 = term->u.appl.args[j];
                                }
                                if (n1==NULL) {
                                    n1 = term->u.appl.args[j];
                                } else if (n2==NULL) {
                                    n2 = term->u.appl.args[j];
                                }
                            }
#ifdef SHOW_ACTIVE
                            _tree_undent();
#endif
                        }
                        if (d->pos_exp==term) {
                            if (p1==NULL) {
                                _th_big_accumulate_small(d->pos_score, 2);
                                d->pos_exp = _ex_true;
                            } else if (p2==NULL) {
                                _th_big_accumulate_small(d->pos_score, 1);
                                d->pos_exp = p1;
                            }
                            //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                        }
                        if (d->neg_exp==term) {
                            if (n1==NULL) {
                                _th_big_accumulate_small(d->neg_score, 2);
                                d->neg_exp = _ex_true;
                            } else if (n2==NULL) {
                                _th_big_accumulate_small(d->neg_score, 1);
                                d->neg_exp = n1;
                            }
                            //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                        }
                        break;
                    case INTERN_OR:
                        p1 = p2 = n1 = n2 = NULL;
                        for (j = 0; j < term->u.appl.count; ++j) {
#ifdef SHOW_ACTIVE
                            _tree_print2("Term check %d %s", j, _th_print_exp(term->u.appl.args[j]));
                            _tree_indent();
                            _tree_print1("sd = %x", sd);
#endif
                            if (pos[j]==p) {
                                sd = get_detail(term->u.appl.args[j],pos[j]);
#ifdef SHOW_ACTIVE
                                _tree_print0("Checking");
                                _tree_print_exp("p_reduce", sd->pos_exp);
                                _tree_print_exp("n_reduce", sd->neg_exp);
#endif
                                //if (sd==NULL) {
                                //    printf("term: %s\n", _th_print_exp(term));
                                //    printf("arg: %d\n", j);
                                //    printf("pos: %d %s\n", pos[j], _th_print_exp(_th_lookup_term(pos[j])));
                                //    printf("table size: %d\n", table_size);
                                //    exit(1);
                                //}
                                _th_big_accumulate(d->count, sd->count);
                                //if (d->count < 0) d->count = 0x7fffffff;
                                if (d->pos_exp==term) {
                                    if (sd->pos_exp==_ex_true) {
#ifdef SHOW_ACTIVE
                                        _tree_print1("Here1 %d", term->term_cache->elimination_score[1]);
#endif
                                        d->pos_exp = _ex_true;
                                        d->pos_score = term->term_cache->elimination_score;
                                    } else {
#ifdef SHOW_ACTIVE
                                        _tree_print1("Here2 %d", sd->pos_score);
#endif
                                        _th_big_accumulate(d->pos_score, sd->pos_score);
                                        //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                                        if (sd->pos_exp != _ex_false) {
                                            if (p1==NULL) {
                                                p1 = sd->pos_exp;
                                            } else if (p2==NULL) {
                                                p2 = sd->pos_exp;
                                            }
                                        }
                                    }
                                }
                                if (d->neg_exp==term) {
                                    if (sd->neg_exp==_ex_true) {
#ifdef SHOW_ACTIVE
                                        _tree_print1("Here3 %d", term->term_cache->elimination_score[1]);
#endif
                                        d->neg_exp = _ex_true;
                                        d->neg_score = term->term_cache->elimination_score;
                                    } else {
#ifdef SHOW_ACTIVE
                                        _tree_print1("Here4 %d", sd->neg_score);
#endif
                                        _th_big_accumulate(d->neg_score, sd->neg_score);
                                        //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                                        if (sd->neg_exp != _ex_false) {
                                            if (n1==NULL) {
                                                n1 = sd->neg_exp;
                                            } else if (n2==NULL) {
                                                n2 = sd->neg_exp;
                                            }
                                        }
                                    }
                                }
                                pos[j] = next_position(sterms[j], term->u.appl.args[j]->term_cache->word_count, pos[j]);
                            } else {
                                if (p1==NULL) {
                                    p1 = term->u.appl.args[j];
                                } else if (p2==NULL) {
                                    p2 = term->u.appl.args[j];
                                }
                                if (n1==NULL) {
                                    n1 = term->u.appl.args[j];
                                } else if (n2==NULL) {
                                    n2 = term->u.appl.args[j];
                                }
                            }
#ifdef SHOW_ACTIVE
                            _tree_undent();
#endif
                        }
                        if (d->pos_exp==term) {
                            if (p1==NULL) {
                                _th_big_accumulate_small(d->pos_score, 2);
                                d->pos_exp = _ex_false;
                            } else if (p2==NULL) {
                                _th_big_accumulate_small(d->pos_score, 1);
                                d->pos_exp = p1;
                            }
                            //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                        }
                        if (d->neg_exp==term) {
                            if (n1==NULL) {
                                _th_big_accumulate_small(d->neg_score, 2);
                                d->neg_exp = _ex_false;
                            } else if (n2==NULL) {
                                _th_big_accumulate_small(d->neg_score, 1);
                                d->neg_exp = n1;
                            }
                            //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                        }
                        break;
                    case INTERN_NOT:
                        if (pos[0]==p) {
                            sd = get_detail(term->u.appl.args[0],pos[0]);
                            _th_big_accumulate(d->count, sd->count);
                            //if (d->count < 0) d->count = 0x7fffffff;
                            if (sd->pos_exp==_ex_true) {
                                d->pos_exp = _ex_false;
                                _th_big_accumulate(d->pos_score, term->term_cache->elimination_score);
                                _th_big_accumulate_small(d->pos_score, 1);
                                //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                            } else if (sd->pos_exp==_ex_false) {
                                d->pos_exp = _ex_true;
                                _th_big_accumulate(d->pos_score, term->term_cache->elimination_score);
                                _th_big_accumulate_small(d->pos_score, 1);
                                //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                            } else if (sd->pos_exp->type==EXP_APPL && sd->pos_exp->u.appl.functor==INTERN_NOT) {
                                d->pos_exp = sd->pos_exp->u.appl.args[0];
                                _th_big_accumulate(d->pos_score, sd->pos_score);
                                _th_big_accumulate_small(d->pos_score, 1);
                                //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                            } else {
                                _th_big_accumulate(d->pos_score, sd->pos_score);
                                //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                            }
                            if (sd->neg_exp==_ex_true) {
                                d->neg_exp = _ex_false;
                                _th_big_accumulate(d->neg_score, term->term_cache->elimination_score);
                                _th_big_accumulate_small(d->neg_score, 1);
                                //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                            } else if (sd->neg_exp==_ex_false) {
                                d->neg_exp = _ex_true;
                                _th_big_accumulate(d->neg_score, term->term_cache->elimination_score);
                                _th_big_accumulate_small(d->neg_score, 1);
                                //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                            } else if (sd->neg_exp->type==EXP_APPL && sd->neg_exp->u.appl.functor==INTERN_NOT) {
                                d->neg_exp = sd->neg_exp->u.appl.args[0];
                                _th_big_accumulate(d->neg_score, sd->neg_score);
                                _th_big_accumulate_small(d->neg_score, 1);
                                //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                            } else {
                                _th_big_accumulate(d->neg_score, sd->neg_score);
                                //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                            }
                            pos[0] = next_position(sterms[0],term->u.appl.args[0]->term_cache->word_count,pos[0]);
                        }
                        break;
                    case INTERN_EQUAL:
#ifdef SHOW_ACTIVE
                        _tree_print0("Here 1");
#endif
                        if (pos[0]==p) {
                            sd = get_detail(term->u.appl.args[0],pos[0]);
#ifdef SHOW_ACTIVE
                            _tree_print0("Here 1a");
#endif
                            _th_big_accumulate(d->count, sd->count);
#ifdef SHOW_ACTIVE
                            _tree_print0("Here 1b");
#endif
                            _th_big_accumulate(d->pos_score, sd->pos_score);
#ifdef SHOW_ACTIVE
                            _tree_print0("Here 1c");
#endif
                            _th_big_accumulate(d->neg_score, sd->neg_score);
#ifdef SHOW_ACTIVE
                            _tree_print0("Here 1d");
#endif
                            //if (d->count < 0) d->count = 0x7fffffff;
                            //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                            //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                            pos[0] = next_position(sterms[0],term->u.appl.args[0]->term_cache->word_count,pos[0]);
                            p1 = sd->pos_exp;
                            n1 = sd->neg_exp;
                        } else {
                            p1 = n1 = term->u.appl.args[0];
                        }
#ifdef SHOW_ACTIVE
                        _tree_print0("Here 2");
#endif
                        if (pos[1]==p) {
                            sd = get_detail(term->u.appl.args[1],pos[1]);
                            _th_big_accumulate(d->count, sd->count);
                            _th_big_accumulate(d->pos_score, sd->pos_score);
                            _th_big_accumulate(d->neg_score, sd->neg_score);
                            //if (d->count < 0) d->count = 0x7fffffff;
                            //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                            //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                            pos[1] = next_position(sterms[1],term->u.appl.args[1]->term_cache->word_count,pos[1]);
                            p2 = sd->pos_exp;
                            n2 = sd->neg_exp;
                        } else {
                            p2 = n2 = term->u.appl.args[1];
                        }
#ifdef SHOW_ACTIVE
                        _tree_print0("Here 3");
#endif
                        if (p1==p2) {
                            _th_big_accumulate(d->pos_score, term->u.appl.args[0]->term_cache->elimination_score);
                            _th_big_accumulate(d->pos_score, term->u.appl.args[1]->term_cache->elimination_score);
                            //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                            _th_big_accumulate_small(d->pos_score, 2);
                            //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                            d->pos_exp = _ex_true;
                        } else if ((p1->type==EXP_INTEGER || p1->type==EXP_RATIONAL || p1==_ex_true || p1==_ex_false) &&
                                   (p2->type==EXP_INTEGER || p2->type==EXP_RATIONAL || p2==_ex_true || p2==_ex_false) &&
                                   p1 != p2) {
                            _th_big_accumulate(d->pos_score, term->u.appl.args[0]->term_cache->elimination_score);
                            _th_big_accumulate(d->pos_score, term->u.appl.args[1]->term_cache->elimination_score);
                            //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                            _th_big_accumulate_small(d->pos_score, 2);
                            //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                            d->pos_exp = _ex_false;
                        } else if (p1==_ex_true) {
                            _th_big_accumulate_small(d->pos_score, 1);
                            //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                            d->pos_exp = p2;
                        } else if (p2==_ex_true) {
                            _th_big_accumulate_small(d->pos_score, 1);
                            //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                            d->pos_exp = p1;
                        } else if (p1==_ex_false) {
                            if (p2->type==EXP_APPL && p2->u.appl.functor==INTERN_NOT) {
                                d->pos_exp = p2->u.appl.args[0];
                            } else {
                                d->pos_exp = _ex_intern_appl(INTERN_NOT,1,&p2);
                                _th_get_active_terms(d->pos_exp);
                            }
                        } else if (p2==_ex_false) {
                            if (p1->type==EXP_APPL && p1->u.appl.functor==INTERN_NOT) {
                                d->pos_exp = p1->u.appl.args[0];
                            } else {
                                d->pos_exp = _ex_intern_appl(INTERN_NOT,1,&p1);
                                _th_get_active_terms(d->pos_exp);
                            }
                        }
#ifdef SHOW_ACTIVE
                        _tree_print0("Here 4");
#endif
                        if (n1==n2) {
                            _th_big_accumulate(d->neg_score, term->u.appl.args[0]->term_cache->elimination_score);
                            _th_big_accumulate(d->neg_score, term->u.appl.args[1]->term_cache->elimination_score);
                            //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                            _th_big_accumulate_small(d->neg_score, 2);
                            //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                            d->neg_exp = _ex_true;
                        } else if ((n1->type==EXP_INTEGER || n1->type==EXP_RATIONAL || n1==_ex_true || n1==_ex_false) &&
                                   (n2->type==EXP_INTEGER || n2->type==EXP_RATIONAL || n2==_ex_true || n2==_ex_false) &&
                                   n1 != n2) {
                            _th_big_accumulate(d->neg_score, term->u.appl.args[0]->term_cache->elimination_score);
                            _th_big_accumulate(d->neg_score, term->u.appl.args[1]->term_cache->elimination_score);
                            //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                            _th_big_accumulate_small(d->neg_score, 2);
                            //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                            d->neg_exp = _ex_false;
                        } else if (n1==_ex_true) {
                            _th_big_accumulate_small(d->neg_score, 1);
                            //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                            d->neg_exp = n2;
                        } else if (n2==_ex_true) {
                            _th_big_accumulate_small(d->neg_score, 1);
                            //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                            d->neg_exp = n1;
                        } else if (n1==_ex_false) {
                            if (n2->type==EXP_APPL && n2->u.appl.functor==INTERN_NOT) {
                                d->neg_exp = n2->u.appl.args[0];
                            } else {
                                d->neg_exp = _ex_intern_appl(INTERN_NOT,1,&n2);
                                _th_get_active_terms(d->neg_exp);
                            }
                        } else if (n2==_ex_false) {
                            if (n1->type==EXP_APPL && n1->u.appl.functor==INTERN_NOT) {
                                d->neg_exp = n1->u.appl.args[0];
                            } else {
                                d->neg_exp = _ex_intern_appl(INTERN_NOT,1,&n1);
                                _th_get_active_terms(d->neg_exp);
                            }
                        }
#ifdef SHOW_ACTIVE
                        _tree_print0("Here 5");
#endif
                        break;
                    case INTERN_ITE:
                        if (pos[0]==p) {
                            sd = get_detail(term->u.appl.args[0],pos[0]);
                            _th_big_accumulate(d->count, sd->count);
#ifdef SHOW_ACTIVE
                            _tree_print_exp("ite 0 pos_exp", sd->pos_exp);
                            _tree_print_exp("ite 0 neg_exp", sd->neg_exp);
                            _tree_print1("ite 0 pos_score %d", sd->pos_score);
                            _tree_print1("ite 0 neg_score %d", sd->neg_score);
#endif
                            if (sd->pos_exp==_ex_true) {
                                _th_big_accumulate(d->pos_score,term->u.appl.args[2]->term_cache->elimination_score);
                                _th_big_accumulate_small(d->pos_score,1);
                                _th_big_accumulate(d->pos_score,sd->pos_score);
                                if (pos[1]==p) {
                                    struct term_detail *sd1 = get_detail(term->u.appl.args[1],pos[1]);
                                    _th_big_accumulate(d->pos_score, sd1->pos_score);
                                    //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                                    d->pos_exp = sd1->pos_exp;
                                } else {
                                    d->pos_exp = term->u.appl.args[1];
                                }
                            } else if (sd->pos_exp==_ex_false) {
                                _th_big_accumulate(d->pos_score, term->u.appl.args[1]->term_cache->elimination_score);
                                _th_big_accumulate_small(d->pos_score,1);
                                _th_big_accumulate(d->pos_score,sd->pos_score);
                                if (pos[2]==p) {
                                    struct term_detail *sd1 = get_detail(term->u.appl.args[2],pos[2]);
                                    _th_big_accumulate(d->pos_score, sd1->pos_score);
                                    //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                                    d->pos_exp = sd1->pos_exp;
                                } else {
                                    d->pos_exp = term->u.appl.args[2];
                                }
                            } else {
                                struct term_detail *sd1;
                                struct term_detail *sd2;
                                _th_big_accumulate(d->pos_score, sd->pos_score);
                                if (pos[1]==p) {
                                    sd1 = get_detail(term->u.appl.args[1],pos[1]);
                                    _th_big_accumulate(d->pos_score, sd1->pos_score);
                                    //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                                }
                                if (pos[2]==p) {
                                    sd2 = get_detail(term->u.appl.args[2],pos[2]);
                                    _th_big_accumulate(d->pos_score, sd2->pos_score);
                                    //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                                }
                            }
                            if (sd->neg_exp==_ex_true) {
                                _th_big_accumulate(d->neg_score, term->u.appl.args[2]->term_cache->elimination_score);
                                _th_big_accumulate_small(d->neg_score, 1);
                                _th_big_accumulate(d->neg_score, sd->neg_score);
                                if (pos[1]==p) {
                                    struct term_detail *sd1 = get_detail(term->u.appl.args[1],pos[1]);
                                    _th_big_accumulate(d->neg_score, sd1->neg_score);
                                    //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                                    d->neg_exp = sd1->neg_exp;
                                } else {
                                    d->neg_exp = term->u.appl.args[1];
                                }
                            } else if (sd->neg_exp==_ex_false) {
                                _th_big_accumulate(d->neg_score, term->u.appl.args[1]->term_cache->elimination_score);
                                _th_big_accumulate_small(d->neg_score,1);
                                _th_big_accumulate(d->neg_score,sd->neg_score);
                                if (pos[2]==p) {
                                    struct term_detail *sd1 = get_detail(term->u.appl.args[2],pos[2]);
                                    _th_big_accumulate(d->neg_score, sd1->neg_score);
                                    //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                                    d->neg_exp = sd1->neg_exp;
                                } else {
                                    d->neg_exp = term->u.appl.args[2];
                                }
                            } else {
                                struct term_detail *sd1;
                                struct term_detail *sd2;
                                _th_big_accumulate(d->neg_score,sd->neg_score);
                                if (pos[1]==p) {
                                    sd1 = get_detail(term->u.appl.args[1],pos[1]);
                                    _th_big_accumulate(d->neg_score, sd1->neg_score);
                                    //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                                }
                                if (pos[2]==p) {
                                    sd2 = get_detail(term->u.appl.args[2],pos[2]);
                                    _th_big_accumulate(d->neg_score, sd2->neg_score);
                                    //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                                }
                            }
                            pos[0] = next_position(sterms[0],term->u.appl.args[0]->term_cache->word_count,pos[0]);
                            if (pos[1]==p) {
                                struct term_detail *sd1 = get_detail(term->u.appl.args[1],pos[1]);
                                _th_big_accumulate(d->count, sd1->count);
                                //if (d->count < 0) d->count = 0x7fffffff;
                                pos[1] = next_position(sterms[1],term->u.appl.args[1]->term_cache->word_count,pos[1]);
                            }
                            if (pos[2]==p) {
                                struct term_detail *sd1 = get_detail(term->u.appl.args[2],pos[2]);
                                _th_big_accumulate(d->count, sd1->count);
                                //if (d->count < 0) d->count = 0x7fffffff;
                                pos[2] = next_position(sterms[2],term->u.appl.args[2]->term_cache->word_count,pos[2]);
                            }
                        } else {
                            sd = get_detail(term->u.appl.args[1],pos[1]);
                            if (pos[1]==p) {
                                _th_big_accumulate(d->count, sd->count);
                                _th_big_accumulate(d->pos_score, sd->pos_score);
                                _th_big_accumulate(d->neg_score, sd->neg_score);
                                //if (d->count < 0) d->count = 0x7fffffff;
                                //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                                //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                                pos[1] = next_position(sterms[1],term->u.appl.args[1]->term_cache->word_count,pos[1]);
                            }
                            sd = get_detail(term->u.appl.args[2],pos[2]);
                            if (pos[2]==p) {
                                _th_big_accumulate(d->count, sd->count);
                                _th_big_accumulate(d->pos_score, sd->pos_score);
                                _th_big_accumulate(d->neg_score, sd->neg_score);
                                //if (d->count < 0) d->count = 0x7fffffff;
                                //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                                //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                                pos[2] = next_position(sterms[2],term->u.appl.args[2]->term_cache->word_count,pos[2]);
                            }
                        }
                        break;
                    default:
                        for (j = 0; j < term->u.appl.count; ++j) {
                            sd = get_detail(term->u.appl.args[j],pos[j]);
                            if (pos[j]==p) {
#ifdef SHOW_ACTIVE
                                _tree_print2("Checking %d %d",j, sd);
#endif
                                _th_big_accumulate(d->count, sd->count);
                                _th_big_accumulate(d->pos_score, sd->pos_score);
                                _th_big_accumulate(d->neg_score, sd->neg_score);
                                //if (d->count < 0) d->count = 0x7fffffff;
                                //if (d->pos_score < 0) d->pos_score = 0x7fffffff;
                                //if (d->neg_score < 0) d->neg_score = 0x7fffffff;
                                pos[j] = next_position(sterms[j],word_count,pos[j]);
                            }
                        }
                }
cont:
                dep = pos_dependency_list[p];
                while (dep != NULL) {
                    if (dep->term->e==term) {
                        if (dep->reduction==_ex_true || dep->reduction==_ex_false) {
                            d->pos_score[1] = 4;
                        } else {
                            d->pos_score[1] = 1;
                        }
                        d->pos_exp = dep->reduction;
                        break;
                    }
                    dep = dep->next;
                }
                dep = neg_dependency_list[p];
                while (dep != NULL) {
                    if (dep->term->e==term) {
                        if (dep->reduction==_ex_true || dep->reduction==_ex_false) {
                            d->neg_score[1] = 4;
                        } else {
                            d->neg_score[1] = 1;
                        }
                        d->neg_exp = dep->reduction;
                        break;
                    }
                    dep = dep->next;
                }
#ifdef SHOW_ACTIVE
                _tree_print1("pos score %d", d->pos_score[1]);
                _tree_print1("neg score %d", d->neg_score[1]);
                _tree_print_exp("pos exp", d->pos_exp);
                _tree_print_exp("neg exp", d->neg_exp);
                _tree_print1("d = %x", d);
                _tree_print1("p = %d", p);
                _tree_print1("i = %d", i);
                _tree_undent();
                //if (d->pos_score < 0 || d->neg_score < 0) {
                //    exit(1);
                //}
#endif
next_cycle:
                p = next_position(terms,word_count,p);
                //printf("next p = %d\n", p);
                //fflush(stdout);
            }
            break;
        default:
            p = first_position(terms, word_count);
            while (p >= 0) {
                //printf("   processing position2 %d\n", p);
                //printf("p = %d\n", p);
                d = create_term_detail(term,p);
                d->count = (unsigned *)_th_alloc(TERM_CACHE_SPACE,sizeof(unsigned) * 2);
                d->neg_score = (unsigned *)_th_alloc(TERM_CACHE_SPACE,sizeof(unsigned) * 2);
                d->pos_score = (unsigned *)_th_alloc(TERM_CACHE_SPACE,sizeof(unsigned) * 2);
                d->count[0] = d->pos_score[0] = d->neg_score[0] = 1;
                if (term==_th_lookup_term(p)) {
                    d->count[1] = 1;
                    d->neg_score[1] = d->pos_score[1] = 2;
                    d->neg_exp = _ex_false;
                    d->pos_exp = _ex_true;
                } else {
                    d->pos_score[1] = d->neg_score[1] = d->count[1] = 0;
                    d->neg_exp = d->pos_exp = term;
                }
                p = next_position(terms,word_count,p);
            }
    }

#ifdef SHOW_ACTIVE
    _tree_undent();
#endif
}

unsigned *_th_get_active_terms(struct _ex_intern *term)
{
    int i, j, term_n;
    unsigned *c;

    if (term->term_cache) {
        update_score_info(term);
        return term->term_cache->terms;
    }

#ifdef SHOW_ACTIVE
    _tree_print_exp("Cache processing", term);
//#ifndef FAST
//    if (_th_is_free_in(term,_th_intern("x_144")) && term->type==EXP_APPL && term->u.appl.functor==INTERN_EQUAL) {
//        fprintf(stderr, "************* pos: %d\n", _tree_count);
//    }
//#endif
    _tree_indent();
#endif

    term->term_cache = (struct term_cache *)_th_alloc(CACHE_SPACE,sizeof(struct term_cache));
    term->term_cache->term = term;
    term->term_cache->next = root;
    root = term->term_cache;

#ifdef SHOW_ACTIVE
    _tree_print1("term->term_cache = %x", term->term_cache);
#endif
    term->term_cache->terms = (unsigned *)_th_alloc(CACHE_SPACE,sizeof(unsigned) * ((table_size + 31)/32));
    term->term_cache->word_count = (table_size + 31)/32;
    term->term_cache->term_count = table_size;
    term->term_cache->elimination_score = (unsigned *)_th_alloc(TERM_CACHE_SPACE,sizeof(unsigned) * _th_score_precision);
    term->term_cache->elimination_score[0] = 1;
    term->term_cache->elimination_score[1] = 1;
    switch (term->type) {
        case EXP_APPL:
#ifdef SHOW_ACTIVE
            //if (level==1 && term->u.appl.functor==INTERN_OR) fprintf(stderr, "cache: %d\n", _tree_count);
#endif
            if (term->u.appl.count > 0) {
                c = _th_get_active_terms(term->u.appl.args[0]);
                for (i = 0; i < term->u.appl.args[0]->term_cache->word_count; ++i) {
                    term->term_cache->terms[i] = c[i];
                }
                for (; i < term->term_cache->word_count; ++i) {
                    term->term_cache->terms[i] = 0;
                }
                _th_big_accumulate(term->term_cache->elimination_score, term->u.appl.args[0]->term_cache->elimination_score);
                for (i = 1; i < term->u.appl.count; ++i) {
                    c = _th_get_active_terms(term->u.appl.args[i]);
                    _th_big_accumulate(term->term_cache->elimination_score, term->u.appl.args[i]->term_cache->elimination_score);
                    for (j = 0; j < term->u.appl.args[i]->term_cache->word_count; ++j) {
                        term->term_cache->terms[j] |= c[j];
                    }
                }
            } else {
                goto def;
            }
            break;
        case EXP_QUANT:
            c = _th_get_active_terms(term->u.quant.exp);
            for (i = 0; i < term->u.quant.exp->term_cache->word_count; ++i) {
                term->term_cache->terms[i] = c[i];
            }
            for (; i < term->term_cache->word_count; ++i) {
                term->term_cache->terms[i] = 0;
            }
            c = _th_get_active_terms(term->u.quant.cond);
            for (i = 0; i < term->u.quant.cond->term_cache->word_count; ++i) {
                term->term_cache->terms[i] |= c[i];
            }
            _th_big_accumulate(term->term_cache->elimination_score, term->u.quant.cond->term_cache->elimination_score);
            _th_big_accumulate(term->term_cache->elimination_score, term->u.quant.exp->term_cache->elimination_score);
            break;
        default:
def:
            for (i = 0; i < term->term_cache->word_count; ++i) {
                term->term_cache->terms[i] = 0;
            }
    }
    term_n = _th_get_term_position(term);
    if (term_n >= 0) {
        //for (i = 0; i < term->term_cache->word_count; ++i) {
        //    term->term_cache->terms[i] |= dependency_table[term_n][i];
        //}
        term->term_cache->terms[term_n/32] |= (1<<(term_n%32));
        _th_big_accumulate_small(term->term_cache->elimination_score, 3);
    }

    //term_n = term_count(term->term_cache);
#ifdef SHOW_ACTIVE
    _tree_print1("term count = %d", j);
#endif

    term->term_cache->detail_max = 0;

    update_score_info(term);

#ifdef SHOW_ACTIVE
    _tree_undent();
#endif

    return term->term_cache->terms;
}

struct _ex_intern *_th_get_score(struct env *env, struct _ex_intern *e, struct _ex_intern *term)
{
    unsigned *l = _th_get_active_terms(e);
    int pos = _th_get_term_position(term);
    unsigned *score;
    struct term_detail *d;
    
    //printf("get score\n");

    if (pos >= e->term_cache->term_count || (l[pos/32] & (1<<(pos%32)))==0) {
        return _ex_intern_appl3_env(env,INTERN_TUPLE,_ex_intern_small_integer(0),e,e);
    }
    
    d = get_detail(e,pos);
    if (d==NULL) {
        return _ex_intern_appl3_env(env,INTERN_TUPLE,_ex_intern_small_integer(0),e,e);
    }

    score = _th_big_copy(REWRITE_SPACE,_th_big_add(d->pos_score,d->neg_score));

    //if (score < 0) score = 0x7fffffff;

    if (d->pos_exp==_ex_true ||
        d->neg_exp==_ex_true) {
        score[1] = -1;
        score[0] = 1;
    }

    return _ex_intern_appl3_env(env,INTERN_TUPLE,
        _ex_intern_integer(score),
        d->pos_exp,d->neg_exp);
}

int _th_has_a_term(struct _ex_intern *e)
{
    unsigned *t = _th_get_active_terms(e);
    int i;
    unsigned u;

    //printf("has_a_term\n");

    u = 0;
    for (i = 0; i < e->term_cache->word_count; ++i) {
        u |= e->term_cache->terms[i];
    }

    return u != 0;
}

struct term_data *_th_get_term_data_holder(struct _ex_intern *e, struct _ex_intern *term)
{
    int hash = ((((int)e)+((int)term))/4)%TERM_INFO_HASH;
    struct term_data_info *info = term_info[hash];

    while (info != NULL) {
        if (info->e==e && info->term==term) {
            return &info->data;
        }
        info = info->next;
    }

    info = (struct term_data_info *)_th_alloc(TERM_CACHE_SPACE,sizeof(struct term_data_info));
    //printf("a alloc %d\n", sizeof(struct term_data_info));
    info->next = term_info[hash];
    info->term = term;
    info->e = e;
    term_info[hash] = info;
    info->data.neg_term = NULL;
    info->data.pos_term = NULL;
    //info->data.term_count = -1;

    return &info->data;
}

int _th_get_elimination_score(struct _ex_intern *term)
{
    if (term->term_cache) {
        return term->term_cache->elimination_score[1];
    } else {
        return -1;
    }
}

void _th_set_elimination_score(struct _ex_intern *term, int score)
{
    _th_get_active_terms(term);

    //printf("set elimination score\n");

    term->term_cache->elimination_score[1] = score;
}

int _th_get_active_terms_word_count(struct _ex_intern *term)
{
    return term->term_cache->word_count;
}

static struct term_list *dependency_cache;
//static struct env *benv = NULL;

struct term_list *_th_get_dependency_cache()
{
    return dependency_cache;
}

void _th_clear_dependency_cache()
{
    int i;
    //if (benv==NULL) benv = _th_default_env(ENVIRONMENT_SPACE);
    dependency_cache = NULL;
    for (i = 0; i < TERM_HASH; ++i) {
        term_by_var[i] = NULL;
    }
}

static void check_valid_list(struct term_list *list)
{
    struct term_list *l, *l2;

    l = list;
    while (l != NULL) {
        struct dependencies *d = l->dependencies;
        while (d != NULL) {
            l2 = list;
            while (l2 != NULL) {
                if (l2==d->term) goto cont;
                l2 = l2->next;
            }
            fprintf(stderr, "Error in dependency list\n");
            exit(1);
cont:
            d = d->next;
        }
        l = l->next;
    }
}

static int can_completely_reduce(struct env *env, struct _ex_intern *e1, struct _ex_intern *e2)
{
    int count;
    unsigned *fv = _th_get_free_vars(e1,&count);
    int i, fc;

    if (count==1) return 1;

    fc = 0;
    for (i = 0; i < count; ++i) {
        if (_th_is_free_in(e2,fv[i])) {
            if (fc) return 1;
            ++fc;
        }
    }

    return 0;
}

static int do_pair_implications = 1;

static void augment_dependency_cache(struct env *env, struct add_list *list)
{
    struct term_list *l, *new_l;
    struct _ex_intern *used;
    struct dependencies *d, *nd;
    struct _ex_intern *e;
    int i;

    _zone_print0("Augmenting cache\n");
    _tree_indent();

    //printf("Augmenting %d\n", table_size);
    //fflush(stdout);

    l = dependency_cache;
    used = _ex_true;
    while (l) {
        l->e->user1 = used;
        used = l->e;
        l = l->next;
    }

    while (list) {
        if (!list->e->user1) {
            int t1 = _th_get_term_position(list->e);
            int count;
            unsigned *fv = _th_get_free_vars(list->e,&count);
            _zone_print_exp("Processing", list->e);
            _tree_indent();
            _zone_print1("number %d", t1);
            new_l = l = (struct term_list *)_th_alloc(TERM_CACHE_SPACE,sizeof(struct term_list));
            //printf("b alloc %d\n", sizeof(struct term_list));
            l->next = dependency_cache;
            dependency_cache = l;
            l->e = list->e;
            l->dependencies = NULL;
            l->neg_dependencies = NULL;
            //printf("Processing %s\n", _th_print_exp(l->e));
            //fflush(stdout);
            if (l->e->type != EXP_VAR && do_pair_implications) {
                for (i = 0; i < count; ++i) {
                    struct term_by_var *tbv;
                    struct t_by_var *tv;
                    int hash = fv[i]%TERM_HASH;
                    tbv = term_by_var[hash];
                    while (tbv) {
                        if (tbv->var==fv[i]) break;
                        tbv = tbv->next;
                    }
                    if (tbv) {
                        //printf("    fv[i] = %s\n", _th_intern_decode(fv[i]));
                        //fflush(stdout);
                        tv = tbv->terms;
                        while (tv) {
                            tv->terms->processed = 0;
                            tv = tv->next;
                        }
                    }
                }
                l = l->next;
                _zone_print0("Checking");
                _tree_indent();
                for (i = 0; i < count; ++i) {
                    struct term_by_var *tbv;
                    struct t_by_var *tv;
                    int hash = fv[i]%TERM_HASH;
                    tbv = term_by_var[hash];
                    while (tbv) {
                        if (tbv->var==fv[i]) break;
                        tbv = tbv->next;
                    }
                    if (tbv) {
                        tv = tbv->terms;
                    } else {
                        tv = NULL;
                    }
                    while (tv) {
                        l = tv->terms;
                        if (!l->processed) {
                            int t2 = _th_get_term_position(l->e);
                            if (t1 >=0 && t2 >= 0 && (e = _th_can_impact(env,dependency_cache->e,l->e))) {
                                dependency_table[t1][t2/32] |= (1<<(t2%32));
                                d = (struct dependencies *)_th_alloc(TERM_CACHE_SPACE,sizeof(struct dependencies));
                                //printf("c alloc %d\n", sizeof(struct dependencies));
                                _tree_undent();
                                _zone_print_exp("parent", dependency_cache->e);
                                _zone_print_exp("child", l->e);
                                _tree_indent();
                                _zone_print2("numbers %d %d", t1, t2);
                                d->next = dependency_cache->dependencies;
                                d->push_level = push_level;
                                d->term = l;
                                if (can_completely_reduce(env,dependency_cache->e,l->e)) {
                                    d->reduction = _th_nc_rewrite(env,e);
                                } else {
                                    d->reduction = e;
                                }
                                _zone_print_exp("reduction",d->reduction);
                                dependency_cache->dependencies = d;
                                if (d->reduction==_ex_true) {
                                    dependency_table[t2][t1/32] |= (1<<(t1%32));
                                    nd = (struct dependencies *)_th_alloc(TERM_CACHE_SPACE,sizeof(struct dependencies));
                                    //printf("d alloc %d\n", sizeof(struct dependencies));
                                    nd->next = l->neg_dependencies;
                                    l->neg_dependencies = nd;
                                    nd->term = dependency_cache;
                                    nd->reduction = _ex_false;
                                    nd->push_level = push_level;
                                    //} else if (d->reduction==_ex_false) {
                                    //    dependency_table[t2][t1/32] |= (1<<(t1%32));
                                    //    nd = (struct dependencies *)_th_alloc(TERM_CACHE_SPACE,sizeof(struct dependencies));
                                    //    nd->next = l->dependencies;
                                    //    l->dependencies = nd;
                                    //    nd->term = dependency_cache;
                                    //    nd->reduction = _ex_false;
                                }
                                _tree_undent();
                                _zone_print0("Checking");
                                _tree_indent();
                            }
                            if (t1>= 0 && t2 >= 0 && (e = _th_can_impact(env,l->e,dependency_cache->e))) {
                                dependency_table[t2][t1/32] |= (1<<(t1%32));
                                d = (struct dependencies *)_th_alloc(TERM_CACHE_SPACE,sizeof(struct dependencies));
                                //printf("e alloc %d\n", sizeof(struct dependencies));
                                _tree_undent();
                                _zone_print_exp("parent", l->e);
                                _zone_print_exp("child", dependency_cache->e);
                                _tree_indent();
                                _zone_print2("numbers %d %d", t2, t1);
                                d->push_level = push_level;
                                d->next = l->dependencies;
                                d->term = dependency_cache;
                                if (can_completely_reduce(env,l->e,dependency_cache->e)) {
                                     d->reduction = _th_nc_rewrite(env,e);
                                } else {
                                     d->reduction = e;
                                }
                                _zone_print_exp("reduction",d->reduction);
                                l->dependencies = d;
                                if (d->reduction==_ex_true) {
                                    dependency_table[t1][t2/32] |= (1<<(t2%32));
                                    nd = (struct dependencies *)_th_alloc(TERM_CACHE_SPACE,sizeof(struct dependencies));
                                    //printf("f alloc %d\n", sizeof(struct dependencies));
                                    nd->push_level = push_level;
                                    nd->next = dependency_cache->neg_dependencies;
                                    dependency_cache->neg_dependencies = nd;
                                    nd->term = l;
                                    nd->reduction = _ex_false;
                                    //} else if (d->reduction==_ex_false) {
                                    //    dependency_table[t1][t2/32] |= (1<<(t2%32));
                                    //    nd = (struct dependencies *)_th_alloc(TERM_CACHE_SPACE,sizeof(struct dependencies));
                                    //    nd->next = dependency_cache->dependencies;
                                    //    dependency_cache->dependencies = nd;
                                    //    nd->term = l;
                                    //    nd->reduction = _ex_false;
                                }
                                _tree_undent();
                                _zone_print0("Checking");
                                _tree_indent();
                            }
                        }
                        l->processed = 1;
                        tv = tv->next;
                    }
                }
                for (i = 0; i < count; ++i) {
                    struct term_by_var *tbv;
                    struct t_by_var *tv;
                    int hash = fv[i]%TERM_HASH;
                    tbv = term_by_var[hash];
                    while (tbv) {
                        if (tbv->var==fv[i]) break;
                        tbv = tbv->next;
                    }
                    if (tbv==NULL) {
                        tbv = (struct term_by_var *)_th_alloc(TERM_CACHE_SPACE,sizeof(struct term_by_var));
                        tbv->next = term_by_var[hash];
                        term_by_var[hash] = tbv;
                        tbv->terms = NULL;
                        tbv->var = fv[i];
                        //printf("Adding tbv %s\n", _th_intern_decode(fv[i]));
                    }
                    tv = (struct t_by_var *)_th_alloc(TERM_CACHE_SPACE,sizeof(struct t_by_var));
                    tv->next = tbv->terms;
                    //printf("Adding tv to %s of %x\n", _th_intern_decode(fv[i]), new_l);
                    tv->terms = new_l;
                    tv->terms->processed = 0;
                    tbv->terms = tv;
                }
                _tree_undent();
            }
            _tree_undent();
        }
        list = list->next;
    }

    while (used) {
        struct _ex_intern *n = used->user1;
        used->user1 = NULL;
        used = n;
    }

    _tree_undent();
}

static int member(struct _ex_intern *e, struct term_list *l)
{
    while (l != NULL) {
		if (l->e==e) {
			return 1;
		}
		l = l->next;
	}

	return 0;
}

static void extract_dependencies(struct term_list *list)
{
    struct term_list *l;
    struct dependencies *d, *nd;

    l = list;
    while (l != NULL) {
        //struct term_list *l2 = dependency_cache;
        //while (l2 != NULL) {
        //    if (l2->e==l->e) goto cont;
        //    l2 = l2->next;
        //}
        //fprintf(stderr,"List not subset\n");
        //fflush(stderr);
        //exit(1);
//cont:
        l->e->user2 = (struct _ex_intern *)l;
        l = l->next;
    }

    l = dependency_cache;
    while (l != NULL) {
        l->e->user1 = (struct _ex_intern *)l;
        l = l->next;
    }

    l = list;
    while (l != NULL) {
        if (l->e->user1) {
            d = ((struct term_list *)l->e->user1)->dependencies;
        } else {
            d = NULL;
        }
        l->dependencies = NULL;
        while (d != NULL) {
            if (d->term->e->user2 && member(d->term->e,list)) {
                nd = (struct dependencies *)_th_alloc(REWRITE_SPACE,sizeof(struct dependencies));
                nd->next = l->dependencies;
                nd->reduction = d->reduction;
                nd->push_level = push_level;
                //if (d->term->e->user2==NULL) {
                //    printf("Illegal dependency for %s\n", _th_print_exp(l->e));
                //    printf("    dependency: %s\n", _th_print_exp(d->term->e));
                //    exit(1);
                //}
                nd->term = (struct term_list *)d->term->e->user2;
                l->dependencies = nd;
            }
            d = d->next;
        }
        l->neg_dependencies = NULL;
        if (l->e->user1) {
            d = ((struct term_list *)l->e->user1)->neg_dependencies;
        } else {
            d = NULL;
        }
        while (d != NULL) {
            if (d->term->e->user2 && member(d->term->e,list)) {
                nd = (struct dependencies *)_th_alloc(REWRITE_SPACE,sizeof(struct dependencies));
                nd->next = l->neg_dependencies;
                nd->reduction = d->reduction;
                nd->push_level = push_level;
                //if (d->term->e->user2==NULL) {
                //    printf("Illegal dependency for %s\n", _th_print_exp(l->e));
                //    printf("    dependency: %s\n", _th_print_exp(d->term->e));
                //    exit(1);
                //}
                nd->term = (struct term_list *)d->term->e->user2;
                l->neg_dependencies = nd;
            }
            d = d->next;
        }
        l = l->next;
    }

    l = list;
    while (l) {
        d = l->dependencies;
        l->total_count = l->count;
        while (d != NULL) {
            l->total_count += d->term->count;
            d = d->next;
        }
        l = l->next;
    }

    l = list;
    while (l != NULL) {
        l->e->user2 = NULL;
        l = l->next;
    }

    l = dependency_cache;
    while (l != NULL) {
        l->e->user1 = NULL;
        l = l->next;
    }
}

void _th_fill_dependencies(struct env *env, struct term_list *list)
{
    extract_dependencies(list);
}

int last_size = 0;
struct add_list *new_list = NULL;

//static struct _ex_intern *nt = NULL;

void _th_new_term(struct _ex_intern *e)
{
    struct add_list *a;

    //if (nt==NULL) nt = _th_parse(_th_get_learn_env(),"(== x_92 x_50)");

    //if (e==nt) {
    //    fprintf(stderr, "Adding %s\n", _th_print_exp(nt));
    //    exit(1);
    //}

    if (lock_table) return;

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        fprintf(stderr, "Illegal term %s\n", _th_print_exp(e));
        exit(1);
    }
    //printf("New term %s\n", _th_print_exp(e));
    //fflush(stdout);

    a = (struct add_list *)_th_alloc(HEURISTIC_SPACE,sizeof(struct add_list));
    a->next = new_list;
    new_list = a;
    a->e = e;
}

int _th_pair_limit = 500;

//#define CHECK_REWRITTEN_COUNT 1
void _th_update_dependency_table(struct env *env, int do_augment)
{
    unsigned **nd;
    struct term_list *t;
    int c = 0;
    int i, j;
    struct add_list *al = new_list;

#ifdef CHECK_REWRITTEN_COUNT
    int total_count = 0;
    int rewritten_count = 0;
    struct _ex_intern *f;

    for (i = 0; i < table_size; ++i) {
        f = lookup_table[i];
        while (f != f->find) f = f->find;
        if (f != lookup_table[i]) f->user2 = _ex_true;
    }
    while (al) {
        f = al->e;
        while (f->find != f) f = f->find;
        if (f != al->e) {
            f->user2 = _ex_true;
        }
        al = al->next;
    }
    al = new_list;
    while (al) {
        ++total_count;
        if (al->e->user2 == _ex_true) {
            ++rewritten_count;
        }
        al = al->next;
    }

    //printf("Augmenting cache %d %d %d\n", table_size, total_count, rewritten_count);
    al = new_list;
    while (al) {
        f = al->e;
        if (f->user2) {
            printf("    Rewritten term %s\n", _th_print_exp(f));
        } else {
            printf("    Term %s\n", _th_print_exp(f));
        }
        while (f->find != f) f = f->find;
        if (f != al->e) {
            f->user2 = NULL;
        }
        al = al->next;
    }
    //fflush(stdout);
    for (i = 0; i < table_size; ++i) {
        f = lookup_table[i];
        while (f != f->find) f = f->find;
        if (f != lookup_table[i]) f->user2 = NULL;
    }
    al = new_list;
#endif

    //printf("Starting update %d\n", table_size);
    //fflush(stdout);

    //check_dependency_table();
    //if (!al) return;


    _zone_print0("Updating dependency table");
    _tree_indent();
    while (al) {
        ++c;
        al = al->next;
    }
    if (table_size + c > table_alloc_size) {
        while (table_alloc_size < table_size + c) {
            table_alloc_size += 8192;
        }
        nd = (unsigned **)_th_alloc(TERM_CACHE_SPACE,sizeof(unsigned *) * table_alloc_size);
        //printf("f alloc %d\n", sizeof(unsigned *) * table_alloc_size);
        for (i = 0; i < table_alloc_size; ++i) {
            nd[i] = (unsigned *)_th_alloc(TERM_CACHE_SPACE,sizeof(unsigned) * (table_alloc_size/32));
            //printf("g alloc %d\n", sizeof(unsigned) * (table_alloc_size/32));
        }
        for (i = 0; i < table_size; ++i) {
            for (j = 0; j < (table_size + 31)/32; ++j) {
                nd[i][j] = dependency_table[i][j];
            }
            while (j < table_alloc_size/32) {
                nd[i][j] = 0;
                ++j;
            }
        }
        //fprintf(stderr, "Updating dependency list %d %d\n", table_size, c);
        //fflush(stderr);
        
        while (i < table_alloc_size) {
            for (j = 0; j < table_alloc_size/32; ++j) {
                nd[i][j] = 0;
            }
            nd[i][i/32] = (1<<(i%32));
            ++i;
        }
        dependency_table = nd;
    }
    do_pair_implications = (table_size + c < _th_pair_limit);
    al = new_list;
    while (al != NULL) {
#ifdef SHOW_ACTIVE
        _tree_print_exp("Adding", al->e);
#endif
        new_term(al->e);
        al = al->next;
    }
    cd = 0;
    if (do_augment) augment_dependency_cache(env,new_list);
    new_list = NULL;
    pos_dependency_list = (struct dependencies **)_th_alloc(TERM_CACHE_SPACE,sizeof(struct dependencies *) * table_size);
    //printf("h alloc %d\n", sizeof(struct dependencies *) * table_size);
    neg_dependency_list = (struct dependencies **)_th_alloc(TERM_CACHE_SPACE,sizeof(struct dependencies *) * table_size);
    //printf("i alloc %d\n", sizeof(struct dependencies *) * table_size);
    //printf("Creating dependency table size %d\n", table_size);
    //fflush(stdout);
    for (i = 0; i < table_size; ++i) {
        pos_dependency_list[i] = 0;
        neg_dependency_list[i] = 0;
    }
    cd = 1;
    t = dependency_cache;
    while (t != NULL) {
        int p = _th_get_term_position(t->e);
        //_zone_print_exp("Adding dependencies for", t->e);
        //_zone_print1("pos %d", p);
        //_zone_print2("dependencies %d %d", t->dependencies, t->neg_dependencies);
        //fprintf(stderr, "Filling position %d\n", p);
        //fflush(stderr);
        pos_dependency_list[p] = t->dependencies;
        neg_dependency_list[p] = t->neg_dependencies;
        t = t->next;
    }

    lookup_table = (struct _ex_intern **)_th_alloc(TERM_CACHE_SPACE,table_size * sizeof(struct _ex_intern *));
    //printf("Allocating lookup_table %x %d\n", lookup_table, table_size * sizeof(struct _ex_intern *));

    //for (i = 0; i < table_size; ++i) {
    //    lookup_table[i] = NULL;
    //}
    //printf("j alloc %d\n", sizeof(struct _ex_intern *) * table_size);

    //_tree_print1("Looking up %d\n", index);
    for (i = 0; i < TERM_HASH; ++i) {
        struct term_lookup *t = table[i];
        while (t != NULL) {
            //_tree_print2("Testing %d %s", t->position, _th_print_exp(t->term));
            lookup_table[t->position] = t->term;
            t = t->next;
        }
    }
    //for (i = 0; i < table_size; ++i) {
    //    if (lookup_table[i]==NULL) {
    //        fprintf(stderr, "Position %d unfilled in lookup table\n", i);
    //        exit(1);
    //    }
    //}
    _tree_undent();
    //printf("Finishing update %d\n", table_size);
    //fflush(stdout);
    //check_dependency_table();
}

struct dependencies *_th_get_dependencies(struct _ex_intern *t)
{
    int p = _th_get_term_position(t);
    if (p < 0) return NULL;

    return pos_dependency_list[p];
}

struct dependencies *_th_get_neg_dependencies(struct _ex_intern *t)
{
    int p = _th_get_term_position(t);
    if (p < 0) return NULL;

    return neg_dependency_list[p];
}

void _th_init_term_cache()
{
    int i;
    new_list = NULL;
    last_size = 0;
    _th_clear_dependency_cache();
    pos_dependency_list = NULL;
    neg_dependency_list = NULL;
    update_list = NULL;
    root = NULL;

    for (i = 0; i < TERM_INFO_HASH; ++i) {
        term_info[i] = NULL;
    }

    for (i = 0; i < TERM_DETAIL_SIZE; ++i) {
        term_details[i] = NULL;
    }
}

int _th_check_term(struct _ex_intern *e, int index)
{
    unsigned *l = _th_get_active_terms(e);
    int x = e->term_cache->word_count;
    int i;
    //printf("check term\n");

    for (i = 0; i < x; ++i) {
        if (l[i] & dependency_table[index][i]) return 1;
    }

    return 0;
}

static void check_for_or_true(struct _ex_intern *e, int n)
{
    int i;

    if (e->type==EXP_APPL) {
        if (e->u.appl.functor==INTERN_OR) {
            for (i = 0; i < e->u.appl.count; ++i) {
                if (e->u.appl.args[i]==_ex_true) {
                    fprintf(stderr, "or true %d\n", n);
                    exit(1);
                }
            }
        }
        for (i = 0; i < e->u.appl.count; ++i) {
            check_for_or_true(e->u.appl.args[i], n);
        }
    }
}

struct _ex_intern *t_rewrite(struct env *env, struct _ex_intern *e, int index)
{
    struct _ex_intern **args, *f, *g, *h;
    int i, j, k;
    unsigned *l = _th_get_active_terms(e);

    //printf("t_rewrite\n");

    _zone_print_exp("t_rewrite", e);

    f = (e->can_cache?_th_get_cache_rewrite(env,e,1):NULL) ;
    //_zone_print_exp("f", f);
    if (f) {
        //check_for_or_true(f,1);
        return f;
    }

    //_zone_print1("index = %d", index);
    if (!_th_check_term(e,index)) return e;
    //_zone_print0("has term");

    if (e->type != EXP_APPL) {
        _tree_print_exp("Rewritng", e);
        return _th_int_rewrite(env,e,1);
    }

    switch (e->u.appl.functor) {
        case INTERN_AND:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            for (i = 0, j = 0; i < e->u.appl.count; ++i) {
                _zone_print1("pos %d", j);
                args[j] = t_rewrite(env,e->u.appl.args[i],index);
                if (args[j]==_ex_false) return _ex_false;
                for (k = 0; k < j; ++k) {
                    if (args[j]==args[k]) goto cont;
                }
                if (args[j]!=_ex_true) ++j;
cont:;
            }
            if (j==0) return _ex_true;
            if (j==1) return args[0];
            h = _th_flatten_top(env,_ex_intern_appl_env(env,INTERN_AND,j,args));
            if (e != h) {
                g = _th_simplify_and(env,h);
            } else {
                g = NULL;
            }
            if (g==NULL) {
                _th_set_cache_rewrite(env,e,h,1,0);
                //check_for_or_true(h,2);
                return h;
            }
            if (g != e) {
                g = t_rewrite(env,g,index);
                _th_set_cache_rewrite(env,e,g,1,0);
                //check_for_or_true(g,3);
                return g;
            }
            _th_set_cache_rewrite(env,e,g,1,0);
            //check_for_or_true(g,4);
            return g;
        case INTERN_OR:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            for (i = 0, j = 0; i < e->u.appl.count; ++i) {
                _zone_print1("pos %d", j);
                args[j] = t_rewrite(env,e->u.appl.args[i],index);
                if (args[j]==_ex_true) return _ex_true;
                for (k = 0; k < j; ++k) {
                    if (args[j]==args[k]) goto cont2;
                }
                if (args[j]!=_ex_false) {
                    ++j;
                }
cont2:;
            }
            if (j==0) return _ex_false;
            if (j==1) return args[0];
            h = _ex_intern_appl_env(env,INTERN_OR,j,args);
            h = _th_flatten_top(env,h);
            if (e != h) {
                g = _th_simplify_or(env,h);
            } else {
                g = NULL;
            }
            if (g==NULL) {
                _th_set_cache_rewrite(env,e,h,1,0);
                //check_for_or_true(h,5);
                return h;
            }
            if (g != e) {
                g = _th_int_rewrite(env,g,1);
                _th_set_cache_rewrite(env,e,g,1,0);
                check_for_or_true(g,6);
                return g;
            }
            _th_set_cache_rewrite(env,e,g,1,0);
            //check_for_or_true(g,7);
            return g;
        case INTERN_NOT:
            f = t_rewrite(env,e->u.appl.args[0],index);
            if (f==_ex_false) {
                _th_set_cache_rewrite(env,e,_ex_true,1,0);
                return _ex_true;
            } else if (f==_ex_true) {
                _th_set_cache_rewrite(env,e,_ex_false,1,0);
                return _ex_false;
            } else if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NOT) {
                _th_set_cache_rewrite(env,e,f->u.appl.args[0],1,0);
                //check_for_or_true(f->u.appl.args[0],8);
                return f->u.appl.args[0];
            } else {
                f = _ex_intern_appl1_env(env,INTERN_NOT,f);
                g = _th_strengthen_in_context(env,f);
                if (g != NULL && g != f) {
                    f = t_rewrite(env,g,index);
                }
                _th_set_cache_rewrite(env,e,f,1,0);
                //check_for_or_true(f,9);
                return f;
            }
        case INTERN_ITE:
            f = t_rewrite(env,e->u.appl.args[0],index);
            if (f==_ex_true) {
                f = t_rewrite(env,e->u.appl.args[1],index);
            } else if (f==_ex_false) {
                f = t_rewrite(env,e->u.appl.args[2],index);
            } else {
                g = _ex_intern_appl3_env(env,INTERN_ITE,f,t_rewrite(env,e->u.appl.args[1],index),t_rewrite(env,e->u.appl.args[2],index));
                h = _th_simplify_ite(env,g);
                if (h==NULL) {
                    f = g;
                } else if (h != e) {
                    f = t_rewrite(env,h,index);
                } else {
                    f = h;
                }
            }
            _th_set_cache_rewrite(env,e,f,1,0);
            //check_for_or_true(f,10);
            return f;
        default:
            _tree_print_exp("Rewriting ", e);
            e = _th_int_rewrite(env,e,1);
            //check_for_or_true(e,11);
            return e;
    }
}

struct _ex_intern *_th_term_rewrite(struct env *env, struct _ex_intern *e, struct _ex_intern *term)
{
    char *mark ;
    struct _ex_intern *res;
    static int r_count = 0;
    int n = _th_get_term_position(term);

    _tree_print_exp("_th_term_rewrite", term);
    _tree_indent();

#ifdef NUMBER_REWRITES
    int old_tree_mute = _tree_mute;
#endif

    //printf("Rewriting %s\n", _th_print_exp(e));

    //if (e==NULL) return NULL ;
    if (e==_ex_true || e==_ex_false) {
        _tree_undent();
        return e;
    }

#ifdef LOG_REWRITE
    if (rewrite_log_file==NULL) {
        rewrite_log_file = fopen("log.rew", "w");
    }
#endif

#ifdef NUMBER_REWRITES
    if (e != _ex_true) _tree_print2("Rewriting %d %s", r_count, _th_print_exp(e)) ;
#ifdef SHOW_REWRITE
    if (r_count==SHOW_REWRITE) {
        _tree_start = 0;
        _tree_end = 2000000;
        _tree_sub = _tree_sub2 = -1;
        _tree_mute = 0;
    }
    if (r_count > SHOW_REWRITE) exit(1);
#endif
    ++r_count;
#endif
#ifdef LOG_REWRITE
    fprintf(rewrite_log_file,"rewrite %d: %s\n", r_count, _th_print_exp(e));
    fflush(rewrite_log_file);
#endif
    _zone_increment() ;
    res = _th_check_rewrite(e) ;
    if (res) {
        _tree_print_exp("From memory", res);
#ifdef NUMBER_REWRITES
        _tree_mute = old_tree_mute;
        _tree_indent();
        if (e != _ex_true) _tree_print_exp("result", res);
        _tree_undent();
#endif
#ifdef LOG_REWRITE
        fprintf(rewrite_log_file,"result %d: %s\n", r_count-1, _th_print_exp(res));
        fflush(rewrite_log_file);
#endif
        _tree_undent();
        return res ;
    }
    if (_th_in_rewrite) {
		_zone_enter_sub();
        res = _th_int_rewrite(env,e,1) ;
		_zone_exit_sub();
        _zone_print_exp("Result", e);
        _th_set_rewrite(res);
#ifdef NUMBER_REWRITES
        _tree_mute = old_tree_mute;
        _tree_indent();
        if (e != _ex_true) _tree_print_exp("result", res);
        _tree_undent();
#endif
#ifdef LOG_REWRITE
        fprintf(rewrite_log_file,"result %d: %s\n", r_count-1, _th_print_exp(res));
        fflush(rewrite_log_file);
#endif
        _tree_undent();
        return res ;
    }

    _th_clear_cache() ;
    _th_rewrite_next = _th_add_contexts_to_cache(env,_th_rewrite_next);
    mark = _th_start_rewrite() ;
	res = e;
	e = NULL;
	_zone_enter_sub();
    res = t_rewrite(env,res,n) ;
	_zone_exit_sub();
    res = _th_finish_rewrite(mark, env, res) ;

    _th_set_rewrite(res) ;

    _zone_print_exp("Result", res);

#ifdef NUMBER_REWRITES
    _tree_mute = old_tree_mute;
    _tree_indent();
    if (res != _ex_true) _tree_print_exp("result", res);
    _tree_undent();
#endif
#ifdef LOG_REWRITE
    fprintf(rewrite_log_file,"result %d: %s\n", r_count-1, _th_print_exp(res));
    fflush(rewrite_log_file);
#endif
    _tree_undent();
    return res ;
}

struct _ex_intern *ts_rewrite(struct env *env, struct _ex_intern *e, unsigned *index)
{
    struct _ex_intern **args, *f, *g, *h;
    int i, j, k;
    unsigned *l;
    
    l = _th_get_active_terms(e);

    //printf("ts_rewrite\n");

    _zone_print_exp("ts_rewrite", e);
    _tree_indent();

    f = (e->can_cache?_th_get_cache_rewrite(env,e,1):NULL) ;
    if (f) {
        _tree_undent();
        return f;
    }

    for (i = 0; i < e->term_cache->word_count; ++i) {
        _zone_print2("%d - %x", i, l[i]);
        if (index[i] & l[i]) goto cont;
    }
    _tree_undent();
    return e;
cont:
    _tree_undent();

    if (e->type != EXP_APPL) return _th_int_rewrite(env,e,1);

    switch (e->u.appl.functor) {
        case INTERN_AND:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            for (i = 0, j = 0; i < e->u.appl.count; ++i) {
                _zone_print1("pos %d", j);
                args[j] = ts_rewrite(env,e->u.appl.args[i],index);
                if (args[j]==_ex_false) return _ex_false;
                for (k = 0; k < j; ++k) {
                    if (args[j]==args[k]) goto cont1;
                }
                if (args[j]!=_ex_true) ++j;
cont1:;
            }
            if (j==0) return _ex_true;
            if (j==1) return args[0];
            h = _th_flatten_top(env,_ex_intern_appl_env(env,INTERN_AND,j,args));
            if (e != h) {
                g = _th_simplify_and(env,h);
            } else {
                g = NULL;
            }
            if (g==NULL) {
                _th_set_cache_rewrite(env,e,h,1,0);
                return h;
            }
            if (g != e) {
                g = ts_rewrite(env,g,index);
                _th_set_cache_rewrite(env,e,g,1,0);
                return g;
            }
            _th_set_cache_rewrite(env,e,g,1,0);
            return g;
        case INTERN_OR:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            for (i = 0, j = 0; i < e->u.appl.count; ++i) {
                _zone_print1("pos %d", j);
                args[j] = ts_rewrite(env,e->u.appl.args[i],index);
                if (args[j]==_ex_true) return _ex_true;
                for (k = 0; k < j; ++k) {
                    if (args[j]==args[k]) goto cont2;
                }
                if (args[j]!=_ex_false) ++j;
cont2:;
            }
            if (j==0) return _ex_false;
            if (j==1) return args[0];
            h = _th_flatten_top(env,_ex_intern_appl_env(env,INTERN_OR,j,args));
            if (e != h) {
                g = _th_simplify_or(env,h);
            } else {
                g = NULL;
            }
            if (g==NULL) {
                _th_set_cache_rewrite(env,e,h,1,0);
                return h;
            }
            if (g != e) {
                g = _th_int_rewrite(env,g,1);
                _th_set_cache_rewrite(env,e,g,1,0);
                return g;
            }
            _th_set_cache_rewrite(env,e,g,1,0);
            return g;
        case INTERN_NOT:
            f = ts_rewrite(env,e->u.appl.args[0],index);
            if (f==_ex_false) {
                _th_set_cache_rewrite(env,e,_ex_true,1,0);
                return _ex_true;
            } else if (f==_ex_true) {
                _th_set_cache_rewrite(env,e,_ex_false,1,0);
                return _ex_false;
            } else if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NOT) {
                _th_set_cache_rewrite(env,e,f->u.appl.args[0],1,0);
                return f->u.appl.args[0];
            } else {
                f = _ex_intern_appl1_env(env,INTERN_NOT,f);
                g = _th_strengthen_in_context(env,f);
                if (g != NULL && g != f) {
                    f = ts_rewrite(env,g,index);
                }
                _th_set_cache_rewrite(env,e,f,1,0);
                return f;
            }
        case INTERN_ITE:
            f = ts_rewrite(env,e->u.appl.args[0],index);
            if (f==_ex_true) {
                f = ts_rewrite(env,e->u.appl.args[1],index);
            } else if (f==_ex_false) {
                f = ts_rewrite(env,e->u.appl.args[2],index);
            } else {
                g = _ex_intern_appl3_env(env,INTERN_ITE,f,ts_rewrite(env,e->u.appl.args[1],index),ts_rewrite(env,e->u.appl.args[2],index));
                h = _th_simplify_ite(env,g);
                if (h==NULL) {
                    f = g;
                } else if (h != e) {
                    f = ts_rewrite(env,h,index);
                } else {
                    f = h;
                }
            }
            _th_set_cache_rewrite(env,e,f,1,0);
            return f;
        default:
            return _th_int_rewrite(env,e,1);
    }
}

struct _ex_intern *_th_terms_rewrite(struct env *env, struct _ex_intern *e, struct add_list *terms)
{
    char *mark ;
    struct _ex_intern *res;
    static int r_count = 0;
    unsigned *index;
    int i, s;

    _zone_print_exp("terms_rewrite", e);
    _tree_indent();

    s = ((table_size+31)/32);
    index = (unsigned *)ALLOCA(sizeof(unsigned *) * s);
    for (i = 0; i < s; ++i) {
        index[i] = 0;
    }

    print_term_indices();
    _zone_print0("Terms");
    _tree_indent();
    while (terms != NULL) {
        struct _ex_intern *f = terms->e;
        int x;
        unsigned *l;
        _zone_print_exp("t", terms->e);
        _tree_indent();
        if (f->type==EXP_APPL && f->u.appl.functor==INTERN_NOT) f = f->u.appl.args[0];
        x = _th_get_term_position(f);
        _zone_print1("pos %d",x);
        if (x < 0) {
            fprintf(stderr,"Term error\n");
            exit(1);
        } 
        l = dependency_table[x];
        _zone_print0("mask");
        _tree_indent();
        for (i = 0; i < s; ++i) {
            _zone_print1("%x", l[i]);
            index[i] |= l[i];
            _zone_print2("l[%d] = %x", i, l[i]);
        }
        _tree_undent();
        _tree_undent();
        terms = terms->next;
    }
    _tree_undent();

#ifdef NUMBER_REWRITES
    int old_tree_mute = _tree_mute;
#endif

    //printf("Rewriting %s\n", _th_print_exp(e));

    //if (e==NULL) return NULL ;
    if (e==_ex_true || e==_ex_false) return e;

#ifdef LOG_REWRITE
    if (rewrite_log_file==NULL) {
        rewrite_log_file = fopen("log.rew", "w");
    }
#endif

#ifdef NUMBER_REWRITES
    if (e != _ex_true) _tree_print2("Rewriting %d %s", r_count, _th_print_exp(e)) ;
#ifdef SHOW_REWRITE
    if (r_count==SHOW_REWRITE) {
        _tree_start = 0;
        _tree_end = 2000000;
        _tree_sub = _tree_sub2 = -1;
        _tree_mute = 0;
    }
    if (r_count > SHOW_REWRITE) exit(1);
#endif
    ++r_count;
#endif
#ifdef LOG_REWRITE
    fprintf(rewrite_log_file,"rewrite %d: %s\n", r_count, _th_print_exp(e));
    fflush(rewrite_log_file);
#endif
    _zone_increment() ;
    res = _th_check_rewrite(e) ;
    if (res) {
        _tree_print_exp("From memory", res);
#ifdef NUMBER_REWRITES
        _tree_mute = old_tree_mute;
        _tree_indent();
        if (e != _ex_true) _tree_print_exp("result", res);
        _tree_undent();
#endif
#ifdef LOG_REWRITE
        fprintf(rewrite_log_file,"result %d: %s\n", r_count-1, _th_print_exp(res));
        fflush(rewrite_log_file);
#endif
        return res ;
    }
    if (_th_in_rewrite) {
		_zone_enter_sub();
        res = _th_int_rewrite(env,e,1) ;
		_zone_exit_sub();
        _zone_print_exp("Result", e);
        _th_set_rewrite(res);
#ifdef NUMBER_REWRITES
        _tree_mute = old_tree_mute;
        _tree_indent();
        if (e != _ex_true) _tree_print_exp("result", res);
        _tree_undent();
#endif
#ifdef LOG_REWRITE
        fprintf(rewrite_log_file,"result %d: %s\n", r_count-1, _th_print_exp(res));
        fflush(rewrite_log_file);
#endif
        _tree_undent();
        return res ;
    }

    _th_clear_cache() ;
    _th_rewrite_next = _th_add_contexts_to_cache(env,_th_rewrite_next);
    mark = _th_start_rewrite() ;
	res = e;
	e = NULL;
	_zone_enter_sub();
    res = ts_rewrite(env,res,index) ;
	_zone_exit_sub();
    res = _th_finish_rewrite(mark, env, res) ;

    _th_set_rewrite(res) ;

    _zone_print_exp("Result", res);

#ifdef NUMBER_REWRITES
    _tree_mute = old_tree_mute;
    _tree_indent();
    if (res != _ex_true) _tree_print_exp("result", res);
    _tree_undent();
#endif
#ifdef LOG_REWRITE
    fprintf(rewrite_log_file,"result %d: %s\n", r_count-1, _th_print_exp(res));
    fflush(rewrite_log_file);
#endif

    _tree_undent();

    return res ;
}

struct dep_list {
    struct dep_list *next;
    struct dependencies *dependencies;
    struct dependencies *neg_dependencies;
};

struct mark_info {
    struct mark_info *parent;
    char *mark;
    struct term_detail *term_details[TERM_DETAIL_SIZE];
    struct term_list *dependency_cache;
    unsigned **dependency_table;
    struct dep_list *dep_list;
    int table_size;
    int table_alloc_size;
    int lock_table;
    struct term_cache *root;
    struct dependencies **pos_dependency_list;
    struct dependencies **neg_dependency_list;
    struct update_list *update_list;
    struct term_lookup *table[TERM_HASH];
    struct term_by_var *term_by_var[TERM_HASH];
    struct _ex_intern **lookup_table;
};

struct mark_info *last_mark;

//static struct mark_info *ppop = NULL;

static char *the_last_mark = NULL;

void check_last_mark(char *place)
{
    if (_th_alloc_check_release(TERM_CACHE_SPACE,the_last_mark)) {
        fprintf(stderr, "Alloc release check failure %s %x\n", place, the_last_mark);
        exit(1);
    }
}

static struct term_by_var *copy_tbv(struct term_by_var *tbv)
{
    struct term_by_var *ret, *t, *p;

    ret = p = NULL;

    while (tbv) {
        t = (struct term_by_var *)_th_alloc(TERM_CACHE_SPACE,sizeof(struct term_by_var));
        t->next = NULL;
        if (p) {
            p->next = t;
        } else {
            ret = t;
        }
        t->terms = tbv->terms;
        t->var = tbv->var;
        p = t;
        tbv = tbv->next;
    }

    return ret;
}

struct mark_info *_th_term_cache_push()
{
    int i;
    char *mark = _th_alloc_mark(TERM_CACHE_SPACE);
    struct mark_info *td = (struct mark_info *)_th_alloc(TERM_CACHE_SPACE,sizeof(struct mark_info));
    struct term_list *t;
    struct dep_list *pd;
    //printf("k alloc %d\n", sizeof(struct mark_info));

    the_last_mark = mark;

    //ppop = NULL;

    //printf("*** PUSH *** %x %d %d\n", td, table_size, push_level);
    //fflush(stderr);

    //printf("Pushing table size %d\n", table_size);
    //printf("Pushing table %x\n", lookup_table);
    //printf("term_by_var[525] = %x\n", term_by_var[525]);
    //fflush(stdout);

    //check_last_mark("Here1");

    td->mark = mark;
    //_tree_print1("push mark %x", td->mark);
    td->lock_table = lock_table;
    td->lookup_table = lookup_table;
    td->dependency_cache = dependency_cache;
    td->table_size = table_size;
    td->table_alloc_size = table_alloc_size;
    td->parent = last_mark;
    td->dependency_table = dependency_table;
    td->pos_dependency_list = pos_dependency_list;
    td->neg_dependency_list = neg_dependency_list;
    td->update_list = update_list;
    for (i = 0; i < TERM_HASH; ++i) {
        td->table[i] = table[i];
        td->term_by_var[i] = term_by_var[i];
        term_by_var[i] = copy_tbv(term_by_var[i]);
    }
    //check_last_mark("Here2");

    for (i = 0; i < TERM_DETAIL_SIZE; ++i) {
        td->term_details[i] = term_details[i];
    }
    //check_last_mark("Here3");

    t = dependency_cache;
    pd = NULL;
    td->dep_list = NULL;
    //while (t) {
    //    d = (struct dep_list *)_th_alloc(TERM_CACHE_SPACE,sizeof(struct dep_list));
    //    printf("l alloc %d %d\n", sizeof(struct dep_list), push_level);
    //    if (pd) {
    //        pd->next = d;
    //    } else {
    //        td->dep_list = d;
    //    }
    //    d->dependencies = t->dependencies;
    //    d->neg_dependencies = t->neg_dependencies;
    //    pd = d;
    //    t = t->next;
    //}
    //if (pd) {
    //    pd->next = NULL;
    //} else {
    //    td->dep_list = NULL;
    //}

    //check_last_mark("Here4");

    td->root = root;

    last_mark = td;

    ++push_level;

    //check_last_mark("Here5");

    //printf("after term_by_var[525] = %x\n", term_by_var[525]);
    //fflush(stdout);
    return td;
}

static unsigned mask[32] = {
        0x1, 0x3, 0x7, 0xf, 0x1f, 0x3f, 0x7f, 0xff,
        0x1ff, 0x3ff, 0x7ff, 0xfff, 0x1fff, 0x3fff, 0x7fff, 0xffff,
        0x1ffff, 0x3ffff, 0x7ffff, 0xfffff, 0x1fffff, 0x3fffff, 0x7fffff, 0xffffff,
        0x1ffffff, 0x3ffffff, 0x7ffffff, 0xfffffff, 0x1fffffff, 0x3fffffff, 0x7fffffff,
        0xffffffff };

void incremental_clear(int table_size, int reduced_size)
{
    int i, j;

    //printf("Reducing from %d to %d\n", table_size, reduced_size);
    //fflush(stdout);

    if (reduced_size==table_size) {
        return;
    }

    for (i = reduced_size; i < table_size; ++i) {
        for (j = 0; j < (table_size+31)/32; ++j) {
            dependency_table[i][j] = 0;
        }
    }
    //printf("Masking %d with %x\n", (reduced_size-1)/32, mask[(reduced_size+31)%32]);
    //printf("top = %d\n", (table_size+31)/32);

    for (i = 0; i < reduced_size; ++i) {
        if (reduced_size > 0) {
            dependency_table[i][(reduced_size-1)/32] &= mask[(reduced_size+31)%32];
            for (j = ((reduced_size-1)/32)+1; j < (table_size+31)/32; ++j) {
                dependency_table[i][j] = 0;
            }
        } else {
            for (j = 0; j < (table_size+31)/32; ++j) {
                dependency_table[i][j] = 0;
            }
        }
    }
}

void _th_term_cache_pop(struct mark_info *td)
{
    struct term_list *t;
    struct dep_list *d;
    int i, cl;
    //struct term_cache *tc;

    --push_level;

    //printf("Popping table size %d %d\n", table_size, td->table_size);
    //printf("Dependency tables %x %x\n", dependency_table, td->dependency_table);
    //printf("term_by_var[525] = %x\n", term_by_var[525]);
    //fflush(stdout);

    //printf("*** POP *** %x %d %d\n", td, table_size, push_level);
    //fflush(stderr);
    //printf("Popping table %x\n", lookup_table);

    //if (ppop==td) {
    //    int x = 0;
    //    x = 1/x;
    //    exit(1);
    //}
    //ppop = td;

    if (dependency_table==td->dependency_table && table_size > td->table_size) {
        //printf("Incremental clear %d\n", td->table_alloc_size, table_alloc_size);
        incremental_clear(table_size, td->table_size);
    }
    if (dependency_table!=td->dependency_table) {
        cl = 1;
    } else {
        cl = 0;
    }
    //if (dependency_table != td->dependency_table) {
    //    printf("Alloc reduction %d %d\n", table_alloc_size, td->table_alloc_size);
    //}
    dependency_table = td->dependency_table;
    pos_dependency_list = td->pos_dependency_list;
    neg_dependency_list = td->neg_dependency_list;
    t = dependency_cache = td->dependency_cache;
    lock_table = td->lock_table;
    d = td->dep_list;
    while (t != NULL) {
        while (t->dependencies && t->dependencies->push_level > push_level) {
            t->dependencies = t->dependencies->next;
        }
        while (t->neg_dependencies && t->neg_dependencies->push_level > push_level) {
            t->neg_dependencies = t->neg_dependencies->next;
        }
        //if (t->dependencies != d->dependencies) {
        //    fprintf(stderr, "Dependency error\n");
        //    exit(1);
        //}
        //if (t->neg_dependencies != d->neg_dependencies) {
        //    fprintf(stderr, "Neg dependency error\n");
        //    exit(1);
        //}
        //d = d->next;
        t = t->next;
    }
    if (t != NULL) {
        fprintf(stderr, "Dependency cache error\n");
        exit(1);
    }

    table_size = td->table_size;
    table_alloc_size = td->table_alloc_size;
    lookup_table = td->lookup_table;
    if (cl) {
        incremental_clear(table_alloc_size, table_size);
    }

    for (i = 0; i < TERM_HASH; ++i) {
        table[i] = td->table[i];
        term_by_var[i] = td->term_by_var[i];
    }

    for (i = 0; i < TERM_DETAIL_SIZE; ++i) {
        term_details[i] = td->term_details[i];
    }

    while (root != td->root) {
        root->term->term_cache = NULL;
        root = root->next;
    }

    last_mark = td->parent;

    while (update_list != td->update_list) {
        //int d = update_list->detail_max;
        update_list->cache->detail_max = update_list->detail_max;
        //if (d > 0) {
        //    update_list->cache->terms[(d+31)/32] &= mask[(d+31)%32];
        //    for (i = ((d+31)/32)+1; i < update_list->cache->word_count; ++i) {
        //        update_list->cache->terms[i] = 0;
        //    }
        //} else {
        //    for (i = 0; i < update_list->cache->word_count; ++i) {
        //        update_list->cache->terms[i] = 0;
        //    }
        //}
        update_list = update_list->next;
    }

#ifdef XX
    tc = root;
    while (tc) {
        //printf("Cleaning %s\n", _th_print_exp(tc->term));
        //printf("Cleaning %x\n", tc->term);
        //printf("tc->term_count, tc->table_size = %d %d\n", tc->term_count, table_size);
        //fflush(stdout);
        if (tc->detail_max >= table_size) {
            tc->term_count = 0;
            tc->detail_max = 0;
            for (i = 0; i < tc->word_count; ++i) {
                tc->terms[i] = 0;
            }
        }
        tc = tc->next;
    }
#endif

    //_tree_print1("pop mark %x", td->mark);
    _th_alloc_release(TERM_CACHE_SPACE,td->mark);
    the_last_mark = NULL;

    //printf("after term_by_var[525] = %x\n", term_by_var[525]);
    //fflush(stdout);
}
