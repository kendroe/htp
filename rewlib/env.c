//#define CHECK_CACHE
/*
 * env.c
 *
 * Environment maintenance data structures
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>

#include "Globals.h"
#include "Intern.h"

struct attribute {
        struct attribute *next ;
        unsigned name ;
        int parameter_count ;
        struct parameter parameters[1] ;
    } ;

#define PRECEDENCE_HASH_SIZE 19

struct PrecNode {
    struct PrecNode *next ;
    unsigned symbol ;
} ;

struct symbol_info {
    struct symbol_info *next ;
    unsigned symbol ;
    struct _ex_intern *prototype ;
    struct _ex_intern *type_functor ;
    struct _ex_intern *type_definition ;
    struct _ex_intern *type ;
    struct _ex_intern *condition ;
    struct _ex_intern *var_type ;
    struct _ex_intern *definition ;
    struct attribute *attr ;

    /* Bits for order properties */
    /*int is_associative : 1 ;*/
    /*int is_communitive : 1 ;*/
    /*int is_order : 1 ;*/
    /*int is_partial_order : 1 ;*/
    /*int is_equal_order : 1 ;*/
    /*int is_equal_partial_order : 1 ;*/

    int attribute_flags;

    int is_finite_type : 1 ;
    int is_finite_constructor : 1 ;
    int is_constructor : 1 ;
    int mark : 1 ;

    int context_level ;
    struct symbol_info *next_context_mark ;

    /* Precedence information */
    unsigned equal_group ;
    struct PrecNode *smaller[PRECEDENCE_HASH_SIZE], *larger[PRECEDENCE_HASH_SIZE] ;
    struct Node *minor_smaller, *minor_larger ;
    unsigned last_entered_minor_smaller, last_entered_minor_larger ;
    struct prex_info *prex_info ;
    unsigned *lex_order ;
} ;

struct rule {
    struct rule *next ;
    struct _ex_intern *rule ;
} ;

#define RULE_OPERAND_HASH 1023

struct rule_operand_list {
	struct rule_operand_list *next;
	struct _ex_intern *operand;
	struct _ex_intern *rule;
};

struct rule_double_operand_list {
	struct rule_double_operand_list *next;
	struct _ex_intern *left_operand;
	struct _ex_intern *right_operand;
	struct _ex_intern *rule;
};

#define MIN_MAX_HASH 1023

struct min_max_list {
	struct min_max_list *next;
	struct _ex_intern *exp;
	struct _ex_intern *value;
    int inclusive;
};

#define VAR_SOLVE_HASH 511

struct var_solve_list {
	struct var_solve_list *next;
	unsigned var;
	struct _ex_intern *rule;
};

#define DIFF_NODE_HASH 511

struct ne_list {
    struct ne_list *next;
	struct _ex_intern *e;
    struct diff_node *target;
    struct _ex_intern *offset;
	struct diff_node *orig_source;
	struct _ex_intern *orig_offset;
};

struct diff_node {
    struct diff_node *next;
    struct diff_edge *edges;
    struct diff_edge *source_edges;
    struct _ex_intern *e;
    struct _ex_intern *limit;
    int limit_delta;
    struct _ex_intern *bottom;
    int bottom_delta;
    int has_limit, has_bottom;
    struct add_list *limit_explanation, *bottom_explanation;
    struct _ex_intern *limit2;
    int limit_delta2;
    struct _ex_intern *bottom2;
    int bottom_delta2;
    int has_limit2, has_bottom2;
    struct add_list *limit_explanation2, *bottom_explanation2;
    struct ne_list *ne_list;
	struct diff_node *eq_merge;
	struct add_list *eq_explanation;
	struct _ex_intern *eq_offset;
	struct diff_node *move, *move_back;
    int visited;
};

struct diff_edge {
    struct diff_edge *next;
    struct diff_edge *source_next;
    struct diff_node *target;
    struct diff_node *source;
    struct _ex_intern *offset;
    struct add_list *explanation;
    int delta;
};

struct context_stack {
    struct context_stack *next ;
    struct small_disc *context_properties ;
    struct small_disc *apply_context_properties ;
	struct rule *context_rules;
    struct rule *simplified_rules;
    struct rule *blocked_rules;
	struct var_type *variables;
	struct _ex_intern *default_type;
    struct add_list *rewrite_chain;
    int slack;
	struct rule_operand_list **rule_operand_table;
	struct rule_double_operand_list **rule_double_operand_table;
	struct var_solve_list **var_solve_table;
	struct min_max_list **min_table;
	struct min_max_list **max_table;
    struct diff_node **diff_node_table;
    struct root_var **root_vars;
    struct term_group **term_groups;
    struct term_group **term_functors;
    struct cache_info *head;
} ;

#define TERM_HASH 1023

struct var_type {
	struct var_type *next;
	unsigned var;
	struct _ex_intern *type;
} ;

struct term_group_list {
    struct term_group_list *next;
    struct term_group *term;
} ;

struct root_var_list {
    struct root_var_list *next;
    struct root_var *var;
} ;

struct root_var_pair_list {
    struct root_var_pair_list *next;
    struct root_var *var1;
    struct root_var *var2;
} ;

struct root_var {
    struct root_var *next;
    struct root_var *parent;
    struct term_group_list *used_in_terms;
    struct term_group_list *equal_terms;
    struct root_var_list *ne_list;
    struct _ex_intern *var;
} ;

struct term_group {
    struct term_group *next;
    struct term_group *functor_next;
    struct _ex_intern *term;
    struct root_var *root_var;
} ;

struct cache_info {
    struct cache_info *next, *prev;
    struct _ex_intern *value, *old_value, *term;
    int line, old_line;
    struct _ex_intern *find, *old_find;
    struct _ex_intern *sig, *old_sig;
    struct _ex_intern *merge, *old_merge;
    struct _ex_intern *original, *old_original;
    struct add_list *explanation, *old_explanation;
    int in_hash;
    int bad;
} ;

struct env {
    int symbol_size ;
    int space;
    struct disc *all_properties ;
    struct disc *apply_properties ;
    struct disc *derive_properties ;
    struct disc *augment_properties ;
    struct disc *macro_properties ;
    struct root_var **root_vars;
    struct term_group **term_groups;
    struct term_group **term_functors;
    struct small_disc *context_properties ;
    struct small_disc *apply_context_properties ;
    struct context_stack *context_stack ;
    struct directive *pp_directives ;
    struct trie_l *pptrie ;
    int rebuild_trie ;
    struct rule *rules, *context_rules, *cr ;
    struct rule *simplified_rules;
    struct rule *blocked_rules;
    int context_level ;
    struct symbol_info *first_context_mark ;
    struct state_checks *state_checks ;
    struct add_list *heuristics ;
	struct _ex_intern *default_type;
	struct var_type *variables;
	struct min_max_list **min_table;
	struct min_max_list **max_table;
    struct diff_node **diff_node_table;
    struct cache_info *head, *tail;
	struct var_solve_list **var_solve_table;
	struct rule_operand_list **rule_operand_table;
	struct rule_double_operand_list **rule_double_operand_table;
    struct add_list *rewrite_chain;
    int slack;
    int vars_fully_connected;
    struct simplex *simplex;
#ifdef CHECK_CACHE
    int cache_installed;
#endif
    struct symbol_info *table[1] ;
} ;

int _th_get_space(struct env *env)
{
    return env->space;
}

//int in_learn = 0;

void _th_print_difference_table(struct env *env)
{
    struct diff_node *d;
    struct diff_edge *e;
    struct add_list *a;
    int i;

	if (env->diff_node_table==NULL) return;

    _tree_print0("Difference table");
    _tree_indent();
    for (i = 0; i < DIFF_NODE_HASH; ++i) {
        if (env->diff_node_table[i]) _tree_print1("Bin %d", i);
        _tree_indent();
        d = env->diff_node_table[i];
        while (d) {
            _tree_print_exp("Node", d->e);
            e = d->edges;
            _tree_indent();
            if (d->limit) _tree_print_exp("limit1", d->limit);
            if (d->bottom) _tree_print_exp("bottom", d->bottom);
            while (e) {
                _tree_print_exp("Edge to", e->target->e);
                _tree_indent();
                _tree_print_exp("Diff", e->offset);
                _tree_print1("Delta %d", e->delta);
                _tree_print0("Explanation");
                _tree_indent();
                a = e->explanation;
                while (a) {
                    _tree_print_exp("e", a->e);
                    a = a->next;
                }
                _tree_undent();
                _tree_undent();
                e = e->next;
            }
            _tree_undent();
            d = d->next;
        }
        _tree_undent();
    }
    _tree_undent();
}

void _th_display_difference_table(struct env *env)
{
    struct diff_node *d;
    struct diff_edge *e;
    struct add_list *a;
	struct ne_list *ne;
    int i;

	if (env->diff_node_table==NULL) return;

    printf("Difference table\n");
    for (i = 0; i < DIFF_NODE_HASH; ++i) {
        if (env->diff_node_table[i]) printf("Bin %d\n", i);
        d = env->diff_node_table[i];
        while (d) {
            printf("    Node %s\n", _th_print_exp(d->e));
			ne = d->ne_list;
			while (ne) {
				printf("        ne %s", _th_print_exp(ne->target->e));
				printf(" (offset %s)\n", _th_print_exp(ne->offset));
				ne = ne->next;
			}
            e = d->edges;
            if (d->limit) printf("        limit %s\n", _th_print_exp(d->limit));
			printf("        has_limit, limit_delta %d %d\n", d->has_limit, d->limit_delta);
			//printf("        Limit explanation\n");
			//a = d->limit_explanation;
			//while (a) {
			//	printf("                %s\n", _th_print_exp(a->e));
			//	a = a->next;
			//}
            if (d->bottom) printf("        bottom %s\n", _th_print_exp(d->bottom));
			printf("        has_bottom, bottom_delta %d %d\n", d->has_bottom, d->bottom_delta);
			//printf("        Bottom explanation\n");
			//a = d->bottom_explanation;
			//while (a) {
			//	printf("                %s\n", _th_print_exp(a->e));
			//	a = a->next;
			//}
            if (d->limit2) printf("        limit2 %s\n", _th_print_exp(d->limit2));
            if (d->bottom2) printf("        bottom2 %s\n", _th_print_exp(d->bottom2));
			printf("        visited = %d\n", d->visited);
			if (d->eq_merge) {
				printf("        merge = %s\n", _th_print_exp(d->eq_merge->e));
				printf("        merge offset = %s\n", _th_print_exp(d->eq_offset));
			    printf("        Merge explanation\n");
			    a = d->eq_explanation;
			    while (a) {
				    printf("                %s\n", _th_print_exp(a->e));
				    a = a->next;
				}
			}
            while (e) {
                printf("        Edge to %s\n", _th_print_exp(e->target->e));
                printf("            Diff %s\n", _th_print_exp(e->offset));
                printf("            Delta %d\n", e->delta);
                printf("            Explanation\n");
                a = e->explanation;
                while (a) {
                    printf("                %s\n", _th_print_exp(a->e));
                    a = a->next;
                }
                e = e->next;
            }
            d = d->next;
        }
    }
}

void _th_initialize_difference_table(struct env *env)
{
    int i;

    env->diff_node_table = (struct diff_node **)_th_alloc(env->space,sizeof(struct diff_node *) * DIFF_NODE_HASH);
    for (i = 0; i < DIFF_NODE_HASH; ++i) {
        env->diff_node_table[i] = NULL;
    }
}

void _th_initialize_simplex(struct env *env)
{
	env->simplex = _th_new_simplex(env);
}

void valid_env(struct env *env)
{
    if (env->diff_node_table && env->diff_node_table[13]==2) {
        fprintf(stderr, "Illegal environment\n");
        exit(1);
    }
    if (env->diff_node_table && _th_check_alloc_block(env->space, (char *)env->diff_node_table)) {
        fprintf(stderr, "Difference table not properly allocated\n");
        exit(1);
    }
}

int _th_delta;
int _th_is_equal_term = 0;
struct _ex_intern *_th_left;
struct _ex_intern *_th_right;
struct _ex_intern *_th_diff;

int is_basic_term(struct _ex_intern *e)
{
    if (e->type==EXP_VAR || e->type==EXP_INTEGER || e->type==EXP_RATIONAL) return 1;

    if (e->type==EXP_APPL && e->u.appl.functor != INTERN_NAT_PLUS &&
        e->u.appl.functor != INTERN_NAT_TIMES && e->u.appl.functor != INTERN_NAT_DIVIDE &&
        e->u.appl.functor != INTERN_NAT_MOD && e->u.appl.functor != INTERN_RAT_PLUS &&
        e->u.appl.functor != INTERN_RAT_TIMES && e->u.appl.functor != INTERN_RAT_DIVIDE &&
        e->u.appl.functor != INTERN_RAT_MOD && e->u.appl.functor != INTERN_ITE) return 1;

    return 0;
}

struct _ex_intern *tmo(struct env *env, struct _ex_intern *e)
{
    if (e->type != EXP_APPL) return NULL;
    if (e->u.appl.functor != INTERN_RAT_TIMES) return NULL;
    if (e->u.appl.count != 2) return NULL;
    if (e->u.appl.args[0]->type==EXP_RATIONAL) {
        if (e->u.appl.args[0]->u.rational.numerator[0]==1 && e->u.appl.args[0]->u.rational.numerator[1]==0xffffffff &&
            e->u.appl.args[0]->u.rational.denominator[0]==1 && e->u.appl.args[0]->u.rational.denominator[1]==1) return e->u.appl.args[1];
    }
    if (e->u.appl.args[1]->type==EXP_RATIONAL) {
        if (e->u.appl.args[1]->u.rational.numerator[0]==1 && e->u.appl.args[1]->u.rational.numerator[1]==0xffffffff &&
            e->u.appl.args[1]->u.rational.denominator[0]==1 && e->u.appl.args[1]->u.rational.denominator[1]==1) return e->u.appl.args[0];
    }
    return NULL;
}

static struct _ex_intern *remove_tmo(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *left[2];
    struct _ex_intern *right[2];
    int lc, rc;
    int i;
    struct _ex_intern *l, *r;
    static struct _ex_intern *zero = NULL;

    if (zero==NULL) zero = _ex_intern_small_rational(0,1);

    lc = 0;
    rc = 0;
    if (e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_RAT_PLUS) {
        for (i = 0; i < e->u.appl.args[0]->u.appl.count; ++i) {
            l = e->u.appl.args[0]->u.appl.args[i];
            r = tmo(env,l);
            if (r) {
                if (rc >= 2) return e;
                right[rc++] = r;
            } else {
                if (lc >= 2) return e;
                if (l != zero) left[lc++] = l;
            }
        }
    } else {
        l = e->u.appl.args[0];
        r = tmo(env,l);
        if (r) {
            if (rc >= 2) return e;
            right[rc++] = r;
        } else {
            if (lc >= 2) return e;
            if (l != zero) left[lc++] = l;
        }
    }
    if (e->u.appl.args[1]->type==EXP_APPL && e->u.appl.args[1]->u.appl.functor==INTERN_RAT_PLUS) {
        for (i = 0; i < e->u.appl.args[1]->u.appl.count; ++i) {
            r = e->u.appl.args[1]->u.appl.args[i];
            l = tmo(env,r);
            if (l) {
                if (lc >= 2) return e;
                left[lc++] = l;
            } else {
                if (rc >= 2) return e;
                if (r != zero) right[rc++] = r;
            }
        }
    } else {
        r = e->u.appl.args[1];
        l = tmo(env,r);
        if (l) {
            if (lc >= 2) return e;
            left[lc++] = l;
        } else {
            if (rc >= 2) return e;
            if (r != zero) right[rc++] = r;
        }
    }

    if (lc==0) {
        l = _ex_intern_small_rational(0,1);
    } else if (lc==1) {
        l = left[0];
    } else {
        l = _ex_intern_appl_env(env,INTERN_RAT_PLUS,lc,left);
    }
    if (rc==0) {
        r = _ex_intern_small_rational(0,1);
    } else if (rc==1) {
        r = right[0];
    } else {
        r = _ex_intern_appl_env(env,INTERN_RAT_PLUS,rc,right);
    }

    return _ex_intern_appl2_equal_env(env,e->u.appl.functor,l,r,_ex_real);
}

int _th_extract_relationship(struct env *env, struct _ex_intern *e)
{
    if (e->type != EXP_APPL) return 0;

    //printf("orig %s\n", _th_print_exp(e));

    if (e->u.appl.functor==INTERN_RAT_LESS) {
        e = remove_tmo(env,e);
        //_zone_print_exp("remove tmo", e);
        if (is_basic_term(e->u.appl.args[0]) && is_basic_term(e->u.appl.args[1])) {
            if (e->u.appl.args[0]->type==EXP_RATIONAL) {
                //printf("Case 1\n");
                _th_left = _ex_intern_small_rational(0,1);
                _th_right = e->u.appl.args[1];
                _th_diff = e->u.appl.args[0];
                _th_is_equal_term = 0;
                _th_delta = 1;
                return 1;
            } else if (e->u.appl.args[1]->type==EXP_RATIONAL) {
                //printf("Case 2\n");
                _th_right = _ex_intern_small_rational(0,1);
                _th_left = e->u.appl.args[0];
                _th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(e->u.appl.args[1]->u.rational.numerator)),
                                           e->u.appl.args[1]->u.rational.denominator);
                _th_delta = 1;
                _th_is_equal_term = 0;
                return 1;
            } else {
                //printf("Case 3\n");
                _th_left = e->u.appl.args[0];
                _th_right = e->u.appl.args[1];
                _th_diff = _ex_intern_small_rational(0,1);
                _th_delta = 1;
                _th_is_equal_term = 0;
                return 1;
            }
        } else if (is_basic_term(e->u.appl.args[0]) && e->u.appl.args[1]->type==EXP_APPL &&
                   e->u.appl.args[1]->u.appl.functor==INTERN_RAT_PLUS &&
                   e->u.appl.args[1]->u.appl.count==2 &&
                   is_basic_term(e->u.appl.args[1]->u.appl.args[0]) &&
                   is_basic_term(e->u.appl.args[1]->u.appl.args[1])) {
            if (e->u.appl.args[1]->u.appl.args[0]->type==EXP_RATIONAL) {
                //printf("Case 4 %s\n", _th_print_exp(e));
                _th_left = e->u.appl.args[0];
                _th_right = e->u.appl.args[1]->u.appl.args[1];
                _th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(e->u.appl.args[1]->u.appl.args[0]->u.rational.numerator)),
                                           e->u.appl.args[1]->u.appl.args[0]->u.rational.denominator);
                _th_delta = 1;
                _th_is_equal_term = 0;
                return 1;
            } else if (e->u.appl.args[1]->u.appl.args[1]->type==EXP_RATIONAL) {
                //printf("Case 5 %s\n", _th_print_exp(e));
                _th_left = e->u.appl.args[0];
                _th_right = e->u.appl.args[1]->u.appl.args[0];
                _th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(e->u.appl.args[1]->u.appl.args[1]->u.rational.numerator)),
                                           e->u.appl.args[1]->u.appl.args[1]->u.rational.denominator);
                _th_delta = 1;
                _th_is_equal_term = 0;
                return 1;
            } else {
                return 0;
            }
        } else if (is_basic_term(e->u.appl.args[1]) && e->u.appl.args[0]->type==EXP_APPL &&
                   e->u.appl.args[0]->u.appl.functor==INTERN_RAT_PLUS &&
                   e->u.appl.args[0]->u.appl.count==2 &&
                   is_basic_term(e->u.appl.args[0]->u.appl.args[0]) &&
                   is_basic_term(e->u.appl.args[0]->u.appl.args[1])) {
            if (e->u.appl.args[0]->u.appl.args[0]->type==EXP_RATIONAL) {
                //printf("Case 6 %s\n", _th_print_exp(e));
                _th_right = e->u.appl.args[1];
                _th_left = e->u.appl.args[0]->u.appl.args[1];
                _th_diff = e->u.appl.args[0]->u.appl.args[0];
                _th_delta = 1;
                _th_is_equal_term = 0;
                return 1;
            } else if (e->u.appl.args[0]->u.appl.args[1]->type==EXP_RATIONAL) {
                //printf("Case 7\n");
                _th_right = e->u.appl.args[1];
                _th_left = e->u.appl.args[0]->u.appl.args[0];
                _th_diff = e->u.appl.args[0]->u.appl.args[1];
                _th_delta = 1;
                _th_is_equal_term = 0;
                return 1;
            } else {
                return 0;
            }
        }
    } else if (e->u.appl.functor==INTERN_EQUAL) {
        e = remove_tmo(env,e);
        if (is_basic_term(e->u.appl.args[0]) && is_basic_term(e->u.appl.args[1])) {
            if (e->u.appl.args[0]->type==EXP_RATIONAL) {
                //printf("Case 1e\n");
                _th_left = _ex_intern_small_rational(0,1);
                _th_right = e->u.appl.args[1];
                _th_diff = e->u.appl.args[0];
                _th_is_equal_term = 1;
                _th_delta = 1;
                return 1;
            } else if (e->u.appl.args[1]->type==EXP_RATIONAL) {
                //printf("Case 2e\n");
                _th_right = _ex_intern_small_rational(0,1);
                _th_left = e->u.appl.args[0];
                _th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(e->u.appl.args[1]->u.rational.numerator)),
                                           e->u.appl.args[1]->u.rational.denominator);
                _th_is_equal_term = 1;
                _th_delta = 1;
                return 1;
            } else {
                //printf("Case 3e\n");
                _th_left = e->u.appl.args[0];
                _th_right = e->u.appl.args[1];
                _th_diff = _ex_intern_small_rational(0,1);
                _th_is_equal_term = 1;
                _th_delta = 1;
                return 1;
            }
        } else if (is_basic_term(e->u.appl.args[0]) && e->u.appl.args[1]->type==EXP_APPL &&
                   e->u.appl.args[1]->u.appl.functor==INTERN_RAT_PLUS &&
                   e->u.appl.args[1]->u.appl.count==2 &&
                   is_basic_term(e->u.appl.args[1]->u.appl.args[0]) &&
                   is_basic_term(e->u.appl.args[1]->u.appl.args[1])) {
            if (e->u.appl.args[1]->u.appl.args[0]->type==EXP_RATIONAL) {
                //printf("Case 4e %s\n", _th_print_exp(e));
                _th_left = e->u.appl.args[0];
                _th_right = e->u.appl.args[1]->u.appl.args[1];
                _th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(e->u.appl.args[1]->u.appl.args[0]->u.rational.numerator)),
                                           e->u.appl.args[1]->u.appl.args[0]->u.rational.denominator);
                _th_is_equal_term = 1;
                _th_delta = 1;
                return 1;
            } else if (e->u.appl.args[1]->u.appl.args[1]->type==EXP_RATIONAL) {
                //printf("Case 5e\n");
                _th_left = e->u.appl.args[0];
                _th_right = e->u.appl.args[1]->u.appl.args[0];
                _th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(e->u.appl.args[1]->u.appl.args[1]->u.rational.numerator)),
                                           e->u.appl.args[1]->u.appl.args[1]->u.rational.denominator);
                _th_is_equal_term = 1;
                _th_delta = 1;
                return 1;
            } else {
                return 0;
            }
        } else if (is_basic_term(e->u.appl.args[1]) && e->u.appl.args[0]->type==EXP_APPL &&
                   e->u.appl.args[0]->u.appl.functor==INTERN_RAT_PLUS &&
                   e->u.appl.args[0]->u.appl.count==2 &&
                   is_basic_term(e->u.appl.args[0]->u.appl.args[0]) &&
                   is_basic_term(e->u.appl.args[0]->u.appl.args[1])) {
            if (e->u.appl.args[0]->u.appl.args[0]->type==EXP_RATIONAL) {
                //printf("Case 6e\n");
                _th_right = e->u.appl.args[1];
                _th_left = e->u.appl.args[0]->u.appl.args[1];
                _th_diff = e->u.appl.args[0]->u.appl.args[0];
                _th_is_equal_term = 1;
                _th_delta = 1;
                return 1;
            } else if (e->u.appl.args[0]->u.appl.args[1]->type==EXP_RATIONAL) {
                //printf("Case 7e\n");
                _th_right = e->u.appl.args[1];
                _th_left = e->u.appl.args[0]->u.appl.args[0];
                _th_diff = e->u.appl.args[0]->u.appl.args[1];
                _th_is_equal_term = 1;
                _th_delta = 1;
                return 1;
            } else {
                return 0;
            }
        }
    } else if (e->u.appl.functor==INTERN_NOT) {
        e = e->u.appl.args[0];
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_RAT_LESS) {
            e = remove_tmo(env,e);
            if (is_basic_term(e->u.appl.args[0]) && is_basic_term(e->u.appl.args[1])) {
                if (e->u.appl.args[0]->type==EXP_RATIONAL) {
                    //printf("Case 8\n");
                    _th_right = _ex_intern_small_rational(0,1);
                    _th_left = e->u.appl.args[1];
                    _th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(e->u.appl.args[0]->u.rational.numerator)),
                        e->u.appl.args[0]->u.rational.denominator);
                    _th_delta = 0;
                    _th_is_equal_term = 0;
                    return 1;
                } else if (e->u.appl.args[1]->type==EXP_RATIONAL) {
                    //printf("Case 9\n");
                    _th_left = _ex_intern_small_rational(0,1);
                    _th_right = e->u.appl.args[0];
                    _th_diff = e->u.appl.args[1];
                    _th_delta = 0;
                    _th_is_equal_term = 0;
                    return 1;
                } else {
                    //printf("Case 10 %s\n", _th_print_exp(e));
                    _th_left = e->u.appl.args[1];
                    _th_right = e->u.appl.args[0];
                    _th_diff = _ex_intern_small_rational(0,1);
                    _th_delta = 0;
                    _th_is_equal_term = 0;
                    return 1;
                }
            } else if (is_basic_term(e->u.appl.args[0]) && e->u.appl.args[1]->type==EXP_APPL &&
                e->u.appl.args[1]->u.appl.functor==INTERN_RAT_PLUS &&
                e->u.appl.args[1]->u.appl.count==2 &&
                is_basic_term(e->u.appl.args[1]->u.appl.args[0]) &&
                is_basic_term(e->u.appl.args[1]->u.appl.args[1])) {
                if (e->u.appl.args[1]->u.appl.args[0]->type==EXP_RATIONAL) {
                    //printf("Case 11 %s\n", _th_print_exp(e));
                    _th_right = e->u.appl.args[0];
                    _th_left = e->u.appl.args[1]->u.appl.args[1];
                    _th_diff = e->u.appl.args[1]->u.appl.args[0];
                    _th_delta = 0;
                    _th_is_equal_term = 0;
                    return 1;
                } else if (e->u.appl.args[1]->u.appl.args[1]->type==EXP_RATIONAL) {
                    //printf("Case 12\n");
                    _th_right = e->u.appl.args[0];
                    _th_left = e->u.appl.args[1]->u.appl.args[0];
                    _th_diff = e->u.appl.args[1]->u.appl.args[1];
                    _th_delta = 0;
                    _th_is_equal_term = 0;
                    return 1;
                } else {
                    return 0;
                }
            } else if (is_basic_term(e->u.appl.args[1]) && e->u.appl.args[0]->type==EXP_APPL &&
                e->u.appl.args[0]->u.appl.functor==INTERN_RAT_PLUS &&
                e->u.appl.args[0]->u.appl.count==2 &&
                is_basic_term(e->u.appl.args[0]->u.appl.args[0]) &&
                is_basic_term(e->u.appl.args[0]->u.appl.args[1])) {
                if (e->u.appl.args[0]->u.appl.args[0]->type==EXP_RATIONAL) {
                    //printf("Case 13 %s\n", _th_print_exp(e));
                    _th_left = e->u.appl.args[1];
                    _th_right = e->u.appl.args[0]->u.appl.args[1];
                    _th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(e->u.appl.args[0]->u.appl.args[0]->u.rational.numerator)),
                        e->u.appl.args[0]->u.appl.args[0]->u.rational.denominator);
                    _th_delta = 0;
                    _th_is_equal_term = 0;
                    return 1;
                } else if (e->u.appl.args[0]->u.appl.args[1]->type==EXP_RATIONAL) {
                    //printf("Case 14\n");
                    _th_left = e->u.appl.args[1];
                    _th_right = e->u.appl.args[0]->u.appl.args[0];
                    _th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(e->u.appl.args[0]->u.appl.args[1]->u.rational.numerator)),
                        e->u.appl.args[0]->u.appl.args[1]->u.rational.denominator);
                    _th_delta = 0;
                    _th_is_equal_term = 0;
                    return 1;
                } else {
                    return 0;
                }
            }
        } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL) {
            e = remove_tmo(env,e);
            if (is_basic_term(e->u.appl.args[0]) && is_basic_term(e->u.appl.args[1])) {
                if (e->u.appl.args[0]->type==EXP_RATIONAL) {
                    //printf("Case 8\n");
                    _th_right = _ex_intern_small_rational(0,1);
                    _th_left = e->u.appl.args[1];
                    _th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(e->u.appl.args[0]->u.rational.numerator)),
                        e->u.appl.args[0]->u.rational.denominator);
                    _th_is_equal_term = -1;
                    _th_delta = 0;
                    return 1;
                } else if (e->u.appl.args[1]->type==EXP_RATIONAL) {
                    //printf("Case 9\n");
                    _th_left = _ex_intern_small_rational(0,1);
                    _th_right = e->u.appl.args[0];
                    _th_diff = e->u.appl.args[1];
                    _th_is_equal_term = -1;
                    _th_delta = 0;
                    return 1;
                } else {
                    //printf("Case 10 %s\n", _th_print_exp(e));
                    _th_left = e->u.appl.args[1];
                    _th_right = e->u.appl.args[0];
                    _th_diff = _ex_intern_small_rational(0,1);
                    _th_is_equal_term = -1;
                    _th_delta = 0;
                    return 1;
                }
            } else if (is_basic_term(e->u.appl.args[0]) && e->u.appl.args[1]->type==EXP_APPL &&
                e->u.appl.args[1]->u.appl.functor==INTERN_RAT_PLUS &&
                e->u.appl.args[1]->u.appl.count==2 &&
                is_basic_term(e->u.appl.args[1]->u.appl.args[0]) &&
                is_basic_term(e->u.appl.args[1]->u.appl.args[1])) {
                if (e->u.appl.args[1]->u.appl.args[0]->type==EXP_RATIONAL) {
                    //printf("Case 11 %s\n", _th_print_exp(e));
                    _th_right = e->u.appl.args[0];
                    _th_left = e->u.appl.args[1]->u.appl.args[1];
                    _th_diff = e->u.appl.args[1]->u.appl.args[0];
                    _th_is_equal_term = -1;
                    _th_delta = 0;
                    return 1;
                } else if (e->u.appl.args[1]->u.appl.args[1]->type==EXP_RATIONAL) {
                    //printf("Case 12\n");
                    _th_right = e->u.appl.args[0];
                    _th_left = e->u.appl.args[1]->u.appl.args[0];
                    _th_diff = e->u.appl.args[1]->u.appl.args[1];
                    _th_is_equal_term = -1;
                    _th_delta = 0;
                    return 1;
                } else {
                    return 0;
                }
            } else if (is_basic_term(e->u.appl.args[1]) && e->u.appl.args[0]->type==EXP_APPL &&
                e->u.appl.args[0]->u.appl.functor==INTERN_RAT_PLUS &&
                e->u.appl.args[0]->u.appl.count==2 &&
                is_basic_term(e->u.appl.args[0]->u.appl.args[0]) &&
                is_basic_term(e->u.appl.args[0]->u.appl.args[1])) {
                if (e->u.appl.args[0]->u.appl.args[0]->type==EXP_RATIONAL) {
                    //printf("Case 13 %s\n", _th_print_exp(e));
                    _th_left = e->u.appl.args[1];
                    _th_right = e->u.appl.args[0]->u.appl.args[1];
                    _th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(e->u.appl.args[0]->u.appl.args[0]->u.rational.numerator)),
                        e->u.appl.args[0]->u.appl.args[0]->u.rational.denominator);
                    _th_is_equal_term = -1;
                    _th_delta = 0;
                    return 1;
                } else if (e->u.appl.args[0]->u.appl.args[1]->type==EXP_RATIONAL) {
                    //printf("Case 14\n");
                    _th_left = e->u.appl.args[1];
                    _th_right = e->u.appl.args[0]->u.appl.args[0];
                    _th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(e->u.appl.args[0]->u.appl.args[1]->u.rational.numerator)),
                        e->u.appl.args[0]->u.appl.args[1]->u.rational.denominator);
                    _th_is_equal_term = -1;
                    _th_delta = 0;
                    return 1;
                } else {
                    return 0;
                }
            }
        }
    }

    return 0;
}

static int has_rat_operator(struct _ex_intern *e)
{
    int i;

    if (e->type==EXP_RATIONAL) return 1;

    if (e->type != EXP_APPL) return 0;

    if (e->u.appl.functor==INTERN_RAT_PLUS || e->u.appl.functor==INTERN_RAT_MINUS ||
        e->u.appl.functor==INTERN_RAT_TIMES || e->u.appl.functor==INTERN_RAT_DIVIDE ||
        e->u.appl.functor==INTERN_RAT_MOD || e->u.appl.functor==INTERN_RAT_LESS) return 1;

    for (i = 0; i < e->u.appl.count; ++i) {
        if (has_rat_operator(e->u.appl.args[i])) return 1;
    }

    return 0;
}

int _th_incomplete_decision_procedure(struct env *env, struct _ex_intern *e)
{
    if (has_rat_operator(e) && !_th_extract_relationship(env,e)) return 1;

    return 0;
}

int _th_is_difference_term(struct env *env, struct _ex_intern *e)
{
    if (has_rat_operator(e)) return _th_extract_relationship(env,e);
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL &&
        e->u.appl.args[0]->type==EXP_VAR && e->u.appl.args[1]->type==EXP_VAR) return 1;
    return 0;
}

//static int space = 4;

static int is_equal = 0;
static struct add_list *is_equal_expl;

static struct _ex_intern *sub_rationals(struct _ex_intern *r1, struct _ex_intern *r2)
{
    unsigned *tmp1, *tmp2, *accumulate;

    if (r1->u.rational.denominator[0]==1 && r1->u.rational.denominator[1]==1 &&
        r2->u.rational.denominator[0]==1 && r2->u.rational.denominator[1]==1) {
        return _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_big_sub(r1->u.rational.numerator,r2->u.rational.numerator)),r1->u.rational.denominator);
    } else {
		//printf("Enter sub_rationals\n");
        tmp1 = r1->u.rational.numerator;
        tmp2 = r1->u.rational.denominator;
        accumulate = _th_big_gcd(r1->u.rational.denominator,r2->u.rational.denominator);
        tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_divide(_th_big_multiply(r1->u.rational.numerator,r2->u.rational.denominator),accumulate));
        tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_sub(tmp1,_th_big_copy(REWRITE_SPACE,_th_big_divide(_th_big_multiply(r2->u.rational.numerator,r1->u.rational.denominator),accumulate))));
        tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_divide(_th_big_multiply(r1->u.rational.denominator,r2->u.rational.denominator),accumulate));

		//printf("Exit sub_rationals\n");

        return _ex_intern_rational(tmp1,tmp2);
    }
}

static struct _ex_intern *add_rationals(struct _ex_intern *r1, struct _ex_intern *r2)
{
    unsigned *tmp1, *tmp2, *accumulate;

    if (r1->u.rational.denominator[0]==1 && r1->u.rational.denominator[1]==1 &&
        r2->u.rational.denominator[0]==1 && r2->u.rational.denominator[1]==1) {
        return _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_big_add(r1->u.rational.numerator,r2->u.rational.numerator)),r1->u.rational.denominator);
    } else {
		//printf("Enter add_rationals\n");
        tmp1 = r1->u.rational.numerator;
        tmp2 = r1->u.rational.denominator;
        accumulate = _th_big_gcd(r1->u.rational.denominator,r2->u.rational.denominator);
        tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_divide(_th_big_multiply(r1->u.rational.numerator,r2->u.rational.denominator),accumulate));
        tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_add(tmp1,_th_big_copy(REWRITE_SPACE,_th_big_divide(_th_big_multiply(r2->u.rational.numerator,r1->u.rational.denominator),accumulate))));
        tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_divide(_th_big_multiply(r1->u.rational.denominator,r2->u.rational.denominator),accumulate));
        //printf("exit add_rationals\n");

        return _ex_intern_rational(tmp1,tmp2);
    }
}

static int rational_less(struct _ex_intern *r1, struct _ex_intern *r2)
{
    unsigned *tmp1, *tmp2;

    if (r1->u.rational.denominator[0]==1 && r1->u.rational.denominator[1]==1 &&
        r2->u.rational.denominator[0]==1 && r2->u.rational.denominator[1]==1) {
        return _th_big_less(r1->u.rational.numerator,r2->u.rational.numerator);
    } else {
        tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(r1->u.rational.numerator,r2->u.rational.denominator));
        tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(r2->u.rational.numerator,r1->u.rational.denominator));
        return _th_big_less(tmp1,tmp2);
    }
}

int has_equal;
static int space = 4;

#ifdef XX
static int fpc(struct env *env, struct diff_node *target, struct diff_node *node, int acc, int _th_delta)
{
    struct diff_edge *e;
    int min;

    //if (node==target && node->visited) {
    //    unsigned *n = acc->u.rational.numerator;
    //    if (_th_delta && n[0]==1 && n[1]==0) return 1;
    //    if (n[0]==1 && n[1]==0) has_equal = 1;
    //   if ((n[n[0]] & 0x80000000)==0 && (n[0]!=1|| n[1]!=0)) return 1;
    //}

    if (node->visited) {
        //printf("%*sAlready visited %s %d\n", space, "", _th_print_exp(node->e), node->limit);
        return 0;
    }

    e = node->edges;

    //printf("%*sChecking node %s\n", space, "", _th_print_exp(node->e));

    min = 500000;
    node->visited = 1;
    while (e) {
        int d1 = (_th_delta || e->_th_delta);
        int sum = acc + ((int)e->offset->u.rational.numerator[1]);
        if (!e->target->visited) {
            if (!e->target->has_limit) {
                //space += 2;
                //printf("%*soffset = %d\n", space, "", e->offset->u.rational.numerator[1]);
                if (fpc(env,target,e->target,sum,d1)) {
                    //space -= 2;
                    return 1;
                }
                //space -=2;
            } else {
                //printf("%*starget = %s limit = %d\n", space+2, "", _th_print_exp(e->target->e), e->target->limit);
            }
            sum = ((int)e->target->limit) - ((int)e->offset->u.rational.numerator[1]);
            if (sum < min) {
                min = sum;
                node->limit_delta = (e->target->limit_delta || e->_th_delta);
            }
            if (sum==min) {
                node->limit_delta = (node->limit_delta || e->target->limit_delta || e->_th_delta);
            }
        }
        e = e->next;
    }
    ((int)node->limit) = min;
    //printf("%*sacc = %d\n", space, "", acc);
    //printf("%*slimit = %d\n", space, "", node->limit);
    if (min < acc ||
        ((node->limit_delta || _th_delta) && min==acc)) {
        return 1;
    }
    if (min==acc && !node->limit_delta && !_th_delta) {
        has_equal = 1;
    }
    node->has_limit = 1;
    node->visited = 0;

    return 0;
}
#endif

static int qbf(struct env *env, struct diff_node *start)
{
    struct diff_node *n;
    struct diff_edge *e;
    int i, j, count, sum;

    count = 0;
    for (i = 0; i < DIFF_NODE_HASH; ++i) {
        n = env->diff_node_table[i];
        while (n) {
            ++count;
            n->bottom = 0;
            n = n->next;
        }
    }

    start->bottom = _ex_true;
    start->limit = 0;

    for (i = 0; i < count-1; ++i) {
        //fprintf(log, "CYCLE\n");
        for (j = 0; j < DIFF_NODE_HASH; ++j) {
            n = env->diff_node_table[j];
            while (n) {
                if (n->bottom) {
                    //fprintf(log, "    Processing vertex %s\n", _th_print_exp(n->e));
                    e = n->edges;
                    while (e) {
                        sum = ((int)n->limit)-e->offset->u.rational.numerator[1];
                        if (!e->target->bottom) {
                            e->target->bottom = _ex_true;
                            e->target->limit = sum;
                            //fprintf(log, "    Vertex %s gets1 %d from", _th_print_exp(e->target->e), sum);
                            //fprintf(log, " %s ", _th_print_exp(n->e));
                            //fprintf(log, "(%s)\n", _th_print_exp(e->offset));
                        } else if (sum < ((int)e->target->limit)) {
                            e->target->limit = sum;
                            //fprintf(log, "    Vertex %s gets2 %d from", _th_print_exp(e->target->e), sum);
                            //fprintf(log, " %s ", _th_print_exp(n->e));
                            //fprintf(log, "(%s)\n", _th_print_exp(e->offset));
                        }
                        e = e->next;
                    }
                }
                n = n->next;
            }
        }
    }

    for (j = 0; j < DIFF_NODE_HASH; ++j) {
        n = env->diff_node_table[j];
        while (n) {
            if (n->bottom) {
                e = n->edges;
                while (e) {
                    sum = ((int)n->limit)-e->offset->u.rational.numerator[1];
                    if (!e->target->bottom) {
                        return 1;
                    } else if (sum < ((int)e->target->limit)) {
                        return 1;
                    }
                    e = e->next;
                }
            }
            n = n->next;
        }
    }

    return 0;
}

int has_positive_cycle(struct env *env)
{
    struct diff_node *n;
#ifdef XX
    struct diff_edge *e;
    FILE *log;
#endif
    int i;
    struct _ex_intern *zero = _ex_intern_small_rational(0,1);
    char *mark;

#ifdef XX
    //if (_tree_zone > 19293) exit(1);
    log = fopen("cycle_log","w");
    fprintf(log, "CHECK CYCLE %d\n", _tree_zone);
    for (i = 0; i < DIFF_NODE_HASH; ++i) {
        n = env->diff_node_table[i];
        while (n) {
            fprintf(log, "node %s\n", _th_print_exp(n->e));
            e = n->edges;
            while (e) {
                fprintf(log, "    edge to %s", _th_print_exp(e->target->e));
                fprintf(log, " (%s)\n", _th_print_exp(e->offset));
                e = e->next;
            }
            n = n->next;
        }
    }
#endif

    for (i = 0; i < DIFF_NODE_HASH; ++i) {
        n = env->diff_node_table[i];
        while (n) {
            n->visited = 0;
            n = n->next;
        }
    }

    for (i = 0; i < DIFF_NODE_HASH; ++i) {
        n = env->diff_node_table[i];
        while (n) {
            //for (j = 0; j < DIFF_NODE_HASH; ++j) {
            //    nn = env->diff_node_table[j];
            //    while (nn) {
            //        nn->has_limit = 0;
            //        nn = nn->next;
            //    }
            //}
            mark = _th_alloc_mark(REWRITE_SPACE);
            has_equal = 0;
            //n->has_limit = 1;
            //n->limit_delta = 0;
            //n->limit = 0;
            //printf("Target %s\n", _th_print_exp(n->e));
            //fprintf(log, "Processing %s\n", _th_print_exp(n->e));
            if (qbf(env,n)) return 1;
            if (has_equal) {
                fprintf(stderr, "Have equal cycle\n");
                return 1;
            }
            n = n->next;
            _th_alloc_release(REWRITE_SPACE,mark);
        }
    }
    //fclose(log);

    return 0;
}

#ifdef PRINT1
int print_cc = 0;
static int ind;
#endif

struct add_list *cc(struct env *env, struct diff_node *target, struct diff_node *node, struct _ex_intern *acc, int delta, struct add_list *explanation)
{
    struct diff_edge *edge;
	unsigned one[2] = { 1, 1 };
	unsigned zero[2] = { 1, 0 };
	unsigned *tmp1;
    struct add_list *expl, *n, *a, *res, *r;
    struct _ex_intern *sum;
    int traverse_children = 0;

#ifdef PRINT1
	if (print_cc) {
        printf("%*snode %s", ind, "", _th_print_exp(node->e));
        printf(" %s %d %x %d", _th_print_exp(acc), delta, node, node->has_bottom);
		printf(" %s %d\n", _th_print_exp(node->bottom), node->bottom_delta);
	}
    ind += 2;
#endif

    _zone_print_exp("cc", node->e);
    _tree_indent();
    _zone_print_exp("acc", acc);
    _zone_print1("delta %d", delta);

	if (node->has_bottom) {
		if (_th_rational_less(node->bottom,acc)) {
			node->bottom = acc;
			node->bottom_delta = delta;
    		node->bottom_explanation = explanation;
			traverse_children = 1;
		} else if (node->bottom==acc && delta && !node->bottom_delta) {
			node->bottom = acc;
			node->bottom_delta = delta;
    		node->bottom_explanation = explanation;
			traverse_children = 1;
		}
	} else {
		node->bottom = acc;
		node->bottom_delta = delta;
        node->has_bottom = 1;
		node->bottom_explanation = explanation;
		traverse_children = 1;
	}

    if (node==target) {
        _zone_print0("At target");
        tmp1 = acc->u.rational.numerator;
        //printf("*** CYCLE ***\n");
        if (!delta && tmp1[0]==1 && tmp1[1]==0) {
            is_equal = 1;
            res = NULL;
            while (explanation) {
                r = (struct add_list *)_th_alloc(env->space,sizeof(struct add_list));
                r->next = res;
                r->e = explanation->e;
                res = r;
                explanation = explanation->next;
            }
            is_equal_expl = res;
        } else if ((tmp1[0]==1 && tmp1[1]==0) ||
                   (tmp1[tmp1[0]] & 0x80000000)==0) {
            res = NULL;
            while (explanation) {
                r = (struct add_list *)_th_alloc(env->space,sizeof(struct add_list));
                r->next = res;
                r->e = explanation->e;
                res = r;
                explanation = explanation->next;
            }
            _zone_print0("Found contradiction 1");
            _tree_undent();
#ifdef PRINT1
			ind-=2;
#endif
			return res;
        }
    }

	if (traverse_children) {
		node->visited = 1;
        edge = node->edges;
		while (edge) {
			sum = _th_add_rationals(acc,edge->offset);
			//printf("Checking node %s\n", _th_print_exp(edge->target->e));
			if (edge->target->visited) {
				//printf("Here1\n");
				if (_th_rational_less(edge->target->bottom,sum) ||
					(edge->target->bottom==sum && !edge->target->bottom_delta && (delta || edge->delta))) {
						struct add_list *r, *res;
						//printf("Here2\n");
						res = NULL;
						while (explanation) {
							r = (struct add_list *)_th_alloc(env->space,sizeof(struct add_list));
							r->next = res;
							r->e = explanation->e;
							res = r;
							explanation = explanation->next;
						}
						explanation = edge->explanation;
						while (explanation) {
							r = (struct add_list *)_th_alloc(env->space,sizeof(struct add_list));
							r->next = res;
							r->e = explanation->e;
							res = r;
							explanation = explanation->next;
						}
						_zone_print0("Found contradiction 2");
						_tree_undent();
#ifdef PRINT1
						ind-=2;
#endif
						return res;
				}
			} else {
				//printf("Here3\n");
				if (!edge->target->has_bottom ||
					_th_rational_less(edge->target->bottom,sum) ||
					(edge->target->bottom==sum && !edge->target->bottom_delta && (delta || edge->delta))) {
	                //printf("Here4\n");
					expl = explanation;
		            a = edge->explanation;
			        while (a) {
				        n = (struct add_list *)ALLOCA(sizeof(struct add_list));
					    n->next = expl;
						expl = n;
						expl->e = a->e;
						a = a->next;
					}
					if (res = cc(env,target,edge->target,sum,(delta||edge->delta),expl)) {
						_tree_undent();
#ifdef PRINT1
						ind-=2;
#endif
						return res;
					}
				}
			}
			edge = edge->next;
		}
	    node->visited = 0;
	}

    _tree_undent();
#ifdef PRINT1
	ind-=2;
#endif
	return NULL;
}

static void fill_limits(struct env *env, struct diff_node *node)
{
    struct diff_edge *edge;
    struct add_list *target_ex, *a, *n;
    struct _ex_intern *sum;

	//printf("Fill limits %s", _th_print_exp(node->e));
    //printf(" (%s)\n", _th_print_exp(node->limit));

    _zone_print_exp("fill_limits", node->e);
    //_tree_print_exp("limit2", node->limit);
    _tree_indent();

    node->visited = 1;
    target_ex = NULL;
    edge = node->edges;
    while (edge) {
        if (!edge->target->visited) {
            _zone_print_exp("Edge", edge->target->e);
            _tree_indent();
            _zone_print_exp("Offset", edge->offset);
            sum = _th_add_rationals(node->limit,edge->offset);
            _zone_print_exp("sum", sum);
            if (edge->target->limit==NULL ||
                rational_less(edge->target->limit,sum)) {
                edge->target->limit = sum;
                edge->target->limit_delta = (node->limit_delta || edge->delta);
                a = edge->explanation;
                target_ex = node->limit_explanation;
                while (a) {
                    n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                    n->next = target_ex;
                    n->e = a->e;
                    target_ex = n;
                    a = a->next;
                }
                edge->target->limit_explanation = target_ex;
                _zone_print0("Here1");
				//printf("Edge %s", _th_print_exp(edge->source->e));
				//printf(" to %s", _th_print_exp(edge->target->e));
				//printf(" offset %s\n", _th_print_exp(edge->offset));
                fill_limits(env,edge->target);
            } else if (edge->target->limit==sum && !edge->target->limit_delta &&
                       (node->limit_delta || edge->delta)) {
                edge->target->limit_delta = 1;
                _zone_print0("Here2");
				//printf("Edge %s", _th_print_exp(edge->source->e));
				//printf(" to %s", _th_print_exp(edge->target->e));
				//printf(" offset %s\n", _th_print_exp(edge->offset));
                fill_limits(env,edge->target);
                target_ex = node->limit_explanation;
                a = edge->explanation;
                while (a) {
                    n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                    n->next = target_ex;
                    n->e = a->e;
                    target_ex = n;
                    a = a->next;
                }
                edge->target->limit_explanation = target_ex;
            }
            _tree_undent();                
        }
        edge = edge->next;
    }

    node->visited = 0;

    _tree_undent();
}

static void fill_limits2(struct env *env, struct diff_node *node)
{
    struct diff_edge *edge;
    struct add_list *target_ex, *a, *n;
    struct _ex_intern *sum;

    _zone_print_exp("fill_limits2", node->e);
    //_tree_print_exp("limit2", node->limit2);
    _tree_indent();

	//printf("Fill limits2 %s", _th_print_exp(node->e));
    //printf(" (%s)\n", _th_print_exp(node->limit2));

	node->visited = 1;
    target_ex = NULL;
    edge = node->edges;
    while (edge) {
        if (!edge->target->visited) {
            _zone_print_exp("Edge", edge->target->e);
            _tree_indent();
            _zone_print_exp("Offset", edge->offset);
            sum = _th_add_rationals(node->limit2,edge->offset);
            _zone_print_exp("sum", sum);
            if (edge->target->limit2==NULL ||
                rational_less(edge->target->limit2,sum)) {
                edge->target->limit2 = sum;
                edge->target->limit_delta2 = (node->limit_delta2 || edge->delta);
                a = edge->explanation;
                target_ex = node->limit_explanation2;
                while (a) {
                    n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                    n->next = target_ex;
                    n->e = a->e;
                    target_ex = n;
                    a = a->next;
                }
                edge->target->limit_explanation2 = target_ex;
                _zone_print0("Here1");
				//printf("Edge %s", _th_print_exp(edge->source->e));
				//printf(" to %s", _th_print_exp(edge->target->e));
				//printf(" offset %s\n", _th_print_exp(edge->offset));
                fill_limits2(env,edge->target);
            } else if (edge->target->limit2==sum && !edge->target->limit_delta2 &&
                       (node->limit_delta2 || edge->delta)) {
                edge->target->limit_delta2 = 1;
                _zone_print0("Here2");
				//printf("Edge %s", _th_print_exp(edge->source->e));
				//printf(" to %s", _th_print_exp(edge->target->e));
				//printf(" offset %s\n", _th_print_exp(edge->offset));
                fill_limits2(env,edge->target);
                target_ex = node->limit_explanation2;
                a = edge->explanation;
                while (a) {
                    n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                    n->next = target_ex;
                    n->e = a->e;
                    target_ex = n;
                    a = a->next;
                }
                edge->target->limit_explanation2 = target_ex;
            }
            _tree_undent();                
        }
        edge = edge->next;
    }

    node->visited = 0;

    _tree_undent();
}

static void fill_bottoms(struct env *env, struct diff_node *node)
{
    struct diff_edge *edge;
    struct add_list *target_ex, *a, *n;
    struct _ex_intern *sum;

	//printf("Fill bottoms %s", _th_print_exp(node->e));
    //printf(" (%s)\n", _th_print_exp(node->bottom));

	_zone_print_exp("fill_bottoms", node->e);
    _tree_indent();

    node->visited = 1;
    target_ex = NULL;
    edge = node->source_edges;
    while (edge) {
        if (!edge->source->visited) {
            _zone_print_exp("Edge", edge->source->e);
            _tree_indent();
            _zone_print_exp("Offset", edge->offset);
            sum = add_rationals(node->bottom,edge->offset);
            if (edge->source->bottom==NULL ||
                rational_less(edge->source->bottom,sum)) {
                edge->source->bottom = sum;
                edge->source->bottom_delta = (node->bottom_delta || edge->delta);
                a = edge->explanation;
                target_ex = node->bottom_explanation;
                while (a) {
                    n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                    n->next = target_ex;
                    n->e = a->e;
                    target_ex = n;
                    a = a->next;
                }
                edge->source->bottom_explanation = target_ex;
				//printf("Edge %s", _th_print_exp(edge->source->e));
				//printf(" to %s", _th_print_exp(edge->target->e));
				//printf(" offset %s\n", _th_print_exp(edge->offset));
                fill_bottoms(env,edge->source);
            } else if (edge->source->bottom==sum && !edge->source->bottom_delta &&
                       (node->bottom_delta || edge->delta)) {
                edge->source->bottom_delta = 1;
				//printf("Edge %s", _th_print_exp(edge->source->e));
				//printf(" to %s", _th_print_exp(edge->target->e));
				//printf(" offset %s\n", _th_print_exp(edge->offset));
                fill_bottoms(env,edge->source);
                a = edge->explanation;
                target_ex = node->bottom_explanation;
                while (a) {
                    n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                    n->next = target_ex;
                    n->e = a->e;
                    target_ex = n;
                    a = a->next;
                }
                edge->source->bottom_explanation = target_ex;
            }
            _tree_undent();                
        }
        edge = edge->source_next;
    }

    node->visited = 0;

    _tree_undent();
}

static void fill_bottoms2(struct env *env, struct diff_node *node)
{
    struct diff_edge *edge;
    struct add_list *target_ex, *a, *n;
    struct _ex_intern *sum;

    _zone_print_exp("fill_bottoms2", node->e);
    _tree_indent();

	//printf("Fill bottoms2 %s", _th_print_exp(node->e));
    //printf(" (%s)\n", _th_print_exp(node->bottom2));
    node->visited = 1;
    target_ex = NULL;
    edge = node->source_edges;
    while (edge) {
        if (!edge->source->visited) {
            _zone_print_exp("Edge", edge->source->e);
            _tree_indent();
            _zone_print_exp("Offset", edge->offset);
            sum = add_rationals(node->bottom2,edge->offset);
            if (edge->source->bottom2==NULL ||
                rational_less(edge->source->bottom2,sum)) {
                edge->source->bottom2 = sum;
                edge->source->bottom_delta2 = (node->bottom_delta2 || edge->delta);
                a = edge->explanation;
                target_ex = node->bottom_explanation2;
                while (a) {
                    n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                    n->next = target_ex;
                    n->e = a->e;
                    target_ex = n;
                    a = a->next;
                }
                edge->source->bottom_explanation2 = target_ex;
				//printf("Edge %s", _th_print_exp(edge->source->e));
				//printf(" to %s", _th_print_exp(edge->target->e));
				//printf(" offset %s\n", _th_print_exp(edge->offset));
                fill_bottoms2(env,edge->source);
            } else if (edge->source->bottom2==sum && !edge->source->bottom_delta2 &&
                       (node->bottom_delta2 || edge->delta)) {
                edge->source->bottom_delta2 = 1;
				//printf("Edge %s", _th_print_exp(edge->source->e));
				//printf(" to %s", _th_print_exp(edge->target->e));
				//printf(" offset %s\n", _th_print_exp(edge->offset));
                fill_bottoms2(env,edge->source);
                a = edge->explanation;
                target_ex = node->bottom_explanation2;
                while (a) {
                    n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                    n->next = target_ex;
                    n->e = a->e;
                    target_ex = n;
                    a = a->next;
                }
                edge->source->bottom_explanation2 = target_ex;
            }
            _tree_undent();                
        }
        edge = edge->source_next;
    }

    node->visited = 0;

    _tree_undent();
}

int node_in_table(struct env *env, struct diff_node *node)
{
	int i;
	struct diff_node *n;

	for (i = 0; i < DIFF_NODE_HASH; ++i) {
		n = env->diff_node_table[i];
		while (n) {
			if (n==node) return 1;
			n = n->next;
		}
	}
	return 0;
}

void check_integrity(struct env *env, char *place)
{
    struct diff_node *node, *rnode;
    struct diff_edge *edge;
	struct ne_list *ne;
    int i, j;
    int hash;
    //struct parent_list *p;

    if (!env->diff_node_table) return;

    for (i = 0; i < DIFF_NODE_HASH; ++i) {
        node = env->diff_node_table[i];
        while (node) {
            edge = node->edges;
            while (edge) {
                for (j = 0; j < DIFF_NODE_HASH; ++j) {
                    rnode = env->diff_node_table[j];
                    while (rnode) {
                        if (rnode==edge->target) goto cont;
                        rnode = rnode->next;
                    }
                }
                fprintf(stderr, "Illegal edge pointer in table at %x %x '%s'\n", edge, edge->target, place);
                exit(1);
cont:
                for (j = 0; j < DIFF_NODE_HASH; ++j) {
                    rnode = env->diff_node_table[j];
                    while (rnode) {
                        if (rnode==edge->source) goto cont2;
                        rnode = rnode->next;
                    }
                }
                fprintf(stderr, "Illegal edge pointer in table at %x %x '%s'\n", edge, edge->source, place);
                exit(1);
cont2:
                edge = edge->next;
            }
			if (node->eq_merge != NULL && !node_in_table(env,node->eq_merge)) {
				fprintf(stderr, "Node %s eq_merge not in table at %s\n", _th_print_exp(node->e), place);
				exit(1);
			}
			ne = node->ne_list;
			while (ne) {
				if (!ne->offset || ne->offset->type != EXP_RATIONAL) {
					fprintf(stderr, "Illegal ne entry for node %s %s\n", _th_print_exp(node->e), place);
					exit(1);
				}
				if (!node_in_table(env,ne->target)) {
					fprintf(stderr, "Illegal ne entry for node %s %s\n", _th_print_exp(node->e), place);
					exit(1);
				}
				ne = ne->next;
			}
            node = node->next;
        }
    }

#ifdef XX
    p = list;

    while (p) {
        if (_th_extract_relationship(env,p->split) && _th_is_equal_term==0) {
            hash = (((int)_th_left)/4)%DIFF_NODE_HASH;
            node = env->diff_node_table[hash];
            while (node && node->e != _th_left) node = node->next;
            if (!node) {
                if (p->unate) {
                    printf("%s not present\n", _th_print_exp(p->split));
                } else {
                    fprintf(stderr, "************* Error: %s not present\n", _th_print_exp(p->split));
                }
                goto cont3;
            }
            edge = node->edges;
            while (edge != NULL) {
                if (edge->target->e==_th_right && edge->delta==_th_delta &&
                    edge->offset==_th_diff) goto cont3;
                edge = edge->next;
            }
            if (p->unate) {
                printf("(b) %s not present\n", _th_print_exp(p->split));
            } else {
                fprintf(stderr, "************* Error(b): %s not present\n", _th_print_exp(p->split));
            }
        }
cont3:
        p = p->next;
    }
#endif
}

static struct _ex_intern *orig;

struct _ex_intern *_th_get_quick_implication(struct env *env, struct _ex_intern *e, struct add_list **expl)
{
    struct _ex_intern *sum, *res, *sum2;
    struct add_list *explanation, *ex1, *ex2, *ex, *ex3 = NULL, *ex4 = NULL;

    struct diff_node *node, *rnode;
    int hash, rhash;

    //_zone_print0("Here1");
    if (!_th_extract_relationship(env,e)) return NULL;
    //_zone_print0("Here2");

    hash = (((int)_th_left)/4)%DIFF_NODE_HASH;
    node = env->diff_node_table[hash];
    while (node && node->e != _th_left) node = node->next;
    if (node==NULL) return NULL;
    _zone_print0("Here3");
    rhash = (((int)_th_right)/4)%DIFF_NODE_HASH;
    rnode = env->diff_node_table[rhash];
    while (rnode && rnode->e != _th_right) rnode = rnode->next;
    if (rnode==NULL) return NULL;
    _zone_print0("Here4");

    _zone_print_exp("node->e", node->e);
    _zone_print_exp("rnode->e", rnode->e);

    //printf("Quick check %s\n", _th_print_exp(e));
    //printf("    left %s\n", _th_print_exp(_th_left));
    //printf("    right %s\n", _th_print_exp(_th_right));
    //printf("    diff %s\n", _th_print_exp(_th_diff));
    //printf("    delta %d\n", _th_delta);
    //printf("    is_equal_term %d\n", _th_is_equal_term);
    //fflush(stdout);

    _zone_print_exp("Quick implication", e);
    _tree_indent();
    _zone_print_exp("left", _th_left);
    _zone_print_exp("right", _th_right);
    _zone_print1("delta %d", _th_delta);
    _zone_print1("is_equal_term %d", _th_is_equal_term);
    _zone_print_exp("diff", _th_diff);
    _zone_print_exp("node bottom", node->bottom);
    _zone_print1("node bottom delta %d", node->bottom_delta);
    _zone_print_exp("rnode bottom", rnode->bottom);
    _zone_print1("rnode bottom delta %d", rnode->bottom_delta);
    _zone_print_exp("node limit", node->limit);
    _zone_print1("node limit delta %d", node->limit_delta);
    _zone_print_exp("rnode limit", rnode->limit);
    _zone_print1("rnode limit delta %d", rnode->limit_delta);
    _zone_print_exp("node bottom2", node->bottom2);
    _zone_print1("node bottom delta 2 %d", node->bottom_delta2);
    _zone_print_exp("rnode bottom2", rnode->bottom2);
    _zone_print1("rnode bottom delta 2 %d", rnode->bottom_delta2);
    _zone_print_exp("node limit 2", node->limit2);
    _zone_print1("node limit delta 2 %d", node->limit_delta2);
    _zone_print_exp("rnode limit2", rnode->limit2);
    _zone_print1("rnode limit delta2 %d", rnode->limit_delta2);

    if (node->limit && node->limit->type != EXP_RATIONAL) {
        _th_print_difference_table(env);
        fprintf(stderr, "Illegal limit in difference table\n");
        exit(1);
    }

    if (_th_is_equal_term) {
        if (rnode->limit && node->bottom) {
            
            sum = add_rationals(rnode->limit,node->bottom);
            
            if (rational_less(_th_diff,sum)) {
                ex1 = node->bottom_explanation;
                ex2 = rnode->limit_explanation;
                if (_th_is_equal_term > 0) {
                    res = _ex_false;
                    goto build_explanation;
                }
                //printf("Making true %s\n", _th_print_exp(e));
                //printf("sum = %s\n", _th_print_exp(sum));
                //printf("diff = %s\n", _th_print_exp(_th_diff));
            } else if (_th_diff==sum && (node->bottom_delta || rnode->limit_delta)) {
                ex1 = node->bottom_explanation;
                ex2 = rnode->limit_explanation;
                if (_th_is_equal_term > 0) {
                    res = _ex_false;
                    goto build_explanation;
                //} else if (!_th_delta) {
                //    res = _ex_intern_appl2_env(env,INTERN_RAT_LESS,_ex_intern_appl2_env(env,INTERN_RAT_PLUS,_th_left,_th_diff),_th_right);
                //    goto build_explanation;
                }
                //printf("Making true %s\n", _th_print_exp(e));
                //printf("sum = %s\n", _th_print_exp(sum));
                //printf("diff = %s\n", _th_print_exp(_th_diff));
                //goto build_explanation;
            }
        }
        
        if (node->limit && rnode->bottom) {
            
            //printf("    node->limit = %s\n", _th_print_exp(node->limit));
            //printf("    rnode->bottom = %s\n", _th_print_exp(rnode->bottom));
            
            sum = add_rationals(node->limit,rnode->bottom);
            //printf("    falsify sum1 = %s\n", _th_print_exp(sum));
            
            sum = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(sum->u.rational.numerator)),sum->u.rational.denominator);
            
            //printf("    falsify sum = %s\n", _th_print_exp(sum));
            //printf("    falsify diff = %s\n", _th_print_exp(_th_diff));
            if (rational_less(sum,_th_diff)) {
                ex1 = rnode->bottom_explanation;
                ex2 = node->limit_explanation;
                if (_th_is_equal_term > 0) {
                    res = _ex_false;
                    goto build_explanation;
                }
                //printf("Falsifying %s\n", _th_print_exp(e));
                //printf("sum = %s\n", _th_print_exp(sum));
                //printf("diff = %s\n", _th_print_exp(_th_diff));
            } else if (sum==_th_diff && (node->limit_delta || rnode->bottom_delta)) {
                ex1 = rnode->bottom_explanation;
                ex2 = node->limit_explanation;
                if (_th_is_equal_term > 0) {
                    res = _ex_false;
                    goto build_explanation;
                }
            }
        }
        if (node->bottom && node->limit && rnode->bottom && rnode->limit) {
            
            //printf("    node->limit = %s\n", _th_print_exp(node->limit));
            //printf("    rnode->bottom = %s\n", _th_print_exp(rnode->bottom));
            
            sum = add_rationals(node->limit,rnode->bottom);
            sum2 = add_rationals(rnode->limit,node->bottom);

			//printf("    falsify sum1 = %s\n", _th_print_exp(sum));
            
            sum = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(sum->u.rational.numerator)),sum->u.rational.denominator);
            
            //printf("    falsify sum = %s\n", _th_print_exp(sum));
            //printf("    falsify diff = %s\n", _th_print_exp(_th_diff));
            if (sum==sum2 && _th_diff==sum && !node->limit_delta && !node->bottom_delta &&
				!rnode->limit_delta && !rnode->bottom_delta) {
                ex1 = rnode->bottom_explanation;
                ex2 = node->limit_explanation;
				ex3 = rnode->limit_explanation;
				ex4 = node->bottom_explanation;
                if (_th_is_equal_term > 0) {
                    res = _ex_true;
                    goto build_explanation;
                }
                //printf("Falsifying %s\n", _th_print_exp(e));
                //printf("sum = %s\n", _th_print_exp(sum));
                //printf("diff = %s\n", _th_print_exp(_th_diff));
            }
        }

	} else {
        if (rnode->limit && node->bottom) {
            
            sum = add_rationals(rnode->limit,node->bottom);
            
            if (rational_less(_th_diff,sum)) {
                ex1 = node->bottom_explanation;
                ex2 = rnode->limit_explanation;
                res = _ex_true;
                //printf("Making true %s\n", _th_print_exp(e));
                //printf("sum = %s\n", _th_print_exp(sum));
                //printf("diff = %s\n", _th_print_exp(_th_diff));
                goto build_explanation;
            }
            if (sum==_th_diff && (!_th_delta || node->bottom_delta || rnode->limit_delta)) {
                ex1 = node->bottom_explanation;
                ex2 = rnode->limit_explanation;
                res = _ex_true;
                //printf("Making true %s\n", _th_print_exp(e));
                //printf("sum = %s\n", _th_print_exp(sum));
                //printf("diff = %s\n", _th_print_exp(_th_diff));
                goto build_explanation;
            }
            if (sum==_th_diff) {
                ex1 = node->bottom_explanation;
                ex2 = rnode->limit_explanation;
                //printf("Converting to inequality %s\n", _th_print_exp(e));
                //printf("sum = %s\n", _th_print_exp(sum));
                //printf("diff = %s\n", _th_print_exp(_th_diff));
                res = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_equal(env,_ex_real,_ex_intern_appl2_env(env,INTERN_RAT_PLUS,_th_left,_th_diff),_th_right));
                //printf("Equality 1\n");
                goto build_explanation;
            }
        }
        
        if (node->limit && rnode->bottom) {
            
            //printf("    node->limit = %s\n", _th_print_exp(node->limit));
            //printf("    rnode->bottom = %s\n", _th_print_exp(rnode->bottom));
            
            sum = add_rationals(node->limit,rnode->bottom);
            //printf("    falsify sum1 = %s\n", _th_print_exp(sum));
            
            sum = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(sum->u.rational.numerator)),sum->u.rational.denominator);
            
            //printf("    falsify sum = %s\n", _th_print_exp(sum));
            //printf("    falsify diff = %s\n", _th_print_exp(_th_diff));
            if (rational_less(sum,_th_diff)) {
                ex1 = rnode->bottom_explanation;
                ex2 = node->limit_explanation;
                res = _ex_false;
                //printf("Falsifying %s\n", _th_print_exp(e));
                //printf("sum = %s\n", _th_print_exp(sum));
                //printf("diff = %s\n", _th_print_exp(_th_diff));
                goto build_explanation;
            }
            if (sum==_th_diff && (_th_delta || node->bottom_delta || rnode->limit_delta)) {
                ex1 = rnode->bottom_explanation;
                ex2 = node->limit_explanation;
                res = _ex_false;
                //printf("Delta 2\n");
                //printf("Falsifying %s\n", _th_print_exp(e));
                //printf("sum = %s\n", _th_print_exp(sum));
                //printf("diff = %s\n", _th_print_exp(_th_diff));
                goto build_explanation;
            }
            if (sum==_th_diff) {
                ex1 = rnode->bottom_explanation;
                ex2 = node->limit_explanation;
                //printf("Converting to equality %s\n", _th_print_exp(e));
                //printf("sum = %s\n", _th_print_exp(sum));
                //printf("diff = %s\n", _th_print_exp(_th_diff));
                res = _ex_intern_appl2_env(env,INTERN_EQUAL,_ex_intern_appl2_env(env,INTERN_RAT_PLUS,_th_left,_th_diff),_th_right);
                //printf("Equality 2\n");
                goto build_explanation;
            }
        }
    }

    _tree_undent();
    return NULL;

build_explanation:
    explanation = NULL;
    while (ex1) {
        ex = (struct add_list *)_th_alloc(env->space,sizeof(struct add_list));
        ex->next = explanation;
        explanation = ex;
        ex->e = ex1->e;
        ex1 = ex1->next;
    }
    while (ex2) {
        ex = (struct add_list *)_th_alloc(env->space,sizeof(struct add_list));
        ex->next = explanation;
        explanation = ex;
        ex->e = ex2->e;
        ex2 = ex2->next;
    }
    while (ex3) {
        ex = (struct add_list *)_th_alloc(env->space,sizeof(struct add_list));
        ex->next = explanation;
        explanation = ex;
        ex->e = ex3->e;
        ex3 = ex3->next;
    }
    while (ex4) {
        ex = (struct add_list *)_th_alloc(env->space,sizeof(struct add_list));
        ex->next = explanation;
        explanation = ex;
        ex->e = ex4->e;
        ex4 = ex4->next;
    }
    if (expl) {
        *expl = explanation;
    }

    //printf("    returning %s\n", _th_print_exp(res));

    _zone_print_exp("reduction", res);
    _tree_undent();
    return res;
}

static void merge_equalities(struct env *env, struct diff_node *node1, struct diff_node *node2, struct _ex_intern *offset, struct add_list *explanation)
{
   struct diff_node *m1, *m2, *orig_root;
   struct add_list *save_expl, *save_expl2;
   struct diff_node *save_merge;
   struct _ex_intern *save_offset, *save_offset2;

   //printf("Merging equalities %s and", _th_print_exp(node1->e));
   //printf(" %s (offset", _th_print_exp(node2->e));
   //printf(" %s)\n", _th_print_exp(offset));
   //save_expl = explanation;
   //while (save_expl) {
	   //printf("    %s\n", _th_print_exp(save_expl->e));
	   //save_expl = save_expl->next;
   //}
   m1 = node1;
   while (m1->eq_merge) m1 = m1->eq_merge;
   m2 = node2;
   while (m2->eq_merge) m2 = m2->eq_merge;
   if (m1==m2) return;
   if (node1->eq_merge==NULL) {
	   node1->eq_merge = node2;
	   node1->eq_explanation = explanation;
	   node1->eq_offset = offset;
	   orig_root = node1;
   } else if (node2->eq_merge==NULL) {
	   node2->eq_merge = node1;
	   node2->eq_explanation = explanation;
	   node2->eq_offset = _th_subtract_rationals(_ex_intern_small_rational(0,1),offset);
	   orig_root = node2;
   } else {
	   m1 = node1;
	   m2 = m1->eq_merge;
	   save_expl = m1->eq_explanation;
	   save_offset = m1->eq_offset;
	   while (m2) {
		   orig_root = m2;
		   save_expl2 = m2->eq_explanation;
		   save_merge = m2->eq_merge;
		   save_offset2 = m2->eq_offset;
		   m2->eq_merge = m1;
		   m2->eq_explanation = save_expl;
		   m2->eq_offset = _th_subtract_rationals(_ex_intern_small_rational(0,1),save_offset);
		   m1 = m2;
		   save_offset = save_offset2;
		   save_expl = save_expl2;
		   m2 = save_merge;
	   }
	   node1->eq_merge = node2;
	   node1->eq_explanation = explanation;
	   node1->eq_offset = offset;
   }

   while (orig_root) {
	   struct ne_list *ne, *nne;
       m1 = orig_root;
	   offset = _ex_intern_small_rational(0,1);
	   while (m1->eq_merge) {
		   offset = _th_add_rationals(offset,m1->eq_offset);
		   m1 = m1->eq_merge;
	   }
	   ne = orig_root->ne_list;
	   while (ne) {
		   struct _ex_intern *noffs = _th_subtract_rationals(ne->offset,offset);
		   nne = m1->ne_list;
		   while (nne) {
			   if (nne->target==ne->target && nne->offset==noffs) goto skip_nne;
			   nne = nne->next;
		   }
		   nne = (struct ne_list *)_th_alloc(env->space,sizeof(struct ne_list));
		   nne->target = ne->target;
		   nne->orig_offset = ne->offset;
		   nne->e = ne->e;
		   nne->offset = noffs;
		   nne->orig_source = orig_root;
		   nne->next = m1->ne_list;
		   m1->ne_list = nne;
skip_nne:
		   ne = ne->next;
	   }
	   orig_root = orig_root->eq_merge;
    }
}

struct add_list *augment_explanation(struct env *env, struct add_list *explanation, struct add_list *ex1, struct _ex_inern *orig)
{
	struct add_list *ex;

	while (ex1) {
		if (ex1->e != orig) {
			ex = explanation;
			while (ex) {
				if (ex->e==ex1->e) goto skip;
				ex = ex->next;
			}
			ex = (struct add_list *)_th_alloc(env->space,sizeof(struct add_list));
			ex->next = explanation;
			explanation = ex;
			ex->e = ex1->e;
		}
skip:
		ex1 = ex1->next;
	}

	return explanation;
}

static struct add_list *check_ne(struct env *env, struct diff_node *left, struct diff_node *right, struct _ex_intern *offset)
{
	struct diff_node *lm, *rm, *m1, *m2;
	struct ne_list *ne;
	struct add_list *explanation, *ex, *ex1;
	int i;

	//printf("check ne %s", _th_print_exp(left->e));
	//printf(" and %s", _th_print_exp(right->e));
	//printf(" (offset %s)\n", _th_print_exp(offset));

	lm = left;
	while (lm->eq_merge) {
		offset = _th_subtract_rationals(offset,lm->eq_offset);
		lm = lm->eq_merge;
	}

	rm = right;
	while (rm->eq_merge) {
		offset = _th_add_rationals(offset,rm->eq_offset);
		rm = rm->eq_merge;
	}

	//printf("lm = %s\n", _th_print_exp(lm->e));
	//printf("rm = %s\n", _th_print_exp(rm->e));
    //printf("offset = %s\n", _th_print_exp(offset));

	ne = lm->ne_list;
	while (ne) {
		if (ne->target==rm && ne->offset==offset) {
			//printf("Found ne source %s", _th_print_exp(lm->e));
			//printf(" target %s", _th_print_exp(ne->target->e));
			//printf(" offset %s\n", _th_print_exp(offset));
			goto found_ne;
		}
		if (ne->target->eq_merge) {
			struct _ex_intern *o1 = offset;
			struct diff_node *m = ne->target;
			while (m->eq_merge) {
				o1 = _th_subtract_rationals(o1,m->eq_offset);
				m = m->eq_merge;
			}
			//printf("m = %s\n", _th_print_exp(m->e));
			//printf("o1 = %s\n", _th_print_exp(o1));
			if (m==rm && o1==ne->offset) {
    			//printf("Found ne2 source %s", _th_print_exp(lm->e));
	    		//printf(" target %s", _th_print_exp(m->e));
		    	//printf(" offset %s\n", _th_print_exp(o1));
				goto found_ne;
			}
		}
		ne = ne->next;
	}
	return NULL;

found_ne:;
	//printf("Orig source %s\n", _th_print_exp(left->e));
	//printf("Orig target %s\n", _th_print_exp(right->e));
	for (i = 0; i < DIFF_NODE_HASH; ++i) {
		struct diff_node *d = env->diff_node_table[i];
		while (d) {
			d->visited = 0;
			d = d->next;
		}
	}
	m1 = left;
	while (m1) {
		m1->visited = 1;
		m1 = m1->eq_merge;
	}
	m2 = lm;
	if (ne->orig_source) m2 = ne->orig_source;
	explanation = NULL;
	while (m2 && !m2->visited) {
		explanation = augment_explanation(env,explanation,m2->eq_explanation,NULL);
		m2 = m2->eq_merge;
	}
	m2->visited = 0;
	m1 = left;
	while (m1 && m1->visited) {
        explanation = augment_explanation(env,explanation,m1->eq_explanation,NULL);
		m1 = m1->eq_merge;
	}
	for (i = 0; i < DIFF_NODE_HASH; ++i) {
		struct diff_node *d = env->diff_node_table[i];
		while (d) {
			d->visited = 0;
			d = d->next;
		}
	}
	m1 = right;
	while (m1) {
		m1->visited = 1;
		m1 = m1->eq_merge;
	}
	//printf("ne->target = %s\n", _th_print_exp(ne->target->e));
	m2 = ne->target;
	while (m2 && !m2->visited) {
		explanation = augment_explanation(env,explanation,m2->eq_explanation,NULL);
		m2 = m2->eq_merge;
	}
	m2->visited = 0;
	m1 = right;
	while (m1 && m1->visited) {
        explanation = augment_explanation(env,explanation,m1->eq_explanation,NULL);
		m1 = m1->eq_merge;
	}
	ex = (struct add_list *)_th_alloc(env->space,sizeof(struct add_list));
	ex->next = explanation;
	ex->e = ne->e;

    return ex;
}

static struct add_list *fill_and_check_equalities(struct env *env, struct _ex_intern *orig)
{
	int i, j;
    struct diff_node *n;
    int count = 0;
	struct diff_node **list;
    struct add_list *ex, *ex1, *explanation;
    struct _ex_intern **offs;
    struct _ex_intern *zero = _ex_intern_small_rational(0,1);
    char *is_first;

	for (i = 0; i < DIFF_NODE_HASH; ++i) {
        n = env->diff_node_table[i];
        while (n) {
			if ((n->limit && n->bottom && _th_add_rationals(n->limit,n->bottom)==zero) ||
				(n->limit2 && n->bottom2 && _th_add_rationals(n->limit2,n->bottom2)==zero)) {
				++count;
			}
			n = n->next;
        }
	}
	list = (struct diff_node **)ALLOCA(sizeof(struct diff_node **) * count);
	offs = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern **) * count);
	is_first = (char *)ALLOCA(sizeof(char) * count);
	count = 0;
	for (i = 0; i < DIFF_NODE_HASH; ++i) {
        n = env->diff_node_table[i];
        while (n) {
			if (n->limit && n->bottom && _th_add_rationals(n->limit,n->bottom)==zero) {
				offs[count] = n->limit;
				is_first[count] = 1;
				list[count++] = n;
				//printf("Adding equality %s", _th_print_exp(n->e));
				//printf(" pos %s\n", _th_print_exp(n->limit));
				//printf("    %s\n", _th_print_exp(n->limit));
				//printf("    %s\n", _th_print_exp(n->bottom));
				//printf("    %s\n", _th_print_exp(n->limit2));
				//printf("    %s\n", _th_print_exp(n->bottom2));
			} else 	 if (n->limit2 && n->bottom2 && _th_add_rationals(n->limit2,n->bottom2)==zero) {
				offs[count] = n->limit2;
				is_first[count] = 0;
				list[count++] = n;
				//printf("Adding equality2 %s", _th_print_exp(n->e));
				//printf(" pos %s\n", _th_print_exp(n->limit2));
				//printf("    %s\n", _th_print_exp(n->limit));
				//printf("    %s\n", _th_print_exp(n->bottom));
				//printf("    %s\n", _th_print_exp(n->limit2));
				//printf("    %s\n", _th_print_exp(n->bottom2));
			}
			n = n->next;
        }
	}
	for (i = 0; i < count; ++i) {
		int j;
	    for (j = 0; j < count; ++j) {
			//printf("Checking ne for %s", _th_print_exp(list[i]->e));
			//printf(" and %s", _th_print_exp(list[j]->e));
			//printf(" (offsets: %s", _th_print_exp(list[i]->bottom));
			//printf(",%s)\n", _th_print_exp(list[j]->bottom));
			if (i != j && (explanation = check_ne(env,list[i],list[j], _th_subtract_rationals(offs[j],offs[i])))) {
				//printf("Found ne %s", _th_print_exp(list[i]->e));
				//printf(" and %s\n", _th_print_exp(list[j]->e));
				//printf("list[i]->bottom = %s\n", _th_print_exp(list[i]->bottom));
				//printf("list[j]->bottom = %s\n", _th_print_exp(list[j]->bottom));
				if (is_first[i] && is_first[j]) {
					explanation = augment_explanation(env,explanation,list[i]->bottom_explanation,orig);
					explanation = augment_explanation(env,explanation,list[i]->limit_explanation,orig);
					explanation = augment_explanation(env,explanation,list[j]->bottom_explanation,orig);
					explanation = augment_explanation(env,explanation,list[j]->limit_explanation,orig);
				} else if (!is_first[i] && !is_first[j]) {
					explanation = augment_explanation(env,explanation,list[i]->bottom_explanation2,orig);
					explanation = augment_explanation(env,explanation,list[i]->limit_explanation2,orig);
					explanation = augment_explanation(env,explanation,list[j]->bottom_explanation2,orig);
					explanation = augment_explanation(env,explanation,list[j]->limit_explanation2,orig);
				} else {
					for (i = 0; i < count; ++i) {
						if (list[i]->bottom) {
        					explanation = augment_explanation(env,explanation,list[i]->bottom_explanation,orig);
						}
						if (list[i]->limit) {
        					explanation = augment_explanation(env,explanation,list[i]->limit_explanation,orig);
						}
						if (list[i]->bottom2) {
        					explanation = augment_explanation(env,explanation,list[i]->bottom_explanation2,orig);
						}
						if (list[i]->limit2) {
        					explanation = augment_explanation(env,explanation,list[i]->limit_explanation2,orig);
						}
					}
				}
#ifdef XX
				printf("Add term failure %s\n", _th_print_exp(orig));
				while (explanation) {
					printf("    %s\n", _th_print_exp(explanation->e));
					explanation = explanation->next;
				}
				_th_display_difference_table(env);
				exit(1);
#endif
				return explanation;
		    }
		}
	}
	for (i = 0; i < count-1; ++i) {
		for (j = i+1; j < count; ++j) {
			if (list[i]->limit==list[i]->bottom && list[j]->limit==list[j]->bottom && list[i]->bottom && list[j]->bottom) {
				explanation = NULL;
				explanation = augment_explanation(env,explanation,list[i]->bottom_explanation,NULL);
				explanation = augment_explanation(env,explanation,list[i]->limit_explanation,NULL);
				explanation = augment_explanation(env,explanation,list[j]->bottom_explanation,NULL);
				explanation = augment_explanation(env,explanation,list[j]->limit_explanation,NULL);
				//printf("Merge1\n");
				merge_equalities(env, list[i], list[j], _th_subtract_rationals(list[j]->limit,list[i]->limit),explanation);
			} else if (list[i]->limit2==list[i]->bottom2 && list[j]->limit2==list[j]->bottom2 && list[i]->limit2 && list[j]->limit2) {
				explanation = NULL;
				explanation = augment_explanation(env,explanation,list[i]->bottom_explanation2,NULL);
				explanation = augment_explanation(env,explanation,list[i]->limit_explanation2,NULL);
				explanation = augment_explanation(env,explanation,list[j]->bottom_explanation2,NULL);
				explanation = augment_explanation(env,explanation,list[j]->limit_explanation2,NULL);
				//printf("Merge2\n");
				merge_equalities(env, list[i], list[j], _th_subtract_rationals(list[j]->limit2,list[i]->limit2),explanation);
			}
		}
	}
	return NULL;
}

static struct add_list *fill_and_check_equality(struct env *env, struct diff_node *left, struct diff_node *right, struct _ex_intern *offset, struct _ex_intern *orig)
{
    struct add_list *explanation;

	if (explanation = check_ne(env,left,right,offset)) {
#ifdef XX
		printf("Add term failure %s\n", _th_print_exp(orig));
		while (explanation) {
			printf("    %s\n", _th_print_exp(explanation->e));
			explanation = explanation->next;
		}
		_th_display_difference_table(env);
		exit(1);
#endif
		return explanation;
	}
	explanation = (struct add_list *)_th_alloc(env->space,sizeof(struct add_list));
	explanation->next = NULL;
	explanation->e = orig;
	merge_equalities(env, left, right, offset, explanation);

	return NULL;
}

struct add_list *_th_prepare_quick_implications(struct env *env, struct _ex_intern *e)
{
    int hash;
    int rhash;
    int i;
    struct diff_node *node, *n;
    struct diff_node *rnode;
    //struct _ex_intern *cdiff;

    orig = e;

    if (!_th_extract_relationship(env,e)) return NULL;
	if (_th_is_equal_term==-1) return NULL;
    if (_th_is_equal_term) _th_delta = 0;

    for (i = 0; i < DIFF_NODE_HASH; ++i) {
        n = env->diff_node_table[i];
        while (n) {
            n->visited = 0;
            n->limit = NULL;
            n->bottom = NULL;
            n->limit2 = NULL;
			n->bottom2 = NULL;
			n = n->next;
        }
    }

    _zone_print0("_th_get_implications");

    hash = (((int)_th_left)/4)%DIFF_NODE_HASH;
    rhash = (((int)_th_right)/4)%DIFF_NODE_HASH;
    node = env->diff_node_table[hash];
    rnode = env->diff_node_table[rhash];
    while (node && node->e != _th_left) node = node->next;
    while (rnode && rnode->e != _th_right) rnode = rnode->next;

    if (node==NULL) return NULL;
    if (rnode==NULL) return NULL;

    node->bottom = _ex_intern_small_rational(0,1);
    node->bottom_explanation = NULL;
    //(struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
    //node->explanation->next = NULL;
    //node->explanation->e = e;
    node->bottom_delta = 0;
    //printf("diff = %s\n", _th_print_exp(_th_diff));
    rnode->limit = _th_diff;
    rnode->limit_explanation = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
    rnode->limit_explanation->next = NULL;
    rnode->limit_explanation->e = e;
    rnode->limit_delta = _th_delta;

    _tree_indent();

    _zone_print_exp("node", node->e);
    _zone_print_exp("rnode", rnode->e);

    fill_limits(env,rnode);
    fill_bottoms(env,node);

	if (_th_is_equal_term) {
        rnode->bottom2 = _th_subtract_rationals(_ex_intern_small_rational(0,1),_th_diff);
        rnode->bottom_explanation2 = NULL;
        //(struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        //node->explanation->next = NULL;
        //node->explanation->e = e;
        rnode->bottom_delta2 = 0;
        //printf("diff = %s\n", _th_print_exp(_th_diff));
        node->limit2 = _ex_intern_small_rational(0,1);
        node->limit_explanation2 = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        node->limit_explanation2->next = NULL;
        node->limit_explanation2->e = e;
        node->limit_delta2 = _th_delta;

        fill_limits2(env,node);
        fill_bottoms2(env,rnode);
	}

	//_zone_print("Before fill_and_check_equalities");

	if ((node->limit && node->limit==_ex_intern_small_rational(0,1)) || (rnode->limit2 && rnode->limit2==_ex_intern_small_rational(0,1))) {
		struct add_list *r;
		//printf("**** CYCLE MERGE **** %s\n", _th_print_exp(e));
		//_th_display_difference_table(env);
        _zone_print0("Doing fill_and_check_equalities");
		//printf("left %s\n", _th_print_exp(_th_left));
		//printf("right %s\n", _th_print_exp(_th_right));
		//printf("diff %s\n", _th_print_exp(_th_diff));
		r = fill_and_check_equalities(env,e);
		if (r) {
    		_tree_undent();
			return r;
		}
	}

	if (_th_is_equal_term) {
		_tree_undent();
		//printf("Quick equality\n");
		//printf("left %s\n", _th_print_exp(_th_left));
		//printf("right %s\n", _th_print_exp(_th_right));
		//printf("diff %s\n", _th_print_exp(_th_diff));
		return fill_and_check_equality(env,node,rnode,_th_diff,e);
	}

#ifdef XX
    if (_zone_active()) {
        _zone_print0("Node info");
        _tree_indent();
        for (i = 0; i < DIFF_NODE_HASH; ++i) {
            n = env->diff_node_table[i];
            while (n) {
                _zone_print_exp("Node", n->e);
                _tree_indent();
                if (n->has_limit) {
                    _zone_print_exp("limit", n->limit);
                    _zone_print1("limit delta %d", n->limit_delta);
                }
                if (n->has_bottom) {
                    _zone_print_exp("bottom", n->bottom);
                    _zone_print1("bottom delta %d", n->bottom_delta);
                }
                _tree_undent();
                n = n->next;
            }
        }
        _tree_undent();
    }
#endif

    _tree_undent();
    return NULL;
}

void _th_prepare_node_implications(struct env *env, struct _ex_intern *e)
{
    int i;
    struct diff_node *n, *node;
    int hash;

    //printf("prepare node implications %s\n", _th_print_exp(e));
    //fflush(stdout);

    if (!_th_extract_relationship(env,e)) return;
    hash = (((int)_th_right)/4)%DIFF_NODE_HASH;
    node = env->diff_node_table[hash];
    while (node && node->e != _th_right) node = node->next;

    for (i = 0; i < DIFF_NODE_HASH; ++i) {
        n = env->diff_node_table[i];
        while (n) {
            n->visited = 0;
            n->limit = NULL;
            n->bottom = NULL;
            n = n->next;
        }
    }

    _zone_print_exp("prepare_node_implications", node->e);
#ifndef FAST
    if (_zone_active()) _th_print_difference_table(env);
#endif

    node->bottom = _ex_intern_small_rational(0,1);
    node->bottom_explanation = NULL;
    node->bottom_delta = 0;
    node->limit = node->bottom;
    node->limit_explanation = NULL;
    node->limit_delta = 0;

#ifdef XX
    for (i = 0; i < DIFF_NODE_HASH; ++i) {
        n = env->diff_node_table[i];
        while (n) {
            if (n->limit) {
                if (n->limit->type!=EXP_RATIONAL) {
                    fprintf(stderr, "Node %s\n", _th_print_exp(node->e));
                    fprintf(stderr, "    has illegal limit %s\n", _th_print_exp(node->limit));
                    exit(1);
                }
            }
            if (n->bottom) {
                if (n->bottom->type!=EXP_RATIONAL) {
                    fprintf(stderr, "Node %s\n", _th_print_exp(node->e));
                    fprintf(stderr, "    has illegal bottom %s\n", _th_print_exp(node->bottom));
                    exit(1);
                }
            }
            n = n->next;
        }
    }
#endif

    _tree_indent();

    fill_limits(env,node);
    fill_bottoms(env,node);

#ifdef XX
    if (_zone_active()) {
        _zone_print0("Node info");
        _tree_indent();
        for (i = 0; i < DIFF_NODE_HASH; ++i) {
            n = env->diff_node_table[i];
            while (n) {
                _zone_print_exp("Node", n->e);
                _tree_indent();
                if (n->has_limit) {
                    _zone_print_exp("limit3", n->limit);
                    _zone_print1("limit delta %d", n->limit_delta);
                }
                if (n->has_bottom) {
                    _zone_print_exp("bottom", n->bottom);
                    _zone_print1("bottom delta %d", n->bottom_delta);
                }
                _tree_undent();
                n = n->next;
            }
        }
        _tree_undent();
    }
#endif

#ifndef FAST
    if (_zone_active()) _th_print_difference_table(env);
#endif

    //check_integrity(env, "prepare_node_implications", NULL);

    _tree_undent();

	return;
}

static void build_model(struct env *env, struct diff_node *node)
{
    struct diff_edge *edge;
    struct add_list *target_ex;
    struct _ex_intern *sum;

    _zone_print_exp("build_model", node->e);
    _tree_indent();

    node->visited = 1;
    target_ex = NULL;
    edge = node->edges;
    while (edge) {
        //if (!edge->target->visited) {
            _zone_print_exp("Edge", edge->target->e);
            _tree_indent();
            _zone_print_exp("Offset", edge->offset);
            sum = add_rationals(node->bottom,edge->offset);
            if (edge->delta) {
                sum = add_rationals(sum,_ex_intern_small_rational(1,1000));
            }
            if (edge->target->bottom==NULL ||
                rational_less(edge->target->bottom,sum)) {
                edge->target->bottom = sum;
                build_model(env,edge->target);
            }
            _tree_undent();                
        //}
        edge = edge->next;
    }

    node->visited = 0;

    _tree_undent();
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

static void print_as_smt(FILE *f, struct env *env, int indent, struct _ex_intern *e)
{
    int i;
    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_AND) {
        fprintf(f,"%*s(and\n", indent, "");
        for (i = 0; i < e->u.appl.count; ++i) {
            print_as_smt(f,env,indent+4,e->u.appl.args[i]);
        }
        fprintf(f,"%*s)\n", indent, "");
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_OR) {
        fprintf(f,"%*s(or\n", indent, "");
        for (i = 0; i < e->u.appl.count; ++i) {
            print_as_smt(f,env,indent+4,e->u.appl.args[i]);
        }
        fprintf(f,"%*s)\n", indent, "");
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_ITE && get_type(env,e->u.appl.args[1])==_ex_bool) {
        fprintf(f,"%*s(if_then_else\n", indent, "");
        for (i = 0; i < e->u.appl.count; ++i) {
            print_as_smt(f,env,indent+4,e->u.appl.args[i]);
        }
        fprintf(f,"%*s)\n", indent, "");
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_ITE) {
        fprintf(f,"%*s(ite\n", indent, "");
        for (i = 0; i < e->u.appl.count; ++i) {
            print_as_smt(f,env,indent+4,e->u.appl.args[i]);
        }
        fprintf(f,"%*s)\n", indent, "");
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL &&
               get_type(env,e->u.appl.args[0])==_ex_bool) {
            fprintf(f,"%*s(iff\n", indent, "");
        for (i = 0; i < e->u.appl.count; ++i) {
            print_as_smt(f,env,indent+4,e->u.appl.args[i]);
        }
        fprintf(f,"%*s)\n", indent, "");
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT &&
               e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_EQUAL &&
               get_type(env,e->u.appl.args[0]->u.appl.args[0])==_ex_bool) {
        fprintf(f,"%*s(not (iff\n", indent, "");
        e = e->u.appl.args[0];
        for (i = 0; i < e->u.appl.count; ++i) {
            print_as_smt(f,env,indent+4,e->u.appl.args[i]);
        }
        fprintf(f,"%*s))\n", indent, "");
    } else if (_th_extract_relationship(env,e)) {
        if (_th_is_equal_term > 0) {
            fprintf(f,"%*s(=", indent, "");
            if (((int)_th_diff->u.rational.numerator[1]) >= 0) {
                fprintf(f, " (+ %s %d)", _th_print_exp(_th_left), ((int)_th_diff->u.rational.numerator[1]));
            } else {
                fprintf(f, " (- %s %d)", _th_print_exp(_th_left), 0-((int)_th_diff->u.rational.numerator[1]));
            }
            fprintf(f, " %s)\n", _th_print_exp(_th_right));
        } else if (_th_is_equal_term < 0) {
            fprintf(f,"%*s(not (=", indent, "");
            if (((int)_th_diff->u.rational.numerator[1]) >= 0) {
                fprintf(f, " (+ %s %d)", _th_print_exp(_th_left), ((int)_th_diff->u.rational.numerator[1]));
            } else {
                fprintf(f, " (- %s %d)", _th_print_exp(_th_left), 0-((int)_th_diff->u.rational.numerator[1]));
            }
            fprintf(f, " %s))\n", _th_print_exp(_th_right));
        } else {
            if (_th_delta) {
                fprintf(f, "%*s(<", indent, "");
            } else {
                fprintf(f, "%*s(<=", indent, "");
            }
            if (((int)_th_diff->u.rational.numerator[1]) >= 0) {
                fprintf(f, " (+ %s %d)", _th_print_exp(_th_left), ((int)_th_diff->u.rational.numerator[1]));
            } else {
                fprintf(f, " (- %s %d)", _th_print_exp(_th_left), 0-((int)_th_diff->u.rational.numerator[1]));
            }
            fprintf(f, " %s)\n", _th_print_exp(_th_right));
        }
    } else if (e==_ex_true || (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT && e->u.appl.args[0]==_ex_false)) {
        fprintf(f, "%*strue\n", indent, "");
    } else if (e==_ex_false || (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT && e->u.appl.args[0]==_ex_true)) {
        fprintf(f, "%*sfalse\n", indent, "");
    } else if (e->type==EXP_VAR) {
        fprintf(f, "%*s%s\n", indent, "", _th_print_exp(e));
    } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
        fprintf(f,"%*s(not\n", indent, "");
        print_as_smt(f,env,indent+4,e->u.appl.args[0]);
        fprintf(f,"%*s)\n", indent, "");
    } else {
        fprintf(f, "Unused %s\n", _th_print_exp(e));
    }
}

void add_state(struct env *env, struct parent_list *list, struct _ex_intern *e, char *name)
{
    FILE *f = fopen("states","a");
    struct parent_list *p;

    if (name != NULL) fprintf(f, "%s\n", name);

#ifdef FAST
    fprintf(f, "STATE\n");
#else
    fprintf(f, "STATE %d\n", _tree_get_indent());
#endif

    fprintf(f, "    :formula (and\n");
    p = list;
    while (p) {
        print_as_smt(f,env,8,p->split);
        p = p->next;
    }
    print_as_smt(f,env,8,e);
    fprintf(f,"    ))\n");
    fclose(f);
}

void dump_state(struct env *env, struct parent_list *list)
{
    FILE *f = fopen("dump.smt","w");
    int i;
    struct diff_node *n;
    //struct _ex_intern *e = _ex_intern_var(_th_intern("cvclZero"));
    //int hash = (((int)e)/4)%DIFF_NODE_HASH;
    struct parent_list *p;

    fprintf(f, "(benchmark dump.smt\n");
    fprintf(f, "    :source { HTP generated for debugging }\n");
    fprintf(f, "    :status unsat\n");
    fprintf(f, "    :logic QF_RDL\n");

    for (i = 0; i < DIFF_NODE_HASH; ++i) {
        n = env->diff_node_table[i];
        while (n) {
            fprintf(f, "    :extrafuns ((%s Real))\n", _th_print_exp(n->e));
            n = n->next;
        }
    }
    fprintf(f, "    :formula (and\n");
    p = list;
    while (p) {
        print_as_smt(f,env,8,p->split);
        p = p->next;
    }
    fprintf(f,"    ))\n");
    fclose(f);
}

int has_bad_model(struct env *env, struct parent_list *list)
{
    int i;
    struct diff_node *n;
    struct _ex_intern *e = _ex_intern_var(_th_intern("cvclZero"));
    int hash = (((int)e)/4)%DIFF_NODE_HASH;
    struct parent_list *p;

    for (i = 0; i < DIFF_NODE_HASH; ++i) {
        n = env->diff_node_table[i];
        while (n) {
            n->visited = 0;
            n->limit = NULL;
            n->bottom = NULL;
            n = n->next;
        }
    }

    n = env->diff_node_table[hash];
    while (n && n->e != e) n = n->next;
    if (n != NULL) {
        n->bottom = _ex_intern_small_rational(0,1);
        build_model(env,n);
    }

    p = list;
    while (p) {
        if (_th_extract_relationship(env,p->split) && _th_is_equal_term==0) {
            struct _ex_intern *t, *lv, *rv;

            hash = (((int)_th_left)/4)%DIFF_NODE_HASH;
            n = env->diff_node_table[hash];
            while (n && n->e != _th_left) n = n->next;
            lv = n->bottom;
            hash = (((int)_th_right)/4)%DIFF_NODE_HASH;
            n = env->diff_node_table[hash];
            while (n && n->e != _th_right) n = n->next;
            rv = n->bottom;

            if (lv  && rv) {
                t = add_rationals(lv,_th_diff);
                if (!_th_delta && t==rv) {
                    ;
                } else if (rational_less(t,rv)) {
                    ;
                } else {
                    return 1;
                }
            }
        }
        p = p->next;
    }

    return 0;
}

static struct add_list *check_for_contradiction(struct env *env)
{
    int hash = (((int)_th_left)/4)%DIFF_NODE_HASH;
    int rhash = (((int)_th_right)/4)%DIFF_NODE_HASH;
    int i;
    struct diff_node *node;
    struct diff_node *rnode;
    //struct _ex_intern *cdiff;
    struct add_list *res;

    //check_integrity(env, "begin check_for_contradiction");

    for (i = 0; i < DIFF_NODE_HASH; ++i) {
        node = env->diff_node_table[i];
        while (node) {
            node->visited = 0;
            node->has_bottom = 0;
            node = node->next;
        }
    }

    //printf("Checking for contradiction %d\n", _tree_zone);
    //printf("Checking for contradiction\n");
    //printf("    left %s\n", _th_print_exp(_th_left));
    //printf("    right %s\n", _th_print_exp(_th_right));
    //printf("    diff %s\n", _th_print_exp(_th_diff));
    //printf("    delta %d\n", _th_delta);

    _zone_print0("Check for contradiction");
    _zone_print2("Hashes %d %d", hash, rhash);

    is_equal = 0;
    node = env->diff_node_table[hash];
    rnode = env->diff_node_table[rhash];
    while (node && node->e != _th_left) node = node->next;
    while (rnode && rnode->e != _th_right) rnode = rnode->next;

    //printf("    node, rnode = %d %d\n", node, rnode);

    if (node==NULL) return 0;
    if (rnode==NULL) return 0;

    //_zone_print0("Here1");

    //cdiff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(_th_diff->u.rational.numerator)),
    //    _th_diff->u.rational.denominator);
    //node->has_bottom = 1;
    //node->bottom = _ex_intern_small_rational(0,1);
    //node->bottom_explanation = NULL;
    //node->bottom_delta = 0;

	//printf("Testing %s to", _th_print_exp(node->e));
	//printf(" %s\n", _th_print_exp(rnode->e));

    _tree_indent();
	//printf("Testing %s %d\n", _th_print_exp(_th_diff), _th_delta);
    res = cc(env, node, rnode, _th_diff, _th_delta, NULL);
    _tree_undent();

    //if (res) {
    //    struct add_list *expl = res;
    //    //printf("Found contradiction %d\n", _tree_zone);
    //    printf("Found countradiction\n");
    //    printf("   left %s\n", _th_print_exp(_th_left));
    //    printf("   right %s\n", _th_print_exp(_th_right));
    //    printf("   diff %s\n", _th_print_exp(_th_diff));
    //    printf("   delta %d\n", _th_delta);
    //    while (expl) {
    //        printf("        %s\n", _th_print_exp(expl->e));
    //        expl = expl->next;
    //    }
    //}

    //check_integrity(env, "end check_for_contradiction");

    return res;
}

static struct add_list *check_for_ne(struct env *env)
{
    int hash = (((int)_th_left)/4)%DIFF_NODE_HASH;
    int rhash = (((int)_th_right)/4)%DIFF_NODE_HASH;
    int i;
    struct diff_node *node;
    struct diff_node *rnode;
    //struct _ex_intern *cdiff;
    struct add_list *res;

    //check_integrity(env, "begin check_for_contradiction");

    //printf("Checking for contradiction %d\n", _tree_zone);
    //printf("Checking for contradiction\n");
    //printf("    left %s\n", _th_print_exp(_th_left));
    //printf("    right %s\n", _th_print_exp(_th_right));
    //printf("    diff %s\n", _th_print_exp(_th_diff));
    //printf("    delta %d\n", _th_delta);

    _zone_print0("Check for ne");
    _zone_print2("Hashes %d %d", hash, rhash);

    is_equal = 0;
    node = env->diff_node_table[hash];
    rnode = env->diff_node_table[rhash];
    while (node && node->e != _th_left) node = node->next;
    while (rnode && rnode->e != _th_right) rnode = rnode->next;

    //printf("    node, rnode = %d %d\n", node, rnode);

    if (node==NULL) return 0;
    if (rnode==NULL) return 0;

    //_zone_print0("Here1");

    //cdiff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(_th_diff->u.rational.numerator)),
    //    _th_diff->u.rational.denominator);
    //node->has_bottom = 1;
    //node->bottom = _ex_intern_small_rational(0,1);
    //node->bottom_explanation = NULL;
    //node->bottom_delta = 0;

	//printf("Testing %s to", _th_print_exp(node->e));
	//printf(" %s\n", _th_print_exp(rnode->e));

    _tree_indent();
	//printf("Testing %s %d\n", _th_print_exp(_th_diff), _th_delta);
    res = check_ne(env, node, rnode, _th_diff);
    _tree_undent();

    //if (res) {
    //    struct add_list *expl = res;
    //    //printf("Found contradiction %d\n", _tree_zone);
    //    printf("Found countradiction\n");
    //    printf("   left %s\n", _th_print_exp(_th_left));
    //    printf("   right %s\n", _th_print_exp(_th_right));
    //    printf("   diff %s\n", _th_print_exp(_th_diff));
    //    printf("   delta %d\n", _th_delta);
    //    while (expl) {
    //        printf("        %s\n", _th_print_exp(expl->e));
    //        expl = expl->next;
    //    }
    //}

    //check_integrity(env, "end check_for_contradiction");

    return res;
}

struct _ex_intern *_th_check_cycle_rless(struct env *env, struct _ex_intern *e, struct add_list **expl)
{
    struct add_list *ex;
    //printf("Checking %s\n", _th_print_exp(e));
    _zone_print_exp("Check rless cycle", e);

    if (!env->diff_node_table) return NULL;

	_zone_print_exp("_th_check_cycle_rless", e);
	//printf("Checking %s\n", _th_print_exp(e));
#ifndef FAST
    if (_zone_active()) _th_print_difference_table(env);
#endif

    if (!_th_extract_relationship(env,e)) return NULL;
    if (_th_is_equal_term < 0) return NULL;

    _zone_print_exp("left", _th_left);
    _zone_print_exp("right", _th_right);
    _zone_print_exp("diff", _th_diff);
    _zone_print1("delta %d", _th_delta);
    _zone_print1("is_equal_term %d", _th_is_equal_term);

    if (_th_is_equal_term) _th_delta = 0;

    if (ex = check_for_contradiction(env)) {
		//printf("False case\n");
        _tree_indent();
        _zone_print0("false");
        _tree_undent();
        //exit(1);
        //printf("    false\n");
        //_th_print_difference_table(env);
        if (expl) *expl = ex;
		_zone_print0("false being returned 0");
        return _ex_false;
    }
    if (is_equal && !_th_is_equal_term) {
        if (expl) *expl = is_equal_expl;
		_zone_print0("equal being returned");
        return _ex_intern_equal(env,_ex_real,_ex_intern_appl2_env(env,INTERN_RAT_PLUS,_th_left,_th_diff),_th_right);
    }

    e = _th_left;
    _th_left = _th_right;
    _th_right = e;

    _th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(_th_diff->u.rational.numerator)),
        _th_diff->u.rational.denominator);
    if (!_th_is_equal_term) {
        _th_delta = !_th_delta;
    }

    if (ex = check_for_contradiction(env)) {
		//printf("True case\n");
        _tree_indent();
        _zone_print0("true");
        _tree_undent();
        //exit(1);
        //printf("    true\n");
        //_th_print_difference_table(env);
        if (expl) *expl = ex;
        if (_th_is_equal_term) {
    		_zone_print0("false being returned 1");
            return _ex_false;
        } else {
    		_zone_print0("true being returned 1");
            return _ex_true;
        }
    }

	if (_th_is_equal_term) {
		struct add_list *ex2, *ex3;
		_th_delta = 1;
		if (ex = check_for_contradiction(env)) {
            e = _th_left;
            _th_left = _th_right;
            _th_right = e;
            _th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(_th_diff->u.rational.numerator)),
                _th_diff->u.rational.denominator);
     		if (ex2 = check_for_contradiction(env)) {
				ex3 = ex2;
				if (ex3==NULL) {
					ex2 = ex;
				} else {
					while (ex3->next) {
						ex3 = ex3->next;
					}
					ex3->next = ex;
				}
				if (expl) *expl = ex2;
        		_zone_print0("true being returned 2");
				//printf("equal true case\n");
				return _ex_true;
			}
		}
		//printf("Checking ne\n");
		//printf("    _th_left = %s\n", _th_print_exp(_th_left));
		//printf("    _th_right = %s\n", _th_print_exp(_th_right));
		//printf("    _th_diff = %s\n", _th_print_exp(_th_diff));
		ex = check_for_ne(env);
		if (ex) {
			if (expl) *expl = ex;
			return _ex_false;
		}
		e = _th_left;
		_th_left = _th_right;
		_th_right = e;
		_th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(_th_diff->u.rational.numerator)),
            _th_diff->u.rational.denominator);
		//printf("Checking ne\n");
		//printf("    _th_left = %s\n", _th_print_exp(_th_left));
		//printf("    _th_right = %s\n", _th_print_exp(_th_right));
		//printf("    _th_diff = %s\n", _th_print_exp(_th_diff));
		ex = check_for_ne(env);
		if (ex) {
			if (expl) *expl = ex;
			return _ex_false;
		}
	}

    return NULL;
}

static struct cycle_list *equals;

struct trail_list {
    struct trail_list *next;
    struct _ex_intern *left, *right, *diff, *expl;
};

static struct _ex_intern *zero = NULL;

int _th_do_implications;

int edge_is_present(struct diff_node *node, struct diff_node *target, struct _ex_intern *offset, int delta)
{
    struct diff_edge *t = node->edges;

    while (t) {
        if (t->offset==offset && t->target==target && t->delta==delta) return 1;
        t = t->next;
    }

    return 0;
}

int source_edge_is_present(struct diff_node *node, struct diff_node *source, struct _ex_intern *offset, int delta)
{
    struct diff_edge *t = node->source_edges;

    while (t) {
        if (t->offset==offset && t->source==source && t->delta==delta) return 1;
        t = t->source_next;
    }

    return 0;
}

static int add_inequality(struct env *env, struct _ex_intern *explanation, struct add_list **expl);

int _th_add_reduction(struct env *env, struct _ex_intern *expl, struct _ex_intern *e, struct _ex_intern *reduce, struct _ex_intern *offset, struct add_list **expla)
{
	static struct _ex_intern *zero=NULL;
    int res;

    if (!is_basic_term(e)) return 0;

    _th_do_implications = 0;

    if (reduce==NULL) {
        if (zero==NULL) zero = _ex_intern_small_rational(0,1);
        reduce = zero;
    }
    if (!is_basic_term(reduce)) return 0;

	if (offset==NULL) {
        if (zero==NULL) zero = _ex_intern_small_rational(0,1);
        offset = zero;
    }

	_th_left = reduce;
	_th_diff = offset;
	_th_right = e;
	_th_delta = 0;
	_th_is_equal_term = 0;
    res = add_inequality(env,expl,expla);
    if (res) return res;
	_th_left = e;
	_th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(offset->u.rational.numerator)),offset->u.rational.denominator);
	_th_right = reduce;
	_th_delta = 0;
	_th_is_equal_term = 0;
    res = add_inequality(env,expl,expla);
    return res;
}

void check_less(struct env *env, char *place)
{
    static struct _ex_intern *ct = NULL;
    int hash;
    struct diff_node *n;
    struct diff_edge *edge;
    static struct _ex_intern *zero = NULL;

    if (ct==NULL) {
        ct = _th_parse(env,"(rless x_9 x_8)");
        zero = _ex_intern_small_rational(0,1);
    }

    if (ct->find != ct) return;
    if (ct->in_hash==0) return;

    hash = (((int)ct->u.appl.args[0])/4)%DIFF_NODE_HASH;

    n = env->diff_node_table[hash];
    while (n && n->e != ct->u.appl.args[0]) n = n->next;
    if (n==NULL) return;

    edge = n->edges;
    while (edge) {
        if (edge->target->e==ct->u.appl.args[1] &&
            edge->delta && edge->offset==zero) {
            _th_print_difference_table(env);
            fprintf(stderr, "Relationship for %s in difference table but not find at %s\n", _th_print_exp(ct), place);
            exit(1);
        }
        edge = edge->next;
    }
}

static int add_inequality(struct env *env, struct _ex_intern *explanation, struct add_list **expl)
{
    int hash = (((int)_th_left)/4)%DIFF_NODE_HASH;
    int rhash = (((int)_th_right)/4)%DIFF_NODE_HASH;
    struct diff_node *node = env->diff_node_table[hash];
    struct diff_node *rnode = env->diff_node_table[rhash];
    struct diff_edge *edge;
    struct add_list *al;
    struct ne_list *ne;

    //char *mark = _th_alloc_mark(REWRITE_SPACE);

    //check_integrity(env, "begin add_inequality");

    while (node && node->e != _th_left) node = node->next;
    while (rnode && rnode->e != _th_right) rnode = rnode->next;

    _zone_print2("Hashes %d %d", hash, rhash);

    if (node==NULL) {
        node = (struct diff_node *)_th_alloc(env->space,sizeof(struct diff_node));
        node->e = _th_left;
        node->next = env->diff_node_table[hash];
        env->diff_node_table[hash] = node;
        node->edges = NULL;
        node->source_edges = NULL;
        node->limit = node->bottom = NULL;
        node->ne_list = NULL;
		node->eq_merge = NULL;
		node->eq_explanation = NULL;
		node->move = node->move_back = NULL;
        _zone_print0("Adding_node");
        //printf("Adding node %x %d\n", node, hash);
    }

    if (rnode==NULL) {
        rnode = (struct diff_node *)_th_alloc(env->space,sizeof(struct diff_node));
        rnode->e = _th_right;
        rnode->next = env->diff_node_table[rhash];
        env->diff_node_table[rhash] = rnode;
        rnode->edges = NULL;
        rnode->source_edges = NULL;
        rnode->limit = rnode->bottom = NULL;
        rnode->ne_list = NULL;
		rnode->eq_merge = NULL;
		rnode->eq_explanation = NULL;
		rnode->move = rnode->move_back = NULL;
        _zone_print0("Adding rnode");
        //printf("Adding rnode %x %d\n", rnode, rhash);
    }

    edge = node->edges;

    while (edge) {
        _zone_print_exp("Edge target", edge->target->e);
        if (edge->target->e==_th_right) {
        	//unsigned *tmp1, *tmp2;
            _zone_print0("Testing target");
            if (edge->offset==_th_diff && (!_th_delta || edge->delta)) return 0;
            _zone_print0("Testing target 1");
            if (rational_less(_th_diff,edge->offset)) return 0;
     		//tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(edge->offset->u.rational.numerator,_th_diff->u.rational.denominator)) ;
	    	//tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(_th_diff->u.rational.numerator,edge->offset->u.rational.denominator)) ;
		    //if (_th_big_less(tmp1,tmp2)) return;
            _zone_print0("Testing target 2");
        }
        edge = edge->next;
    }

    if (!edge_is_present(node,rnode,_th_diff,_th_delta)) {
        edge = (struct diff_edge *)_th_alloc(env->space,sizeof(struct diff_edge));
        al = (struct add_list *)_th_alloc(env->space,sizeof(struct add_list));

        edge->next = node->edges;
        edge->source_next = rnode->source_edges;
        node->edges = edge;
        rnode->source_edges = edge;
        edge->delta = _th_delta;
        edge->offset = _th_diff;
        al->e = explanation;
        al->next = NULL;
        edge->explanation = al;
        //printf("edge = %x\n", edge);
        if (_th_diff==NULL) {
            printf("diff null\n");
            exit(1);
        }
        edge->target = rnode;
        edge->source = node;

#ifdef XX
        ne = node->ne_list;
        while (ne) {
            if (ne->target==edge->target && ne->offset==edge->offset) {
                edge->delta = 1;
            }
            ne = ne->next;
        }
#endif

    }
    //printf("Adding edge 3 %d %s", _tree_zone, _th_print_exp(edge->source->e));
    //printf(" %s", _th_print_exp(edge->target->e));
    //printf(" %s %d\n", _th_print_exp(edge->offset), edge->delta);

    //_th_alloc_release(REWRITE_SPACE, mark);

    //check_integrity(env, "end add_inequality");

    return 0;
}

static int add_not_equal(struct env *env, struct _ex_intern *explanation,struct add_list **expl)
{
    int hash = (((int)_th_left)/4)%DIFF_NODE_HASH;
    int rhash = (((int)_th_right)/4)%DIFF_NODE_HASH;
    struct diff_node *node = env->diff_node_table[hash];
    struct diff_node *rnode = env->diff_node_table[rhash];
	struct diff_node *m1, *m2;
    struct diff_edge *edge;
    struct ne_list *ne;
    struct _ex_intern *offset;

    //char *mark = _th_alloc_mark(REWRITE_SPACE);

    //check_integrity(env, "begin add_inequality");

    while (node && node->e != _th_left) node = node->next;
    while (rnode && rnode->e != _th_right) rnode = rnode->next;

    _zone_print2("Hashes %d %d", hash, rhash);

    if (node==NULL) {
        node = (struct diff_node *)_th_alloc(env->space,sizeof(struct diff_node));
        node->e = _th_left;
        node->next = env->diff_node_table[hash];
        env->diff_node_table[hash] = node;
        node->edges = NULL;
        node->source_edges = NULL;
        node->limit = node->bottom = NULL;
        node->ne_list = NULL;
		node->eq_merge = NULL;
		node->eq_explanation = NULL;
		node->move = node->move_back = NULL;
        _zone_print0("Adding_node");
        //printf("Adding node %x %d\n", node, hash);
    }

    if (rnode==NULL) {
        rnode = (struct diff_node *)_th_alloc(env->space,sizeof(struct diff_node));
        rnode->e = _th_right;
        rnode->next = env->diff_node_table[rhash];
        env->diff_node_table[rhash] = rnode;
        rnode->edges = NULL;
        rnode->source_edges = NULL;
        rnode->limit = rnode->bottom = NULL;
        rnode->ne_list = NULL;
		rnode->eq_merge = NULL;
		rnode->eq_explanation = NULL;
		rnode->move = rnode->move_back = NULL;
        _zone_print0("Adding rnode");
        //printf("Adding rnode %x %d\n", rnode, rhash);
    }

	m1 = node;
	offset = _ex_intern_small_rational(0,1);
	while (m1->eq_merge) {
		offset = _th_add_rationals(offset,m1->eq_offset);
		m1 = m1->eq_merge;
	}
	m2 = rnode;
	while (m2->eq_merge) {
		offset = _th_subtract_rationals(offset,m2->eq_offset);
		m2 = m2->eq_merge;
	}
	if (m1==m2 && offset==_th_diff) {
		//printf("    Add ne failure\n");
		//printf("        %s\n", _th_print_exp(node->e));
		//printf("        %s\n", _th_print_exp(rnode->e));
		//printf("        %s\n", _th_print_exp(offset));
		if (expl) {
			struct add_list *explanation, *ex, *ex1;
			int i;
			for (i = 0; i < DIFF_NODE_HASH; ++i) {
				struct diff_node *d = env->diff_node_table[i];
				while (d) {
					d->visited = 0;
					d = d->next;
				}
			}
			m1 = node;
			while (m1) {
				m1->visited = 1;
				m1 = m1->eq_merge;
			}
			m2 = rnode;
			explanation = NULL;
			while (m2 && !m2->visited) {
				ex1 = m2->eq_explanation;
				while (ex1) {
					ex = explanation;
					while (ex) {
						if (ex->e==ex1->e) goto skip2;
						ex = ex->next;
					}
					ex = (struct add_list *)_th_alloc(env->space,sizeof(struct add_list));
					ex->next = explanation;
					ex->e = ex1->e;
					explanation = ex;
skip2:
					ex1 = ex1->next;
				}
				m2 = m2->eq_merge;
			}
			m2->visited = 0;
			m1 = node;
			while (m1 && m1->visited) {
				ex1 = m1->eq_explanation;
				while (ex1) {
					ex = explanation;
					while (ex) {
						if (ex->e==ex1->e) goto skip1;
						ex = ex->next;
					}
					ex = (struct add_list *)_th_alloc(env->space,sizeof(struct add_list));
					ex->next = explanation;
					ex->e = ex1->e;
					explanation = ex;
skip1:
					ex1 = ex1->next;
				}
				m1 = m1->eq_merge;
			}
			*expl = explanation;
			//while (explanation) {
			//	printf("        %s\n", _th_print_exp(explanation->e));
			//	explanation = explanation->next;
			//}
#ifdef XX
			printf("node->e = %s\n", _th_print_exp(node->e));
			printf("rnode->e = %s\n", _th_print_exp(rnode->e));
            printf("Add ne failure %s\n", _th_print_exp(_ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_equal(env,_ex_real,_ex_intern_appl2_env(env,INTERN_RAT_PLUS,_th_left,_th_diff),_th_right))));
			while (explanation) {
				printf("    %s\n", _th_print_exp(explanation->e));
				explanation = explanation->next;
			}
			_th_display_difference_table(env);
			exit(1);
#endif
		}
		return 1;
	}

#ifdef XX
    edge = node->edges;
    while (edge) {
        if (!edge->delta && edge->target==rnode && edge->offset==_th_diff) {
            struct diff_edge *n = (struct diff_edge *)_th_alloc(env->space,sizeof(struct diff_edge));
            struct add_list *al;
            n->next = node->edges;
            node->edges = n;
            n->delta = 1;
            n->offset = edge->offset;
            n->source = edge->source;
            n->target = edge->target;
            n->source_next = edge->target->source_edges;
            edge->target->source_edges = n;
            al = (struct add_list *)_th_alloc(env->space,sizeof(struct add_list));
            al->next = edge->explanation;
            n->explanation = al;
            if (_th_diff->u.rational.numerator[0]==1 && _th_diff->u.rational.numerator[1]==0) {
                al->e = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_EQUAL,_th_left,_th_right));
            } else {
                al->e = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_EQUAL,_ex_intern_appl2_env(env,INTERN_RAT_PLUS,_th_left,_th_diff),_th_right));
            }
            goto cont;
        }
        edge = edge->next;
    }
#endif

    offset = _th_subtract_rationals(_th_diff,offset);
	ne = m1->ne_list;
	while (ne) {
		if (ne->target==m2 && ne->offset==offset) goto skip;
		ne = ne->next;
	}
	ne = (struct ne_list *)_th_alloc(env->space,sizeof(struct ne_list));
    ne->next = m1->ne_list;
    m1->ne_list = ne;
    ne->target = m2;
    ne->offset = offset;
	ne->orig_offset = _th_diff;
	ne->orig_source = node;
	ne->e = explanation;
	if (m1==node) {
		ne->orig_source = NULL;
		ne->orig_offset = NULL;
	}
skip:
#ifdef XX
cont:
    _th_diff = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(_th_diff->u.rational.numerator)),
        _th_diff->u.rational.denominator);

    edge = rnode->edges;
    while (edge) {
        if (!edge->delta && edge->target==node && edge->offset==_th_diff) {
            struct diff_edge *n = (struct diff_edge *)_th_alloc(env->space,sizeof(struct diff_edge));
            struct add_list *al;
            n->next = rnode->edges;
            rnode->edges = n;
            n->delta = 1;
            n->offset = edge->offset;
            n->source = edge->source;
            n->target = edge->target;
            n->source_next = edge->target->source_edges;
            edge->target->source_edges = n;
            al = (struct add_list *)_th_alloc(env->space,sizeof(struct add_list));
            al->next = edge->explanation;
            n->explanation = al;
            if (_th_diff->u.rational.numerator[0]==1 && _th_diff->u.rational.numerator[1]==0) {
                al->e = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_EQUAL,_th_left,_th_right));
            } else {
                al->e = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_EQUAL,_ex_intern_appl2_env(env,INTERN_RAT_PLUS,_th_right,_th_diff),_th_left));
            }
            goto cont1;
        }
        edge = edge->next;
    }

    ne = (struct ne_list *)_th_alloc(env->space,sizeof(struct ne_list));
    ne->next = rnode->ne_list;
    rnode->ne_list = ne;
    ne->target = node;
    ne->offset = _th_diff;
	ne->orig_source = NULL;
	ne->orig_offset = NULL;
	ne->e = explanation;
cont1:;
#endif
    return 0;
}

static struct add_list *explanation;

static struct add_list *collect_right(struct env *env, struct diff_node *node, struct add_list *tail)
{
    struct add_list *n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
    struct diff_edge *e;

    if (node->visited) return tail;

    n->next = tail;
    n->e = node->e;
    if (n->e==NULL) {
        fprintf(stderr, "Null expression 1\n");
        exit(1);
    }
    node->visited = 1;

    e = node->edges;
    while (e) {
        n = collect_right(env, e->target, n);
        e = e->next;
    }

    return n;
}

static struct add_list *collect_left(struct env *env, struct diff_node *node, struct add_list *tail)
{
    struct add_list *n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
    struct diff_edge *e;

    if (node->visited) return tail;
    node->visited = 1;

    n->next = tail;
    n->e = node->e;
    if (n->e==NULL) {
        fprintf(stderr, "Null expression 2\n");
        exit(1);
    }
    e = node->source_edges;
    while (e) {
        n = collect_left(env, e->source, n);
        e = e->source_next;
    }

    return n;
}

static struct _ex_intern *user2_trail = NULL;

struct add_list *_th_collect_impacted_terms(struct env *env, struct _ex_intern *e)
{
    int i;
    struct diff_node *node, *rnode;
    struct add_list *res, *l, *l2, *l3, *l4, *r;
    int hash;
    int rhash;

    if (!env->diff_node_table) return NULL;

    if (!_th_extract_relationship(env,e)) return NULL;
    //if (_th_is_equal_term) return NULL;

    hash = (((int)_th_left)/4)%DIFF_NODE_HASH;
    rhash = (((int)_th_right)/4)%DIFF_NODE_HASH;

    for (i = 0; i < DIFF_NODE_HASH; ++i) {
        node = env->diff_node_table[i];
        while (node) {
            node->visited = 0;
            node = node->next;
        }
    }

    _zone_print1("Hash %d", hash);
    _zone_print1("RHash %d", rhash);
    _zone_print_exp("left", _th_left);
    _zone_print_exp("right", _th_right);

    node = env->diff_node_table[hash];
    rnode = env->diff_node_table[rhash];
    while (node && node->e != _th_left) node = node->next;
    while (rnode && rnode->e != _th_right) rnode = rnode->next;

    l = NULL;
    if (rnode) l = collect_right(env, rnode, l);
    for (i = 0; i < DIFF_NODE_HASH; ++i) {
        struct diff_node *node = env->diff_node_table[i];
        while (node) {
            node->visited = 0;
            node = node->next;
        }
    }
    if (node) l = collect_left(env, node, l);
    for (i = 0; i < DIFF_NODE_HASH; ++i) {
        node = env->diff_node_table[i];
        while (node) {
            node->visited = 0;
            node = node->next;
        }
    }

    user2_trail = _ex_true;
    _ex_true->user2 = NULL;

    res = NULL;
    while (l != NULL) {
        //_zone_print_exp("Collecting for term", l->e);
        if (!l->e->user2) {
            l->e->user2 = user2_trail;
            user2_trail = l->e;
            l2 = l->e->used_in;
            while (l2) {
                if (!l2->e->user2) {
                    l2->e->user2 = user2_trail;
                    user2_trail = l2->e;
                    if (l2->e->type==EXP_APPL && (l2->e->u.appl.functor==INTERN_RAT_LESS || l2->e->u.appl.functor==INTERN_EQUAL)) {
                        r = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                        r->next = res;
                        res = r;
                        res->e = l2->e;
                    }
                    if (l2->e->type==EXP_APPL && (l2->e->u.appl.functor==INTERN_RAT_PLUS || l2->e->u.appl.functor==INTERN_RAT_TIMES)) {
                        l3 = l2->e->used_in;
                        while (l3) {
                            if (!l3->e->user2) {
                                l3->e->user2 = user2_trail;
                                user2_trail = l3->e;
                                if (l3->e->type==EXP_APPL && (l3->e->u.appl.functor==INTERN_RAT_LESS || l3->e->u.appl.functor==INTERN_EQUAL)) {
                                    r = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                                    r->next = res;
                                    res = r;
                                    res->e = l3->e;
                                }
                                if (l3->e->type==EXP_APPL && l3->e->u.appl.functor==INTERN_RAT_PLUS) {
                                    l4 = l3->e->used_in;
                                    while (l4) {
                                        if (!l4->e->user2) {
                                            l4->e->user2 = user2_trail;
                                            user2_trail = l4->e;
                                            if (l4->e->type==EXP_APPL && (l4->e->u.appl.functor==INTERN_RAT_LESS || l4->e->u.appl.functor==INTERN_EQUAL)) {
                                                r = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                                                r->next = res;
                                                res = r;
                                                res->e = l4->e;
                                            }
                                        }
                                        l4 = l4->next;
                                    }
                                }
                            }
                            l3 = l3->next;
                        }
                    }
                }
                l2 = l2->next;
            }
        }
        l = l->next;
    }
    while (user2_trail) {
        struct _ex_intern *n = user2_trail->user2;
        user2_trail->user2 = NULL;
        user2_trail = n;
    }
    return res;
}

int check_for_fill(struct env *env, struct add_list **expl)
{
    struct _ex_intern *small;
    struct _ex_intern *large;
    struct _ex_intern *pos;
    struct add_list *smalle, *largee;
    int hash = (((int)_th_left)/4)%DIFF_NODE_HASH;
    int rhash = (((int)_th_right)/4)%DIFF_NODE_HASH;
    struct diff_node *node = env->diff_node_table[hash];
    struct diff_node *rnode = env->diff_node_table[rhash];
    struct diff_edge *edge;
    struct ne_list *ne;
    static struct _ex_intern *one = NULL;
    struct add_list *n;

    if (one==NULL) one = _ex_intern_small_rational(1,1);

    //char *mark = _th_alloc_mark(REWRITE_SPACE);

    //check_integrity(env, "begin add_inequality");

    //printf("Checking fill %s and", _th_print_exp(_th_left));
    //printf(" %s\n", _th_print_exp(_th_right));

    while (node && node->e != _th_left) node = node->next;
    while (rnode && rnode->e != _th_right) rnode = rnode->next;

    //printf("Nodes %x %x\n", node, rnode);

    if (node==NULL || rnode==NULL) return 0;

    small = large = NULL;

    edge = node->edges;
    while (edge) {
        if (edge->target==rnode) {
            if (small==NULL || _th_rational_less(edge->offset,small)) {
                small = edge->offset;
                smalle = edge->explanation;
            }
            if (small==edge->offset && edge->delta) {
                small = _th_add_rationals(small,one);
                smalle = edge->explanation;
            }
        }
        edge = edge->next;
    }

    edge = rnode->edges;
    while (edge) {
        if (edge->target==node) {
            struct _ex_intern *ro
                         = _ex_intern_rational(_th_big_copy(REWRITE_SPACE,_th_complement(edge->offset->u.rational.numerator)),
                                                            edge->offset->u.rational.denominator);
            if (large==NULL || _th_rational_less(large,ro)) {
                large = ro;
                largee = edge->explanation;
            }
            if (large==ro && edge->delta) {
                large = _th_subtract_rationals(large,one);
                largee = edge->explanation;
            }
        }
        edge = edge->source_next;
    }

    //printf("Small %s\n", _th_print_exp(small));
    //printf("Large %s\n", _th_print_exp(large));

    if (small==NULL || large==NULL) return 0;

    pos = small;
    while (!_th_rational_less(large,pos)) {
        ne = node->ne_list;
        //printf("Checking %s\n", _th_print_exp(pos));
        while (ne) {
            if (ne->offset==pos && ne->target==rnode) goto cont;
            ne = ne->next;
        }
        return 0;
cont:
        pos = _th_add_rationals(pos,one);
    }

    //printf("Good\n");

    *expl = NULL;

    while (largee) {
        n = *expl;
        while (n) {
            if (n->e== (*expl)->e) goto cont1;
            n = n->next;
        }
        n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        n->next = *expl;
        *expl = n;
        n->e = largee->e;
cont1:
        largee = largee->next;
    }
    while (smalle) {
        n = *expl;
        while (n) {
            if (n->e== (*expl)->e) goto cont2;
            n = n->next;
        }
        n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        n->next = *expl;
        *expl = n;
        n->e = smalle->e;
cont2:
        smalle = smalle->next;
    }
    pos = small;
    while (!_th_rational_less(large,pos)) {
        n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        n->next = *expl;
        *expl = n;
        n->e = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_EQUAL,_ex_intern_appl2_env(env,INTERN_RAT_PLUS,node->e,pos),rnode->e));
        pos = _th_add_rationals(pos,one);
    }
    return 1;
}

#ifdef PRINT1
struct _ex_intern *add_left, *add_right, *add_e;
#endif

static int add_rless_term(struct env *env, struct _ex_intern *e)
{
    int res = 0;
    struct add_list *al;
    struct _ex_intern *r;

    //check_integrity(env, "begin add_rless_term");
    //printf("Adding %s\n", _th_print_exp(e));
    _zone_print_exp("Add rless", e);

    if (!env->diff_node_table) return 0;

	//if (_th_check_cycle_rless(env,e,&al)==_ex_false) {
	//	res = 1 / res;
	//}

	r = _th_check_cycle_rless(env,e,&al);
	if (r==_ex_false) {
		return 1;
	}

    if (!_th_extract_relationship(env,e)) return 0;

#ifdef PRINT1
	add_e = e;
	add_left = _th_left;
	add_right = _th_right;
#endif

    if (_th_is_equal_term) _th_delta = 0;

	//if (explanation = check_for_contradiction(env)) return 1;

    //if (is_equal) {
    //    fprintf(stderr, "Adding equal term\n");
    //    exit(1);
    //}

    //_th_print_difference_table(env);

    //printf("    left %s\n", _th_print_exp(_th_left));
    //printf("    right %s\n", _th_print_exp(_th_right));
    //printf("    diff %s\n", _th_print_exp(_th_diff));
    //printf("    delta %d\n", _th_delta);
    _tree_indent();
    _zone_print_exp("left", _th_left);
    _zone_print_exp("right", _th_right);
    _zone_print_exp("diff", _th_diff);
    _zone_print1("delta %d", _th_delta);
    _zone_print1("is_equal_term %d", _th_is_equal_term);

#ifndef FAST
    //if (_zone_active()) _th_print_difference_table(env);
#endif
    if (_th_is_equal_term==-1) {
        res = add_not_equal(env,e,&explanation);
    } else if (_th_is_equal_term==0) {
		explanation = _th_prepare_quick_implications(env,e);
		printf("explanation = %x\n", explanation);
		if (explanation) {
			al = explanation;
			while (al) {
				printf("    %s\n", _th_print_exp(al->e));
				al = al->next;
			}
			_tree_undent();
			return 1;
		}
        res = add_inequality(env,e,&explanation);
    } else {
		explanation = _th_prepare_quick_implications(env,e);
		printf("equal left %s\n", _th_print_exp(_th_left));
		printf("equal right %s\n", _th_print_exp(_th_right));
		printf("equal diff %s\n", _th_print_exp(_th_diff));
		printf("explanation = %x\n", explanation);
		if (explanation) {
			al = explanation;
			while (al) {
				printf("    %s\n", _th_print_exp(al->e));
				al = al->next;
			}
			_tree_undent();
			return 1;
		}
		res = _th_add_reduction(env,e,_th_right,_th_left,_th_diff,&explanation);
#ifdef XX
		struct _ex_intern *l = e->u.appl.args[0];
        struct _ex_intern *r = e->u.appl.args[1];
		struct _ex_intern *o = NULL;
        if (l->type==EXP_APPL && l->u.appl.functor==INTERN_RAT_PLUS) {
            struct _ex_intern *x = l;
            l = r;
            r = x;
            _zone_print0("Switch");
        }
		o = NULL;
	    if (r->type==EXP_APPL && r->u.appl.functor==INTERN_RAT_PLUS && r->u.appl.count==2) {
		    if (r->u.appl.args[0]->type==EXP_RATIONAL) {
			    o = r->u.appl.args[0];
				r = r->u.appl.args[1];
			} else if (r->u.appl.args[1]->type==EXP_RATIONAL) {
				o = r->u.appl.args[1];
				r = r->u.appl.args[0];
			} else {
				res = 0;
			}
		}
		if (_th_term_compare(env,l,r)>0) {
			struct _ex_intern *x = l;
			l = r;
			r = x;
			if (o) o = _ex_intern_rational(_th_complement(o->u.rational.numerator),o->u.rational.denominator);
		}
		printf("Reducing %s\n", _th_print_exp(l));
		printf("    to %s\n", _th_print_exp(r));
        res = _th_add_reduction(env,l,r,o,&explanation);
#endif
	}
#ifndef FAST
    //if (_zone_active()) _th_print_difference_table(env);
#endif

    //check_integrity(env, "end add_rless_term");
    _tree_undent();

    //if (_th_is_integer_logic() && check_for_fill(env,&explanation)) {
    //    res = 1;
    //}

#ifdef XX
	if (!res) {
		//struct add_list *ex;
		explanation = _th_prepare_quick_implications(env,e);
		//while (ex) {
		//	printf("   expl %s\n", _th_print_exp(ex->e));
		//	ex = ex->next;
		//}
		if (explanation) return 1;
	}
#endif

    return res;
}

void check_cycle(struct env *env, char *pos)
{
    struct cache_info *c = env->head;

    while (c) {
        if (c==c->next) {
            fprintf(stderr, "env->head cycle: %s\n", pos);
            exit(1);
        }
        c = c->next;
    }
}

//static struct _ex_intern *x = NULL;
//static struct _ex_intern *y = NULL;

//static struct _ex_intern *mt = NULL;

//static struct add_list *mt_explan = NULL;
//static struct _ex_intern *mt_explan_e = NULL;

//void check_mt()
//{
//    if (mt_explan) {
//        if (mt_explan->e != mt_explan_e) {
//            fprintf(stderr, "Explanation changed\n");
//            exit(1);
//        }
//    }
//}

void has_false_cycle()
{
    struct _ex_intern *e = _ex_false;

    while (e->merge) {
        e = e->merge;
        if (e==_ex_false) {
            fprintf(stderr, "Has false cycle\n");
            exit(1);
        }
    }
}

void check_invalid_merge()
{
    static struct _ex_intern *x = NULL;
    struct _ex_intern *e;

#ifndef FAST
    if (x==NULL && _tree_zone >= 60000) x = _th_parse(_th_get_learn_env(),"(rless x_50 x_46)");
#endif
    if (x==NULL) return;

    e = x;
    while (e && e->merge) e = e->merge;

    if (e==_ex_false) {
        e = x;
        while (e && e->find && e != e->find) e = e->find;
        if (e != _ex_false) {
            fprintf(stderr, "Illegal find construction\n");
            exit(1);
        }
    }
}

//struct _ex_intern *ft = NULL, *ft2 = NULL;

void _th_add_merge_explanation(struct env *env, struct _ex_intern *term, struct _ex_intern *merge, struct add_list *explanation)
{
    struct cache_info *n = (struct cache_info *)_th_alloc(env->space,sizeof(struct cache_info));
    //struct add_list *a;
#ifndef FAST
    struct add_list *el;
#endif

#ifndef FAST
    if (merge==term && (merge->type != EXP_APPL || (merge->u.appl.functor != INTERN_AND && merge->u.appl.functor != INTERN_OR && merge->u.appl.functor != INTERN_NOT && merge->u.appl.functor != INTERN_ITE))) {
        fprintf(stderr, "Illegal merge\n");
        exit(1);
    }
#endif

    //if (ft==NULL) {
    //    ft = _th_parse(env, "(== (rplus #-1/1 x_93) x_91)");
    //}
    //if (env != _th_get_learn_env() && term==ft) {
    //if (_tree_zone > 60600) {
    //    printf("%d,%d: Merging %s the value", _tree_zone, _tree_count, _th_print_exp(term));
    //    printf(" %s\n", _th_print_exp(merge));
    //}
    //a = explanation;
    //while (a) {
    //    if (a->e->type==EXP_APPL && a->e->u.appl.functor==INTERN_EQUAL &&
    //        a->e->u.appl.args[0]->type==EXP_APPL && a->e->u.appl.args[0]->u.appl.functor==INTERN_RAT_PLUS &&
    //        a->e->u.appl.args[1]->type==EXP_APPL && a->e->u.appl.args[1]->u.appl.functor==INTERN_RAT_PLUS) {
    //        printf("%d,%d: (double rplus) Merging %s the value", _tree_zone, _tree_count, _th_print_exp(term));
    //        printf(" %s\n", _th_print_exp(merge));
    //    }
    //    a = a->next;
    //}
#ifdef CHECK_FOR_MERGE_CYCLE
    struct _ex_intern *m = merge;
    while (m) {
        if (m==term) {
            fprintf(stderr, "Adding merge cycle\n");
            fprintf(stderr, "    %s\n", _th_print_exp(term));
            fprintf(stderr, "    %s\n", _th_print_exp(merge));
            exit(1);
        }
        m = m->merge;
    }
#endif

#ifndef FAST
    el = explanation;
	while(el) {
#ifdef XX
		struct _ex_intern *f1, *f2;
		if (el->e->type==EXP_APPL && el->e->u.appl.functor==INTERN_EQUAL) {
			f1 = el->e->u.appl.args[0];
			f2 = el->e->u.appl.args[1];
		} else if (el->e->type==EXP_APPL && el->e->u.appl.functor==INTERN_NOT) {
			f1 = el->e->u.appl.args[0];
			f2 = _ex_false;
		} else {
			f1 = el->e;
			f2 = _ex_true;
		}
    	while (f1->find != NULL && f1->find != f1) f1 = f1->find;
    	while (f2->find != NULL && f2->find != f2) f2 = f2->find;
		if (f1 != f2) {
			int i = 0;
			fprintf(stderr, "Illegal explanation being added %s\n", _th_print_exp(el->e));
			fprintf(stderr, "    %s\n", _th_print_exp(f1));
			fprintf(stderr, "    %s\n", _th_print_exp(f2));
			fprintf(stderr, "for %s to", _th_print_exp(term));
			fprintf(stderr, " %s\n", _th_print_exp(merge));
			i = 1/i;
		}
#endif
		if (el->e==NULL) {
			int i = 0;
			fprintf(stderr, "Adding illegal explanation for %s", _th_print_exp(term));
			fprintf(stderr, " to %s\n", _th_print_exp(merge));
			el = explanation;
			while (el) {
				fprintf(stderr, "    %s\n", _th_print_exp(el->e));
				el = el->next;
			}
			i = 1 / i;
			exit(1);
		}
		el = el->next;
	}
#endif

#ifdef CHECK_CACHE
    if (!env->cache_installed) {
        struct add_list *expl;
        fprintf(stderr, "_th_add_merge_explanation: Cache not installed\n");
        fprintf(stderr, "    term = %s\n", _th_print_exp(term));
        fprintf(stderr, "    merge = %s\n", _th_print_exp(merge));
        expl = explanation;
        while (expl) {
            printf("        %s\n", _th_print_exp(expl->e));
            expl = expl->next;
        }
        exit(1);
    }
#endif

    if (merge==_ex_true && (term->type != EXP_APPL || (term->u.appl.functor != INTERN_EQUAL && term->u.appl.functor != INTERN_NOT))) {
        struct add_list *a = explanation;
        while (a) {
            if (a->e==term) {
                fprintf(stderr, "Error: term in explanation %s\n", _th_print_exp(term));
                exit(1);
            }
            a = a->next;
        }
    }

    //if (mt==NULL) {
    //    mt = _th_parse(env, "(not (== x_41 x_55))");
    //}

    //if (term==mt /*&& env == _th_get_learn_env()*/) {
    //    _zone_print_exp("Merging", term);
    //    _zone_print_exp("and", merge);
    //    printf("add_merge_explanation %d %d %x %s", _tree_zone, _tree_count, env, _th_print_exp(term));
    //    printf(" %s\n", _th_print_exp(merge));
    //    printf("     explanation %x\n", explanation);
    //    printf("     exp %x\n", explanation->e);
    //    fflush(stdout);
    //    a = explanation;
    //    while (a) {
    //        printf("    %s\n", _th_print_exp(a->e));
    //        a = a->next;
    //    }
    //    mt_explan = explanation;
    //    mt_explan_e = explanation->e;
    //}

    //if (x==NULL) {
    //    x = _th_parse(env,"(f2 c_2)");
    //    y = _th_parse(env,"(f2 c_0)");
    //}

    //_zone_print_exp("add_me", term);
    //_zone_print_exp("and", merge);

    //if ((term==x && merge==y) || (term==y && merge==x)) {
    //    struct add_list *expl = explanation;
    //    printf("Merge trap %x %d\n", env, _tree_zone);
    //    _zone_print0("*** MERGE TRAP ***");
    //    while (expl) {
    //        printf("    %s\n", _th_print_exp(expl->e));
    //        expl = expl->next;
    //    }
        //if (env != 0x2e2594 && _tree_zone > 479000) exit(1);
    //}

    if (env->head==NULL) {
        env->head = env->tail = n;
        n->next = n->prev = NULL;
    } else {
        n->next = env->head;
        env->head->prev = n;
        n->prev = NULL;
        env->head = n;
    }
    n->value = n->old_value = term->rewrite;
    n->find = n->old_find = term->find;
    n->old_line = n->line = term->cache_line;
    n->old_merge = term->merge;
    n->old_explanation = term->explanation;
    n->merge = term->merge = merge;
    n->original = n->old_original = term->original;
    n->explanation = term->explanation = explanation;
    n->term = term;
    n->bad = (term->cache_bad?3:0);
    n->sig = n->old_sig = term->sig;
    if (term->in_hash) {
        n->in_hash = 3;
    } else {
        n->in_hash = 0;
    }
}

static struct _ex_intern *t1, *t2;

void check_terms()
{
    if (t1==NULL) {
        struct env *env = _th_get_learn_env();
        if (env==NULL) return;
        t1 = _th_parse(env, "x_64");
        t2 = _th_parse(env, "(== x_64 x_50)");
    }

    if (t2 && t2->in_hash) {
        struct add_list *l = t1->used_in;
        while (l) {
            if (l->e==t2) return;
            l = l->next;
        }
        fprintf(stderr, "(== x_64 x_50) not properly hashed\n");
        exit(1);
    }
}

void check_x53()
{
    static struct _ex_intern *e = NULL;

    if (e==NULL) e = _ex_intern_var(_th_intern("x_53"));

    if (e->original && e->original->type==0) {
        fprintf(stderr, "Illegal original\n");
        exit(1);
    }
}

void check_learn_env()
{
    static struct env *env = NULL;
    struct cache_info *info;

    if (env==NULL) env = _th_get_learn_env();

    if (env==NULL) return;

#ifndef FAST
    if (_tree_zone < 323219) return;
#endif

    info = env->tail;

    while (info) {
        if (((int)info)==0x5ef2794 && _th_check_alloc_block(env->space,(char *)info)) {
            fprintf(stderr, "Error: block %x not valid\n", info);
            exit(1);
        }
        if (((int)info->term)&3) {
            fprintf(stderr, "Error in learn env %x %x %x\n", info, info->next, info->term);
            exit(1);
        }
        info = info->prev;
    }
}

void check_explanations(struct env *nenv)
{
    static struct env *env = NULL;
    //struct cache_info *info;
    struct add_list *l;
    static struct _ex_intern *exp = NULL;

    if (nenv) env = nenv;

    if (env==NULL) return;

    if (exp==NULL) exp = _th_parse(env, "(rless #2/1 (rplus (rtimes #-1/1 cvclZero) x_6))");

    l = exp->explanation;
    while (l) {
        if (((int)l)&3) {
            fprintf(stderr, "Error in explanation for %s\n", _th_print_exp(exp));
            exit(1);
        }
        l = l->next;
    }

#ifdef XX
    info = env->head;
    while (info) {
        if (info->explanation != info->old_explanation) {
            l = info->explanation;
            while (l) {
                if (((int)l)&3) {
                    fprintf(stderr, "Error in explanation for %s\n", _th_print_exp(info->term));
                    exit(1);
                }
                l = l->next;
            }
        }
        info = info->next;
    }
#endif
}

void _th_add_cache_assignment(struct env *env, struct _ex_intern *term, struct _ex_intern *val)
{
    struct cache_info *n = (struct cache_info *)_th_alloc(env->space,sizeof(struct cache_info));

#ifdef CHECK_CACHE
    if (!env->cache_installed) {
        fprintf(stderr, "_th_add_cache_assignment: Cache not installed\n");
        fprintf(stderr, "    term = %s\n", _th_print_exp(term));
        fprintf(stderr, "    val = %s\n", _th_print_exp(val));
        exit(1);
    }
#endif
    //if (term->rewrite==_ex_false) {
    //    printf("Assigning to false\n");
    //    exit(1);
    //}
    //printf("Adding %d %s\n", _tree_zone, _th_print_exp(term));
    //printf("val %s\n", _th_print_exp(val));
    //struct add_list *a;

    //if (term->type==EXP_VAR && val->type != EXP_VAR && _th_is_free_in(val, term->u.var)) {
    //    printf("Recursive var assignment %s %s\n", _th_intern_decode(term->u.var), _th_print_exp(val));
    //    exit(1);
    //}
    //check_cycle(env, "add_cache_assignment");
#ifdef XX
    static unsigned c0 = 0, c1, p1;

    if (c0==0) {
        c0 = _th_intern("c_0");
        c1 = _th_intern("c_1");
        p1 = _th_intern("p1");
    }

    if (in_learn &&
        term->type==EXP_APPL && term->u.appl.functor==p1 &&
        term->u.appl.args[0]->type==EXP_VAR &&
        term->u.appl.args[0]->u.var==c1 &&
        term->u.appl.args[1]->type==EXP_VAR &&
        term->u.appl.args[1]->u.var==c0) {
        fprintf(stderr, "Assigning %s = ", _th_print_exp(term));
        fprintf(stderr, "%s\n", _th_print_exp(val));
        exit(1);
    }
#endif
    if (env->head==NULL) {
        env->head = env->tail = n;
        n->next = n->prev = NULL;
    } else {
        n->next = env->head;
        env->head->prev = n;
        n->prev = NULL;
        env->head = n;
    }
    n->value = val;
    n->old_line = term->cache_line;
#ifndef FAST
    n->line = term->cache_line = _tree_count;
#else
    n->line = 0;
#endif
    n->old_value = term->rewrite;
    n->find = n->old_find = term->find;
    n->original = n->old_original = term->original;
    n->merge = n->old_merge = term->merge;
    n->explanation = n->old_explanation = term->explanation;
    //if (term->rewrite == _ex_false && val != _ex_false) {
    //    fprintf(stderr, "Overwriting false in %s\n", _th_print_exp(term));
    //    fprintf(stderr, "val = %s\n", _th_print_exp(val));
    //    fprintf(stderr, "cache bad = %d\n", term->cache_bad);
    //    exit(1);
    //}
    term->rewrite = val;
    n->term = term;
    if (val != NULL && val != term) {
        _ex_delete_term(term);
    } else if (term->find==term) {
        _ex_add_term(term);
    }
    //a = (struct add_list *)_th_alloc(env->space,sizeof(struct add_list));
    //a->next = val->cached_in;
    //val->cached_in = a;
    //a->e = term;
    n->bad = (term->cache_bad?1:0);
    n->sig = n->old_sig = term->sig;
    if (term->in_hash) {
        n->in_hash = 3;
    } else {
        n->in_hash = 0;
    }
    term->cache_bad = 0;

    //if (term->type==EXP_APPL && !strcmp(_th_intern_decode(term->u.appl.functor),"p2")) {
    //    printf("%d: Adding cache assignment %s ->", _tree_zone, _th_print_exp(term));
    //    printf(" %s\n", _th_print_exp(val));
    //}
    //if (term==_ex_false && val==_ex_true) exit(1);
}

//static struct _ex_intern *rl1 = NULL;

void _th_add_signature(struct env *env, struct _ex_intern *term, struct _ex_intern *sig)
{
    struct cache_info *n = (struct cache_info *)_th_alloc(env->space,sizeof(struct cache_info));

#ifdef CHECK_CACHE
    if (!env->cache_installed) {
        fprintf(stderr, "_th_add_signature: Cache not installed\n");
        fprintf(stderr, "    term = %s\n", _th_print_exp(term));
        fprintf(stderr, "    sig = %s\n", _th_print_exp(sig));
        exit(1);
    }
#endif
    //if (rl1==NULL) rl1 = _th_parse(env,"(rless x_92 x_88)");

    //if (term==rl1) {
    //    if (env==_th_get_learn_env()) {
    //        printf("In learn env\n");
    //    } else {
    //        printf("In normal env\n");
    //    }
    //    printf("%d: signature %s\n", _tree_zone, _th_print_exp(term));
    //    printf("    is %s\n", _th_print_exp(sig));
    //    if (sig==_ex_false) exit(1);
    //}

    if (env->head==NULL) {
        env->head = env->tail = n;
        n->next = n->prev = NULL;
    } else {
        n->next = env->head;
        env->head->prev = n;
        n->prev = NULL;
        env->head = n;
    }
    n->old_line = n->line = term->cache_line;
    n->value = n->old_value = term->rewrite;
    n->old_sig = term->sig;
    n->find = n->old_find = term->find;
    n->sig = term->sig = sig;
    n->merge = n->old_merge = term->merge;
    n->original = n->old_original = term->original;
    n->explanation = n->old_explanation = term->explanation;
    n->term = term;
    n->bad = (term->cache_bad?3:0);
    if (term->in_hash) {
        n->in_hash = 3;
    } else {
        n->in_hash = 0;
    }
}

//#define CHECK_MERGE

void _th_add_find(struct env *env, struct _ex_intern *term, struct _ex_intern *find)
{
    struct cache_info *n = (struct cache_info *)_th_alloc(env->space,sizeof(struct cache_info));

#ifdef CHECK_MERGE
    struct _ex_intern *t = term;
    struct _ex_intern *f = find;

    while (t->merge) t = t->merge;
    while (f->merge) f = f->merge;
    if (t != f) {
        fprintf(stderr, "Merge error\n");
        fprintf(stderr,"term = %s\n", _th_print_exp(term));
        fprintf(stderr,"find = %s\n", _th_print_exp(find));
        fprintf(stderr,"t = %s\n", _th_print_exp(t));
        fprintf(stderr,"f = %s\n", _th_print_exp(f));
        exit(1);
    }
#endif

#ifdef CHECK_CACHE
    if (!env->cache_installed) {
        fprintf(stderr, "_th_add_find: Cache not installed\n");
        fprintf(stderr, "    term = %s\n", _th_print_exp(term));
        fprintf(stderr, "    find = %s\n", _th_print_exp(find));
        exit(1);
    }
#endif
    //if (ft==NULL) {
    //    ft = _th_parse(env, "(== (rplus #-1/1 x_93) x_91)");
    //}
    //if (env != _th_get_learn_env() && term==ft) {
    //if (_tree_zone > 60600) {
    //    printf("%d,%d: Assigning %s the value", _tree_zone, _tree_count, _th_print_exp(term));
    //    printf(" %s\n", _th_print_exp(find));
    //}

    //if ((term->find==_ex_true || term->find==_ex_false || term->find->type==EXP_RATIONAL)) {
    //    fprintf(stderr, "Error: reassigning constant find of term %s\n", _th_print_exp(term));
    //    fprintf(stderr, "term->find: %s\n", _th_print_exp(term->find));
    //    fprintf(stderr, "find: %s\n", _th_print_exp(find));
    //    exit(1);
    //}
    //if (ft==NULL) {
    //    ft = _th_parse(env,"(== (rplus x_93 #1/1) x_69)");
    //    ft2 = _th_parse(env, "(== (rplus #-1/1 x_93) x_91)");
    //}

    //if (term==ft || term==ft2) {
    //    printf("%d: find %s to", _tree_zone, _th_print_exp(term));
    //    printf(" %s\n", _th_print_exp(find));
    //    if (term==ft2 && find==_ex_false && _tree_zone==1288798) {
    //        fprintf(stderr, "Illegal assignment\n");
    //        exit(1);
    //    }
    //}

    //if (_zone_active()) {
    //    _tree_print_exp("term", term);
    //    _tree_print_exp("find", find);
    //    if (term==_ex_false && find==_ex_true) {
    //        fprintf(stderr, "false finds true\n");
    //        exit(1);
    //    }
    //}
    //printf("%d: find %s\n", _tree_zone, _th_print_exp(term));
    //printf("    is %s\n", _th_print_exp(find));

    if (term->rewrite != term && term->rewrite != find && term->rewrite) {
        printf("Rewrite not to self %s\n", _th_print_exp(term->rewrite));
        printf("term = %s\n", _th_print_exp(term));
        exit(1);
    }
    //if (term->find==_ex_false) {
    //    printf("Assigning to false find\n");
    //    exit(1);
    //}
    if (env->head==NULL) {
        env->head = env->tail = n;
        n->next = n->prev = NULL;
    } else {
        n->next = env->head;
        env->head->prev = n;
        n->prev = NULL;
        env->head = n;
    }
    if (find != term) {
        _ex_delete_term(term);
    } else if (term->rewrite==NULL || term->rewrite==term) {
        _ex_add_term(term);
    }
    n->value = n->old_value = term->rewrite;
    n->old_line = n->line = term->cache_line;
    n->old_sig = term->sig;
    n->old_find = term->find;
    n->find = term->find = find;
    n->sig = n->old_sig = term->sig;
    n->merge = n->old_merge = term->merge;
    n->original = n->old_original = term->original;
    n->explanation = n->old_explanation = term->explanation;
    n->term = term;
    n->bad = (term->cache_bad?3:0);
    if (term->in_hash) {
        n->in_hash = 3;
    } else {
        n->in_hash = 0;
    }
}

void _th_add_original(struct env *env, struct _ex_intern *term, struct _ex_intern *original)
{
    struct cache_info *n = (struct cache_info *)_th_alloc(env->space,sizeof(struct cache_info));

#ifdef CHECK_CACHE
    if (!env->cache_installed) {
        fprintf(stderr, "_th_add_original: Cache not installed\n");
        fprintf(stderr, "    term = %s\n", _th_print_exp(term));
        fprintf(stderr, "    original = %s\n", _th_print_exp(original));
        exit(1);
    }
#endif
    //printf("%d: add original %s\n", _tree_zone, _th_print_exp(term));
    //printf("    is %s\n", _th_print_exp(original));

    //if (term->find==_ex_false) {
    //    printf("Assigning to false find\n");
    //    exit(1);
    //}
    if (env->head==NULL) {
        env->head = env->tail = n;
        n->next = n->prev = NULL;
    } else {
        n->next = env->head;
        env->head->prev = n;
        n->prev = NULL;
        env->head = n;
    }
    n->value = n->old_value = term->rewrite;
    n->old_line = n->line = term->cache_line;
    n->old_sig = term->sig;
    n->find = n->old_find = term->find;
    n->old_original = term->original;
    n->original = term->original = original;
    n->sig = n->old_sig = term->sig;
    n->merge = n->old_merge = term->merge;
    n->explanation = n->old_explanation = term->explanation;
    n->term = term;
    n->bad = (term->cache_bad?3:0);
    if (term->in_hash) {
        n->in_hash = 3;
    } else {
        n->in_hash = 0;
    }
}

void _th_mark_bad(struct env *env, struct _ex_intern *term)
{
    struct cache_info *n = (struct cache_info *)_th_alloc(env->space,sizeof(struct cache_info));
    //struct add_list *a;

#ifdef CHECK_CACHE
    if (!env->cache_installed) {
        fprintf(stderr, "_th_mark_bad: Cache not installed\n");
        fprintf(stderr, "    term = %s\n", _th_print_exp(term));
        exit(1);
    }
#endif

    if (term->cache_bad) return;

    //check_cycle(env, "mark_bad");

    //printf("n = %x\nenv->head = %x\n", n, env->head);

    if (env->head==NULL) {
        env->head = env->tail = n;
        n->next = n->prev = NULL;
    } else {
        n->next = env->head;
        env->head->prev = n;
        n->prev = NULL;
        env->head = n;
    }
    n->value = n->old_value = term->rewrite;
    n->old_line = n->line = term->cache_line;
    n->sig = n->old_sig = term->sig;
    n->find = n->old_find = term->find;
    n->original = n->old_original = term->original;
    n->merge = n->old_merge = term->merge;
    n->explanation = n->old_explanation = term->explanation;
    //if (term->rewrite == _ex_false) {
    //    fprintf(stderr, "Overwriting false in %s\n", _th_print_exp(term));
    //    exit(1);
    //}
    n->term = term;
    n->bad = (term->cache_bad?3:2);
    n->in_hash = (term->in_hash?3:0);
    term->cache_bad = 1;
    if (term->find != term) _ex_add_term(term);
    //if (term->type==EXP_APPL && !strcmp(_th_intern_decode(term->u.appl.functor),"p2")) {
    //    printf("%d: Marking bad %s => ", _tree_zone, _th_print_exp(term));
    //    printf("%s\n", _th_print_exp(term->rewrite));
    //}
}

int hack_check = 0;
struct _ex_intern *hack_exp = NULL;
struct env *hack_env = NULL;
int do_hack_check = 1;

void the_hack_check()
{
    if (do_hack_check && hack_check) {
        if (!hack_exp->in_hash) {
            fprintf(stderr, "%s not in hash (hack check)\n", _th_print_exp(hack_exp));
            exit(1);
        }
    }
}

void _th_mark_inhash(struct env *env, struct _ex_intern *term)
{
    struct cache_info *n = (struct cache_info *)_th_alloc(env->space,sizeof(struct cache_info));

#ifdef CHECK_CACHE
    if (!env->cache_installed) {
        fprintf(stderr, "_th_mark_inhash: Cache not installed\n");
        fprintf(stderr, "    term = %s\n", _th_print_exp(term));
        exit(1);
    }
#endif

    //if (hack_exp==NULL) {
    //    hack_exp = _th_parse(env, "(rless x_9 cvclZero)");
    //}
    //if (hack_exp==term) {
    //    printf("STARTING HACK CHECK %x\n", env);
    //    hack_env = env;
    //    hack_check = 1;
    //}

    if (term->in_hash) return;

    //printf("Marking in hash %d %s\n", _tree_zone, _th_print_exp(term));

    if (env->head==NULL) {
        env->head = env->tail = n;
        n->next = n->prev = NULL;
    } else {
        n->next = env->head;
        env->head->prev = n;
        n->prev = NULL;
        env->head = n;
    }
    n->old_line = n->line = term->cache_line;
    n->value = n->old_value = term->rewrite;
    n->sig = n->old_sig = term->sig;
    n->find = n->old_find = term->find;
    n->merge = n->old_merge = term->merge;
    n->original = n->old_original = term->original;
    n->explanation = n->old_explanation = term->explanation;
    n->term = term;
    n->bad = (term->cache_bad?3:0);
    n->in_hash = (term->in_hash?3:2);
    term->in_hash = 1;
}

void _th_remove_cache(struct env *env)
{
    struct cache_info *c;
    int count = 0;

#ifdef CHECK_CACHE
    env->cache_installed = 0;
#endif
    c = env->head;
    //printf("*** Start remove ***\n");
    while (c) {
        ++count;
        //printf("c = %x %s\n", c, _th_print_exp(c->term));
        if (c==c->next) {
            fprintf(stderr, "LOOP %d\n", count);
            exit(1);
        }
        c->term->rewrite = NULL;
        c->term->cache_bad = 0;
        c->term->sig = NULL;
        c->term->find = c->term;
        c->term->in_hash = 0;
        //printf("Removing inhash %d %s\n", c->term->in_hash, _th_print_exp(c->term));
        c->term->merge = NULL;
        c->term->explanation = NULL;
        //if (c->original) {
        //    printf("%d: removing original %s\n", _tree_zone, _th_print_exp(c->term));
        //}
        c->term->original = NULL;
        _ex_add_term(c->term);
        c = c->next;
    }
}

void clean_cache(struct env *env)
{
    struct cache_info *c;
    c = env->head;
    while (c) {
        _th_add_cache_assignment(env,c->term,NULL);
        c = c->next;
    }
}

void _th_install_cache(struct env *env)
{
    struct cache_info *c;

#ifdef CHECK_CACHE
    env->cache_installed = 1;
#endif
    //printf("install cache %x\n", env);

    //do_hack_check = (hack_env==env);
    //if (do_hack_check) {
    //    printf("HACK CHECK ON\n");
    //} else {
    //    printf("HACK CHECK OFF\n");
    //}

    c = env->tail;
    //printf("*** Start install ***\n");
    while (c) {
        if (((int)c->term)&0x3) {
            fprintf(stderr, "Illegal value for c->term\n");
            exit(1);
        }
        //printf("c = %x\n", c);
        //fflush(stderr);
        c->term->rewrite = c->value;
        c->term->cache_bad = (((c->bad)&2)/2);
        c->term->sig = c->sig;
        c->term->find = c->find;
        c->term->merge = c->merge;
        c->term->explanation = c->explanation;
        c->term->cache_line = c->line;
        c->term->in_hash = (((c->in_hash)&2)/2);
        //if (c->term->in_hash) {
        //    printf("Adding inhash 2 %s\n", _th_print_exp(c->term));
        //} else {
            //printf("Removing inhash 2 %s\n", _th_print_exp(c->term));
            //printf("sig = %s\n", _th_print_exp(c->sig));
            //printf("old sig = %s\n", _th_print_exp(c->old_sig));
            //printf("find = %s\n", _th_print_exp(c->find));
            //printf("old find = %s\n", _th_print_exp(c->old_find));
            //printf("merge = %s\n", _th_print_exp(c->merge));
            //printf("old merge = %s\n", _th_print_exp(c->old_merge));
            //printf("explanation = %x\n", c->explanation);
            //printf("old explanation = %x\n", c->old_explanation);
            //printf("c->value = %s\n", _th_print_exp(c->value));
            //printf("c->old_value = %s\n", _th_print_exp(c->old_value));
            //printf("c->original = %s\n", _th_print_exp(c->original));
            //printf("c->old_original = %s\n", _th_print_exp(c->old_original));
            //printf("c->bad, c->in_hash = %d %d\n", c->bad, c->in_hash);
        //}
        //if (c->term->original != c->original) {
        //    printf("%d: installing original %s as ", _tree_zone, _th_print_exp(c->term));
        //    printf("%s\n", _th_print_exp(c->original));
        //}
        c->term->original = c->original;
        if ((c->term->cache_bad || c->term->rewrite==NULL || c->term->rewrite==c->term) && c->term->find==c->term) {
            _ex_add_term(c->term);
        } else {
            _ex_delete_term(c->term);
        }
        c = c->prev;
    }
}

void _th_clean_cache(struct env *env)
{
    struct cache_info *c = env->head;

    //_zone_print("clean cache");
    //_tree_indent();

    while (c) {
        //_zone_print_exp("Testing", c->term);
        //_zone_print1("addr %x", c);
        if (!c->term->cache_bad && c->term->rewrite != NULL) {
            //_tree_indent();
            //_zone_print0("Marking");
            //_tree_undent();
            _th_mark_bad(env,c->term);
            _ex_add_term(c->term);
        }
        //if (c==c->next) {
        //    fprintf(stderr, "_th_clean_cache: cycle %s\n", _th_print_exp(c->term));
        //    exit(1);
        //}
        c = c->next;
    }

    //_tree_undent();
}

static struct root_var *find_root_var(int s, struct env *env, struct _ex_intern *var)
{
    int hash = (((int)var)/4)%TERM_HASH;

    struct root_var *v = env->root_vars[hash];

    //_zone_print_exp("Fining root var", var);
    if (var != _ex_true && var != _ex_false && var->type==EXP_APPL) {
        fprintf(stderr, "find_root_var: Illegal variable type\n");
        exit(1);
    }
    while (v && v->var != var) {
        v = v->next;
    }

    if (v==NULL) {
        v = (struct root_var *)_th_alloc(s,sizeof(struct root_var));
        v->next = env->root_vars[hash];
        env->root_vars[hash] = v;
        v->parent = NULL;
        v->used_in_terms = NULL;
        v->equal_terms = NULL;
        v->ne_list = NULL;
        v->var = var;
    } else {
        //_zone_print0("Here2");
        while (v->parent) {
            //_zone_print2("d %d %d", v, v->parent);
            v = v->parent;
        }
    }

    return v;
}

static struct term_group *find_group(int s, struct env *env, struct _ex_intern *e, struct root_var *nv)
{
    int hash = ((int)e->u.appl.functor)%TERM_HASH;
    struct term_group *t = env->term_groups[hash];

    //_zone_print_exp("find group", e);

    if (e->type != EXP_APPL) {
        fprintf(stderr, "Find group of %s\n", _th_print_exp(e));
        fflush(stderr);
        exit(1);
    }

    while (t && t->term != e) {
        t = t->next;
    }

    if (t==NULL) {
        struct term_group_list *l;
        int i, j;
        //_zone_print0("Creating");
        t = (struct term_group *)_th_alloc(s,sizeof(struct term_group));
        t->next = env->term_groups[hash];
        env->term_groups[hash] = t;
        t->term = e;
        hash = e->u.appl.functor%TERM_HASH;
        t->functor_next = env->term_functors[hash];
        if (nv==NULL) {
            struct _ex_intern *tt;
            t->root_var = find_root_var(s,env,_ex_intern_var(_th_new_term_var(env)));
            tt = _th_get_type(env,e->u.appl.functor);
            if (tt) {
                tt = tt->u.appl.args[1];
                _th_set_var_type(env,t->root_var->var->u.var,tt);
            }
        } else {
            t->root_var = nv;
        }
        l = (struct term_group_list *)_th_alloc(s,sizeof(struct term_group_list));
        l->next = t->root_var->equal_terms;
        t->root_var->equal_terms = l;
        l->term = t;
        env->term_functors[hash] = t;
        for (i = 0; i < e->u.appl.count; ++i) {
            struct root_var *rv;
            for (j = 0; j < i; ++j) {
                if (e->u.appl.args[i]==e->u.appl.args[j]) goto cont;
            }
            rv = find_root_var(s,env,e->u.appl.args[i]);
            l = (struct term_group_list *)_th_alloc(s,sizeof(struct term_group_list));
            l->next = rv->used_in_terms;
            rv->used_in_terms = l;
            l->term = t;
cont:;
        }
    }

    return t;
}

static int equal_terms(int s, struct env *env, struct _ex_intern *e, struct _ex_intern *f)
{
    struct root_var *rv1, *rv2;
    int i;

    if (e->type != EXP_APPL || f->type != EXP_APPL) return e==f;

    if (e->u.appl.functor != f->u.appl.functor) return 0;
    
    if (e->u.appl.count != f->u.appl.count) return 0;

    //_zone_print_exp("et e", e);
    //_zone_print_exp("et f", f);

    for (i = 0; i < e->u.appl.count; ++i) {
        rv1 = find_root_var(s,env,e->u.appl.args[i]);
        rv2 = find_root_var(s,env,f->u.appl.args[i]);
        if (rv1 != rv2) return 0;
    }

    return 1;
}

static int divide_point(int s, struct env *env, struct _ex_intern *e, struct _ex_intern *f)
{
    int i;
    int pos = 0;
    struct root_var *srv1 = NULL, *srv2 = NULL;

    if (e->type != EXP_APPL || f->type != EXP_APPL) return 0;

    if (e->u.appl.functor != f->u.appl.functor) return 0;

    if (e->u.appl.count != f->u.appl.count) return 0;

    for (i = 0; i < e->u.appl.count; ++i) {
        struct root_var *rv1 = find_root_var(s, env, e->u.appl.args[i]);
        struct root_var *rv2 = find_root_var(s, env, f->u.appl.args[i]);

        if (rv1 != rv2) {
            if (pos && (rv1 != srv1 || rv2 != srv2)) return 0;
            srv1 = rv1;
            srv2 = rv2;
            pos = i+1;
        }
    }

    return 0;
}

static void add_ne(int s, struct root_var *rv1, struct root_var *rv2)
{
    struct root_var_list *ne = rv1->ne_list;

    while (ne) {
        if (ne->var==rv2) return;
        ne = ne->next;
    }

    ne = (struct root_var_list *)_th_alloc(s,sizeof(struct root_var_list));
    ne->next = rv1->ne_list;
    rv1->ne_list =ne;
    ne->var = rv2;
}

static struct _ex_intern *normalize_term(int s, struct env *env, struct _ex_intern *term);

static int term_changed;

static struct term_group_list *add_term_group(int s, struct env *env, struct root_var *rv, struct term_group_list *tgl, struct _ex_intern *term_o)
{
    struct term_group_list *gl;
    struct _ex_intern *term;

    term = normalize_term(s, env, term_o);
    term_changed = (term != term_o);
    gl = tgl;

    //_zone_print_exp("add term group", term_o);
    //_zone_print_exp("normalized", term);
    //_zone_print_exp("add term group root var", rv->var);

    while (gl != NULL) {
        if (gl->term->term==term) return tgl;
        gl = gl->next;
    }

    gl = (struct term_group_list *)_th_alloc(s,sizeof(struct term_group_list));
    gl->next = tgl;
    gl->term = find_group(s,env,term,rv);

    return gl;
}

static int has_root_var(struct root_var *rv, struct root_var_list *rvl)
{
    while (rvl) {
        if (rvl->var==rv) return 1;
        rvl = rvl->next;
    }
    return 0;
}

static int divide(int s, struct env *env, struct root_var *rv1, struct root_var *rv2);

static int propagate_divide(int s, struct env *env, struct root_var *rv1)
{
    struct root_var *rv2;
    struct root_var_list *ne;
    struct term_group_list *tg1, *tg2;

    ne = rv1->ne_list;
    while (ne) {
        tg1 = rv1->equal_terms;
        rv2 = ne->var;
        if (!rv2->parent) {
            while (tg1) {
                tg2 = rv2->equal_terms;
                while (tg2) {
                    if (tg1->term->term->u.appl.functor==tg2->term->term->u.appl.functor) {
                        int x = divide_point(s,env,tg1->term->term,tg2->term->term);
                        if (x) {
                            --x;
                            if (divide(s,env,find_root_var(s,env,tg1->term->term->u.appl.args[x]),
                                find_root_var(s,env,tg2->term->term->u.appl.args[x]))) {
                                return 1;
                            }
                        }
                    }
                    tg2 = tg2->next;
                }
                tg1 = tg1->next;
            }
        }
        ne = ne->next;
    }

    return 0;
}

static int join(int s, struct env *env, struct root_var *rv1, struct root_var *rv2)
{
    struct root_var_list *ne;
    struct term_group_list *u1;
    struct term_group_list *u2;
    //struct term_group_list *uterms;
    struct root_var_list *rebuild_ne = NULL;
    struct root_var_list *rebuild_equal_terms = NULL;
    struct root_var_pair_list *joins = NULL;

    _zone_print_exp("Joining", rv1->var);
    _zone_print_exp("and", rv2->var);

    while (rv1->parent) {
        rv1 = rv1->parent;
    }

    while (rv2->parent) {
        rv2 = rv2->parent;
    }

    if (rv1==rv2) {
        _zone_print0("ret 0");
        return 0;
    }

    ne = rv1->ne_list;

    while (ne) {
        if (ne->var==rv2) {
            _zone_print0("ret 1");
            return 1;
        }
        ne = ne->next;
    }

    //_zone_print0("Here1");

    if (_th_is_term(rv1->var) && !_th_is_term(rv2->var)) {
        struct root_var *t = rv1;
        rv1 = rv2;
        rv2 = t;
    }
    rv2->parent = rv1;

    //_zone_print0("Here2");

    ne = rv2->ne_list;
    while (ne) {
        add_ne(s, rv1, ne->var);
        add_ne(s, ne->var, rv1);
        if (!has_root_var(ne->var,rebuild_ne)) {
            struct root_var_list *n = (struct root_var_list *)ALLOCA(sizeof(struct root_var_list));
            n->next = rebuild_ne;
            rebuild_ne = n;
            n->var = ne->var;
        }
        ne = ne->next;
    }

    //_zone_print0("Here3");

    u2 = rv2->equal_terms;
    u1 = rv1->equal_terms;
    rv1->equal_terms = NULL;
    while (u1) {
        rv1->equal_terms = add_term_group(s,env,rv1,rv1->equal_terms,u1->term->term);
        u1 = u1->next;
    }
    while (u2) {
        rv1->equal_terms = add_term_group(s,env,rv1,rv1->equal_terms,u2->term->term);
        u2 = u2->next;
    }

    //_zone_print0("Here4");

    u1 = rv1->used_in_terms;
    u2 = rv2->used_in_terms;
    //rv1->used_in_terms = NULL;

    while (u1) {
        struct root_var *rv, *rv2;
        struct term_group *tg;
        struct _ex_intern *r;
        struct root_var_pair_list *nj;
        //rv1->used_in_terms = add_term_group(s,env,u1->term->root_var,rv1->used_in_terms,u1->term->term);
        //_zone_print_exp("Processing term", u1->term->term);
        rv = u1->term->root_var;
        while (rv->parent) rv = rv->parent;
        r = normalize_term(s,env,u1->term->term);
        //_zone_print_exp("Normalized to ", r);
        if (r != u1->term->term) {
            tg = find_group(s,env,r,rv);
            rv2 = tg->root_var;
            while (rv2->parent) rv2 = rv2->parent;
            if (rv != rv2) {
                nj = (struct root_var_pair_list *)ALLOCA(sizeof(struct root_var_pair_list));
                nj->next = joins;
                joins = nj;
                joins->var1 = rv;
                joins->var2 = rv2;
            }
            if (!has_root_var(rv,rebuild_equal_terms)) {
                struct root_var_list *n = (struct root_var_list *)ALLOCA(sizeof(struct root_var_list));
                //_zone_print_exp("Adding rebuild for", rv->var);
                n->next = rebuild_equal_terms;
                rebuild_equal_terms = n;
                n->var = rv2;
            }
        }
        u1 = u1->next;
    }
    while (u2) {
        struct root_var *rv, *rv2;
        struct term_group *tg;
        struct _ex_intern *r;
        struct root_var_pair_list *nj;
        //rv1->used_in_terms = add_term_group(s,env,u2->term->root_var,rv1->used_in_terms,u2->term->term);
        //_zone_print_exp("Processing term 2", u2->term->term);
        rv = u2->term->root_var;
        while (rv->parent) rv = rv->parent;
        r = normalize_term(s,env,u2->term->term);
        //_zone_print_exp("Normalized to ", r);
        if (r != u2->term->term) {
            tg = find_group(s,env,r,rv);
            rv2 = tg->root_var;
            while (rv2->parent) rv2 = rv2->parent;
            if (rv != rv2) {
                nj = (struct root_var_pair_list *)ALLOCA(sizeof(struct root_var_pair_list));
                nj->next = joins;
                joins = nj;
                joins->var1 = rv;
                joins->var2 = rv2;
            }
            if (!has_root_var(rv,rebuild_equal_terms)) {
                struct root_var_list *n = (struct root_var_list *)ALLOCA(sizeof(struct root_var_list));
                //_zone_print_exp("Adding rebuild for", rv->var);
               n->next = rebuild_equal_terms;
               rebuild_equal_terms = n;
               n->var = rv2;
            }
        }
        u2 = u2->next;
    }

    //_zone_print0("Here5");

    propagate_divide(s,env,rv1);

    while (rebuild_equal_terms != NULL) {
        u1 = rebuild_equal_terms->var->equal_terms;
        rebuild_equal_terms->var->equal_terms = NULL;
        while (u1 != NULL) {
            rebuild_equal_terms->var->equal_terms = add_term_group(s,env,rebuild_equal_terms->var,rebuild_equal_terms->var->equal_terms,u1->term->term);
            u1 = u1->next;
        }
        propagate_divide(s,env,rebuild_equal_terms->var);
        rebuild_equal_terms = rebuild_equal_terms->next;
    }

    while (rebuild_ne != NULL) {
        ne = rebuild_ne->var->ne_list;
        rebuild_ne->var->ne_list = NULL;
        while (ne) {
            struct root_var *v = ne->var;
            while (v->parent) {
                v = v->parent;
            }
            add_ne(s,rebuild_ne->var,v);
            ne = ne->next;
        }
        propagate_divide(s,env,rebuild_ne->var);
        rebuild_ne = rebuild_ne->next;
    }

    u1 = rv1->used_in_terms;
    while (u1) {
        u2 = rv2->used_in_terms;
        while (u2) {
            if (u1->term->term==u2->term->term) {
                if (join(s,env,u1->term->root_var,u2->term->root_var)) return 1;
            }
            u2 = u2->next;
        }
        u1 = u1->next;
    }
    while (joins) {
        if (join(s,env,joins->var1,joins->var2)) return 1;
        joins = joins->next;
    }
    //_zone_print0("Here6");
    if (rv1->var==_ex_true) {
        u1 = rv1->equal_terms;
        while (u1) {
            if (u1->term->term->u.appl.functor==INTERN_EQUAL) {
                if (_th_add_equality(s,env,u1->term->term->u.appl.args[0],u1->term->term->u.appl.args[1])) return 1;
            }
            if (u1->term->term->u.appl.functor==INTERN_NOT) {
                if (_th_add_equality(s,env,u1->term->term->u.appl.args[0],_ex_false)) return 1;
            }
            u1 = u1->next;
        }
    }
    //_zone_print0("Here7");
    if (rv1->var==_ex_false) {
        u1 = rv1->equal_terms;
        while (u1) {
            if (u1->term->term->u.appl.functor==INTERN_EQUAL) {
                if (_th_add_inequality(s,env,u1->term->term->u.appl.args[0],u1->term->term->u.appl.args[1])) return 1;
            }
            if (u1->term->term->u.appl.functor==INTERN_NOT) {
                if (_th_add_equality(s,env,u1->term->term->u.appl.args[0],_ex_true)) return 1;
            }
            u1 = u1->next;
        }
    }
    //_zone_print0("Here8");
    return 0;
}

static int divide(int s, struct env *env, struct root_var *rv1, struct root_var *rv2)
{
    //struct root_var_list *ne;
    struct term_group_list *e1;
    struct term_group_list *e2;
    //struct term_group_list *eterms;
 
    _zone_print_exp("Dividing", rv1->var);
    _zone_print_exp("and", rv2->var);

    while (rv1->parent) {
        rv1 = rv1->parent;
    }

    while (rv2->parent) {
        rv2 = rv2->parent;
    }

    if (rv1==rv2) return 1;

    add_ne(s,rv1,rv2);
    add_ne(s,rv2,rv1);

    e1 = rv1->equal_terms;
    //e2 = rv2->equal_terms;
    //while (e2) {
    //    eterms = (struct term_group_list *)_th_alloc(s,sizeof(struct term_group_list));
    //    eterms->next = rv1->equal_terms;
    //    rv1->equal_terms = eterms;
    //    eterms->term = e2->term;
    //    e2 = e2->next;
    //}
    while (e1) {
        e2 = rv2->used_in_terms;
        while (e2) {
            int x;
            if (x = divide_point(s,env,e1->term->term,e2->term->term)) {
                rv1 = find_root_var(s,env,e1->term->term->u.appl.args[x-1]);
                rv2 = find_root_var(s,env,e2->term->term->u.appl.args[x-1]);
                if (divide(s,env,rv1,rv2)) return 1;
            }
            e2 = e2->next;
        }
        e1 = e1->next;
    }

    return 0;
}

static int add_var_term(int s, struct env *env, struct _ex_intern *var, struct _ex_intern *term)
{
    struct root_var *rv = find_root_var(s, env, var);
    struct term_group *g = find_group(s, env,term, NULL);
    struct root_var *grv = rv;

    while (grv->parent) {
        grv = grv->parent;
    }

    if (g->root_var==rv) return 0;

    if (g->root_var==NULL) {
        g->root_var = rv;
        return 0;
    }

    return join(s, env, g->root_var, rv);
}

static int add_var_term_divide(int s, struct env *env, struct _ex_intern *var, struct _ex_intern *term)
{
    struct root_var *rv = find_root_var(s, env, var);
    struct term_group *g = find_group(s, env,term, NULL);
    struct root_var *grv = rv;

    while (grv->parent) {
        grv = grv->parent;
    }

    if (g->root_var==rv) return 0;

    if (g->root_var==NULL) {
        g->root_var = rv;
        return 0;
    }

    return divide(s, env, g->root_var, rv);
}

struct _ex_intern *_th_get_root(int s, struct env *env, struct _ex_intern *term)
{
    struct term_group *g;
    struct root_var *rv;
    //_zone_print_exp("_th_get_root", term);

    if (term->type==EXP_VAR || term->type==EXP_INTEGER || term->type==EXP_RATIONAL || term==_ex_true ||
        term==_ex_false) {
        struct root_var *rv = find_root_var(s,env,term);
        while (rv->parent) rv = rv->parent;
        return rv->var;
    }

    term = normalize_term(s,env,term);
    g = find_group(s, env, term, NULL);

    rv = g->root_var;
    while (rv->parent) {
        rv = rv->parent;
    }
    return rv->var;
}

static struct _ex_intern *normalize_term(int s, struct env *env, struct _ex_intern *term)
{
    int i;
    struct _ex_intern **args;

    if (term->type != EXP_APPL) return term;
    if (term==_ex_true || term==_ex_false) return term;

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * term->u.appl.count);
    for (i = 0; i < term->u.appl.count; ++i) {
        struct _ex_intern *e = normalize_term(s,env,term->u.appl.args[i]);
        args[i] = _th_get_root(s,env,e);
    }

    return _ex_intern_appl_env(env,term->u.appl.functor,term->u.appl.count,args);
}

int _th_add_equality(int s, struct env *env, struct _ex_intern *term1, struct _ex_intern *term2)
{
    struct root_var *rv1, *rv2;

    //_zone_print_exp("Add equality", term1);
    //_zone_print_exp("and", term2);
    term1 = normalize_term(s,env,term1);
    term2 = normalize_term(s,env,term2);
    if (term1==_ex_true && term2->type==EXP_APPL && term2->u.appl.functor==INTERN_NOT) {
        return _th_add_equality(s,env,_ex_false,term2->u.appl.args[0]);
    }
    if (term1==_ex_false && term2->type==EXP_APPL && term2->u.appl.functor==INTERN_NOT) {
        return _th_add_equality(s,env,_ex_true,term2->u.appl.args[0]);
    }
    if (term2==_ex_true && term1->type==EXP_APPL && term1->u.appl.functor==INTERN_NOT) {
        return _th_add_equality(s,env,_ex_false,term1->u.appl.args[0]);
    }
    if (term2==_ex_false && term1->type==EXP_APPL && term1->u.appl.functor==INTERN_NOT) {
        return _th_add_equality(s,env,_ex_true,term1->u.appl.args[0]);
    }
    if (term1==_ex_true && term2->type==EXP_APPL && term2->u.appl.functor==INTERN_EQUAL) {
        _th_add_equality(s,env,term2->u.appl.args[0],term2->u.appl.args[1]);
    }
    if (term1==_ex_false && term2->type==EXP_APPL && term2->u.appl.functor==INTERN_EQUAL) {
        _th_add_inequality(s,env,term2->u.appl.args[0],term2->u.appl.args[1]);
    }
    if (term2==_ex_true && term1->type==EXP_APPL && term1->u.appl.functor==INTERN_EQUAL) {
        _th_add_equality(s,env,term1->u.appl.args[0],term1->u.appl.args[1]);
    }
    if (term2==_ex_false && term1->type==EXP_APPL && term1->u.appl.functor==INTERN_EQUAL) {
        _th_add_inequality(s,env,term2->u.appl.args[0],term1->u.appl.args[1]);
    }

    if (term1->type==EXP_VAR || term1->type==EXP_INTEGER || term1->type==EXP_RATIONAL || term1==_ex_true ||
        term1==_ex_false) {
        if (term2->type==EXP_VAR || term2->type==EXP_INTEGER || term2->type==EXP_RATIONAL ||
            term2==_ex_true || term2==_ex_false) {
            rv1 = find_root_var(s, env, term1);
            rv2 = find_root_var(s, env, term2);
            return join(s, env, rv1, rv2);
        } else {
            return add_var_term(s, env, term1, term2);
        }
    } else {
        if (term2->type==EXP_VAR || term2->type==EXP_INTEGER || term2->type==EXP_RATIONAL || term2==_ex_true ||
            term2==_ex_false) {
            return add_var_term(s, env, term2, term1);
        } else {
            struct term_group *g = find_group(s, env, term1, NULL);
            return add_var_term(s, env, g->root_var->var, term2);
        }
    }
}

int _th_add_inequality(int s, struct env *env, struct _ex_intern *term1, struct _ex_intern *term2)
{
    struct root_var *rv1, *rv2;
    //_zone_print_exp("Add inequality", term1);
    //_zone_print_exp("and", term2);
    term1 = normalize_term(s,env,term1);
    term2 = normalize_term(s,env,term2);

    if (term1==_ex_false) {
        return _th_add_equality(s,env,_ex_true,term2);
    }
    if (term1==_ex_true) {
        return _th_add_equality(s,env,_ex_false,term2);
    }
    if (term2==_ex_false) {
        return _th_add_equality(s,env,_ex_true,term1);
    }
    if (term2==_ex_true) {
        return _th_add_equality(s,env,_ex_false,term1);
    }
    if (term1->type==EXP_VAR || term1->type==EXP_INTEGER || term1->type==EXP_RATIONAL) {
        if (term2->type==EXP_VAR || term2->type==EXP_INTEGER || term2->type==EXP_RATIONAL) {
            rv1 = find_root_var(s, env, term1);
            rv2 = find_root_var(s, env, term2);
            return divide(s, env, rv1, rv2);
        } else {
            return add_var_term_divide(s, env, term1, term2);
        }
    } else {
        if (term2->type==EXP_VAR || term2->type==EXP_INTEGER || term2->type==EXP_RATIONAL) {
            return add_var_term_divide(s, env, term2, term1);
        } else {
            struct term_group *g = find_group(s, env, term1, NULL);
            return add_var_term_divide(s, env, g->root_var->var, term2);
        }
    }
}

int _th_equality_status(int s,struct env *env, struct _ex_intern *term1, struct _ex_intern *term2)
{
    struct root_var *rv1, *rv2;
    struct root_var_list *rl;

    //_zone_print_exp("Testing equality status", term1);
    //_zone_print_exp("and", term2);

    term1 = normalize_term(s,env,term1);
    term2 = normalize_term(s,env,term2);

    if (term1->type==EXP_VAR || term1->type==EXP_INTEGER || term1->type==EXP_RATIONAL || term1==_ex_true ||
        term1==_ex_false) {
        rv1 = find_root_var(s,env,term1);
    } else {
        struct term_group *g = find_group(s, env, term1, NULL);
        rv1 = g->root_var;
    }

    if (term2->type==EXP_VAR || term2->type==EXP_INTEGER || term2->type==EXP_RATIONAL || term2==_ex_true ||
        term2==_ex_false) {
        rv2 = find_root_var(s,env,term2);
    } else {
        struct term_group *g = find_group(s, env, term2, NULL);
        rv2 = g->root_var;
    }

    while (rv1->parent) rv1 = rv1->parent;
    while (rv2->parent) rv2 = rv2->parent;

    if (rv1==rv2) return 1;

    rl = rv1->ne_list;
    while (rl) {
        if (rl->var==rv2) return -1;
        rl = rl->next;
    }

    return 0;
}

static int root_var_cmp(struct root_var *rv1, struct root_var *rv2)
{
    struct _ex_intern *r1 = rv1->var;
    struct _ex_intern *r2 = rv2->var;
    char *n1, *n2;
    unsigned *tmp1, *tmp2;

    if (r1==r2) return 0;

    switch (r1->type) {
        case EXP_APPL:
            if (r2->type != EXP_APPL) return 1;
            if (r1==_ex_true && r2==_ex_false) return 1;
            return -1;
        case EXP_INTEGER:
            if (r2->type==EXP_APPL) return -1;
            if (r2->type!=EXP_INTEGER) return 1;
            if (_th_big_less(r1->u.integer,r2->u.integer)) return 1;
            return -1;
        case EXP_RATIONAL:
            if (r2->type==EXP_APPL || r2->type==EXP_INTEGER) return -1;
            if (r2->type!=EXP_RATIONAL) return 1;
            tmp1 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(r1->u.rational.numerator,r2->u.rational.denominator));
            tmp2 = _th_big_copy(REWRITE_SPACE,_th_big_multiply(r2->u.rational.numerator,r1->u.rational.denominator));
            if (_th_big_less(tmp1,tmp2)) return 1;
            return -1;
        case EXP_VAR:
            if (r2->type==EXP_APPL || r2->type==EXP_INTEGER || r2->type==EXP_RATIONAL) return -1;
            if (r2->type != EXP_VAR) return 1;
            n1 = _th_intern_decode(r1->u.var);
            n2 = _th_intern_decode(r2->u.var);
            if (strncmp(n1,"_term",5)) {
                if (strncmp(n2,"_term",5)) {
                    //printf("Here1\n");
                    return strcmp(n2,n1);
                } else {
                    //printf("Here2\n");
                    return 1;
                }
            } else {
                if (strncmp(n2,"_term",5)) {
                    //printf("Here3\n");
                    return -1;
                } else {
                    //printf("Here4\n");
                    return atoi(n2+5)-atoi(n1+5);
                }
            }
        default:
            return 0;
    }
}

struct root_var_list *find_place(struct root_var_list *l, struct root_var *v)
{
    if (l==NULL) return NULL;

    if (root_var_cmp(l->var,v) < 0) return NULL;

    while (l->next) {
        if (root_var_cmp(l->next->var,v)<0) {
            return l;
        }
        l = l->next;
    }
    return l;
}

void _th_print_equality_info(struct env *env)
{
    int i;
    struct root_var *rv, *p;
    struct term_group_list *gl;
    struct root_var_list *rvl, *all, *n, *place;

    _tree_print0("Equality info");
    _tree_indent();

    all = NULL;
    for (i = 0; i < TERM_HASH; ++i) {
        rv = env->root_vars[i];
        while (rv) {
            n = (struct root_var_list *)ALLOCA(sizeof(struct root_var_list));
            place = find_place(all,rv);
            if (place) {
                n->next = place->next;
                place->next = n;
            } else {
                n->next = all;
                all = n;
            }
            n->var = rv;
            rv = rv->next;
        }
    }
#ifdef XX
    n = all;
    while (n) {
        if (n->next) {
            printf("vars %s %s\n", _th_intern_decode(n->var->var->u.var), _th_intern_decode(n->next->var->var->u.var));
            if (root_var_cmp(n->var,n->next->var)<0) {
                printf("Illegal order\n");
                exit(1);
            }
        }
        n = n->next;
    }
#endif
    _tree_print0("Root variables");
    _tree_indent();
    n = all;
    while (n) {
        rv = n->var;
        p = rv;
        while (p->parent) {
            p = p->parent;
        }
        if (rv==p) {
            _tree_print_exp("Var", rv->var);
            _tree_indent();
            _tree_print0("Terms");
            _tree_indent();
            gl = rv->equal_terms;
            while (gl) {
                _tree_print_exp("term", gl->term->term);
                gl = gl->next;
            }
            _tree_undent();
            _tree_print0("Terms containing var");
            _tree_indent();
            gl = rv->used_in_terms;
            while (gl) {
                _tree_print_exp("term", gl->term->term);
                gl = gl->next;
            }
            _tree_undent();
            rvl = rv->ne_list;
            _tree_print0("ne list");
            _tree_indent();
            while (rvl) {
                _tree_print_exp("ne", rvl->var->var);
                rvl = rvl->next;
            }
            _tree_undent();
            _tree_undent();
        }
        n = n->next;
    }
    _tree_undent();

    _tree_print0("Eliminated root variables");
    _tree_indent();
    n = all;
    while (n) {
        rv = n->var;
        p = rv;
        while (p->parent) {
            p = p->parent;
        }
        if (rv!=p) {
            _tree_print_exp("var", rv->var);
            _tree_indent();
            _tree_print_exp("parent", p->var);
            _tree_print0("Terms");
            _tree_indent();
            gl = rv->equal_terms;
            while (gl) {
                _tree_print_exp("term", gl->term->term);
                gl = gl->next;
            }
            _tree_undent();
            _tree_print0("Terms containing var");
            _tree_indent();
            gl = rv->used_in_terms;
            while (gl) {
                _tree_print_exp("term", gl->term->term);
                gl = gl->next;
            }
            _tree_undent();
            rvl = rv->ne_list;
            _tree_print0("ne list");
            _tree_indent();
            while (rvl) {
                _tree_print_exp("ne", rvl->var->var);
                rvl = rvl->next;
            }
            _tree_undent();
            _tree_undent();
        }
        n = n->next;
    }
    _tree_undent();

    _tree_print0("Term groups");
    _tree_indent();
    for (i = 0; i < TERM_HASH; ++i) {
        struct term_group *g;
        g = env->term_groups[i];
        while (g) {
            _tree_print_exp("term group", g->term);
            _tree_indent();
            _tree_print_exp("var", g->root_var->var);
            _tree_undent();
            g = g->next;
        }
    }
    _tree_undent();

    _tree_print0("Term groups (by functor)");
    _tree_indent();
    for (i = 0; i < TERM_HASH; ++i) {
        struct term_group *g;
        g = env->term_functors[i];
        while (g) {
            _tree_print_exp("term group", g->term);
            _tree_indent();
            _tree_print_exp("var", g->root_var->var);
            _tree_undent();
            g = g->functor_next;
        }
    }
    _tree_undent();

    _tree_undent();

    for (i = 0; i < TERM_HASH; ++i) {
        struct root_var *rv = env->root_vars[i];
        while (rv != NULL) {
            if (!rv->parent) {
                struct root_var_list *ne = rv->ne_list;
                while (ne) {
                    if (!ne->var->parent) {
                        struct term_group_list *tgl1 = rv->equal_terms;
                        while (tgl1) {
                            struct term_group_list *tgl2 = ne->var->equal_terms;
                            while (tgl2) {
                                if (tgl1->term->term->u.appl.functor==tgl2->term->term->u.appl.functor) {
                                    int x = divide_point(ENVIRONMENT_SPACE,env,tgl1->term->term,tgl2->term->term);
                                    if (x) {
                                        struct root_var *rv1 = find_root_var(ENVIRONMENT_SPACE,env,tgl1->term->term->u.appl.args[x-1]);
                                        struct root_var *rv2 = find_root_var(ENVIRONMENT_SPACE,env,tgl2->term->term->u.appl.args[x-1]);
                                        struct root_var_list *n = rv1->ne_list;
                                        while (n) {
                                            if (n->var==rv2) goto cont;
                                            n = n->next;
                                        }
                                        printf("Missed inequality\n");
                                        exit(1);
                                    }
cont:;
                                }
                                tgl2 = tgl2->next;
                            }
                            tgl1 = tgl1->next;
                        }
                    }
                    ne = ne->next;
                }
            }
            rv = rv->next;
        }
    }
}

static int has_equality(struct env *env, struct parent_list *l, struct _ex_intern *t1, struct _ex_intern *t2)
{
    while (l) {
        struct _ex_intern *e = _th_unmark_vars(env,l->split);
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_ORIENTED_RULE && e->u.appl.args[2]==_ex_true) {
            if (t1==e->u.appl.args[0] && t2==e->u.appl.args[1]) return 1;
            if (t1==e->u.appl.args[1] && t2==e->u.appl.args[0]) return 1;
            if (e->u.appl.args[1]==_ex_true) {
                e = e->u.appl.args[0];
                if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL) {
                    if (t1==e->u.appl.args[0] && t2==e->u.appl.args[1]) return 1;
                    if (t1==e->u.appl.args[1] && t2==e->u.appl.args[0]) return 1;
                }
            }
        } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL) {
            if (t1==e->u.appl.args[0] && t2==e->u.appl.args[1]) return 1;
            if (t1==e->u.appl.args[1] && t2==e->u.appl.args[0]) return 1;
        }
        l = l->next;
    }
    return 0;
}

static int has_inequality(struct env *env, struct parent_list *l, struct _ex_intern *t1, struct _ex_intern *t2)
{
    while (l) {
        struct _ex_intern *e = _th_unmark_vars(env,l->split);
        if (e->type==EXP_APPL && e->u.appl.functor==INTERN_ORIENTED_RULE && e->u.appl.args[2]==_ex_true) {
            if (e->u.appl.args[1]==_ex_false) {
                e = e->u.appl.args[0];
                if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL) {
                    if (t1==e->u.appl.args[0] && t2==e->u.appl.args[1]) return 1;
                    if (t1==e->u.appl.args[1] && t2==e->u.appl.args[0]) return 1;
                }
            }
        } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
            e = e->u.appl.args[0];
            if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL) {
                if (t1==e->u.appl.args[0] && t2==e->u.appl.args[1]) return 1;
                if (t1==e->u.appl.args[1] && t2==e->u.appl.args[0]) return 1;
            }
        }
        l = l->next;
    }
    return 0;
}

static struct parent_list *add_eq(struct env *env, struct parent_list *l, struct _ex_intern *t1, struct _ex_intern *t2)
{
    struct parent_list *nl;

    //if (has_equality(env,l,t1,t2)) return l;

    nl = (struct parent_list *)_th_alloc(HEURISTIC_SPACE,sizeof(struct parent_list));
    nl->next = l;
    nl->split = _ex_intern_appl2_env(env,INTERN_EQUAL,t1,t2);

    return nl;
}

static struct parent_list *add_neq(struct env *env, struct parent_list *l, struct _ex_intern *t1, struct _ex_intern *t2)
{
    struct parent_list *nl;

    //if (has_inequality(env,l,t1,t2)) return l;

    nl = (struct parent_list *)_th_alloc(HEURISTIC_SPACE,sizeof(struct parent_list));
    nl->next = l;
    nl->split = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_EQUAL,t1,t2));

    return nl;
}

struct parent_list *_th_add_equalities(struct parent_list *l, struct env *env)
{
    int i;
    struct root_var *rv;

    for (i = 0; i < TERM_HASH; ++i) {
        rv = env->root_vars[i];
        while (rv != NULL) {
            if (rv->parent != NULL) {
                l = add_eq(env,l,rv->var,rv->parent->var);
            } else {
                struct term_group_list *tg = rv->equal_terms;
                struct root_var_list *rvl = rv->ne_list;

                while (tg != NULL) {
                    l = add_eq(env,l,rv->var,tg->term->term);
                    tg = tg->next;
                }

                while (rvl != NULL) {
                    l = add_neq(env,l,rv->var,rvl->var->var);
                    rvl = rvl->next;
                }
            }
            rv = rv->next;
        }
    }

    return l;
}

static int variables_fully_connected(struct env *env)
{
    int i;
    struct root_var_list *vars, *nrvl;
    struct root_var *rv;

    vars = NULL;
    for (i = 0; i < TERM_HASH; ++i) {
        rv = env->root_vars[i];
        while (rv) {
            if (!rv->parent && rv->var->type==EXP_VAR && strncmp(_th_intern_decode(rv->var->u.var),"_term",5)) {
                nrvl = (struct root_var_list *)ALLOCA(sizeof(struct root_var_list));
                nrvl->next = vars;
                vars = nrvl;
                nrvl->var = rv;
            }
            rv = rv->next;
        }
    }

    while (vars != NULL) {
        nrvl = vars->next;
        while (nrvl != NULL) {
            struct root_var_list *ne;
            ne = vars->var->ne_list;
            while (ne) {
                if (ne->var==nrvl->var) goto cont;
                ne =ne->next;
            }
            return env->vars_fully_connected = 0;
cont:
            nrvl = nrvl->next;
        }
        vars = vars->next;
    }

    return env->vars_fully_connected = 1;
}

static struct add_list *collect_equalities_between_vars(struct env *env)
{
    int i;
    struct root_var_list *vars, *nrvl;
    struct root_var *rv;
    struct add_list *ret, *n;

    vars = NULL;
    for (i = 0; i < TERM_HASH; ++i) {
        rv = env->root_vars[i];
        while (rv) {
            if (!rv->parent && rv->var->type==EXP_VAR && strncmp(_th_intern_decode(rv->var->u.var),"_term",5)) {
                nrvl = (struct root_var_list *)ALLOCA(sizeof(struct root_var_list));
                nrvl->next = vars;
                vars = nrvl;
                nrvl->var = rv;
                //printf("Adding var %s\n", _th_print_exp(rv->var));
            }
            rv = rv->next;
        }
    }

    ret = NULL;
    while (vars != NULL) {
        //printf("var = %s\n", _th_print_exp(vars->var->var));
        nrvl = vars->next;
        while (nrvl != NULL) {
            struct _ex_intern *t1 = _th_get_var_type(env,vars->var->var->u.var);
            struct _ex_intern *t2 = _th_get_var_type(env,nrvl->var->var->u.var);
            //printf("nrvl = %s\n", _th_print_exp(nrvl->var->var));
            //printf("t1 = %s\n", _th_print_exp(t1));
            //printf("t2 = %s\n", _th_print_exp(t2));
            //if (vars->var->var==_ex_true || vars->var->var==_ex_false ||
            //    nrvl->var->var==_ex_true || nrvl->var->var==_ex_false) exit(1);
            if (t1==t2) {
                struct root_var_list *ne = vars->var->ne_list;
                while (ne) {
                    if (ne->var==nrvl->var) goto cont;
                    ne = ne->next;
                }
                n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                n->next = ret;
                ret = n;
                n->e = _ex_intern_appl2_env(env,INTERN_EQUAL,vars->var->var,nrvl->var->var);
                //printf("Adding equality %s\n", _th_print_exp(n->e));
cont:;
            }
            nrvl = nrvl->next;
        }
        vars = vars->next;
    }

    return ret;
}

static int is_fully_connected(struct env *env, struct root_var *var)
{
    struct term_group_list *gl;

    if (var->var->type != EXP_VAR) return 1;

    if (strncmp(_th_intern_decode(var->var->u.var),"_term",5)) return 1;

    gl = var->equal_terms;

    while (gl) {
        int i;
        struct _ex_intern *e = gl->term->term;
        for (i = 0; i < e->u.appl.count; ++i) {
            struct root_var *rv = find_root_var(ENVIRONMENT_SPACE,env,e->u.appl.args[i]);
            if (rv->var->type==EXP_VAR && !strncmp(_th_intern_decode(rv->var->u.var),"_term",5)) goto cont;
        }
        return 1;
cont:
        gl = gl->next;
    }
    return  0;
}

static struct add_list *collect_equalities_between_fcfs(struct env *env)
{
    int i;
    struct root_var_list *vars, *nrvl;
    struct root_var *rv;
    struct add_list *ret, *n;

    vars = NULL;
    for (i = 0; i < TERM_HASH; ++i) {
        rv = env->root_vars[i];
        while (rv) {
            if (!rv->parent && ((rv->var->type==EXP_VAR && strncmp(_th_intern_decode(rv->var->u.var),"_term",5)) || is_fully_connected(env,rv))) {
                nrvl = (struct root_var_list *)ALLOCA(sizeof(struct root_var_list));
                nrvl->next = vars;
                vars = nrvl;
                nrvl->var = rv;
            }
            rv = rv->next;
        }
    }

    ret = NULL;
    while (vars != NULL) {
        nrvl = vars->next;
        while (nrvl != NULL) {
            struct _ex_intern *t1 = _th_get_var_type(env,vars->var->var->u.var);
            struct _ex_intern *t2 = _th_get_var_type(env,nrvl->var->var->u.var);
            if (t1==t2) {
                struct root_var_list *ne = vars->var->ne_list;
                while (ne) {
                    if (ne->var==nrvl->var) goto cont;
                    ne = ne->next;
                }
                n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                n->next = ret;
                ret = n;
                n->e = _ex_intern_appl2_env(env,INTERN_EQUAL,vars->var->var,nrvl->var->var);
                //printf("Adding equality %s\n", _th_print_exp(n->e));
cont:;
            }
            nrvl = nrvl->next;
        }
        vars = vars->next;
    }

    //exit(1);
    return ret;
}

struct add_list *_th_collect_restricted_equalities(struct env *env)
{
    if (variables_fully_connected(env)) {
        return collect_equalities_between_fcfs(env);
    } else {
        return collect_equalities_between_vars(env);
    }
}

int _th_score_equality(struct env *env, struct _ex_intern *term)
{
    struct root_var *rv;
    struct term_group_list *tgl;
    struct root_var_list *rvl;
    int count;

    if (term->type != EXP_APPL || term->u.appl.functor != INTERN_EQUAL) {
        if (term->type==EXP_APPL && term->u.appl.functor==INTERN_NOT) {
            term = _ex_intern_appl2_env(env,INTERN_EQUAL,term->u.appl.args[0],_ex_false);
        } else {
            term = _ex_intern_appl2_env(env,INTERN_EQUAL,term,_ex_true);
        }
    }

    count = 0;

    rv = find_root_var(ENVIRONMENT_SPACE,env,_th_get_root(ENVIRONMENT_SPACE,env,term->u.appl.args[0]));
    if (rv->var->type != EXP_VAR || strncmp(_th_intern_decode(rv->var->u.var),"_term",5)) {
        ++count;
    }
    tgl = rv->equal_terms;
    while (tgl) {
        ++count;
        tgl = tgl->next;
    }
    rvl = rv->ne_list;
    while (rvl) {
        ++count;
        rvl = rvl->next;
    }

    rv = find_root_var(ENVIRONMENT_SPACE,env,_th_get_root(ENVIRONMENT_SPACE,env,term->u.appl.args[1]));
    if (rv->var->type != EXP_VAR || strncmp(_th_intern_decode(rv->var->u.var),"_term",5)) {
        ++count;
    }
    tgl = rv->equal_terms;
    while (tgl) {
        ++count;
        tgl = tgl->next;
    }
    rvl = rv->ne_list;
    while (rvl) {
        ++count;
        rvl = rvl->next;
    }

    return count;
}

int _th_legal_split(struct env *env, struct _ex_intern *term)
{
    struct root_var *rv;
    struct term_group_list *tgl;

    if (term->type != EXP_APPL || term->u.appl.functor != INTERN_EQUAL) {
        if (term->type==EXP_APPL && term->u.appl.functor==INTERN_NOT) {
            term = _ex_intern_appl2_env(env,INTERN_EQUAL,term->u.appl.args[0],_ex_false);
        } else {
            term = _ex_intern_appl2_env(env,INTERN_EQUAL,term,_ex_true);
        }
    }

    rv = find_root_var(ENVIRONMENT_SPACE,env,_th_get_root(ENVIRONMENT_SPACE,env,term->u.appl.args[0]));
    if (rv->var->type == EXP_VAR && !strncmp(_th_intern_decode(rv->var->u.var),"_term",5)) {
        if (env->vars_fully_connected) {
            tgl = rv->equal_terms;
            while (tgl) {
                int i;
                for (i = 0; i < tgl->term->term->u.appl.count; ++i) {
                    struct root_var *rv1 = find_root_var(ENVIRONMENT_SPACE,env,tgl->term->term->u.appl.args[i]);
                    if (!is_fully_connected(env,rv1)) goto cont1;
                }
                goto good1;
cont1:
                tgl = tgl->next;
            }
        }
        return 0;
    }
good1:

    rv = find_root_var(ENVIRONMENT_SPACE,env,_th_get_root(ENVIRONMENT_SPACE,env,term->u.appl.args[1]));
    if (rv->var->type == EXP_VAR && !strncmp(_th_intern_decode(rv->var->u.var),"_term",5)) {
        if (env->vars_fully_connected) {
            tgl = rv->equal_terms;
            while (tgl) {
                int i;
                for (i = 0; i < tgl->term->term->u.appl.count; ++i) {
                    struct root_var *rv1 = find_root_var(ENVIRONMENT_SPACE,env,tgl->term->term->u.appl.args[i]);
                    if (!is_fully_connected(env,rv1)) goto cont2;
                }
                goto good2;
cont2:
                tgl = tgl->next;
            }
        }
        return 0;
    }
good2:

    return 1;
}

struct add_list *_th_collect_equalities(struct env *env)
{
    int i;
    struct root_var_list *vars, *nrvl;
    struct root_var *rv;
    struct add_list *ret, *n;

    vars = NULL;
    for (i = 0; i < TERM_HASH; ++i) {
        rv = env->root_vars[i];
        while (rv) {
            if (!rv->parent) {
                nrvl = (struct root_var_list *)ALLOCA(sizeof(struct root_var_list));
                nrvl->next = vars;
                vars = nrvl;
                nrvl->var = rv;
            }
            rv = rv->next;
        }
    }

    ret = NULL;
    while (vars != NULL) {
        nrvl = vars->next;
        while (nrvl != NULL) {
            struct _ex_intern *t1 = _th_get_var_type(env,vars->var->var->u.var);
            struct _ex_intern *t2 = _th_get_var_type(env,vars->var->var->u.var);
            if (t1==t2) {
                struct root_var_list *ne = vars->var->ne_list;
                while (ne) {
                    if (ne->var==nrvl->var) goto cont;
                    ne = ne->next;
                }
                n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
                n->next = ret;
                ret = n;
                n->e = _ex_intern_appl2_env(env,INTERN_EQUAL,vars->var->var,nrvl->var->var);
cont:;
            }
            nrvl = nrvl->next;
        }
        vars = vars->next;
    }

    return ret;
}

unsigned _th_new_slack(struct env *env)
{
    char name[10];

    sprintf(name, "_slack%d", env->slack++);

    //printf("**** New slack %s %d\n", name, _tree_zone);

    return _th_intern(name);
}

unsigned _th_new_term_var(struct env *env)
{
    char name[10];

    sprintf(name, "_term%d", env->slack++);

    //printf("**** New slack %s %d\n", name, _tree_zone);

    return _th_intern(name);
}

static struct _ex_intern *max_term(struct env *env, struct _ex_intern *appl,int skip_count, struct _ex_intern **skip_list)
{
    int i, j;
    struct _ex_intern *max;

    max = NULL;
    for (i = 0; i < appl->u.appl.count; ++i) {
        for (j = 0; j < skip_count; ++j) {
            if (appl->u.appl.args[i]==skip_list[j]) goto cont;
        }
        if (max==NULL || _th_term_compare(env,max,appl->u.appl.args[i]) > 0) {
            max = appl->u.appl.args[i];
        }
cont:;
    }

    return max;
}

int _th_term_compare(struct env *env, struct _ex_intern *term1, struct _ex_intern *term2)
{
    int i;

    if (term1==term2) return 0;

    if (term2==_ex_true) return -1;
    if (term1==_ex_true) return 1;
    if (term2==_ex_false) return -1;
    if (term1==_ex_false) return 1;

    if (term1->type==EXP_APPL) {
        if (term1->u.appl.functor==INTERN_NAT_PLUS || term1->u.appl.functor==INTERN_NAT_TIMES ||
            term1->u.appl.functor==INTERN_RAT_PLUS || term1->u.appl.functor==INTERN_RAT_TIMES ||
            term1->u.appl.functor==INTERN_NAT_DIVIDE || term1->u.appl.functor==INTERN_RAT_DIVIDE) {
            if (term2->type!=EXP_APPL || term2->u.appl.functor!=term1->u.appl.functor) {
                struct _ex_intern *max;
                for (i = 0; i < term1->u.appl.count; ++i) {
                    if (term2==term1->u.appl.args[i]) return -1;
                }
                max = max_term(env,term1,0,NULL);
                return _th_term_compare(env,max,term2);
            }
        }
    }
    if (term2->type==EXP_APPL) {
        if (term2->u.appl.functor==INTERN_NAT_PLUS || term2->u.appl.functor==INTERN_NAT_TIMES ||
            term2->u.appl.functor==INTERN_RAT_PLUS || term2->u.appl.functor==INTERN_RAT_TIMES ||
            term2->u.appl.functor==INTERN_NAT_DIVIDE || term2->u.appl.functor==INTERN_RAT_DIVIDE) {
            if (term1->type!=EXP_APPL || term1->u.appl.functor!=term2->u.appl.functor) {
                struct _ex_intern *max;
                for (i = 0; i < term2->u.appl.count; ++i) {
                    if (term1==term2->u.appl.args[i]) return 1;
                }
                max = max_term(env,term2,0,NULL);
                return _th_term_compare(env,term1,max);
            }
        }
    }

    if (term1->height < term2->height) return 1;
    if (term1->height > term2->height) return -1;

    switch (term1->type) {
        case EXP_INTEGER:
            if (term2->type==EXP_INTEGER) {
                if (_th_big_less(term1->u.integer,term2->u.integer)) return 1;
                return -1;
            }
            return 1;
        case EXP_RATIONAL:
            if (term2->type==EXP_INTEGER) return -1;
            if (term2->type!=EXP_RATIONAL) return 1;
            return (((int)term1) < ((int)term2))?1:-1;
        case EXP_STRING:
            if (term2->type==EXP_INTEGER || term2->type==EXP_RATIONAL) return -1;
            if (term2->type!=EXP_STRING) return 1;
            return strcmp(term1->u.string,term2->u.string);
        case EXP_MARKED_VAR:
            if (term2->type==EXP_INTEGER || term2->type==EXP_RATIONAL || term2->type==EXP_STRING) return -1;
            if (term2->type!=EXP_MARKED_VAR) return 1;
            return strcmp(_th_intern_decode(term1->u.marked_var.var),_th_intern_decode(term2->u.marked_var.var));
        case EXP_VAR:
            if (term2->type==EXP_INTEGER || term2->type==EXP_RATIONAL || term2->type==EXP_STRING ||
                term2->type==EXP_MARKED_VAR) return -1;
            if (term2->type!=EXP_VAR) return 1;
            return strcmp(_th_intern_decode(term1->u.var),_th_intern_decode(term2->u.var));
        case EXP_APPL:
            if (term1->u.appl.functor==term2->u.appl.functor) {
                struct _ex_intern **skip_list = ALLOCA(sizeof(struct _ex_intern *) * (term1->u.appl.count + term2->u.appl.count));
                int pos = 0;
                struct _ex_intern *max1, *max2;
                max1 = max_term(env,term1,0,NULL);
                max2 = max_term(env,term2,0,NULL);
                while (max1==max2 && max1 != NULL && max2 != NULL) {
                    skip_list[pos++] = max1;
                    max1 = max_term(env,term1,pos,skip_list);
                    max2 = max_term(env,term2,pos,skip_list);
                }
                if (max1==NULL) {
                    if (max2==NULL) {
                        for (i = 0; i < term1->u.appl.count; ++i) {
                            int x = _th_term_compare(env,term1->u.appl.args[i],term2->u.appl.args[i]);
                            if (x != 0) return x;
                        }
                        return 0;
                    } else {
                        return 1;
                    }
                } else {
                    if (max2==NULL) {
                        return -1;
                    } else {
                        return _th_term_compare(env,max1,max2);
                    }
                }
            }
            if (_th_has_smaller_precedence(env,term1->u.appl.functor,term2->u.appl.functor)) return 1;
            if (_th_has_smaller_precedence(env,term2->u.appl.functor,term1->u.appl.functor)) return -1;
            return term2->u.appl.functor-term1->u.appl.functor;
        default:
            return 0;
    }
}

int _th_is_term(struct _ex_intern *term)
{
    if (term->type==EXP_VAR) {
        char *s = _th_intern_decode(term->u.var);
        if (s[0]=='_' && s[1]=='t' && s[2]=='e' && s[3]=='r' && s[4]=='m') {
            return atoi(s+5)+1;
        } else {
            return 0;
        }
    } else if (term->type==EXP_MARKED_VAR) {
        char *s = _th_intern_decode(term->u.var);
        if (s[0]=='_' && s[1]=='t' && s[2]=='e' && s[3]=='r' && s[4]=='m') {
            return atoi(s+5)+1;
        } else {
            return 0;
        }
    } else {
        return 0;
    }
}

int _th_is_slack(struct _ex_intern *term)
{
    if (term->type==EXP_VAR) {
        char *s = _th_intern_decode(term->u.var);
        if (s[0]=='_' && s[1]=='s' && s[2]=='l' && s[3]=='a' && s[4]=='c' && s[5]=='k') {
            return atoi(s+6)+1;
        } else {
            return 0;
        }
    } else if (term->type==EXP_MARKED_VAR) {
        char *s = _th_intern_decode(term->u.var);
        if (s[0]=='_' && s[1]=='s' && s[2]=='l' && s[3]=='a' && s[4]=='c' && s[5]=='k') {
            return atoi(s+6)+1;
        } else {
            return 0;
        }
    } else {
        return 0;
    }
}

int _th_term_cmp(struct _ex_intern **t1, struct _ex_intern **t2)
{
    int x, y;

    //_zone_print2("_th_term_cmp %d %s", *t1, _th_print_exp(*t1));
    //_zone_print2("_th_term_cmp %d %s", *t2, _th_print_exp(*t2));
    if (x = _th_is_slack(*t1)) {
        if (y = _th_is_slack(*t2)) {
            return x-y;
        } else {
            return 1;
        }
    } else if (x = _th_is_term(*t1)) {
        if (_th_is_slack(*t2)) {
            return -1;
        } else if (y = _th_is_term(*t2)) {
            return x-y;
        } else {
            return 1;
        }
    } else {
        if (_th_is_slack(*t2) || _th_is_term(*t2)) {
            return -1;
        } else {
            //_zone_print1("diff %d", (((int)*t2)-((int)*t1)));
            return ((int)*t2)-((int)*t1);
        }
    }
}

void _print_simplified_rules(struct env *env)
{
    struct rule *r = env->simplified_rules;

    printf("RULES\n");
    while (r) {
        printf("    %x %x %s\n", r, r->rule, _th_print_exp(r->rule));
        r = r->next;
    }
}

void _th_add_simplified_rule(struct env *env, struct _ex_intern *rule)
{
    struct rule *r = (struct rule *)_th_alloc(env->space, sizeof(struct rule));
    //int c;
    //if (rule==NULL) {
    //    int i = 0;
    //    i = 1 / i;
    //}
    //printf("Marking as simplified %s\n", _th_print_exp(rule));
    //_th_get_marked_vars(rule->u.appl.args[1], &c);
    //if (c) {
    //    exit(1);
    //}
    //if (rule->u.appl.args[0]->type==EXP_MARKED_VAR &&
    //    !strcmp(_th_intern_decode(rule->u.appl.args[0]->u.marked_var.var),"_slack4")) {
    //    fprintf(stderr,"Illegal simplification mark %s\n", _th_print_exp(rule));
    //}
    r->next = env->simplified_rules;
    r->rule = rule;
    //if (env->simplified_rules) {
    //    printf("add_simplified_rule %x %x\n", r, r->next);
    //} else {
    //    printf("add_simplified_rule 0\n");
    //}

    env->simplified_rules = r;

    //_print_simplified_rules(env);
}

void _th_add_original_rule(struct env *env, struct _ex_intern *rule)
{
    struct rule *r = (struct rule *)_th_alloc(env->space, sizeof(struct rule));
    //int c;
    //if (rule==NULL) {
    //    int i = 0;
    //    i = 1 / i;
    //}
    //printf("Marking as simplified %s\n", _th_print_exp(rule));
    //_th_get_marked_vars(rule->u.appl.args[1], &c);
    //if (c) {
    //    exit(1);
    //}
    //if (rule->u.appl.args[0]->type==EXP_MARKED_VAR &&
    //    !strcmp(_th_intern_decode(rule->u.appl.args[0]->u.marked_var.var),"_slack4")) {
    //    fprintf(stderr,"Illegal simplification mark %s\n", _th_print_exp(rule));
    //}
    r->next = env->blocked_rules;
    r->rule = rule;
    //if (env->simplified_rules) {
    //    printf("add_simplified_rule %x %x\n", r, r->next);
    //} else {
    //    printf("add_simplified_rule 0\n");
    //}

    env->blocked_rules = r;

    //_print_simplified_rules(env);
}

static int in_list (struct env *env, struct _ex_intern *rule)
{
    struct rule *r = env->simplified_rules;
    while (r) {
        if (r->rule==rule) return 1;
        r = r->next;
    }
    return 0;
}

void _th_mark_simplified(struct env *env)
{
    struct rule *r = env->simplified_rules;

    //printf("mark simplified %x\n", env->simplified_rules);

    while (r) {
        //fprintf(stderr, "Marking simplified rule %s\n", _th_print_exp(r->rule));
        r->rule->rule_simplified = 1;
        r = r->next;
    }
}

void _th_clear_simplified(struct env *env)
{
    struct rule *r = env->simplified_rules;

    while (r) {
        r->rule->rule_simplified = 0;
        r = r->next;
    }
}

void _th_mark_blocked(struct env *env)
{
    struct rule *r = env->blocked_rules;

    //printf("mark simplified %x\n", env->simplified_rules);

    while (r) {
        //fprintf(stderr, "Marking simplified rule %s\n", _th_print_exp(r->rule));
        r->rule->rule_blocked = 1;
        r = r->next;
    }
}

void _th_clear_blocked(struct env *env)
{
    struct rule *r = env->blocked_rules;

    while (r) {
        r->rule->rule_blocked = 0;
        r = r->next;
    }
}

void _th_set_block_rule(int space, struct env *env, struct _ex_intern *rule)
{
    struct rule *r = (struct rule *)_th_alloc(space, sizeof(struct rule));
    r->next = env->blocked_rules;
    r->rule = rule;
    //if (env->simplified_rules) {
    //    printf("add_simplified_rule %x %x\n", r, r->next);
    //} else {
    //    printf("add_simplified_rule 0\n");
    //}

    env->blocked_rules = r;
}

struct _ex_intern *_th_get_block_rule(struct env *env)
{
//    return env->block_rule;
    return NULL;
}

struct _ex_intern *_th_add_contexts_to_cache(struct env *env, struct _ex_intern *tail)
{
    struct add_list *a = env->rewrite_chain;

    struct _ex_intern *br = _th_get_block_rule(env);

    //if (env->use_only_original) return tail;

    _zone_print0("Adding context rules");
    _tree_indent();
    _zone_print_exp("br", br);

    while (a) {
        //_zone_print2("orig %d %s", a->e->rule_original, _th_print_exp(a->e));
        if (!a->e->rule_blocked) {
            struct _ex_intern *e = _th_unmark_vars(env,a->e);
            //if (a->e->type != EXP_APPL) {
            //    fprintf(stderr, "%x %x %s\n", env, a, _th_print_exp(a->e));
            //    fflush(stderr);
            //}
            if (e->u.appl.args[0]->rewrite==NULL) {
                e->u.appl.args[0]->rewrite = e->u.appl.args[1];
                _zone_print_exp("Adding context rule to cache", a->e);
                e->u.appl.args[0]->next_cache = tail;
                tail = e->u.appl.args[0];
            }
        }
        a = a->next;
    }
    _tree_undent();
    return tail;
}

static struct env *last_env = NULL ;
static char *ppmark = NULL ;

struct _ex_intern *_th_get_exp_type(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *t;

    switch (e->type) {
        case EXP_APPL:
            if (e->u.appl.functor==INTERN_ITE) {
				return _th_get_exp_type(env,e->u.appl.args[1]);
			} else {
                t = _th_get_type(env,e->u.appl.functor);
                if (t==NULL) return 0;
                return t->u.appl.args[1];
			}
        case EXP_VAR:
            return _th_get_var_type(env,e->u.var);
        case EXP_RATIONAL:
            return _ex_real;
		case EXP_INTEGER:
			return _ex_int;
        default:
            return NULL;
    }
}

struct _ex_intern *_th_get_var_type(struct env *env,unsigned v)
{
	struct var_type *vars = env->variables;

	while (vars != NULL) {
		if (vars->var==v) return vars->type;
		vars = vars->next;
	}

	return env->default_type;
}

void _th_set_var_type(struct env *env, unsigned v, struct _ex_intern *type)
{
	struct var_type *var = (struct var_type *)_th_alloc(ENVIRONMENT_SPACE,sizeof(struct var_type));
	
	var->var = v;
	var->type = type;
	var->next = env->variables;
	env->variables = var;
}

void _th_copy_var_types(struct env *env, struct env *parent_env)
{
	struct var_type *vars = parent_env->variables;

	while (vars) {
		_th_set_var_type(env,vars->var,vars->type);
		vars = vars->next;
	}
}

void _th_set_default_var_type(struct env *env, struct _ex_intern *type)
{
	env->default_type = type;
}


struct state_checks *_th_get_state_checks(struct env *env)
{
    return env->state_checks ;
}

void _th_set_state_checks(struct env *env, struct state_checks *state_checks)
{
    env->state_checks = state_checks ;
}

struct trie_l *_th_get_trie(struct env *env)
{
    if (env != last_env) return NULL ;
    if (env->rebuild_trie) return NULL ;
    return env->pptrie ;
}

struct _ex_intern *_th_get_first_rule(struct env *env, struct rule **cr)
{
    if (env->rules) {
        *cr = env->rules->next ;
        return env->rules->rule ;
    } else {
        *cr = NULL ;
        return NULL ;
    }
}

int _th_rule_in_context(struct env *env, struct _ex_intern *rule)
{
	struct rule *r = env->context_rules;

	while (r) {
        //_tree_print_exp("Rule", rule);
        //_tree_print_exp("Checking against", r->rule);
		if (r->rule==rule) return 1;
		r = r->next;
	}

	return 0;
}

struct _ex_intern *_th_get_first_context_rule(struct env *env, struct rule **cr)
{
    if (env->context_rules) {
        *cr = env->context_rules->next ;
        return env->context_rules->rule ;
    } else {
        *cr = NULL ;
        return NULL ;
    }
}

struct _ex_intern *_th_get_next_rule(struct env *env, struct rule **cr)
{
    if (*cr) {
        struct _ex_intern *r = (*cr)->rule ;
        *cr = (*cr)->next ;
        return r ;
    } else {
        return NULL ;
    }
}

void _th_mark_tested(struct env *env, struct _ex_intern *e)
{
    _th_disc_mark_tested(env->context_properties, e) ;
}

void _th_mark_used(struct env *env, struct _ex_intern *e)
{
    _th_disc_mark_used(env->context_properties, e) ;
}

struct _ex_intern *_th_get_context_rule_set(struct env *env)
{
    return _th_get_small_set(env,env->context_properties) ;
}

char *_th_get_mark()
{
    return ppmark ;
}

void _th_set_trie_mark(struct env *env, struct trie_l *trie, char *mark)
{
    ppmark = mark ;
    env->pptrie = trie ;
    env->rebuild_trie = 0 ;
    last_env = env ;
}

struct env *_th_new_empty_env(int s, int size)
{
    struct env *e ;
    int i;

    if (size < 1000) size = 1000 ;
    e = (struct env *)_th_alloc(s,sizeof(struct env)+(size-1)*sizeof(struct symbol_info *)) ;
    e->symbol_size = size ;
    while(--size >=0) {
        e->table[size] = NULL ;
    }
#ifdef CHECK_CACHE
    e->cache_installed = 1;
#endif
    e->slack = 0;
    e->space = s;
    e->head = e->tail = NULL;
    e->all_properties = _th_new_disc(s) ;
    e->apply_properties = _th_new_disc(s) ;
    e->derive_properties = _th_new_disc(s) ;
    e->augment_properties = _th_new_disc(s) ;
    e->context_properties = _th_new_small(s) ;
    e->apply_context_properties = _th_new_small(s) ;
    e->macro_properties = _th_new_disc(s) ;
    e->context_stack = NULL ;
    e->pp_directives = NULL ;
    e->rules = NULL ;
	e->context_rules = NULL ;
    e->rebuild_trie = 1 ;
    e->pptrie = NULL ;
    e->context_level = 0 ;
    e->state_checks = NULL ;
    e->first_context_mark = NULL ;
	e->variables = NULL ;
    e->rewrite_chain = NULL ;
    e->default_type = NULL;
    //fprintf(stderr, "Assigning rewrite_chain 3 %x %x\n", e, e->rewrite_chain);
    e->simplified_rules = NULL ;
    e->blocked_rules = NULL ;
	e->rule_operand_table = (struct rule_operand_list **)_th_alloc(s,sizeof(struct rule_operand_list *) * RULE_OPERAND_HASH);
	e->rule_double_operand_table = (struct rule_double_operand_list **)_th_alloc(s,sizeof(struct rule_double_operand_list *) * RULE_OPERAND_HASH);
	for (i = 0; i < RULE_OPERAND_HASH; ++i) {
		e->rule_operand_table[i] =  NULL;
		e->rule_double_operand_table[i] =  NULL;
	}
	e->var_solve_table = (struct var_solve_list **)_th_alloc(s,sizeof(struct var_solve_list *) * RULE_OPERAND_HASH);
	for (i = 0; i < VAR_SOLVE_HASH; ++i) {
		e->var_solve_table[i] =  NULL;
	}
	e->min_table = (struct min_max_list **)_th_alloc(s,sizeof(struct min_max_list *) * MIN_MAX_HASH);
	e->max_table = (struct min_max_list **)_th_alloc(s,sizeof(struct min_max_list *) * MIN_MAX_HASH);
    e->diff_node_table = NULL;
    e->simplex = NULL;
	for (i = 0; i < MIN_MAX_HASH; ++i) {
		e->min_table[i] = e->max_table[i] = NULL;
	}
    e->term_groups = (struct term_group **)_th_alloc(s,sizeof(struct term_group *) * TERM_HASH);
    e->term_functors = (struct term_group **)_th_alloc(s,sizeof(struct term_group *) * TERM_HASH);
    e->root_vars = (struct root_var **)_th_alloc(s,sizeof(struct root_var *) * TERM_HASH);
    for (i = 0; i < TERM_HASH; ++i) {
        e->term_groups[i] = NULL;
        e->term_functors[i] = NULL;
        e->root_vars[i] = NULL;
    }

    return e ;
}

static void check_has_top_var(struct env *env, struct _ex_intern *e)
{
    int i ;
    int j ;

    if (e->u.appl.args[0]->type != EXP_APPL) return ;

    e->no_top_var = 1 ;
    for (i = 0; i < e->u.appl.args[0]->u.appl.count; ++i) {
        if (e->u.appl.args[0]->u.appl.args[i]->type == EXP_VAR) {
            if (_th_is_free_in(e->u.appl.args[2],e->u.appl.args[0]->u.appl.args[i]->u.var)) goto cont;
            for (j = 0; j < e->u.appl.args[0]->u.appl.count; ++j) {
                if (i != j) {
                    if (_th_is_free_in(e->u.appl.args[0]->u.appl.args[j],
                        e->u.appl.args[0]->u.appl.args[i]->u.var)) goto cont ;
                }
            }
            e->no_top_var = 0 ;
            return ;
cont: ;
        }
    }
    return ;
}

static void add_to_operand_table(int s, struct env *env, struct _ex_intern *rule)
{
	struct _ex_intern *e;

	e = _th_extract_relation(env,rule);

	if (_th_is_binary_term(env,e)) {
		struct _ex_intern *l = _th_unmark_vars(env,_th_get_left_operand(env,e));
		struct _ex_intern *r = _th_unmark_vars(env,_th_get_right_operand(env,e));
		int hash = (((int)l)/4+((int)r)/4)%RULE_OPERAND_HASH;
		struct rule_double_operand_list *rol;
        //_zone_print_exp("Adding prop expression", e);
        //_zone_print_exp("left ",l);
        //_zone_print_exp("right", r);
		rol = (struct rule_double_operand_list *)_th_alloc(s,sizeof(struct rule_double_operand_list));
		rol->next = env->rule_double_operand_table[hash];
		env->rule_double_operand_table[hash] = rol;
		rol->left_operand = l;
		rol->right_operand = r;
		rol->rule = rule;

        if (e->u.appl.functor != INTERN_EQUAL || rule->u.appl.functor != INTERN_ORIENTED_RULE ||
            rule->u.appl.args[1]==_ex_true) {
            
            if (l->type != EXP_APPL || l->u.appl.functor != INTERN_NAT_PLUS) {
                struct rule_operand_list *rol;
                l = _th_get_core(env,l);
                hash = (((int)l)/4)%RULE_OPERAND_HASH;
                rol = (struct rule_operand_list *)_th_alloc(s,sizeof(struct rule_operand_list));
                rol->next = env->rule_operand_table[hash];
                env->rule_operand_table[hash] = rol;
                rol->operand = l;
                rol->rule = rule;
            }
            
            if (r->type != EXP_APPL || r->u.appl.functor != INTERN_NAT_PLUS) {
                struct rule_operand_list *rol;
                r = _th_get_core(env,r);
                hash = (((int)r)/4)%RULE_OPERAND_HASH;
                rol = (struct rule_operand_list *)_th_alloc(s,sizeof(struct rule_operand_list));
                rol->next = env->rule_operand_table[hash];
                env->rule_operand_table[hash] = rol;
                rol->operand = r;
                rol->rule = rule;
            }
        }
	}
}

static void add_to_var_solve_table(int s, struct env *env, struct _ex_intern *e)
{
    int hash;
	unsigned var;
    struct _ex_intern *term;
    unsigned *fv;
	int count;
    struct var_solve_list *vsl;

	if (e->u.appl.args[2] != _ex_true) return;

	if (e->u.appl.args[1]==_ex_true) {
		if (e->u.appl.args[0]->type==EXP_APPL && e->u.appl.args[0]->u.appl.functor==INTERN_EQUAL) {
			e = e->u.appl.args[0];
		} else {
			return;
		}
	}

	if (e->u.appl.args[0]->type==EXP_MARKED_VAR) {
		var = e->u.appl.args[0]->u.marked_var.var;
		term = e->u.appl.args[1];
	} else if (e->u.appl.args[1]->type==EXP_MARKED_VAR) {
		var = e->u.appl.args[1]->u.marked_var.var;
		term = e->u.appl.args[0];
	} else {
		return;
	}

	if (_th_is_marked_in(term,var)) return;
    fv = _th_get_free_vars(term,&count);
	if (count) return;

	hash = (((int)var)/4)%RULE_OPERAND_HASH;
	vsl = (struct var_solve_list *)_th_alloc(s,sizeof(struct var_solve_list));
	vsl->next = env->var_solve_table[hash];
	env->var_solve_table[hash] = vsl;
	vsl->var = var;
	vsl->rule = term;
}

static int mless(struct _ex_intern *s, struct _ex_intern *l)
{
#ifdef _DEBUG
    if (s->type != l->type) {
        fprintf(stderr, "Illegal min max types\n");
        exit(1);
    }
#endif
    if (s->type==EXP_INTEGER) {
        return _th_big_less(s->u.integer,l->u.integer);
    } else if (s->type==EXP_RATIONAL) {
        return _th_rational_less(s,l);
    } else {
        fprintf(stderr, "Illegal min max types\n");
        exit(1);
    }
}

static void add_to_min_max_tables(int s, struct env *env, struct _ex_intern *e)
{
    unsigned *fv;
    int count;

    //printf("Min Max %d %s\n", _tree_zone, _th_print_exp(e));

    //_zone_print_exp("Adding min_max", e);

    if (e->u.appl.args[1]==_ex_true && e->u.appl.args[2]==_ex_true) {
        struct _ex_intern *f = e->u.appl.args[0];
        unsigned one[2] = { 1, 1 };
        if (f->type==EXP_APPL && (f->u.appl.functor==INTERN_NAT_LESS || f->u.appl.functor==INTERN_RAT_LESS)) {
            fv = _th_get_free_vars(e, &count);
            if (count) return;
            //printf("    Here10\n");
            if (f->u.appl.args[0]->type==EXP_INTEGER || f->u.appl.args[0]->type==EXP_RATIONAL) {
                struct _ex_intern *exp = _th_unmark_vars(env,f->u.appl.args[1]);
                int hash = (((int)exp)/4)%MIN_MAX_HASH;
                struct min_max_list *min = env->min_table[hash];
                //fprintf(stderr, "Adding min %s\n", _th_print_exp(f));
                while (min != NULL) {
                    if (min->exp==exp) break;
                    min = min->next;
                }
                //if (min) fprintf(stderr, "Existing min %s\n", _th_print_exp(min->value));
                //fprintf(stderr, "New min %s\n", _th_print_exp(f->u.appl.args[0]));
                if (min==NULL || mless(min->value,f->u.appl.args[0]) || (min->value==f->u.appl.args[0] && min->inclusive)) {
                    min = (struct min_max_list *)_th_alloc(s,sizeof(struct min_max_list));
                    min->next = env->min_table[hash];
                    env->min_table[hash] = min;
                    min->exp = exp;
                    min->value = f->u.appl.args[0];
                    if (min->value->type==EXP_INTEGER) {
                        min->value = _ex_intern_integer(_th_big_add(min->value->u.integer,_ex_one->u.integer));
                        min->inclusive = 1;
                    } else {
                        min->inclusive = 0;
                    }
                    //printf("Adding min %s\n", _th_print_exp(min->exp));
                    //printf("     value %s\n", _th_print_exp(min->value));
                }
            } else if (f->u.appl.args[1]->type==EXP_INTEGER || f->u.appl.args[1]->type==EXP_RATIONAL) {
                struct _ex_intern *exp = _th_unmark_vars(env,f->u.appl.args[0]);
                int hash = (((int)exp)/4)%MIN_MAX_HASH;
                struct min_max_list *max = env->max_table[hash];
                //fprintf(stderr, "Adding max %s\n", _th_print_exp(f));
                while (max != NULL) {
                    if (max->exp==exp) break;
                    max = max->next;
                }
                //if (max) fprintf(stderr, "Existing max %s\n", _th_print_exp(max->value));
                //fprintf(stderr, "New max %s\n", _th_print_exp(f->u.appl.args[1]));
                if (max==NULL || mless(f->u.appl.args[1],max->value) || (max->value==f->u.appl.args[1] && max->inclusive)) {
                    max = (struct min_max_list *)_th_alloc(s,sizeof(struct min_max_list));
                    max->next = env->max_table[hash];
                    env->max_table[hash] = max;
                    max->exp = exp;
                    max->value = f->u.appl.args[1];
                    if (max->value->type==EXP_INTEGER) {
                        max->value = _ex_intern_integer(_th_big_sub(max->value->u.integer,_ex_one->u.integer));
                        max->inclusive = 1;
                    } else {
                        max->inclusive = 0;
                    }
                }
            }
        } else if (f->type==EXP_APPL && f->u.appl.functor==INTERN_EQUAL) {
            struct _ex_intern *g = NULL, *h = NULL;
            //printf("    Here11\n");
            if (f->u.appl.args[0]->type==EXP_INTEGER || f->u.appl.args[0]->type==EXP_RATIONAL) {
                g = f->u.appl.args[0];
                h = f->u.appl.args[1];
            } else if (f->u.appl.args[1]->type==EXP_INTEGER || f->u.appl.args[0]->type==EXP_RATIONAL) {
                g = f->u.appl.args[1];
                h = f->u.appl.args[0];
            }
            if (h) {
                int hash;
                struct min_max_list *m;
                h = _th_unmark_vars(env,h);
                hash = (((int)h)/4)%MIN_MAX_HASH;
                m = env->max_table[hash];
                fv = _th_get_free_vars(e, &count);
                if (count) return;
                while (m != NULL) {
                    if (m->exp==h) break;
                    m = m->next;
                }
                if (m==NULL || mless(g,m->value)) {
                    m = (struct min_max_list *)_th_alloc(s,sizeof(struct min_max_list));
                    m->next = env->max_table[hash];
                    env->max_table[hash] = m;
                    m->exp = h;
                    m->value = g;
                    m->inclusive = 1;
                }
                m = env->min_table[hash];
                while (m != NULL) {
                    if (m->exp==h) break;
                    m = m->next;
                }
                if (m==NULL || mless(m->value,g)) {
                    m = (struct min_max_list *)_th_alloc(s,sizeof(struct min_max_list));
                    m->next = env->min_table[hash];
                    env->min_table[hash] = m;
                    m->exp = h;
                    m->value = g;
                    m->inclusive = 1;
                }
            }
        }
    } else if (e->u.appl.args[1]==_ex_false && e->u.appl.args[2]==_ex_true) {
        struct _ex_intern *f = e->u.appl.args[0];
        if (f->type==EXP_APPL && (f->u.appl.functor==INTERN_NAT_LESS || f->u.appl.functor==INTERN_RAT_LESS)) {
            //fprintf(stderr, "Adding %s\n", _th_print_exp(e));
            fv = _th_get_free_vars(e, &count);
            if (count) return;
            //printf("    Here10\n");
            if (f->u.appl.args[0]->type==EXP_INTEGER || f->u.appl.args[0]->type==EXP_RATIONAL) {
                struct _ex_intern *m = f->u.appl.args[0];
                struct _ex_intern *exp = _th_unmark_vars(env,f->u.appl.args[1]);
                int hash = (((int)exp)/4)%MIN_MAX_HASH;
                struct min_max_list *max = env->max_table[hash];
                while (max != NULL) {
                    if (max->exp==exp) break;
                    max = max->next;
                }
                //if (max) fprintf(stderr, "Existing max %s\n", _th_print_exp(max->value));
                //fprintf(stderr, "New max %s\n", _th_print_exp(m));
                if (max==NULL || mless(m,max->value)) {
                    max = (struct min_max_list *)_th_alloc(s,sizeof(struct min_max_list));
                    max->next = env->max_table[hash];
                    env->max_table[hash] = max;
                    max->exp = exp;
                    max->value = m;
                    max->inclusive = 1;
                    //printf("Adding min %s\n", _th_print_exp(min->exp));
                    //printf("     value %s\n", _th_print_exp(min->value));
                }
            } else if (f->u.appl.args[1]->type==EXP_INTEGER || f->u.appl.args[1]->type==EXP_RATIONAL) {
                struct _ex_intern *m = f->u.appl.args[1];
                struct _ex_intern *exp = _th_unmark_vars(env,f->u.appl.args[0]);
                int hash = (((int)exp)/4)%MIN_MAX_HASH;
                struct min_max_list *min = env->min_table[hash];
                while (min != NULL) {
                    if (min->exp==exp) break;
                    min = min->next;
                }
                //if (min) fprintf(stderr, "Existing min %s\n", _th_print_exp(min->value));
                //fprintf(stderr, "New min %s\n", _th_print_exp(m));
                if (min==NULL || mless(min->value,m)) {
                    min = (struct min_max_list *)_th_alloc(s,sizeof(struct min_max_list));
                    min->next = env->min_table[hash];
                    env->min_table[hash] = min;
                    min->exp = exp;
                    min->value = m;
                    min->inclusive = 1;
                }
            }
        }
    } else if ((e->u.appl.args[1]->type==EXP_INTEGER || e->u.appl.args[1]->type==EXP_RATIONAL) && e->u.appl.args[2]==_ex_true) {
        struct _ex_intern *g, *h;
        int hash;
        struct min_max_list *m;
        //printf("    Here12\n");
        fv = _th_get_free_vars(e, &count);
        if (count) return;
        g = e->u.appl.args[1];
        h = e->u.appl.args[0];
        h = _th_unmark_vars(env,h);
        hash = (((int)h)/4)%MIN_MAX_HASH;
        m = env->max_table[hash];
        while (m != NULL) {
            if (m->exp==h) break;
            m = m->next;
        }
        if (m==NULL || mless(g,m->value)) {
            m = (struct min_max_list *)_th_alloc(s,sizeof(struct min_max_list));
            m->next = env->max_table[hash];
            env->max_table[hash] = m;
            m->exp = h;
            m->value = g;
            m->inclusive = 1;
        }
        m = env->min_table[hash];
        while (m != NULL) {
            if (m->exp==h) break;
            m = m->next;
        }
        if (m==NULL || mless(m->value,g)) {
            m = (struct min_max_list *)_th_alloc(s,sizeof(struct min_max_list));
            m->next = env->min_table[hash];
            env->min_table[hash] = m;
            m->exp = h;
            m->value = g;
            m->inclusive = 1;
        }
    }
}

static void _add_property(int s, struct env *env, struct _ex_intern *e, int priority)
{
    struct _ex_intern *args[3], *r ;

    _zone_print_exp("Adding property %s", e);

    if (e->type==EXP_APPL &&
        e->u.appl.functor == INTERN_AND) {
        int i ;
        for (i = 0; i < e->u.appl.count; ++i) {
            _add_property(s, env, e->u.appl.args[i], priority) ;
        }
        return ;
    }

    //printf("Adding property %s with priority %d\n", _th_print_exp(e), priority) ;

    if (e->type==EXP_APPL && e->u.appl.functor==INTERN_HEURISTIC && e->u.appl.count==4) {
        struct add_list *al = (struct add_list *)_th_alloc(s,sizeof(struct add_list));
        struct add_list *ale;
        al->next = NULL;
        if (env->heuristics==NULL) {
            env->heuristics = al;
        } else {
            ale = env->heuristics;
            while (ale->next != NULL) ale = ale->next;
            ale->next = al;
        }
        al->e = e;
        return;
    }

    if (e->type != EXP_APPL || e->u.appl.count != 3 ||
        (e->u.appl.functor != INTERN_ORIENTED_RULE &&
         e->u.appl.functor != INTERN_FORCE_ORIENTED &&
         e->u.appl.functor != INTERN_UNORIENTED_RULE &&
         e->u.appl.functor != INTERN_DOUBLE_ARROW &&
         e->u.appl.functor != INTERN_INFERENCE &&
         e->u.appl.functor != INTERN_MACRO_ARROW)) {
        int i = 0 ;
        if (e==_ex_true) return ;
        fprintf(stderr,"Warning: Illegal rule format %s\n", _th_print_exp(e)) ;
        exit(1) ;
    }
#ifdef _DEBUG
    if (_th_has_duplicate_var(e->u.appl.args[0])) {
        fprintf(stderr, "Warning: Duplicate variable in left hand side of %s\n", _th_print_exp(e)) ;
    }
#endif
    if (e->u.appl.functor==INTERN_MACRO_ARROW) {
        _th_add_disc(s,env->macro_properties,e,priority) ;
    } else if (e->u.appl.functor==INTERN_INFERENCE) {
        _th_add_disc(s,env->augment_properties,e,priority) ;
    } else if (e->u.appl.functor==INTERN_DOUBLE_ARROW) {
        _th_add_disc(s,env->derive_properties,e,priority) ;
    } else {
        args[0] = e->u.appl.args[1] ;
        args[1] = e->u.appl.args[0] ;
        args[2] = e->u.appl.args[2] ;
        r = _ex_intern_appl(e->u.appl.functor,3,args) ;
        check_has_top_var(env,e) ;
        check_has_top_var(env,r) ;
        if (e->u.appl.functor == INTERN_ORIENTED_RULE || e->u.appl.functor == INTERN_FORCE_ORIENTED) {
            struct rule *r = (struct rule *)_th_alloc(s,sizeof(struct rule)) ;
            r->next = env->rules ;
            env->rules = r ;
            r->rule = e ;
            _th_add_disc(s,env->apply_properties,e,priority) ;
        }
        _th_add_disc(s,env->all_properties,e,priority) ;
        _th_add_disc(s,env->all_properties,r,priority) ;
    }

	//printf("Adding prop %s\n", _th_print_exp(e));

	//add_to_operand_table(s,env,e);
    add_to_min_max_tables(s, env, e);

    if (e->u.appl.args[1]==_ex_true && e->u.appl.args[2]==_ex_true) {
        e = _th_unmark_vars(env,e->u.appl.args[0]);
        add_rless_term(env, e);
    } else if (e->u.appl.args[1]==_ex_false && e->u.appl.args[2]==_ex_true) {
        e = _th_unmark_vars(env,_ex_intern_appl1_env(env,INTERN_NOT,e->u.appl.args[0]));
        add_rless_term(env, e);
    }
}

void _th_add_property(struct env *env, struct _ex_intern *e)
{
    if (e->type==EXP_APPL &&
        e->u.appl.functor == INTERN_PRIORITY &&
        e->u.appl.count == 2 &&
        e->u.appl.args[0]->type == EXP_INTEGER) {
        _add_property(env->space,env,e->u.appl.args[1],e->u.appl.args[0]->u.integer[1]) ;
    } else {
        _add_property(env->space,env,e,0) ;
    }
}

static struct symbol_info *_get_symbol_info(int s, struct env *env, unsigned symbol)
{
    struct symbol_info *info = env->table[symbol%env->symbol_size] ;
    int i ;

    while (info != NULL && info->symbol != symbol) info = info->next ;

    if (info == NULL) {
        if (s < 0) {
            return NULL ;
        } else {
            //printf("New info for %s\n", _th_intern_decode(symbol));
            info = (struct symbol_info *)_th_alloc(INTERN_SPACE,sizeof(struct symbol_info)) ;

            info->next = env->table[symbol%env->symbol_size] ;
            env->table[symbol%env->symbol_size] = info ;

            info->type = info->var_type = info->definition = info->type_definition = NULL ;
            info->is_finite_type = info->is_finite_constructor = info->is_constructor = 0 ;
            info->attribute_flags = 0;
            info->attr = NULL ;
            info->symbol = info->equal_group = symbol ;
            for (i = 0; i < PRECEDENCE_HASH_SIZE; ++i) {
                info->smaller[i] = info->larger[i] = NULL ;
            }
            info->minor_smaller = info->minor_larger = NULL ;
            info->last_entered_minor_smaller = info->last_entered_minor_larger = 0xffffffff ;
            info->mark = 1 ;
            info->prex_info = NULL ;
            info->lex_order = NULL ;
            info->context_level = 0 ;
            info->type_functor = NULL ;
        }
    }

    return info ;
}

static int _add_context_property(int s, struct env *env, struct _ex_intern *e, int priority)
{
    struct _ex_intern *args[3], *r ;
    int res ;
    unsigned int *mv ;
    int c ;
    struct rule *rule;

    _zone_print_exp("Adding context property", e);

    //printf("Adding property %s\n", _th_print_exp(e));
    //fflush(stdout);
    //if (e->u.appl.args[0]->type==EXP_MARKED_VAR && !strcmp(_th_intern_decode(e->u.appl.args[0]->u.marked_var.var),"_slack8") &&
    //    e->u.appl.args[1]->type==EXP_RATIONAL) {
    //    exit(1);
    //}
    //_zone_print_exp("Adding context property", e);
    //_th_get_free_vars(e, &c);
    //if (c) {
    //    fprintf(stderr, "Illegal rule being added %s\n", _th_print_exp(e));
    //    exit(1);
    //}
    if (e->type==EXP_APPL &&
        e->u.appl.functor == INTERN_AND) {
        int i ;
        res = 0 ;
        for (i = 0; i < e->u.appl.count; ++i) {
            if (_add_context_property(s, env, e->u.appl.args[i], priority)) res = 1 ;
        }
        return res ;
    }

    if (e->type != EXP_APPL || e->u.appl.count != 3 ||
        (e->u.appl.functor != INTERN_ORIENTED_RULE &&
         e->u.appl.functor != INTERN_UNORIENTED_RULE &&
         e->u.appl.functor != INTERN_FORCE_ORIENTED)) {
        int i = 0 ;
        if (e==_ex_true) return 0 ;
        fprintf(stderr,"Illegal rule format 3 %s\n", _th_print_exp(e)) ;
        fflush(stderr);
        exit(1) ;
    }

    mv = _th_get_marked_vars(e,&c) ;

    while (--c >= 0) {
        struct symbol_info *info ;
        info = _get_symbol_info(s,env,mv[c]) ;
        if (!info->context_level) {
            //printf("Adding context_mark for %s\n", _th_intern_decode(mv[c]));
            info->context_level = env->context_level + 1 ;
            info->next_context_mark = env->first_context_mark ;
            env->first_context_mark = info ;
        }
    }

    args[0] = e->u.appl.args[1] ;
    args[1] = e->u.appl.args[0] ;
    args[2] = e->u.appl.args[2] ;
    r = _ex_intern_appl(INTERN_UNORIENTED_RULE,3,args) ;
    check_has_top_var(env,e) ;
    check_has_top_var(env,r) ;

    rule = (struct rule *)_th_alloc(s,sizeof(struct rule)) ;
    rule->next = env->context_rules ;
    rule->rule = e;
	env->context_rules = rule;

    if (e->u.appl.functor==INTERN_ORIENTED_RULE || e->u.appl.functor==INTERN_FORCE_ORIENTED) {
        if (e->u.appl.args[1]->type==EXP_INTEGER) {
            struct rule *r = env->context_rules;
            while (r) {
                if (r->rule->u.appl.args[0]==e->u.appl.args[0]) {
                    if (r->rule->u.appl.args[1]->type==EXP_INTEGER &&
                        r->rule->u.appl.args[1] != e->u.appl.args[1]) {
                        printf("Contradiction found\n");
                        exit(1);
                    }
                }
                r = r->next;
            }
        }
        if (e->u.appl.args[2]==_ex_true) {
            unsigned *fv = _th_get_free_vars(e->u.appl.args[0],&c);
            //_zone_print0("Here1");
            if (!c) {
                //_zone_print0("Here2");
                //struct _ex_intern *t = _th_unmark_vars(env,e);
                struct add_list *a = (struct add_list *)_th_alloc(s,sizeof(struct add_list));
                //_zone_print0("Here3");
                //fprintf(stderr, "Adding %x %x %s\n", env, a, _th_print_exp(t));
                //fflush(stderr);
                a->next = env->rewrite_chain;
                env->rewrite_chain = a;
                a->e = e;
            }
            res = _th_add_small(s,env,env->apply_context_properties,e,priority);
        } else {
            //_zone_print0("Here4");
            res = _th_add_small(s,env,env->apply_context_properties,e,priority);
        }
    } else {
        res = 0 ;
    }
    res = (_th_add_small(s,env,env->context_properties,e,priority) || res) ;
    res = (_th_add_small(s,env,env->context_properties,r,priority) || res) ;

	//printf("Adding property %s\n", _th_print_exp(e));

	add_to_operand_table(s,env,e);
	add_to_var_solve_table(s,env,e);
    add_to_min_max_tables(s, env, e);

    if (e->u.appl.args[1]==_ex_true && e->u.appl.args[2]==_ex_true) {
        e = _th_unmark_vars(env,e->u.appl.args[0]);
        add_rless_term(env, e);
    } else if (e->u.appl.args[1]==_ex_false && e->u.appl.args[2]==_ex_true) {
        e = _th_unmark_vars(env,_ex_intern_appl1_env(env,INTERN_NOT,e->u.appl.args[0]));
        add_rless_term(env, e);
    }
    return res ;
}

void check_merges(struct env *env)
{
	int i;
    struct add_list *expl;

	for (i = 0; i < DIFF_NODE_HASH; ++i) {
		struct diff_node *node = env->diff_node_table[i];
		while (node) {
			if (node->eq_merge) {
				struct _ex_intern *e = _ex_intern_equal(env,_ex_real,_ex_intern_appl2_env(env,INTERN_RAT_PLUS,node->e,node->eq_offset),node->eq_merge->e);
				struct _ex_intern *x;
				if ((x = _th_check_cycle_rless(env,e,&expl))!=_ex_true) {
					printf("Merge failure %s", _th_print_exp(e));
					printf(" to %s %x\n", _th_print_exp(x), x);
					_th_display_difference_table(env);
					exit(1);
				}
			}
			node = node->next;
		}
	}
}

static struct _ex_intern *get_a_path(struct env *env, struct diff_node *n1, struct diff_node *n2, struct _ex_intern *offset, struct _ex_intern *limit)
{
	struct diff_edge *e;
	//printf("    Visiting %s\n", _th_print_exp(n1->e));
	if (n1->visited) return NULL;
	if (n1==n2 && offset==limit) return offset;
	n1->visited = 1;
	e = n1->edges;
	while (e) {
		struct _ex_intern *o = _th_add_rationals(offset,e->offset);
		struct _ex_intern *r = get_a_path(env,e->target,n2,o,limit);
		if (r) {
			n1->visited = 0;
			return r;
		}
		e = e->next;
	}
	n1->visited = 0;
	return NULL;
}

static void check_merge_paths(struct env *env)
{
	int i, j;
    struct diff_node *n1, *n2, *n, *m1, *m2;
    struct _ex_intern *offset, *x;

	for (i = 0; i < DIFF_NODE_HASH; ++i) {
		n = env->diff_node_table[i];
		while (n) {
			n->visited = 0;
			n = n->next;
		}
	}

	for (i = 0; i < DIFF_NODE_HASH; ++i) {
		n1 = env->diff_node_table[i];
		while (n1) {
        	for (j = 0; j < DIFF_NODE_HASH; ++j) {
		        n2 = env->diff_node_table[j];
		        while (n2) {
					if (n1 != n2) {
						m1 = n1;
						offset = _ex_intern_small_rational(0,1);
						while (m1->eq_merge) {
							offset = _th_add_rationals(offset,m1->eq_offset);
							m1 = m1->eq_merge;
						}
						m2 = n2;
						while (m2->eq_merge) {
							offset = _th_subtract_rationals(offset,m2->eq_offset);
							m2 = m2->eq_merge;
						}
						//printf("Testing %s to", _th_print_exp(n1->e));
						//printf(" %s\n", _th_print_exp(n2->e));
						if (m1==m2 && (x = get_a_path(env,n1,n2,_ex_intern_small_rational(0,1),offset)) != offset) {
							printf("Illegal path %s to ", _th_print_exp(n1->e));
							printf("%s (", _th_print_exp(n2->e));
							printf("%s)\n", _th_print_exp(offset));
							printf("path offset = %s\n", _th_print_exp(x));
							m1 = n1;
							printf("Merge 1\n");
							while (m1) {
								printf("    %s\n", _th_print_exp(m1->e));
								if (m1->eq_offset) printf("        %s\n", _th_print_exp(m1->eq_offset));
								m1 = m1->eq_merge;
							}
							m1 = n2;
							printf("Merge 2\n");
							while (m1) {
								printf("    %s\n", _th_print_exp(m1->e));
								if (m1->eq_offset) printf("        %s\n", _th_print_exp(m1->eq_offset));
								m1 = m1->eq_merge;
							}
							_th_display_difference_table(env);
							exit(1);
						}
					}
					n2 = n2->next;
           		}
	        }
			n1 = n1->next;
		}
	}
}

int _th_add_predicate(struct env *env, struct _ex_intern *e, struct add_list **expl)
{
    int res = 0;

    printf("********** ADDING DOMAIN TERM %s\n", _th_print_exp(e));
	//check_integrity(env,"begin add predicate");

    //struct _ex_intern *p = _th_derive_prepare(env,_th_mark_vars(env,e));

    //if (p) {
    //    add_to_operand_table(env->space,env,p);
	//    add_to_var_solve_table(env->space,env,p);
    //    add_to_min_max_tables(env->space, env,p);
    //}

    //printf("Adding %s\n", _th_print_exp(e));
    if (env->diff_node_table) res = add_rless_term(env, e);

	//if (!res) check_merges(env);

    if (!res && env->simplex) {
        explanation = _th_add_equation(env->simplex,e);
        //if (res) {
        //    fprintf(stderr, "Simplex failure\n");
        //    exit(1);
        //}
        //if (res && expl) *expl = NULL;
		if (explanation) res = 1;
    }

	if (expl && res) {
        *expl = explanation;
	}
	if (explanation) {
		printf("Fail explanation\n");
		while (explanation) {
			printf("    %s\n", _th_print_exp(explanation->e));
			explanation = explanation->next;
		}
    }

	//_th_display_difference_table(env);
    //check_integrity(env,"end add predicate");
    //printf("Done\n");

	//check_merge_paths(env);

    return res;
}

struct _ex_intern *_th_get_first_rule_by_operands(struct env *env, struct _ex_intern *l, struct _ex_intern *r, struct rule_double_operand_list **iter)
{
	int hash = (((int)l)/4+((int)r)/4)%RULE_OPERAND_HASH;
	struct rule_double_operand_list *rol = env->rule_double_operand_table[hash];

	while (rol) {
		if ((rol->left_operand==l && rol->right_operand==r) ||
			(rol->left_operand==r && rol->right_operand==l)) {
            *iter = rol->next;
			return rol->rule;
		}
		rol = rol->next;
	}
	return NULL;
}

struct _ex_intern *_th_get_next_rule_by_operands(struct _ex_intern *l, struct _ex_intern *r, struct rule_double_operand_list **iter)
{
	struct rule_double_operand_list *rol = *iter;

	while (rol) {
		if ((rol->left_operand==l && rol->right_operand==r) ||
			(rol->left_operand==r && rol->right_operand==l)) {
            *iter = rol->next;
			return rol->rule;
		}
		rol = rol->next;
	}
	return NULL;
}

struct _ex_intern *_th_get_first_rule_by_operand(struct env *env, struct _ex_intern *oper, struct rule_operand_list **iter)
{
	int hash = (((int)oper)/4)%RULE_OPERAND_HASH;
	struct rule_operand_list *rol = env->rule_operand_table[hash];

	while (rol) {
		if (rol->operand==oper) {
            *iter = rol->next;
			return rol->rule;
		}
		rol = rol->next;
	}
	return NULL;
}

struct _ex_intern *_th_get_next_rule_by_operand(struct _ex_intern *oper, struct rule_operand_list **iter)
{
	struct rule_operand_list *rol = *iter;

	while (rol) {
		if (rol->operand==oper) {
            *iter = rol->next;
			return rol->rule;
		}
		rol = rol->next;
	}
	return NULL;
}

struct _ex_intern *_th_get_first_rule_by_var_solve(struct env *env, unsigned var, struct var_solve_list **iter)
{
	int hash = (((int)var)/4)%VAR_SOLVE_HASH;
	struct var_solve_list *vsl = env->var_solve_table[hash];

	while (vsl) {
		if (vsl->var==var) {
            *iter = vsl->next;
			return vsl->rule;
		}
		vsl = vsl->next;
	}
	return NULL;
}

struct _ex_intern *_th_get_next_rule_by_var_solve(unsigned var, struct var_solve_list **iter)
{
	struct var_solve_list *vsl = *iter;

	while (vsl) {
		if (vsl->var==var) {
            *iter = vsl->next;
			return vsl->rule;
		}
		vsl = vsl->next;
	}
	return NULL;
}

int _th_inclusive;
struct _ex_intern *_th_get_upper_bound(struct env *env, struct _ex_intern *var)
{
	int hash;
	struct min_max_list *m;
	//var = _th_mark_vars(env,var);
	hash = (((int)var)/4)%MIN_MAX_HASH;
	m = env->max_table[hash];

	while (m != NULL) {
        if (m->exp==var) {
            _th_inclusive = m->inclusive;
            return m->value;
        }
		m = m->next;
	}

	return NULL;
}

struct _ex_intern *_th_get_lower_bound(struct env *env, struct _ex_intern *var)
{
	int hash;
	struct min_max_list *m;
	//var = _th_mark_vars(env,var);
	hash = (((int)var)/4)%MIN_MAX_HASH;
	m = env->min_table[hash];

	while (m != NULL) {
        if (m->exp==var) {
            _th_inclusive = m->inclusive;
            return m->value;
        }
		m = m->next;
	}

	return NULL;
}

int _th_add_context_property(struct env *env, struct _ex_intern *e)
{
    if (e->type==EXP_APPL &&
        e->u.appl.functor == INTERN_PRIORITY &&
        e->u.appl.count == 2 &&
        e->u.appl.args[0]->type == EXP_INTEGER) {
        return _add_context_property(HEURISTIC_SPACE,env,e->u.appl.args[1],e->u.appl.args[0]->u.integer[1]) ;
    } else {
        return _add_context_property(HEURISTIC_SPACE,env,e,0) ;
    }
}

struct small_disc *_th_get_context_rules(struct env *env)
{
    return env->context_properties ;
}

struct small_disc *_th_get_forward_context_rules(struct env *env)
{
    return env->apply_context_properties ;
}

struct disc *_th_get_forward_rules(struct env *env)
{
    return env->apply_properties ;
}

struct disc *_th_get_derive_rules(struct env *env)
{
    return env->derive_properties ;
}

struct disc *_th_get_augment_rules(struct env *env)
{
    return env->augment_properties ;
}

struct disc *_th_get_macro_rules(struct env *env)
{
    return env->macro_properties ;
}

struct disc *_th_get_all_rules(struct env *env)
{
    return env->all_properties ;
}

void _th_add_lex_info(int s, struct env *env, unsigned sym, int count, int *order)
{
    struct symbol_info *info = _get_symbol_info(s,env,sym) ;
    int i ;

    //printf("Adding lex info %s\n", _th_intern_decode(sym)) ;

    info->lex_order = (unsigned *)_th_alloc(s, sizeof(unsigned) * (count+1)) ;
    info->lex_order[0] = count ;
    for (i = 0; i < count; ++i) {
        info->lex_order[i+1] = order[i] ;
    }
}

int *_th_get_lex_info(struct env *env, unsigned sym)
{
    struct symbol_info *info = _get_symbol_info(-1,env,sym) ;

    if (info != NULL) {
        return info->lex_order ;
    } else {
        return NULL ;
    }
}

void _th_add_function(struct env *env, struct _ex_intern *prototype,
                      struct _ex_intern *type, struct _ex_intern *cond,
                      int defc, struct _ex_intern **def)
{
    struct symbol_info *info = _get_symbol_info(HEURISTIC_SPACE,env,prototype->u.appl.functor) ;

    info->prototype = prototype ;
    info->type = type ;
    info->condition = cond ;
    info->definition = _ex_intern_appl(INTERN_ORIENTED_RULE,defc,def) ;
}

struct _ex_intern *_th_get_function_precondition(struct env *env, unsigned f)
{
    struct symbol_info *info = _get_symbol_info(-1,env,f) ;
    if (info==NULL) return NULL ;
    return info->condition ;
}

struct _ex_intern *_th_get_function_prototype(struct env *env, unsigned f)
{
    struct symbol_info *info = _get_symbol_info(-1,env,f) ;
    if (info==NULL) return NULL ;
    return info->prototype ;
}

unsigned info_bin(unsigned attr,struct parameter *parameters)
{
    struct _ex_intern *e ;

    switch (parameters[0].type) {

        case SYMBOL_PARAMETER:
            return parameters[0].u.symbol ;

        case EXP_PARAMETER:
            e = parameters[0].u.exp ;
            if (e->type == EXP_APPL) {
                return e->u.appl.functor ;
            } else if (e->type == EXP_QUANT) {
                return e->u.quant.quant ;
            }
            return 0 ;

        case FUNCTOR_MATCH:
            return parameters[0].u.functor ;

        default:
            return 0 ;
    }
}

int match(unsigned count, struct parameter *pat, struct parameter *attr)
{
    unsigned i, j ;

    for (i = 0; i < count; ++i) {
        if (pat[i].type==WILD || pat[i].type==FUNCTOR_MATCH) continue ;
        if (pat[i].type != attr[i].type) return 0 ;
        switch (pat[i].type) {
            case SYMBOL_PARAMETER:
                if (pat[i].u.symbol!=attr[i].u.symbol) return 0 ;
                break ;
            case EXP_PARAMETER:
                if (pat[i].u.exp!=attr[i].u.exp) return 0 ;
                break ;
            case INTEGER_LIST_PARAMETER:
                for (j = 0; j <= pat[i].u.integer_list[0]; ++j) {
                    if (pat[i].u.integer_list[j]!=attr[i].u.integer_list[j]) return 0 ;
                }
                break ;
            case SYMBOL_LIST_PARAMETER:
                for (j = 0; j <= pat[i].u.symbol_list[0]; ++j) {
                    if (pat[i].u.symbol_list[j]!=attr[i].u.symbol_list[j]) return 0 ;
                }
                break ;
        }
    }
    return 1 ;
}

static struct attribute *attr ;
static int template_count ;
static struct parameter *template ;
static unsigned a_sym ;

void _th_get_attrib(struct env *env,unsigned asym,int count, struct parameter *t)
{
    struct symbol_info *info = _get_symbol_info(-1,env,info_bin(asym,t)) ;
    if (info==NULL) {
        attr = NULL ;
        return ;
    }
    attr = info->attr;
    template_count = count ;
    template = t ;
    a_sym = asym ;
}

struct parameter *_th_get_next_attrib(int *c)
{
    struct attribute *a ;
    while (attr != NULL) {
        a = attr ;
        attr = attr->next ;
        if (a->parameter_count >= template_count &&
            a->name== a_sym &&
            match(template_count, template, a->parameters)) {
            *c = a->parameter_count ;
            return a->parameters ;
        }
    }
    *c = 0 ;
    return NULL ;
}

void _th_add_attrib(struct env *env,unsigned asym,unsigned count,struct parameter *parameters)
{
    struct symbol_info *info = _get_symbol_info(HEURISTIC_SPACE,env,info_bin(asym,parameters)) ;
    struct attribute *attr = (struct attribute *)_th_alloc(env->space,sizeof(struct attribute) + (count-1)*sizeof(struct parameter)) ;
    unsigned i, j ;

    //if (info_bin(asym,parameters)==1) {
    //    printf("attr = %d\n", attr) ;
    //}
    attr->next = info->attr ;
    info->attr = attr ;

    attr->name = asym ;
    attr->parameter_count = count ;

    for (i = 0; i < count; ++i) {
         attr->parameters[i] = parameters[i] ;
         switch (parameters[i].type) {

              case SYMBOL_LIST_PARAMETER:
                  attr->parameters[i].u.symbol_list = (unsigned *)_th_alloc(env->space,sizeof(unsigned) * (parameters[i].u.symbol_list[0] + 1)) ;
                  for (j = 0; j <= parameters[i].u.symbol_list[0]; ++j) {
                      attr->parameters[i].u.symbol_list[j] = parameters[i].u.symbol_list[j] ;
                  }
                  break ;

              case INTEGER_LIST_PARAMETER:
                  attr->parameters[i].u.integer_list = (int *)_th_alloc(env->space,sizeof(int) * (parameters[i].u.integer_list[0] + 1)) ;
                  for (j = 0; j <= parameters[i].u.integer_list[0]; ++j) {
                      attr->parameters[i].u.integer_list[j] = parameters[i].u.integer_list[j] ;
                  }
                  break ;

         }
    }    

    switch (attr->name) {
        case INTERN_AC:
            info->attribute_flags |= (ATTRIBUTE_A | ATTRIBUTE_C) ;
            break ;
        case INTERN_C:
            info->attribute_flags |= ATTRIBUTE_C ;
            break ;
        case INTERN_A:
            info->attribute_flags |= ATTRIBUTE_A ;
            break ;
        case INTERN_PO:
            info->attribute_flags |= ATTRIBUTE_PO ;
            break ;
        case INTERN_TO:
            info->attribute_flags |= ATTRIBUTE_TO ;
            break ;
        case INTERN_EPO:
            info->attribute_flags |= ATTRIBUTE_EPO ;
            break ;
        case INTERN_ETO:
            info->attribute_flags |= ATTRIBUTE_ETO ;
            break ;
        case INTERN_EQ:
            info->attribute_flags |= ATTRIBUTE_EQ ;
            break ;
        case INTERN_NE:
            info->attribute_flags |= ATTRIBUTE_NE ;
            break ;
    }
}

int _th_is_comparison(struct env *env, unsigned sym)
{
    struct symbol_info *info = env->table[sym%env->symbol_size];
    while (info != NULL) {
        if (info->symbol==sym) return (info->attribute_flags & (ATTRIBUTE_EPO | ATTRIBUTE_ETO | ATTRIBUTE_PO | ATTRIBUTE_TO | ATTRIBUTE_EQ | ATTRIBUTE_NE)) ;
        info = info->next;
    }
    return 0 ;
}

int _th_ac_arity(struct env *env, unsigned sym)
{
    struct symbol_info *info = _get_symbol_info(-1,env,sym) ;
    if (info == NULL) return 0 ;
    /*** TEMPORARY ***/
    if (info->type == NULL) return 0 ;
    return info->type->u.appl.args[0]->u.appl.count-2 ;
}

int _th_is_ac(struct env *env, unsigned sym)
{
    struct symbol_info *info = env->table[sym%env->symbol_size];
    while (info != NULL) {
        if (info->symbol==sym) return (info->attribute_flags & (ATTRIBUTE_A | ATTRIBUTE_C))==(ATTRIBUTE_A | ATTRIBUTE_C) ;
        info = info->next;
    }
    return 0 ;
}

int _th_used_var(struct env *env, unsigned sym)
{
    struct symbol_info *info = _get_symbol_info(-1,env,sym) ;
    if (info == NULL) return 0 ;
    return info->context_level > 0 ;
}

int _th_is_a(struct env *env, unsigned sym)
{
    struct symbol_info *info = _get_symbol_info(-1,env,sym) ;
    if (info == NULL) return 0 ;
    return (info->attribute_flags & (ATTRIBUTE_A | ATTRIBUTE_C))==ATTRIBUTE_A ;
}

int _th_is_c(struct env *env, unsigned sym)
{
    struct symbol_info *info = env->table[sym%env->symbol_size];
    while (info != NULL) {
        if (info->symbol==sym) return (info->attribute_flags & (ATTRIBUTE_A | ATTRIBUTE_C))==ATTRIBUTE_C ;
        info = info->next;
    }
    return 0 ;
}

int _th_is_ac_or_c(struct env *env, unsigned sym)
{
    struct symbol_info *info = env->table[sym%env->symbol_size];
    while (info != NULL) {
        if (info->symbol==sym) return info->attribute_flags & ATTRIBUTE_C ;
        info = info->next;
    }
    return 0 ;
}

int _th_is_a_or_c(struct env *env, unsigned sym)
{
    struct symbol_info *info = _get_symbol_info(-1,env,sym) ;
    if (info == NULL) return 0 ;
    return (info->attribute_flags & (ATTRIBUTE_A | ATTRIBUTE_C)) ;
}

int _th_get_attribute_flags(struct env *env, unsigned sym)
{
    struct symbol_info *info = env->table[sym%env->symbol_size];
    while (info != NULL) {
        if (info->symbol==sym) return info->attribute_flags ;
        info = info->next;
    }
    return 0 ;
}

int _th_is_constructor(struct env *env, unsigned s)
{
    if (s==INTERN_T) return 1 ;
    else {
        struct symbol_info *info = _get_symbol_info(-1,env,s) ;
        if (info==NULL) return 0 ;
        return info->is_constructor ;
    }
}

static unsigned _equal_base(struct env *env, unsigned s)
{
    struct symbol_info *info = _get_symbol_info(-1,env,s) ;

    if (info == NULL) return s ;

    while (info && info->equal_group != s) {
        s = info->equal_group ;
        info = _get_symbol_info(-1,env,s) ;
    }

    return s ;
}

int _th_has_smaller_precedence(struct env *env, unsigned sm, unsigned lg)
{
    struct PrecNode *n ;

    if (_th_is_constructor(env,sm) && !_th_is_constructor(env,lg)) {
        return 1 ;
    } else if (lg==INTERN_SPECIAL_REWRITES_USING || lg==INTERN_SPECIAL_REWRITES) {
        return 1 ;
    } else if (_th_is_constructor(env,lg) && !_th_is_constructor(env,sm)) {
        return 0 ;
    } else {
        unsigned small = _equal_base(env,sm) ;
        unsigned large = _equal_base(env,lg) ;

        struct symbol_info *info = _get_symbol_info(-1,env,small) ;

        if (info==NULL) return 0 ;

        n = info->larger[large%PRECEDENCE_HASH_SIZE] ;
        while (n != NULL) {
            if (n->symbol==large) {
                return 1 ;
            }
            n = n->next ;
        }
        return 0 ;
    }
}

void _th_dump_precedence_info(struct env *env, FILE *f)
{
    int i ;

    for (i = 0; i < env->symbol_size; ++i) {
        struct symbol_info *info = env->table[i] ;
        while (info != NULL) {
            int j ;
            fprintf(f, "BASE %s %s\n", _th_intern_decode(info->symbol), _th_intern_decode(_equal_base(env, info->symbol))) ;
            for (j = 0; j < PRECEDENCE_HASH_SIZE; ++j) {
                struct PrecNode *n = info->larger[j] ;
                while (n != NULL) {
                    fprintf(f, "ORDER %s %s\n", _th_intern_decode(info->symbol), _th_intern_decode(n->symbol)) ;
                    n = n->next ;
                }
            }
            info = info->next ;
        }
    }
}

int _th_has_equal_precedence(struct env *env, unsigned sm, unsigned lg)
{
    unsigned small = _equal_base(env,sm) ;
    unsigned large = _equal_base(env,lg) ;

    return small==large ;
}

int _th_has_smaller_minor_precedence(struct env *env, unsigned small, unsigned large)
{
    struct symbol_info *info = _get_symbol_info(-1,env,small) ;

    if (info==NULL) return 0 ;

    return _bl_find_int(info->minor_larger,large) ;
}

int _th_add_precedence(int s,struct env *env, unsigned sm, unsigned lg)
{
    unsigned small = _equal_base(env,sm) ;
    unsigned large = _equal_base(env,lg) ;
    struct symbol_info *info_s = _get_symbol_info(s,env,small) ;
    struct symbol_info *info_l = _get_symbol_info(s,env,large) ;
    struct symbol_info *info, *info2 ;
    int x, y ;
    struct PrecNode *n, *m, *p ;

    //printf("    Adding %s %s\n", _th_intern_decode(sm), _th_intern_decode(lg)) ;

    if (_th_is_constructor(env,small)) {
        if (!_th_is_constructor(env,large)) return 0 ;
    } else {
        if (_th_is_constructor(env,large)) return 1 ;
    }
    if (small==large) {
        printf("*** ERROR: Cannot add precedence %s < %s\n", _th_intern_decode(small), _th_intern_decode(large)) ;
        return 1 ;
    }

    n = info_s->smaller[large%PRECEDENCE_HASH_SIZE] ;
    while (n != NULL) {
        if (n->symbol==large) {
            printf("*** ERROR: Cannot add precedence %s < %s\n", _th_intern_decode(small), _th_intern_decode(large)) ;
            return 1 ;
        }
        n = n->next ;
    }
    n = info_l->smaller[small%PRECEDENCE_HASH_SIZE] ;
    while (n != NULL) {
        if (n->symbol==small) return 0 ;
        n = n->next ;
    }

    //printf("        Inserting\n") ;

    n = (struct PrecNode *)_th_alloc(s,sizeof(struct PrecNode)) ;
    n->next = info_s->larger[large%PRECEDENCE_HASH_SIZE] ;
    info_s->larger[large%PRECEDENCE_HASH_SIZE] = n ;
    n->symbol = large ;

    n = (struct PrecNode *)_th_alloc(s,sizeof(struct PrecNode)) ;
    n->next = info_l->smaller[small%PRECEDENCE_HASH_SIZE] ;
    info_l->smaller[small%PRECEDENCE_HASH_SIZE] = n ;
    n->symbol = small ;

    for (x = 0; x < PRECEDENCE_HASH_SIZE; ++x) {
        //cc = 0 ;
        m = info_s->smaller[x] ;
        while (m != NULL) {
            info = _get_symbol_info(s,env,m->symbol) ;
            n = info->larger[large%PRECEDENCE_HASH_SIZE] ;
            while (n != NULL) {
                if (n->symbol==large) goto cont1 ;
                n = n->next ;
            }
            //printf("                Adding pair1 %s %s\n", _th_intern_decode(m->symbol), _th_intern_decode(large));
            //++cc ;

            n = (struct PrecNode *)_th_alloc(s,sizeof(struct PrecNode)) ;
            n->next = info->larger[large%PRECEDENCE_HASH_SIZE] ;
            info->larger[large%PRECEDENCE_HASH_SIZE] = n ;
            n->symbol = large ;

            n = (struct PrecNode *)_th_alloc(s,sizeof(struct PrecNode)) ;
            n->next = info_l->smaller[m->symbol%PRECEDENCE_HASH_SIZE] ;
            info_l->smaller[m->symbol%PRECEDENCE_HASH_SIZE] = n ;
            n->symbol = m->symbol ;
cont1:
            m = m->next ;
        }
        //printf("            Adding1 %d\n", cc) ;
    }

    for (x = 0; x < PRECEDENCE_HASH_SIZE; ++x) {
        m = info_l->larger[x] ;
        //cc = 0 ;
        while (m != NULL) {
            info = _get_symbol_info(s,env,m->symbol) ;
            n = info->smaller[small%PRECEDENCE_HASH_SIZE] ;
            while (n != NULL) {
                if (n->symbol==small) goto cont2 ;
                n = n->next ;
            }
            //printf("                Adding pair2 %s %s\n", _th_intern_decode(small), _th_intern_decode(m->symbol));
            //++cc ;

            n = (struct PrecNode *)_th_alloc(s,sizeof(struct PrecNode)) ;
            n->next = info->smaller[small%PRECEDENCE_HASH_SIZE] ;
            info->smaller[small%PRECEDENCE_HASH_SIZE] = n ;
            n->symbol = small ;

            n = (struct PrecNode *)_th_alloc(s,sizeof(struct PrecNode)) ;
            n->next = info_s->larger[m->symbol%PRECEDENCE_HASH_SIZE] ;
            info_s->larger[m->symbol%PRECEDENCE_HASH_SIZE] = n ;
            n->symbol = m->symbol ;
cont2:
            m = m->next ;
        }
        //printf("            Adding2 %d\n", cc) ;
    }

    for (x = 0; x < PRECEDENCE_HASH_SIZE; ++x) {
        //cc = 0 ;
        m = info_s->smaller[x] ;
        while (m != NULL) {
            info = _get_symbol_info(s,env,m->symbol) ;
            for (y = 0; y < PRECEDENCE_HASH_SIZE; ++y) {
                p = info_l->larger[y] ;
                while (p != NULL) {
                    n = info->larger[p->symbol%PRECEDENCE_HASH_SIZE] ;
                    while (n != NULL) {
                        if (n->symbol==p->symbol) goto cont3 ;
                        n = n->next ;
                    }
                    info2 = _get_symbol_info(s,env,p->symbol) ;
                    //printf("                Adding pair3 %s %s\n", _th_intern_decode(m->symbol), _th_intern_decode(p->symbol));
                    //++cc ;

                    n = (struct PrecNode *)_th_alloc(s,sizeof(struct PrecNode)) ;
                    n->next = info->larger[p->symbol%PRECEDENCE_HASH_SIZE] ;
                    info->larger[p->symbol%PRECEDENCE_HASH_SIZE] = n ;
                    n->symbol = p->symbol ;

                    n = (struct PrecNode *)_th_alloc(s,sizeof(struct PrecNode)) ;
                    n->next = info2->smaller[m->symbol%PRECEDENCE_HASH_SIZE] ;
                    info2->smaller[m->symbol%PRECEDENCE_HASH_SIZE] = n ;
                    n->symbol = m->symbol ;
cont3:
                    p = p->next ;
                }
            }
            m = m->next ;
        }
        //printf("            Adding3 %d\n", cc) ;
    }

    return 0 ;
}

int _th_add_max_precedence(int s,struct env *env, unsigned lg)
{
    int i ;

    for (i = 0; i < env->symbol_size; ++i) {
        struct symbol_info *info ;
        info = env->table[i] ;
        while (info != NULL ) {
            //printf("    processing %s\n",_th_intern_decode(info->symbol)) ;
            //fflush(stdout) ;
            if (info->symbol != lg && !_th_has_smaller_precedence(env,lg,info->symbol)) {
                _th_add_precedence(s,env,info->symbol,lg) ;
            }
            info = info->next ;
        }
    }
    _th_add_precedence(s,env,INTERN_SETQ,lg) ;
    _th_add_precedence(s,env,INTERN_ALL,lg) ;
    _th_add_precedence(s,env,INTERN_EXISTS,lg) ;

    return 0 ;
}

int _th_add_minor_precedence(int s,struct env *env, unsigned small, unsigned large)
{
    struct symbol_info *info_s = _get_symbol_info(s,env,small) ;
    struct symbol_info *info_l = _get_symbol_info(s,env,large) ;
    struct symbol_info *info ;
    int x ;

    if (small==large) return 1 ;

    x = _bl_find_int(info_s->minor_smaller, large) ;
    if (x != 0) return 1 ;
    x = _bl_find_int(info_l->minor_smaller, small) ;
    if (x != 0) return 0 ;

    _bl_insert_int(&(info_s->minor_larger), large) ;
    _bl_save_value(info_s->last_entered_minor_larger) ;
    info_s->last_entered_minor_larger = large ;

    _bl_insert_int(&(info_l->minor_smaller), small) ;
    _bl_save_value(info_l->last_entered_minor_smaller) ;
    info_l->last_entered_minor_smaller = small ;

    x = info_s->last_entered_minor_smaller ;
    while ((x&0x3fffffff) != 0x3fffffff) {
        info = _get_symbol_info(s,env,x) ;
        _bl_insert_int(&(info->minor_larger), large) ;
        _bl_save_value(info->last_entered_minor_larger) ;
        info->last_entered_minor_larger = large ;

        _bl_insert_int(&(info_l->minor_smaller), x) ;
        _bl_save_value(info_l->last_entered_minor_smaller) ;
        info_l->last_entered_minor_smaller = x ;

        x = _bl_find_int(info_s->minor_smaller, x) ;
    }

    x = info_l->last_entered_minor_larger ;
    while ((x&0x3fffffff) != 0x3fffffff) {
        info = _get_symbol_info(s,env,x) ;

        _bl_insert_int(&(info->minor_smaller), small) ;
        _bl_save_value(info->last_entered_minor_smaller) ;
        info->last_entered_minor_smaller = small ;

        _bl_insert_int(&(info_s->minor_larger), x) ;
        _bl_save_value(info_s->last_entered_minor_larger) ;
        info_s->last_entered_minor_larger = x ;

        x = _bl_find_int(info_l->minor_larger, x) ;
    }

    return 0 ;
}

static void copy_precedence_info(int s,struct env *env, unsigned e1, unsigned e2)
{
    struct symbol_info *info = _get_symbol_info(s,env,e1) ;
    int x ;
    struct PrecNode *n ;

    for (x = 0; x < PRECEDENCE_HASH_SIZE; ++x) {
        n = info->larger[x] ;
        while (n != NULL) {
            _th_add_precedence(s,env,e2,n->symbol) ;
            n = n->next ;
        }
    }

    for (x = 0; x < PRECEDENCE_HASH_SIZE; ++x) {
        n = info->smaller[x] ;
        while (n != NULL) {
            _th_add_precedence(s,env,n->symbol,e2) ;
            n = n->next ;
        }
    }
}

int _th_add_equal_precedence(int s,struct env *env,unsigned e1,unsigned e2)
{
    struct symbol_info *info = _get_symbol_info(s,env,e1) ;

    if (_th_has_smaller_precedence(env,e1,e2) ||
        _th_has_smaller_precedence(env,e2,e1)) return 1 ;

    while (e1 != info->equal_group) {
        e1 = info->equal_group ;
        info->equal_group = e2 ;
        info = _get_symbol_info(s,env,e1) ;
    }
    copy_precedence_info(s,env,info->equal_group, e2) ;
    info->equal_group = e2 ;

    return 0 ;
}

void _th_env_init()
{
}

static int cmp(const void *i1,const void *i2)
{
    return *((const int *)i2)-*((const int *)i1) ;
}


//static struct add_list *binary_terms = NULL;
//
//struct add_list *_th_get_binary_terms()
//{
//    return binary_terms;
//}

#ifndef FAST
static int interning_equal = 0;
#endif

struct _ex_intern *_ex_intern_equal(struct env *env, struct _ex_intern *type_inst,
                                    struct _ex_intern *left, struct _ex_intern *right)
{
	struct _ex_intern *r;
#ifndef FAST
	interning_equal = 1;
#endif
    r = _ex_intern_appl2_env(env,INTERN_EQUAL,left,right);
	r->type_inst = type_inst;
#ifndef FAST
	if (type_inst != NULL && type_inst!=_ex_real && type_inst != _ex_int && type_inst != _ex_bool) {
		int i = 0;
		fprintf(stderr, "Illegal type inst 2 for %s\n", _th_print_exp(r));
		fprintf(stderr, "type_inst = %s\n", _th_print_exp(type_inst));
		i = 1/i;
		exit(1);
	}
	if (type_inst==NULL) {
		int i = 0;
		fprintf(stderr, "Illegal intern 2 %s\n", _th_print_exp(r));
		i = 1/i;
		exit(1);
	}
	interning_equal = 0;
#endif
	return r;
}

struct _ex_intern *_ex_intern_appl_equal_env(struct env *env,unsigned f,int c, struct _ex_intern *args[], struct _ex_intern *type_inst)
{
	struct _ex_intern *r;
#ifndef FAST
	interning_equal = 1;
#endif
    r = _ex_intern_appl_env(env,f,c,args);
	r->type_inst = type_inst;
#ifndef FAST
	if (type_inst != NULL && type_inst!=_ex_real && type_inst != _ex_int && type_inst != _ex_bool) {
		int i = 0;
		fprintf(stderr, "Illegal type inst for %s\n", _th_print_exp(r));
		fprintf(stderr, "%s\n", _th_print_exp(r->u.appl.args[0]));
		fprintf(stderr, "type_inst = %s\n", _th_print_exp(type_inst));
		i = 1/i;
		exit(1);
	}
	if (type_inst==NULL && f==INTERN_EQUAL) {
		int i=0;
		fprintf(stderr, "Illegal intern 1 %s\n", _th_print_exp(r));
		i = 1/i;
		exit(1);
	}
	interning_equal = 0;
#endif
	return r;
}

#ifndef FAST
int _th_block_check = 0;
#endif

struct _ex_intern *_ex_intern_appl_env(struct env *env,unsigned f,int c, struct _ex_intern *args[])
{
    struct _ex_intern *r;
    int arity ;

	if (env != NULL && _th_is_ac_or_c(env,f)) {
        arity = _th_ac_arity(env,f) ;
        if (arity < 0 || arity > c) {
            int x = 0;
            printf("Illegal arity in _ex_intern_appl_env\n") ;
            x = 1 / x ;
        }
        qsort(args+arity,c-arity,sizeof(struct _ex_intern *),cmp) ;
    }

    r = _ex_intern_appl(f,c,args) ;
#ifndef FAST
	if (!_th_block_check && r->u.appl.functor==INTERN_EQUAL && r->type_inst==NULL && !interning_equal) {
		int i = 0;
		fprintf(stderr, "Illegal intern %s\n", _th_print_exp(r));
		i = 1/i;
		exit(1);
	}
#endif

    //if (_ex_is_new && f != INTERN_NOT && f != INTERN_OR && f != INTERN_AND && f != INTERN_XOR && f != INTERN_ITE) {
    //    struct _ex_intern *t = _th_get_type(env,f);
    //    if (t->u.appl.args[1]==_ex_bool) {
    //        int count;
    //        _th_get_marked_vars(r,&count);
    //        if (count==0) {
    //            struct add_list *a = (struct add_list *)_th_alloc(INTERN_SPACE,sizeof(struct add_list));
    //            a->next = binary_terms;
    //            binary_terms = a;
    //            a->e = r;
    //        }
    //    }
    //}
    return r;
}

struct _ex_intern *_ex_intern_appl1_env(struct env *env, unsigned f,struct _ex_intern *a1)
{
    struct _ex_intern *args[1] ;
    args[0] = a1 ;
    return _ex_intern_appl_env(env,f,1,args) ;
}

struct _ex_intern *_ex_intern_appl2_env(struct env *env, unsigned f,struct _ex_intern *a1, struct _ex_intern *a2)
{
    struct _ex_intern *args[2] ;
    args[0] = a1 ;
    args[1] = a2 ;
    return _ex_intern_appl_env(env,f,2,args) ;
}

struct _ex_intern *_ex_intern_appl2_equal_env(struct env *env, unsigned f,struct _ex_intern *a1, struct _ex_intern *a2, struct _ex_intern *type_inst)
{
    struct _ex_intern *args[2] ;
    args[0] = a1 ;
    args[1] = a2 ;
    return _ex_intern_appl_equal_env(env,f,2,args,type_inst) ;
}

struct _ex_intern *_ex_intern_appl3_env(struct env *env, unsigned f,struct _ex_intern *a1, struct _ex_intern *a2, struct _ex_intern *a3)
{
    struct _ex_intern *args[3] ;
    args[0] = a1 ;
    args[1] = a2 ;
    args[2] = a3 ;
    return _ex_intern_appl_env(env,f,3,args) ;
}

struct _ex_intern *_ex_intern_appl4_env(struct env *env, unsigned f,struct _ex_intern *a1, struct _ex_intern *a2, struct _ex_intern *a3, struct _ex_intern *a4)
{
    struct _ex_intern *args[4] ;
    args[0] = a1 ;
    args[1] = a2 ;
    args[2] = a3 ;
    args[3] = a4 ;
    return _ex_intern_appl_env(env,f,4,args) ;
}

struct _ex_intern *_ex_intern_appl5_env(struct env *env, unsigned f,struct _ex_intern *a1, struct _ex_intern *a2, struct _ex_intern *a3, struct _ex_intern *a4, struct _ex_intern *a5)
{
    struct _ex_intern *args[5] ;
    args[0] = a1 ;
    args[1] = a2 ;
    args[2] = a3 ;
    args[3] = a4 ;
    args[4] = a5 ;
    return _ex_intern_appl_env(env,f,5,args) ;
}

struct _ex_intern *_ex_intern_appl6_env(struct env *env, unsigned f,struct _ex_intern *a1, struct _ex_intern *a2, struct _ex_intern *a3, struct _ex_intern *a4, struct _ex_intern *a5, struct _ex_intern *a6)
{
    struct _ex_intern *args[6] ;
    args[0] = a1 ;
    args[1] = a2 ;
    args[2] = a3 ;
    args[3] = a4 ;
    args[4] = a5 ;
    args[5] = a6 ;
    return _ex_intern_appl_env(env,f,6,args) ;
}

static struct prex_param_info *copy_prex_param_info(int s,struct prex_param_info *info)
{
    int i ;
    struct prex_param_info *n = (struct prex_param_info *)_th_alloc(s,sizeof(struct prex_param_info) +
                                sizeof(struct elist *) * (info->count-1)) ;

    n->count = info->count ;
    n->param = info->param ;
    for (i = 0; i < n->count; ++i) {
        n->exps[i] = info->exps[i] ;
    }

    return n ;
}

static struct prex_info *copy_prex_info(int s, struct prex_info *info)
{
    int i ;
    struct prex_info *n = (struct prex_info *)_th_alloc(s,sizeof(struct prex_info) +
                          sizeof(struct prex_param_info *) * (info->count-1)) ;

    n->count = info->count ;
    for (i = 0; i < info->count; ++i) {
        n->info[i] = copy_prex_param_info(s,info->info[i]) ;
    }

    return n ;
}

void _th_add_prex_info(int s, struct env *e, unsigned sym, struct prex_info *i)
{
    struct symbol_info *info = _get_symbol_info(s,e,sym) ;

    info->prex_info = copy_prex_info(s,i) ;
}

struct prex_info *_th_get_prex_info(struct env *e, unsigned sym)
{
    struct symbol_info *info = _get_symbol_info(-1,e,sym) ;
    if (info==NULL) return NULL ;
    return info->prex_info ;
}

static int _is_closed_definition(struct env *env,struct _ex_intern *t) ;

static int _icd(struct env *env,struct _ex_intern *t)
{
    struct symbol_info *info ;
    int i ;

    if (t->type == EXP_APPL) {
        info = _get_symbol_info(-1,env,t->u.appl.functor) ;
        if (info==NULL) return 0 ;
        if (!info->mark) {
            info->mark = 1 ;
            if (!_is_closed_definition(env,info->type_definition)) {
                return 0 ;
            }
            info->mark = 0 ;
        }
        for (i = 0; i < t->u.appl.count; ++i) {
            if (!_icd(env,t->u.appl.args[i])) return 0 ;
        }
    }
    return 1 ;
}

static int _is_closed_definition(struct env *env,struct _ex_intern *t)
{
    int i, j ;

    for (i = 0; i < t->u.appl.count; ++i) {
        struct _ex_intern *cl = t->u.appl.args[i] ;
        for (j = 0; j < cl->u.appl.count; ++j) {
            if (!_icd(env, cl->u.appl.args[j])) return 0 ;
        }
    }

    return 1 ;
}

static void _atp(int s, struct env *env, struct _ex_intern *t, struct _ex_intern *cl)
{
    int i, j ;

    if (t->type == EXP_APPL) {
        struct symbol_info *info = _get_symbol_info(-1,env,t->u.appl.functor) ;
        if (info != NULL && cl != info->type_definition &&
            info->type_definition != NULL &&
            _is_closed_definition(env,info->type_definition)) {
            for (i = 0; i < cl->u.appl.count; ++i) {
                for (j = 0; j < info->type_definition->u.appl.count; ++j) {
                    _th_add_precedence(s,env,
                        info->type_definition->u.appl.args[j]->u.appl.functor,
                        cl->u.appl.args[i]->u.appl.functor) ;
                }
            }
        }
    }
}

static void _add_type_precedences(int s, struct env *env, struct _ex_intern *t)
{
    int i,j ;
    for (i = 0; i < t->u.appl.count; ++i) {
         struct _ex_intern *cl = t->u.appl.args[i] ;
         for (j = 0; j < cl->u.appl.count; ++j) {
              _atp(s,env,cl->u.appl.args[j],t) ;
         }
    }
}

static int smaller_constructor(struct env *env, struct _ex_intern *t, struct _ex_intern *c1, struct _ex_intern *c2)
{
    return c1->u.appl.count == 0 && c2->u.appl.count != 0 ;
}

struct _ex_intern *_th_get_type_definition(struct env *e, unsigned sym)
{
    struct symbol_info *info = _get_symbol_info(-1,e,sym);

    if (info==NULL) return NULL;
    return info->type_definition;
}

struct _ex_intern *_th_get_type_functor(struct env *e, unsigned sym)
{
    struct symbol_info *info = _get_symbol_info(-1,e,sym);

    if (info==NULL) return NULL;
    return info->type_functor;
}

void _th_add_type_definition(struct env *e, struct _ex_intern *f,
                             struct _ex_intern *t)
{
    struct symbol_info *info = _get_symbol_info(HEURISTIC_SPACE,e,f->u.appl.functor) ;
    int finite_type, i, j ;

    if (info->type_definition != NULL) {
        printf("Type already defined\n") ;
        exit(1) ;
    }
    info->type_functor = f ;
    info->type_definition = t ;

    if (t==NULL) return ;

    finite_type = 1 ;
    for (i = 0; i < t->u.appl.count; ++i) {
        if (t->u.appl.args[i]->u.appl.count!=0) {
            finite_type = 0 ;
            break ;
        }
    }
    info->is_finite_type = finite_type ;
    for (i = 0; i < t->u.appl.count; ++i) {
         struct symbol_info *info2 = _get_symbol_info(HEURISTIC_SPACE,e,t->u.appl.args[i]->u.appl.functor) ;
         info2->is_finite_constructor = finite_type ;
         info2->is_constructor = 1 ;
    }
    _add_type_precedences(e->space,e,t) ;
    for (i = 0; i < t->u.appl.count; ++i) {
        info = _get_symbol_info(HEURISTIC_SPACE,e,t->u.appl.args[i]->u.appl.functor) ;
        for (j = 0; j < t->u.appl.count; ++j) {
             struct _ex_intern *args[2] ;
             args[1] = f ;
             args[0] = _ex_intern_appl_env(e,INTERN_TUPLE,
                                           t->u.appl.args[i]->u.appl.count,
                                           t->u.appl.args[i]->u.appl.args) ;
             info->type = _ex_intern_appl_env(e,INTERN_FUNCTION,2,args) ;
             if (smaller_constructor(e,t,t->u.appl.args[i],t->u.appl.args[j])) {
                 _th_add_precedence(e->space,e,t->u.appl.args[i]->u.appl.functor,
                                    t->u.appl.args[j]->u.appl.functor) ;
             }
        }
    }
}

int _th_is_finite_type(struct env *e, unsigned t)
{
    struct symbol_info *info = _get_symbol_info(-1,e,t) ;
    if (info == NULL) return 0 ;
    return info->is_finite_type ;
}

int _th_is_finite_constructor(struct env *e, unsigned t)
{
    struct symbol_info *info = _get_symbol_info(-1,e,t) ;
    if (info == NULL) return 0 ;
    return info->is_finite_constructor ;
}

int _th_smallest_symbol_of_type(struct env *e, unsigned s)
{
    struct symbol_info *info = _get_symbol_info(-1,e,s) ;
    int i ;

    if (info == NULL) return 0 ;
    if (!info->is_constructor) return 0 ;
    info = _get_symbol_info(-1,e,info->type->u.appl.args[1]->u.appl.functor) ;

    for (i = 0; i < info->type_definition->u.appl.count; ++i) {
        if (s != info->type_definition->u.appl.args[i]->u.appl.functor) {
            if (!_th_has_smaller_precedence(e,s,info->type_definition->u.appl.args[i]->u.appl.functor)) return 0 ;
        }
    }

    return 1 ;
}

struct _ex_intern *_th_get_type(struct env *env, unsigned symbol)
{
    struct symbol_info *info = _get_symbol_info(-1,env,symbol) ;
    if (info==NULL) return NULL ;
    return info->type ;
}

static struct root_var *copy_root_chain(int s, struct root_var *root)
{
    struct root_var *n;

    if (root==NULL) return NULL;

    n = (struct root_var *)_th_alloc(s,sizeof(struct root_var));
    n->equal_terms = root->equal_terms;
    n->ne_list = root->ne_list;
    n->used_in_terms = root->used_in_terms;
    n->parent = root->parent;
    n->var = root->var;

    n->next = copy_root_chain(s,root->next);

    return n;
}

static int clevel = 0;

//void check_env(struct env *env, char *check)
//{
//    printf("mark %s %x\n", check, env->first_context_mark);
//}

int _th_push_count(struct env *env)
{
    int c = 0;
    struct context_stack *cs = env->context_stack;

    while (cs) {
        ++c;
        cs = cs->next;
    }

    return c;
}

void check_cs(struct env *env)
{
    int c = 0;
    struct context_stack *cs = env->context_stack;
    while (cs && c < 200) {
        ++c;
        cs = cs->next;
    }
    if (c != clevel) {
        printf("Context stack level error %d %d\n", c, clevel);
        //exit(1);
    }
}

struct diff_node *copy_diff_nodes(struct env *env, struct diff_node *d)
{
    struct diff_node *n;

    if (d==NULL) return NULL;

    n = (struct diff_node *)_th_alloc(env->space,sizeof(struct diff_node));
    n->e = d->e;
    n->edges = d->edges;
    n->source_edges = d->source_edges;
    n->limit = n->bottom = NULL;
    n->limit2 = n->bottom2 = NULL;
    n->ne_list = d->ne_list;
	n->eq_merge = d->eq_merge;
	n->eq_explanation = d->eq_explanation;
	n->eq_offset = d->eq_offset;
	n->move = NULL;
	n->move_back = d;
	d->move = n;
    n->next = copy_diff_nodes(env,d->next);

    return n;
}

static void clear_move(struct env *env)
{
	int i;
	struct diff_node *n;

	for (i = 0; i < DIFF_NODE_HASH; ++i) {
		n = env->diff_node_table[i];
		while (n) {
			n->move = NULL;
			n = n->next;
		}
	}
}

static void move_data(struct env *env)
{
	struct diff_edge *edge;
	int i;
	struct diff_node *n;
    struct ne_list *ne;

	for (i = 0; i < DIFF_NODE_HASH; ++i) {
		n = env->diff_node_table[i];
		while (n) {
			edge = n->edges;
			while (edge) {
				if (edge->target->move) edge->target = edge->target->move;
				if (edge->source->move) edge->source = edge->source->move;
				edge = edge->next;
			}
			ne = n->ne_list;
			while (ne) {
				if (ne->target->move) ne->target = ne->target->move;
				if (ne->orig_source && ne->orig_source->move) ne->orig_source = ne->orig_source->move;
				ne = ne->next;
			}
			if (n->eq_merge && n->eq_merge->move) n->eq_merge = n->eq_merge->move;
			n = n->next;
		}
	}
}

static void move_back_data(struct env *env)
{
	struct diff_edge *edge;
	int i;
	struct diff_node *n;
    struct ne_list *ne;

	for (i = 0; i < DIFF_NODE_HASH; ++i) {
		n = env->diff_node_table[i];
		while (n) {
			edge = n->edges;
			while (edge) {
				if (edge->target->move_back) edge->target = edge->target->move_back;
				if (edge->source->move_back) edge->source = edge->source->move_back;
				edge = edge->next;
			}
			ne = n->ne_list;
			while (ne) {
				if (ne->target->move_back) ne->target = ne->target->move_back;
				if (ne->orig_source && ne->orig_source->move_back) ne->orig_source = ne->orig_source->move_back;
				ne = ne->next;
			}
			//if (n->eq_merge && n->eq_merge->move_back) n->eq_merge = n->eq_merge->move_back;
			n = n->next;
		}
	}
}

void _th_push_context_rules(struct env *env)
{
    struct context_stack *cs ;
    int i;

    //check_integrity(env, "begin push");

	//printf("**** PUSH CONTEXT ****\n");

    //check_cs(env);

    printf("*** PUSH CONTEXT *** %d %x %x\n", clevel++, env, env->first_context_mark);
    //if (env->first_context_mark) printf("mark %s\n", _th_intern_decode(env->first_context_mark->symbol));

    if (env->simplex) _th_simplex_push(env->simplex);

    cs = (struct context_stack *)_th_alloc(env->space,sizeof(struct context_stack)) ;

    //printf("push %x\n", env->simplified_rules);
    //_print_simplified_rules(env);

    cs->next = env->context_stack ;
    cs->context_properties = env->context_properties ;
    cs->apply_context_properties = env->apply_context_properties ;
	cs->context_rules = env->context_rules;
    cs->simplified_rules = env->simplified_rules;
    cs->blocked_rules = env->blocked_rules;
	cs->variables = env->variables;
	cs->default_type = env->default_type;
    env->context_properties = _th_push_small(env->space,env->context_properties) ;
    env->apply_context_properties = _th_push_small(env->space,env->apply_context_properties) ;
    env->context_stack = cs ;
    cs->slack = env->slack;
	cs->min_table = env->min_table;
	cs->max_table = env->max_table;
    cs->diff_node_table = env->diff_node_table;
	cs->rule_operand_table = env->rule_operand_table;
	cs->rule_double_operand_table = env->rule_double_operand_table;
	cs->var_solve_table = env->var_solve_table;
    cs->rewrite_chain = env->rewrite_chain;
    cs->head = env->head;
    env->min_table = (struct min_max_list **)_th_alloc(env->space,sizeof(struct min_max_list *) * MIN_MAX_HASH);
    env->max_table = (struct min_max_list **)_th_alloc(env->space,sizeof(struct min_max_list *) * MIN_MAX_HASH);
	env->rule_operand_table = (struct rule_operand_list **)_th_alloc(env->space,sizeof(struct rule_operand_table *) * RULE_OPERAND_HASH);
	env->rule_double_operand_table = (struct rule_double_operand_list **)_th_alloc(env->space,sizeof(struct rule_double_operand_table *) * RULE_OPERAND_HASH);
	env->var_solve_table = (struct var_solve_list **)_th_alloc(env->space,sizeof(struct var_solve_table *) * VAR_SOLVE_HASH);
    for (i = 0; i < MIN_MAX_HASH; ++i) {
		env->min_table[i] = cs->min_table[i];
		env->max_table[i] = cs->max_table[i];
	}
	for (i = 0; i < RULE_OPERAND_HASH; ++i) {
		env->rule_operand_table[i] = cs->rule_operand_table[i];
		env->rule_double_operand_table[i] = cs->rule_double_operand_table[i];
	}
	for (i = 0; i < VAR_SOLVE_HASH; ++i) {
		env->var_solve_table[i] = cs->var_solve_table[i];
	}
    if (env->diff_node_table) {
        env->diff_node_table = (struct diff_node **)_th_alloc(env->space,sizeof(struct diff_node *) * DIFF_NODE_HASH);
        for (i = 0; i < DIFF_NODE_HASH; ++i) {
            env->diff_node_table[i] = copy_diff_nodes(env,cs->diff_node_table[i]);
        }
#ifdef XX
        for (i = 0; i < DIFF_NODE_HASH; ++i) {
            struct diff_node *n = env->diff_node_table[i];
            while (n) {
                struct diff_edge *e = n->edges;
                while (e) {
                    e->target = e->target->child;
                    e->source = e->source->child;
                    e = e->next;
                }
                n = n->next;
            }
        }
#endif
		move_data(env);
		clear_move(env);
    }
    cs->root_vars = env->root_vars;
    cs->term_groups = env->term_groups;
    cs->term_functors = env->term_functors;
    env->root_vars = (struct root_var **)_th_alloc(env->space,sizeof(struct root_var *) * TERM_HASH);
    env->term_groups = (struct term_group **)_th_alloc(env->space,sizeof(struct term_group *) * TERM_HASH);
    env->term_functors = (struct term_group **)_th_alloc(env->space,sizeof(struct term_functors *) * TERM_HASH);
    for (i = 0; i < TERM_HASH; ++i) {
        env->root_vars[i] = cs->root_vars[i];
        cs->root_vars[i] = copy_root_chain(env->space,cs->root_vars[i]);
        env->term_groups[i] = cs->term_groups[i];
        env->term_functors[i] = cs->term_functors[i];
    }
    ++env->context_level ;

    //check_integrity(env, "end push");
}

int _th_get_stack_level(struct env *env)
{
	int l = 0;
	struct context_stack *cs;
	cs = env->context_stack;
	while (cs) {
		cs = cs->next;
		++l;
	}
	return l;
}

void *_th_quick_mark(struct env *env)
{
	return env->head;
}

void _th_quick_pop(struct env *env, void *m)
{
	while (env->head != m) {
        env->head->term->rewrite = env->head->old_value;
        env->head->term->cache_line = env->head->old_line;
        env->head->term->sig = env->head->old_sig;
        env->head->term->find = env->head->old_find;
        env->head->term->merge = env->head->old_merge;
        //if (env->head->term->original != env->head->old_original) {
        //    printf("%d: reverting %s to ", _tree_zone, _th_print_exp(env->head->term));
        //    printf("%s\n", _th_print_exp(env->head->old_original));
        //}
        env->head->term->original = env->head->old_original;
        env->head->term->explanation = env->head->old_explanation;

        if (env->head->bad&1) {
            env->head->term->cache_bad = 1;
        } else {
            env->head->term->cache_bad = 0;
        }
        if (env->head->in_hash&1) {
            //printf("Adding inhash 3 %s\n", _th_print_exp(env->head->term));
            env->head->term->in_hash = 1;
        } else {
            //printf("Removing inhash 3 %s\n", _th_print_exp(env->head->term));
            env->head->term->in_hash = 0;
        }
        if (env->head->term->cache_bad || env->head->term->rewrite==NULL || env->head->term->rewrite==env->head->term) {
            _ex_add_term(env->head->term);
        } else {
            _ex_delete_term(env->head->term);
        }
		env->head = env->head->next;
	}
}

void _th_pop_context_rules(struct env *env)
{
    struct symbol_info *p, *s;
    int i;
    static struct _ex_intern *rt;

	//printf("**** POP CONTEXT ****\n");

#ifdef PRINT1
	add_left = add_right = add_e = NULL;
#endif

    if (env->simplex) _th_simplex_pop(env->simplex);

    //if (rt==NULL) rt = _th_parse(env,"(rless x_9 x_8)");

    //check_integrity(env, "begin pop");

    //check_cs(env);

    printf("*** POP CONTEXT *** %d\n", --clevel);

    env->context_properties = env->context_stack->context_properties;
    env->apply_context_properties = env->context_stack->apply_context_properties;
	env->context_rules = env->context_stack->context_rules;
    env->simplified_rules = env->context_stack->simplified_rules;
    env->blocked_rules = env->context_stack->blocked_rules;
	env->variables = env->context_stack->variables;
	env->default_type = env->context_stack->default_type;
    env->min_table = env->context_stack->min_table;
    env->max_table = env->context_stack->max_table;
    env->diff_node_table = env->context_stack->diff_node_table;
    if (env->diff_node_table) {
#ifdef XX
		for (i = 0; i < DIFF_NODE_HASH; ++i) {
            struct diff_node *n = env->diff_node_table[i];
            while (n) {
                struct diff_edge *e = n->edges;
                while (e) {
                    e->target = e->target->parent;
                    e->source = e->source->parent;
                    e = e->next;
                }
                n = n->next;
            }
        }
#endif
		move_back_data(env);
    }
	env->rule_operand_table = env->context_stack->rule_operand_table;
	env->rule_double_operand_table = env->context_stack->rule_double_operand_table;
	env->var_solve_table = env->context_stack->var_solve_table;
    env->rewrite_chain = env->context_stack->rewrite_chain;
    env->slack = env->context_stack->slack;
    env->term_groups = env->context_stack->term_groups;
    env->term_functors = env->context_stack->term_functors;
    for (i = 0; i < TERM_HASH; ++i) {
        if (env->context_stack->root_vars[i]==NULL) {
            env->root_vars[i] = NULL;
        } else {
            struct root_var *er, *cr;
            while (env->root_vars[i] && env->root_vars[i]->var != env->context_stack->root_vars[i]->var) {
                env->root_vars[i] = env->root_vars[i]->next;
            }
            er = env->root_vars[i];
            cr = env->context_stack->root_vars[i];
            while (er != NULL) {
                er->equal_terms = cr->equal_terms;
                er->ne_list = cr->ne_list;
                er->used_in_terms = cr->used_in_terms;
                er->parent = cr->parent;
                er = er->next;
                cr = cr->next;
            }
        }
        env->context_stack->root_vars[i] = env->root_vars[i];
    }
    env->root_vars = env->context_stack->root_vars;

    //fprintf(stderr, "Assigning rewrite chain pop %x %x\n", env, env->rewrite_chain);
    while (env->head && env->head != env->context_stack->head) {
        //if ((env->head->bad&2)==0) {
        //    env->head->term->rewrite->cached_in = env->head->term->rewrite->cached_in->next;
        //}
        //if (env->head->term->type==EXP_APPL && !strcmp(_th_intern_decode(env->head->term->u.appl.functor),"p2")) {
        //    printf("Reverting %s ->", _th_print_exp(env->head->term));
        //    printf(" to (%d) %s\n", (env->head->bad)&1, _th_print_exp(env->head->old_value));
        //}
        //printf("env = %d\n", env);
        //fflush(stdout);
        //printf("env->head = %d\n", env->head);
        //fflush(stdout);
        //printf("env->head->term = %d\n", env->head->term);
        //fflush(stdout);
        //printf("env->head->term->rewrite = %d\n", env->head->term->rewrite);
        //fflush(stdout);
        //if (env->head->term==rt) {
        //    printf("Popping %s\n", _th_print_exp(rt));
        //    printf("   env->head->find = %s\n", _th_print_exp(env->head->find));
        //    printf("   env->head->old_find = %s\n", _th_print_exp(env->head->old_find));
        //    printf("   env->head->value = %s\n", _th_print_exp(env->head->value));
        //    printf("   env->head->old_value = %s\n", _th_print_exp(env->head->old_value));
        //    printf("   env->head->sig = %s\n", _th_print_exp(env->head->sig));
        //    printf("   env->head->old_sig = %s\n", _th_print_exp(env->head->old_sig));
        //    printf("   env->head->merge = %s\n", _th_print_exp(env->head->merge));
        //    printf("   env->head->old_merge = %s\n", _th_print_exp(env->head->old_merge));
        //    printf("   env->head->explanation = %x\n", env->head->explanation);
        //    printf("   env->head->old_explanation = %x\n", env->head->old_explanation);
        //    printf("   env->head->original = %s\n", _th_print_exp(env->head->original));
        //    printf("   env->head->old_original = %s\n", _th_print_exp(env->head->old_original));
        //    printf("   env->head->bad, env->head->in_hash = %d %d\n", env->head->bad, env->head->in_hash);
        //}
        env->head->term->rewrite = env->head->old_value;
        env->head->term->cache_line = env->head->old_line;
        env->head->term->sig = env->head->old_sig;
        env->head->term->find = env->head->old_find;
        env->head->term->merge = env->head->old_merge;
        //if (env->head->term->original != env->head->old_original) {
        //    printf("%d: reverting %s to ", _tree_zone, _th_print_exp(env->head->term));
        //    printf("%s\n", _th_print_exp(env->head->old_original));
        //}
        env->head->term->original = env->head->old_original;
        env->head->term->explanation = env->head->old_explanation;

        if (env->head->bad&1) {
            env->head->term->cache_bad = 1;
        } else {
            env->head->term->cache_bad = 0;
        }
        if (env->head->in_hash&1) {
            //printf("Adding inhash 3 %s\n", _th_print_exp(env->head->term));
            env->head->term->in_hash = 1;
        } else {
            //printf("Removing inhash 3 %s\n", _th_print_exp(env->head->term));
            env->head->term->in_hash = 0;
        }
        if (env->head->term->cache_bad || env->head->term->rewrite==NULL || env->head->term->rewrite==env->head->term) {
            _ex_add_term(env->head->term);
        } else {
            _ex_delete_term(env->head->term);
        }
        env->head = env->head->next;
    }
    if (env->head) {
        env->head->prev = NULL;
    } else {
        env->tail = NULL;
    }

    env->context_stack = env->context_stack->next;
    p = NULL ;
    s = env->first_context_mark ;

    while (s) {
        //printf("Processing %x %s\n", s, _th_intern_decode(s->symbol));
        if (s->context_level > env->context_level) {
            s->context_level = 0 ;
            if (p==NULL) {
                env->first_context_mark = s->next_context_mark ;
            } else {
                p->next_context_mark = s->next_context_mark ;
            }
            s = s->next_context_mark ;
        } else {
            p = s ;
            s = s->next_context_mark ;
        }
        if (s != NULL && s==s->next_context_mark) {
            fprintf(stderr, "pop_context_rules failure\n") ;
            exit(1) ;
        }
    }
    --env->context_level ;

    //check_integrity(env, "end pop");
}

struct env *_th_default_env(int s)
{
    struct env *env = _th_new_empty_env(s, _th_intern_count()) ;
    struct parameter parameters[5] ;

    struct symbol_info *info = _get_symbol_info(s,env,INTERN_SET) ;
    info->is_constructor = 1 ;

    info->type = _th_parse(env,"(-> (Tuple a a) (Set a))");

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_UNION ;
    _th_add_attrib(env,INTERN_AC,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_INTERSECT ;
    _th_add_attrib(env,INTERN_AC,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_CONCAT ;
    _th_add_attrib(env,INTERN_A,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_FUNCTION ;
    _th_add_attrib(env,INTERN_A,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_SET ;
    _th_add_attrib(env,INTERN_C,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_AND ;
    _th_add_attrib(env,INTERN_AC,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_XOR ;
    _th_add_attrib(env,INTERN_AC,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_OR ;
    _th_add_attrib(env,INTERN_AC,1,parameters) ;

    //parameters[0].type = SYMBOL_PARAMETER ;
    //parameters[0].u.symbol = INTERN_NC_AND ;
    //_th_add_attrib(env,INTERN_A,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_ANDQ ;
    _th_add_attrib(env,INTERN_A,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_NOTL ;
    _th_add_attrib(env,INTERN_A,1,parameters) ;

    //parameters[0].type = SYMBOL_PARAMETER ;
    //parameters[0].u.symbol = INTERN_NC_OR ;
    //_th_add_attrib(env,INTERN_A,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_NAT_PLUS ;
    _th_add_attrib(env,INTERN_AC,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_NAT_MIN ;
    _th_add_attrib(env,INTERN_AC,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_NAT_MAX ;
    _th_add_attrib(env,INTERN_AC,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_NAT_TIMES ;
    _th_add_attrib(env,INTERN_AC,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_RAT_PLUS ;
    _th_add_attrib(env,INTERN_AC,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_RAT_TIMES ;
    _th_add_attrib(env,INTERN_AC,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_EQUAL ;
    _th_add_attrib(env,INTERN_C,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_SEPARATE ;
    _th_add_attrib(env,INTERN_C,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_PRECEQ ;
    parameters[1].type = SYMBOL_PARAMETER ;
    parameters[1].u.symbol = INTERN_EQUAL ;
    _th_add_attrib(env,INTERN_EPO,2,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_NAT_LESS ;
    parameters[1].type = SYMBOL_PARAMETER ;
    parameters[1].u.symbol = INTERN_EQUAL ;
    _th_add_attrib(env,INTERN_TO,2,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_RAT_LESS ;
    parameters[1].type = SYMBOL_PARAMETER ;
    parameters[1].u.symbol = INTERN_EQUAL ;
    _th_add_attrib(env,INTERN_TO,2,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_SUBSET ;
    parameters[1].type = SYMBOL_PARAMETER ;
    parameters[1].u.symbol = INTERN_EQUAL ;
    _th_add_attrib(env,INTERN_EPO,2,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_EQUAL ;
    _th_add_attrib(env,INTERN_EQ,1,parameters) ;

    //printf("true false %x %x\n", _th_parse(env,"(True)"), _th_parse(env,"(False)")) ;

    _th_add_type_definition(env, _th_parse(env,"(Bool)"), _th_parse(env,"(| (True) (False))")) ;
    _th_add_type_definition(env, _th_parse(env,"(Unit)"), _th_parse(env,"(| (Identity) (Trivial))")) ;
    _th_add_type_definition(env, _th_parse(env,"(Int)"), NULL) ;
    _th_add_type_definition(env, _th_parse(env,"(Real)"), NULL) ;
    _th_add_type_definition(env, _th_parse(env,"(String)"), NULL) ;
    _th_add_type_definition(env, _th_parse(env,"(Array)"), NULL) ;

    _th_add_function(env,_th_parse(env,"(Tuple a b)"),_th_parse(env,"(-> (Tuple (AnyType) (AnyType)) (AnyType))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(Function a b)"),_th_parse(env,"(-> (Tuple (AnyType) (AnyType)) (AnyType))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(subst a b c)"), _th_parse(env,"(-> (Tuple a a b) b)"), _th_parse(env, "(True)"), 0, NULL) ;
    _th_add_function(env,_th_parse(env,"(replace a b c)"), _th_parse(env,"(-> (Tuple a b b) a)"), _th_parse(env, "(True)"), 0, NULL) ;
    _th_add_function(env,_th_parse(env,"(matchClosure a b)"),_th_parse(env,"(-> (Tuple y x) (Set x))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(testMatchClosure a b)"),_th_parse(env,"(-> (Tuple y x) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(specialRewrites a)"),_th_parse(env,"(-> a (Set a))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(specialRewritesUsing a b)"),_th_parse(env,"(-> (Tuple a b) (Set a))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(getContextRules)"), _th_parse(env, "(-> (Tuple) (Set (Bool)))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(checkMode)"), _th_parse(env, "(-> (Tuple) (Int))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(checkState)"), _th_parse(env, "(-> (Tuple) (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(checkValidity)"), _th_parse(env, "(-> (Tuple a (Bool) (Int)) (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(checkValidityTerm)"), _th_parse(env, "(-> (Tuple (Bool) (Bool) (Bool) (Int)) (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(markVars)"), _th_parse(env, "(-> a a)"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(match a b)"), _th_parse(env, "(-> (Tuple a b) (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(QUOTE a)"), _th_parse(env, "(-> a a)"), _th_parse(env, "(True)"),0,NULL) ;
    //_th_add_function(env,_th_parse(env,"(add a)"), _th_parse(env, "(-> (Bool) (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    //_th_add_function(env,_th_parse(env,"(delete a)"), _th_parse(env, "(-> (Bool) (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    //_th_add_function(env,_th_parse(env,"(change a b)"), _th_parse(env, "(-> (Tuple (Bool) (Bool)) (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(getTerms a)"), _th_parse(env, "(-> (Tuple) (Set (Bool)))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(getLimitTerm a)"), _th_parse(env, "(-> (Tuple) (Set (Bool)))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(getCurrentTerm a)"), _th_parse(env, "(-> (Tuple) (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(unquantify a)"), _th_parse(env, "(-> (Bool) (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(QUOTE a)"), _th_parse(env, "(-> a a)"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(noFunctor a)"), _th_parse(env, "(-> a (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(noAugment)"), _th_parse(env, "(-> (Tuple) (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(unquote a)"), _th_parse(env, "(-> a a)"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(illegalTerm a)"), _th_parse(env, "(-> a (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(normal_condition a)"), _th_parse(env, "(-> a (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(rewritable a)"), _th_parse(env, "(-> a (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(hasFreeVars a)"), _th_parse(env, "(-> a (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(kb_rules a)"), _th_parse(env, "(-> (Bool) (Set (Bool)))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(nestingLimit a)"),_th_parse(env, "(-> (Int) (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(prune a)"),_th_parse(env, "(-> (Tuple a a) (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(varAsString a)"),_th_parse(env, "(-> a (String))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(specialType a)"),_th_parse(env, "(-> a (Type))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(heuristic name prop div cond)"),_th_parse(env,"(-> (Tuple (String) a (Set (Tuple (Bool) (Bool))) (Bool)) (Bool))"),_ex_true,0,NULL) ;
    _th_add_function(env,_th_parse(env,"(setsize set)"),_th_parse(env,"(-> (Set a) (Int))"),_ex_true,0,NULL);
    _th_add_function(env,_th_parse(env,"(ite cond tval fval)"),_th_parse(env, "(-> (Tuple (Bool) a a) a)"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(solveFor v exp)"),_th_parse(env, "(-> (Tuple a (Bool)) (Bool))"),_th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(gcd x y)"),_th_parse(env, "(-> (Tuple (Int) (Int)) (Int))"),_th_parse(env, "(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(nmin a b)"),_th_parse(env,"(-> (Tuple (Int) (Int)) (Int))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(nmax a b)"),_th_parse(env,"(-> (Tuple (Int) (Int)) (Int))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(store a b c)"),_th_parse(env,"(-> (Tuple (Array) (Int) (Int)) (Array))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(select a b)"),_th_parse(env,"(-> (Tuple (Array) (Int)) (Int))"),_th_parse(env,"(True)"),0,NULL) ;

    _th_add_precedence(s,env,INTERN_SPECIAL_TYPE,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_NESTING_LIMIT,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_KB_RULES,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_MARK_VARS,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_GET_CONTEXT_RULES,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_CHECK_MODE,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_CHECK_STATE,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_CHECK_VALIDITY,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_CHECK_VALIDITY_TERM,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_UNQUANTIFY,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_NORMAL_CONDITION,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_ILLEGAL_TERM,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_REWRITABLE,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_HAS_FREE_VARS,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_QUOTE,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_NORMAL,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_NO_AUGMENT,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_NO_FUNCTOR,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_UNQUOTE,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_NAT_INTEGRATE,INTERN_NAT_SOLVE_INTEGRATE);
    _th_add_precedence(s,env,INTERN_NAT_INTEGRATE,INTERN_NAT_INTEGRATE_SET);
    _th_add_precedence(s,env,INTERN_NAT_INTEGRATE_SET,INTERN_SETSIZE);

    _th_add_function(env,_th_parse(env,"(quantify a)"), _th_parse(env, "(-> (Bool) (Bool))"), _th_parse(env, "(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_QUANTIFY,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_ALL,INTERN_DOUBLE_ARROW) ;
    _th_add_function(env,_th_parse(env,"(=> a b c)"),_th_parse(env,"(-> (Tuple (Bool) (Bool) (Bool)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_ALL,INTERN_INFERENCE) ;
    _th_add_function(env,_th_parse(env,"(--> a b c)"),_th_parse(env,"(-> (Tuple (Bool) (Bool) (Bool)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_DOUBLE_ARROW,INTERN_ORIENTED_RULE) ;
    _th_add_function(env,_th_parse(env,"(@> a b c)"),_th_parse(env,"(-> (Tuple a b (Bool)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_MACRO_ARROW,INTERN_ORIENTED_RULE) ;
    _th_add_precedence(s,env,INTERN_FORCE_ORIENTED,INTERN_ORIENTED_RULE) ;
    _th_add_function(env,_th_parse(env,"(+> a b c)"),_th_parse(env,"(-> (Tuple a a (Bool)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(-> a b c)"),_th_parse(env,"(-> (Tuple a a (Bool)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(= a b c)"),_th_parse(env,"(-> (Tuple a a (Bool)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_ORIENTED_RULE,INTERN_UNORIENTED_RULE) ;
    _th_add_function(env,_th_parse(env,"(defined a)"),_th_parse(env,"(-> a (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(priority n x)"),_th_parse(env,"(-> (Tuple (Int) (Bool)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_UNORIENTED_RULE,INTERN_DEFINED) ;
    _th_add_function(env,_th_parse(env,"(|| a b)"),_th_parse(env,"(-> (Tuple (Bool) (Bool)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_DEFINED,INTERN_OR) ;
    _th_add_function(env,_th_parse(env,"(&& a b)"),_th_parse(env,"(-> (Tuple (Bool) (Bool)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(xor a b)"),_th_parse(env,"(-> (Tuple (Bool) (Bool)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_OR,INTERN_AND) ;
    _th_add_precedence(s,env,INTERN_AND,INTERN_XOR) ;
    _th_add_function(env,_th_parse(env,"(or a b)"),_th_parse(env,"(-> (Tuple (Bool) (Bool)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_DEFINED,INTERN_NC_OR) ;
    _th_add_function(env,_th_parse(env,"(and a b)"),_th_parse(env,"(-> (Tuple (Bool) (Bool)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(andq a b)"),_th_parse(env,"(-> (Tuple (Bool) (Bool)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(notl a b)"),_th_parse(env,"(-> (Tuple (Bool) (Bool)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_NC_OR,INTERN_NC_AND) ;
    _th_add_precedence(s,env,INTERN_NC_OR,INTERN_ANDQ) ;
    _th_add_function(env,_th_parse(env,"(not a)"),_th_parse(env,"(-> (Bool) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_AND,INTERN_NOT) ;
    _th_add_precedence(s,env,INTERN_NC_AND,INTERN_NOT) ;
    _th_add_precedence(s,env,INTERN_ANDQ,INTERN_NOT) ;
    _th_add_function(env,_th_parse(env,"(Default a)"),_th_parse(env,"(-> (Bool) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(Def a)"),_th_parse(env,"(-> (Bool) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(== a b)"),_th_parse(env,"(-> (Tuple a a) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_NOT,INTERN_EQUAL) ;
    _th_add_function(env,_th_parse(env,"(nless a b)"),_th_parse(env,"(-> (Tuple (Int) (Int)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_EQUAL,INTERN_NAT_LESS) ;
    _th_add_function(env,_th_parse(env,"(rless a b)"),_th_parse(env,"(-> (Tuple (Real) (Real)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_NAT_LESS,INTERN_RAT_LESS) ;
    _th_add_function(env,_th_parse(env,"(nplus a b)"),_th_parse(env,"(-> (Tuple (Int) (Int)) (Int))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_RAT_LESS,INTERN_NAT_PLUS) ;
    _th_add_function(env,_th_parse(env,"(npower a b)"),_th_parse(env,"(-> (Tuple (Int) (Int)) (Int))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_NAT_LESS,INTERN_NAT_POWER) ;
    _th_add_function(env,_th_parse(env,"(rplus a b)"),_th_parse(env,"(-> (Tuple (Real) (Real)) (Real))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_NAT_PLUS,INTERN_RAT_PLUS) ;
    _th_add_function(env,_th_parse(env,"(nminus a b)"),_th_parse(env,"(-> (Tuple (Int) (Int)) (Int))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_RAT_PLUS,INTERN_NAT_TIMES) ;
    _th_add_function(env,_th_parse(env,"(rminus a b)"),_th_parse(env,"(-> (Tuple (Real) (Real)) (Real))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_NAT_MINUS,INTERN_RAT_MINUS) ;
    _th_add_function(env,_th_parse(env,"(ntimes a b)"),_th_parse(env,"(-> (Tuple (Int) (Int)) (Int))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_RAT_MINUS,INTERN_NAT_DIVIDE) ;
    _th_add_function(env,_th_parse(env,"(rtimes a b)"),_th_parse(env,"(-> (Tuple (Real) (Real)) (Real))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_NAT_TIMES,INTERN_RAT_TIMES) ;
    _th_add_function(env,_th_parse(env,"(ndivide a b)"),_th_parse(env,"(-> (Tuple (Int) (Int)) (Int))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_RAT_TIMES,INTERN_NAT_MINUS) ;
    _th_add_function(env,_th_parse(env,"(rdivide a b)"),_th_parse(env,"(-> (Tuple (Real) (Real)) (Real))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_NAT_DIVIDE,INTERN_RAT_DIVIDE) ;
    _th_add_function(env,_th_parse(env,"(nmod a b)"),_th_parse(env,"(-> (Tuple (Int) (Int)) (Int))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_RAT_DIVIDE,INTERN_NAT_MOD) ;
    _th_add_function(env,_th_parse(env,"(rmod a b)"),_th_parse(env,"(-> (Tuple (Real) (Real)) (Real))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_NAT_MOD,INTERN_RAT_MOD) ;
    _th_add_function(env,_th_parse(env,"(size s)"),_th_parse(env,"(-> (String) (Int))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(q_nat n)"),_th_parse(env,"(-> (Int) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(q_var n)"),_th_parse(env,"(-> x (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(q_unusedVar n)"),_th_parse(env,"(-> x (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_Q_VAR,INTERN_AND) ;
    _th_add_precedence(s,env,INTERN_Q_UNUSED_VAR,INTERN_AND) ;
    _th_add_function(env,_th_parse(env,"(q_rat n)"),_th_parse(env,"(-> (Real) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(natrat a)"),_th_parse(env,"(-> (Int) (Real))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_RAT_MOD,INTERN_NAT_TO_RAT) ;
    _th_add_function(env,_th_parse(env,"(ratnat a)"),_th_parse(env,"(-> (Real) (Int))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_NAT_TO_RAT,INTERN_RAT_TO_NAT) ;
    _th_add_function(env,_th_parse(env,"(natstring a)"),_th_parse(env,"(-> (Int) (String))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_RAT_TO_NAT,INTERN_NAT_TO_STRING) ;
    _th_add_function(env,_th_parse(env,"(compatible_prec l r)"),_th_parse(env,"(-> (Tuple a b) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(marked_subset l r)"),_th_parse(env,"(-> (Tuple a a) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(char s i)"),_th_parse(env,"(-> (Tuple (String) (Int)) (Int))"),_th_parse(env,"(&& (nless -1 i) (nless i (size s)))"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(apply a b)"),_th_parse(env,"(=> (Tuple (=> a b) a) b)"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_NAT_TO_STRING,INTERN_APPLY) ;
    _th_add_function(env,_th_parse(env,"(union a b)"),_th_parse(env,"(-> (Tuple (Set x) (Set x)) (Set x))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_APPLY,INTERN_UNION) ;
    _th_add_precedence(s,env,INTERN_EQUAL,INTERN_MEMBER) ;
    _th_add_function(env,_th_parse(env,"(intersect a b)"),_th_parse(env,"(-> (Tuple (Set x) (Set x)) (Set x))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_UNION,INTERN_INTERSECT) ;
    _th_add_function(env,_th_parse(env,"(difference a b)"),_th_parse(env,"(-> (Tuple (Set x) (Set x)) (Set x))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_INTERSECT,INTERN_DIFFERENCE) ;
    _th_add_function(env,_th_parse(env,"(member a b)"),_th_parse(env,"(-> (Tuple x (Set x)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_SUBSET,INTERN_UNION) ;
    _th_add_precedence(s,env,INTERN_SEPARATE,INTERN_UNION) ;
    _th_add_function(env,_th_parse(env,"(subset a b)"),_th_parse(env,"(-> (Tuple (Set x) (Set x)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(separate a b)"),_th_parse(env,"(-> (Tuple (Set x) (Set x)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_MEMBER,INTERN_SUBSET) ;
    _th_add_precedence(s,env,INTERN_MEMBER,INTERN_SEPARATE) ;
    _th_add_function(env,_th_parse(env,"(concat a b)"),_th_parse(env,"(-> (Tuple (String) (String)) (String))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_CONCAT,INTERN_NAT_PLUS) ;
    _th_add_function(env,_th_parse(env,"(buildFunctor a b)"),_th_parse(env,"(-> (Tuple (String) a) b)"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_COMPATIBLE_PREC,INTERN_EQUAL) ;
    _th_add_precedence(s,env,INTERN_BUILD_FUNCTOR,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_FUNCTOR_ARGS,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_IS_APPL,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_ARG_COUNT,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_UNCOMPOSE,INTERN_DOUBLE_ARROW) ;
    _th_add_function(env,_th_parse(env,"(uncompose a b)"),_th_parse(env,"(=> (Tuple (=> a b) (=> c b)) (=> a c))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(functorArgs a b)"),_th_parse(env,"(-> a (List b))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(isAppl a)"),_th_parse(env,"(-> a (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(argCount a)"),_th_parse(env,"(-> a (Int))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(isFreeIn a b)"),_th_parse(env,"(-> (Tuple a b) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(removeAnd a b)"),_th_parse(env,"(-> (Bool) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(typeOf a)"),_th_parse(env,"(-> a (Type))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_precedence(s,env,INTERN_TYPE_OF, INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_MATCH,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_GET_TERMS,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_GET_LIMIT_TERM,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_CUT,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_EXCLUDE_SET,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_APPLY_CONTEXT,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_EVAL_COND,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_USE_CONTEXT,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_IN_CONTEXT,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_BLOCK_CONTEXT,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_SIMPLIFY_COND,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_CUT_LOCAL,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_FIRE_ON_CHANGE,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_IS_FREE_IN,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_REMOVE_AND,INTERN_DOUBLE_ARROW) ;
    _th_add_function(env,_th_parse(env,"(fireOnChange a b)"),_th_parse(env,"(-> (Tuple (Bool) (Bool)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(cut)"),_th_parse(env,"(-> (Tuple) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(excludeSet a)"),_th_parse(env,"(-> a (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(applyContext a)"),_th_parse(env,"(-> a (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(evalCond a)"),_th_parse(env,"(-> (Bool) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(useContext a)"),_th_parse(env,"(-> a (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(inContext a)"),_th_parse(env,"(-> a (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(blockContext a)"),_th_parse(env,"(-> a (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(simplifyCond a)"),_th_parse(env,"(-> (Bool) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(cutLocal)"),_th_parse(env,"(-> (Tuple) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    //_th_add_precedence(s,env,INTERN_DIFFERENCE,INTERN_MAP_SET) ;
    //_th_add_precedence(s,env,INTERN_DIFFERENCE,INTERN_FILTER_SET) ;
    _th_add_precedence(s,env,INTERN_FILTER_SET,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_MAP_SET,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_CHOOSE,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_CHOOSE_CONTEXT_RULE,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_LAMBDA,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_AND_SET,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_OR_SET,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_UNION_SET,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_SET_LIST,INTERN_DOUBLE_ARROW) ;
    _th_add_precedence(s,env,INTERN_LIST_SET,INTERN_DOUBLE_ARROW) ;
    _th_add_function(env,_th_parse(env,"(choose)"),_th_parse(env,"(-> (Tuple x (Set x)) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(chooseContextRule)"),_th_parse(env,"(-> (Bool) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(mapSet f s)"),_th_parse(env,"(=> (Tuple (=> a b) (Set a)) (Set b))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(filterSet f s)"),_th_parse(env,"(=> (Tuple (=> a (Bool)) (Set a)) (Set a))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(setlist s)"),_th_parse(env,"(=> (Set a) (List a))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(listset s)"),_th_parse(env,"(=> (List a) (Set a))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(unionSet f s)"),_th_parse(env,"(=> (Set (Set a)) (Set a))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(andSet f s)"),_th_parse(env,"(=> (Set a) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(orSet f s)"),_th_parse(env,"(=> (Set a) (Bool))"),_th_parse(env,"(True)"),0,NULL) ;

    _th_add_function(env,_th_parse(env,"(nintegrate f l h)"),_th_parse(env,"(=> (Tuple (=> (Int) (Int)) (Int) (Int)) (Int))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(nintegrateset f s)"),_th_parse(env,"(=> (Tuple (=> (Int) (Int)) (Set (Int))) (Int))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(nsolveintegrate f l h)"),_th_parse(env,"(=> (Tuple (=> (Int) (Int)) (Int) (Int)) (Int))"),_th_parse(env,"(True)"),0,NULL) ;
    _th_add_function(env,_th_parse(env,"(normal exp)"),_th_parse(env, "(=> a a)"),_th_parse(env,"(True)"),0,NULL);

    _th_add_property(env,_th_parse(env,"(-> (preceq 0 y) (True) (True))")) ;

    _th_add_property(env,_th_parse(env,"(-> (prune (== x y) z) (True) (q_var x))")) ;

    //_th_add_property(env,_th_parse(env,"(-> (|| (inContext x) y) (True) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (&& (inContext x) y) y (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (not (inContext x)) (False) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (|| (useContext x) y) (True) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (&& (useContext x) y) y (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (not (useContext x)) (False) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (|| (blockContext x) y) (True) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (&& (blockContext x) y) y (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (not (blockContext x)) (False) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (|| (applyContext x) y) (True) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (&& (applyContext x) y) y (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (not (applyContext x)) (False) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (|| (excludeSet x) y) (True) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (&& (excludeSet x) y) y (True))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (not (excludeSet x)) (False) (True))")) ;
    //_th_add_property(env,_th_parse(env,"(+> (|| (&& a b) c) (&& (|| a c) (|| b c)) (rewritable (QUOTE (|| a c))))")) ;
    //_th_add_property(env,_th_parse(env,"(+> (-> (union a b) c (True)) (-> a (difference c b) (True)) (and (separate a b) (compatible_prec a (difference c b))))")) ;
    //printf("Rules:\n");
    //_th_print_disc(env->apply_properties);
    //_th_add_property(env,_th_parse(env,"(-> (prune x y) (True) (q_var x))")) ;
    //_th_add_property(env,_th_parse(env,"(-> (prune (member x y) z) (and (applyContext \"mainContext\")) (q_var x))")) ;

	//_th_add_equality_rules(s,env);
	//_th_add_set_rules(s,env);
	//_th_add_setsize_rules(s,env);
	//_th_add_calculus_rules(s,env);
	//_th_add_boolean_rules(s,env);
	//_th_add_solve_rules(s,env);

    return env ;
}

static unsigned arg_start, arg_size ;
static struct _ex_intern **args, **all_args ;

#define ARG_INCREMENT 4000

static void set_start(int x)
{
    arg_start += x ;
    args = all_args + arg_start ;
}

static void check_size(unsigned size)
{
    if (arg_start + size > arg_size) {
        int old_size = arg_size;
        struct _ex_intern **old_args = all_args;
        int i;
        //printf("Before %d\n", arg_size);
        arg_size = arg_start + size + ARG_INCREMENT ;
        //printf("Here %d\n", arg_size);
        all_args = (struct _ex_intern **)MALLOC(sizeof(struct _ex_intern *) * arg_size) ;
        if (all_args==NULL) {
            fprintf(stderr,"env: check_size: Error in malloc\n");
            exit(1);
        }
        for (i = 0; i < old_size; ++i) all_args[i] = old_args[i];
        set_start(0) ;
    }
}

struct _ex_intern *_th_flatten_top(struct env *env, struct _ex_intern *e)
{
    int i, j, pos ;
    int change = 0 ;
    struct _ex_intern *f ;

    if (!_th_is_ac(env,e->u.appl.functor) && !_th_is_a(env,e->u.appl.functor)) return e;

    for (i=0, pos=0; i < e->u.appl.count; ++i) {
        if (e->u.appl.args[i]->type==EXP_APPL &&
            e->u.appl.functor==e->u.appl.args[i]->u.appl.functor) {
            change = 1 ;
            set_start(pos) ;
            f = _th_flatten_top(env,e->u.appl.args[i]) ;
            set_start(0-pos) ;
            for (j = 0; j < f->u.appl.count; ++j) {
                check_size(pos+1) ;
                args[pos++] = f->u.appl.args[j] ;
            }
        } else {
            check_size(pos+1) ;
            args[pos++] = e->u.appl.args[i] ;
        }
    }
    if (change) {
        return _ex_intern_appl_env(env,e->u.appl.functor,pos,args) ;
    } else {
        return e ;
    }
}

struct _ex_intern *_th_flatten(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern *f, *g, **args ;
    int i ;

    switch (e->type) {
        case EXP_APPL:
            if (_th_is_ac(env,e->u.appl.functor) || _th_is_a(env,e->u.appl.functor)) {
                e = _th_flatten_top(env,e) ;
            }
            args = ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = _th_flatten(env,e->u.appl.args[i]) ;
            }
            return _ex_intern_appl_env(env,e->u.appl.functor, e->u.appl.count,args) ;
        case EXP_QUANT:
            f = _th_flatten(env,e->u.quant.exp) ;
            g = _th_flatten(env,e->u.quant.cond) ;
            return _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,e->u.quant.vars,f,g) ;
        default:
            return e ;
    }

}

int _th_exp_depth(struct _ex_intern *e)
{
    int i, depth, max;

    switch (e->type) {
        case EXP_APPL:
            max = 0;
            for (i = 0; i < e->u.appl.count; ++i) {
                depth = _th_exp_depth(e->u.appl.args[i]);
                if (depth > max) max = depth;
            }
            return max;
        case EXP_QUANT:
            depth = _th_exp_depth(e->u.quant.exp);
            max = _th_exp_depth(e->u.quant.cond);
            return (depth>max)?depth:max;
        default:
            return 1;
    }
}

struct _ex_intern *_th_flatten_level(struct env *env, struct _ex_intern *e, int level)
{
    struct _ex_intern *f, *g, **args ;
    int i ;

    if (level<1) return e;

    switch (e->type) {
        case EXP_APPL:
            if (_th_is_ac(env,e->u.appl.functor) || _th_is_a(env,e->u.appl.functor)) {
                e = _th_flatten_top(env,e) ;
            }
            args = ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = _th_flatten_level(env,e->u.appl.args[i], level-1) ;
            }
            return _ex_intern_appl_env(env,e->u.appl.functor, e->u.appl.count,args) ;
        case EXP_QUANT:
            f = _th_flatten_level(env,e->u.quant.exp,level-1) ;
            g = _th_flatten_level(env,e->u.quant.cond,level-1) ;
            return _ex_intern_quant(e->u.quant.quant,e->u.quant.var_count,e->u.quant.vars,f,g) ;
        default:
            return e ;
    }

}

struct directive *_th_get_pp_directives(struct env *env)
{
    return env->pp_directives ;
}

void _th_set_pp_directives(struct env *env, struct directive *d)
{
    env->rebuild_trie = 1 ;
    env->pp_directives = d ;
}

static struct symbol_info *copy_table(int space, struct symbol_info *table)
{
    struct symbol_info *copy;
    
    if (table==NULL) return NULL;

    copy = (struct symbol_info *)_th_alloc(space, sizeof(struct symbol_info));

    memcpy(copy, table, sizeof(struct symbol_info));

    copy->next = copy_table(space, table->next);

    return copy;
}

struct env *_th_copy_env(int space, struct env *env)
/*
 * Create a copy of the environment to which data can be added without
 * effecting the original.  Parts are shallow copied and parts
 * are deep copied.
 */
{
    struct env *copy = _th_new_empty_env(space, env->symbol_size);
    int i;

    copy->all_properties = _th_copy_disc(space, env->all_properties);
    copy->apply_properties = _th_copy_disc(space, env->apply_properties);
    copy->derive_properties = _th_copy_disc(space, env->derive_properties);
    copy->augment_properties = _th_copy_disc(space, env->augment_properties);
    copy->macro_properties = _th_copy_disc(space, env->macro_properties);
    copy->context_properties = _th_copy_small(space, env->context_properties);
    copy->apply_context_properties = _th_copy_small(space, env->apply_context_properties);
    copy->context_stack = env->context_stack;
    copy->pp_directives = env->pp_directives;
    copy->rebuild_trie = 1;
    copy->rules = env->rules;
    copy->cr = env->cr;
    copy->context_level = env->context_level;
    copy->state_checks = env->state_checks;
    copy->heuristics = env->heuristics;

    for (i = 0; i < copy->symbol_size; ++i) {
        copy->table[i] = copy_table(space, env->table[i]);
    }

    return copy;
}

struct add_list *_th_rollback(struct env *env, struct _ex_intern *rule)
{
    struct context_stack *cs = env->context_stack;
    struct add_list *a = NULL, *n;
    struct rule *r = env->context_rules;

    while (r && r->rule != rule) {
        if (cs != NULL && cs->context_rules==r) {
            cs = cs->next;
        }
        n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        n->next = a;
        n->e = r->rule;
        a = n;
        r = r->next;
    }
    if (r) {
        if (cs != NULL && cs->context_rules==r) {
            cs = cs->next;
        }
        n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        n->next = a;
        n->e = r->rule;
        a = n;
        r = r->next;
    }
    while (r && (!cs || r != cs->context_rules)) {
        n = (struct add_list *)_th_alloc(REWRITE_SPACE,sizeof(struct add_list));
        n->next = a;
        n->e = r->rule;
        a = n;
        r = r->next;
    }
    if (cs) cs = cs->next;
    if (cs) {
        env->context_properties = env->context_stack->context_properties;
        env->apply_context_properties = env->context_stack->apply_context_properties;
        env->context_rules = env->context_stack->context_rules;
        env->simplified_rules = env->context_stack->simplified_rules;
        env->blocked_rules = env->context_stack->blocked_rules;
        env->variables = env->context_stack->variables;
        env->default_type = env->context_stack->default_type;
        env->min_table = env->context_stack->min_table;
        env->max_table = env->context_stack->max_table;
        env->rule_operand_table = env->context_stack->rule_operand_table;
        env->rule_double_operand_table = env->context_stack->rule_double_operand_table;
        env->var_solve_table = env->context_stack->var_solve_table;
        env->rewrite_chain = env->context_stack->rewrite_chain;
        //fprintf(stderr, "Assigning rewrite_chain 1 %x %x\n", env, env->rewrite_chain);
        env->context_stack = env->context_stack->next;
    } else {
        int i;
        env->context_properties = _th_new_small(REWRITE_SPACE) ;
        env->apply_context_properties = _th_new_small(REWRITE_SPACE) ;
	    env->context_rules = NULL ;
     	env->variables = NULL ;
        env->default_type = NULL;
        env->rewrite_chain = NULL;
        //fprintf(stderr, "Assigning rewrite_chain 2 %x %x\n", env, env->rewrite_chain);
    	env->rule_operand_table = (struct rule_operand_list **)_th_alloc(REWRITE_SPACE,sizeof(struct rule_operand_list *) * RULE_OPERAND_HASH);
	    env->rule_double_operand_table = (struct rule_double_operand_list **)_th_alloc(REWRITE_SPACE,sizeof(struct rule_double_operand_list *) * RULE_OPERAND_HASH);
	    for (i = 0; i < RULE_OPERAND_HASH; ++i) {
		    env->rule_operand_table[i] =  NULL;
		    env->rule_double_operand_table[i] =  NULL;
        }
	    env->var_solve_table = (struct var_solve_list **)_th_alloc(REWRITE_SPACE,sizeof(struct var_solve_list *) * RULE_OPERAND_HASH);
	    for (i = 0; i < VAR_SOLVE_HASH; ++i) {
		    env->var_solve_table[i] =  NULL;
        }
	    env->min_table = (struct min_max_list **)_th_alloc(REWRITE_SPACE,sizeof(struct min_max_list *) * MIN_MAX_HASH);
	    env->max_table = (struct min_max_list **)_th_alloc(REWRITE_SPACE,sizeof(struct min_max_list *) * MIN_MAX_HASH);
	    for (i = 0; i < MIN_MAX_HASH; ++i) {
		    env->min_table[i] = env->max_table[i] = NULL;
        }
    }

    return a;
}

