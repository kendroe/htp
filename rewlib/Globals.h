/*
 * globals.h
 *
 * Global variable and procedure declarations.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#ifndef REWLIB_GLOBALS_H
#define REWLIB_GLOBALS_H

struct _ex_intern;
struct rule_operand_list;
struct rule_double_operand_list;
struct var_solve_list;
struct learn_info;
struct rule;

#include <stdio.h>
#include <stdlib.h>

//#define USE_MALLOC
#ifdef USE_MALLOC
#define ALLOCA(x) malloc(x)
#else
#ifdef WIN32
#define ALLOCA _alloca
#else
#define ALLOCA alloca
#endif
#endif

#ifdef WIN32
#define TIME_LIMIT 600
#else
#define TIME_LIMIT 3600
#endif

#define EXPIRATION 1155021962+900*24*60*60
 
/* Debug stuff */
int _th_check_restart(int t);
#ifdef FAST
void _tree_init(char *log);
void _tree_shutdown();
void _zone_increment();
void _tree_set_time_limit(unsigned t);

#define _tree_indent()
#define _tree_undent()
#define _zone_enter_sub()
#define _zone_exit_sub()
#define _th_save_cache(cache)
#define _th_reference_cache(cache)
#define _tree_start_local(n)
#define _tree_finish_local()
#define _tree_print_exp(s,exp)

#define _zone_print0(x)
#define _zone_print1(x,a)
#define _zone_print2(x,a,b)
#define _zone_print3(x,a,b,c)
#define _zone_print4(x,a,b,c,d)
#define _zone_print5(x,a,b,c,d,e)
#define _zone_print6(x,a,b,c,d,e,f)
#define _zone_print_exp(s,e)

#define _tree_print0(x)
#define _tree_print1(x,a)
#define _tree_print2(x,a,b)
#define _tree_print3(x,a,b,c)
#define _tree_print4(x,a,b,c,d)
#define _tree_print5(x,a,b,c,d,e)
#define _tree_print6(x,a,b,c,d,e,f)

#define _d_print(x)
#define _d_print1(x,y)
#define _d_print2(x,a,b)
#define _d_print3(x,a,b,c)
#define _d_print4(x,a,b,c,d)
#define _d_print5(x,a,b,c,d,e)
#define _d_print6(x,a,b,c,d,e,f)

#define zone_active() 0

#else

#define _tree_print0(x) _tree_print(x)
#define _tree_print1(x,a) _tree_print(x,a)
#define _tree_print2(x,a,b) _tree_print(x,a,b)
#define _tree_print3(x,a,b,c) _tree_print(x,a,b,c)
#define _tree_print4(x,a,b,c,d) _tree_print(x,a,b,c,d)
#define _tree_print5(x,a,b,c,d,e) _tree_print(x,a,b,c,d,e)
#define _tree_print6(x,a,b,c,d,e,f) _tree_print(x,a,b,c,d,e,f)

void _tree_init(char *log) ;
void _tree_shutdown() ;
void _tree_indent() ;
void _tree_undent() ;
int _tree_get_indent() ;
void _zone_increment() ;
void _tree_print(char *x, ...) ;
void _zone_print(char *x, ...) ;
void _zone_enter_sub() ;
void _zone_exit_sub() ;
void _th_save_cache(unsigned cache) ;
void _th_reference_cache(unsigned cache) ;
void _tree_start_local(char *n);
void _tree_finish_local();
void _tree_print_exp(char *s, struct _ex_intern *exp);

void _tree_set_time_limit(unsigned t);

extern int _info_flag ;
extern int _tree_interactive, _tree_core ;
extern int _tree_start, _tree_end ;
extern int _tree_zone ;
extern int _tree_subzone ;
extern int _tree_subzone_level ;
extern int _tree_sub ;
extern int _tree_sub2 ;
extern int _tree_mute ;
extern int _tree_count ;

#define _zone_active() ((!_tree_mute) && _tree_zone >= _tree_start && _tree_zone <= _tree_end && (_tree_subzone_level==0 || _tree_sub < 0 || (_tree_subzone>=_tree_sub && _tree_subzone<=_tree_sub2)))
#define _zone_print0(x) if (_zone_active()) _tree_print(x) ;
#define _zone_print1(x,a) if (_zone_active()) _tree_print(x,a) ;
#define _zone_print2(x,a,b) if (_zone_active()) _tree_print(x,a,b) ;
#define _zone_print3(x,a,b,c) if (_zone_active()) _tree_print(x,a,b,c) ;
#define _zone_print4(x,a,b,c,d) if (_zone_active()) _tree_print(x,a,b,c,d) ;
#define _zone_print5(x,a,b,c,d,e) if (_zone_active()) _tree_print(x,a,b,c,d,e) ;
#define _zone_print6(x,a,b,c,d,e,f) if (_zone_active()) _tree_print(x,a,b,c,d,e,f) ;
#define _zone_print_exp(s,e) if(_zone_active()) _tree_print_exp(s,e) ;
#ifdef _DEBUG
#define _d_print(x) printf(x)
#define _d_print1(x,y) printf(x,y)
#define _d_print2(x,a,b) printf(x,a,b)
#define _d_print3(x,a,b,c) printf(x,a,b,c)
#define _d_print4(x,a,b,c,d) printf(x,a,b,c,d)
#define _d_print5(x,a,b,c,d,e) printf(x,a,b,c,d,e)
#define _d_print6(x,a,b,c,d,e,f) printf(x,a,b,c,d,e,f)
#define _debug_print(x) _tree_print(x)
#define _debug_print1(x,y) _tree_print(x,y)
#define _debug_print2(x,a,b) _tree_print(x,a,b)
#define _debug_print3(x,a,b,c) _tree_print(x,a,b,c)
#define _debug_print4(x,a,b,c,d) _tree_print(x,a,b,c,d)
#define _debug_print5(x,a,b,c,d,e) _tree_print(x,a,b,c,d,e)
#define _debug_print6(x,a,b,c,d,e,f) _tree_print(x,a,b,c,d,e,f)
#define _debug_zone_print(x) _zone_print(x)
#define _debug_zone_print1(x,y) _zone_print(x,y)
#define _debug_zone_print2(x,a,b) _zone_print(x,a,b)
#define _debug_zone_print3(x,a,b,c) _zone_print(x,a,b,c)
#define _debug_zone_print4(x,a,b,c,d) _zone_print(x,a,b,c,d)
#define _debug_zone_print5(x,a,b,c,d,e) _zone_print(x,a,b,c,d,e)
#define _debug_zone_print6(x,a,b,c,d,e,f) _zone_print(x,a,b,c,d,e,f)
#define _debug_indent() _tree_indent()
#define _debug_undent() _tree_undent()
#define _info_print(x) _tree_print(x)
#define _info_print1(x,a) _tree_print(x,a)
#define _info_print2(x,a,b) _tree_print(x,a,b)
#define _info_print3(x,a,b,c) _tree_print(x,a,b,c)
#define _info_print4(x,a,b,c,d) _tree_print(x,a,b,c,d)
#define _info_print5(x,a,b,c,d,e) _tree_print(x,a,b,c,d,e)
#define _info_print6(x,a,b,c,d,e,f) _tree_print(x,a,b,c,d,e,f)
#else
#define _d_print(x)
#define _d_print1(x,y)
#define _d_print2(x,a,b)
#define _d_print3(x,a,b,c)
#define _d_print4(x,a,b,c,d)
#define _d_print5(x,a,b,c,d,e)
#define _d_print6(x,a,b,c,d,e,f)
#define _debug_print(x)
#define _debug_print1(x,y)
#define _debug_print2(x,a,b)
#define _debug_print3(x,a,b,c)
#define _debug_print4(x,a,b,c,d)
#define _debug_print5(x,a,b,c,d,e)
#define _debug_print6(x,a,b,c,d,e,f)
#define _debug_zone_print(x)
#define _debug_zone_print1(x,y)
#define _debug_zone_print2(x,a,b)
#define _debug_zone_print3(x,a,b,c)
#define _debug_zone_print4(x,a,b,c,d)
#define _debug_zone_print5(x,a,b,c,d,e)
#define _debug_zone_print6(x,a,b,c,d,e,f)
#define _debug_indent()
#define _debug_undent()
#define _info_print(x) if (_info_flag) _tree_print(x)
#define _info_print1(x,a) if (_info_flag) _tree_print(x,a)
#define _info_print2(x,a,b) if (_info_flag) _tree_print(x,a,b)
#define _info_print3(x,a,b,c) if (_info_flag) _tree_print(x,a,b,c)
#define _info_print4(x,a,b,c,d) if (_info_flag) _tree_print(x,a,b,c,d)
#define _info_print5(x,a,b,c,d,e) if (_info_flag) _tree_print(x,a,b,c,d,e)
#define _info_print6(x,a,b,c,d,e,f) if (_info_flag) _tree_print(x,a,b,c,d,e,f)
#endif
#endif

int _th_get_indent();
void _th_set_indent(int indent);

/* Spaces for allocation */

#define INTERN_SPACE      0
#define INTERN_TEMP_SPACE 1
#define MATCH_SPACE       2
#define REWRITE_SPACE     3
#define TERM_CACHE_SPACE  4
#define TRANSITIVE_SPACE  5
#define CACHE_SPACE       6
#define PARSE_SPACE       7
#define TYPE_SPACE        8
#define ENVIRONMENT_SPACE 9
#define SEARCH_SPACE      10
#define CHECK_SPACE       11
#define HEURISTIC_SPACE   12
#define LEARN_ENV_SPACE   13
#define DERIVATION_BASE   14

/* alloc.c */
void _th_alloc_init() ;
void _th_alloc_shutdown() ;
char *_th_alloc(int,int) ;
void _th_alloc_clear(int) ;
int _th_alloc_check_release(int space, char *pos);
void _th_alloc_release(int, char *) ;
char *_th_alloc_mark(int) ;
int _th_check_alloc_block(int space, char *c);

/* bignum.c */
void _th_init_bignum() ;
void _th_big_print_hex(unsigned *) ;
unsigned *_th_big_add(unsigned *,unsigned *) ;
unsigned *_th_big_accumulate(unsigned *,unsigned *) ;
unsigned *_th_big_accumulate_small(unsigned *a, int x);
unsigned *_th_big_sub(unsigned *,unsigned *) ;
int _th_big_less(unsigned *,unsigned *) ;
int _th_big_equal(unsigned *,unsigned *) ;
unsigned *_th_big_multiply(unsigned *,unsigned *) ;
unsigned *_th_big_divide(unsigned *,unsigned *) ;
unsigned *_th_big_mod(unsigned *,unsigned *) ;
unsigned *_th_big_power(unsigned *,unsigned *) ;
int _th_big_is_negative(unsigned *) ;
#define _th_big_is_zero(x) (x[0]==1 && x[1]==0)
unsigned *_th_big_copy(int,unsigned *) ;
unsigned *_th_complement(unsigned *) ;
unsigned *_th_big_gcd(unsigned *x, unsigned *y);

/* intern.c */
void _th_intern_init() ;
int _th_intern_count() ;
void _th_intern_shutdown() ;
int _th_intern(char *) ;
char *_th_intern_decode(int) ;
int _th_intern_concat(int,int) ;
int _th_intern_is_legal(int) ;
unsigned _th_intern_get_data(int) ;
void _th_intern_set_data(int,unsigned) ;
unsigned _th_intern_get_data2(int) ;
void _th_intern_set_data2(int,unsigned) ;
void _th_intern_push_quant(unsigned, unsigned, int) ;
void _th_intern_pop_quant(unsigned) ;
int _th_intern_get_quant_level(unsigned) ;

/* balanced.c */
struct Node ;

void _bl_save_value(unsigned) ;
unsigned _bl_find_int(struct Node *,unsigned) ;
unsigned _bl_insert_int(struct Node **,unsigned) ;
unsigned _bl_find_int2(struct Node *,unsigned *) ;
unsigned _bl_insert_int2(struct Node **,unsigned *) ;
unsigned _bl_find_int3(struct Node *,unsigned *) ;
unsigned _bl_insert_int3(struct Node **,unsigned *) ;
unsigned _bl_find_intc(struct Node *,char *) ;
unsigned _bl_insert_intc(struct Node **,char *) ;
unsigned _bl_find_ints(struct Node *,unsigned *) ;
unsigned _bl_insert_ints(struct Node **,unsigned *) ;

/* exp_intern.c */
void _ex_init() ;
void _ex_shutdown() ;

#define EXP_INTEGER    1
#define EXP_RATIONAL   2
#define EXP_STRING     3
#define EXP_APPL       4
#define EXP_CASE       5
#define EXP_QUANT      6
#define EXP_VAR        7
#define EXP_MARKED_VAR 8
#define EXP_INDEX      9

#define MAX_ARGS 100000

struct _ex_intern *_ex_intern_integer(unsigned *) ;
struct _ex_intern *_ex_intern_small_integer(int) ;
struct _ex_intern *_ex_intern_small_rational(int,int) ;
struct _ex_intern *_ex_intern_rational(unsigned *,unsigned *) ;
struct _ex_intern *_ex_intern_string(char *) ;
//int _ex_is_new;
struct _ex_intern *_ex_intern_appl(unsigned,int,struct _ex_intern **) ;
struct _ex_intern *_ex_intern_case(struct _ex_intern *,int,struct _ex_intern **) ;
struct _ex_intern *_ex_intern_quant(unsigned,int,unsigned *,struct _ex_intern *,struct _ex_intern *) ;
struct _ex_intern *_ex_intern_var(unsigned) ;
struct _ex_intern *_ex_intern_marked_var(unsigned,int) ;
struct _ex_intern *_ex_intern_index(struct _ex_intern *,unsigned,int) ;
struct _ex_intern *_ex_intern_string(char *) ;
struct _ex_intern *_ex_find_equality(struct _ex_intern *left, struct _ex_intern *right);

struct env ;

void _ex_used_in_push();
void _ex_used_in_pop();
void _ex_add_used_in(struct _ex_intern *e);
void _ex_push() ;
void _ex_pop() ;
struct _ex_intern *_ex_reintern(struct env *,struct _ex_intern *) ;
int _ex_valid_expression(struct _ex_intern *e) ;
void _ex_release() ;

struct _ex_base {
    struct _ex_intern *next ;
    unsigned type : 4 ;
    int has_special_term : 1 ;
    int mark1 : 1 ;
    int mark2 : 1 ;
    int no_top_var : 1 ;
    int can_cache : 1 ;
    int in_backchain : 1 ;
    int unate_processed : 1 ;
    int unate_true : 1 ;
    int unate_false : 1 ;
    int is_marked_term : 1;
    int rule_simplified : 1;
    int rule_blocked : 1;
    int cache_bad : 1;
    int in_hash : 1;
    int in_rewrite ;
    unsigned rule_in_use : 10 ;
    struct _ex_intern *next_cache ;
    struct _ex_intern *rewrite ;
    struct _ex_intern *find ;
    struct _ex_intern *marked_term ;
    struct _ex_intern *unmarked_term ;
    struct _ex_intern *user1;
    struct _ex_intern *user2;
    struct _ex_intern *user3;
    struct term_cache *term_cache;
    struct _ex_intern *type_inst;
    struct _ex_intern *prepare;
    struct _ex_intern *sig;
    struct _ex_intern *merge;
    struct _ex_intern *original;
    struct add_list *explanation;
    struct add_list *used_in;
    struct add_list *cached_in;
    int used_level;
    int height;
    unsigned print_line ;
    unsigned cache_line;
    struct _ex_intern *print_next;
    struct _ex_intern *next_term, *prev_term;
#ifdef _DEBUG
    int rule_use_count ;
    int rule_try_count ;
    struct _ex_intern *next_rule ;
    int backchain_tries ;
    struct _ex_intern *next_backchain ;
#endif
} ;

#define MAX_IN_USE 1023

struct _ex_intern *_th_top_rule ;
struct _ex_intern *_th_top_backchain ;
extern int _th_in_rewrite ;

struct _ex_intern {
    struct _ex_intern *next ;
    unsigned type : 4 ;
    int has_special_term : 1 ;
    int mark1 : 1 ;
    int mark2 : 1 ;
    int no_top_var : 1 ;
    int can_cache : 1 ;
    int in_backchain : 1 ;
    int unate_processed : 1 ;
    int unate_true : 1 ;
    int unate_false : 1 ;
    int is_marked_term : 1;
    int rule_simplified : 1;
    int rule_blocked : 1;
    int cache_bad : 1;
    int in_hash : 1;
    int in_rewrite ;
    unsigned rule_in_use : 10 ;
    struct _ex_intern *next_cache ;
    struct _ex_intern *rewrite ;
    struct _ex_intern *find ;
    struct _ex_intern *marked_term ;
    struct _ex_intern *unmarked_term ;
    struct _ex_intern *user1;
    struct _ex_intern *user2;
    struct _ex_intern *user3;
    struct term_cache *term_cache;
    struct _ex_intern *type_inst;
    struct _ex_intern *prepare;
    struct _ex_intern *sig;
    struct _ex_intern *merge;
    struct _ex_intern *original;
    struct add_list *explanation;
    struct add_list *used_in;
    struct add_list *cached_in;
    int used_level;
    int height;
    unsigned print_line ;
    unsigned cache_line;
    struct _ex_intern *print_next;
    struct _ex_intern *next_term, *prev_term;
#ifdef _DEBUG
    int rule_use_count ;
    int rule_try_count ;
    struct _ex_intern *next_rule ;
    int backchain_tries ;
    struct _ex_intern *next_backchain ;
#endif
    union u {
        unsigned integer[1] ;
        struct rat { unsigned int *numerator, *denominator ; } rational ;
        char string[1] ;
        struct ap { unsigned functor ; int count ; struct _ex_intern *args[1] ; } appl ;
        struct cs { struct _ex_intern *exp ; int count ; struct _ex_intern *args[1] ; } case_stmt ;
        struct qu { unsigned quant ; struct _ex_intern *exp, *cond; int var_count ; unsigned vars[1] ; } quant ;
        unsigned var ;
        struct mv { unsigned var ; int quant_level ; } marked_var ;
        struct in { struct _ex_intern *exp; unsigned functor; int term ; } index ;
    } u ;
} ;

extern struct _ex_intern *_ex_true ;
extern struct _ex_intern *_ex_false ;
extern struct _ex_intern *_ex_nil ;
extern struct _ex_intern *_ex_bool ;
extern struct _ex_intern *_ex_int ;
extern struct _ex_intern *_ex_real ;
extern struct _ex_intern *_ex_array ;
extern struct _ex_intern *_ex_one ;
extern struct _ex_intern *_ex_r_one ;

void _th_collect_and_print_classes(struct env *env, int stop_on_errors);
void _ex_add_term(struct _ex_intern *e);
void _ex_delete_term(struct _ex_intern *e);
struct _ex_intern *_ex_get_first_term();

/* parse.c */
void _th_parse_init() ;
extern struct _ex_intern *_th_parse(struct env *,char *) ;
unsigned *_th_parse_number(char *) ;

/* svc_parse.c */
void _th_svc_parse_init() ;
extern struct _ex_intern *_th_svc_parse(struct env *,char *) ;
struct _ex_intern *_th_process_svc_file(struct env *env, char *name) ;
struct _ex_intern *_th_process_svc_script(struct env *env, char *name) ;

/* print.c */
extern int _th_block_complex;
char *_th_print_exp(struct _ex_intern *exp) ;
char *_th_tree_exp(unsigned line, struct _ex_intern *exp) ;
void _th_print_init() ;
void _th_print_shutdown() ;
void _th_print_number(unsigned *) ;
char *_th_print_buf ;
void _th_adjust_buffer(int) ;
extern int _th_pos ;
void _th_get_position(char *text, unsigned cound, unsigned *index, int pos, int *start, int *end) ;

/* exp_utils.c */
void _th_clear_var_data(struct _ex_intern *) ;
void _th_increment_var_data(struct _ex_intern *) ;
void _th_decrement_var_data(struct _ex_intern *) ;
void _th_increment_var_data2(struct _ex_intern *) ;
void _th_decrement_var_data2(struct _ex_intern *) ;
int _th_has_duplicate_var(struct _ex_intern *e) ;

unsigned *_th_get_free_vars(struct _ex_intern *, int *) ;
int _th_is_free_in(struct _ex_intern *, unsigned) ;
int _th_is_marked_in(struct _ex_intern *, unsigned) ;
void _th_unflag_free_vars(struct _ex_intern *) ;
unsigned *_th_get_free_vars_leave_marked(struct _ex_intern *, int *) ;
unsigned *_th_cont_free_vars_leave_marked(struct _ex_intern *, int *) ;
unsigned *_th_get_all_vars(struct _ex_intern *, int *) ;
unsigned _th_name_away_from_list(int,unsigned *, unsigned) ;
unsigned _th_name_away(struct _ex_intern *,unsigned) ;
void _th_multi_name_away(struct _ex_intern *e,unsigned var, int count, unsigned *array) ;
unsigned *_th_get_marked_vars(struct _ex_intern *, int *) ;
unsigned *_th_get_marked_vars_leave_marked(struct _ex_intern *, int *) ;
struct _ex_intern *_th_mark_vars(struct env *,struct _ex_intern *) ;
struct _ex_intern *_th_mark_vars_list(struct env *,struct _ex_intern *,int,unsigned *) ;
struct _ex_intern *_th_mark_var(struct env *,struct _ex_intern *,unsigned) ;
struct _ex_intern *_th_unmark_vars(struct env *,struct _ex_intern *) ;
struct _ex_intern *_th_rename_marked_vars(struct env *,struct _ex_intern *,unsigned,unsigned) ;
struct _ex_intern *_th_unmark_vars_list(struct env *,struct _ex_intern *,int,unsigned *) ;
struct _ex_intern *_th_unmark_var(struct env *,struct _ex_intern *,unsigned) ;
struct _ex_intern *_th_get_term(struct _ex_intern *,int,int *) ;
struct _ex_intern *_th_replace_term(struct env *,struct _ex_intern *,int,int *,struct _ex_intern *) ;
struct _ex_intern *_th_remove_marked_vars(struct env *, struct _ex_intern *, int) ;

/* subst.c */
struct _ex_unifier ;

struct _ex_unifier *_th_new_unifier(unsigned) ;
struct _ex_unifier *_th_add_pair(unsigned,struct _ex_unifier *,unsigned,struct _ex_intern *) ;
struct _ex_unifier *_th_copy_unifier(unsigned,struct _ex_unifier *) ;
struct _ex_unifier *_th_shallow_copy_unifier(unsigned,struct _ex_unifier *) ;
struct _ex_intern *_th_apply(struct _ex_unifier *,unsigned) ;
struct _ex_intern *_th_subst(struct env *,struct _ex_unifier *,struct _ex_intern *) ;
struct _ex_intern *_th_marked_subst(struct env *,struct _ex_unifier *,struct _ex_intern *) ;
struct _ex_unifier *_th_select_subs(unsigned,struct _ex_unifier *,unsigned *) ;
struct _ex_unifier *_th_remove_subs(unsigned,struct _ex_unifier *,unsigned *) ;
struct _ex_unifier *_th_merge_subs(unsigned,struct _ex_unifier *,struct _ex_unifier *) ;
struct _ex_unifier *_th_compose(unsigned,struct _ex_unifier *,struct _ex_unifier *) ;
void *_th_dom_init(int,struct _ex_unifier *) ;
unsigned _th_dom_next(void *) ;
void _th_update_unifier(struct env *,unsigned,struct _ex_intern *,struct _ex_unifier *) ;

void _th_print_unifier(struct _ex_unifier *) ;
void _th_zone_print_unifier(struct _ex_unifier *) ;
struct _ex_intern *_th_unifier_as_exp(struct env *env, struct _ex_unifier *u) ;

/* disc.c */
struct small_disc ;
struct disc ;

struct small_disc *_th_new_small(int) ;
struct small_disc *_th_copy_small(int,struct small_disc *) ;
struct small_disc *_th_push_small(int,struct small_disc *) ;
void _th_disc_mark_tested(struct small_disc *, struct _ex_intern *) ;
void _th_disc_mark_used(struct small_disc *, struct _ex_intern *) ;
int _th_add_small(int,struct env *,struct small_disc *,struct _ex_intern *, int) ;
void _th_init_find_small(struct small_disc *,struct _ex_intern *, void **) ;
struct _ex_intern *_th_next_find_small(void **, int *) ;
struct _ex_intern *_th_get_small_set(struct env *env, struct small_disc *d) ;
void _th_add_disc(int s,struct disc *disc, struct _ex_intern *e, int priority) ;

struct disc_iterator {
    struct small_rule *results[MAX_ARGS+3] ;
    int result_count ;
} ;

struct disc *_th_new_disc(int) ;
void _th_init_find(struct disc_iterator *, struct disc *,struct _ex_intern *) ;
struct _ex_intern *_th_next_find(struct disc_iterator *, int *) ;
struct disc *_th_copy_disc(int,struct disc *) ;
void _th_add_disc(int,struct disc *,struct _ex_intern *, int) ;
void _th_priority_range(struct disc *d, int *min, int *max) ;

/* env.c */
#define SYMBOL_PARAMETER       1
#define EXP_PARAMETER          2
#define INTEGER_LIST_PARAMETER 3
#define SYMBOL_LIST_PARAMETER  4
#define INTEGER_PARAMETER      5
#define WILD                   6
#define FUNCTOR_MATCH          7

struct parameter {
    char type ;
    union {
        unsigned symbol ;
        unsigned functor ;
        struct _ex_intern *exp ;
        int integer ;
        unsigned *integer_list ;
        unsigned *symbol_list ;
    } u ;
} ;

struct prex_param_info {
        int param ;
        int count ;
        struct _ex_intern *exps[1] ;
    } ;

struct prex_info {
        int count ;
        struct prex_param_info *info[1] ;
    } ;

struct env *_th_new_empty_env(int,int) ;
struct env *_th_default_env(int) ;

void _th_env_init () ;

struct directive;

void _th_add_cache_assignment(struct env *env, struct _ex_intern *term, struct _ex_intern *val);
void _th_add_signature(struct env *env, struct _ex_intern *term, struct _ex_intern *val);
void _th_add_find(struct env *env, struct _ex_intern *term, struct _ex_intern *find);
void _th_add_original(struct env *env, struct _ex_intern *term, struct _ex_intern *find);
void _th_mark_inhash(struct env *env, struct _ex_intern *term);
void _th_add_merge_explanation(struct env *env, struct _ex_intern *term, struct _ex_intern *merge, struct add_list *explanation);
void _th_clean_cache(struct env *env);
void _th_remove_cache(struct env *env);
void _th_install_cache(struct env *env);
struct _ex_intern *_th_get_type_definition(struct env *e, unsigned sym);
struct _ex_intern *_th_get_type_functor(struct env *e, unsigned sym);
void _th_add_function(struct env *, struct _ex_intern *, struct _ex_intern *,
                      struct _ex_intern *,int, struct _ex_intern **) ;
void _th_add_property(struct env *,struct _ex_intern *) ;
int _th_add_context_property(struct env *,struct _ex_intern *) ;
void _th_add_type_definition(struct env *,
                             struct _ex_intern *, struct _ex_intern *) ;
void _th_add_attrib(struct env *,unsigned,unsigned,struct parameter *) ;
void _th_add_imported(int,struct env *,char *) ;
int _th_add_precedence(int,struct env *,unsigned,unsigned) ;
int _th_add_max_precedence(int,struct env *,unsigned) ;
int _th_add_equal_precedence(int,struct env *,unsigned,unsigned) ;
void _th_add_group(int,struct env *,unsigned,int,unsigned *) ;
int _th_add_minor_precedence(int,struct env *,unsigned,unsigned) ;
void _th_push_context_rules(struct env *) ;
void _th_pop_context_rules(struct env *) ;
void _th_add_var_type(int,struct env *,unsigned,struct _ex_intern *) ;
void _th_add_prex_info(int,struct env *,unsigned,struct prex_info *) ;
void _th_set_pp_directives(struct env *,struct directive *) ;
void _th_add_lex_info(int,struct env *,unsigned,int,int *) ;

int *_th_get_lex_info(struct env *,unsigned) ;
int _th_smallest_symbol_of_type(struct env *,unsigned) ;
struct disc *_th_get_forward_rules(struct env *) ;
struct disc *_th_get_derive_rules(struct env *) ;
struct disc *_th_get_augment_rules(struct env *) ;
struct disc *_th_get_macro_rules(struct env *) ;
struct disc *_th_get_all_rules(struct env *) ;
struct small_disc *_th_get_context_rules(struct env *) ;
struct small_disc *_th_get_forward_context_rules(struct env *) ;
unsigned *getAllConstructors(struct env *,int *) ;
struct _ex_intern *_th_get_function_type(struct env *,unsigned) ;
int _th_get_arity(struct env *,unsigned) ;
struct _ex_intern *_th_get_function_precondition(struct env *, unsigned) ;
struct _ex_intern *_th_get_function_prototype(struct env *, unsigned) ;
struct _ex_intern **_th_get_function_definition(struct env *,unsigned,int *) ;
int _th_is_finite_type(struct env *,unsigned) ;
struct _ex_intern *_th_get_var_type(struct env *,unsigned) ;
void _th_set_var_type(struct env *, unsigned, struct _ex_intern *) ;
struct _ex_intern *_th_get_exp_type(struct env *env, struct _ex_intern *e);
void _th_copy_var_types(struct env *env, struct env *parent_env) ;
void _th_set_default_var_type(struct env *env, struct _ex_intern *) ;
void _th_get_attrib(struct env *,unsigned,int,struct parameter *) ;
struct parameter *_th_get_next_attrib(int *) ;
struct _ex_intern **_th_select_attrib(struct env *,unsigned,int,int *) ;
struct _ex_intern **_th_all_attrib(struct env *,unsigned,int,int *) ;
int _th_is_finite_constructor(struct env *,unsigned) ;
int _th_is_ac(struct env *,unsigned) ;
int _th_is_comparison(struct env *env, unsigned sym) ;
int _th_used_var(struct env *,unsigned) ;
int _th_ac_arity(struct env *,unsigned) ;
int _th_is_ac_or_c(struct env *,unsigned) ;
int _th_is_a_or_c(struct env *,unsigned) ;
int _th_is_a(struct env *,unsigned) ;
int _th_is_c(struct env *,unsigned) ;
int _th_get_attribute_flags(struct env *,unsigned) ;
int _th_is_eq(struct env *,unsigned) ;
int _th_is_order(struct env *,unsigned) ;
int _th_is_imported(struct env *,char *) ;
int _th_is_constructor(struct env *,unsigned) ;
struct _ex_intern *_th_get_type(struct env *,unsigned) ;
int _th_has_smaller_precedence(struct env *,unsigned,unsigned) ;
int _th_has_smaller_minor_precedence(struct env *,unsigned,unsigned) ;
struct prex_info *_th_get_prex_info(struct env *,unsigned) ;
int _th_has_equal_precedence(struct env *,unsigned,unsigned) ;
unsigned *_th_get_name_aways(struct env *,int *) ;
struct directive *_th_get_pp_directives(struct env *) ;
void _th_set_block_rule(int space, struct env *, struct _ex_intern *rule) ;
struct _ex_intern *_th_get_block_rule(struct env *) ;
int _th_use_only_original(struct env *);

struct _ex_intern **_th_get_all_env_rules(struct env *,int *) ;
unsigned *_th_get_all_symbols(struct env *,int *) ;
unsigned *_th_get_smaller_symbols(struct env *,unsigned,int *) ;
unsigned *_th_get_equal_symbols(struct env *,unsigned,int *) ;
unsigned *_th_get_greater_symbols(struct env *,unsigned,int *) ;
char **_th_get_precedence_info(struct env *,int *) ;
char **_th_get_functions(struct env *,int *) ;
char **_th_get_types(struct env *,int *) ;
char **_th_get_attributes(struct env *,int *) ;
char **_th_get_function_detail(struct env *,unsigned,int *) ;

struct _th_unifier *name_away_bound_vars(struct _ex_intern *,int,unsigned *,struct _ex_intern **) ;
struct _ex_intern *_th_flatten(struct env *,struct _ex_intern *) ;
struct _ex_intern *_th_flatten_level(struct env *,struct _ex_intern *, int) ;
struct _ex_intern *_th_flatten_top(struct env *,struct _ex_intern *) ;
int _th_exp_depth(struct _ex_intern *exp);
struct _ex_intern *_th_filter_list(struct env *,struct _ex_intern *) ;
#ifndef FAST
extern int _th_block_check;
#endif
struct _ex_intern *_ex_intern_appl_env(struct env *,unsigned,int,struct _ex_intern **) ;
struct _ex_intern *_ex_intern_appl1_env(struct env *env, unsigned f,struct _ex_intern *a1) ;
struct _ex_intern *_ex_intern_appl2_env(struct env *env, unsigned f,struct _ex_intern *a1, struct _ex_intern *a2) ;
struct _ex_intern *_ex_intern_appl2_equal_env(struct env *env, unsigned f,struct _ex_intern *a1, struct _ex_intern *a2, struct _ex_intern *type_inst) ;
struct _ex_intern *_ex_intern_appl3_env(struct env *env, unsigned f,struct _ex_intern *a1, struct _ex_intern *a2, struct _ex_intern *a3) ;
struct _ex_intern *_ex_intern_appl4_env(struct env *env, unsigned f,struct _ex_intern *a1, struct _ex_intern *a2, struct _ex_intern *a3, struct _ex_intern *a4) ;
struct _ex_intern *_ex_intern_appl5_env(struct env *env, unsigned f,struct _ex_intern *a1, struct _ex_intern *a2, struct _ex_intern *a3, struct _ex_intern *a4, struct _ex_intern *a5) ;
struct _ex_intern *_ex_intern_appl6_env(struct env *env, unsigned f,struct _ex_intern *a1, struct _ex_intern *a2, struct _ex_intern *a3, struct _ex_intern *a4, struct _ex_intern *a5, struct _ex_intern *a6) ;
struct _ex_intern *_ex_intern_appl_equal_env(struct env *env,unsigned f,int c, struct _ex_intern *args[], struct _ex_intern *type_inst);
struct _ex_intern *_ex_intern_equal(struct env *env, struct _ex_intern *type_inst,
                                    struct _ex_intern *left, struct _ex_intern *right);

struct trie_l *_th_get_trie(struct env *env) ;
char *_th_get_mark() ;
void _th_set_trie_mark(struct env *env, struct trie_l *trie, char *mark) ;
struct _ex_intern *_th_get_context_rule_set(struct env *env) ;
void _th_dump_precedence_info(struct env *env, FILE *f) ;

void _th_mark_tested(struct env *, struct _ex_intern *) ;
void _th_mark_used(struct env *, struct _ex_intern *) ;

struct _ex_intern *_th_get_first_rule(struct env *env, struct rule **cr) ;
struct _ex_intern *_th_get_first_context_rule(struct env *env, struct rule **cr) ;
int _th_rule_in_context(struct env *env, struct _ex_intern *rule) ;
struct _ex_intern *_th_get_next_rule(struct env *env, struct rule **cr) ;
struct state_checks *_th_get_state_checks(struct env *env) ;
void _th_set_state_checks(struct env *env, struct state_checks *state_checks) ;
struct env *_th_copy_env(int space, struct env *env) ;
int _th_get_space(struct env *env);

#define ATTRIBUTE_A   1
#define ATTRIBUTE_C   2
#define ATTRIBUTE_TO  4
#define ATTRIBUTE_PO  8
#define ATTRIBUTE_ETO 16
#define ATTRIBUTE_EPO 32
#define ATTRIBUTE_EQ 64
#define ATTRIBUTE_NE  128

extern int _th_inclusive;
struct _ex_intern *_th_get_upper_bound(struct env *env, struct _ex_intern *var);
struct _ex_intern *_th_get_lower_bound(struct env *env, struct _ex_intern *var);

struct _ex_intern *_th_get_first_rule_by_operands(struct env *env, struct _ex_intern *l, struct _ex_intern *r, struct rule_double_operand_list **iter);
struct _ex_intern *_th_get_next_rule_by_operands(struct _ex_intern *l, struct _ex_intern *r, struct rule_double_operand_list **iter);
struct _ex_intern *_th_get_first_rule_by_operand(struct env *env, struct _ex_intern *oper, struct rule_operand_list **iter);
struct _ex_intern *_th_get_next_rule_by_operand(struct _ex_intern *oper, struct rule_operand_list **iter);
struct _ex_intern *_th_get_first_rule_by_var_solve(struct env *env, unsigned var, struct var_solve_list **iter);
struct _ex_intern *_th_get_next_rule_by_var_solve(unsigned var, struct var_solve_list **iter);

struct _ex_intern *_th_add_contexts_to_cache(struct env *env, struct _ex_intern *tail);

void _th_add_simplified_rule(struct env *env, struct _ex_intern *rule);
void _th_mark_simplified(struct env *env);
void _th_clear_simplified(struct env *env);

void _th_add_original_rule(struct env *env, struct _ex_intern *rule);
void _th_mark_blocked(struct env *env);
void _th_clear_blocked(struct env *env);

struct add_list *_th_rollback(struct env *env, struct _ex_intern *rule);

unsigned _th_new_slack(struct env *env);
int _th_term_cmp(struct _ex_intern **t1, struct _ex_intern **t2);
int _th_is_slack(struct _ex_intern *term);
unsigned _th_new_term_var(struct env *env);
int _th_is_term(struct _ex_intern *term);

void _th_print_equality_info(struct env *env);
int _th_add_equality(int s, struct env *env, struct _ex_intern *term1, struct _ex_intern *term2);
int _th_add_inequality(int s, struct env *env, struct _ex_intern *term1, struct _ex_intern *term2);
int _th_equality_status(int s,struct env *env, struct _ex_intern *term1, struct _ex_intern *term2);
struct _ex_intern *_th_get_root(int s, struct env *env, struct _ex_intern *term);
struct parent_list *_th_add_equalities(struct parent_list *l, struct env *env);
int _th_legal_split(struct env *env, struct _ex_intern *term);

int _th_score_equality(struct env *env, struct _ex_intern *term);
struct add_list *_th_collect_restricted_equalities(struct env *env);
struct add_list *_th_collect_equalities(struct env *env);

int _th_term_compare(struct env *env, struct _ex_intern *term1, struct _ex_intern *t2);
void _th_mark_bad(struct env *env, struct _ex_intern *term);

struct add_list *_th_get_binary_terms();

int _th_push_count(struct env *env);

void _th_initialize_difference_table(struct env *env);
void _th_initialize_simplex(struct env *env);
struct _ex_intern *_th_check_cycle_rless(struct env *env, struct _ex_intern *e, struct add_list **expl);
struct add_list *_th_collect_impacted_terms(struct env *env, struct _ex_intern *e);

struct cycle_list {
    struct cycle_list *next;
    struct _ex_intern *e;
    struct add_list *explanation;
};
struct cycle_list *_th_get_equal_cycle_info(struct env *env, struct _ex_intern *e);
struct add_list *_th_prepare_quick_implications(struct env *env, struct _ex_intern *e);
void _th_prepare_node_implications(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_get_quick_implication(struct env *env, struct _ex_intern *e, struct add_list **expl);
int _th_add_reduction(struct env *env, struct _ex_intern *ex, struct _ex_intern *e, struct _ex_intern *reduce, struct _ex_intern *offset, struct add_list **expl);
int _th_do_implications;

void _th_print_difference_table(struct env *env);
void _th_display_difference_table(struct env *env);
int _th_add_predicate(struct env *env, struct _ex_intern *e, struct add_list **explanation);

int _th_incomplete_decision_procedure(struct env *env, struct _ex_intern *e);
int _th_is_difference_term(struct env *env, struct _ex_intern *e);

extern int _th_delta;
extern int _th_is_equal_term;
extern struct _ex_intern *_th_left;
extern struct _ex_intern *_th_right;
extern struct _ex_intern *_th_diff;

int _th_extract_relationship(struct env *env, struct _ex_intern *e);

void *_th_quick_mark(struct env *env);
void _th_quick_pop(struct env *env, void *m);

/* match.c */

struct match_return {
    struct match_return *next ;
    struct _ex_unifier *theta ;
} ;

struct unify_return {
    struct unify_return *next ;
    struct _ex_unifier *theta1 ;
    struct _ex_unifier *theta2 ;
} ;

int _th_equal(struct env *,struct _ex_intern *,struct _ex_intern *) ;
struct match_return *_th_match(struct env *, struct _ex_intern *, struct _ex_intern *) ;
int _th_much_smaller(struct env *,struct _ex_intern *,struct _ex_intern *) ;
int _th_equal_smaller(struct env *,struct _ex_intern *,struct _ex_intern *) ;
int _th_smaller(struct env *,struct _ex_intern *,struct _ex_intern *) ;
int _th_smaller2(struct env *,struct _ex_intern *,struct _ex_intern *) ;
int _th_smaller3(struct env *,struct _ex_intern *,struct _ex_intern *) ;
int _th_all_symbols_smaller(struct env *env,struct _ex_intern *e,unsigned s) ;

int _th_more_general(struct _ex_intern *,struct _ex_intern *) ;
int _th_has_unifier(struct _ex_intern *,struct _ex_intern *) ;

struct match_return *_th_unify(struct env *env, struct _ex_intern *p, struct _ex_intern *e);

/* rule_app.c */
struct add_list {
    struct add_list *next ;
    struct _ex_intern *e ;
} ;

struct change_list {
    struct change_list *next ;
    struct _ex_intern *rule ;
    struct _ex_intern *terms ;
    int execute ;
} ;

extern struct change_list *_th_change_list ;

extern struct _ex_intern *_th_limit_term ;
struct _ex_intern *_th_gen_context(struct env *) ;
struct _ex_intern *_th_rewrite_rule(struct env *,struct _ex_intern *, int) ;
struct _ex_intern *_th_fast_rewrite_rule(struct env *,struct _ex_intern *, int) ;
int _th_possibility_count ;
extern struct _ex_intern **_th_possible_rewrites ;
extern struct _ex_intern **_th_possible_conditions ;
extern int _th_keep_inductive ;
void _th_special_rewrite_rule(int, struct env *, struct _ex_intern *,unsigned,unsigned *) ;
void _th_special_rewrite_rule_no_var(int, struct env *, struct _ex_intern *,unsigned,unsigned *) ;
void _th_derive_rewrite_rule(int, struct env *, struct _ex_intern *) ;
struct add_list *_th_apply_inference_rule(struct env *env, struct _ex_intern *e, int count, struct _ex_intern **args, struct add_list *al, struct change_list *changes, struct add_list *tail, int min, int max, int n, struct _ex_intern **derives) ;
void _th_cond_special_rewrite_rule(int, struct env *, struct _ex_intern *,unsigned,unsigned *) ;
struct _ex_intern *_th_augment_expression(struct env *, struct _ex_intern *, struct _ex_intern *) ;
struct _ex_intern *_th_macro_expand(struct env *env, struct _ex_intern *macro, struct _ex_intern *tail) ;
extern struct _ex_intern *_th_gargs ;
extern struct _ex_intern *_th_current_exp ;
int _th_on_add_list(struct env *env, struct add_list *add, struct _ex_intern *e) ;
int _th_cond_level() ;
void _th_increment_cond_level();
void _th_decrement_cond_level();
int _th_in_context(unsigned);
void _th_check_possible_rewrites(int count);

/* equality.c */
extern int _th_use_transitive;
struct _ex_intern *_th_simplify_equality(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_fast_simplify_equality(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_normalize_equality(struct env *env,struct _ex_intern *e);
void _th_add_equality_rules(int s, struct env *env);

/* boolean.c */
extern int _th_ite_simplification_level;
extern int _th_do_and_context, _th_do_or_context;

struct _ex_intern *_th_simplify_ite(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_xor(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_and(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_or(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_not(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_equal_ite(struct env *env, struct _ex_intern *e);
void _th_add_boolean_rules(int s, struct env *env);

/* case.c */
void _th_add_boolean_rules(int s, struct env *env);
struct _ex_intern *_th_simplify_case(struct env *env, struct _ex_intern *e);

/* calculus.c */
struct _ex_intern *_th_simplify_nat_integrate(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_nat_solve_integrate(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_nat_integrate_set(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_remove_free_terms(struct env *env, struct _ex_intern *quant);
struct _ex_intern *_th_range_set_size(struct env *env, struct _ex_intern *set);
void _th_add_calculus_rules(int s, struct env *env);

/* finite.c */
struct _ex_intern *_th_invert_or_equations(struct env *env, struct _ex_intern *exp);
struct _ex_intern *_th_trans_constant(struct _ex_intern *cond, int dir, struct _ex_intern *term, int count, unsigned *fv);
struct _ex_intern *_th_augment_finite_rule(struct env *env, struct _ex_intern *rule);

/* lambda.c */
struct _ex_intern *_th_simplify_apply(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_lambda(struct env *env, struct _ex_intern *e);

/* quant.c */
struct _ex_intern *_th_simplify_exists(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_all(struct env *env, struct _ex_intern *e);

/* set.c */
struct _ex_intern *_th_simplify_difference(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_union(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_subset(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_separate(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_member(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_intersect(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_setq(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_remove_equal_bound(struct env *env, struct _ex_intern *quant);
void _th_add_set_rules(int s, struct env *env);

/* setsize.c */
struct _ex_intern *_th_simplify_setsize(struct env *env, struct _ex_intern *e);
void _th_add_setsize_rules(int s, struct env *env);

/* builtin.c */
struct _ex_intern *_th_builtin(struct env *, struct _ex_intern *);
int _th_is_constant(struct env *env, struct _ex_intern *e);

extern int _th_integrate_split_limit;
extern int _th_not_limit;

/* transitive.c */
struct _ex_intern *_th_get_right_operand(struct env *env,struct _ex_intern *e);
struct _ex_intern *_th_get_left_operand(struct env *env,struct _ex_intern *e);
int _th_is_an_eq(struct env *, struct _ex_intern *);
int _th_is_ne(struct env *, struct _ex_intern *);
int _th_is_le(struct env *, struct _ex_intern *);
int _th_is_lt(struct env *, struct _ex_intern *);
int _th_compatible_terms(struct env *env, struct _ex_intern *e, struct _ex_intern *f);
struct _ex_intern *_th_combine_operands(struct env *,
                                           struct _ex_intern *,
                                           struct _ex_intern *,
                                           int *);
struct _ex_intern *_th_strengthen(struct env *env, struct _ex_intern *base, struct _ex_intern *e);
struct _ex_intern *_th_reverse_strengthen(struct env *env, struct _ex_intern *base, struct _ex_intern *e);
struct _ex_intern *_th_strengthen_term(struct env *env, struct _ex_intern *base, struct _ex_intern *e);
struct add_list *_th_unary_descendents(struct env *env, struct _ex_intern *e);
struct add_list *_th_binary_descendents(struct env *, struct _ex_intern *, struct _ex_intern *, struct _ex_intern **);
struct add_list *_th_implied_descendents(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_extract_relation(struct env *env, struct _ex_intern *e);

void _th_trans_push(struct env *env) ;
void _th_trans_pop() ;
int _th_add_rule(struct env *, struct _ex_intern *) ;
void _th_transitive_init() ;
void _th_transitive_reset() ;
struct _ex_intern *_th_transitive(struct env *,struct _ex_intern *) ;
int _th_is_binary_term(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_search_equality(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_search_less(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_r_search_equality(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_r_search_less(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_or_terms(struct env *env, struct _ex_intern *base, struct _ex_intern *e);
struct _ex_intern *_th_and_terms(struct env *env, struct _ex_intern *base, struct _ex_intern *e);

/* solve.c */
int _th_has_non_unity(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_linear_solve(struct env *env, unsigned var, struct _ex_intern *e);
struct _ex_intern *_th_nat_equal_linear_solve(struct env *env, unsigned var, struct _ex_intern *e);
struct _ex_intern *_th_nat_less_linear_solve(struct env *env, unsigned var, struct _ex_intern *e);
struct _ex_intern *_th_solve_term(struct env *env, int var_count, unsigned *vars, struct _ex_intern *term);
struct _ex_intern *_th_solve_for_a_var(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_r_solve_for_a_var(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_equation(struct env *env, struct _ex_intern *exp);
struct _ex_intern *_th_r_simplify_equation(struct env *env, struct _ex_intern *exp);
struct _ex_intern *_th_simplify_nat_plus(struct env *env, struct _ex_intern *exp);
struct _ex_intern *_th_simplify_nat_minus(struct env *env, struct _ex_intern *exp);
struct _ex_intern *_th_simplify_nat_less(struct env *env, struct _ex_intern *exp);
struct _ex_intern *_th_simplify_nat_rat(struct env *env, struct _ex_intern *exp);
struct _ex_intern *_th_simplify_nat_times(struct env *env, struct _ex_intern *exp);
struct _ex_intern *_th_simplify_nat_divide(struct env *env, struct _ex_intern *exp);
struct _ex_intern *_th_simplify_nat_min(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_nat_max(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_rat_plus(struct env *env, struct _ex_intern *exp);
struct _ex_intern *_th_simplify_rat_less(struct env *env, struct _ex_intern *exp);
struct _ex_intern *_th_simplify_rat_times(struct env *env, struct _ex_intern *exp);
struct _ex_intern *_th_simplify_rat_divide(struct env *env, struct _ex_intern *exp);
struct _ex_intern *_th_simplify_rat_minus(struct env *env, struct _ex_intern *exp);
struct _ex_intern *_th_add_term(struct env *env, struct _ex_intern *sum, struct _ex_intern *t);
struct _ex_intern *_th_r_add_term(struct env *env, struct _ex_intern *sum, struct _ex_intern *t);
struct _ex_intern *_th_get_coef(struct env *, struct _ex_intern *e);
struct _ex_intern *_th_get_core(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_r_get_coef(struct env *, struct _ex_intern *e);
struct _ex_intern *_th_r_get_core(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_build_term(struct env *env, struct _ex_intern *coef, struct _ex_intern *core);
struct _ex_intern *_th_r_build_term(struct env *env, struct _ex_intern *coef, struct _ex_intern *core);
struct _ex_intern *_th_collect_like_terms(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_r_collect_like_terms(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_remove_times_neg_one(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_r_remove_times_neg_one(struct env *env, struct _ex_intern *e);
void _th_add_solve_rules(int s, struct env *env);
struct _ex_intern *_th_reverse_terms(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_r_reverse_terms(struct env *env, struct _ex_intern *e);
struct add_list *_th_get_transpositions(struct env *env, struct _ex_intern *e, struct add_list *al);
struct _ex_intern *_th_add_rationals(struct _ex_intern *r1, struct _ex_intern *r2);
struct _ex_intern *_th_subtract_rationals(struct _ex_intern *r1, struct _ex_intern *r2);
struct add_list *_th_basic_terms(struct _ex_intern *e, struct add_list *list);
int _th_is_variable_term(struct _ex_intern *e);
int _th_can_solve_for(struct env *env, struct _ex_intern *var, struct _ex_intern *rhs);

/* derive.c */
char *_th_derive_push(struct env *env) ;
void _th_derive_pop(struct env *env) ;
void _th_derive_pop_release(struct env *env, char *rel) ;
int _th_derive_and_add(struct env *env, struct _ex_intern *rule) ;
void _th_derive_and_add_property(int space, struct env *env, struct _ex_intern *rule) ;
struct _ex_intern *_th_derive_simplify(struct env *env, struct _ex_intern *e) ;
struct _ex_intern *_th_derive_prepare(struct env *env, struct _ex_intern *e) ;
void _th_derive_add_prepared(struct env *env, struct _ex_intern *e) ;
int _th_applicable_rule(struct env *env, struct _ex_intern *rule, struct _ex_intern *e) ;
struct _ex_intern *_th_derive_prepare_detailed(struct env *env, struct _ex_intern *e) ;
struct _ex_intern *_th_negate_term(struct env *env, struct _ex_intern *term);

/* cache.c */
void _th_cache_init();
void _th_cache_shutdown();
void _th_flush_context();
void _th_push_context() ;
void _th_pop_context() ;
void _th_reset_context() ;
void _th_add_context_rule(struct _ex_intern *) ;
void _th_quant_add_context_rule(unsigned, int) ;
struct _ex_intern *_th_get_cache_rewrite(struct env *,struct _ex_intern *, int do_transitive) ;
void _th_set_cache_rewrite(struct env *env, struct _ex_intern *, struct _ex_intern *, int do_transitive, unsigned start_cycle) ;
void _th_clear_cache() ;
int _th_check_block(int cycle) ;
struct _ex_intern *_th_get_context() ;
extern struct _ex_intern *_th_context ;
extern struct _ex_intern *_th_full_context ;
extern unsigned _th_cycle ;
#define MAX_LEVELS 30
extern unsigned _th_context_level ;
extern unsigned _th_context_used[MAX_LEVELS] ;
extern unsigned _th_context_tested[MAX_LEVELS] ;
extern unsigned _th_context_any_tested ;
extern unsigned _th_context_any_used ;
extern unsigned _th_violation_tested ;
extern unsigned _th_violation_used ;
void _th_add_cache(struct _ex_intern *, struct _ex_intern *) ;
extern void _th_reintern_cache(struct env *);
struct _ex_intern *_th_rewrite_next;

/* rewrite.c */
struct _ex_intern *_th_augment(struct env *env, struct _ex_intern *e) ;
void _th_init_rewrite(char *log);
void _th_shutdown_rewrite();
struct _ex_intern *_th_rewrite(struct env *, struct _ex_intern *) ;
struct _ex_intern *_th_nc_rewrite(struct env *, struct _ex_intern *) ;
struct _ex_intern *_th_int_rewrite(struct env *, struct _ex_intern *, int) ;
struct _ex_intern *_th_and_elaborate(struct env *, struct _ex_intern *) ;
int _th_quant_level ;
void _th_or_push(struct env *env, struct _ex_intern **,int,int) ;
void _th_and_push(struct env *env, struct _ex_intern **,int,int) ;
void _th_and_push1(struct env *env, struct _ex_intern **,int,int) ;
char *_th_start_rewrite() ;
struct _ex_intern *_th_finish_rewrite(char *mark, struct env *env, struct _ex_intern *res) ;

void _th_check_result(struct env *env, struct _ex_intern *result, int check_mode) ;
extern int _th_check_state ;
extern int _th_do_context_rewrites ;
extern int _th_do_and_or_context_rewrites ;
extern int _th_test_mode ;

/* type.c */
void _th_type_init() ;
struct _ex_unifier *_th_checkTyping(struct env *, struct _ex_intern *, struct _ex_intern *) ;
struct _ex_intern *_th_exp_var_type(struct _ex_unifier *u, unsigned v, int count, int *index);
void _th_clearTypeInfo() ;
void _th_check() ;
struct _ex_intern *_th_return_type(struct env *env, struct _ex_intern *e);

/* pp.c */

#define FORBID_BREAK   1
#define OPTIONAL_BREAK 2
#define REQUIRED_BREAK 3

#define PARSE_PATTERN    1
#define PRINT_PATTERN    2
#define INPUT_PATTERN    3
#define PARSE_PERMIT     4
#define PARSE_BREAK      5
#define PARSE_PRECEDENCE 6
#define PARSE_MARK       7
#define PARSE_USE_RULE   8

struct element {
	int is_var ;
	union {
		unsigned token ;
		struct {
			unsigned variable ;
			unsigned mode ;
			int precedence ;
		} var ;
	} u ;
} ;

struct directive {
        struct directive *next ;
        int type ;
        union {
            struct pattern {
                unsigned rule ;
                int precedence ;
                struct directive *permits ;
                struct _ex_intern *condition ;
                struct _ex_intern *exp ;
                struct _ex_intern *print_condition ;
                struct _ex_intern *print_exp ;
                int token_count ;
                struct element token_list[1] ;
            } pattern ;
            struct permit {
                unsigned rule ;
                unsigned mode ;
                struct directive *next ;
            } permit ;
            struct use_rule {
                unsigned rule ;
                unsigned mode ;
                struct _ex_intern *condition ;
                struct directive *next ;
            } use_rule ;
            struct parse_break {
                unsigned rule ;
                int count ;
                struct br {
                    int break_mode ;
                    int indent ;
                    int child_breaks_allowed ;
                } list[1] ;
            } parse_break ;
            struct parse_mark {
                int rule ;
                int start ;
                int end ;
                int count ;
                int index[1] ;
            } parse_mark ;
        } u ;
    } ;

/* pplex.c */
extern int *_th_row ;
extern int *_th_column ;
extern unsigned *_th_file ;
extern int *_th_end_row ;
extern int *_th_end_column ;
extern unsigned *_th_tokens ;

int _th_tokenize_string(char *s, char *file) ;
int _th_is_number(unsigned) ;
int _th_is_identifier(unsigned) ;
int _th_is_string(unsigned) ;

/* ppdir.c */
struct directive *_th_tokenize_line(int, char *, struct directive *) ;
void _th_print_directives(struct directive *) ;
/* ppparse.c */
void _th_push_current(unsigned) ;
void _th_pop_current() ;
unsigned _th_find_position(unsigned *, unsigned *) ;
struct _ex_intern *_th_pp_parse(char *file, struct env *, char *) ;
struct _ex_intern *_th_pp_parse_mode(char *file, struct env *, unsigned, char *) ;
extern int **_th_index ;
extern int _th_index_count ;
char *_th_pp_print(struct env *env, unsigned mode, int width, struct _ex_intern *) ;
#ifdef FAST
#define _th_pp_tree_print(env,mode,width,e)
#define _th_pp_file_print(f,h,env,mode,width,e)
#else
void _th_pp_tree_print(struct env *env, unsigned mode, int width, struct _ex_intern *e) ;
void _th_pp_file_print(FILE *f,char *h,struct env *env, unsigned mode, int width, struct _ex_intern *e) ;
#endif
#define _th_pp_zone_print(env,mode,width,e) if (_zone_active()) _th_pp_tree_print(env,mode,width,e)

/* Load.c */
struct env *_th_process_file(struct env *env, char *file_name, FILE *f);
void _th_read_file(FILE *f);
extern char _th_source_buffer[];
int _th_svcs(struct env *env, char *file);
int _th_smt(struct env *env, char *name, int print_failures);
int _th_preprocess_smt(struct env *env, char *name);
int _th_smt_autorun(struct env *env, char *name);
int _th_print_smt(struct env *env, char *name);

/* memory.c */
struct _ex_intern *_th_check_rewrite(struct _ex_intern *e) ;
void _th_set_rewrite(struct _ex_intern *e) ;
void _th_write_memory() ;
void _th_init_memory(struct env *env) ;

/* heuristic.c */
struct heuristic_node {
    struct heuristic_node *next;
    struct heuristic_node *first_child;
    struct heuristic_node *parent;
    struct _ex_intern *assumption;
    struct _ex_intern *before_property;
    struct _ex_intern *property;
    char *heuristic;
    int time_step;
    int condition_count;
    int *conditions;
} ;

void setApplicationHook(int (*f)(struct env *env, struct heuristic_node *, char *), char **);
struct heuristic_node *heuristic_solve(struct env *env, struct _ex_intern *exp);
struct heuristic_node *apply_heuristic(struct env *env, struct _ex_intern *exp, char *heuristic);
int is_finished(struct heuristic_node *node);
struct _ex_intern *_th_generate_universal(struct env *env, struct _ex_intern *exp,
                                          int (*qualify)(struct env *env, struct _ex_intern *),
                                          int (*weight)(struct env *, struct _ex_intern *));
void _th_build_context(struct env *, struct _ex_intern *);
int _th_global_heuristics(int do_universal, struct env *env, struct heuristic_node *node, char *heuristic);
struct heuristic_node *_th_new_node(struct heuristic_node *parent);

extern int _th_break_pressed;

#endif

/* mymalloc.c */

void _th_print_results();

/*#define MALLOC_DEBUG*/
#ifdef MALLOC_DEBUG

#include <malloc.h>

void *_th_malloc(char *,int,int);
void _th_free(char *,int,void *);
void *_th_realloc(char *, int, void *, int);

#define MALLOC(x) _th_malloc(__FILE__,__LINE__,x)
#define FREE(x) _th_free(__FILE__,__LINE__,x)
#define REALLOC(x,y) _th_realloc(__FILE__,__LINE__,x,y)

#else

#define MALLOC(x) malloc(x)
#define FREE(x) free(x)
#define REALLOC(x,y) realloc(x,y)

#endif

/* case_split.c */
struct fail_list {
    struct fail_list *next;
    struct parent_list *conditions;
    struct parent_list *reduced_form;
    struct _ex_intern *e;
};

struct parent_list {
    struct parent_list *next;
    struct _ex_intern *exp;
    struct _ex_intern *split;
    int rhs;
    int unate;
    int used_in_learn;
};

extern double _th_initial_conflict_limit;
extern double _th_bump_decay;
extern double _th_random_probability;
extern double _th_conflict_factor;

struct _ex_intern *_th_case_split(struct env *env, struct _ex_intern *exp);
struct fail_list *_th_prove(struct env *env, struct _ex_intern *e);
#define PREPROCESS_DEFAULT 0
#define PREPROCESS_CNF     1
#define PREPROCESS_SAT     2
#define PREPROCESS_UNSAT   3
#define PREPROCESS_NORUN   4

int _th_preprocess(struct env *env, struct _ex_intern *e, char *write_file, char *write_d_file);

extern int _th_do_symmetry;
extern int _th_do_grouping;
extern int _th_do_break_flower;
extern int _th_do_learn;
extern int _th_do_unate;
extern int _th_score_mode;
extern int _th_use_composite_conds;
extern int _th_equality_only;

/* fd.c */
struct fd_handle;
extern int _fd_combination_limit;

struct fd_handle *_fd_solve(struct env *env, struct _ex_intern *exp);
struct _ex_intern *_fd_get_value_n(struct env *env, struct fd_handle *fd, unsigned var, int n);
struct _ex_intern *_fd_get_value_count(struct env *env, struct fd_handle *fd, unsigned var);
void _fd_push(struct fd_handle *);
void _fd_pop(struct fd_handle *);
void _fd_revert(struct fd_handle *);
int _fd_instantiate(struct env *env, struct fd_handle *, unsigned var, struct _ex_intern *value);
struct _ex_intern *_th_get_max(struct env *env, struct _ex_intern *context_rules, struct _ex_intern *exp, unsigned var);
struct _ex_intern *_th_get_min(struct env *env, struct _ex_intern *context_rules, struct _ex_intern *exp, unsigned var);
struct _ex_intern *_fd_get_min_value(struct env *env, struct fd_handle *fd, unsigned var);
struct _ex_intern *_fd_get_max_value(struct env *env, struct fd_handle *fd, unsigned var);
struct _ex_intern *_fd_get_min_open(struct env *env, struct fd_handle *fd, unsigned var);
struct _ex_intern *_fd_get_max_open(struct env *env, struct fd_handle *fd, unsigned var);
extern int _th_do_domain_score;

/* crewrite.c */
extern int _th_rewriting_context;
struct _ex_intern *_th_context_rewrite(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_strengthen_in_context(struct env *env, struct _ex_intern *exp);
struct _ex_intern *_th_eliminate_var(struct env *env, struct _ex_intern *exp);
extern int _th_add_rule_and_implications(struct env *env, struct _ex_intern *e);
extern int _th_has_complex_term(struct _ex_intern *exp, int level);
struct _ex_intern *_th_can_impact(struct env *env, struct _ex_intern *e1, struct _ex_intern *e2);
void _th_crewrite_init();
int _th_uninterpreted_functor(int functor);
int _th_assert_predicate(struct env *env, struct _ex_intern *pred);
int _th_deny_predicate(struct env *env, struct _ex_intern *pred);
int _th_reassert_unblocked_rules(struct env *env);
void _th_block_predicate(struct env *env, struct _ex_intern *assertion);
struct _ex_intern *_th_simp(struct env *env, struct _ex_intern *e);
struct add_list *_th_retrieve_explanation(struct env *env, struct _ex_intern *pred);

/* abstraction.c */
struct _ex_intern *_th_abstract_condition(struct env *env, struct _ex_intern *e);

/* bitblast.c */
struct _ex_intern *_th_bit_blast(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_process_mod(struct env *env, struct _ex_intern *e);
struct add_list *_th_get_not_equals(struct env *env, struct _ex_intern *var);
struct _ex_intern *_th_bit_blast_comparison(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_equality_false_by_range(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_r_equality_false_by_range(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_nless_by_range(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_rless_by_range(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_pos_test_rless_by_range(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_multiply_rationals(struct _ex_intern *a, struct _ex_intern *b);
struct _ex_intern *_th_divide_rationals(struct _ex_intern *a, struct _ex_intern *b);
int _th_rational_less(struct _ex_intern *a, struct _ex_intern *b);

/* unate.c */
struct dependencies {
    struct dependencies *next;
    int push_level;
    struct term_list *term;
    struct _ex_intern *reduction;
};

struct term_list {
	struct term_list *next;
	struct _ex_intern *e;
    struct dependencies *dependencies;
    struct dependencies *neg_dependencies;
    int processed;
	int count;
    int total_count;
};

struct _ex_intern *_th_find_unate(struct env *env, struct _ex_intern *e);
struct term_list *_th_get_terms(struct env *env, struct _ex_intern *e, struct term_list *list);
int _th_term_count(struct env *env, struct _ex_intern *e, struct _ex_intern *term);
int _th_has_term(struct env *env, struct _ex_intern *e, struct _ex_intern *term);
int _th_another_cond_as_subterm(struct env *env, struct _ex_intern *e, struct term_list *list);
void _th_clear_dependency_cache();
void _th_fill_dependencies(struct env *env, struct term_list *list);
struct term_list *_th_eliminate_composite_conds(struct env *env, struct term_list *list);

extern struct _ex_intern *_th_reduced_exp;
struct add_list *_th_eliminate_unates(struct env *env, struct _ex_intern *e, struct term_list *terms);
struct _ex_intern *_th_reduction_score(struct env *env, struct term_list *all, struct term_list *tl, struct _ex_intern *e);
int _th_my_contains_ite(struct _ex_intern *e);
int _th_is_boolean_term(struct env *env, struct _ex_intern *e);

/* learn.c */
void _th_print_trail(char *heading, struct parent_list *l);
int _th_learn_has_non_unity(struct env *env, struct learn_info *info);
void _th_abstract_tuples(struct env *env, struct learn_info *info);
void _th_elim_simp_var(struct env *env, struct learn_info *info);
void _th_elim_var(struct env *env, struct learn_info *info, unsigned var, struct _ex_intern *exp);
int _th_solved_case(struct env *env, struct learn_info *info, struct parent_list *list);
int _th_add_list(struct env *env, struct learn_info *info, struct parent_list *list);
int _th_learn_score(struct env *env, struct learn_info *info, struct _ex_intern *term, struct parent_list *p);
int _th_learn(struct env *env, struct learn_info *info, struct parent_list *list, struct term_list *terms, int from_domain);
struct learn_info *_th_new_learn_info(struct env *env);
int _th_get_learns(struct learn_info *info);
int _th_get_generalizations(struct learn_info *info);
void _th_dump_learn(struct learn_info *info);
extern int _th_learned_domain_case;
struct _ex_intern *_th_learned_unate_case(struct env *env, struct learn_info *info, struct parent_list *list);
struct _ex_intern *_th_learned_non_domain_unate_case(struct env *env, struct learn_info *info, struct parent_list *list);
int _th_get_reject_count(struct env *env, struct learn_info *learn, struct _ex_intern *term);
struct _ex_intern *_th_add_learn_terms(struct learn_info *info, struct _ex_intern *e);
struct _ex_intern *_th_transfer_to_learn(struct env *env, struct learn_info *info,struct parent_list *list, struct _ex_intern *e);
int _th_add_tuple_from_list(struct env *env, struct learn_info *info, struct add_list *list);
extern int _th_cycle_limit;
int _th_add_assignment(struct env *env, struct learn_info *info, struct _ex_intern *e, int d);
int _th_create_add_assignment(struct env *env, struct learn_info *info, struct _ex_intern *e, int d);
void _th_delete_assignment(struct env *env, struct learn_info *info, struct _ex_intern *e);
struct _ex_intern *_th_get_assignment(struct env *env, struct learn_info *info, struct _ex_intern *e);
void _th_print_assignments(struct learn_info *info);
int _th_learn_term_count(struct learn_info *info);
void _th_learn_print_assignments(struct learn_info *info);
void _th_learn_add_score_dependencies(struct env *env, struct learn_info *info);
struct env *_th_learn_get_env(struct learn_info *info);
struct _ex_intern *_th_learn_choose(struct env *env, struct learn_info *info, struct parent_list *parents);
struct _ex_intern *_th_learn_choose_signed(struct env *env, struct learn_info *info, struct parent_list *parents, double random_probability);
extern int _th_quit_on_no_antecedant;
void _th_add_unate_tail(struct env *env, struct learn_info *info, struct parent_list *list);

struct _ex_intern *_th_get_first_neg_tuple(struct learn_info *info);
struct _ex_intern *_th_get_next_neg_tuple(struct learn_info *info);

double _th_learn_pos_score(struct env *env, struct learn_info *info, struct _ex_intern *term);
double _th_learn_neg_score(struct env *env, struct learn_info *info, struct _ex_intern *term);
void _th_learn_increase_bump(struct learn_info *info, double factor);

/* term_cache.c */
struct term_data {
    int pos_score;
    struct _ex_intern *pos_term;
    int neg_score;
    struct _ex_intern *neg_term;
    //int term_count;
};

int _th_get_table_size();
void _th_lock_table();
int _th_get_term_position(struct _ex_intern *e);
struct _ex_intern *_th_lookup_term(int index);
void _th_fill_dependencies(struct env *env, struct term_list *list);
void _th_new_term(struct _ex_intern *e);
void _th_update_dependency_table(struct env *env, int do_augment);
int _th_check_term(struct _ex_intern *e, int index);
int _th_get_active_terms_word_count(struct _ex_intern *term);
int _th_get_elimination_score(struct _ex_intern *term);
void _th_set_elimination_score(struct _ex_intern *term, int score);
struct term_data *_th_get_term_data_holder(struct _ex_intern *e, struct _ex_intern *term);
struct _ex_intern *_th_term_rewrite(struct env *env, struct _ex_intern *e, struct _ex_intern *term);
struct _ex_intern *_th_terms_rewrite(struct env *env, struct _ex_intern *e, struct add_list *terms);
void _th_init_term_cache();
struct dependencies *_th_get_dependencies(struct _ex_intern *t);
struct dependencies *_th_get_neg_dependencies(struct _ex_intern *t);
int _th_has_a_term(struct _ex_intern *e);
struct _ex_intern *_th_get_score(struct env *env, struct _ex_intern *e, struct _ex_intern *term);
struct term_list *_th_get_dependency_cache();

struct mark_info *_th_term_cache_push();
void _th_term_cache_pop(struct mark_info *);

/* smt_parser.y */
struct _ex_intern *_th_parse_smt(struct env *env, char *name);
struct env *_th_get_learn_env();
extern int _th_unknown;
unsigned _th_get_status();
char *_th_get_status_name();
char *_th_get_name();
char *_th_get_logic_name();
int _th_is_difference_logic();
int _th_is_bclt_logic();
int _th_is_integer_logic();
int _th_is_symmetry_logic();

extern int _th_hack_conversion;
extern int _th_pair_limit;
extern int _th_hack_has_real;
extern int _th_hack_has_int;


/* array.c */
struct _ex_intern *_th_simplify_select(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_store(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_array_equality(struct env *env, struct _ex_intern *e);
struct _ex_intern *_th_simplify_ee(struct env *env, struct _ex_intern *e);

/* parse_yices_ce.c */
void _th_parse_yices_ce(struct env *env, FILE *file);
int _th_matches_yices_ce(struct env *env, struct parent_list *p, struct _ex_intern *e);
void _th_build_yices_env();
struct _ex_intern *_th_yices_ce_value(struct env *env, struct _ex_intern *e);

/* print_smt.c */
void _th_print_state(struct env *env, struct parent_list *list, struct learn_info *info, struct _ex_intern *e, FILE *f, char *name, char *status, char *logic);

/* symmetry.c */
struct _ex_intern *_th_augment_with_symmetries(struct env *env, struct _ex_intern *e);

/* grouping.c */
extern int _th_block_bigs;
struct _ex_intern *_th_simplify_groupings(struct env *env, struct _ex_intern *e, struct parent_list *unates, struct learn_info *info);
struct _ex_intern *_th_break_flower(struct env *env, struct _ex_intern *e, struct parent_list *unates, struct learn_info *info);

/* decompose.c */
void _th_add_to_learn(struct env *env, struct learn_info *info, struct _ex_intern *e, struct parent_list *list);
struct _ex_intern *_th_remove_nested_ite(struct env *env, struct learn_info *info, struct _ex_intern *e, struct parent_list *list);
struct _ex_intern *_th_variablize_functions(struct env *env, struct _ex_intern *e);

/* dimacs.c */
int _th_is_sat(struct learn_info *info);
void _th_print_dimacs(struct learn_info *info, FILE *file);

/* simplex.c */
struct simplex;
void _th_print_simplex(struct simplex *simplex);
struct simplex *_th_new_simplex(struct env *env);
void _th_simplex_push(struct simplex *simplex);
void _th_simplex_pop(struct simplex *simplex);
struct add_list *_th_add_equation(struct simplex *simplex, struct _ex_intern *e);


int Minisat_main(int argc, char** argv);
