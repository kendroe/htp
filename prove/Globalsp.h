/*
 * globals.h
 *
 * Global variable and procedure declarations.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdio.h>
#include "../rewlib/Globals.h"
#include "../rewlib/Intern.h"

struct entry;

/* verify.c */
void _th_verify(int space, struct env *env, struct entry *list) ;

/* command.c */
void _th_command_init() ;
void _th_command_shutdown() ;
int _th_process(char *) ;
int _th_find_space();

#define MAX_DERIVATIONS 20

extern struct node *_th_derivation[MAX_DERIVATIONS] ;
extern int _th_derivation_space[MAX_DERIVATIONS] ;
extern char *_th_derivation_name[MAX_DERIVATIONS] ;

extern int _th_derivation_count;

extern struct node *_th_cut_buffer ;
extern int _th_cut_space;

extern int _th_derivation_count;

/* derivation.c */
#define DEFINITION_NODE   1
#define TYPE_NODE         2
#define PROOF_NODE        3
#define ATTRIB_NODE       4
#define PRECEDENCE_NODE   5
#define COMMENT_NODE      6
#define IMPORT_NODE       7
#define PP_DIRECTIVE_NODE 8
#define MODULE_NODE       9

struct node_root {
        struct node *next ;
        char type ;
        int exported : 1 ;
        int valid : 1 ;
    } ;

#define REWRITE              1
#define EXPAND               2
#define UNIVERSAL            3
#define SPECIAL_REWRITE      4
#define COND_SPECIAL_REWRITE 5

struct proof {
        struct _ex_intern *term ;
        int operation ;
        int selection ;
        struct _ex_intern *choice, *condition ;
        struct _ex_unifier *fill_in ;
        struct _ex_intern *ind_exp ;
        int child_count ;
        struct proof *parent;
        struct proof *children[1] ;
    } ;

#define PREC_LESS  1
#define PREC_LEX   2
#define PREC_EQUAL 3
#define PREC_GROUP 4
#define PREC_BLOCK 5
#define PREC_MINOR 6

struct node {
        struct node *next ;
        char type ;
        int exported : 1 ;
        int valid : 1 ;
        union {
            struct module {
                unsigned module;
                struct node *branch_nodes;
            } module ;
            struct definition {
                struct _ex_intern *template ;
                struct _ex_intern *type ;
                struct _ex_intern *precondition ;
                int count ;
                struct _ex_intern *rules[1] ;
            } definition ;
            struct type_definition {
                struct _ex_intern *ttype ;
                struct _ex_intern *ttypedef ;
            } type_definition ;
            struct comment {
                char text[1] ;
            } comment ;
            struct pp_directive {
                char text[1] ;
            } pp_directive ;
            struct import {
                struct node *item_list ;
                char text[1] ;
            } import ;
            struct pr {
                int display_all : 1 ;
                struct _ex_intern *property ;
                struct _ex_intern *order ;
                struct proof *proof ;
            } proof ;
            struct attrib {
                int count ;
                int param ;
                struct parameter parameter[1] ;
            } attrib ;
            struct precedence {
                int type ;
                unsigned left, right ;
            } precedence ;
            struct precedence_block {
                int type ;
                unsigned left ;
                int pos ;
                struct _ex_intern *block ;
            } precedence_block ;
            struct precedence_list {
                int type ;
                unsigned left ;
                int count ;
                unsigned list[1] ;
            } precedence_list ;
        } u ;
    } ;

struct node *_th_load_derivation(unsigned, char *) ;
struct node *_th_find_node(struct node *, int) ;
struct node *_th_h_find_node(struct node *, char *) ;
struct node *_th_insert_comment(int, struct node *, char *, char *,int,int) ;
struct node *_th_insert_proof(int, struct node *, char *, char *,char *,int,int) ;
struct node *_th_insert_proof_env(int, struct env *env, struct node *, char *, char *,char *,int,int) ;
struct node *_th_insert_pp_directive(int, struct node *, char *, char *,int,int) ;
struct node *_th_insert_precedence(int, struct node *, char *, char *,int,int) ;
struct node *_th_insert_attrib(int, struct node *, char *, char *,int,int) ;
struct node *_th_insert_type(int, struct node *, char *, char *,int,int) ;
struct node *_th_insert_type_env(int, struct env *env, struct node *, char *, char *,int,int) ;
struct node *_th_insert_import(int, struct node *, char *, char *,int,int) ;
struct node *_th_insert_definition(int, struct node *, char *, int, int) ;
struct node *_th_insert_theorem(int, struct node *, unsigned, struct _ex_intern *);
struct node *_th_copy_node(int, struct node *node) ;
struct node *_th_copy_derivation(int, struct node *) ;
struct node *_th_copy_derivation_range(int, struct node *, int, int) ;
struct node *_th_copy_derivation_except_range(int, struct node *, char *, int, int) ;
struct node *_th_insert_nodes(struct node *, struct node *, int) ;
void _th_print_attrib(FILE *, struct node *) ;
struct node *_th_get_proof(int, struct node *, char *) ;
struct node *_th_return_proof(struct node *der, struct node *node, char *pos) ;
void _th_save_derivation(struct node *, char *name) ;
void _th_invalidate_derivation(struct node *, char *) ;
struct env *_th_add_to_env(int s, struct env *env, struct node *der) ;
struct env *_th_build_env(int,struct env *,struct node *) ;
struct env *_th_h_build_env(char *,struct env *,struct node *) ;
int _th_total_node_count(struct node *) ;
int _th_unfinished_node_count(struct node *) ;
struct proof *_th_get_node(int, int *,struct node *) ;
struct proof *_th_get_unfinished_node(int, struct node *) ;
int _th_cancel_operation(struct proof *) ;
int _th_rewrite_operation(int, struct env *, struct node *, struct proof *) ;
void _th_incorporate_rewrite(struct env *,int, int, struct _ex_unifier *) ;
void _th_incorporate_expansion(int, struct env *, struct node *, struct proof *, int) ;
void _th_incorporate_universal(int, struct env *, struct node *, struct proof *, struct _ex_intern *, int, unsigned, unsigned *) ;

void _th_start_definition();
int _th_incomplete_definition();
int _th_add_definition_line(struct env *env, char *s);
void _th_special_rewrite_operation(int s, struct env *env, struct node *node, struct proof *proof, unsigned c, unsigned *sub) ;
void _th_condition_special_rewrite_operation(int s, struct env *env, struct node *node, struct proof *proof, unsigned c, unsigned *sub) ;
int _th_get_suffix(char *pos);
void _th_strip_suffix(char *pos);
struct env *_th_build_module_env(struct env *env, unsigned module, struct node *der);

struct env *_th_base_env;

/* expand.c */
unsigned **_th_get_expandable_variables(int, struct _ex_intern *, int *) ;
struct _ex_intern **_th_expand_var(int, struct env *, struct _ex_intern *,unsigned,unsigned,unsigned *) ;
unsigned **_th_get_universal_positions(int, struct _ex_intern *, int *) ;
unsigned **_th_get_all_positions(int, struct _ex_intern *, unsigned *) ;
struct _ex_intern **_th_expand_universal(int, struct env *, struct _ex_intern *,struct _ex_intern *,unsigned,unsigned *) ;

/* search_utils.c */
void _th_best_order(struct env *,int,int,struct _ex_intern **,struct _ex_intern **,int *) ;
int _th_compare_match(struct env *,struct _ex_intern *,struct _ex_intern *,struct _ex_intern *) ;
int _th_distance(struct env *, struct _ex_intern *, struct _ex_intern *) ;
int _th_bad_term_count(struct env *env, struct _ex_intern *, int, struct _ex_intern **) ;
int _th_all_bad_term_count(struct env *env, struct _ex_intern *, struct _ex_intern *) ;

/* search_node.c */
struct search_node {
    struct search_node *next ;
    struct search_node *next_sibling ;
    int goal_count ;
    struct search_node *children ;
    int cost ;
    int state ;
    struct _ex_intern *goals[2] ;
} ;

#define NODE_STATE_CLOSED    0
#define NODE_STATE_NORMALIZE 1
#define NODE_STATE_BRANCH    2

struct search_node *_th_find_search_node(unsigned, struct _ex_intern **) ;
struct search_node *_th_add_successor(struct search_node *, int, struct _ex_intern **) ;
void _th_close_node(struct search_node *) ;
void _th_clear_lists() ;

/* normalize.c */
struct _ex_intern *_th_normalize(struct env *, struct _ex_intern *, struct _ex_intern *) ;
extern int _th_complete_solution ;

/* compile.c */

#define PushConstant 1
		/*Exp*/
#define PushCond     2
		/*Exp*/
#define JumpSub      3
        /*int*/
#define Jump         4
        /*int*/
#define IfZero       5
#define Operation    6
        /*int*/
#define Load         7
        /*Exp*/
#define Store        8
        /*Exp*/
#define StorePop     9
        /*Exp*/
#define Pop          10
        /*int*/
#define Rotate       11
        /*int*/
#define Assert       12
        /*string * Exp*/
#define Block        13
#define ParBlock     14
#define Declare      15
        /*string * Exp*/
#define StaticEnv    16
        /*Exp list*/
#define Noop         17
#define Dup          18
#define Invariant    19
        /*string * Exp*/
#define Label        20
        /*string*/
#define Return       21

struct instruction {
	struct instruction *next ;
	int operation ;
	int file, line ;
        union {
	    struct _ex_intern *exp ;
            struct {
	         unsigned operation ;
                 struct _ex_intern *param ;
            } op ;
	    int arg ;
            unsigned label ;
            struct {
                unsigned function ;
                int count ;
            } jumpsub ;
            struct {
                struct instruction **thread ;
                int count ;
            } block ;
	    struct {
		unsigned var ;
		struct _ex_intern *type ;
            } declare ;
	} u ;
} ;

#define ENTRY_FUNCTION        1
#define ENTRY_GLOBAL_VARIABLE 2
#define ENTRY_TYPEDEF         3
#define ENTRY_INVARIANT       4
#define ENTRY_PRECONDITION    5
#define ENTRY_POSTCONDITION   6
#define ENTRY_MODIFIES        7
#define ENTRY_EXTERN_FUNCTION 8

struct cparameter {
	unsigned name ;
	struct _ex_intern *type ;
} ;

struct local_vars {
    struct local_vars *next ;
    unsigned name ;
    unsigned scope ;
    int disabled ;
    struct _ex_intern *type ;
} ;

struct entry {
	struct entry *next ;
	struct _ex_intern *annotations ;
	int type ;
	union {
        struct function {
			char *name ;
			int count ;
			struct _ex_intern *return_type ;
			struct instruction *code ;
            struct local_vars *local_vars ;
			struct cparameter parameters[1] ;
		} function ;
		struct global_variable {
			unsigned var ;
			struct _ex_intern *type ;
		} global_var ;
		struct typed {
			unsigned name ;
            struct _ex_intern *type ;
		} typedef_def ;
		struct cond {
			unsigned function ;
			struct _ex_intern *condition ;
            struct _ex_intern *variable ;
            struct _ex_intern *type ;
		} cond ;
	} u ;
} ;

struct name_space *_th_name_space ;

struct record_field {
	struct record_field *next ;
	unsigned ref_num ;
	unsigned name ;
	struct _ex_intern *type ;
	struct _ex_intern *initialization ;
} ;

struct member_function {
	struct member_function *next ;
	int is_virtual ;
	unsigned name ;
	struct _ex_intern *return_type ;
	int param_count ;
	struct _ex_intern *param_type[1] ;
} ;

struct record_info {
	struct record_info *next ;
	struct record_list *parents, *children ;
	unsigned name ;
	struct record_field *field ;
	struct member_function *functions ;
} ;

struct record_list {
    int start_point ;
	struct record_list *next ;
	struct record_info *record ;
} ;

struct typedefs {
	struct typedefs *next ;
	unsigned name ;
	struct _ex_intern *type ;
} ;

struct name_space {
	struct name_space *next, *child, *parent ;
	unsigned name ;
	struct record_info *records ;
	struct record_field *variables ;
	struct typedefs *typedefs ;
} ;

struct state_checks {
    struct state_checks *next ;
    char *name ;
    struct _ex_intern *condition ;
} ;

void _th_print_instruction(int pos, struct instruction *instruction) ;
struct entry *_th_compile(int space, struct env *env, struct _ex_intern *program) ;
void _th_print_assembly(struct entry *e) ;

/* verilog.c */
struct assign_group {
    struct assign_group *next;
    unsigned variable;
    unsigned decl;
    unsigned cut_processed;
    int low;
    int high;
    struct add_list *assigns;
};

struct module_pointer_list {
    struct module_pointer_list *next;
    struct module_list *module;
    struct _ex_intern *instance_exp;
    struct add_list *instantiation;
    unsigned instance;
};

struct var_list {
    struct var_list *next;
    unsigned var;
};

struct trigger_order {
    struct trigger_order *next;
    unsigned var;
    struct trigger_order_list *parents;
    struct trigger_order_list *children;
};

struct trigger_order_list {
    struct trigger_order_list *next;
    struct trigger_order *order;
};

struct child_edge_list {
    struct child_edge_list *next;
    int child;
};

struct effects_list {
    struct effects_list *next;
    char *variable;
};

struct variable_list {
    struct variable_list *next;
    char *variable;
    struct effects_list *effects_list;
};

struct condition_node {
    int parent;
    int branch;
    int valid_for_node;
    struct _ex_intern *condition;
    struct child_edge_list *children;
    struct trigger_order_list *parents;
    struct variable_list *variable_list;
};

#ifdef CONDITION_CHECK
struct applicable_conditions {
    struct applicable_conditions *next;
    struct _ex_intern *exp;
    struct add_list *conditions;
};

#define RULE_HASH_SIZE 511
#define CONDITION_HASH_SIZE 2047
#endif

struct module_list {
    struct module_list *next;
    unsigned name;
    struct add_list *declarations;
    struct add_list *assertions;
    struct module_pointer_list *children;
    struct assign_group *groups;
    struct var_list *state_var_list;
    struct var_list *clock_var_list;
    struct trigger_order *trigger_order;
    int is_root_module;
    struct _ex_intern *assign_exp;
    struct variable_list *effects;
    struct variable_list *cycle_effects;
#ifdef CONDITION_CHECK
    struct applicable_conditions *applicable_rules[RULE_HASH_SIZE];
    struct applicable_conditions *applicable_conditions[CONDITION_HASH_SIZE];
#endif
    int condition_node_count;
    struct condition_node *condition_nodes;
};

extern int module_space;
extern char *module_mark;
extern struct module_list *modules;
extern struct env *verilog_env;
extern int verilog_derivation;

struct module_list *find_module(unsigned name);
int load_model(char *project);

struct _ex_intern *_th_verify_assertion(struct module_list *ml, struct _ex_intern *e, char *local);
void _th_add_verilog_assertions(struct env *env, struct module_list *ml);
