/*
 * This program is free software.  See LICENSE for more information
 */

%{

#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"

#define YYMAXDEPTH 5000000

int _th_hack_conversion = 1;

extern char *yytext;

void yyerror(char *error)
{
    fprintf(stderr, "Error: %s\n", error);
    exit(1);
}

struct symtab {
    struct symtab *next;
    int name;
	struct _ex_intern *value;
	struct _ex_intern *type;
};

struct attribute {
    struct attribute *next;
    int name;
	int value;
};

#define HASH_SIZE 97

static struct symtab *table[HASH_SIZE];
static struct symtab *type_table[HASH_SIZE];
static char *mark;
static struct _ex_intern *type_list;
static struct env *env = NULL;
static struct env *lenv = NULL;
static struct _ex_unifier *u;
struct unifier_list {
    struct unifier_list *next;
    struct _ex_unifier *u;
    char *mark;
    int name;
} *ulist;
static int logic_name;
static char *bench_name;
static int status;
static struct _ex_intern *assumption;
static struct _ex_intern *formula;
//extern char yytoken[2000];

static struct name_list {
    struct name_list *next;
    char *mark;
    int name;
} *name_list;


char *_th_get_logic_name()
{
    return _th_intern_decode(logic_name);
}

int _th_is_difference_logic()
{
    return logic_name==INTERN_QF_UFIDL || logic_name==INTERN_QF_IDL || logic_name==INTERN_QF_RDL;
}

int _th_is_bclt_logic()
{
    return logic_name==INTERN_QF_UFIDL || logic_name==INTERN_QF_IDL || logic_name==INTERN_QF_RDL || logic_name==INTERN_QF_UF;
}

int _th_is_symmetry_logic()
{
    return logic_name==INTERN_QF_UF;
}

int _th_is_integer_logic()
{
    return logic_name==INTERN_QF_UFIDL || logic_name==INTERN_QF_IDL || logic_name==INTERN_QF_LIA || logic_name==INTERN_QF_UFLIA ||
           logic_name==INTERN_QF_AUFLIA || logic_name==INTERN_AUFLIA;
}

char *_th_get_name()
{
    return bench_name;
}

static void push_variable(int name)
{
     struct name_list *n;
     char *mark = _th_alloc_mark(PARSE_SPACE);
     n = (struct name_list *)_th_alloc(PARSE_SPACE,sizeof(struct name_list));
     n->next = name_list;
     n->mark = mark;
     name_list = n;
     n->name = name;
     //fprintf(stderr, "Pushing var %s\n", _th_intern_decode(name));
}

static void set_value(struct _ex_intern *value)
{
    struct unifier_list *n;

    //fprintf(stderr, "Pushing %s %s\n", _th_intern_decode(name_list->name), _th_print_exp(value));

    n = (struct unifier_list *)_th_alloc(PARSE_SPACE, sizeof(struct unifier_list));
    n->next = ulist;
    ulist = n;
    ulist->name = name_list->name;
    ulist->mark = name_list->mark;
    n->u = u;
    u = _th_shallow_copy_unifier(PARSE_SPACE,u);
    u = _th_add_pair(PARSE_SPACE,u,name_list->name,value);
    name_list = name_list->next;
}

static void pop_variable()
{
    char *mark = ulist->mark;
    u = ulist->u;
    //printf("Popping %s\n", _th_intern_decode(ulist->name));
    ulist = ulist->next;
    //_th_alloc_release(PARSE_SPACE,mark);
}

static struct _ex_intern *get_type(struct _ex_intern *exp)
{
    struct _ex_intern *t;

    if (exp->user2) return exp->user2;

    if (exp->type==EXP_APPL && exp->u.appl.functor==INTERN_ATTR) {
        exp->next_cache = type_list;
        type_list = exp;
	    return exp->user2 = get_type(exp->u.appl.args[0]);
	}

    /* For now, no polymorphic types--so this will work. */
    exp->next_cache = type_list;
    type_list = exp;
    switch (exp->type) {
        case EXP_INTEGER:
            exp->user2 = _ex_int;
            break;
        case EXP_RATIONAL:
            exp->user2 = _ex_real;
            break;
        case EXP_VAR:
            exp->user2 = _th_get_var_type(env,exp->u.var);
            break;
        case EXP_APPL:
            if (exp->u.appl.functor==INTERN_ITE) {
                t = get_type(exp->u.appl.args[1]);
                exp->user2 = t;
            } else {
                t = _th_get_type(env,exp->u.appl.functor);
                exp->user2 = t->u.appl.args[1];
            }
            break;
        default:
            exp->user2 = NULL;
    }
    return exp->user2;
}

static struct _ex_intern *build_attr_term(struct _ex_intern *exp, struct attribute *attrs)
{
    if (attrs==NULL) return exp;

	return _ex_intern_appl3_env(env, INTERN_ATTR,
	                                 build_attr_term(exp,attrs->next),
	                                 _ex_intern_string(_th_intern_decode(attrs->name)),
									 _ex_intern_string(_th_intern_decode(attrs->value)));
}

static struct boolean_term *build_formula_attr(struct boolean_term *exp, struct attribute *attrs)
{
    return exp;
}

static struct _ex_intern *normalize_terms(struct add_list *args)
{
    struct add_list *a = args;
	struct _ex_intern *type = _ex_int;

	while (a != NULL) {
	    struct _ex_intern *t = get_type(a->e);
		if (t == _ex_real) {
		    type = _ex_real;
		} else if (t != _ex_int) {
		    fprintf(stderr, "Term %s must have a numeric type\n", _th_print_exp(a->e));
            fprintf(stderr, "Type is %s\n", _th_print_exp(t));
			exit(1);
		}
		a = a->next;
	}

	if (type==_ex_real) {
	    a = args;
		while (a != NULL) {
		    struct _ex_intern *t = get_type(a->e);
			if (t==_ex_int) {
			    a->e = _ex_intern_appl1_env(env,INTERN_NAT_TO_RAT,a->e);
			}
		    a = a->next;
		}
	}

	return type;
}

static struct _ex_intern *build_fun_term(int functor, struct add_list *al);

static void cleanup()
{
    while (type_list) {
	    type_list->user2 = NULL;
		type_list = type_list->next_cache;
    }
    //_th_alloc_release(PARSE_SPACE, mark);
}

static struct symtab *find_entry(int symbol)
{
    int pos = symbol%HASH_SIZE;
    struct symtab *s = table[pos];

	while (s != NULL) {
	    if (s->name==symbol) return s;
		s = s->next;
    }

	return NULL;
}

static struct symtab *insert_entry(int symbol)
{
    int pos = symbol%HASH_SIZE;
    struct symtab *s = (struct symtab *)_th_alloc(PARSE_SPACE,sizeof(struct symtab));

    s->next = table[pos];
	table[pos] = s;
	s->name = symbol;
	s->value = s->type = NULL;
}

int _th_hack_has_real = 0;
int _th_hack_has_int = 0;

static struct symtab *find_type_entry(int symbol)
{
    int pos = symbol%HASH_SIZE;
    struct symtab *s = type_table[pos];

    if (symbol==INTERN_INT) _th_hack_has_int = 1;
    if (symbol==INTERN_REAL) _th_hack_has_real = 1;

	while (s != NULL) {
	    if (s->name==symbol) {
            return s;
        }
		s = s->next;
    }

	return NULL;
}

static struct symtab *insert_type_entry(int symbol)
{
    int pos = symbol%HASH_SIZE;
    struct symtab *s = (struct symtab *)_th_alloc(PARSE_SPACE,sizeof(struct symtab));

    s->next = type_table[pos];
	type_table[pos] = s;
	s->name = symbol;
	s->value = s->type = NULL;
    return s;
}

static void init_table()
{
    int i;
    struct symtab *s;

	for (i = 0; i < HASH_SIZE; ++i) {
	    table[i] = NULL;
		type_table[i] = NULL;
    }

	//mark = _th_alloc_mark(PARSE_SPACE);
	type_list = NULL;

    if (env==NULL) {
        env = _th_default_env(ENVIRONMENT_SPACE);
    }
    if (lenv==NULL) {
        lenv = _th_default_env(LEARN_ENV_SPACE);
    }
	u = _th_new_unifier(PARSE_SPACE);
    ulist = NULL;
    logic_name = 0;
    status = 0;
    assumption = NULL;
    formula = NULL;
    _th_set_default_var_type(env, NULL);
    _th_set_default_var_type(lenv, NULL);
    if (_th_hack_conversion > 0) {
	    s = insert_type_entry(INTERN_INT);
        s->type = _ex_real;
	    s = insert_type_entry(INTERN_REAL);
        s->type = _ex_real;
    } else if (_th_hack_conversion < 0) {
	    s = insert_type_entry(INTERN_INT);
        s->type = _ex_int;
	    s = insert_type_entry(INTERN_REAL);
        s->type = _ex_int;
    } else {
	    s = insert_type_entry(INTERN_INT);
        s->type = _ex_int;
	    s = insert_type_entry(INTERN_REAL);
        s->type = _ex_real;
    }
	s = insert_type_entry(INTERN_CAP_ARRAY);
    s->type = _ex_intern_appl_env(env,INTERN_CAP_ARRAY,0,NULL);
	s = insert_type_entry(INTERN_U);
    s->type = _ex_intern_appl_env(env,INTERN_U,0,NULL);
}

static struct _ex_intern *build_equality(struct _ex_intern *l, struct add_list *r)
{
   struct _ex_intern *e;
   if (r->next!=NULL) {
       fprintf(stderr, "Error: equality is only allowed to have two arguments\n");
       fprintf(stderr, "    %s\n", _th_print_exp(l));
       while (r) {
           fprintf(stderr, "    %s\n", _th_print_exp(r->e));
           r = r->next;
       }
       exit(1);
   }
   if (get_type(l)==_ex_int && get_type(r->e)==_ex_real) {
       l = _ex_intern_appl1_env(env,INTERN_NAT_TO_RAT,l);
   }
   if (get_type(l)==_ex_real && get_type(r->e)==_ex_int) {
       r->e = _ex_intern_appl1_env(env,INTERN_NAT_TO_RAT,r->e);
   }
   if (get_type(l) != get_type(r->e)) {
       fprintf(stderr, "Error: terms of equality must have the same type\n");
       fprintf(stderr, "l = %s\n", _th_print_exp(l));
       fprintf(stderr, "r = %s\n", _th_print_exp(r->e));
       exit(1);
   }
   e = _ex_intern_equal(env,get_type(l),l,r->e);
   //printf("Built equality function %s\n", _th_print_exp(e));
   return e;
}

static struct _ex_intern *build_distinct(struct _ex_intern *l, struct add_list *r)
{
   struct _ex_intern *e, *ret, *t1, *t2;

   ret = NULL;
   while (r) {
        struct add_list *t = r;
        while (t) {
            t1 = l;
            t2 = t->e;
            if (get_type(t1)==_ex_int && get_type(t2)==_ex_real) {
                t1 = _ex_intern_appl1_env(env,INTERN_NAT_TO_RAT,t1);
            }
            if (get_type(t1)==_ex_real && get_type(t2)==_ex_int) {
                t2 = _ex_intern_appl1_env(env,INTERN_NAT_TO_RAT,t2);
            }
            if (get_type(t1) != get_type(t2)) {
                fprintf(stderr, "Error: terms of equality must have the same type\n");
                fprintf(stderr, "l = %s\n", _th_print_exp(t1));
                fprintf(stderr, "r = %s\n", _th_print_exp(t2));
                exit(1);
            }
            e = _ex_intern_appl2_env(env,get_type(t1),t1,t2);
            e = _ex_intern_appl1_env(env,INTERN_NOT,e);
            if (ret) {
                ret = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,e,ret));
            } else {
                ret = e;
            }
            t = t->next;
        }
        l = r->e;
        r = r->next;
   }

   return ret;
}

static struct _ex_intern *build_ite(struct _ex_intern *c, struct _ex_intern *l, struct _ex_intern *r)
{
   struct _ex_intern *e;

   if (get_type(l)==_ex_int && get_type(r)==_ex_real) {
       l = _ex_intern_appl1_env(env,INTERN_NAT_TO_RAT,l);
   }
   if (get_type(l)==_ex_real && get_type(r)==_ex_int) {
       r = _ex_intern_appl1_env(env,INTERN_NAT_TO_RAT,r);
   }
   if (get_type(l) != get_type(r)) {
       fprintf(stderr, "Error: terms of ite must have the same type\n");
       fprintf(stderr, "l = %s\n", _th_print_exp(l));
       fprintf(stderr, "r = %s\n", _th_print_exp(r));
       exit(1);
   }
   e = _ex_intern_appl3_env(env,INTERN_ITE,c,l,r);
   e->type_inst = get_type(l);
   //printf("Built equality function %s\n", _th_print_exp(e));
   return e;
}

static int add_list_len(struct add_list *a)
{
    int count = 0;
    while (a) {
        ++count;
        a = a->next;
    }
    return count;
}

struct bt_list {
    struct bt_list *next;
    struct boolean_term *term;
};

static int bt_list_len(struct bt_list *a)
{
    int count = 0;
    while (a) {
        ++count;
        a = a->next;
    }
    return count;
}

static struct _ex_intern *shift_parameters(struct _ex_intern *ret, struct add_list *params)
{
    struct _ex_intern *x;

    while (params) {
        x = params->e;
        params->e = ret;
        ret = x;
        params = params->next;
    }

    return ret;
}

static void add_function(int fun, struct _ex_intern *ret, struct add_list *params)
{
    int count = 0, i;
    struct add_list *p = params;
    struct _ex_intern **args, *e, *t;
    char v[10];

    if (e = _th_get_type(env,fun)) {
        fprintf(stderr, "e = %s\n", _th_print_exp(e));
        fprintf(stderr, "Function or predicate '%s' already defined.\n", _th_intern_decode(fun));
        exit(1);
    }

    while (p) {
        p = p->next;
        ++count;
    }

    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
    count = 0;
    while (params) {
        args[count++] = params->e;
        params = params->next;
    }

    if (count==1) {
        t = _ex_intern_appl2_env(env,INTERN_ORIENTED_RULE,args[0],ret);
    } else {
        t = _ex_intern_appl2_env(env,INTERN_ORIENTED_RULE,_ex_intern_appl_env(env,INTERN_TUPLE,count,args),ret);
    }

    for (i = 0; i < count; ++i) {
        sprintf(v, "v%d", i);
        args[i] = _ex_intern_var(_th_intern(v));
    }

    e = _ex_intern_appl_env(env,fun,count,args);
    _th_add_function(env,e,t,_ex_true,0,NULL);
    _th_add_function(lenv,e,t,_ex_true,0,NULL);
    //fprintf(stderr, "Adding function %s %x\n", _th_print_exp(e), env);
}

extern int yylex();

struct boolean_term {
    int connective;
    struct _ex_intern *term;
    struct boolean_term *cond;
    struct boolean_term *left;
    struct boolean_term *right;
};

static struct boolean_term *build_connective(int connective, struct bt_list *r);

int bool_exp_count(int connective, struct boolean_term *term)
{
    if (term->connective != connective) return 1;

    return bool_exp_count(connective, term->left)+bool_exp_count(connective, term->right);
}

struct _ex_intern *build_bool_exp(struct env *env, struct boolean_term *term);

int fill_args(struct _ex_intern **args, int connective, struct boolean_term *term)
{
    int count;

    if (term->connective==connective) {
        count = fill_args(args, connective, term->left);
        args += count;
        count += fill_args(args, connective, term->right);
        return count;
    } else {
        args[0] = build_bool_exp(env,term);
        return 1;
    }
}

struct _ex_intern *build_ac_bool_exp(struct env *env, int connective, int functor, struct boolean_term *term)
{
    int count = bool_exp_count(connective,term);
    struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);

    fill_args(args,connective,term);

    return _th_flatten_top(env,_ex_intern_appl_env(env,functor,count,args));
}

%}

%union {
    unsigned            uval;
	int                 ival;
    char		    	*string;
    struct boolean_term *boolean;
    struct bt_list      *booleans;
    struct _ex_intern	*exp;
	struct add_list     *exps;
	struct attribute    *attr;
}

%token <string> NUMERAL_TOK
%token <string> VAR_TOK
%token <string> SYM_TOK
%token <string> STRING_TOK
%token <string> AR_SYMB
%token <string> USER_VAL_TOK
%token TRUE_TOK
%token FALSE_TOK
%token ITE_TOK
%token NOT_TOK
%token IMPLIES_TOK
%token IF_THEN_ELSE_TOK
%token AND_TOK
%token OR_TOK
%token XOR_TOK
%token IFF_TOK
%token EXISTS_TOK
%token FORALL_TOK
%token LET_TOK
%token FLET_TOK
%token NOTES_TOK
%token SORTS_TOK
%token FUNS_TOK
%token PREDS_TOK
%token EXTENSIONS_TOK
%token DEFINITION_TOK
%token AXIOMS_TOK
%token LOGIC_TOK
%token COLON_TOK
%token LPAREN_TOK
%token RPAREN_TOK
%token SAT_TOK
%token UNSAT_TOK
%token UNKNOWN_TOK
%token ASSUMPTION_TOK
%token FORMULA_TOK
%token STATUS_TOK
%token BENCHMARK_TOK
%token EXTRASORTS_TOK
%token EXTRAFUNS_TOK
%token EXTRAPREDS_TOK
%token LANGUAGE_TOK
%token DOLLAR_TOK
%token EQUALS_TOK
%token DISTINCT_TOK
%token SEMICOLON_TOK
%token EOF_TOK

%start benchmark

%type <ival>    benchmark
%type <ival>    attribute
%type <ival>    fvar
%type <ival>    fun_symb
%type <ival>    pred_symb
%type <ival>    user_value
%type <exp>     basic_term
%type <attr>    annotation
%type <attr>    annotations
%type <attr>    annotation_tail
%type <ival>    logic_name
%type <ival>    status
%type <exp>     prop_atom
%type <exp>     an_atom
%type <exp>     an_term
%type <exps>    an_terms
%type <ival>    quant_symb
%type <boolean> an_formula
%type <booleans> an_formulas
%type <ival>    connective
%type <exp>     sort_symb
%type <exps>    sort_symbs
%type <ival>    sort_symb_decl
%type <ival>    bench_name

%%
benchmark:
    LPAREN_TOK BENCHMARK_TOK bench_name bench_attributes RPAREN_TOK
    {
      
	/*(
      	let b = BENCH($3,$4) in
      	  if not (Hashtbl.mem symbol_table "status") then 
            raise (Validation_error "Status not defined.")
          else 
      	    if not (Hashtbl.mem symbol_table "formula") then 
              raise (Validation_error "Formula not defined.")
            else 
      	      if not (Hashtbl.mem symbol_table "logic") then 
                raise (Validation_error "Logic not defined.")
              else 
              (
		      	Hashtbl.clear symbol_table;
		      	Hashtbl.clear extrasorts;
              	Hashtbl.clear extrafuns;
	    	  	Hashtbl.clear extrapreds;
	      
	      		Hashtbl.replace symbol_table "---" "---";
		      	Hashtbl.replace extrasorts "---" "---";
		      	Hashtbl.replace extrafuns "---" "---";
	    	  	Hashtbl.replace extrapreds "---" "---";
	      	
			Hashtbl.replace extrasorts "Int" "Int";
		      	Hashtbl.replace extrasorts "Real" "Real";
		      	Hashtbl.replace extrasorts "Array" "Array";
				Hashtbl.replace extrapreds "<=" "<=";
				Hashtbl.replace extrapreds ">=" ">=";
				Hashtbl.replace extrapreds ">" ">";
				Hashtbl.replace extrapreds "<" "<";
				Hashtbl.replace extrapreds "select" "select";
				Hashtbl.replace extrafuns "+" "+";
				Hashtbl.replace extrafuns "-" "-";
				Hashtbl.replace extrafuns "*" "*";
				Hashtbl.replace extrafuns "select" "select";
				Hashtbl.replace extrafuns "store" "store";
				Hashtbl.replace extrafuns "~" "~";
                b;
              )
      )*/
    }

bench_name:
    SYM_TOK 
    { 
	    fprintf(stderr, "\nBench_name:%s\n", yytext);
        bench_name = strdup(yytext);
		$$ = _th_intern(yytext);
    }

bench_attributes:
    bench_attribute bench_attributes
  | bench_attribute

bench_attribute:
    COLON_TOK ASSUMPTION_TOK an_formula
    {
        if (assumption==NULL) {
            assumption = build_bool_exp(env,$3);
        } else {
            assumption = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_AND,assumption,build_bool_exp(env,$3)));
        }
    }
  | COLON_TOK FORMULA_TOK an_formula 
    {
      if (formula != NULL) {
          fprintf(stderr, "Formula already defined\n");
          exit(1);
      }
      formula = build_bool_exp(env,$3);
    }
  | COLON_TOK STATUS_TOK status 
    {
      if (status) {
          fprintf(stderr, "More than one status definition found.\n");
          exit(1);
      }
      //printf("Setting status %s\n", _th_intern_decode($3));
      status = $3;
    }
  | COLON_TOK LOGIC_TOK logic_name 
    {
      if (logic_name) {
          fprintf(stderr, "More than one logic definition found.\n");
          exit(1);
      }
      //printf("Setting logic name %s\n", _th_intern_decode($3));
      logic_name = $3;
    }
  | COLON_TOK EXTRASORTS_TOK LPAREN_TOK sort_symb_decls RPAREN_TOK
  | COLON_TOK EXTRAFUNS_TOK LPAREN_TOK fun_symb_decls RPAREN_TOK
  | COLON_TOK EXTRAPREDS_TOK LPAREN_TOK pred_symb_decls RPAREN_TOK
  | COLON_TOK NOTES_TOK STRING_TOK
  | annotation

logic_name:
    SYM_TOK { $$ = _th_intern(yytext); }

status:
    SAT_TOK { $$ = INTERN_SAT; }
  | UNSAT_TOK { $$ = INTERN_UNSAT; }
  | UNKNOWN_TOK { $$ = INTERN_UNKNOWN; }

sort_symbs:
    sort_symb sort_symbs
    {
      /* return a list of sorts */
      struct add_list *al;
      al = (struct add_list *)_th_alloc(PARSE_SPACE,sizeof(struct add_list));
      al->next = $2;
      al->e = $1;
      $$ = al;
    }
  | sort_symb 
    { 
      /* return a singleton list of one sort */
      struct add_list *al;
      al = (struct add_list *)_th_alloc(PARSE_SPACE,sizeof(struct add_list));
      al->next = NULL;
      al->e = $1;
      $$ = al;
    }

sort_symb_decls:
    sort_symb_decls sort_symb_decl
    { 
      /* declare sort names */
    }
  | sort_symb_decl 
    { 
      /* declare a singleton list of one sort name */
    }


fun_symb_decls:
    fun_symb_decls fun_symb_decl
  | fun_symb_decl



fun_symb_decl:
    LPAREN_TOK fun_symb sort_symb sort_symbs annotations RPAREN_TOK
    {
      /* returns the signature of a function with annotations */
      struct _ex_intern *r = shift_parameters($3,$4);
      add_function($2,r,$4);
    }
  | LPAREN_TOK fun_symb sort_symb sort_symbs RPAREN_TOK
    {
      /* returns the signature of a function without annotations */
      struct _ex_intern *r = shift_parameters($3,$4);
      add_function($2,r,$4);
    }
  | LPAREN_TOK fun_symb sort_symb annotations RPAREN_TOK
    {
        /* returns the signature of a function with annotations */
        if (_th_get_var_type(env,$2)) {
            fprintf(stderr, "Function %s already defined\n", _th_intern_decode($2));
            exit(1);
        }
        _th_set_var_type(env,$2,$3);
        _th_set_var_type(lenv,$2,$3);
    }
  | LPAREN_TOK fun_symb sort_symb RPAREN_TOK
    {
      /* returns the signature of a function without annotations */
      if (_th_get_var_type(env,$2)) {
          fprintf(stderr, "Function %s already defined\n", _th_intern_decode($2));
          exit(1);
      }
      _th_set_var_type(env,$2,$3);
      _th_set_var_type(lenv,$2,$3);
    }

pred_symb_decls:
    pred_symb_decls pred_symb_decl
  | pred_symb_decl

pred_symb_decl:
    LPAREN_TOK pred_symb sort_symbs annotations RPAREN_TOK
    {
      /* returns the signature of a predicate with annotations */
      add_function($2,_ex_bool,$3);
    }
  | LPAREN_TOK pred_symb annotations RPAREN_TOK
    {
      /* returns the signature of a predicate with annotations */
      if (_th_get_var_type(env,$2)) {
          fprintf(stderr, "Predicate %s already defined\n", _th_intern_decode($2));
          exit(1);
      }
      _th_set_var_type(env,$2,_ex_bool);
      _th_set_var_type(lenv,$2,_ex_bool);
    }
  | LPAREN_TOK pred_symb sort_symbs RPAREN_TOK
    {
      /* returns the signature of a predicate without annotations */
      add_function($2,_ex_bool,$3);
    }
  | LPAREN_TOK pred_symb  RPAREN_TOK
    {
      /* returns the signature of a predicate without annotations */
      if (_th_get_var_type(env,$2)) {
          fprintf(stderr, "Predicate %s already defined\n", _th_intern_decode($2));
          exit(1);
      }
      _th_set_var_type(env,$2,_ex_bool);
      _th_set_var_type(lenv,$2,_ex_bool);
    }

an_formulas:
    an_formula an_formulas
    {
        struct bt_list *a;
        a = (struct bt_list *)_th_alloc(PARSE_SPACE,sizeof(struct bt_list));
        a->next = $2;
        a->term = $1;
        if (a->term==NULL) exit(1);
        $$ = a;
    }
  | an_formula
    {
        struct bt_list *a;
        a = (struct bt_list *)_th_alloc(PARSE_SPACE,sizeof(struct bt_list));
        a->next = NULL;
        a->term = $1;
        if (a->term==NULL) exit(1);
        $$ = a;
    }

an_formula:
    an_atom
    {
      $$ = (struct boolean_term *)_th_alloc(PARSE_SPACE,sizeof(struct boolean_term));
      $$->connective = 0;
      $$->term = $1;
    }
  | LPAREN_TOK connective an_formulas annotations RPAREN_TOK
    {
      /* returns a formula for one of the boolean connectives with annotations */
      $$ = build_formula_attr(build_connective($2,$3),$4);
      //if ($$==NULL) printf("Fail1\n");
    }
  | LPAREN_TOK connective an_formulas RPAREN_TOK
    {
      /* returns a formula for one of the boolean connectives without annotations */
      $$ = build_connective($2,$3);
      //if ($$==NULL) printf("Fail2\n");
    }
  | LPAREN_TOK quant_symb quant_vars an_formula annotations RPAREN_TOK
    {
      /* returns a quantified formula with annotations
      FA(QUANT($2,$3,$4),$5) */
    }
  | LPAREN_TOK quant_symb quant_vars an_formula RPAREN_TOK
    {
      /* returns a quantified formula with no annotations
      F(QUANT($2,$3,$4)) */
    }
  | LPAREN_TOK LET_TOK LPAREN_TOK VAR_TOK { push_variable(_th_intern(yytext)); } an_term
    {
       /* returns a let formula with annotations */
        set_value($6);
    }
    RPAREN_TOK an_formula annotation_tail
    {
        $$ = build_formula_attr($9,$10);
        pop_variable();
        //if ($$==NULL) printf("Fail3\n");
    }
  | LPAREN_TOK FLET_TOK LPAREN_TOK fvar { push_variable($4); } an_formula
    {
        /* returns a flet formula with annotations */
        set_value(build_bool_exp(env,$6));
    }
    RPAREN_TOK an_formula annotation_tail
    {
        $$ = build_formula_attr($9,$10);
        pop_variable();
        //if ($$==NULL) printf("Fail5\n");
    }

quant_vars:
    quant_vars quant_var 
    {
      /* returns a list of binders
      $2::$1 */
    }
  | quant_var 
    {
      /* returns a singleton list with one binder in it
      [$1] */
    }

quant_var: 
    LPAREN_TOK VAR_TOK sort_symb RPAREN_TOK
    {
      /* returns the name of the variable along with the name of its sort
      ($2,$3) */
    }

quant_symb:
    EXISTS_TOK { $$ = INTERN_EXISTS; }
  | FORALL_TOK { $$ = INTERN_ALL; }

connective:
    NOT_TOK { $$ = NOT_TOK; }
  | IMPLIES_TOK { $$ = IMPLIES_TOK; }
  | IF_THEN_ELSE_TOK { $$ = IF_THEN_ELSE_TOK; }
  | AND_TOK { $$ = AND_TOK; }
  | OR_TOK { $$ = OR_TOK; }
  | XOR_TOK { $$ = XOR_TOK; }
  | IFF_TOK { $$ = IFF_TOK; }


an_atom:
    prop_atom 
    {
      /* returns a formula for a propositional atom with no annotations */
      $$ = $1;
      //if ($$==NULL) printf("Fail7\n");
    }
  | LPAREN_TOK prop_atom annotations RPAREN_TOK 
    {
      /* returns a formula for a propositional atom with annotations */
      $$ = build_attr_term($2,$3);
      //if ($$==NULL) printf("Fail8\n");
    }
  | LPAREN_TOK pred_symb an_terms annotations RPAREN_TOK
    {
      /* returns a formula for a predicate that has 1 or more arguments with annotations*/
      struct _ex_intern *r = build_attr_term(build_fun_term($2,$3),$4);
      if (get_type(r) != _ex_bool) {
          fprintf(stderr, "Error: %s is not a predicate\n", _th_intern_decode($2));
          exit(1);
      }
      $$ = r;
    }
  | LPAREN_TOK pred_symb an_terms RPAREN_TOK
    {
      /* returns a formula for a predicate that has 1 or more arguments with no annotations*/
      struct _ex_intern *r = build_fun_term($2,$3);
      if (get_type(r) != _ex_bool) {
          fprintf(stderr, "Error: %s is not a predicate\n", _th_intern_decode($2));
          exit(1);
      }
      $$ = r;
    }
  | LPAREN_TOK EQUALS_TOK an_term an_terms annotations RPAREN_TOK
    {
      /* returns a formula for equality with annotations
         Note that it requires at least two terms*/
      $$ = build_attr_term(build_equality($3,$4),$5);
    }
  | LPAREN_TOK EQUALS_TOK an_term an_terms RPAREN_TOK
    {
      /* returns a formula for equality with no annotations
         Note that it requires at least two terms*/      
      $$ = build_equality($3,$4);
    }
  | LPAREN_TOK DISTINCT_TOK an_term an_terms annotations RPAREN_TOK
    {
      /* returns a formula for distinct with annotations
         Note that it requires at least two terms*/
      $$ = build_attr_term(build_distinct($3,$4),$5);
    }
  | LPAREN_TOK DISTINCT_TOK an_term an_terms RPAREN_TOK
    {
      /* returns a formula for distinct with no annotations
         Note that it requires at least two terms*/
      $$ = build_distinct($3,$4);
    }


prop_atom:
    TRUE_TOK
    {
      /* returns a formula for true */
      $$ = _ex_true;
    }
  | FALSE_TOK
    { 
      /* returns a formula for false */
      $$ = _ex_false;

    }
  | fvar
    {
      /* returns a formula variable that should be bound with a flet formula higher in the parse tree */
	  struct _ex_intern *r = _th_apply(u,$1);
	  if (r==NULL) {
	      fprintf(stderr, "let variable %s is undefined\n", _th_intern_decode($1));
		  exit(1);
      }
      if (get_type(r) != _ex_bool) {
          fprintf(stderr, "let variabl %s is not a boolean\n", _th_intern_decode($1));
          exit(1);
      }
      $$ = r;
    }
  | pred_symb 
    {
      /* returns a predicate with no arguments (a propositional variable) */
      if (_th_get_var_type(env,$1)!=_ex_bool) {
		  fprintf(stderr, "predicate %s is not defined (or not a boolean)\n", _th_intern_decode($1));
		  exit(1);
	  }
      $$ = _ex_intern_var($1);
    }
  

an_terms:
    an_term an_terms 
    {
      /* returns a list of terms*/
      struct add_list *a = (struct add_list *)_th_alloc(PARSE_SPACE,sizeof(struct add_list));
      a->next = $2;
      a->e = $1;
      $$ = a;
    }
  | an_term 
    { 
      /* returns a singleton list of terms */
      struct add_list *a = (struct add_list *)_th_alloc(PARSE_SPACE,sizeof(struct add_list));
      a->next = NULL;
      a->e = $1;
      $$ = a;
    }

an_term:
    basic_term 
    { 
      /* returns a basic term with no annotations */
      $$ = $1;
    }
  | LPAREN_TOK basic_term annotations RPAREN_TOK 
    {
      /* adds annotations to a basic term and returns an annotated term */
	  $$ = build_attr_term($2,$3);
    }
  | LPAREN_TOK fun_symb an_terms annotations RPAREN_TOK
    {
      /* returns a function term with at least one argument with annotations */
      $$ = build_attr_term(build_fun_term($2,$3),$4);
    }
  | LPAREN_TOK fun_symb an_terms RPAREN_TOK
    {
      /* returns a function term with at least one argument with no annotations */
	  //if (_th_get_type(env,$2)==NULL) {
	  //    fprintf(stderr, "Illegal function symbol %s\n", _th_intern_decode($2));
      //	  exit(1);
      //}
      $$ = build_fun_term($2,$3);
    }
  | LPAREN_TOK ITE_TOK an_formula an_term an_term annotations RPAREN_TOK
    {
      /* returns an ITE term with annotations */
      $$ = build_attr_term(build_ite(build_bool_exp(env,$3),$4,$5),$6);
    }
  | LPAREN_TOK ITE_TOK an_formula an_term an_term RPAREN_TOK
    {
      /* returns an ITE term with no annotations */
      $$ = build_ite(build_bool_exp(env,$3),$4,$5);
    }


basic_term:
    VAR_TOK 
    { 
      /* returns a variable term*/
      struct _ex_intern *r = _th_apply(u,_th_intern(yytext));
      if (r==NULL) {
          fprintf(stderr, "%s is undefined\n", yytext);
          exit(1);
      }
      $$ = r;
    }
  | NUMERAL_TOK 
    {
      /* returns a numeral term*/
	  $$ = _th_parse(env,yytext);
    }
  | fun_symb 
    {
	  struct _ex_intern *s = _th_get_var_type(env,$1);
	  if (s==NULL) {
	      fprintf(stderr, "Function %s not yet defined.\n", _th_intern_decode($1));
		  exit(1);
	  }
	  $$ = _ex_intern_var($1);
    }

annotations:
    annotation annotations 
    { 
      /*  returns a list of annotations*/
      $$ = $1;
	  $1->next = $2;
    }
  | annotation 
    {
	  /* returns a singleton list of annotations */
      $$ = $1;
    }

annotation_tail:
    RPAREN_TOK
    {
      $$ = NULL;
    }
  | annotations RPAREN_TOK
    {
      $$ = $1;
    }
  
annotation:
    attribute 
    {
      /* returns the attribute's name and None because it doesn't have a corresponding value */
	  struct attribute *attr = (struct attribute *)_th_alloc(CACHE_SPACE,sizeof(struct attribute));
	  attr->name = $1;
	  attr->value = 0;
	  attr->next = NULL;
	  $$ = attr;
    }
  | attribute user_value 
    {
      /* returns the attribute's name and None because it doesn't have a corresponding value */
	  struct attribute *attr = (struct attribute *)_th_alloc(CACHE_SPACE,sizeof(struct attribute));
	  attr->name = $1;
	  attr->value = $2;
	  attr->next = NULL;
	  $$ = attr;
    }

user_value:
    USER_VAL_TOK
    {
    	$$ = _th_intern(yytext);
    }

sort_symb_decl:
    SYM_TOK 
    { 
      /* returns the name of the sort symbol*/
	  int i = _th_intern(yytext);
      struct symtab *s = find_type_entry(i);
	  if (s!=NULL) {
	      fprintf(stderr, "sort %s is already defined.\n", $1);
		  exit(1);
      }
	  s = insert_type_entry(i);
      s->type = _ex_intern_appl_env(env,i,0,NULL);
      $$ = i;
    }

sort_symb:
    SYM_TOK 
    { 
      /* returns the name of the sort symbol*/
      struct symtab *s = find_type_entry(_th_intern(yytext));
	  if (s==NULL) {
	      fprintf(stderr, "sort %s is not defined.\n", yytext);
		  exit(1);
      }
      $$ = s->type;
    }

pred_symb:
    SYM_TOK 
    {
        /* returns the name of the predicate */
        $$ = _th_intern(yytext);
    }
  | AR_SYMB 
    {
        /* returns the name of the predicate  */
        $$ = _th_intern(yytext);
    }

fun_symb:
    SYM_TOK
    {
        /* returns the name of the function */
        $$ = _th_intern(yytext);
    }
  | AR_SYMB 
    { 
        /* returns the name of the function */
        $$ = _th_intern(yytext);
    }


attribute:
    COLON_TOK SYM_TOK { $$ = _th_intern_concat(INTERN_COLON, _th_intern(yytext)); }

fvar:
    DOLLAR_TOK SYM_TOK { $$ = _th_intern_concat(INTERN_DOLLAR_SIGN, _th_intern(yytext)); }

%%

struct _ex_intern *build_bool_exp(struct env *env, struct boolean_term *term)
{
    switch (term->connective) {
        case 0:
            return term->term;
        case NOT_TOK:
            return _ex_intern_appl1_env(env,INTERN_NOT,build_bool_exp(env,term->left));
        case IMPLIES_TOK:
            return _th_flatten_top(env,
                       _ex_intern_appl2_env(env,INTERN_OR,
                           _ex_intern_appl1_env(env,INTERN_NOT,build_bool_exp(env,term->left)),
                           build_bool_exp(env,term->right)));
        case IF_THEN_ELSE_TOK:
            return _ex_intern_appl3_env(env,INTERN_ITE,
                       build_bool_exp(env,term->cond),
                       build_bool_exp(env,term->left),
                       build_bool_exp(env,term->right));
        case AND_TOK:
            return build_ac_bool_exp(env,AND_TOK,INTERN_AND,term);
        case OR_TOK:
            return build_ac_bool_exp(env,OR_TOK,INTERN_OR,term);
        case XOR_TOK:
            return build_ac_bool_exp(env,XOR_TOK,INTERN_XOR,term);
        case IFF_TOK:
            return _ex_intern_equal(env,_ex_bool,build_bool_exp(env,term->left),
                                                 build_bool_exp(env,term->right));
        default:
            fprintf(stderr, "Internal parser error\n");
            exit(1);
    }
}

static struct _ex_intern *build_arith_term(int nfunctor, int rfunctor, struct add_list *al)
{
    struct _ex_intern *type = normalize_terms(al);
    type = normalize_terms(al);

	if (type==_ex_int) {
	    return build_fun_term(nfunctor, al);
	} else {
	    return build_fun_term(rfunctor, al);
    }
}

int _th_unknown;

static struct _ex_intern *build_fun_term(int functor, struct add_list *al)
{
    int count;
	struct add_list *a;
    struct _ex_intern **args, *e;
    struct _ex_intern *type;

    if (functor==INTERN_STORE || functor==INTERN_SELECT) {
        _th_unknown = 1;
    }

    if (functor==INTERN_TILDE) {
        struct _ex_intern *type = get_type(al->e);
        if (type==_ex_int) {
            return _ex_intern_appl2_env(env,INTERN_NAT_MINUS,_ex_intern_small_integer(0),al->e);
        } else {
            return _ex_intern_appl2_env(env,INTERN_RAT_MINUS,_ex_intern_small_rational(0,1),al->e);
        }
    }

    if (functor==INTERN_PLUS) {
	    return build_arith_term(INTERN_NAT_PLUS,INTERN_RAT_PLUS,al);
	}
    if (functor==INTERN_STAR) {
	    return build_arith_term(INTERN_NAT_TIMES,INTERN_RAT_TIMES,al);
	}
    if (functor==INTERN_SLASH) {
        functor = INTERN_RAT_DIVIDE;
	    //return build_arith_term(INTERN_NAT_DIVIDE,INTERN_RAT_DIVIDE,al);
	}
    if (functor==INTERN_MINUS) {
	    return build_arith_term(INTERN_NAT_MINUS,INTERN_RAT_MINUS,al);
	}
    if (functor==INTERN_PERCENT) {
	    return build_arith_term(INTERN_NAT_MOD,INTERN_RAT_MOD,al);
	}
	if (functor==INTERN_LESS) {
        return build_arith_term(INTERN_NAT_LESS,INTERN_RAT_LESS,al);
	}
    if (functor==INTERN_GREATER) {
	    a = al->next;
		a->next = al;
		al->next = NULL;
		return build_arith_term(INTERN_NAT_LESS,INTERN_RAT_LESS,a);
	}
    if (functor==INTERN_GREATER_EQUAL) {
	    return _ex_intern_appl1_env(env,INTERN_NOT,build_arith_term(INTERN_NAT_LESS,INTERN_RAT_LESS,al));
	}
	if (functor==INTERN_LESS_EQUAL) {
	    a = al->next;
		a->next = al;
		al->next = NULL;
		return _ex_intern_appl1_env(env,INTERN_NOT,build_arith_term(INTERN_NAT_LESS,INTERN_RAT_LESS,a));
	}
	if (functor==INTERN_EQUAL) {
        if (get_type(al->e)==_ex_int && get_type(al->next->e)==_ex_real) {
		    al->e = _ex_intern_appl1_env(env,INTERN_NAT_TO_RAT,al->e);
		}
	    if (get_type(al->e)==_ex_real && get_type(al->next->e)==_ex_int) {
		    al->next->e = _ex_intern_appl1_env(env,INTERN_NAT_TO_RAT,al->next->e);
		}
	}

    type = _th_get_type(env,functor);
    if (type==NULL) {
        fprintf(stderr, "Undefined function %s used.\n", _th_intern_decode(functor));
        exit(1);
    }

	a = al;
	count = 0;
	while (a) {
	    ++count;
		a = a->next;
	}

    if (!_th_is_ac(env,functor) && !_th_is_a(env,functor) &&
        ((type->u.appl.args[0]->u.appl.functor != INTERN_TUPLE && count !=1) ||
         (type->u.appl.args[0]->u.appl.functor == INTERN_TUPLE && count != type->u.appl.args[0]->u.appl.count))) {
         fprintf(stderr, "Arg count mismatch for %s (got %d arg(s), type = %s)\n", _th_intern_decode(functor), count, _th_print_exp(type));
         exit(1);
    }

	args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * count);
	a = al;
	count = 0;
	while (a) {
        if (functor==INTERN_EQUAL) {
            if (get_type(a->e) != get_type(a->next->e)) {
                printf("type mismatch of the arguments to =\n");
            }
        } else {
            //printf("type is %s %s\n", _th_intern_decode(functor), _th_print_exp(type));
            if (type->u.appl.args[0]->u.appl.functor==INTERN_TUPLE) {
                int p = count;
                if (_th_is_ac(env,functor)) p = 0;
                if (get_type(a->e)==_ex_int && type->u.appl.args[0]->u.appl.args[p]==_ex_real) {
                    a->e = _ex_intern_appl1_env(env,INTERN_NAT_TO_RAT,a->e);
                } else if (get_type(a->e) != type->u.appl.args[0]->u.appl.args[p]) {
                    printf("type mismatch a of %s in position %d of functor %s\n",
                           _th_print_exp(a->e), count, _th_intern_decode(functor));
                }
            } else {
                if (get_type(a->e)==_ex_int && type->u.appl.args[0]==_ex_real) {
                    a->e = _ex_intern_appl1_env(env,INTERN_NAT_TO_RAT,a->e);
                } else if (get_type(a->e) != type->u.appl.args[0]) {
                    printf("type mismatch b of %s in position %d of functor %s\n",
                           _th_print_exp(a->e), count, _th_intern_decode(functor));
                }
            }
        }
	    args[count++] = a->e;
		a = a->next;
	}

	e = _ex_intern_appl_env(env, functor, count, args);
    if (_th_is_ac(env,functor) || _th_is_a(env,functor)) {
        e = _th_flatten_top(env,e);
    }

    //printf("Built function %s\n", _th_print_exp(e));
    return e;
}

static struct boolean_term *build_connective(int connective, struct bt_list *r)
{
    struct boolean_term *term = (struct boolean_term *)_th_alloc(PARSE_SPACE,sizeof(struct boolean_term));
    struct boolean_term *ot;

    term->connective = connective;

    switch (connective) {
        case NOT_TOK:
            if (bt_list_len(r) != 1) {
                fprintf(stderr, "Error: more than one parameter for NOT\n");
                exit(1);
            }
            term->left = r->term;
            break;
        case IMPLIES_TOK:
        case IFF_TOK:
            if (bt_list_len(r) != 2) {
                fprintf(stderr, "Error: IMPLIES or IFF takes two parameters\n");
                exit(1);
            }
            term->left = r->term;
            term->right = r->next->term;
            break;
        case AND_TOK:
        case OR_TOK:
        case XOR_TOK:
            if (bt_list_len(r)==1) {
                term = r->term;
                break;
            } else {
                //if (bt_list_len(r) < 2) {
                //    fprintf(stderr, "Error: AND/OR/XOR take atleast two parameters\n");
                //    exit(1);
                //}
                ot = term;
                while (r->next->next != NULL) {
                    term->connective = connective;
                    term->left = r->term;
                    term->right = (struct boolean_term *)_th_alloc(PARSE_SPACE,sizeof(struct boolean_term));
                    term = term->right;
                    r = r->next;
                }
                term->connective = connective;
                term->left = r->term;
                term->right = r->next->term;
                term = ot;
            }
            break;
           
        case IF_THEN_ELSE_TOK:
            if (bt_list_len(r) != 3) {
                fprintf(stderr, "Error: IF_THEN_ELSE takes 3 parameters\n");
                exit(1);
            }
            term->cond = r->term;
            term->left = r->next->term;
            term->right = r->next->next->term;
            break;
        default:
            fprintf(stderr, "Internal error\n");
            exit(1);
    }

    return term;
}

struct env *_th_get_learn_env()
{
    //_th_pop_context_rules(ENVIRONMENT_SPACE, lenv);
    //_th_push_context_rules(ENVIRONMENT_SPACE, lenv);

    return lenv;
}

unsigned _th_get_status()
{
    return (unsigned)status;
}

char *_th_get_status_name()
{
    return _th_intern_decode((unsigned)status);
}

struct _ex_intern *_th_parse_smt(struct env *e, char *name)
{
    extern int yyparse();
    struct _ex_intern *res;
    extern FILE *yyin;
    char *mark = _th_alloc_mark(PARSE_SPACE);
    char *mark2 = _th_alloc_mark(REWRITE_SPACE);

    _th_hack_has_real = 0;
    _th_hack_has_int = 0;

    env = e;
    lenv = NULL;

    _th_unknown = 0;

    if (name) {
        yyin = fopen(name, "r");
        if (yyin==NULL) {
            fprintf(stderr, "File not found\n");
            exit(1);
        }
    }

    init_table();
    //while (1) {
    //    extern char *yytext;
    //    int x = yylex();
    //    printf("x, yytext = %d %s\n", x, yytext);
    //}
    yyparse();
    if (assumption==NULL) {
        res = _ex_intern_appl1_env(env,INTERN_NOT,formula);
    } else {
        res = _ex_intern_appl2_env(env,INTERN_OR,
                  _ex_intern_appl1_env(env,INTERN_NOT,assumption),
                  _ex_intern_appl1_env(env,INTERN_NOT,formula));
    }
    cleanup();

    if (name) fclose(yyin);

    _th_alloc_release(PARSE_SPACE,mark);
    _th_alloc_release(REWRITE_SPACE,mark2);

    env = NULL;

    _th_push_context_rules(lenv);

    return res;
}
