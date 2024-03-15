/*
 * parse.c
 *
 * Parser routines for the prover.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <ctype.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "Globals.h"
#include "Intern.h"

static char *p ;

static void skip_white_space()
{
    while (*p == ' ' || *p=='\t' || *p== '\n') ++p ;
}

#define MAX_IDENTIFIER 200

int is_letter(char c)
{
	return isalpha(c) || c=='_' || c=='+' || c=='!' || c=='<' || c=='>' || c== '=' || c=='*' ||
		   c=='/' || c=='.';
}

static unsigned read_identifier(int dollar_start)
/*
 * Parse an identifier and return the interned value
 */
{
    char identifier[MAX_IDENTIFIER+1] ;
    int x = 0 ;

    if (is_letter(*p) || (*p=='$' && dollar_start)) {
        identifier[x++] = tolower(*p++) ;
        while (is_letter(*p) || *p=='-' || isdigit(*p)) {
            if (x >= MAX_IDENTIFIER) {
                return 0 ;
            }
            identifier[x++] = tolower(*p++) ;
        }
        identifier[x++] = 0 ;
        return _th_intern(identifier) ;
    } else {
        return 0 ;
    }
}

#define MAX_STRING 255

#define ARG_INCREMENT 4000

static struct _ex_intern **args, **all_args ;
static unsigned arg_size, arg_start ;

void _th_svc_parse_init()
{
    arg_size = ARG_INCREMENT ;

    all_args = args =
        (struct _ex_intern **)MALLOC(sizeof(struct _ex_intern *) * ARG_INCREMENT) ;
    arg_start = 0 ;
}

static void set_start()
{
    args = all_args + arg_start ;
}

static void check_size(unsigned size)
{
    if (arg_start + size > arg_size) {
        arg_size = arg_start + size + ARG_INCREMENT ;
        all_args = (struct _ex_intern **)REALLOC(all_args,sizeof(struct _ex_intern *) * arg_size) ;
        set_start() ;
    }
}

#define TYPE_ANY      0
#define TYPE_BOOL    -1
#define TYPE_INTEGER -2
#define TYPE_BITVEC  -3
#define TYPE_REAL    -4

#define HASH_SIZE 4001

struct type_hash {
	struct type_hash *next;
	unsigned var;
	int type;
};

struct term_hash {
	struct term_hash *next;
	unsigned number;
	struct _ex_intern *term;
	int type;
};

static struct type_hash *type_table[HASH_SIZE];

static struct term_hash *term_table[HASH_SIZE];

int return_type;
int has_nplus_in_ite(struct _ex_intern *e)
{
	int i;

	if (e==NULL) return 0;

	switch (e->type) {
	    case EXP_APPL:
			if (e->u.appl.functor==INTERN_ITE && e->u.appl.args[0]->type==EXP_APPL &&
				e->u.appl.args[0]->u.appl.functor==INTERN_NAT_PLUS) {
				//int *x = 0;
				printf("Plus in ite: %s\n", _th_print_exp(e));
				fflush(stdout);
				//printf("*x = %d\n", *x);
				return 1;
			}
			for (i = 0; i < e->u.appl.count; ++i) {
				if (has_nplus_in_ite(e->u.appl.args[i])) {
					//printf("    Parent: %s\n", _th_print_exp(e));
					//fflush(stdout);
					return 1;
				}
			}
			return 0;
		default:
			return 0;
	}
}

static struct _ex_intern *parse_exp(struct env *env, int expected_type)
{
    struct _ex_intern *exp, *cond, *exp2 ;
    static char string[MAX_STRING] ;
	struct _ex_intern *args[MAX_ARGS];
	int types[MAX_ARGS];
    int n, n2, width ;
    unsigned var, id ;
    struct term_hash *term;
	struct type_hash *type;
	int hash;
	unsigned zero[2] = { 1, 0 };
	unsigned two[2] = { 1, 2 };
	unsigned *acc;
    //char x;

	//x = 0;
	//if (strlen(p) > 500) {
	//	x = p[500];
	//	p[500] = 0;
	//}
    //printf("Parsing '%s'\n", p);
	//printf("**********************************************************Here a '%s'\n", p);
    //printf("expected type = %d\n", expected_type);
    //if (x) p[500] = x;
	//fflush(stdout);

    skip_white_space() ;

	//printf("Here b %d\n", expected_type);
	//fflush(stdout);

    if (*p=='(' || *p=='{') {
		++p;
		skip_white_space();
        if (isdigit(*p)) {
            n = 0;
            while (isdigit(*p)) {
                n = n*10 + *p - '0';
                ++p;
            }
            skip_white_space();
            if (*p==')' || *p=='}') {
                ++p;
                return _ex_intern_small_integer(n);
            } else {
                return NULL;
            }
        }
		id = read_identifier(0);
		skip_white_space();
		//printf("Here c %d\n", id);
		//fflush(stdout);
		switch (id) {
		    case INTERN_BITSEL:
				//printf("bitsel\n");
				exp = parse_exp(env, TYPE_INTEGER);
				//if (has_nplus_in_ite(exp)) exit(1);
				if (exp==NULL) {
					printf("bitsel bad 1\n");
					return NULL;
				}
				skip_white_space();
				cond = parse_exp(env, TYPE_INTEGER);
				//if (has_nplus_in_ite(cond)) exit(1);
				//printf("Parse sel1 %s\n", _th_print_exp(cond));
				if (cond==NULL) {
					printf("bitsel bad 2\n");
					return NULL;
				}
				if (cond->type != EXP_INTEGER) {
					printf("bitsel bad 3\n");
					return NULL;
				}
     			if (cond->u.integer[0] != 1 ||
					(cond->u.integer[1] & 0x80000000)) {
					printf("bitsel bad 3\n");
					return NULL;
				}
                n = (int)cond->u.integer[1];
				skip_white_space();
				cond = parse_exp(env, TYPE_INTEGER);
				//if (has_nplus_in_ite(cond)) exit(1);
				//printf("Parse sel2 %s\n", _th_print_exp(cond));
				if (cond==NULL) {
					printf("bitsel bad 4\n");
					return NULL;
				}
				if (cond->type != EXP_INTEGER) {
					printf("bitsel bad 5\n");
					return NULL;
				}
     			if (cond->u.integer[0] != 1 ||
					(cond->u.integer[1] & 0x80000000)) {
					printf("bitsel bad 6\n");
					return NULL;
				}
                n2 = (int)cond->u.integer[1];
				//printf("Range %d %d\n", n, n2);
				if (n2 > n) {
					printf("bitsel bad 7\n");
					return NULL;
				}
				return_type = (int)n - n2 + 1;
				//printf("Select %d %d\n", n, n2);
				//printf("n-n2+1 = %d\n", n-n2+1);
				//printf("int %s\n", _th_print_exp(exp = _ex_intern_small_integer(n-n2+1)));
				//printf("val %d %d\n", exp->u.integer[0], exp->u.integer[1]);
				exp = _ex_intern_appl2_env(env,INTERN_NAT_MOD,
					      _ex_intern_appl2_env(env,INTERN_NAT_DIVIDE,
						      exp,
							  _ex_intern_appl2_env(env,INTERN_NAT_POWER,_ex_intern_small_integer(2),_ex_intern_small_integer(n2))),
						  _ex_intern_appl2_env(env,INTERN_NAT_POWER,_ex_intern_small_integer(2),_ex_intern_small_integer(n-n2+1)));
				printf("bitsel exp = %s\n", _th_print_exp(exp));
				printf("type = %d\n", return_type);
				break;
			case INTERN_BITPLUS:
				//printf("bitplus\n");
                n = 0 ;
				if (*p=='@') {
					++p;
					n2 = 0;
					while (isdigit(*p)) {
						n2 = (n2 * 10) + *p - '0';
						++p;
					}
					skip_white_space();
					width = n2;
				} else {
    				width = 0;
				}
                while (*p != ')' && *p != '}' && *p) {
					if (n==MAX_ARGS) {
						printf("bitplus bad 1\n");
						return NULL;
					}
                    cond = parse_exp(env, TYPE_INTEGER) ;
    				//if (has_nplus_in_ite(cond)) exit(1);
					if (cond==NULL) {
						printf("bitplus bad 2\n");
						return NULL;
					}
					if (return_type==TYPE_INTEGER || return_type==TYPE_ANY) {
						n2 = TYPE_INTEGER;
					} else if (return_type==TYPE_BOOL) {
						return_type = 1;
						cond = _ex_intern_appl3_env(env,INTERN_ITE,cond,_ex_intern_small_integer(1),_ex_intern_small_integer(0));
						//if (cond->u.appl.args[0]->type==EXP_INTEGER) {
						//	fprintf(stderr, "Fail 1\n");
						//	exit(1);
						//}
					} else if (return_type < 0) {
						printf("bitplus bad 3\n");
						return NULL;
					} else if (return_type > n2 && n2 != TYPE_INTEGER) {
						n2 = return_type;
					}
                    args[n++] = cond ;
                    skip_white_space() ;
				}
				//printf("bitplus done %d\n", n2);
                exp = _ex_intern_appl_env(env,INTERN_NAT_PLUS,n,args) ;
                exp = _th_flatten_top(env,exp);
				if (n2 != TYPE_INTEGER) {
					//printf("plus %d\n", n2);
				    exp = _ex_intern_appl2_env(env,INTERN_NAT_MOD,exp,_ex_intern_appl2_env(env,INTERN_NAT_POWER,_ex_intern_small_integer(2),_ex_intern_small_integer(n2+1)));
				}
				if (width) {
					return_type = width;
				} else if (n2==TYPE_INTEGER) {
                    return_type = TYPE_INTEGER;
				} else {
				    return_type = n2+1;
				}
				break;
			case INTERN_BITCAT:
				//printf("bitcat\n");
				n2 = 0;
                n = 0 ;
				//printf("bitcat\n");
                while (*p != ')' && *p != '}' && *p) {
					if (n==MAX_ARGS) {
						printf("bitcat bad 1\n");
						return NULL;
					}
                    cond = parse_exp(env, 0) ;
    				//if (has_nplus_in_ite(cond)) exit(1);
					if (cond==NULL) {
						printf("bitcat bad 2\n");
						return NULL;
					}
					if (return_type==TYPE_BOOL) {
						cond = _ex_intern_appl3_env(env,INTERN_ITE,cond,_ex_intern_small_integer(1),_ex_intern_small_integer(0));
						//if (cond->u.appl.args[0]->type==EXP_INTEGER) {
						//	fprintf(stderr, "Fail 2\n");
						//	exit(1);
						//}
						return_type = 1;
					}
					if (return_type <= 0) {
						printf("bitcat bad 3 %d\n", return_type);
						return NULL;
					}
					//printf("    returned %s %d\n", _th_print_exp(cond), return_type);
					types[n] = return_type;
					n2 += return_type;
                    args[n++] = cond ;
                    skip_white_space() ;
				}
				return_type = n2;
				for (id = 0; id < (unsigned)n; ++id) {
					types[id] = 0;
					for (n2 = (int)id+1; n2 < n; ++n2) {
						types[id] += types[n2];
					}
					args[id] = _ex_intern_appl2_env(env,INTERN_NAT_TIMES,
						           args[id],
								   _ex_intern_appl2_env(env,INTERN_NAT_POWER,
								       _ex_intern_small_integer(2),
									   _ex_intern_small_integer(types[id])));
				}
				exp = _ex_intern_appl_env(env,INTERN_NAT_PLUS,n,args);
                exp = _th_flatten_top(env,exp);
				break;
			case INTERN_BITNOT:
				//printf("bitnot\n");
				cond = parse_exp(env, expected_type);
    		    //if (has_nplus_in_ite(cond)) exit(1);
				if (cond==NULL) {
					printf("bitnot bad 1\n");
					return NULL;
				}
				if (return_type==TYPE_BOOL) {
					cond = _ex_intern_appl3_env(env,INTERN_ITE,cond,_ex_intern_small_integer(1),_ex_intern_small_integer(0));
					//if (cond->u.appl.args[0]->type==EXP_INTEGER) {
				 	//	fprintf(stderr, "Fail 3\n");
					//	exit(1);
					//}
					return_type = 1;
				}
				if (return_type <= 0) {
					printf("bitnot bad 2\n");
					return NULL;
				}
				exp = _ex_intern_appl2_env(env,INTERN_NAT_MINUS,
					      _ex_intern_appl2_env(env,INTERN_NAT_PLUS,
						      _ex_intern_small_integer(-1),
							  _ex_intern_appl2_env(env,INTERN_NAT_POWER,
							      _ex_intern_small_integer(2),
								  _ex_intern_small_integer(return_type))),
						  cond);
				break;
			case INTERN_BITCONST:
				//printf("bitconst\n");
                n = 0 ;
				acc = zero;
                while (*p != ')' && *p != '}' && *p) {
                    cond = parse_exp(env, TYPE_INTEGER) ;
    				//if (has_nplus_in_ite(cond)) exit(1);
					if (cond==NULL) {
						printf("bitconst bad 1\n");
						return NULL;
					}
					if (cond->type != EXP_INTEGER) {
						printf("bitconst bad 2\n");
						return NULL;
					}
     				if (cond->u.integer[0] != 1 ||
						(cond->u.integer[1] != 0 && cond->u.integer[1] != 1)) {
						printf("bitconst bad 3\n");
						return NULL;
					}
					acc = _th_big_copy(PARSE_SPACE,_th_big_multiply(acc,two));
					acc = _th_big_copy(PARSE_SPACE,_th_big_add(acc,cond->u.integer));
                    skip_white_space() ;
					++n;
				}
				exp = _ex_intern_integer(acc);
				return_type = n;
				break;
			case INTERN_NC_AND:
				//printf("nc_and\n");
                n = 0 ;
                while (*p != ')' && *p != '}' && *p) {
					if (n==MAX_ARGS) {
						printf("and bad 1\n");
						return NULL;
					}
                    cond = parse_exp(env, TYPE_BOOL) ;
    				//if (has_nplus_in_ite(cond)) exit(1);
					if (cond==NULL) {
						printf("and bad 2\n");
						return NULL;
					}
					if (return_type > 0 || return_type==TYPE_INTEGER) {
						cond = _ex_intern_appl1_env(env,INTERN_NOT,
							       _ex_intern_appl2_env(env,INTERN_EQUAL,cond,_ex_intern_small_integer(0)));
					}
                    args[n++] = cond ;
                    skip_white_space() ;
				}
                exp = _th_flatten_top(env,_ex_intern_appl_env(env,INTERN_AND,n,args)) ;
				return_type = TYPE_BOOL;
				break;
			case INTERN_NC_OR:
				//printf("nc_or\n");
                n = 0 ;
                while (*p != ')' && *p != '}' && *p) {
					if (n==MAX_ARGS) {
						printf("or bad 1\n");
						return NULL;
					}
                    cond = parse_exp(env, TYPE_BOOL) ;
    				//if (has_nplus_in_ite(cond)) exit(1);
					if (cond==NULL) {
						printf("or bad 2\n");
						return NULL;
					}
					if (return_type > 0 || return_type==TYPE_INTEGER) {
						cond = _ex_intern_appl1_env(env,INTERN_NOT,
							       _ex_intern_appl2_env(env,INTERN_EQUAL,cond,_ex_intern_small_integer(0)));
					}
                    args[n++] = cond ;
                    skip_white_space() ;
				}
                exp = _th_flatten_top(env,_ex_intern_appl_env(env,INTERN_OR,n,args)) ;
				return_type = TYPE_BOOL;
				break;
			case INTERN_NOT:
				//printf("not\n");
                cond = parse_exp(env, TYPE_BOOL) ;
    			//if (has_nplus_in_ite(cond)) exit(1);
				if (cond==NULL) {
					printf("not bad 1\n");
					return NULL;
				}
				if (return_type > 0 || return_type==TYPE_INTEGER) {
					cond = _ex_intern_appl1_env(env,INTERN_NOT,
							   _ex_intern_appl2_env(env,INTERN_EQUAL,cond,_ex_intern_small_integer(0)));
				}
                skip_white_space() ;
                exp = _ex_intern_appl1_env(env,INTERN_NOT,cond) ;
				return_type = TYPE_BOOL;
				break;
			case INTERN_ORIENTED_RULE:
			case INTERN_DOUBLE_ARROW:
				//printf("oriented_rule\n");
                cond = parse_exp(env, TYPE_BOOL) ;
    			//if (has_nplus_in_ite(cond)) exit(1);
				if (cond==NULL) {
					printf("arrow bad 1\n");
					return NULL;
				}
				if (return_type > 0 || return_type==TYPE_INTEGER) {
					cond = _ex_intern_appl1_env(env,INTERN_NOT,
							   _ex_intern_appl2_env(env,INTERN_EQUAL,cond,_ex_intern_small_integer(0)));
				}
                skip_white_space() ;
                exp = parse_exp(env, TYPE_BOOL) ;
    			//if (has_nplus_in_ite(cond)) exit(1);
				if (exp==NULL) {
					printf("arrow bad 2\n");
					return NULL;
				}
				if (return_type > 0 || return_type==TYPE_INTEGER) {
					exp = _ex_intern_appl1_env(env,INTERN_NOT,
							   _ex_intern_appl2_env(env,INTERN_EQUAL,exp,_ex_intern_small_integer(0)));
				}
                skip_white_space() ;
                exp = _th_flatten_top(env,_ex_intern_appl2_env(env,INTERN_OR,_ex_intern_appl1_env(env,INTERN_NOT,cond),exp));
				return_type = TYPE_BOOL;
				break;
			case INTERN_UNORIENTED_RULE:
				//printf("unoriented_rule\n");
                cond = parse_exp(env, TYPE_ANY) ;
    			//if (has_nplus_in_ite(cond)) exit(1);
				if (cond==NULL) {
					printf("equal bad 1\n");
					return NULL;
				}
                n2 = return_type;
                skip_white_space() ;
                exp = parse_exp(env, TYPE_ANY) ;
    		    //if (has_nplus_in_ite(exp)) exit(1);
				if (exp==NULL) {
					printf("equal bad 2\n");
					return NULL;
				}
				if ((return_type > 0 || return_type==TYPE_INTEGER) &&
					n2==TYPE_BOOL) {
					exp = _ex_intern_appl1_env(env,INTERN_NOT,
							   _ex_intern_appl2_env(env,INTERN_EQUAL,exp,_ex_intern_small_integer(0)));
				}
				if ((n2 > 0 || n2==TYPE_INTEGER) && return_type==TYPE_BOOL) {
					cond = _ex_intern_appl1_env(env,INTERN_NOT,
							   _ex_intern_appl2_env(env,INTERN_EQUAL,cond,_ex_intern_small_integer(0)));
				}
                skip_white_space() ;
				//if (cond->type==EXP_APPL && exp->type==EXP_APPL) {
				//	if ((cond->u.appl.functor==INTERN_NOT && exp->u.appl.functor==INTERN_NAT_PLUS) ||
				//		(exp->u.appl.functor==INTERN_NOT && cond->u.appl.functor==INTERN_NAT_PLUS)) {
				//		printf("Error 1: %d %d\n", return_type, n2);
				//		exit(1);
				//	}
				//}
                exp = _ex_intern_appl2_env(env,INTERN_EQUAL,cond,exp) ;
				return_type = TYPE_BOOL;
				break;
			case INTERN_ITE:
				//printf("ite\n");
				//printf("Here d\n");
				//fflush(stdout);
                cond = parse_exp(env, TYPE_BOOL) ;
    			//if (has_nplus_in_ite(cond)) exit(1);
				//printf("Here e\n");
				//fflush(stdout);
				if (cond==NULL) {
					printf("ite bad 1\n");
					return NULL;
				}
				//if (cond->type==EXP_APPL && (cond->u.appl.functor==INTERN_NAT_PLUS || cond->u.appl.functor==INTERN_NAT_TIMES) &&
				//	return_type != TYPE_INTEGER && return_type <= 0) {
				//	printf("ERROR %s\n", _th_print_exp(cond));
				//	exit(1);
				//}
				if (return_type > 0 || return_type==TYPE_INTEGER) {
					cond = _ex_intern_appl1_env(env,INTERN_NOT,
							   _ex_intern_appl2_env(env,INTERN_EQUAL,cond,_ex_intern_small_integer(0)));
				}
                skip_white_space() ;
                exp = parse_exp(env, TYPE_ANY) ;
    			//if (has_nplus_in_ite(exp)) exit(1);
				if (exp==NULL) {
					printf("ite bad 2 (cond = %s)\n", _th_print_exp(cond));
					return NULL;
				}
                n2 = return_type;
				//printf("n2 = %d\n", n2);
				skip_white_space() ;
                exp2 = parse_exp(env, TYPE_ANY) ;
    			//if (has_nplus_in_ite(exp2)) exit(1);
				if (exp2==NULL) {
					printf("ite bad 3\n");
					return NULL;
				}
                skip_white_space() ;
				//printf("return_type, n2 = %d %d\n", return_type, n2);
				//printf("orig cond = %s\n", _th_print_exp(cond));
				//printf("orig exp = %s\n", _th_print_exp(exp));
				//printf("orig exp2 = %s\n", _th_print_exp(exp2));
                if (n2==TYPE_BOOL && (return_type==TYPE_INTEGER || return_type > 0)) {
					//printf("exp = %s\n", _th_print_exp(exp));
					//printf("exp2 = %s\n", _th_print_exp(exp2));
					exp = _ex_intern_appl3_env(env,INTERN_ITE,exp,_ex_intern_small_integer(1),_ex_intern_small_integer(0));
					//if (exp->u.appl.args[0]->type==EXP_INTEGER) {
					//	fprintf(stderr, "Fail 4\n");
					//	exit(1);
					//}
					n2 = 1;
				} else if (return_type==TYPE_BOOL && (n2==TYPE_INTEGER || n2 > 0)) {
					exp2 = _ex_intern_appl3_env(env,INTERN_ITE,exp2,_ex_intern_small_integer(1),_ex_intern_small_integer(0));
					//if (exp2->u.appl.args[0]->type==EXP_INTEGER) {
					//	fprintf(stderr, "Fail 5\n");
					//	exit(1);
					//}
					return_type = 1;
				}
				if (return_type > 0 && n2 > 0) {
					if (n2 > return_type) return_type = n2;
				} else if ((return_type > 0 && n2==TYPE_INTEGER) || (return_type==TYPE_INTEGER && n2>0)) {
					return_type = TYPE_INTEGER;
				} else if (return_type != 0 && n2 != 0 && return_type != n2) {
					fprintf(stderr, "Type mismatch\n");
					exit(1);
				}
				//printf("cond = %s\n", _th_print_exp(cond));
				//printf("exp = %s\n", _th_print_exp(exp));
				//printf("exp2 = %s\n", _th_print_exp(exp2));
				exp = _ex_intern_appl3_env(env, INTERN_ITE, cond, exp, exp2);
			    //if (exp->u.appl.args[0]->type==EXP_INTEGER) {
				//	fprintf(stderr, "Fail 6\n");
				//	exit(1);
				//}
				break;
			case INTERN_PLUS:
				id = INTERN_NAT_PLUS;
				goto cont;
			case INTERN_MINUS:
				id = INTERN_NAT_MINUS;
				goto cont;
			case INTERN_SLASH:
				id = INTERN_NAT_DIVIDE;
				goto cont;
			case INTERN_STAR:
				id = INTERN_NAT_TIMES;
				goto cont;
            case INTERN_GREATER:
                skip_white_space();
                cond = parse_exp(env, TYPE_ANY) ;
                skip_white_space();
                //if (has_nplus_in_ite(cond)) exit(1);
                if (cond==NULL) {
                    printf("greater bad 1\n");
                    return NULL;
                }
                exp = parse_exp(env, TYPE_ANY) ;
                //if (has_nplus_in_ite(cond)) exit(1);
                if (exp==NULL) {
                    printf("greater bad 2\n");
                    return NULL;
                }
                exp = _ex_intern_appl2_env(env,INTERN_NAT_LESS,exp,cond);
                return_type = TYPE_BOOL;
                skip_white_space();
                break;
            case INTERN_GREATER_EQUAL:
                skip_white_space();
                cond = parse_exp(env, TYPE_ANY) ;
                skip_white_space();
                //if (has_nplus_in_ite(cond)) exit(1);
                if (cond==NULL) {
                    printf("greater bad 1\n");
                    return NULL;
                }
                exp = parse_exp(env, TYPE_ANY) ;
                //if (has_nplus_in_ite(cond)) exit(1);
                if (exp==NULL) {
                    printf("greater bad 2\n");
                    return NULL;
                }
                exp = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_NAT_LESS,cond,exp));
                return_type = TYPE_BOOL;
                skip_white_space();
                break;
            case INTERN_SLASH_EQUAL:
                skip_white_space();
                cond = parse_exp(env, TYPE_ANY) ;
                skip_white_space();
                //if (has_nplus_in_ite(cond)) exit(1);
                if (cond==NULL) {
                    printf("greater bad 1\n");
                    return NULL;
                }
                exp = parse_exp(env, TYPE_ANY) ;
                //if (has_nplus_in_ite(cond)) exit(1);
                if (exp==NULL) {
                    printf("greater bad 2\n");
                    return NULL;
                }
                exp = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl2_env(env,INTERN_EQUAL,cond,exp));
                return_type = TYPE_BOOL;
                skip_white_space();
                break;
			case INTERN_LESS:
				id = INTERN_NAT_LESS;
				goto cont;
			case INTERN_BICONDITIONAL:
				id = INTERN_EQUAL;
                args[0] = parse_exp(env, TYPE_BOOL);
                if (args[0]==NULL) {
                    printf("biconditional bad 1\n");
                    return NULL;
                }
                skip_white_space();
                args[1] = parse_exp(env, TYPE_BOOL);
                if (args[1]==NULL) {
                    printf("biconditional bad 1\n");
                    return NULL;
                }
                skip_white_space();
                return_type = TYPE_BOOL;
                exp = _ex_intern_appl2_env(env,INTERN_EQUAL,args[0],args[1]);
                break;
			case INTERN_LESS_EQUAL:
				//printf("less_equal\n");
				args[1] = parse_exp(env, TYPE_ANY);
    			//if (has_nplus_in_ite(args[1])) exit(1);
				if (args[1]==NULL) {
					printf("le bad 1\n");
					return NULL;
				}
				skip_white_space();
				args[0] = parse_exp(env, TYPE_ANY);
    			//if (has_nplus_in_ite(args[0])) exit(1);
				if (args[0]==NULL) {
					printf("le bad 2\n");
					return NULL;
				}
				skip_white_space();
				exp = _ex_intern_appl1_env(env,INTERN_NOT,_ex_intern_appl_env(env,INTERN_NAT_LESS,2,args));
				return_type = TYPE_BOOL;
				break;
			case INTERN_READ:
			case INTERN_WRITE:
			default:
cont:
				//printf("default %d\n", id);
                n = 0 ;
                while (*p != ')' && *p != '}' && *p) {
					if (n==MAX_ARGS) {
						printf("rw bad 1\n");
						return NULL;
					}
                    //printf("Parsing before '%s'\n", p);
					//printf("Parsing term\n");
                    cond = parse_exp(env, TYPE_ANY) ;
    				//if (has_nplus_in_ite(cond)) exit(1);
					if (cond==NULL) {
						printf("rw bad 2\n");
						return NULL;
					}
                    args[n++] = cond ;
                    skip_white_space() ;
				}
                if (n==0) {
                    char *c = _th_intern_decode(id);
                    if (isdigit(*c)) {
                        exp = _ex_intern_small_integer(atoi(c));
                        return_type = TYPE_INTEGER;
                    } else {
                        exp = _ex_intern_var(id);
        				return_type = TYPE_ANY;
                    }
                } else {
                    exp = _th_flatten_top(env,_ex_intern_appl_env(env,id,n,args)) ;
    				return_type = TYPE_ANY;
                }
				//printf("Parsed %s\n", _th_print_exp(exp));
				//printf("Rest: %s\n", p);
		}
		skip_white_space();
		if (*p != ')' && *p != '}') {
			printf("generally bad 1\n");
			return NULL;
		}
		++p;
		//printf("Returning %s %d %s\n", _th_print_exp(exp), return_type, _th_intern_decode(id));
		return exp;
	} else if (*p=='[') {
		++p;
next_id:
		skip_white_space();
        id = read_identifier(0);
		//printf("id 1 = %d %s\n", id, _th_intern_decode(id));
		switch (id) {
		    case INTERN_ARRAY:
				skip_white_space();
				id = read_identifier(0);
				//printf("id 2 = %d %s\n", id, _th_intern_decode(id));
				if (id != INTERN_UNKNOWN) {
					printf("array bad 1\n");
					return NULL;
				}
				goto next_id;
		    case INTERN_BITVEC:
				skip_white_space();
				if (!isdigit(*p)) {
					printf("bitvec bad 1\n");
					return NULL;
				}
				n = 0;
				while (isdigit(*p)) {
					n = n * 10 + *p - '0';
					++p;
				}
				//printf("*** Parsing bitvec %d\n", n);
				skip_white_space();
				//printf("n = %d\n", n);
				goto common;
			case INTERN_BARRAY:
				skip_white_space();
				if (!isdigit(*p)) {
					printf("barray bad 1\n");
					return NULL;
				}
				n = 0;
				while (isdigit(*p)) {
					n = n * 10 + *p - '0';
					++p;
				}
				//printf("*** Parsing bit array %d\n", n);
				skip_white_space();
				if (read_identifier(0) != INTERN_BIT) {
					printf("barray bad 2\n");
					return NULL;
				}
				skip_white_space();
				//printf("Here2\n");
				//if (*p != ']') return NULL;
				//++p;
common:
				if (*p=='$') {
                    n2 = read_identifier(1);
                    //printf("id = %s\n", _th_intern_decode(n2));
            		hash = (int)(n2%HASH_SIZE);
		            term = term_table[hash];
                    //printf("hash, term = %d %x\n", hash, term);
		            while (term != NULL) {
			            if (term->number==(unsigned)n2) break;
						term = term->next;
					}
					if (*p==':') {
						++p;
						id = read_identifier(0);
             			term = (struct term_hash *)_th_alloc(PARSE_SPACE,sizeof(struct term_hash));
			            term->next = term_table[hash];
			            term_table[hash] = term;
			            term->term = _ex_intern_var(id);
			            term->number = n2;
			            term->type = n;
					} else if (*p!=' ' && term != NULL) {
			            return_type = term->type;
						id = term->term->u.var;
					} else {
						printf("common bad 1\n");
						return NULL;
					}
				} else {
				    id = read_identifier(0);
				}
				//printf("id 2 = %d %s\n", id, _th_intern_decode(id));
				if (id==0) {
					printf("common bad 2\n");
					return NULL;
				}
				//printf("Here\n");
				hash = (int)(id%HASH_SIZE);
				type = type_table[hash];
				while (type) {
					//printf("type = %x\n", type);
					//fflush(stdout);
					//printf("type id %s\n", _th_intern_decode(type->var));
					//printf("type %d\n", type->type);\
					//fflush(stdout);
					if (type->var==id && type->type != n) {
						printf("common bad 3\n");
						return NULL;
					}
					if (type->var==id) break;
					type = type->next;
				}
				if (type==NULL) {
				    type = (struct type_hash *)_th_alloc(PARSE_SPACE,sizeof(struct type_hash));
				    if (n==TYPE_BOOL) {
					    _th_set_var_type(env,id,_th_parse(env,"(Bool)"));
					} else if (n==TYPE_REAL) {
					    _th_set_var_type(env,id,_th_parse(env,"(Real)"));
					} else {
				        _th_set_var_type(env,id,_th_parse(env,"(Int)"));
					}
				    if (n > 0) {
					    struct _ex_intern *l = _ex_intern_appl2_env(env,INTERN_NAT_LESS,_ex_intern_small_integer(-1),_ex_intern_var(id));
					    struct _ex_intern *h = _ex_intern_appl2_env(env,INTERN_NAT_LESS,
						                           _ex_intern_var(id),
							    				   _ex_intern_appl2_env(env,INTERN_NAT_POWER,_ex_intern_small_integer(2),_ex_intern_small_integer(n)));
						l = _th_nc_rewrite(env,l);
					    h = _th_nc_rewrite(env,h);
					    _th_derive_add_prepared(env,_th_derive_prepare(env,l));
					    _th_derive_add_prepared(env,_th_derive_prepare(env,h));
					}
				}
				type->next = type_table[hash];
				type_table[hash] = type;
				type->type = n;
				type->var = id;
				return_type = n;
         		skip_white_space();
				//printf("p = %s\n", p);
				if (*p != ']') {
					printf("common bad 4\n");
					return NULL;
				}
				++p;
				//printf("var %s %d\n", _th_intern_decode(id), return_type);
				return _ex_intern_var(id);
			default:
				printf("default bad\n");
				return NULL;
		}
	} else if (*p=='$') {
		n = read_identifier(1);
        //printf("id2 = %s\n", _th_intern_decode(n));
        //printf("Identifier %s\n", _th_intern_decode(n));
		//printf("Here b %s\n", p);
		//if (id==INTERN_LTRUE) {
		//	return_type = TYPE_BOOL;
		//	return _ex_true;
		//} else if (id==INTERN_LFALSE) {
		//	return_type = TYPE_BOOL;
		//	return _ex_false;
		//}
		hash = (int)(n%HASH_SIZE);
		term = term_table[hash];
        //printf("hash, term = %d %x\n", hash, term);
		while (term != NULL) {
			if (term->number==(unsigned)n) break;
			term = term->next;
		}
		//printf("term = %d\n", term);
		if (*p==':' && term==NULL) {
			char *q = p;
			++p;
			exp = parse_exp(env, expected_type);
			//if (has_nplus_in_ite(exp)) {
			//	printf("String: %s\n", q);
			//	term = term_table[146%HASH_SIZE];
			//	while (term != NULL) {
			//		if (term->number==146) break;
			//		term = term->next;
			//	}
			//	printf("exp = %s\n", _th_print_exp(exp));
			//	printf("term = %s\n", _th_print_exp(term->term));
			//	printf("type = %d\n", term->type);
			//	printf("expected_type = %d\n", expected_type);
			//	fflush(stdout);
			//	exit(1);
			//}
			if (exp==NULL) {
				printf("$ bad 1\n");
				return NULL;
			}
			term = (struct term_hash *)_th_alloc(PARSE_SPACE,sizeof(struct term_hash));
			term->next = term_table[hash];
			term_table[hash] = term;
			term->term = exp;
			term->number = n;
			term->type = return_type;
			//printf("cached exp %s %d\n", _th_print_exp(exp), term->type);
			return exp;
		} else if (*p!=':' && term != NULL) {
			//printf("Here now %d %d\n", term->term, term->type);
			return_type = term->type;
            //printf("Returning %s\n", _th_print_exp(term->term));
			return term->term;
		} else {
			printf("$ bad 2\n");
			return NULL;
		}
	} else if (isdigit(*p) || *p=='-') { /* Number */
		unsigned *value, multiplier[2] = { 1, 1 } ;
		//printf("Parsing number\n");
		if (*p=='-') {
			multiplier[1] = -1 ;
			++p ;
		} else {
			multiplier[1] = 1 ;
		}
		value = _th_parse_number(p) ;
		while (isdigit(*p)) {
			++p;
		}
		//printf("After p %s\n", p);
		if (value==NULL) {
			printf("value bad 1\n");
			return 0 ;
		}
		if (multiplier[1] != 1) value = _th_big_multiply(multiplier, value) ;
		return_type = TYPE_INTEGER;
		//printf("Integer %s\n", _th_print_exp(_ex_intern_integer(value)));
		return _ex_intern_integer(value) ;
	} else if (is_letter(*p)) { /* Variable */
		var = read_identifier(0) ;
		if (var==INTERN_LTRUE) {
			return_type = TYPE_BOOL;
			return _ex_true;
		}
		if (var==INTERN_LFALSE) {
			return_type = TYPE_BOOL;
			return _ex_false;
		}
		if (var==0) {
			printf("id bad 1\n");
			return 0 ;
		}
		hash = (int)(var%HASH_SIZE);
		type = type_table[hash];
		while (type) {
			if (type->var==var) break;
			type = type->next;
		}
		//printf("expected type = %d\n", expected_type);
		//printf("type = %x\n", type);
		if (type==NULL) {
			if (expected_type==TYPE_BOOL) {
				_th_set_var_type(env,var,_th_parse(env,"(Bool)"));
			} else if (expected_type==TYPE_REAL) {
				_th_set_var_type(env,var,_th_parse(env,"(Real)"));
			} else {
				_th_set_var_type(env,var,_th_parse(env,"(Int)"));
			}
			type = (struct type_hash *)_th_alloc(PARSE_SPACE,sizeof(struct type_hash));
			type->next = type_table[hash];
			type_table[hash] = type;
			type->var = var;
			type->type = expected_type;
			//printf("New var\n");
		}
		//printf("type->type = %d\n", type->type);
		if (expected_type != type->type) {
			if (expected_type==TYPE_INTEGER && type->type==TYPE_REAL) {
				type->type = TYPE_INTEGER;
			} else if ((expected_type != TYPE_REAL || type->type != TYPE_INTEGER) &&
				       (expected_type != TYPE_INTEGER || type->type <= 0) &&
				       expected_type != TYPE_ANY) {
				printf("id bad 2 %d %d %s\n", expected_type, type->type, _th_intern_decode(var));
				return NULL;
			}
		}
		return_type = type->type;
		return _ex_intern_var(var) ;
	} else { /* Illegal character */
		printf("Bad\n");
		return 0 ;
	}
}

struct _ex_intern *_th_svc_parse(struct env *env,char *s)
{
    char *mark ;
    struct _ex_intern *e ;
    int i;

	for (i = 0; i < HASH_SIZE; ++i) {
		term_table[i] = NULL;
		type_table[i] = NULL;
	}

    p = s ;

    mark = _th_alloc_mark(PARSE_SPACE) ;

    e = parse_exp(env, TYPE_BOOL) ;

    _th_alloc_release(PARSE_SPACE, mark) ;

	//if (has_nplus_in_ite(e)) exit(1);

    return e ;
}

#define MAX_FILE 10000000

struct _ex_intern *_th_process_svc_file(struct env *env, char *name)
{
	char line[MAX_FILE+1];
    char *l, *c;
	int paren_count;
    char *mark ;
    struct _ex_intern *e, *ret = NULL;
    int i;
    FILE *file;

	for (i = 0; i < HASH_SIZE; ++i) {
		term_table[i] = NULL;
		type_table[i] = NULL;
	}

    mark = _th_alloc_mark(PARSE_SPACE) ;

	file = fopen(name, "r");
	if (file==NULL) return NULL;

	while (!feof(file)) {
		l = line;
		paren_count = 0;
		do {
			do {
				l[0] = 0;
				fgets(l, MAX_FILE-(l-line), file);
                c = l;
				while (*c) ++c;
				--c;
				while (c >= l && (*c == ' ' || *c == '\n')) {
					*c = 0;
					--c;
				}
			} while ((l[0]==';' || l[0]==0) && !feof(file));
			c = l;
			while (*c) {
				if (*c=='(' || *c=='[' || *c=='{') ++paren_count;
				if (*c==')' || *c==']' || *c=='}') --paren_count;
				if (*c=='\n') *c = ' ';
				++c;
			}
			*c = ' ';
			++c;
			*c = 0;
            l = c;
		} while (!feof(file) && paren_count > 0);

        //printf("Total line: %s\n", line);

		p = line;
		e = parse_exp(env, TYPE_BOOL);
    	//if (has_nplus_in_ite(e)) exit(1);
		//printf("e = %s\n", _th_print_exp(e));
        if (e) ret = e;

		line[0] = 0;
		if (feof(file)) break;
	}

	_th_alloc_release(PARSE_SPACE, mark);

	return ret;
}

struct _ex_intern *_th_process_svc_script(struct env *env, char *name)
{
    char line[MAX_FILE+1];
    char *c;
    char *mark ;
    struct _ex_intern *e, *ret = NULL;
    int i;
    FILE *file;
    unsigned id;
    int hash;
    struct term_hash *term;
    int paren_count;
    char *l;

    for (i = 0; i < HASH_SIZE; ++i) {
        term_table[i] = NULL;
        type_table[i] = NULL;
    }
    
    mark = _th_alloc_mark(PARSE_SPACE) ;
    
    file = fopen(name, "r");
    if (file==NULL) return NULL;
    
    ret = NULL;

    while (!feof(file)) {
        int count = 0;
        paren_count = 0;
        l = line;
        do {
            l[0] = 0;
            fgets(l, MAX_FILE-(l-line), file);
            //printf("line, paren_count, count = %d %d %d\n", strlen(line), paren_count, count++);
            c = line;
            while (*c) ++c;
            --c;
            while (c >= line && (*c == ' ' || *c == '\n')) {
                *c = 0;
                --c;
            }
            while (*l) {
                switch (*l) {
                    case '(':
                        ++paren_count;
                        break;
                    case ')':
                        --paren_count;
                        break;
                    case '\n':
                        *l = ' ';
                        break;
                }
                ++l;
            }
        } while (paren_count > 0);

        //printf("Total line: %s\n", line);
        
        if (line[0] != ';') {
            if (!strncmp(line,"set",3)) {
                p = line+3;
                skip_white_space();
                //printf("********************************************************\n");
                id = read_identifier(1);
                //printf("id = %s\n", _th_intern_decode(id));
                skip_white_space();
                //printf("p = %s\n", p);
                e = parse_exp(env, TYPE_ANY);
                //printf("exp = %s\n", _th_print_exp(e));
                if (e==NULL) {
                    printf("Bad exp\n");
                    _th_alloc_release(PARSE_SPACE, mark);
                    return NULL;
                }
         		hash = (int)(id%HASH_SIZE);
		        term = (struct term_hash *)_th_alloc(PARSE_SPACE,sizeof(struct term_hash));
                //printf("hash, term = %d %x\n", hash, term);
                term->next = term_table[hash];
                term_table[hash] = term;
                term->number = id;
                term->term = e;
                term->type = return_type;
            } else if (!strncmp(line,"check_valid",11)) {
                p = line+11;
                skip_white_space();
                //fprintf(stderr,"Starting parse\n");
                //fflush(stderr);
                ret = parse_exp(env, TYPE_BOOL);
                //fprintf(stderr,"Finishing parse\n");
                //fflush(stderr);
                //printf("ret = %s\n", _th_print_exp(ret));
                return ret;
            }
        }
        line[0] = 0;
        if (feof(file)) break;
    }
    
    _th_alloc_release(PARSE_SPACE, mark);
    
    return ret;
}

