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

#include "Globals.h"
#include "Intern.h"

static char *p ;

static void skip_white_space()
{
    while (*p == ' ' || *p=='\t' || *p== '\n') ++p ;
}

#define MAX_IDENTIFIER 80

int my_isspecial(char c)
{
    return c=='!' || c=='@' || c=='#' || c=='$' || c=='%' || c=='^'|| c=='&' ||
           c=='*' || c=='~' || c=='`' || c=='\'' || c=='\\' || c=='|' ||
           c==',' || c=='.' || c=='<' || c=='>' || c=='?' || c=='/' || c==':' ||
           c==';' || c=='=' || c=='+' || c=='-' || c=='_' ;
}

static unsigned read_identifier()
/*
 * Parse an identifier and return the interned value
 */
{
    char identifier[MAX_IDENTIFIER+1] ;
    int x = 0 ;

    if (my_isspecial(*p)) {
        identifier[x++] = *p++ ;
        while (my_isspecial(*p)) {
            if (x >= MAX_IDENTIFIER) {
                return 0 ;
            }
            identifier[x++] = *p++ ;
        }
        identifier[x++] = 0 ;
        return _th_intern(identifier) ;
    } else if (isalpha(*p)) {
        identifier[x++] = *p++ ;
    } else {
        return 0 ;
    }
    while (isalnum(*p)||*p=='_'||*p=='!') {
        if (x >= MAX_IDENTIFIER) {
            return 0 ;
        }
        identifier[x++] = *p++ ;
    }
    identifier[x++] = 0 ;

    return _th_intern(identifier) ;
}

unsigned *_th_parse_number(char *ptr)
{
    unsigned *num ;
    unsigned zero[2] = { 1, 0 } ;
    unsigned ten[2] = { 1, 10 } ;
    unsigned digit[2] = { 1, 0 } ;
    //extern int bignum_print;

    if (!isdigit(*ptr)) return NULL ;

	//bignum_print = 0;
	num = zero ;
    while(isdigit(*ptr)) {
        num = _th_big_copy(PARSE_SPACE, _th_big_multiply(num,ten)) ;
        digit[1] = *ptr - '0' ;
        num = _th_big_copy(PARSE_SPACE, _th_big_add(num,digit)) ;
        ++ptr ;
    }
	p = ptr ;
	//bignum_print = 1;
    return num ;
}

#define MAX_STRING 255

#define ARG_INCREMENT 4000

static struct _ex_intern **args, **all_args ;
static unsigned arg_size, arg_start ;

void _th_parse_init()
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

//FILE *output;

#define MAX_VARS 200

static struct _ex_intern *parse_exp(struct env *env)
{
    struct _ex_intern *exp, *cond ;
    static char string[MAX_STRING] ;
    unsigned vars[MAX_VARS] ;
    int n ;
    unsigned var, id ;

    skip_white_space() ;

    //fprintf(output, "Parsing '%s'\n", p);
    //fflush(output);

    if (*p!='(') {
        if (isdigit(*p) || *p=='-') { /* Number */
            unsigned *value, multiplier[2] = { 1, 1 } ;
            if (*p=='-') {
                multiplier[1] = -1 ;
                ++p ;
            } else {
                multiplier[1] = 1 ;
            }
            value = _th_parse_number(p) ;
            if (value==NULL) return 0 ;
            if (multiplier[1] != 1) value = _th_big_multiply(multiplier, value) ;
            return _ex_intern_integer(value) ;
        } else if (*p=='#') { /* Rational */
            unsigned multiplier[2] = { 1, 1 }, *numerator, *denominator ;
            ++p ;
            if (*p=='-') {
                multiplier[1] = -1 ;
                ++p ;
            } else {
                multiplier[1] = 1 ;
            }
            numerator = _th_parse_number (p) ;
            if (numerator==NULL) return NULL ;
            if (*p != '/') return NULL ;
            ++p ;
            denominator = _th_parse_number(p) ;
            if (denominator==NULL) return NULL ;
            if (multiplier[1] != 1) numerator = _th_big_multiply(multiplier, numerator) ;
            return _ex_intern_rational(numerator, denominator) ;
        } else if (isalpha(*p)) { /* Variable or marked var */
            var = read_identifier() ;
            if (var==0) return 0 ;
            if (*p=='\'') {
                ++p ;
                return _ex_intern_marked_var(var,_th_intern_get_quant_level(var)) ;
            } else {
                return _ex_intern_var(var) ;
            }
        } else if (*p=='"') { /* String */
            n = 0 ;
            ++p ;
            while(*p != '"' && *p) {
                if (n>=MAX_STRING) return 0 ;
                if (*p=='\\') {
                    ++p ;
                    switch (*p) {
                        case 0:
                            return 0 ;
                        case 'n':
                            string[n++] = '\n' ;
                            break ;
                        case 't':
                            string[n++] = '\t' ;
                            break ;
                        case 'r':
                            string[n++] = '\r' ;
                            break ;
                        default:
                            string[n++] = *p ;
                    }
                    ++p ;
                } else {
                    string[n++] = *p++ ;
                }
            }
            if (!*p) return 0 ;
            ++p ;
            string[n] = 0 ;
            return _ex_intern_string(string) ;
        } else { /* Illegal character */
            return 0 ;
        }
    }
    ++p ;

    /* Default--either appl, case, quant or index */

    skip_white_space() ;

    id = read_identifier() ;
    if (id==0) return 0 ;
    skip_white_space() ;

    switch(id) {

        case INTERN_ALL:
            if (*p != '(') return 0 ;
            ++p ;
            n = 0 ;
            skip_white_space() ;
            while(*p != ')' && *p && *p!=':') {
                if (n>=MAX_VARS) return 0 ;
                id = vars[n++] = read_identifier() ;
                if (id==0) return 0 ;
                skip_white_space() ;
            }
            cond = _ex_true ;
            if (*p==':') {
                ++p ;
                skip_white_space() ;
                cond = parse_exp(env) ;
                if (cond==0) return 0 ;
                skip_white_space() ;
            }
            if (*p != ')') return 0 ;
			++p ;
            skip_white_space() ;
            if (!*p) return 0 ;
            exp = parse_exp(env) ;
            skip_white_space() ;
            if (*p++!=')') return 0 ;
            return _ex_intern_quant(INTERN_ALL,n,vars,exp,cond) ;

        case INTERN_EXISTS:
            if (*p != '(') return 0 ;
            ++p ;
            n = 0 ;
            skip_white_space() ;
            while(*p != ')' && *p) {
                if (n>=MAX_VARS) return 0 ;
                id = vars[n++] = read_identifier() ;
                if (id==0) return 0 ;
                skip_white_space() ;
            }
            if (*p != ')') return 0 ;
            ++p ;
            skip_white_space() ;
            if (!*p) return 0 ;
            exp = parse_exp(env) ;
            skip_white_space() ;
            if (*p++!=')') return 0 ;
            return _ex_intern_quant(INTERN_EXISTS,n,vars,exp,_ex_true) ;

        case INTERN_LAMBDA:
            skip_white_space() ;
            id = vars[0] = read_identifier() ;
            if (id==0) return 0 ;
            skip_white_space() ;
            if (!*p) return 0 ;
            exp = parse_exp(env) ;
            skip_white_space() ;
            if (*p++!=')') return 0 ;
            return _ex_intern_quant(INTERN_LAMBDA,1,vars,exp,_ex_true) ;

        case INTERN_CAP_SET:
            if (*p != '(') goto def ;
            ++p ;
            n = 0 ;
            skip_white_space() ;
            while(*p != ')' && *p && *p != ':') {
                if (n>=MAX_VARS) return 0 ;
                id = vars[n++] = read_identifier() ;
                if (id==0) return 0 ;
                skip_white_space() ;
            }
            cond = _ex_true ;
            if (*p==':') {
                ++p ;
                skip_white_space() ;
                cond = parse_exp(env) ;
                if (cond==0) return 0 ;
                skip_white_space() ;
            }
            if (*p != ')') return 0 ;
            ++p ;
            skip_white_space() ;
            if (!*p) return 0 ;
            exp = parse_exp(env) ;
            skip_white_space() ;
            if (*p++!=')') return 0 ;
            return _ex_intern_quant(INTERN_SETQ,n,vars,exp,cond) ;

        case INTERN_INDEX:
            exp = parse_exp (env) ;
            if (id==0) return 0 ;
            skip_white_space() ;
            id = read_identifier() ;
            if (id==0) return 0 ;
            skip_white_space() ;
            n = _th_parse_number(p)[1] ;
            if (n < 0) return 0 ;
            skip_white_space() ;
            if (*p++!=')') return 0 ;
            return _ex_intern_index(exp,id,n) ;

        case INTERN_CASE:
            exp = parse_exp(env) ;
            n = 0 ;
            skip_white_space() ;
            while (*p != ')' && *p) {
                check_size(n*2+2) ;
                arg_start += n*2 ;
                set_start() ;
                cond = parse_exp(env) ;
                arg_start -= n*2 ;
                set_start() ;
                args[n*2] = cond ;
                if (cond==0) return 0 ;
                skip_white_space() ;
                arg_start += n*2+1 ;
                set_start() ;
                cond = parse_exp(env) ;
                arg_start -= n*2+1 ;
                set_start() ;
                args[n*2+1] = cond ;
                if (cond==0) return 0 ;
                skip_white_space() ;
                ++n ;
            }
            if (!*p) return 0 ;
            ++p ;
            return _ex_intern_case(exp,n,args) ;

        default:
def:

            n = 0 ;
            while (*p != ')' && *p) {
                check_size(n+1) ;
                arg_start += n+1 ;
                set_start() ;
                //fprintf(output, "Parsing arg %s\n", p);
                //fflush(output);
                cond = parse_exp(env) ;
                arg_start -= n+1 ;
                set_start() ;
                args[n++] = cond ;
                if (cond==0) return 0 ;
                skip_white_space() ;
            }
            if (!*p) return 0 ;
            ++p ;
            if (env==NULL) {
                return _ex_intern_appl(id,n,args) ;
            } else {
				struct _ex_intern *e;
#ifndef FAST
				++_th_block_check;
#endif
				e = _ex_intern_appl_env(env,id,n,args) ;
#ifndef FAST
				--_th_block_check;
#endif
				return e ;
            }
    }
}

struct _ex_intern *_th_parse(struct env *env,char *s)
{
    char *mark ;
    struct _ex_intern *e ;

    //output = fopen("output","w");

    p = s ;

    mark = _th_alloc_mark(PARSE_SPACE) ;

    e = parse_exp(env) ;

    _th_alloc_release(PARSE_SPACE, mark) ;

    return e ;
}

