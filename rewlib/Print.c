/*
 * print.c
 *
 * Print routines for the prover.
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

#define INITIAL_PRINT_SIZE 1000000
char *_th_print_buf ;
static int print_size ;

void _th_print_init()
{
    _th_print_buf = (char *)malloc(INITIAL_PRINT_SIZE) ;
    print_size = INITIAL_PRINT_SIZE ;
}

void _th_print_shutdown()
{
}

int _th_pos = 0 ;

void _th_adjust_buffer(int size)
{
    if (print_size-_th_pos-size <= 0) {
        print_size += size + 1000000 ;
        _th_print_buf = REALLOC(_th_print_buf, print_size) ;
        if (_th_print_buf==NULL) {
            printf("Error in realloc\n") ; 
            exit(1) ;
        }
    }
}

#define print_string(s) \
    { _th_adjust_buffer(strlen(s)) ; \
      strcpy(_th_print_buf+_th_pos,s) ; \
      _th_pos+=strlen(s) ; }

#define print_char(c) \
    { _th_adjust_buffer(1) ; \
      _th_print_buf[_th_pos++] = c ; }

#define print_small_number(n) \
    { _th_adjust_buffer(15) ; \
      sprintf(_th_print_buf+_th_pos,"%d",n) ; \
      _th_pos +=strlen(_th_print_buf+_th_pos) ; }

void _th_print_number(unsigned *n)
{
    unsigned ten[] = { 1, 10 } ;
    unsigned zero[] = { 1, 0 } ;
    unsigned *digit ;
    int start_index ;
    char s ;
    int i ;
    //extern int bignum_print;

    _th_adjust_buffer(*n * 10 + 5) ;
    //printf("orig n = %u %u %u %u\n", n[0], n[1], n[2], n[3]);
    if (_th_big_is_negative(n)) {
        //printf("Complement\n");
        n = _th_big_copy(PARSE_SPACE,_th_big_sub(zero,n)) ;
        _th_print_buf[_th_pos++] = '-' ;
    }
    if (n[0]==1&&n[1]==0) {
        _th_print_buf[_th_pos++] = '0' ;
        return ;
    }
	//bignum_print = 0;
    start_index = _th_pos ;
    i = 0;
    //printf("Print\n");
    while (n[0] != 1 || n[1] != 0) {
        //printf("n = %u %u %u %u\n", n[0], n[1], n[2], n[3]);
        digit = _th_big_mod(n,ten) ;
        if (digit[1] > 9) {
            printf("n[0], n[1], n[2], n[3] = %u %u %u %u\n", n[0], n[1], n[2], n[3]);
            fprintf(stderr, "Illegal digit %d\n", digit[1]);
            exit(1);
        }
        _th_print_buf[_th_pos++] = digit[1] + '0' ;
        n = _th_big_copy(PARSE_SPACE,_th_big_divide(n,ten)) ;
        ++i;
        if (i>=10000) {
            printf("n = %d %d %d %d\n", n[0], n[1], n[2], n[3]);
            exit(1);
        }
    }
    for (i = (start_index + _th_pos + 1) / 2; i < _th_pos; ++i) {
        s = _th_print_buf[i] ;
        _th_print_buf[i] = _th_print_buf[start_index + _th_pos - i - 1] ;
        _th_print_buf[start_index + _th_pos - i - 1] = s ;
    }
	//bignum_print = 1;
}

static void _print_vars(struct _ex_intern *e)
{
    int i ;

    for (i = 0; i < e->u.quant.var_count; ++i) {
        char *sym ;
        sym = _th_intern_decode(e->u.quant.vars[i]) ;
        print_string(sym) ;
        if (i < e->u.quant.var_count-1) print_char(' ') ;
    }

}

static unsigned print_line = 0;
static struct _ex_intern *print_next;

static int depth = 0;

#define MAX_DEPTH 10

static void indent_line(int d)
{
    while (d) {
        print_char(' ');
        --d;
    }
}

static int height(struct _ex_intern *e)
{
    int i;
    int mh, nh;

    switch (e->type) {
        case EXP_APPL:
            mh = 1;
            for (i = 0; i < e->u.appl.count; ++i) {
                nh = height(e->u.appl.args[i]);
                if (mh > nh+1) mh = nh+1;
            }
            return mh;
        case EXP_QUANT:
            mh = height(e->u.quant.exp);
            nh = height(e->u.quant.cond);
            if (mh > nh) {
                return mh+1;
            } else {
                return nh+1;
            }
        default:
            return 1;
    }
}

static void _print_exp(struct _ex_intern *e)
{
    char *p ;
    char *sym ;
    int i ;
    //int h = height(e);

    ++depth;
    //if (depth==MAX_DEPTH) {
    //    print_string("<...>");
    //    --depth;
    //    return;
    //}

	if (print_line) {
		if (e->print_line) {
			char s[50];
			sprintf(s, "$%d", e->print_line);
			print_string(s);
            if (_th_has_complex_term(e,5)) {
                --depth;
			    return;
            } else {
                print_char(':');
            }
		} else {
			char s[50];
			e->print_line = print_line;
            e->print_next = print_next;
            print_next = e;
            ++print_line;
			sprintf(s, "$%d:", e->print_line, e);
			print_string(s);
		}
	}

    if (e==NULL) {
		_th_adjust_buffer(10);
        print_string("<NULL>");
        --depth;
		return;
	}
	if (((int)e) < 100) {
		_th_adjust_buffer(30);
		print_string("<Illegal #");
		print_small_number(((int)e));
		print_string(">");
        --depth;
		return;
	}

    switch (e->type) {

        case EXP_INTEGER:
            _th_print_number(e->u.integer) ;
            break ;

        case EXP_RATIONAL:
            _th_adjust_buffer(30) ;
            _th_print_buf[_th_pos++]='#' ;
            _th_print_number(e->u.rational.numerator) ;
            _th_print_buf[_th_pos++]='/' ;
            _th_print_number(e->u.rational.denominator) ;
            break ;

        case EXP_STRING:
            p = e->u.string ;
            _th_adjust_buffer(2+strlen(p)*2) ;
            _th_print_buf[_th_pos++] = '"' ;
            while(*p) {
                switch (*p) {
                    case '"':
                        _th_print_buf[_th_pos++] = '\\' ;
                        _th_print_buf[_th_pos++] = '"' ;
                        break ;
                    case '\\':
                        _th_print_buf[_th_pos++] = '\\' ;
                        _th_print_buf[_th_pos++] = '\\' ;
                        break ;
                    case '\n':
                        _th_print_buf[_th_pos++] = '\\' ;
                        _th_print_buf[_th_pos++] = 'n' ;
                        break ;
                    case '\r':
                        _th_print_buf[_th_pos++] = '\\' ;
                        _th_print_buf[_th_pos++] = 'r' ;
                        break ;
                    case '\t':
                        _th_print_buf[_th_pos++] = '\\' ;
                        _th_print_buf[_th_pos++] = 't' ;
                        break ;
                    default:
                        _th_print_buf[_th_pos++] = *p ;
                }
                ++p ;
            }
            _th_print_buf[_th_pos++] = '"' ;
            break ;

        case EXP_VAR:
            sym = _th_intern_decode(e->u.var) ;
            print_string(sym) ;
            break ;

        case EXP_MARKED_VAR:
            sym = _th_intern_decode(e->u.marked_var.var) ;
            print_string(sym) ;
            print_char('\'') ;
            if (e->u.marked_var.quant_level != 0) {
                print_small_number(e->u.marked_var.quant_level) ;
                print_char('\'') ;
            }
            break ;

        case EXP_APPL:
            sym = _th_intern_decode(e->u.appl.functor) ;
            print_char('(') ;
            print_string(sym) ;
            if (e->type_inst) {
                print_char('{');
                _print_exp(e->type_inst);
                print_char('}');
            }
            for (i = 0; i < e->u.appl.count; ++i) {
                if (print_line && (e->u.appl.functor==INTERN_AND ||
                                   e->u.appl.functor==INTERN_OR ||
                                   e->u.appl.functor==INTERN_ITE)) {
                    print_char('\n');
                    indent_line(depth+1);
                } else {
                    print_char(' ') ;
                }
                _print_exp(e->u.appl.args[i]) ;
            }
            print_char(')') ;
            break ;

        case EXP_CASE:
            print_string("(case ") ;
            _print_exp(e->u.case_stmt.exp) ;
            for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
                print_char(' ') ;
                _print_exp(e->u.case_stmt.args[i]) ;
            }
            print_char(')') ;
            break ;

        case EXP_INDEX:
            print_string("(INDEX ") ;
            _print_exp(e->u.index.exp) ;
            print_char(' ') ;
            sym = _th_intern_decode(e->u.index.functor) ;
            print_string(sym) ;
            print_char(' ') ;
            print_small_number(e->u.index.term) ;
            print_char(')') ;
            break ;

        case EXP_QUANT:
            switch (e->u.quant.quant) {
                 case INTERN_ALL:
                     print_string("(ALL (") ;
                     _print_vars(e) ;
                     if (e->u.quant.cond != _ex_true) {
                         print_string(" : ") ;
                         _print_exp(e->u.quant.cond) ;
                     }
                     print_string(") ") ;
                     _print_exp(e->u.quant.exp) ;
                     _th_adjust_buffer(1) ;
                     print_char(')') ;
                     break ;

                 case INTERN_EXISTS:
                     print_string("(EXISTS (") ;
                     _print_vars(e) ;
                     print_string(") ") ;
                     _print_exp(e->u.quant.exp) ;
                     print_char(')') ;
                     break ;

                 case INTERN_SETQ:
                     print_string("(SET (") ;
                     _print_vars(e) ;
                     if (e->u.quant.cond != _ex_true) {
                         print_string(" : ") ;
                         _print_exp(e->u.quant.cond) ;
                     }
                     print_string(") ") ;
                     _print_exp(e->u.quant.exp) ;
                     print_char(')') ;
                     break ;

                 case INTERN_LAMBDA:
                     print_string("(lambda ") ;
                     _print_vars(e) ;
                     print_char(' ') ;
                     _print_exp(e->u.quant.exp) ;
                     print_char(')') ;
                     break ;

                 default:
                     print_string("<quant printing error>") ;
                     break ;

            }
            break ;
        default:
            //fprintf(stderr, "Printing error\n") ;
            //fflush(stderr) ;
            //exit(1) ;
            print_string("<printing error ") ;
            print_small_number(e->type);
            print_string(">");
            fprintf(stderr, "Illegal term %d\n", e->type);
            fflush(stderr);
            i = 0;
            i = 1/i;
            exit(1);
    }

    --depth;
}

int _th_block_complex = 0;

char *_th_print_exp(struct _ex_intern *e)
{
    int save_pos = _th_pos ;
    char *mark ;

    //if (e && e->type==EXP_APPL && e->u.appl.count > 30) return "xx";
#ifdef XX
	if (e != NULL && _th_has_complex_term(e,10)) {
        if (e->type==EXP_APPL && !_th_block_complex) {
            print_string(_th_intern_decode(e->u.appl.functor));
            _th_print_buf[_th_pos++] = 0;
            _th_pos = save_pos;
            return _th_print_buf+_th_pos;
        }
        print_line = 1;
    } else {
		print_line = 0;
	}
#endif
	print_next = NULL;
    mark = _th_alloc_mark(PARSE_SPACE) ;
    if (e==NULL) {
        return "<NULL>" ;
    }
    _print_exp(e) ;
    _th_print_buf[_th_pos++] = 0 ;
    _th_pos = save_pos ;
    _th_alloc_release(PARSE_SPACE, mark) ;
    while (print_next) {
        print_next->print_line = 0;
        print_next = print_next->print_next;
    }
    print_line = 0;
    return _th_print_buf+_th_pos ;
}

char *_th_tree_exp(unsigned pl, struct _ex_intern *e)
{
    int save_pos = _th_pos ;
    char *mark ;
    //return "xx";
	print_line = pl;
    mark = _th_alloc_mark(PARSE_SPACE) ;
    if (e==NULL) {
        return "<NULL>" ;
    }
    _print_exp(e) ;
    _th_print_buf[_th_pos++] = 0 ;
    _th_pos = save_pos ;
    _th_alloc_release(PARSE_SPACE, mark) ;
	print_line = 0;
    return _th_print_buf+_th_pos ;
}

int skip_to_end(char *text, int pos)
{
    int level = 1 ;

    while(level > 0 && text[pos]) {
        switch (text[pos]) {
            case '(': ++level ; break ;
            case ')': --level ; break ;
        }
        ++pos ;
    }
    return pos-1 ;
}

void _th_get_position(char *text, unsigned count, unsigned *index, int pos, int *start, int *end)
{
    int n, find, special = 0 ;

    while (text[pos]==' ') ++pos ;

    *start = *end = -1 ;

    if (count==0) {
        *start = pos ;
        switch (text[pos++]) {
            case '(':
                pos = skip_to_end(text, pos) ;
                break ;
            case '"':
                while(text[pos] && text[pos] != '"') ++pos ;
                break ;
            default:
                while(text[pos] != ' ' && text[pos] != ')') ++pos ;
        }
        *end = pos ;
        return ;
    }

    if (text[pos]=='(') {
        ++pos ;
        find = index[0] ;
        while (text[pos]==' ') ++pos ;
        if ((!strncmp(text+pos,"SET",3) || !strncmp(text+pos,"ALL",3)) &&
            find==0) {
            special = 1 ;
        } else if ((!strncmp(text+pos,"EXISTS",6) || !strncmp(text+pos,"LAMBDA",6)) &&
            find==0) {
            return ;
        }
        while (text[pos]>' ') ++pos ;
        while (text[pos]==' ') ++pos ;
        n = 0 ;
        while (n < find) {
            while (text[pos]==' ') ++pos ;
            switch (text[pos++]) {
                case '(':
                    pos = skip_to_end(text, pos) ;
                    ++pos ;
                    break ;
                case '"':
                    while(text[pos] && text[pos] != '"') ++pos ;
                    ++pos ;
                    break ;
                default:
                    while(text[pos] != ' ' && text[pos] != ')') ++pos ;
            }
            ++n ;
        }
        while (text[pos]==' ') ++pos ;
        if (special) {
            if (text[pos]!='(') return ;
            ++pos ;
            while (text[pos] != ':') ++pos ;
            ++pos ;
            while (text[pos]==' ') ++pos ;
        }
        _th_get_position(text, count-1, index+1, pos, start, end) ;
        return ;
    }

    return ;
}

