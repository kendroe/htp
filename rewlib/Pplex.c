/*
 * pplex.c
 *
 * Search routines
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <ctype.h>
#include "Globals.h"
#include "Intern.h"
#include <string.h>

unsigned ismypunct(char x)
{
    return ispunct(x) && x != ':' && x != ';' && x != '"' && x != '\'' &&
           x != '(' && x != ')' && x != '[' && x != ']' && x != '{' &&
           x != '}' && x != '\\' && x!= ',' && x!='_' && x!='*';
}

static unsigned start_row, start_column, start_file, row, column, last_column ;

void process_newline(char **pointer)
{
    char *c, name[1000] ;
    
    while (!strncmp(*pointer,"#line",5)) {
        *pointer += 5 ;
        while (**pointer==' ') ++*pointer ;
        row = atoi(*pointer) ;
        while (**pointer != ' ') ++*pointer ;
        while (**pointer == ' ') ++*pointer ;
        ++*pointer ;
        c = name ;
        while (**pointer != '"') {
            *c++ = **pointer ;
            ++*pointer ;
        }
        *c = 0 ;
        start_file = _th_intern(name) ;
        while (**pointer && **pointer != '\n') ++*pointer ;
        if (**pointer) ++*pointer ;
    }
}

void move_to_next(char **pointer)
{
	if (**pointer=='\n') {
		++row ;
		last_column = column ;
		column = 0 ;
		++*pointer ;
		process_newline(pointer) ;
	} else {
		++column ;
		++*pointer ;
	}
}

unsigned parse_token(char **pointer)
{
    char *str ;
    char *p ;
    
retry:
    while (**pointer==' ' || **pointer=='\n' || **pointer=='\t') move_to_next(pointer) ;
    
    start_row = row ;
    start_column = column ;
    
    switch (**pointer) {
        
    case 0:
        return 0 ;
    case '/':
        move_to_next(pointer) ;
        switch (**pointer) {
        case '/':
            move_to_next(pointer) ;
            if (**pointer=='#') {
                move_to_next(pointer) ;
                return INTERN_ONE_LINE_DIRECTIVE ;
            }
            while (**pointer && **pointer != '\n') {
                move_to_next(pointer) ;
            }
            //return INTERN_ONE_LINE_COMMENT ;
            goto retry ;
        case '*':
            move_to_next(pointer) ;
            if (**pointer=='#') {
                move_to_next(pointer) ;
                return INTERN_START_DIRECTIVE ;
            }
            while (**pointer) {
                if (**pointer=='*') {
                    move_to_next(pointer) ;
                    if (**pointer=='/') {
                        move_to_next(pointer) ;
                        goto retry ;
                    } else {
                        continue ;
                    }
                }
                move_to_next(pointer) ;
            }
            goto retry ;
        }
        return INTERN_SLASH ;
        case '(':
            move_to_next(pointer) ;
            return INTERN_LEFT_PAREN ;
        case ')':
            move_to_next(pointer) ;
            return INTERN_RIGHT_PAREN ;
        case '[':
            move_to_next(pointer) ;
            return INTERN_LEFT_BRACKET ;
        case ']':
            move_to_next(pointer) ;
            return INTERN_RIGHT_BRACKET ;
        case '{':
            move_to_next(pointer) ;
            return INTERN_LEFT_BRACE ;
        case '}':
            move_to_next(pointer) ;
            return INTERN_RIGHT_BRACE ;
        case ':':
            move_to_next(pointer) ;
            return INTERN_COLON ;
        case ',':
            move_to_next(pointer) ;
            return INTERN_COMMA ;
        case ';':
            move_to_next(pointer) ;
            return INTERN_SEMICOLON ;
        case '%':
            move_to_next(pointer) ;
            return INTERN_PERCENT ;
		case '*':
			move_to_next(pointer) ;
			return INTERN_STAR ;
        case '\\':
            move_to_next(pointer) ;
            if (**pointer=='b') {
                move_to_next(pointer) ;
                return INTERN_SPACE_BAR ;
            }
            return INTERN_BACK_SLASH ;
        case '"':
            p = *pointer ;
            ++p ;
            while (*p && *p != '"') {
                if (*p=='\\' && p[1]) {
                    p += 2 ;
                } else {
                    ++p ;
                }
            }
            str = (char *)ALLOCA(sizeof(char) * (p - *pointer + 2)) ;
            p = str ;
            *p++ = **pointer ;
            move_to_next(pointer) ;
            while (**pointer && **pointer != '"') {
                if (**pointer=='\\') {
                    move_to_next(pointer) ;
                    switch (**pointer) {
                    case 'n':
                        *p++ = '\n' ;
                        break ;
                    case 'r':
                        *p++ = '\r' ;
                        break ;
                    default:
                        if (isdigit(**pointer)) {
                            if (isdigit((*pointer)[1])) {
                                if (isdigit((*pointer)[2])) {
                                    *p++ = (**pointer - '0') * 100 + ((*pointer)[1] - '0') * 10 + ((*pointer)[2] - '0') ;
                                    move_to_next(pointer) ;
                                    move_to_next(pointer) ;
                                    move_to_next(pointer) ;
                                } else {
                                    *p++ = (**pointer - '0') * 10 + ((*pointer)[1] - '0') ;
                                    move_to_next(pointer) ;
                                    move_to_next(pointer) ;
                                }
                            } else {
                                *p++ = **pointer - '0' ;
                                move_to_next(pointer) ;
                            }
                        } else {
                            *p++ = **pointer ;
                            move_to_next(pointer) ;
                        }
                    }
                } else {
                    *p++= **pointer ;
                    move_to_next(pointer) ;
                }
            }
            if (**pointer) {
                move_to_next(pointer) ;
                *p++ = '"' ;
            }
            *p = 0 ;
            return _th_intern(str) ;
        case '\'':
            move_to_next(pointer) ;
            str = (char *)ALLOCA(sizeof(char) * 4) ;
            str[3] = 0 ;
            str[0] = str[2] = '\'' ;
            if (**pointer=='\\') {
                if (isdigit((*pointer)[1])) {
                    if (isdigit((*pointer)[2])) {
                        if (isdigit((*pointer)[3])) {
                            if ((*pointer)[4]=='\'') {
                                str[2] = ((*pointer)[1]-'0') * 100 +
                                    ((*pointer)[2]-'0') * 10 +
                                    ((*pointer)[3]-'0') ;
                                return _th_intern(str) ;
                            } else return INTERN_SQUOTE ;
                        }
                        if ((*pointer)[3]=='\'') {
                            str[2] = ((*pointer)[1]-'1') * 10 +
                                ((*pointer)[2]-'0') ;
                            return _th_intern(str) ;
                        } else return INTERN_SQUOTE ;
                    } else return INTERN_SQUOTE ;
                    if ((*pointer)[2]=='\'') {
                        str[2] = ((*pointer)[1]-'1') * 10 +
                            ((*pointer)[2]-'0') ;
                        return _th_intern(str) ;
                    } else return INTERN_SQUOTE ;
                } else if ((*pointer)[2]=='\'') {
                    switch ((*pointer)[1]) {
                    case 'n':
                        str[2] = '\n' ;
                        break ;
                    case 'r':
                        str[2] = '\r' ;
                        break ;
                    default:
                        str[2] = (*pointer)[1] ;
                    }
                    move_to_next(pointer) ;
                    move_to_next(pointer) ;
                    move_to_next(pointer) ;
                    return _th_intern(str) ;
                }
                return INTERN_SQUOTE ;
            } else if ((*pointer)[1]=='\'') {
                str[1]=**pointer ;
                move_to_next(pointer) ;
                move_to_next(pointer) ;
                return _th_intern(str) ;
            } else return INTERN_SQUOTE ;
        default:
            if (isalpha(**pointer) || **pointer=='_') {
                p = *pointer ;
                while (isalnum(*p) || *p=='_') ++p ;
                str = (char *)ALLOCA(p-*pointer+1) ;
                p = str ;
                while (isalnum(**pointer) || **pointer=='_') {
                    *p++ = **pointer ;
                    move_to_next(pointer) ;
                }
                *p = 0 ;
                return _th_intern(str) ;
            } else if (isdigit(**pointer)) {
                p = *pointer ;
                while (isdigit(*p)) ++p ;
                str = (char *)ALLOCA(p-*pointer+1) ;
                p = str ;
                while (isdigit(**pointer)) {
                    *p++ = **pointer ;
                    move_to_next(pointer) ;
                }
                *p = 0 ;
                return _th_intern(str) ;
            } else if (ismypunct(**pointer)) {
                p = *pointer ;
                while (ismypunct(*p)) ++p ;
                str = (char *)ALLOCA(p-*pointer+1) ;
                p = str ;
                while (ismypunct(**pointer)) {
                    *p++ = **pointer ;
                    move_to_next(pointer) ;
                    if (**pointer=='@' && *(*pointer -1)=='>') break ;
                }
                *p = 0 ;
                return _th_intern(str) ;
            }
            return 0 ;
    }
}

int *_th_row ;
int *_th_column ;
unsigned *_th_file ;
int *_th_end_row ;
int *_th_end_column ;
unsigned *_th_tokens ;

#define SIZE_INCREMENT 1000

static unsigned bufsize = 0 ;

static void check_size(unsigned x)
{
	if (x <= bufsize) return ;

	x += SIZE_INCREMENT ;

	if (bufsize==0) {
		_th_row = (unsigned *)MALLOC(sizeof(unsigned) * x) ;
		_th_column = (unsigned *)MALLOC(sizeof(unsigned) * x) ;
		_th_file = (unsigned *)MALLOC(sizeof(unsigned) * x) ;
		_th_end_row = (unsigned *)MALLOC(sizeof(unsigned) * x) ;
		_th_end_column = (unsigned *)MALLOC(sizeof(unsigned) * x) ;
		_th_tokens = (unsigned *)MALLOC(sizeof(unsigned) * x) ;
	} else {
		_th_row = (unsigned *)REALLOC(_th_row,sizeof(unsigned) * x) ;
		_th_end_row = (unsigned *)REALLOC(_th_end_row,sizeof(unsigned) * x) ;
		_th_column = (unsigned *)REALLOC(_th_column,sizeof(unsigned) * x) ;
		_th_file = (unsigned *)REALLOC(_th_file,sizeof(unsigned) * x) ;
		_th_end_column = (unsigned *)REALLOC(_th_end_column,sizeof(unsigned) * x) ;
		_th_tokens = (unsigned *)REALLOC(_th_tokens,sizeof(unsigned) * x) ;
	}
	bufsize = x ;
}

int _th_tokenize_string(char *s, char *file)
{
    int count = 0 ;
    /*unsigned i ;*/

    start_file = _th_intern(file) ;
    row = 1 ;
    column = 0 ;
    //process_newline(&s) ;
    while (*s) {
        check_size(count+2) ;
        _th_tokens[count] = parse_token(&s) ;
        _th_row[count] = start_row ;
        _th_column[count] = start_column ;
        _th_file[count] = start_file;
        if (column==0) {
            _th_row[count+1] = _th_end_row[count] = row-1 ;
            _th_column[count+1] = _th_end_column[count] = last_column ;
        } else {
            _th_row[count+1] = _th_end_row[count] = row ;
            _th_column[count+1] = _th_end_column[count] = column-1 ;
        }
        if (!_th_tokens[count]) break ;
        ++count ;
    }
    /*for (i = 0; i < count; ++i) {
        printf("%s %d %d %d %d\n",
        _th_intern_decode(_th_tokens[i]),
        _th_row[i],
        _th_column[i],
        _th_end_row[i],
        _th_end_column[i]) ;
    }*/
    _th_tokens[count] = 0 ;
    return count ;
}

int _th_is_number(unsigned tok)
{
	char *t ;
	
	if (tok==0) return 0 ;
	
	t = _th_intern_decode(tok) ;

	return isdigit(*t) ;
}

int _th_is_identifier(unsigned tok)
{
	char *t ;
	
	if (tok==0) return 0 ;

	t = _th_intern_decode(tok) ;

	return isalpha(*t) ;
}

int _th_is_string(unsigned tok)
{
	char *t ;
	
	if (tok==0) return 0 ;

	t = _th_intern_decode(tok) ;

	return *t=='"' ;
}
