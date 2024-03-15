/*
* ppdir.c
*
* Directive parsing for the pretty printer
*
* (C) 2024, Kenneth Roe
*
* GNU Affero General Public License
*/
#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"

static unsigned split_tokens(unsigned count)
{
    unsigned level = 0 ;
    unsigned i ;
    
    for (i = 1; i < count; ++i) {
        if (_th_tokens[i]==INTERN_LEFT_PAREN ||
            _th_tokens[i]==INTERN_LEFT_BRACKET ||
            _th_tokens[i]==INTERN_LEFT_BRACE) {
            ++level ;
        } else if (_th_tokens[i]==INTERN_RIGHT_PAREN ||
            _th_tokens[i]==INTERN_RIGHT_BRACKET ||
            _th_tokens[i]==INTERN_RIGHT_BRACE) {
            --level ;
        } else if (_th_tokens[i]==INTERN_COLON && level==0) {
            return i ;
        }
    }
    return 0 ;
}

static unsigned count_symbols(unsigned starts, unsigned ends, unsigned s1, unsigned s2, unsigned e1, unsigned e2)
{
    unsigned count = 0 ;
    unsigned escape_char = _th_tokens[starts++] ;
    
    while(starts <= ends && _th_tokens[starts]) {
        if (_th_tokens[starts]==escape_char) {
            while (_th_tokens[++starts] != escape_char) {
                if (starts==ends) return 0 ;
            }
        }
        ++count ;
        ++starts ;
    }
    
    if (s1) ++count ;
    if (s2) ++count ;
    if (e1) ++count ;
    if (e2) ++count ;
    
    return count ;
}

static unsigned end_pos;
static struct _ex_intern *build_exp(unsigned start, unsigned end)
{
    unsigned count, i ;
    char *line ;
    int paren_level = 0 ;

    for (i = start, count = 0; i <= end; ++i) {
        if (_th_tokens[i]==INTERN_LEFT_PAREN) ++paren_level ;
        if (_th_tokens[i]==INTERN_RIGHT_PAREN) --paren_level ;
        count += 1+strlen(_th_intern_decode(_th_tokens[i])) ;
        if (paren_level==0) break ;
    }
    end_pos = i+1 ;

    line = (char *)ALLOCA(count+2) ;
    
    for (i = start, count = 0; i < end_pos; ++i) {
        strcpy(line+count, _th_intern_decode(_th_tokens[i])) ;
        count += strlen(line+count) ;
        line[count++] = ' ' ;
    }
    
    line[count] = 0 ;
    return _th_parse(NULL,line) ;
}

static struct _ex_intern *the_condition ;
static struct _ex_intern *the_print_exp ;
static struct _ex_intern *the_print_condition ;

static struct _ex_intern *parse_rule_exp(unsigned start, unsigned end, int allow_cond )
{
    struct _ex_intern *result ;

    result = build_exp(start, end) ;
    if (end_pos <= end && allow_cond) {
        the_condition = build_exp(end_pos, end) ;
        if (end_pos <= end) {
            the_print_exp = build_exp(end_pos, end) ;
            if (end_pos <= end) {
                the_print_condition = build_exp(end_pos, end) ;
            } else {
                the_print_condition = the_condition ;
            }
        } else {
            the_print_exp = result ;
            the_print_condition = the_condition ;
        }
    } else {
        the_condition = _ex_true ;
        the_print_exp = result ;
        the_print_condition = _ex_true ;
    }

    //printf("result = %s\n", _th_print_exp(result)) ;
    //printf("the_condition = %s\n", _th_print_exp(the_condition)) ;
    //printf("the_print_exp = %s\n", _th_print_exp(the_print_exp)) ;
    //printf("the_print_condition = %s\n", _th_print_exp(the_print_condition)) ;
    return result ;
}

static int fill_list(struct directive *d, unsigned start, unsigned end, unsigned s1, unsigned s2, unsigned e1, unsigned e2)
{
    unsigned count ;
    unsigned i ;
    unsigned escape_token ;
    
    count = 0 ;
    
    if (s1) {
        d->u.pattern.token_list[count].is_var = 0 ;
        d->u.pattern.token_list[count++].u.token = s1 ;
    }
    
    if (s2) {
        d->u.pattern.token_list[count].is_var = 0 ;
        d->u.pattern.token_list[count++].u.token = s2 ;
    }
    
    escape_token = _th_tokens[start] ;
    
    for (i = start+1; i <= end && _th_tokens[i]; ++i) {
        if (_th_tokens[i]==escape_token) {
            d->u.pattern.token_list[count].is_var = 1 ;
            if (_th_tokens[i+1]==escape_token) {
                d->u.pattern.token_list[count].u.var.variable =
                    d->u.pattern.token_list[count].u.var.mode =
                    d->u.pattern.token_list[count].u.var.precedence = 0 ;
                ++i ;
            } else {
                if (!_th_is_identifier(_th_tokens[i+1]) ||
                    !_th_is_identifier(_th_tokens[i+2])) {
                    return 1 ;
                }
                d->u.pattern.token_list[count].u.var.variable = _th_tokens[i+1] ;
                d->u.pattern.token_list[count].u.var.mode = _th_tokens[i+2] ;
                if (_th_tokens[i+3]==escape_token) {
                    d->u.pattern.token_list[count].u.var.precedence = 0 ;
                } else if (_th_is_number(_th_tokens[i+3])) {
                    d->u.pattern.token_list[count].u.var.precedence = atoi(_th_intern_decode(_th_tokens[i+3])) ;
                    ++i ;
                } else {
                    return 1 ;
                }
                i += 3 ;
            }
            ++count ;
        } else {
            d->u.pattern.token_list[count].is_var = 0 ;
            d->u.pattern.token_list[count++].u.token = _th_tokens[i] ;
        }
    }
    
    if (e2) {
        d->u.pattern.token_list[count].is_var = 0 ;
        d->u.pattern.token_list[count++].u.token = e2 ;
    }
    
    if (e1) {
        d->u.pattern.token_list[count].is_var = 0 ;
        d->u.pattern.token_list[count++].u.token = e1 ;
    }
    
    return 0 ;
}

static unsigned count_breaks(unsigned start,unsigned ends)
{
    unsigned count = 0 ;
    
    while (start <= ends) {
        if (_th_tokens[start]==INTERN_POUND) {
            ++start ;
            if (_th_tokens[start]==INTERN_FBM ||
                _th_tokens[start]==INTERN_OL ||
                _th_tokens[start]==INTERN_ML) {
                start += 2 ;
            } else if (_th_tokens[start]==INTERN_OBM ||
                _th_tokens[start]==INTERN_RBM) {
                start += 3 ;
            } else if (_th_tokens[start]==INTERN_FB) {
                ++count ;
                start += 2 ;
            } else {
                ++count ;
                start += 3 ;
            }
        } else {
            ++count ;
            ++start ;
        }
    }
    return count ;
}

static struct directive *parse_pattern(int space, unsigned id, unsigned mode, unsigned count, unsigned first, unsigned type, struct directive *next, unsigned start1, unsigned end1, unsigned start2, unsigned end2)
{
    unsigned split, start, precedence, element_count ;
    struct directive *directive, *result ;
    
    split = split_tokens(count) ;
    if (split==0) return NULL ;
    if (!_th_is_identifier(id)) return NULL ;
    if (_th_is_number(_th_tokens[first+1])) {
        start = first+2 ;
        precedence = atoi(_th_intern_decode(_th_tokens[first+1])) ;
    } else {
        start = first+1 ;
        precedence = 10000 ;
    }
    element_count = count_symbols(split+1,count,start1,start2,end1,end2) ;
    result = (struct directive *)_th_alloc(space,sizeof(struct directive) + element_count * sizeof(struct element)) ;
    result->type = type ;
    result->next = next ;
    result->u.pattern.rule = id ;
    result->u.pattern.precedence = precedence ;
    result->u.pattern.exp = parse_rule_exp(start, split-1, 1) ;
    result->u.pattern.condition = the_condition ;
    result->u.pattern.print_exp = the_print_exp ;
    result->u.pattern.print_condition = the_print_condition ;
    if (result->u.pattern.exp==NULL) return NULL ;
    result->u.pattern.token_count = element_count ;
    if (fill_list(result, split+1, count, start1, start2, end1, end2)) {
        return NULL ;
    }
    directive = (struct directive *)_th_alloc(space,sizeof(struct directive)) ;
    directive->type = PARSE_PERMIT ;
    directive->u.permit.mode = mode ;
    directive->u.permit.rule = id ;
    directive->u.permit.next = NULL ;
    result->u.pattern.permits = directive ;
    directive->next = result ;
    
    return directive ;
    //result = (struct directive *)_th_alloc(space,sizeof(struct directive) + element_count * 3 * sizeof(int)) ;
    //result->next = directive ;
    //result->type = PARSE_BREAK ;
    //result->u.parse_break.rule = id ;
    //result->u.parse_break.count = element_count ;
    //for (i = 0; i < element_count; ++i) {
    //if (result->u.pattern.token_list[i].is_var) {
    //result->u.parse_break.list[i].break_mode = REQUIRED_BREAK ;
    //result->u.parse_break.list[i].indent = 1 ;
    //result->u.parse_break.list[i].child_breaks_allowed = 1 ;
    //} else {
    //result->u.parse_break.list[i].break_mode = FORBID_BREAK ;
    //result->u.parse_break.list[i].indent = 1 ;
    //result->u.parse_break.list[i].child_breaks_allowed = 0 ;
    //}
    //}
    //return result ;
}

void _th_print_directives(struct directive *d)
{
	char *pat ;
    int i ;

	/**********/

	if (d==NULL) return ;
	switch (d->type) {
	    case PARSE_PATTERN:
                pat = "both" ;
                goto cont ;
            case PRINT_PATTERN:
                pat = "print" ;
                goto cont ;
            case INPUT_PATTERN:
                pat = "input" ;
cont:
                printf("Directive: %s\n", pat) ;
                printf("    rule: %s\n",
                       _th_intern_decode(d->u.pattern.rule)) ;
                printf("    expression: %s\n", _th_print_exp(d->u.pattern.exp)) ;
                printf("    condition: %s\n", _th_print_exp(d->u.pattern.condition)) ;
                printf("    tokens:") ;
                for (i = 0; i < d->u.pattern.token_count; ++i) {
                    if (d->u.pattern.token_list[i].is_var) {
                        printf(" #%s %s %d#",
                               _th_intern_decode(d->u.pattern.token_list[i].u.var.variable),
                               _th_intern_decode(d->u.pattern.token_list[i].u.var.mode),
                               d->u.pattern.token_list[i].u.var.precedence) ;
                    } else if (d->u.pattern.token_list[i].u.token==INTERN_SPACE_BAR) {
                        printf(" \\b") ;
                    } else {
                        printf(" %s", _th_intern_decode(d->u.pattern.token_list[i].u.token)) ;
                    }
                }
                printf("\n") ;
                break ;
            case PARSE_PERMIT:
                printf("permit %s %s\n",
                    _th_intern_decode(d->u.permit.rule),
                    _th_intern_decode(d->u.permit.mode)) ;
                break ;
            case PARSE_USE_RULE:
                printf("use rule %s %s\n    condition: %s\n",
                    _th_intern_decode(d->u.use_rule.rule),
                    _th_intern_decode(d->u.use_rule.mode),
                    _th_print_exp(d->u.use_rule.condition)) ;
                break ;
            case PARSE_BREAK:
                printf("break %s\n    ", _th_intern_decode(d->u.parse_break.rule)) ;
                for (i = 0; i < d->u.parse_break.count; ++i) {
                    printf(" #%d %d %d#",
                           d->u.parse_break.list[i].break_mode,
                           d->u.parse_break.list[i].indent,
                           d->u.parse_break.list[i].child_breaks_allowed) ;
                }
                printf("\n") ;
                break ;
            case PARSE_PRECEDENCE:
                printf("precedence\n") ;
                break ;
            case PARSE_MARK:
                printf("mark %s %d %d index",
                       _th_intern_decode(d->u.parse_mark.rule),
                       d->u.parse_mark.start,
                       d->u.parse_mark.end) ;
                for (i = 0; i < d->u.parse_mark.count; ++i) {
                    printf(" %d", d->u.parse_mark.index[i]) ;
                }
                printf("\n") ;
    }
    _th_print_directives(d->next) ;
}

static unsigned add_suffix(unsigned tok, int suffix)
{
	char name[100] ;
	sprintf(name, "%s/%d", _th_intern_decode(tok), suffix) ;
	return _th_intern(name) ;
}

static void add_permit_links(struct directive *permit, struct directive *rules)
{
    while (rules != NULL) {
        if ((rules->type==PARSE_PATTERN || rules->type==PRINT_PATTERN || rules->type==INPUT_PATTERN) &&
            rules->u.pattern.rule==permit->u.permit.rule) {
            permit->u.permit.next = rules->u.pattern.permits ;
            rules->u.pattern.permits = permit ;
            return ;
        }
        rules = rules->next ;
    }
}

static void add_rule_links(struct directive *rule, struct directive *permits)
{
    while (permits != NULL) {
        if (permits->type == PARSE_PERMIT &&
            rule->u.pattern.rule==permits->u.permit.rule) {
            permits->u.permit.next = rule->u.pattern.permits ;
            rule->u.pattern.permits = permits ;
            return ;
        }
        permits = permits->next ;
    }
}

struct directive *_th_tokenize_line(int space, char *s, struct directive *rest)
{
    unsigned count = _th_tokenize_string(s, "line") ;
    unsigned split, start, id, precedence, br_mode, br_indent, br_flag, type ;
    struct directive *result, *directive ;
    unsigned element_count, i ;

    switch (_th_tokens[0]) {

        case INTERN_INPUT:
        case INTERN_OUTPUT:
        case INTERN_DEFAULT:
            switch (_th_tokens[0]) {
                case INTERN_INPUT:
                    type = INPUT_PATTERN ;
                    break ;
                case INTERN_OUTPUT:
                    type = PRINT_PATTERN ;
                    break ;
                case INTERN_DEFAULT:
                    type = PARSE_PATTERN ;
                    break ;
            }
            return parse_pattern(space, _th_tokens[2], _th_tokens[1], count, 2, type, rest, 0, 0, 0, 0) ;

        case INTERN_MODE:
            directive = parse_pattern(space, _th_tokens[4], _th_tokens[1], count, 4, PARSE_PATTERN, rest, 0, 0, 0, 0) ;
            if (directive==NULL) return NULL ;
            directive = parse_pattern(space, add_suffix(_th_tokens[4],1), INTERN_DEFAULT, count, 4, PARSE_PATTERN, directive, _th_tokens[2], _th_tokens[3], 0, 0) ;
            return directive ;

        case INTERN_INFIX:
            directive = parse_pattern(space, _th_tokens[4], _th_tokens[1], count, 4, PARSE_PATTERN, rest, 0, 0, 0, 0) ;
            if (directive==NULL) return NULL ;
            directive = parse_pattern(space, add_suffix(_th_tokens[4],1), _th_tokens[1], count, 4, PARSE_PATTERN, directive, _th_tokens[2], _th_tokens[3], 0, 0) ;
            return directive ;

        case INTERN_INFIX_MODE:
            directive = parse_pattern(space, _th_tokens[6], _th_tokens[1], count, 6, PARSE_PATTERN, rest, 0, 0, 0, 0) ;
            if (directive==NULL) return NULL ;
            directive = parse_pattern(space, add_suffix(_th_tokens[6],1), INTERN_DEFAULT, count, 6, PARSE_PATTERN, directive, _th_tokens[2], _th_tokens[3], 0, 0) ;
            if (directive==NULL) return NULL ;
            directive = parse_pattern(space, add_suffix(_th_tokens[6],2), _th_tokens[1], count, 6, PARSE_PATTERN, directive, _th_tokens[4], _th_tokens[5], 0, 0) ;
            if (directive==NULL) return NULL ;
            directive = parse_pattern(space, add_suffix(_th_tokens[6],3), INTERN_DEFAULT, count, 6, PARSE_PATTERN, directive, _th_tokens[2], _th_tokens[3], _th_tokens[4], _th_tokens[5]) ;
            return directive ;

        case INTERN_PATTERN:
            split = split_tokens(count) ;
            if (split==0) return NULL ;
            if (!_th_is_identifier(_th_tokens[1])) return NULL ;
            if (!_th_is_identifier(_th_tokens[2])) return NULL ;
            id = _th_tokens[1] ;
            if (_th_is_number(_th_tokens[3])) {
                start = 4 ;
                precedence = atoi(_th_intern_decode(_th_tokens[2])) ;
            } else {
                start = 3 ;
                precedence = 10000 ;
            }
            element_count = count_symbols(split+1,count,0,0,0,0) ;
            result = (struct directive *)_th_alloc(space,sizeof(struct directive) + element_count * sizeof(struct element)) ;
            result->type = PARSE_PATTERN ;
            result->next = rest ;
            result->u.pattern.rule = _th_tokens[2] ;
            result->u.pattern.precedence = precedence ;
            result->u.pattern.exp = parse_rule_exp(start, split-1, 1) ;
            result->u.pattern.condition = the_condition ;
            result->u.pattern.print_exp = the_print_exp ;
            result->u.pattern.print_condition = the_print_condition ;
            result->u.pattern.token_count = element_count ;
            add_rule_links(result,rest) ;
            if (fill_list(result, split+1,count,0,0,0,0)) {
                return NULL ;
            }
            return result ;

        case INTERN_PERMIT:
             if (!_th_is_identifier(_th_tokens[1])) return NULL ;
             if (!_th_is_identifier(_th_tokens[2])) return NULL ;
             if (count != 3) return NULL ;
             directive = (struct directive *)_th_alloc(space,sizeof(struct directive)) ;
             directive->type = PARSE_PERMIT ;
             directive->u.permit.mode = _th_tokens[1] ;
             directive->u.permit.rule = _th_tokens[2] ;
             directive->next = rest ;
             add_permit_links(directive,rest) ;
             return directive ;

        case INTERN_USE_RULE:
             if (!_th_is_identifier(_th_tokens[1])) return NULL ;
             if (!_th_is_identifier(_th_tokens[2])) return NULL ;
             if (count != 3) return NULL ;
             directive = (struct directive *)_th_alloc(space,sizeof(struct directive)) ;
             directive->type = PARSE_USE_RULE ;
             directive->u.use_rule.mode = _th_tokens[1] ;
             directive->u.use_rule.rule = _th_tokens[2] ;
             directive->u.use_rule.condition = parse_rule_exp(3, count-1, 0) ;
             directive->u.pattern.print_exp = the_print_exp ;
             directive->u.pattern.print_condition = the_print_condition ;
             directive->next = rest ;
             add_permit_links(directive,rest) ;
             return directive ;

         case INTERN_MARK:
             if (!_th_is_identifier(_th_tokens[1])) return NULL ;
             for (i = 2; i < count; ++i) {
                 if (!_th_is_number(_th_tokens[i])) return NULL ;
             }
             directive = (struct directive *)_th_alloc(space,sizeof(struct directive) + (count - 4) * sizeof(unsigned)) ;
             directive->type = PARSE_MARK ;
             directive->u.parse_mark.rule = _th_tokens[1] ;
             directive->u.parse_mark.start = atoi(_th_intern_decode(_th_tokens[2])) ;
             directive->u.parse_mark.end = atoi(_th_intern_decode(_th_tokens[3])) ;
             for (i = 0; i < count - 4; ++i) {
                 directive->u.parse_mark.index[i] = atoi(_th_intern_decode(_th_tokens[i+4])) ;
             }
             directive->u.parse_mark.count = count - 4 ;
             directive->next = rest ;
             return directive ;

        case INTERN_BREAK:
            element_count = count_breaks(2,count) ;
            directive = (struct directive *)_th_alloc(space,sizeof(struct directive) + element_count * sizeof(int) * 3) ;
            directive->type = PARSE_BREAK ;
            directive->u.parse_break.rule = _th_tokens[1] ;
            directive->u.parse_break.count = element_count ;
            directive->next = rest ;
            br_flag = 0 ;
            br_indent = 0 ;
            br_mode = FORBID_BREAK ;
            start = 2 ;
            i = 0 ;
            while (start < count) {
                if (_th_tokens[start]==INTERN_POUND) {
                    ++start ;
                    if (start==count) return NULL ;
                    switch (_th_tokens[start]) {
                        case INTERN_FBM:
                            br_mode = FORBID_BREAK ;
                            ++start ;
                            if (start==count) return NULL ;
                            if (_th_tokens[start] != INTERN_POUND) return NULL ;
                            ++start ;
                            break ;
                        case INTERN_OL:
                            br_flag = 0 ;
                            ++start ;
                            if (start==count) return NULL ;
                            if (_th_tokens[start] != INTERN_POUND) return NULL ;
                            ++start ;
                            break ;
                        case INTERN_ML:
                            br_flag = 1 ;
                            ++start ;
                            if (start==count) return NULL ;
                            if (_th_tokens[start] != INTERN_POUND) return NULL ;
                            ++start ;
                            break ;
                        case INTERN_OBM:
                            br_mode = OPTIONAL_BREAK ;
                            ++start ;
                            if (start==count) return NULL ;
                            if (!_th_is_number(_th_tokens[start])) return NULL ;
                            br_indent = atoi(_th_intern_decode(_th_tokens[start])) ;
                            ++start ;
                            if (start==count) return NULL ;
                            if (_th_tokens[start] != INTERN_POUND) return NULL ;
                            ++start ;
                            break ;
                        case INTERN_RBM:
                            br_mode = REQUIRED_BREAK ;
                            ++start ;
                            if (start==count) return NULL ;
                            if (!_th_is_number(_th_tokens[start])) return NULL ;
                            br_indent = atoi(_th_intern_decode(_th_tokens[start])) ;
                            ++start ;
                            if (start==count) return NULL ;
                            if (_th_tokens[start] != INTERN_POUND) return NULL ;
                            ++start ;
                            break ;
                        case INTERN_FB:
                            directive->u.parse_break.list[i].break_mode = FORBID_BREAK ;
                            directive->u.parse_break.list[i].indent = br_indent ;
                            directive->u.parse_break.list[i].child_breaks_allowed = br_flag ;
                            ++i ;
                            ++start ;
                            if (start==count) return NULL ;
                            if (_th_tokens[start] != INTERN_POUND) return NULL ;
                            ++start ;
                            break ;
                        case INTERN_OB:
                            directive->u.parse_break.list[i].break_mode = OPTIONAL_BREAK ;
                            directive->u.parse_break.list[i].child_breaks_allowed = br_flag ;
                            ++start ;
                            if (!_th_is_number(_th_tokens[start])) return NULL ;
                            directive->u.parse_break.list[i].indent = atoi(_th_intern_decode(_th_tokens[start])) ;
                            ++start ;
                            ++i ;
                            if (_th_tokens[start] != INTERN_POUND) return NULL ;
                            ++start ;
                            break ;
                        case INTERN_RB:
                            directive->u.parse_break.list[i].break_mode = REQUIRED_BREAK ;
                            directive->u.parse_break.list[i].child_breaks_allowed = br_flag ;
                            ++start ;
                            if (!_th_is_number(_th_tokens[start])) return NULL ;
                            directive->u.parse_break.list[i].indent = atoi(_th_intern_decode(_th_tokens[start])) ;
                            ++start ;
                            ++i ;
                            if (_th_tokens[start] != INTERN_POUND) return NULL ;
                            ++start ;
                            break ;
                        default:
                            return NULL ;
                    }
                } else {
                    directive->u.parse_break.list[i].break_mode = br_mode ;
                    directive->u.parse_break.list[i].indent = br_indent ;
                    directive->u.parse_break.list[i].child_breaks_allowed = br_flag ;
                    ++i ; ++start ;
                }
            }
            return directive ;
        default:
            return NULL ;
    }
}
