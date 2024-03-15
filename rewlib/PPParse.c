//#define DEBUG
/*
 * ppparse.c
 *
 * Pretty printer stuff--directive parsing, parsing and printing
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero Generl Public License
 */
#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"

#define INITIAL_PRINT_SIZE 100000
char *_th_pp_print_buf ;
static int print_size ;

void _th_pp_print_init()
{
    _th_pp_print_buf = (char *)MALLOC(INITIAL_PRINT_SIZE) ;
    print_size = INITIAL_PRINT_SIZE ;
}

void _th_pp_print_shutdown()
{
}

int _th_pp_pos = 0 ;

void _th_pp_adjust_buffer(int size)
{
    if (print_size-_th_pp_pos-size <= 0) {
        print_size += size + 100000 ;
        _th_pp_print_buf = (char *)REALLOC(_th_pp_print_buf, print_size) ;
        if (_th_pp_print_buf==NULL) {
            printf("Error in REALLOC\n") ; 
            exit(1) ;
        }
    }
}

static int *current ;
static int current_count ;
static int current_alloc ;

int _th_index_count ;
static unsigned index_alloc ;
int **_th_index ;

static void check_current(int size)
{
    if (size > current_alloc) {
        unsigned ca = current_alloc ;
        current_alloc = size + 500 ;
        if (ca==0) {
            current = (int *)MALLOC(sizeof(unsigned) * current_alloc) ;
        } else {
            current = (int *)REALLOC(current, sizeof(unsigned) * current_alloc) ;
        }
    }
}

void _th_push_current(unsigned c)
{
    check_current(current_count+1) ;
    current[current_count++] = c ;
}

void _th_pop_current()
{
    --current_count ;
}

static void check_index(unsigned size)
{
    if (size > index_alloc) {
        unsigned oi = index_alloc ;
        index_alloc = size + 500 ;
        if (oi==0) {
            _th_index = (int **)MALLOC(sizeof(unsigned *) * index_alloc) ;
        } else {
            _th_index = (int **)REALLOC(_th_index, sizeof(unsigned *) * index_alloc) ;
        }
    }
}

static void free_index()
{
    int i ;
    
    for (i = 0; i < _th_index_count; ++i) {
        FREE(_th_index[i]) ;
    }
    _th_index_count = 0 ;
}

static void add_index(unsigned file, unsigned startx, unsigned starty, unsigned endx, unsigned endy)
{
    int i ;
    
    check_index(_th_index_count+1) ;
    _th_index[_th_index_count] = (int *)MALLOC(sizeof(unsigned) * (current_count+6)) ;
    
    for (i = 0; i < current_count; ++i) {
        _th_index[_th_index_count][i+6] = current[i] ;
    }
    
    _th_index[_th_index_count][0] = startx ;
    _th_index[_th_index_count][1] = starty ;
    _th_index[_th_index_count][2] = endx ;
    _th_index[_th_index_count][3] = endy ;
    _th_index[_th_index_count][4] = file ;
    _th_index[_th_index_count][5] = current_count ;
    
    ++_th_index_count ;
}

unsigned _th_find_position(unsigned *row, unsigned *column)
{
	int i, pos, count, j ;

	pos = 0xffffffff ;
    count = 0 ;

#ifdef DEBUG
	printf("Finding") ;
	for (i = 0; i < current_count; ++i) {
		printf(" %d", current[i]) ;
	}
	printf("\n") ;
#endif

	for (i = 0; i < _th_index_count; ++i) {
		if (_th_index[i][5] <= current_count &&
			_th_index[i][5] >= count) {
#ifdef DEBUG
			printf("Testing %d %d ->",
				_th_index[i][0], _th_index[i][1]) ;
			for (j = 0; j < _th_index[i][5]; ++j) {
				printf(" %d", _th_index[i][6+j]) ;
			}
			printf("\n") ;
#endif
			for (j = 0; j < _th_index[i][5]; ++j) {
				if (_th_index[i][6+j] != current[j]) goto cont ;
			}
			count = _th_index[i][5] ;
			pos = i ;
cont: ;
		}
	}
	if (pos != 0xffffffff) {
		if (column) *column = _th_index[pos][0] ;
		if (row) *row = _th_index[pos][1] ;
		return _th_index[pos][4] ;
	}
	return 0 ;
}

struct trie {
	struct trie *next ;
	struct trie *children ;
	struct element e ;
	struct directive *terminal ;
} ;

struct trie_l {
	struct trie_l *next ;
	struct trie *trie ;
	unsigned mode ;
	struct directive *terminal ;
} ;

static void _print_trie(struct trie *trie, int indent)
{
    int i ;
    
    if (trie==NULL) return ;
    
    i = indent ;
    while (i--) printf(" ") ;
    if (trie->e.is_var) {
        printf("trie var %s %s %d\n",
            _th_intern_decode(trie->e.u.var.variable),
            _th_intern_decode(trie->e.u.var.mode),
            trie->e.u.var.precedence) ;
    } else if (trie->e.u.token) {
        printf("trie token %s\n", _th_intern_decode(trie->e.u.token)) ;
    } else {
        printf("no trie token\n") ;
    }
    if (trie->terminal != NULL) {
        i = indent ;
        while (i--) printf(" ") ;
        printf("terminal %s\n", _th_intern_decode(trie->terminal->u.pattern.rule)) ;
    }
    _print_trie(trie->children, indent+4) ;
    _print_trie(trie->next, indent) ;
}

static void _print_trie_l(struct trie_l *trie)
{
    while (trie != NULL) {
        printf("Trie for mode %s\n", _th_intern_decode(trie->mode)) ;
        _print_trie(trie->trie, 4) ;
        if (trie->terminal != NULL) {
            printf("terminal %s\n", _th_intern_decode(trie->terminal->u.pattern.rule)) ;
        }
        trie = trie->next ;
    }
}

static int similar_elements(struct element *e1, struct element *e2)
{
    if (e1->is_var != e2->is_var) return 0 ;
    
    if (e1->is_var) {
        return e1->u.var.mode==e2->u.var.mode &&
            e1->u.var.precedence==e2->u.var.precedence ;
    } else {
        return e1->u.token==e2->u.token ;
    }
}

static int used_in_mode(unsigned rule, unsigned mode, struct directive *directive)
{
    while (directive != NULL) {
        if (directive->type==PARSE_PERMIT) {
            if (rule==directive->u.permit.rule &&
                mode==directive->u.permit.mode) return 1 ;
        }
        directive = directive->next ;
    }
    return 0 ;
}

#define MAX_RULE_SIZE 200

static int size = 0 ;

static int valid_element(struct directive *d, int pos)
{
    if (d->u.pattern.token_list[pos].is_var) {
        return d->u.pattern.token_list[pos].u.var.variable != 0 ;
    } else {
        return d->u.pattern.token_list[pos].u.token != INTERN_SPACE_BAR ;
    }
}

static int valid_element_count(struct directive *d)
{
    int i, count = 0 ;
    
    for (i = 0; i < d->u.pattern.token_count; ++i) {
        if (valid_element(d, i)) ++count ;
    }
    
    return count ;
}

static int valid_element_pos(struct directive *d, int pos)
{
    int i = 0 ;
    
    for (i = 0; i < d->u.pattern.token_count; ++i) {
        if (valid_element(d, i)) --pos ;
        if (pos<0) return i ;
    }
    return -1 ;
}

static struct trie *build_trie(unsigned mode, struct directive *d1, struct trie *node)
{
    struct trie *l1 ;
    
    if (size==MAX_RULE_SIZE) return NULL ;
    
    if (d1->u.pattern.token_list[valid_element_pos(d1,size)].is_var &&
        size < valid_element_count(d1)) {
        char name[10] ;
        unsigned v, ov ;
        sprintf(name, "_var%d", size) ;
        v = _th_intern(name) ;
        ov = d1->u.pattern.token_list[valid_element_pos(d1,size)].u.var.variable ;
        if (v != ov) {
            struct _ex_unifier *u = _th_new_unifier(PARSE_SPACE) ;
            u = _th_add_pair(PARSE_SPACE, u, ov, _ex_intern_var(v)) ;
            d1->u.pattern.exp = _th_subst(NULL,u,d1->u.pattern.exp) ;
            d1->u.pattern.condition = _th_subst(NULL,u,d1->u.pattern.condition) ;
            d1->u.pattern.print_exp = _th_subst(NULL,u,d1->u.pattern.print_exp) ;
            d1->u.pattern.print_condition = _th_subst(NULL,u,d1->u.pattern.print_condition) ;
            d1->u.pattern.token_list[valid_element_pos(d1,size)].u.var.variable = v ;
        }
    }
    if (valid_element_count(d1) > size) {
        l1 = node ;
        while (l1 != NULL) {
            if (similar_elements(&l1->e, &d1->u.pattern.token_list[valid_element_pos(d1,size)])) {
                ++size ;
                l1->children = build_trie(mode,d1,l1->children) ;
                --size ;
                goto cont ;
            }
            l1 = l1->next ;
        }
        if (l1==NULL) {
            l1 = (struct trie *)_th_alloc(PARSE_SPACE, sizeof(struct trie)) ;
            l1->children = NULL ;
            l1->next = node ;
            l1->e = d1->u.pattern.token_list[valid_element_pos(d1,size)] ;
            node = l1 ;
            node->terminal = NULL ;
            ++size ;
            l1->children = build_trie(mode,d1,l1->children) ;
            --size ;
        }
    }
cont:
    if (valid_element_count(d1)==size+1) {
        l1->terminal = d1 ;
    }
    return node ;
}

static struct trie_l *find_trie(struct trie_l *l, unsigned mode)
{
    while (l != NULL) {
        if (l->mode==mode) return l ;
        l = l->next ;
    }
    
    return NULL ;
}

static struct trie_l *build_trie_list(struct directive *directive)
{
    struct directive *m, *d = directive ;
    struct trie_l *trie_l = NULL, *tl ;
    struct trie_l *trie ;
    
    while (d != NULL) {
        if (d->type==PARSE_PATTERN) {
            m = directive ;
            while (m != NULL) {
                if (m->type==PARSE_PERMIT && m->u.permit.rule==d->u.pattern.rule) {
                    trie = find_trie(trie_l, m->u.permit.mode) ;
                    if (trie==NULL) {
                        tl = (struct trie_l *)_th_alloc(PARSE_SPACE,sizeof(struct trie_l)) ;
                        tl->next = trie_l ;
                        tl->mode = m->u.permit.mode ;
                        trie = trie_l = tl ;
                        tl->trie = NULL ;
                        tl->terminal = NULL ;
                    }
                    /*printf("pattern: %s %s\n", _th_intern_decode(d->u.pattern.rule),
                    _th_intern_decode(m->u.permit.mode)) ;
                    for (i = 0; i < valid_element_count(d); ++i) {
                    char *s = _th_intern_decode(d->u.pattern.token_list[valid_element_pos(d,i)].u.var.variable) ;
                    if (d->u.pattern.token_list[valid_element_pos(d,i)].is_var) {
                    printf("    %d var %s\n", i, _th_intern_decode(d->u.pattern.token_list[valid_element_pos(d,i)].u.var.variable)) ;
                    } else {
                    printf("    %d %s\n", i, _th_intern_decode(d->u.pattern.token_list[valid_element_pos(d,i)].u.token)) ;
                    }
                }*/
                    trie->trie = build_trie(m->u.permit.mode,d,trie->trie) ;
                    if (valid_element_count(d)==0) trie->terminal = d ;
                }
                m = m->next ;
            }
        }
        d = d->next ;
    }
    
    return trie_l ;
}

static unsigned *vars ;
static unsigned vars_alloc = 0 ;

int _th_failx, _th_faily ;
#define UPDATE_FAIL(x,y) if (y > _th_faily || (y==_th_faily && x > _th_failx)) { _th_failx = x ; _th_faily = y ; }

static struct _ex_intern *parse(struct env *env, unsigned mode, struct trie_l *, unsigned *, int) ;

static void check_vars(unsigned size)
{
	if (size > vars_alloc) {
		unsigned va = vars_alloc ;
		vars_alloc = size + 100 ;
		if (va==0) {
			vars = (unsigned *)MALLOC(sizeof(unsigned) * vars_alloc) ;
		} else {
			vars = (unsigned *)REALLOC(vars, sizeof(unsigned) * vars_alloc) ;
		}
	}
}

static unsigned *parse_vars(int *pointer, int *count)
{
	*count = 0 ;
	while (1) {
		if (!_th_is_identifier(_th_tokens[*pointer])) return NULL ;
		check_vars(*count+1) ;
		vars[*count] = _th_tokens[*pointer] ;
		++*pointer ;
		++*count ;
		if (_th_tokens[*pointer] != INTERN_COMMA) return vars ;
		++*pointer ;
	}
}

struct _ex_intern_l {
	struct _ex_intern_l *next ;
	struct _ex_intern *e ;
} ;

static struct _ex_intern_l *parse_list(struct env *env, struct trie_l *trie, unsigned mode, unsigned *pointer,unsigned i)
{
    if (_th_tokens[*pointer]==INTERN_RIGHT_PAREN) {
        return NULL ;
    } else {
        struct _ex_intern_l *l = (struct _ex_intern_l *)_th_alloc(PARSE_SPACE,sizeof(struct _ex_intern_l)) ;
        _th_push_current(i) ;
        l->e = parse(env, mode, trie, pointer, 0) ;
        _th_pop_current() ;
        l->next = NULL ;
        if (_th_tokens[*pointer]!=INTERN_COMMA) {
            return l ;
        }
        ++*pointer ;
        l->next = parse_list(env, trie, mode, pointer, i+1) ;
        return l ;
    }
}

static struct _ex_intern *intern_appl_list(struct env *env, unsigned f, struct _ex_intern_l *list)
{
    unsigned count ;
    struct _ex_intern_l *l ;
    struct _ex_intern **args ;
    
    l = list ;
    count = 0 ;
    
    while (l != NULL) {
        ++count ;
        l = l->next ;
    }
    
    args = (struct _ex_intern **)ALLOCA(count * sizeof(struct _ex_intern *)) ;
    
    count = 0 ;
    while (list != NULL) {
        args[count++] = list->e ;
        list = list->next ;
    }
    
    return _ex_intern_appl_env(env,f,count,args) ;
}

static struct _ex_intern *intern_appl1_list(struct env *env, unsigned f, struct _ex_intern *first, struct _ex_intern_l *list)
{
    unsigned count ;
    struct _ex_intern_l *l ;
    struct _ex_intern **args ;
    
    l = list ;
    count = 0 ;
    
    while (l != NULL) {
        ++count ;
        l = l->next ;
    }
    
    ++count ;

    args = (struct _ex_intern **)ALLOCA(count * sizeof(struct _ex_intern *)) ;
    
    count = 0 ;
    args[count++] = first ;

    while (list != NULL) {
        args[count++] = list->e ;
        list = list->next ;
    }
    
    return _ex_intern_appl_env(env,f,count,args) ;
}

static struct _ex_intern *parse_default(struct env *env, struct trie_l *trie, unsigned mode, int *pointer)
{
    unsigned pfile = _th_file[*pointer] ;
    unsigned startx = _th_column[*pointer] ;
    unsigned starty = _th_row[*pointer] ;
    unsigned *vars, id ;
    int count ;
    struct _ex_intern *e, *p ;
    struct _ex_intern_l *l ;
    int index_save = _th_index_count ;
    int pointer_save = *pointer ;
    unsigned *lvs ;
    int i ;

    switch (_th_tokens[*pointer]) {
        
    case INTERN_EXISTS:
        ++*pointer ;
        if (_th_tokens[*pointer] != INTERN_LEFT_PAREN) goto cancel ;
        ++*pointer ;
        vars = parse_vars(pointer, &count) ;
        if (vars==NULL) goto cancel ;
        lvs = (unsigned *)ALLOCA(sizeof(unsigned) * count) ;
        for (i = 0; i < count; ++i) lvs[i] = vars[i] ;
        if (_th_tokens[*pointer] != INTERN_RIGHT_PAREN) goto cancel ;
        ++*pointer ;
        _th_push_current(0) ;
        e = parse(env, mode, trie, (int *)pointer, 0) ;
        _th_pop_current() ;
        if (e==NULL) goto cancel ;
        add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
        return _ex_intern_quant(INTERN_EXISTS,count,lvs,e,_ex_true) ;
        
    case INTERN_LAMBDA:
        ++*pointer ;
        if (_th_tokens[*pointer] != INTERN_LEFT_PAREN) goto cancel ;
        ++*pointer ;
        vars = parse_vars(pointer, &count) ;
        if (vars==NULL) goto cancel ;
        lvs = (unsigned *)ALLOCA(sizeof(unsigned) * count) ;
        for (i = 0; i < count; ++i) lvs[i] = vars[i] ;
        if (_th_tokens[*pointer] != INTERN_RIGHT_PAREN) goto cancel ;
        ++*pointer ;
        _th_push_current(0) ;
        e = parse(env, mode, trie, (unsigned *)pointer, 0) ;
        _th_pop_current() ;
        if (e==NULL) goto cancel ;
        add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
        return _ex_intern_quant(INTERN_LAMBDA,count,lvs,e,_ex_true) ;
        
    case INTERN_ALL:
        ++*pointer ;
        if (_th_tokens[*pointer] != INTERN_LEFT_PAREN) goto cancel ;
        ++*pointer ;
        vars = parse_vars(pointer, &count) ;
        if (vars==NULL) goto cancel ;
        lvs = (unsigned *)ALLOCA(sizeof(unsigned) * count) ;
        for (i = 0; i < count; ++i) lvs[i] = vars[i] ;
        p = _ex_true ;
        if (_th_tokens[*pointer] == INTERN_COLON) {
            ++*pointer ;
            _th_push_current(1) ;
            p = parse(env, INTERN_DEFAULT, trie, (unsigned *)pointer, 0) ;
            _th_pop_current() ;
            if (_th_tokens[*pointer]!=INTERN_RIGHT_PAREN) goto cancel ;
        } else if (_th_tokens[*pointer] != INTERN_RIGHT_PAREN) goto cancel ;
        ++*pointer ;
        _th_push_current(0) ;
        e = parse(env, mode, trie, (unsigned *)pointer, 0) ;
        _th_pop_current() ;
        if (e==NULL) goto cancel ;
        add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
        return _ex_intern_quant(INTERN_ALL,count,lvs,e,p) ;
        
    case INTERN_LEFT_BRACE:
        ++*pointer ;
        if (_th_tokens[*pointer]==INTERN_RIGHT_BRACE) {
            ++*pointer ;
            add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
            return _ex_intern_appl_env(env,INTERN_SET,0,NULL) ;
        }
        _th_push_current(0) ;
        e = parse(env, mode, trie, (unsigned *)pointer, 0) ;
        _th_pop_current() ;
        if (e==NULL) goto cancel ;
        switch (_th_tokens[*pointer]) {
        case INTERN_LEFT_BRACKET:
            ++*pointer ;
            vars = parse_vars(pointer, &count) ;
            if (vars==NULL) goto cancel ;
            lvs = (unsigned *)ALLOCA(sizeof(unsigned) * count) ;
            for (i = 0; i < count; ++i) lvs[i] = vars[i] ;
            if (_th_tokens[*pointer] != INTERN_RIGHT_BRACKET) goto cancel ;
            ++*pointer ;
            if (_th_tokens[*pointer] != INTERN_COLON) goto cancel ;
            ++*pointer ;
            _th_push_current(1) ;
            p = parse(env, mode, trie, (unsigned *)pointer, 0) ;
            _th_pop_current() ;
            if (_th_tokens[*pointer]!=INTERN_RIGHT_BRACE) goto cancel ;
            ++*pointer ;
            add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
            return _ex_intern_quant(INTERN_SETQ,count,lvs, e,p) ;
        case INTERN_RIGHT_BRACE:
            ++*pointer ;
            add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
            return _ex_intern_appl1_env(env,INTERN_SET,e) ;
        case INTERN_COMMA:
            ++*pointer ;
            l = parse_list(env, trie, mode, (unsigned *)pointer, INTERN_SET) ;
            if (_th_tokens[*pointer]!=INTERN_RIGHT_BRACE) goto cancel ;
            ++*pointer ;
            add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
            return intern_appl1_list(env, INTERN_SET, e, l)  ;
        default:
            goto cancel;
        }
    case INTERN_PERCENT:
        _th_push_current(0) ;
        ++*pointer ;
        l = parse_list(env, trie, mode, (unsigned *)pointer, 0) ;
        if (_th_tokens[*pointer]!=INTERN_PERCENT) goto cancel ;
        ++*pointer ;
        add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
        _th_pop_current() ;
        e = intern_appl_list(env,INTERN_CONCAT, l) ;

        i = *pointer ;

        if (_th_tokens[*pointer] != INTERN_LEFT_PAREN) goto cancel ;
        _th_push_current(1) ;
        ++*pointer ;
        l = parse_list(env, trie, mode, (unsigned *)pointer, 0) ;
        if (_th_tokens[*pointer]!=INTERN_RIGHT_PAREN) goto cancel ;
        ++*pointer ;
        add_index(pfile, _th_column[i], _th_row[i], _th_column[*pointer-1], _th_row[*pointer-1]) ;
        _th_pop_current() ;
        add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;

        return _ex_intern_appl2_env(env,INTERN_BUILD_FUNCTOR,
            e,
            intern_appl_list(env, INTERN_TUPLE, l)) ;
        break ;
    default:
        if (_th_is_string(_th_tokens[*pointer])) {
            char *t = _th_intern_decode(_th_tokens[*pointer]) ;
            char *s = (char *)ALLOCA(strlen(t)) ;
            strcpy(s, t+1) ;
            s[strlen(s)-1] = 0 ;
            ++*pointer ;
            add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
            return _ex_intern_string(s) ;
        } else if (_th_tokens[*pointer]==INTERN_MINUS && _th_is_number(_th_tokens[*pointer+1]) &&
            _th_tokens[*pointer+2]==INTERN_SLASH && _th_is_number(_th_tokens[*pointer+3])) {
            unsigned *x = _th_parse_number(_th_intern_decode(_th_tokens[*pointer+1])) ;
            unsigned *y = _th_parse_number(_th_intern_decode(_th_tokens[*pointer+3])) ;
            unsigned multiplier[2] = { 1, -1 } ;
            x = _th_big_multiply(x, multiplier) ;
            *pointer += 4 ;
            add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
            return _ex_intern_rational(x,y) ;
        } else if (_th_is_number(_th_tokens[*pointer]) && _th_tokens[*pointer+1]==INTERN_SLASH && _th_is_number(_th_tokens[*pointer+2])) {
            unsigned *x = _th_parse_number(_th_intern_decode(_th_tokens[*pointer])) ;
            unsigned *y = _th_parse_number(_th_intern_decode(_th_tokens[*pointer+2])) ;
            ++*pointer ;
            add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
            return _ex_intern_rational(x,y) ;
        } else if (_th_tokens[*pointer]==INTERN_MINUS && _th_is_number(_th_tokens[*pointer+1])) {
            unsigned *x = _th_parse_number(_th_intern_decode(_th_tokens[*pointer+1])) ;
            unsigned multiplier[2] = { 1, -1 } ;
            x = _th_big_multiply(x, multiplier) ;
            *pointer += 2 ;
            add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
            return _ex_intern_integer(x) ;
        } else if (_th_is_number(_th_tokens[*pointer])) {
            unsigned *x = _th_parse_number(_th_intern_decode(_th_tokens[*pointer])) ;
            ++*pointer ;
            add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
            return _ex_intern_integer(x) ;
        } else if (_th_tokens[*pointer]==0 || !_th_is_identifier(id = _th_tokens[*pointer])) {
            goto cancel ;
        }
        ++*pointer ;
        if (_th_tokens[*pointer]==INTERN_LEFT_PAREN) {
            ++*pointer ;
            l = parse_list(env, trie, mode, (unsigned *)pointer, 0) ;
            if (_th_tokens[*pointer]!=INTERN_RIGHT_PAREN) goto cancel ;
            ++*pointer ;
            add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
            return intern_appl_list(env, id, l)  ;
        } else if (_th_is_constructor(env, id)) {
            add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
            return _ex_intern_appl(id,0,NULL) ;
        } else {
            add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
            return _ex_intern_var(id) ;
        }
    }
cancel:
    UPDATE_FAIL(_th_column[*pointer],_th_row[*pointer]) ;
    _th_index_count = index_save ;
    *pointer = pointer_save ;
        
    return NULL ;
}

static void expand_indices(struct _ex_intern *e, int pos, int first, int last)
{
    int i, j ;
    
    switch (e->type) {
        
    case EXP_VAR:
        for (i = first; i < last; ++i) {
            if (((unsigned)_th_index[i][6+pos])== e->u.var) {
                _th_index[i] = (int *)REALLOC(_th_index[i], sizeof(unsigned) * (6 + _th_index[i][5]+current_count+5-pos)) ;
                if (current_count==pos) {
                    for (j = pos + 6; j < 5 + _th_index[i][5]; ++j) {
                        _th_index[i][j] = _th_index[i][j+1] ;
                    }
                } else {
                    for (j = 6 + _th_index[i][5] - current_count + pos; j >= pos && j!=0xffffffff; --j) {
                        _th_index[i][j+6+current_count-pos-1] = _th_index[i][j+6] ;
                    }
                    for (j = pos; j < current_count; ++j) {
                        _th_index[i][j+6] = current[j] ;
                    }
                }
                _th_index[i][5] += current_count - pos - 1;
            }
        }
        break ;
        
    case EXP_APPL:
        for (i = 0; i < e->u.appl.count; ++i) {
            _th_push_current(i) ;
            expand_indices(e->u.appl.args[i],pos,first,last);
            _th_pop_current() ;
        }
        break ;
        
    case EXP_CASE:
        _th_push_current(0) ;
        expand_indices(e->u.case_stmt.exp,pos,first,last) ;
        _th_pop_current() ;
        for (i = 0; i < e->u.case_stmt.count * 2; ++i) {
            _th_push_current(i+1) ;
            expand_indices(e->u.case_stmt.args[i],pos,first,last) ;
            _th_pop_current() ;
        }
        break ;
        
    case EXP_QUANT:
        _th_push_current(0) ;
        expand_indices(e->u.quant.cond,pos,first,last) ;
        _th_pop_current() ;
        _th_push_current(1) ;
        expand_indices(e->u.quant.exp,pos,first,last) ;
        _th_pop_current() ;
        break ;
    }
}

int ret_prec ;

static struct _ex_intern *parse_trie_no_prefix(struct env *env, unsigned mode, struct trie *trie, struct trie_l *trie_l, unsigned *pointer, int precedence, unsigned startp)
{
    unsigned pfile = _th_file[startp] ;
    unsigned startx = _th_column[startp] ;
    unsigned starty = _th_row[startp] ;
    struct _ex_intern *e,  *cond ;
    int index_save[MAX_RULE_SIZE] ;
    struct _ex_unifier *subst[MAX_RULE_SIZE] ;
    struct trie *trie_save[MAX_RULE_SIZE] ;
    struct trie_l *mode_trie = find_trie(trie_l, mode) ;
    unsigned pointer_save[MAX_RULE_SIZE] ;
    int pos = 0 ;
    struct trie *root_trie = trie ;
    
#ifdef DEBUG
    printf("Parsing at %d in mode %s\n", *pointer, _th_intern_decode(mode)) ;
#endif
    
    if (trie==NULL) return NULL ;
    
    index_save[0] = _th_index_count ;
    subst[0] = _th_new_unifier(PARSE_SPACE) ;
    trie_save[0] = trie ;
    pointer_save[0] = *pointer ;
    while(1) {
        while (trie==NULL) {
            UPDATE_FAIL(_th_column[*pointer],_th_row[*pointer]) ;
            if (pos > 0 && trie_save[pos-1]->terminal != NULL &&
                trie_save[pos-1]->terminal->u.pattern.precedence >= precedence) {
                e = trie_save[pos-1]->terminal->u.pattern.exp ;
                cond = trie_save[pos-1]->terminal->u.pattern.condition ;
                cond = _th_subst(env,subst[pos],cond) ;
#ifdef DEBUG
                printf("cond = %s\n", _th_print_exp(cond)) ;
#endif
                cond = _th_rewrite(env,cond) ;
                //printf("Done: %s\n", _th_print_exp(cond)) ;
                if (cond != _ex_true) goto cont2 ;
                expand_indices(e,current_count,index_save[0],_th_index_count) ;
                e = _th_subst(env,subst[pos],e) ;
                add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
                ret_prec =trie_save[pos-1]->terminal->u.pattern.precedence ;
#ifdef DEBUG
                printf("Success1 of mode %s\n", _th_intern_decode(mode)) ;
#endif
                return e ;
            }
cont2:
            if (pos==0) {
                if (mode_trie->terminal != NULL) {
#ifdef DEBUG
                    printf("Success2 of mode %s\n", _th_intern_decode(mode)) ;
#endif
                    add_index(pfile, startx, starty, startx, starty) ;
                    return mode_trie->terminal->u.pattern.exp ;
                } else {
#ifdef DEBUG
                    printf("Fail of mode %s\n", _th_intern_decode(mode)) ;
#endif
                    return NULL ;
                }
            }
#ifdef DEBUG
            printf("    Backing up to %d in mode %s\n", pos-1, _th_intern_decode(mode)) ;
#endif
            _th_index_count = index_save[--pos] ;
            *pointer = pointer_save[pos] ;
            trie = trie_save[pos] ;
            trie = trie->next ;
            trie_save[pos] = trie ;
        }
#ifdef DEBUG
        printf("    Parsing at %d %s %d %s\n", *pointer, _th_intern_decode(_th_tokens[*pointer]), pos, _th_intern_decode(mode)) ;
#endif
        if (trie->e.is_var) {
            if (pos > 0 || trie->e.u.var.mode != mode) {
#ifdef DEBUG
                printf("        Testing var %d %s %s\n", *pointer, _th_intern_decode(trie->e.u.var.variable), _th_intern_decode(trie->e.u.var.mode)) ;
#endif
                _th_push_current(trie->e.u.var.variable) ;
                e = parse(env,trie->e.u.var.mode,trie_l,pointer,trie->e.u.var.precedence) ;
                _th_pop_current() ;
                if (e != NULL) {
                    subst[pos+1] = _th_copy_unifier(PARSE_SPACE, subst[pos]) ;
                    _th_add_pair(PARSE_SPACE, subst[pos+1],trie->e.u.var.variable, e) ;
                    trie_save[pos] = trie ;
                    ++pos ;
                    index_save[pos] = _th_index_count ;
                    pointer_save[pos] = *pointer ;
                    trie = trie->children ;
                    goto cont ;
                }
            }
        } else {
#ifdef DEBUG
            printf("        Testing token %s\n",
                _th_intern_decode(trie->e.u.token)) ;
#endif
            if (trie->e.u.token==_th_tokens[*pointer]) {
                trie_save[pos] = trie ;
                subst[pos+1] = _th_copy_unifier(PARSE_SPACE, subst[pos]) ;
                ++pos ;
                index_save[pos] = _th_index_count ;
                pointer_save[pos] = *pointer ;
                ++*pointer ;
                trie = trie->children ;
                goto cont ;
            }
        }
        trie = trie->next ;
cont:
        trie_save[pos] = trie ;
    }
}

unsigned get_var(struct trie *trie)
{
    if (trie==NULL) return 0 ;
    if (trie->e.is_var) return trie->e.u.var.variable ;
    return get_var(trie->next) ;
}

static struct _ex_intern *parse_trie(struct env *env, unsigned mode, struct trie_l *trie_l, unsigned *pointer, int precedence)
{
    unsigned pfile = _th_file[*pointer] ;
    unsigned startx = _th_column[*pointer] ;
    unsigned starty = _th_row[*pointer] ;
    int pos ;
    int prec, max_prec ;
    struct trie *trie, *t, *ttop, *current ;
    struct trie_l *trie_l2 = find_trie(trie_l, mode) ;
    struct _ex_intern *e, *r ;
    int e_start, e_end ;
    unsigned startp = *pointer ;
    
    if (trie_l2==NULL) {
        trie = NULL ;
    } else {
        trie = trie_l2->trie ;
    }
    
    e_start = _th_index_count ;
    _th_push_current(get_var(trie)) ;
    e = parse_trie_no_prefix(env, mode, trie, trie_l, pointer, precedence, startp) ;
    if (e==NULL) {
        switch (mode) {
        case INTERN_DEFAULT:
        case INTERN_DEF:
            e = parse_default(env, trie_l, mode, (int *)pointer) ;
            break ;
        case INTERN_NATURAL:
            if (_th_is_number(_th_tokens[*pointer])) {
                unsigned *x = _th_parse_number(_th_intern_decode(_th_tokens[*pointer])) ;
                ++*pointer ;
                add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
                e = _ex_intern_integer(x) ;
            }
            break ;
        case INTERN_IDENTIFIER:
            if (_th_is_identifier(_th_tokens[*pointer])) {
                ++*pointer ;
                add_index(pfile, startx, starty, _th_column[*pointer-1], _th_row[*pointer-1]) ;
                e = _ex_intern_string(_th_intern_decode(_th_tokens[*pointer-1])) ;
            }
            break ;
        }
    }
    if (e==NULL) {
        _th_pop_current() ;
        return NULL ;
    }
    e_end = _th_index_count-1 ;
    
    pos = 0 ;
    max_prec = 10001 ;
    current = NULL ;
    while (1) {
        ttop = NULL ;
        if (current == NULL) {
#ifdef DEBUG
            printf("current == NULL\n") ;
#endif
            t = trie ;
            prec = -1 ;
            while (t != NULL) {
#ifdef DEBUG
                printf("Trie: ") ;
                if (t->e.is_var) {
                    printf("var %s %s\n", _th_intern_decode(t->e.u.var.variable),
                        _th_intern_decode(t->e.u.var.mode)) ;
                } else {
                    printf("const %s\n", _th_intern_decode(t->e.u.token)) ;
                }
#endif
                if (t->e.is_var && t->e.u.var.mode==mode) {
#ifdef DEBUG
                    printf("Testing a trie %d\n", t->e.u.var.precedence) ;
                    printf("    %d %d %d\n", prec, precedence, max_prec) ;
#endif
                    if (t->e.u.var.precedence >= precedence &&
                        t->e.u.var.precedence > prec &&
                        t->e.u.var.precedence <= max_prec) {
                        ttop = t ;
                        prec = t->e.u.var.precedence ;
                    }
                }
                t = t->next ;
            }
        } else {
#ifdef DEBUG
            printf("current != NULL\n") ;
#endif
            t = current->next ;
            ttop = NULL ;
            while (t != NULL) {
#ifdef DEBUG
                printf("Trie: ") ;
                if (t->e.is_var) {
                    printf("var %s %s\n", _th_intern_decode(t->e.u.var.variable),
                        _th_intern_decode(t->e.u.var.mode)) ;
                } else {
                    printf("const %s\n", _th_intern_decode(t->e.u.token)) ;
                }
#endif
                if (t->e.is_var && t->e.u.var.mode==mode &&
                    t->e.u.var.precedence==current->e.u.var.precedence) {
#ifdef DEBUG
                    printf("Setting ttop\n") ;
#endif
                    ttop = t ;
                    prec = t->e.u.var.precedence ;
                }
                t = t->next ;
            }
            if (ttop==NULL) {
                t = trie ;
                prec = -1 ;
                while (t != NULL) {
                    if (t->e.is_var && t->e.u.var.mode==mode) {
                        if (t->e.u.var.precedence > prec &&
                            t->e.u.var.precedence >= precedence &&
                            t->e.u.var.precedence <= max_prec &&
                            t->e.u.var.precedence < current->e.u.var.precedence) {
                            ttop = t ;
                            prec = t->e.u.var.precedence ;
                        }
                    }
                    t = t->next ;
                }
            }
        }
        if (ttop==NULL) {
            _th_pop_current() ;
            expand_indices(_ex_intern_var(get_var(trie)),current_count,e_start,_th_index_count) ;
            return e ;
        }
        current = ttop ;
        r = parse_trie_no_prefix(env, mode, current->children,
            trie_l, pointer, precedence, startp) ;
        if (r != NULL) {
            struct _ex_unifier *u = _th_new_unifier(PARSE_SPACE) ;
            u = _th_add_pair(PARSE_SPACE, u, ttop->e.u.var.variable, e) ;
            expand_indices(r, current_count-1, e_start, e_end+1) ;
            r = _th_subst(env, u, r) ;
            e = r ;
            e_end = _th_index_count - 1 ;
            max_prec = ret_prec ;
            current = NULL ;
        }
    }
}

static struct _ex_intern *parse(struct env *env, unsigned mode, struct trie_l *trie, unsigned *pointer, int precedence)
{
	return parse_trie(env,mode,trie,pointer,precedence) ;
}

struct _ex_intern *_th_pp_parse(char *file, struct env *env, char *text)
{
    unsigned pointer = 0 ;
    struct trie_l *trie = _th_get_trie(env) ;
    struct _ex_intern *res ;
    char *mark ;
    
    if (trie==NULL) {
        mark = _th_get_mark() ;
        if (mark != NULL) _th_alloc_release(PARSE_SPACE,mark) ;
        mark = _th_alloc_mark(PARSE_SPACE) ;
        trie = build_trie_list(_th_get_pp_directives(env)) ;
        _th_set_trie_mark(env,trie,mark) ;
    }
    mark = _th_alloc_mark(PARSE_SPACE) ;
#ifdef DEBUG
    _print_trie_l(trie) ;
    printf("string: %s\n", text) ;
#endif
    _th_failx = _th_faily = 0 ;
    _th_tokenize_string(text, file) ;
    free_index() ;
    res = parse(env, INTERN_DEFAULT, trie, &pointer, 0) ;
    _th_alloc_release(PARSE_SPACE,mark) ;
    return res ;
}

struct _ex_intern *_th_pp_parse_mode(char *file, struct env *env, unsigned mode, char *text)
{
    unsigned pointer = 0 ;
    struct trie_l *trie = _th_get_trie(env) ;
    struct _ex_intern *res ;
    char *mark ;
#ifdef DEBUG
    _print_trie_l(trie) ;
    printf("string: %s\n", text) ;
#endif
    if (trie==NULL) {
        mark = _th_get_mark() ;
        if (mark != NULL) _th_alloc_release(PARSE_SPACE,mark) ;
        mark = _th_alloc_mark(PARSE_SPACE) ;
        trie = build_trie_list(_th_get_pp_directives(env)) ;
        _th_set_trie_mark(env,trie,mark) ;
    }
    mark = _th_alloc_mark(PARSE_SPACE) ;
    _th_failx = _th_faily = 0 ;
    _th_tokenize_string(text, file) ;
    free_index() ;
    res = parse(env, mode, trie, &pointer, 0) ;
    _th_alloc_release(PARSE_SPACE,mark) ;
    return res ;
}

static int currentx, currenty ;

#define print_string(buffer,limit,s) \
    { if (strlen(s) >= (unsigned)*limit) return 0 ; \
      strcpy(*buffer,s) ; \
      (*limit)-=strlen(s) ; \
      currentx += strlen(s) ; \
      (*buffer)+=strlen(s) ; }

#define print_char(buffer,limit,c) \
    { if (*limit < 1) return 0 ; \
      *(*buffer)++ = c ; \
      ++currentx ; \
      --*limit ; }

#define print_small_number(buffer,limit,n) \
    { if (*limit < 15) return 0 ; \
      sprintf(*buffer,"%d",n) ; \
      (*limit) -= strlen(*buffer) ; \
      currentx += strlen(*buffer) ; \
      (*buffer) += strlen(*buffer) ; }

static int print_number(char **buffer, unsigned *limit, unsigned *n)
{
    unsigned ten[] = { 1, 10 } ;
    unsigned zero[] = { 1, 0 } ;
    char s ;
    int i ;
    unsigned *digit ;
    char *start ;

    if (*n * 10 + 5 > *limit) return 0 ;

    if (_th_big_is_negative(n)) {
        n = _th_big_copy(PARSE_SPACE,_th_big_sub(zero,n)) ;
        **buffer = '-' ;
        ++*buffer ;
        ++currentx ;
        if (*limit==0) return 0 ;
        --*limit ;
    }
    if (n[0]==1&&n[1]==0) {
        **buffer = '0' ;
        ++*buffer ;
        ++currentx ;
        if (*limit==0) return 0 ;
        --*limit ;
        return 1 ;
    }
    start = *buffer ;
    while (n[0] != 1 || n[1] != 0) {
        digit = _th_big_mod(n,ten) ;
        **buffer = digit[1] + '0' ;
        ++*buffer ;
        ++currentx ;
        if (*limit==0) return 0 ;
        --*limit ;
        n = _th_big_copy(PARSE_SPACE,_th_big_divide(n,ten)) ;
    }
    for (i = 0; i < (*buffer - start) / 2; ++i) {
        s = start[i] ;
        start[i] = start[*buffer - start - i - 1] ;
        start[*buffer - start - i - 1] = s ;
    }
    return 1 ;
}

#define mprint_string(s) \
    { _th_pp_adjust_buffer(strlen(s)) ; \
      currentx += strlen(s) ; \
      strcpy(_th_pp_print_buf+_th_pp_pos,s) ; \
      _th_pp_pos+=strlen(s) ; }

#define mprint_char(c) \
    { _th_pp_adjust_buffer(1) ; \
      ++currentx ; \
      _th_pp_print_buf[_th_pp_pos++] = c ; }

#define mprint_small_number(buffer,limit,n) \
    { _th_pp_adjust_buffer(15) ; \
      sprintf(_th_pp_print_buf+_th_pp_pos,"%d",n) ; \
      currentx += strlen(_th_pp_print_buf+_th_pp_pos) ; \
      _th_pp_pos += strlen(_th_pp_print_buf+_th_pp_pos) ; }

int push_exp_index(struct _ex_intern *e, unsigned v)
{
    int i, res ;

    switch (e->type) {
    case EXP_VAR:
        if (e->u.var==v) return 0 ;
        return -1 ;
    case EXP_APPL:
        for (i = 0; i < e->u.appl.count; ++i) {
            _th_push_current(i) ;
            res = push_exp_index(e->u.appl.args[i],v) ;
            if (res >= 0) return res+1 ;
            _th_pop_current() ;
        }
        return -1 ;
    case EXP_QUANT:
        _th_push_current(0) ;
        res = push_exp_index(e->u.quant.exp, v) ;
        if (res >= 0) return res+1 ;
        _th_pop_current() ;
        _th_push_current(1) ;
        res = push_exp_index(e->u.quant.cond, v) ;
        if (res >= 0) return res+1 ;
        _th_pop_current() ;
        return -1 ;
    case EXP_INDEX:
        _th_push_current(0) ;
        res = push_exp_index(e->u.index.exp, v) ;
        if (res >= 0) return res+1 ;
        _th_pop_current() ;
        return -1 ;
    case EXP_CASE:
        _th_push_current(0) ;
        res = push_exp_index(e->u.case_stmt.exp, v) ;
        if (res >= 0) return res+1 ;
        _th_pop_current() ;
        for (i = 0; i < e->u.case_stmt.count*2; ++i) {
            _th_push_current(i+1) ;
            res = push_exp_index(e->u.case_stmt.exp, v) ;
            if (res >= 0) return res+1 ;
            _th_pop_current() ;
        }
        return -1 ;
    default:
        return -1 ;
    }
}

static int _print_vars(char **buffer, int *width, struct _ex_intern *e)
{
    int i ;

    for (i = 0; i < e->u.quant.var_count; ++i) {
        char *sym ;
        sym = _th_intern_decode(e->u.quant.vars[i]) ;
        print_string(buffer,width,sym) ;
        if (i < e->u.quant.var_count-1) print_char(buffer,width,',') ;
    }

    return 1 ;
}

static int _mprint_vars(struct _ex_intern *e)
{
    int i ;

    for (i = 0; i < e->u.quant.var_count; ++i) {
        char *sym ;
        sym = _th_intern_decode(e->u.quant.vars[i]) ;
        mprint_string(sym) ;
        if (i < e->u.quant.var_count-1) mprint_char(',') ;
    }

    return 1 ;
}

static int rule_permitted_in_mode(unsigned mode, struct directive *rule)
{
    struct directive *d = rule->u.pattern.permits ;
    while (d != NULL) {
        if (d->u.permit.rule==rule->u.pattern.rule && d->u.permit.mode==mode) {
            return 1 ;
        }
        d = d->u.permit.next ;
    }

    return 0 ;
}

static struct directive *find_pattern(struct directive *list, unsigned rule)
{
    while (list != NULL) {
        if (list->type==PARSE_BREAK && list->u.parse_break.rule==rule) return list ;
        list = list->next ;
    }
    return NULL ;
}

static int is_mode_rule(struct directive *rule, unsigned mode)
{
    int i ;

    if (rule->u.pattern.exp->type != EXP_VAR) return 0 ;

    for (i = 0; i < rule->u.pattern.token_count; ++i) {
        if (rule->u.pattern.token_list[i].is_var &&
            rule->u.pattern.token_list[i].u.var.mode != mode) return 1 ;
    }

    return 0 ;
}

static int is_paren_rule(struct directive *rule, unsigned mode)
{
    int i ;

    if (rule->u.pattern.exp->type != EXP_VAR) return 0 ;

    for (i = 0; i < rule->u.pattern.token_count; ++i) {
        if (rule->u.pattern.token_list[i].is_var &&
            rule->u.pattern.token_list[i].u.var.mode != mode) return 0 ;
    }

    return 1 ;
}

static int _print_one_line(struct env *env, unsigned mode, int prec, char **buffer, int *width, struct _ex_intern *e) ;

static int _print_one_line_rule(struct env *env, unsigned mode, int prec, char **buffer, int *width, struct _ex_intern *e)
{
    struct directive *d = _th_get_pp_directives(env) ;
    struct directive *dir = d ;
    int res, depth ;
    int term ;
    int startx = currentx ;
    int starty = currenty ;

    if (e==NULL) return -1 ;

    //printf("Rule print %s %s %d\n", _th_print_exp(e), _th_intern_decode(mode), prec) ;

    while (d != NULL) {
        if ((d->type==PRINT_PATTERN || d->type==PARSE_PATTERN) &&
            !is_paren_rule(d,mode) &&
            (!is_mode_rule(d,mode) || d->u.pattern.print_condition != _ex_true) &&
            rule_permitted_in_mode(mode,d)) {
            //printf("    Testing rule %s %d\n", _th_print_exp(d->u.pattern.print_exp), d->u.pattern.precedence) ;
            if (e->type==EXP_APPL &&
                _th_is_ac(env,e->u.appl.functor) &&
                d->u.pattern.print_exp->type==EXP_APPL &&
                d->u.pattern.print_exp->u.appl.functor==e->u.appl.functor &&
                d->u.pattern.print_exp->u.appl.count==2 &&
                d->u.pattern.print_exp->u.appl.args[0]->type==EXP_VAR &&
                d->u.pattern.print_exp->u.appl.args[1]->type==EXP_VAR) {
                int i, begin ;
                struct _ex_intern *expa, *expb, *exp ;
                unsigned va, vb ;
                int pos ;

                //printf("        AC-match\n") ;
                if (d->u.pattern.precedence < prec) goto paren_case ;

                //printf("Here b %s\n", _th_intern_decode(d->u.pattern.rule)) ;
                va = d->u.pattern.print_exp->u.appl.args[0]->u.var ;
                vb = d->u.pattern.print_exp->u.appl.args[1]->u.var ;
                expa = e->u.appl.args[0] ;
                expb = e->u.appl.args[1] ;
                begin = -1 ;
                pos = 1 ;
                //printf("Using rule %s for %s\n", _th_intern_decode(d->u.pattern.rule), _th_print_exp(e)) ;
                //fflush(stdout) ;
                //char *start = *buffer ;
                //printf("Rule %s for %s\n", _th_intern_decode(d->u.pattern.rule), _th_intern_decode(e->u.appl.functor)) ;
                for (i = 0; i < d->u.pattern.token_count; ++i) {
                    //printf("i, begin, pos = %d %d %d\n", i, begin, pos) ;
                    if (d->u.pattern.token_list[i].is_var) {
                        //printf("Here1 %d %s\n", *width, _th_print_exp(_th_apply(u,d->u.pattern.token_list[i].u.var.variable))) ;
                        //fflush(stdout) ;
                        
                        if (d->u.pattern.token_list[i].u.var.variable != 0) {
                            if (d->u.pattern.token_list[i].u.var.variable==va) {
                                exp = expa ;
                                term = 0 ;
                            } else {
                                exp = expb ;
                                term = pos ;
                            }
                            _th_push_current(term) ;
                            res = _print_one_line(env,
                                d->u.pattern.token_list[i].u.var.mode,
                                d->u.pattern.token_list[i].u.var.precedence,
                                buffer,
                                width,
                                exp) ;
                            _th_pop_current() ;
                            if (!res) return 0 ;
                        } else {
                            if (begin==-1) {
                                begin = i ;
                            } else {
                                ++pos ;
                                if (pos < e->u.appl.count) {
                                    expb = e->u.appl.args[pos] ;
                                    i = begin ;
                                }
                            }
                        }
                    } else {
                        char *t = _th_intern_decode(d->u.pattern.token_list[i].u.token) ;
                        //printf("Here2 %d '%s'\n", *width, t) ;
                        //fflush(stdout) ;
                        print_string(buffer,width,t) ;
                    }
                }
                //**buffer = 0 ;
                //printf("good printout of %s\n", start) ;
                add_index(0,startx,starty,currentx,currenty) ;
                return 1 ;
            } else {
                struct match_return *mr ;
                mr = _th_match(env,d->u.pattern.print_exp,e) ;
                while (mr != NULL) {
                    struct _ex_unifier *u = mr->theta ;
                    int i ;
                    struct _ex_intern *cond = _th_subst(env, u, d->u.pattern.print_condition) ;
                    //printf("cond = %s\n", _th_print_exp(cond)) ;
                    cond = _th_rewrite(env,cond) ;
                    //printf("Done: %s\n", _th_print_exp(cond)) ;
                    if (cond != _ex_true) goto cont ;
                    //printf("        non-AC match\n") ;

                    if (d->u.pattern.precedence < prec) goto paren_case ;
                    
                    for (i = 0; i < d->u.pattern.token_count; ++i) {
                        if (d->u.pattern.token_list[i].is_var) {
                            //printf("            Var position %s %d %s %s\n",
                            //    _th_intern_decode(d->u.pattern.token_list[i].u.var.mode),
                            //    d->u.pattern.token_list[i].u.var.precedence,
                            //    _th_intern_decode(d->u.pattern.token_list[i].u.var.variable),
                            //    _th_print_exp(_th_apply(u,d->u.pattern.token_list[i].u.var.variable))) ;
                            if (d->u.pattern.token_list[i].u.var.variable != 0) {
                                depth = push_exp_index(d->u.pattern.print_exp,d->u.pattern.token_list[i].u.var.variable) ;
                                res = _print_one_line(env,
                                    d->u.pattern.token_list[i].u.var.mode,
                                    d->u.pattern.token_list[i].u.var.precedence,
                                    buffer,
                                    width,
                                    _th_apply(u,d->u.pattern.token_list[i].u.var.variable)) ;
                                while (depth-- > 0) _th_pop_current() ;
                                if (!res) return 0 ;
                            }
                        } else {
                            char *t = _th_intern_decode(d->u.pattern.token_list[i].u.token) ;
                            print_string(buffer,width,t) ;
                        }
                    }
                    add_index(0,startx,starty,currentx,currenty) ;
                    return 1 ;
cont:
                    mr = mr->next ;
                }
            }
        }
        d = d->next ;
    }

    //printf("No rule\n") ;
    return 0 ;

paren_case:
    d = dir ;
    //printf("Case 3 %s\n", _th_print_exp(e)) ;
    if (mode==INTERN_DEFAULT) {
        print_string(buffer,width,"(") ;
        if (!_print_one_line(env,INTERN_DEFAULT,0,buffer,width,e)) return 0 ;
        print_string(buffer,width,")") ;
        return 1 ;
    } else {
        while (d != NULL) {
            //printf("    Checking if paren rule %s %s\n", _th_intern_decode(d->u.pattern.rule),
            //       _th_print_exp(d->u.pattern.print_exp)) ;
            if ((d->type==PRINT_PATTERN || d->type==PARSE_PATTERN) &&
                is_paren_rule(d,mode) &&
                rule_permitted_in_mode(mode,d)) {
                int i ;
                
                //printf("Using rule %s for %s\n", _th_intern_decode(d->u.pattern.rule), _th_print_exp(e)) ;
                //char *start = *buffer ;
                for (i = 0; i < d->u.pattern.token_count; ++i) {
                    //printf("i = %d\n", i) ;
                    //if (d->u.pattern.token_list[i].is_var) {
                        //printf("Here1 %d %s\n", *width, _th_print_exp(_th_apply(u,d->u.pattern.token_list[i].u.var.variable))) ;
                        //fflush(stdout) ;
                        if (d->u.pattern.token_list[i].is_var &&
                            d->u.pattern.token_list[i].u.var.variable != 0) {
                            //printf("Printing %s %d\n",
                            //    _th_intern_decode(d->u.pattern.token_list[i].u.var.mode),
                            //    d->u.pattern.token_list[i].u.var.precedence);
                            if (!_print_one_line(env,
                                d->u.pattern.token_list[i].u.var.mode,
                                d->u.pattern.token_list[i].u.var.precedence,
                                buffer,
                                width,
                                e)) return 0 ;
                        } else {
                            char *t = _th_intern_decode(d->u.pattern.token_list[i].u.token) ;
                            //printf("Here2 %d '%s'\n", *width, t) ;
                            //fflush(stdout) ;
                            print_string(buffer,width,t) ;
                        }
                    //}
                }
                //**buffer = 0 ;
                //printf("good printout of %s\n", start) ;
                add_index(0,startx,starty,currentx,currenty) ;
                return 1 ;
            }
            d = d->next ;
        }
    }
    return 0 ;
}

static int _print_one_line_default(struct env *env, int prec, char **buffer, int *width, struct _ex_intern *e)
{
    char *p ;
    char *sym ;
    int i, res ;
    int startx = currentx ;
    int starty = currenty ;

    if (e==NULL) {
        print_string(buffer,width,"<NULL>") ;
        return 1 ;
    }

    switch (e->type) {

        case EXP_INTEGER:
            if (!print_number(buffer, (unsigned *)width, e->u.integer)) return 0 ;
            break ;

        case EXP_RATIONAL:
            if (!print_number(buffer, (unsigned *)width, e->u.rational.numerator)) return 0 ;
            print_char(buffer,width,'/') ;
            if (!print_number(buffer, (unsigned *)width, e->u.rational.denominator)) return 0 ;
            break ;

        case EXP_STRING:
            p = e->u.string ;
            print_char(buffer,width,'"') ;
            while(*p) {
                switch (*p) {
                    case '"':
                        if (*width < 2) return 0 ;
                        *width -= 2 ;
                        *(*buffer)++ = '\\' ;
                        *(*buffer)++ = '"' ;
                        currentx += 2 ;
                        break ;
                    case '\\':
                        if (*width < 2) return 0 ;
                        *width -= 2 ;
                        *(*buffer)++ = '\\' ;
                        *(*buffer)++ = '\\' ;
                        currentx += 2 ;
                        break ;
                    case '\n':
                        if (*width < 2) return 0 ;
                        *width -= 2 ;
                        *(*buffer)++ = '\\' ;
                        *(*buffer)++ = 'n' ;
                        currentx += 2 ;
                        break ;
                    case '\r':
                        if (*width < 2) return 0 ;
                        *width -= 2 ;
                        *(*buffer)++ = '\\' ;
                        *(*buffer)++ = 'r' ;
                        currentx += 2 ;
                        break ;
                    case '\t':
                        if (*width < 2) return 0 ;
                        *width -= 2 ;
                        *(*buffer)++ = '\\' ;
                        *(*buffer)++ = 't' ;
                        currentx += 2 ;
                        break ;
                    default:
                        print_char(buffer,width,*p) ;
                }
                ++p ;
            }
            print_char(buffer,width,'"') ;
            break ;

        case EXP_VAR:
            sym = _th_intern_decode(e->u.var) ;
            print_string(buffer,width,sym) ;
            break ;

        case EXP_MARKED_VAR:
            sym = _th_intern_decode(e->u.marked_var.var) ;
            print_string(buffer,width,sym) ;
            print_char(buffer,width,'\'') ;
            if (e->u.marked_var.quant_level != 0) {
                print_small_number(buffer,width,e->u.marked_var.quant_level) ;
                print_char(buffer,width,'\'') ;
            }
            break ;

        case EXP_APPL:
            sym = _th_intern_decode(e->u.appl.functor) ;
            print_string(buffer,width,sym) ;
            print_char(buffer,width,'(') ;
            for (i = 0; i < e->u.appl.count; ++i) {
                if (i > 0) print_char(buffer,width,',') ;
                _th_push_current(i) ;
                if (!_print_one_line(env, INTERN_DEFAULT, 0, buffer, width, e->u.appl.args[i])) {
                    _th_pop_current() ;
                    return 0 ;
                }
                _th_pop_current() ;
            }
            print_char(buffer,width,')') ;
            break ;

        case EXP_CASE:
            print_string(buffer,width,"case ") ;
            _th_push_current(0) ;
            res = _print_one_line(env, INTERN_DEFAULT, 0, buffer, width, e->u.case_stmt.exp) ;
            _th_pop_current() ;
            if (!res) return 0 ;
            for (i = 0; i < e->u.case_stmt.count; ++i) {
                if (i==0) {
                    print_string(buffer,width," of ") ;
                } else {
                    print_char(buffer,width,'|') ;
                }
                _th_push_current(i*2+1) ;
                res = _print_one_line(env, INTERN_DEFAULT, 0, buffer, width, e->u.case_stmt.args[i*2]) ;
                _th_pop_current() ;
                if (!res) return 0 ;
                print_char(buffer,width,':') ;
                _th_push_current(i*2+2) ;
                res = _print_one_line(env, INTERN_DEFAULT, 0,buffer, width, e->u.case_stmt.args[i*2+1]) ;
                _th_pop_current() ;
                if (!res) return 0 ;
            }
            break ;

        case EXP_INDEX:
            print_string(buffer,width,"INDEX(") ;
            _th_push_current(0) ;
            res = _print_one_line(env, INTERN_DEFAULT, 0, buffer, width, e->u.index.exp) ;
            _th_pop_current() ;
            if (!res) return 0 ;
            print_char(buffer,width,',') ;
            sym = _th_intern_decode(e->u.index.functor) ;
            print_string(buffer,width,sym) ;
            print_char(buffer,width,',') ;
            print_small_number(buffer,width,e->u.index.term) ;
            print_char(buffer,width,')') ;
            break ;

        case EXP_QUANT:
            switch (e->u.quant.quant) {
                 case INTERN_ALL:
                     print_string(buffer,width,"ALL (") ;
                     if (!_print_vars(buffer,width,e)) return 0 ;
                     if (e->u.quant.cond != _ex_true) {
                         print_string(buffer,width," : ") ;
                         _th_push_current(1) ;
                         res = _print_one_line(env, INTERN_DEFAULT, 0, buffer, width, e->u.quant.cond) ;
                         _th_pop_current() ;
                         if (!res) return 0 ;
                     }
                     print_string(buffer,width,") ") ;
                     _th_push_current(0) ;
                     res = _print_one_line(env, INTERN_DEFAULT, 0, buffer, width, e->u.quant.exp) ;
                     _th_pop_current() ;
                     if (!res) return 0 ;
                     break ;

                 case INTERN_EXISTS:
                     print_string(buffer,width,"EXISTS (") ;
                     if (!_print_vars(buffer,width,e)) return 0 ;
                     print_string(buffer, width, ") ") ;
                     _th_push_current(0) ;
                     res = _print_one_line(env, INTERN_DEFAULT, 0, buffer, width, e->u.quant.exp) ;
                     _th_pop_current() ;
                     if (!res) return 0 ;
                     break ;

                 case INTERN_SETQ:
                     print_string(buffer,width,"{ ") ;
                     _th_push_current(0) ;
                     res = _print_one_line(env, INTERN_DEFAULT, 0, buffer, width, e->u.quant.exp) ;
                     _th_pop_current() ;
                     if (!res) return 0 ;
                     print_string(buffer,width," [") ;
                     if (!_print_vars(buffer,width,e)) return 0 ;
                     print_string(buffer,width,"] ") ;
                     if (e->u.quant.cond != _ex_true) {
                         print_string(buffer,width,": ") ;
                         _th_push_current(1) ;
                         res = _print_one_line(env, INTERN_DEFAULT, 0, buffer, width, e->u.quant.cond) ;
                         _th_pop_current() ;
                         if (!res) return 0 ;
                     }
                     print_string(buffer,width," }") ;
                     break ;

                 case INTERN_LAMBDA:
                     print_string(buffer,width,"lambda (") ;
                     if (!_print_vars(buffer,width,e)) return 0 ;
                     print_string(buffer,width,") ") ;
                     _th_push_current(0) ;
                     res = _print_one_line(env, INTERN_DEFAULT, 0, buffer, width, e->u.quant.exp) ;
                     _th_pop_current() ;
                     if (!res) return 0 ;
                     break ;
                 default:
                     print_string(buffer,width,"<quant printing error>") ;
                     break ;

            }
            break ;
        default:
            print_string(buffer,width,"<printing error>") ;
    }
    add_index(0,startx,starty,currentx,currenty) ;
    return 1;
}

static int _print_one_line(struct env *env, unsigned mode, int prec, char **buffer, int *width, struct _ex_intern *e)
{
    int res ;
    char *ms = _th_alloc_mark(MATCH_SPACE) ;
    int x = currentx ;
    int y = currenty ;
    char *m = *buffer ;
    int index_count = _th_index_count ;

    //printf("Printing %s %s\n", _th_intern_decode(mode), _th_print_exp(e)) ;

    res = _print_one_line_rule(env,mode,prec,buffer,width,e) ;

    _th_alloc_release(MATCH_SPACE,ms) ;

    if (res > 0) return res ;

    _th_index_count = index_count ;
    currentx = x ;
    currenty = y ;
    *buffer = m ;

    if (mode==INTERN_DEFAULT || mode==INTERN_DEF) {
        if (_print_one_line_default(env, prec, buffer, width, e)) {
            return 1 ;
        } else {
            _th_index_count = index_count ;
            currentx = x ;
            currenty = y ;
        }
    } else if (mode==INTERN_IDENTIFIER) {
        if (e->type==EXP_STRING) {
            print_string(buffer,width,e->u.string);
            return 1;
        }
    } else if (mode==INTERN_NATURAL) {
        if (e->type==EXP_INTEGER) {
            return print_number(buffer,(unsigned *)width,e->u.integer);
        }
    }

    return 0 ;
}

static int indent_factor = 2 ;

static void indent(int indent)
{
    int i = indent_factor * indent ;

    _th_pp_adjust_buffer(i) ;
    while(i--) _th_pp_print_buf[_th_pp_pos++] = ' ' ;
}

static void cr_indent(int ind)
{
    _th_pp_adjust_buffer(1) ;
    _th_pp_print_buf[_th_pp_pos++] = '\n' ;
    indent(ind) ;

    ++currenty ;
    currentx = ind * indent_factor ;
}

static int _pp_print(struct env *env, int ind, unsigned mode, unsigned prec, int width, struct _ex_intern *e) ;

int has_markers(struct directive *d)
{
    int i ;
    int mcount = 0 ;

    for (i = 0; i < d->u.pattern.token_count; ++i) {
        if (d->u.pattern.token_list[i].is_var && d->u.pattern.token_list[i].u.var.variable==0) ++mcount ;
    }
    return (mcount==2) ;
}

static int _pp_print_rule(struct env *env, int ind, unsigned mode, int prec, int width, struct _ex_intern *e)
{
    struct directive *d = _th_get_pp_directives(env) ;
    struct directive *dir = d ;
    int pass_ind = ind ;
    int res, depth, term ;
    int startx = currentx ;
    int starty = currenty ;

    if (e==NULL) return -1 ;

    while (d != NULL) {
        int pos_save = _th_pp_pos ;
        if ((d->type==PRINT_PATTERN || d->type==PARSE_PATTERN) &&
            !is_paren_rule(d,mode) &&
            (!is_mode_rule(d,mode) || d->u.pattern.print_condition != _ex_true) &&
            rule_permitted_in_mode(mode,d)) {
            if (e->type==EXP_APPL &&
                _th_is_ac(env,e->u.appl.functor) &&
                d->u.pattern.print_exp->type==EXP_APPL &&
                d->u.pattern.print_exp->u.appl.functor==e->u.appl.functor &&
                d->u.pattern.print_exp->u.appl.count==2 &&
                d->u.pattern.print_exp->u.appl.args[0]->type==EXP_VAR &&
                d->u.pattern.print_exp->u.appl.args[1]->type==EXP_VAR &&
                has_markers(d) &&
                e->u.appl.count > 1) {
                int i, begin ;
                struct _ex_intern *expa, *expb, *exp ;
                unsigned va, vb ;
                int pos ;
                struct directive *breaks = find_pattern(dir, d->u.pattern.rule) ;

                if (d->u.pattern.precedence < prec) goto paren_case ;

                //printf("Here b %s\n", _th_intern_decode(d->u.pattern.rule)) ;
                va = d->u.pattern.print_exp->u.appl.args[0]->u.var ;
                vb = d->u.pattern.print_exp->u.appl.args[1]->u.var ;
                expa = e->u.appl.args[0] ;
                expb = e->u.appl.args[1] ;
                begin = -1 ;
                pos = 1 ;
                //printf("Using rule %s for %s\n", _th_intern_decode(d->u.pattern.rule), _th_print_exp(e)) ;
                //fflush(stdout) ;
                //char *start = *buffer ;
                //printf("Rule %s for %s\n", _th_intern_decode(d->u.pattern.rule), _th_intern_decode(e->u.appl.functor)) ;
                for (i = 0; i < d->u.pattern.token_count; ++i) {
                    if (breaks != NULL) {
                        if (breaks->u.parse_break.list[i].break_mode==OPTIONAL_BREAK ||
                            breaks->u.parse_break.list[i].break_mode==REQUIRED_BREAK) {
                            pass_ind = breaks->u.parse_break.list[i].indent+ind ;
                            cr_indent(pass_ind) ;
                        }
                    }
                    //printf("i, begin, pos = %d %d %d\n", i, begin, pos) ;
                    if (d->u.pattern.token_list[i].is_var) {
                        //printf("Here1 %d %s\n", *width, _th_print_exp(_th_apply(u,d->u.pattern.token_list[i].u.var.variable))) ;
                        //fflush(stdout) ;
                        
                        if (d->u.pattern.token_list[i].u.var.variable != 0) {
                            if (breaks==NULL && i > 0) {
                                pass_ind = ind+1 ;
                                cr_indent(pass_ind) ;
                            }
                            if (d->u.pattern.token_list[i].u.var.variable==va) {
                                exp = expa ;

                                term = 0 ;
                            } else {
                                exp = expb ;
                                term = pos ;
                            }
                            _th_push_current(pos) ;
                            res = _pp_print(env,pass_ind,
                                    d->u.pattern.token_list[i].u.var.mode,
                                    d->u.pattern.token_list[i].u.var.precedence,
                                    width,
                                    exp) ;
                                //printf("    Fail\n") ;
                            _th_pop_current() ;
                            if (res < 0) return -1 ;
                                //_th_pp_pos = pos_save ;
                                //goto cont1 ;
                        } else {
                            if (begin==-1) {
                                begin = i ;
                            } else {
                                ++pos ;
                                if (pos < e->u.appl.count) {
                                    expb = e->u.appl.args[pos] ;
                                    i = begin ;
                                }
                            }
                        }
                    } else {
                        char *t = _th_intern_decode(d->u.pattern.token_list[i].u.token) ;
                        //printf("Here2 %d '%s'\n", *width, t) ;
                        //fflush(stdout) ;
                        mprint_string(t) ;
                    }
                }
                //**buffer = 0 ;
                //printf("good printout of %s\n", start) ;
                add_index(0,startx,starty, currentx, currenty) ;
                return 1 ;
            } else {
                struct match_return *mr ;
                struct directive *breaks = find_pattern(dir, d->u.pattern.rule) ;
                mr = _th_match(env,d->u.pattern.print_exp,e) ;
                while (mr != NULL) {
                    struct _ex_unifier *u = mr->theta ;
                    int i ;
                    struct _ex_intern *cond = _th_subst(env,u,d->u.pattern.print_condition) ;
                    //printf("cond1 = %s\n", _th_print_exp(cond)) ;
                    cond = _th_rewrite(env,cond) ;
                    if (cond != _ex_true) goto cont ;

                    if (d->u.pattern.precedence < prec) goto paren_case ;

                    //printf("printing with rule %s\n", _th_intern_decode(d->u.pattern.rule)) ;
                    
                    for (i = 0; i < d->u.pattern.token_count; ++i) {
                        if (breaks != NULL) {
                            if (breaks->u.parse_break.list[i].break_mode==OPTIONAL_BREAK ||
                                breaks->u.parse_break.list[i].break_mode==REQUIRED_BREAK) {
                                pass_ind = breaks->u.parse_break.list[i].indent+ind ;
                                cr_indent(pass_ind) ;
                            }
                        }
                        if (d->u.pattern.token_list[i].is_var) {
                            if (d->u.pattern.token_list[i].u.var.variable != 0) {
                                if (breaks==NULL && i > 0) {
                                    pass_ind = ind+1 ;
                                    cr_indent(pass_ind) ;
                                }
                                depth = push_exp_index(d->u.pattern.print_exp, d->u.pattern.token_list[i].u.var.variable) ;
                                //printf("Printing var in mode %s\n", _th_intern_decode(d->u.pattern.token_list[i].u.var.mode)) ;
                                res = _pp_print(env,
                                        pass_ind,
                                        d->u.pattern.token_list[i].u.var.mode,
                                        d->u.pattern.token_list[i].u.var.precedence,
                                        width,
                                        _th_apply(u,d->u.pattern.token_list[i].u.var.variable)) ;
                                while (depth-- > 0) _th_pop_current() ;
                                if (res < 0) return -1 ;
                                    //pos_save = _th_pp_pos ;
                                    //goto cont1 ;
                            }
                        } else {
                            char *t = _th_intern_decode(d->u.pattern.token_list[i].u.token) ;
                            mprint_string(t) ;
                        }
                    }
                    add_index(0,startx,starty, currentx, currenty) ;
                    return 1 ;
cont:
                    mr = mr->next ;
                }
            }
        }
        d = d->next ;
    }

    //printf("No rule\n") ;
    return -1 ;

paren_case:
    d = dir ;
    //printf("Case 3 %s\n", _th_print_exp(e)) ;
    if (mode==INTERN_DEFAULT) {
        mprint_string("(") ;
        _pp_print(env,ind,INTERN_DEFAULT,0,width,e) ;
        mprint_string(")") ;
        return 1 ;
    } else {
        while (d != NULL) {
            int pos_save = _th_pp_pos ;
            if ((d->type==PRINT_PATTERN || d->type==PARSE_PATTERN) &&
                is_paren_rule(d,mode) &&
                rule_permitted_in_mode(mode,d)) {
                struct directive *breaks = find_pattern(dir, d->u.pattern.rule) ;
                int i ;
                
                //printf("Using rule %s for %s\n", _th_intern_decode(d->u.pattern.rule), _th_print_exp(e)) ;
                //fflush(stdout) ;
                //char *start = *buffer ;
                for (i = 0; i < d->u.pattern.token_count; ++i) {
                    if (breaks != NULL) {
                        if (breaks->u.parse_break.list[i].break_mode==OPTIONAL_BREAK ||
                            breaks->u.parse_break.list[i].break_mode==REQUIRED_BREAK) {
                            pass_ind = breaks->u.parse_break.list[i].indent+ind ;
                            cr_indent(pass_ind) ;
                        }
                    }
                    //printf("i = %d\n", i) ;
                    if (d->u.pattern.token_list[i].is_var) {
                        if (breaks==NULL && i > 0) {
                            pass_ind = ind+1 ;
                            cr_indent(pass_ind) ;
                        }
                        //printf("Here1 %d %s\n", *width, _th_print_exp(_th_apply(u,d->u.pattern.token_list[i].u.var.variable))) ;
                        //fflush(stdout) ;
                        if (d->u.pattern.token_list[i].u.var.variable != 0) {
                            if (_pp_print(env,pass_ind,
                                    d->u.pattern.token_list[i].u.var.mode,
                                    d->u.pattern.token_list[i].u.var.precedence,
                                    width,
                                    e) < 0) {
                                return -1 ;
                                //pos_save = _th_pp_pos ;
                                //goto cont2 ;
                            }
                        }
                    } else {
                        char *t = _th_intern_decode(d->u.pattern.token_list[i].u.token) ;
                        //printf("Here2 %d '%s'\n", *width, t) ;
                        //fflush(stdout) ;
                        mprint_string(t) ;
                    }
                }
                //**buffer = 0 ;
                //printf("good printout of %s\n", start) ;
                return 1 ;
            }
            d = d->next ;
        }
    }
    return -1 ;
}

static void _pp_print_default(struct env *env, int indent, int prec, int width, struct _ex_intern *e)
{
    char *p, *b ;
    char *sym ;
    int i ;
    int startx = currentx ;
    int starty = currenty ;
    unsigned dw = 4000 ;

    if (e==NULL) {
        mprint_string("<NULL>") ;
        return ;
    }

    switch (e->type) {

        case EXP_INTEGER:
            b = _th_pp_print_buf+_th_pp_pos ;
            print_number(&b,&dw,e->u.integer) ;
            *b = 0 ;
            _th_pp_pos += b - _th_pp_print_buf ;
            break ;

        case EXP_RATIONAL:
            /*mprint_char('#') ;*/
            b = _th_pp_print_buf+_th_pp_pos ;
            print_number(&b,&dw,e->u.rational.numerator) ;
            *b = 0 ;
            _th_pp_pos += b - _th_pp_print_buf ;
            mprint_char('/') ;
            b = _th_pp_print_buf+_th_pp_pos ;
            print_number(&b,&dw,e->u.rational.denominator) ;
            *b = 0 ;
            _th_pp_pos += b - _th_pp_print_buf ;
            break ;

        case EXP_STRING:
            p = e->u.string ;
            _th_pp_adjust_buffer(strlen(p) * 2 + 2) ;
            mprint_char('"') ;
            while(*p) {
                switch (*p) {
                    case '"':
                        _th_pp_print_buf[_th_pp_pos++] = '\\' ;
                        _th_pp_print_buf[_th_pp_pos++] = '"' ;
                        currentx += 2 ;
                        break ;
                    case '\\':
                        _th_pp_print_buf[_th_pp_pos++] = '\\' ;
                        _th_pp_print_buf[_th_pp_pos++] = '\\' ;
                        currentx += 2 ;
                        break ;
                    case '\n':
                        _th_pp_print_buf[_th_pp_pos++] = '\\' ;
                        _th_pp_print_buf[_th_pp_pos++] = 'n' ;
                        currentx += 2 ;
                        break ;
                    case '\r':
                        _th_pp_print_buf[_th_pp_pos++] = '\\' ;
                        _th_pp_print_buf[_th_pp_pos++] = 'r' ;
                        currentx += 2 ;
                        break ;
                    case '\t':
                        _th_pp_print_buf[_th_pp_pos++] = '\\' ;
                        _th_pp_print_buf[_th_pp_pos++] = 't' ;
                        currentx += 2 ;
                        break ;
                    default:
                        mprint_char(*p) ;
                }
                ++p ;
            }
            mprint_char('"') ;
            break ;

        case EXP_VAR:
            sym = _th_intern_decode(e->u.var) ;
            mprint_string(sym) ;
            break ;

        case EXP_MARKED_VAR:
            sym = _th_intern_decode(e->u.marked_var.var) ;
            mprint_string(sym) ;
            mprint_char('\'') ;
            if (e->u.marked_var.quant_level != 0) {
                mprint_small_number(buffer,width,e->u.marked_var.quant_level) ;
                mprint_char('\'') ;
            }
            break ;

        case EXP_APPL:
            sym = _th_intern_decode(e->u.appl.functor) ;
            mprint_string(sym) ;
            mprint_char('(') ;
            for (i = 0; i < e->u.appl.count; ++i) {
                if (i > 0) {
                    mprint_char(',') ;
                }
                cr_indent(indent+1) ;
                _th_push_current(i) ;
                _pp_print(env, indent+1, INTERN_DEFAULT, prec, width, e->u.appl.args[i]) ;
                _th_pop_current() ;
            }
            mprint_char(')') ;
            break ;

        case EXP_CASE:
            mprint_string("case ") ;
            _th_push_current(0) ;
            _pp_print(env, indent+1, INTERN_DEFAULT, prec, width, e->u.case_stmt.exp) ;
            _th_pop_current() ;
            for (i = 0; i < e->u.case_stmt.count; ++i) {
                if (i==0) {
                    mprint_string(" of ") ;
                } else {
                    mprint_char('|') ;
                }
                cr_indent(indent+1) ;
                _th_push_current(i*2+1) ;
                _pp_print(env, indent+1, INTERN_DEFAULT, prec, width, e->u.case_stmt.args[i*2]) ;
                _th_pop_current() ;
                mprint_char(':') ;
                _th_push_current(i*2+2) ;
                _pp_print(env, indent+1, INTERN_DEFAULT, prec, width, e->u.case_stmt.args[i*2+1]) ;
                _th_pop_current() ;
            }
            break ;

        case EXP_INDEX:
            mprint_string("INDEX(") ;
            _th_push_current(0) ;
            _pp_print(env, indent+1, INTERN_DEFAULT, prec, width, e->u.index.exp) ;
            _th_pop_current() ;
            mprint_char(',') ;
            mprint_string(_th_intern_decode(e->u.index.functor)) ;
            mprint_char(',') ;
            mprint_small_number(buffer,width,e->u.index.term) ;
            mprint_char(')') ;
            break ;

        case EXP_QUANT:
            switch (e->u.quant.quant) {
                 case INTERN_ALL:
                     mprint_string("ALL (") ;
                     _mprint_vars(e) ;
                     if (e->u.quant.cond != _ex_true) {
                         mprint_string(" : ") ;
                         _th_push_current(1) ;
                         _pp_print(env, indent+1, INTERN_DEFAULT, prec, width, e->u.quant.cond) ;
                         _th_pop_current() ;
                     }
                     mprint_string(") ") ;
                     _th_push_current(0) ;
                     _pp_print(env, indent+1, INTERN_DEFAULT, prec, width, e->u.quant.exp) ;
                     _th_pop_current() ;
                     break ;

                 case INTERN_EXISTS:
                     mprint_string("EXISTS (") ;
                     _mprint_vars(e) ;
                     mprint_string(") ") ;
                     _th_push_current(0) ;
                     _pp_print(env, indent+1, INTERN_DEFAULT, prec, width, e->u.quant.exp) ;
                     _th_pop_current() ;
                     break ;

                 case INTERN_SETQ:
                     mprint_string("{ ") ;
                     _th_push_current(0) ;
                     _pp_print(env, indent+1, INTERN_DEFAULT, prec, width, e->u.quant.exp) ;
                     _th_pop_current() ;
                     mprint_string(" [") ;
                     _mprint_vars(e) ;
                     mprint_string("] ") ;
                     if (e->u.quant.cond != _ex_true) {
                         mprint_string(": ") ;
                         _th_push_current(1) ;
                         _pp_print(env, indent+1, INTERN_DEFAULT, prec, width, e->u.quant.cond) ;
                         _th_pop_current() ;
                     }
                     mprint_string(" }") ;
                     break ;

                 case INTERN_LAMBDA:
                     mprint_string("lambda (") ;
                     _mprint_vars(e) ;
                     mprint_string(") ") ;
                     _th_push_current(0) ;
                     _pp_print(env, indent+1, INTERN_DEFAULT, prec, width, e->u.quant.exp) ;
                     _th_pop_current() ;
                     break ;

            }
            break ;
        default:
            mprint_string("<Printing error>") ;
            break ;
    }
    add_index(0,startx,starty,currentx,currenty) ;
}

static int _pp_print(struct env *env, int ind, unsigned mode, unsigned prec, int width, struct _ex_intern *e)
{
    char *buffer, *ms ;
    int w = width ;
    int res ;
    int index_count, x, y ;
    //printf("Printing %s in mode %s\n", _th_print_exp(e), _th_intern_decode(mode)) ;
    _th_pp_adjust_buffer(2001) ;
    _th_pp_adjust_buffer(width) ;
    buffer = _th_pp_print_buf+_th_pp_pos ;
    res = _th_pp_pos - 1 ;
    while (res >= 0 && _th_pp_print_buf[res] != '\n') {
        --res ;
        --w ;
    }
    index_count = _th_index_count ;
    x = currentx ;
    y = currenty ;
    if (_print_one_line(env, mode, prec, &buffer, &w, e)) {
        _th_pp_pos = buffer - _th_pp_print_buf ;
        return 1 ;
    }
    _th_index_count = index_count ;
    currentx = x ;
    currenty = y ;

    ms = _th_alloc_mark(MATCH_SPACE) ;

    res = _pp_print_rule(env, ind, mode, prec, width, e) ;
    
    _th_alloc_release(MATCH_SPACE,ms) ;

    if (res >= 0) return res ;
    _th_index_count = index_count ;
    currentx = x ;
    currenty = y ;
    if (mode==INTERN_DEFAULT) {
        _pp_print_default(env, ind, prec, width, e) ;
        return 1 ;
    } else if (mode==INTERN_IDENTIFIER) {
        if (e->type==EXP_STRING) {
            mprint_string(e->u.string);
            return 1;
        }
    } else if (mode==INTERN_NATURAL) {
        if (e->type==EXP_INTEGER) {
            _th_print_number(e->u.integer);
        }
    }

    return res ;
}

char *_th_pp_print(struct env *env, unsigned mode, int width, struct _ex_intern *e)
{
    //if (e->type==EXP_APPL && e->u.appl.functor==INTERN_CONS) {
        //printf("\n\n\n    *** DIRECTIVES ***\n\n\n") ;
        //_th_print_directives(_th_get_pp_directives(env)) ;
    //}

    free_index();
    currentx = 0 ;
    currenty = 1 ;

    _th_pp_pos = 0 ;
    _pp_print(env, 0, mode, 0, width, e) ;
    _th_pp_print_buf[_th_pp_pos] = 0 ;

    //if (e->type==EXP_APPL && e->u.appl.functor==INTERN_CONS) {
        //printf("%s\n",_th_pp_print_buf) ;
        //fflush(stdout) ;
        //exit(1) ;
    //}
    return _th_pp_print_buf ;
}

#ifndef FAST
void _th_pp_tree_print(struct env *env, unsigned mode, int width, struct _ex_intern *e)
{
    char *r = _th_pp_print(env, mode, width, e) ;
    int pos = 0 ;
    //printf("Placing in tree:\n%s\n", r) ;
    while (*r) {
        int cpos = 0 ;
        int final = 1 ;
        char *s ;
        while(*r==' ') {
            ++r ;
            ++cpos ;
        }
        cpos /= indent_factor ;
        s = r ;
        while (*s && *s != '\n') ++s ;
        final = !*s ;
        *s = 0 ;
        if (*r) {
            while (pos < cpos) {
                _tree_indent() ;
                ++pos ;
                if (pos < cpos) _tree_print0(" ") ;
            }
            while (pos > cpos) {
                _tree_undent() ;
                --pos ;
            }
            //printf("Adding line %d %s\n", pos, r) ;
            _tree_print0(r) ;
        }
        if (final) break ;
        r = ++s ;
    }
    while (pos > 0) {
        _tree_undent() ;
        --pos ;
    }
}

void _th_pp_file_print(FILE *f, char *h, struct env *env, unsigned mode, int width, struct _ex_intern *e)
{
    char *r = _th_pp_print(env, mode, width, e) ;
    int pos = 0 ;
    //printf("Placing in tree:\n%s\n", r) ;
    while (*r) {
        int final = 1 ;
        char *s ;
        s = r ;
        while (*s && *s != '\n') ++s ;
        final = !*s ;
        *s = 0 ;
        if (*r) {
            fprintf(f,"%s %s\n", h, r) ;
        }
        if (final) break ;
        r = ++s ;
    }
    while (pos > 0) {
        _tree_undent() ;
        --pos ;
    }
}
#endif
