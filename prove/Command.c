/*
 * command.c
 *
 * Routines for handling UI commands
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "Globalsp.h"

struct node *_th_derivation[MAX_DERIVATIONS] ;
int _th_derivation_space[MAX_DERIVATIONS] ;
char *_th_derivation_name[MAX_DERIVATIONS] ;

int _th_derivation_count = 1 ;

struct node *_th_cut_buffer = NULL ;
int _th_cut_space = 0 ;

int _th_errno ;

FILE *log_file ;

void _th_command_init()
{
    //log_file = fopen("prove.log","w") ;
    log_file = NULL;
}

void _th_command_shutdown()
{
    if (log_file) fclose(log_file) ;
}

void inputline(char *s)
{
    gets(s) ;
    if (log_file) {
        fprintf(log_file, "%s\n", s) ;
        fflush(log_file) ;
    }
}

int _th_find_space()
{
    int i, space ;

    for (space = DERIVATION_BASE;; ++space) {
        for (i = 1; i < _th_derivation_count; ++i) {
            if (_th_derivation_space[i]==space) goto cont ;
        }
        if (space==module_space) goto cont ;
        if (space==_th_cut_space) goto cont ;
        goto found ;
cont: ;
    } 
found: ;
	return space ;
}

static int _difference_count(struct _ex_intern *e1, struct _ex_intern *e2)
{
    int i;
    int total;

    if (e1==e2) return 0;
    if (e1->type != e2->type) return 1;

    switch (e1->type) {

        case EXP_APPL:
            if (e1->u.appl.functor != e2->u.appl.functor) return 1;
            if (e1->u.appl.count != e2->u.appl.count) return 1;
            total = 0;
            for (i = 0; i < e1->u.appl.count; ++i) {
                total += _difference_count(e1->u.appl.args[i],e2->u.appl.args[i]);
            }
            return total;

        case EXP_QUANT:
            if (e1->u.quant.quant != e2->u.quant.quant) return 1;
            if (e1->u.quant.var_count != e2->u.quant.var_count) return 1;
            for (i = 0; i < e1->u.quant.var_count; ++i) {
                if (e1->u.quant.vars[i] != e2->u.quant.vars[i]) return 1;
            }
            return _difference_count(e1->u.quant.exp,e2->u.quant.exp)+
                   _difference_count(e1->u.quant.cond,e2->u.quant.cond);

        case EXP_CASE:
            if (e1->u.case_stmt.count != e2->u.case_stmt.count) return 1;
            total = _difference_count(e1->u.case_stmt.exp,e2->u.case_stmt.exp);
            for (i = 0; i < e1->u.case_stmt.count*2; ++i) {
                total += _difference_count(e1->u.case_stmt.args[i],e2->u.case_stmt.args[i]);
            }
            return total;

        default:
            return 1;
    }
}

struct index_list {
    struct index_list *next;
    int index;
} ;

static int find_index(struct index_list *index)
{
    struct index_list *ind;
    int count, i, j;

    count = 0;
    ind = index;
    while (ind != NULL) {
        ind = ind->next;
        ++count;
    }

    for (i = 0; i < _th_index_count; ++i) {
        if (count==_th_index[i][5]) {
            ind = index;
            for (j = 5+count; j > 5; --j) {
                if (ind->index!=_th_index[i][j]) goto cont;
            }
            return i;
        }
cont:;
    }
    return -1;
}

static void _print_differences(struct index_list *parent, struct _ex_intern *e1, struct _ex_intern *e2)
{
    int i;
    struct index_list this_index;

    this_index.next = parent;

    if (e1==e2) return;
    if (e1->type != e2->type) goto print_difference;

    switch (e1->type) {

        case EXP_APPL:
            if (e1->u.appl.functor != e2->u.appl.functor) goto print_difference;
            if (e1->u.appl.count != e2->u.appl.count) goto print_difference;
            for (i = 0; i < e1->u.appl.count; ++i) {
                this_index.index = i;
                _print_differences(&this_index, e1->u.appl.args[i],e2->u.appl.args[i]);
            }
            return;

        case EXP_QUANT:
            if (e1->u.quant.quant != e2->u.quant.quant) goto print_difference;
            if (e1->u.quant.var_count != e2->u.quant.var_count) goto print_difference;
            for (i = 0; i < e1->u.quant.var_count; ++i) {
                if (e1->u.quant.vars[i] != e2->u.quant.vars[i]) goto print_difference;
            }
            this_index.index = 0;
            _print_differences(&this_index,e1->u.quant.exp,e2->u.quant.exp);
            this_index.index = 1;
            _print_differences(&this_index,e1->u.quant.cond,e2->u.quant.cond);
            return;

        case EXP_CASE:
            if (e1->u.case_stmt.count != e2->u.case_stmt.count) goto print_difference;
            this_index.index = 0;
            _print_differences(&this_index,e1->u.case_stmt.exp,e2->u.case_stmt.exp);
            for (i = 0; i < e1->u.case_stmt.count*2; ++i) {
                this_index.index = i+1;
                _print_differences(&this_index,e1->u.case_stmt.args[i],e2->u.case_stmt.args[i]);
            }
            return;
    }
print_difference:
    i = find_index(parent);
    if (i >= 0) {
        printf("%d\n%d\n%d\n%d\n", _th_index[i][0], _th_index[i][1]-1, _th_index[i][2], _th_index[i][3]-1);
    } else {
        printf("0\n0\n0\n0\n");
    }
}

static void _save()
{
    char s[80] ;
    int d ;

    inputline(s) ;

    d = atoi(s) ;

    _th_save_derivation(_th_derivation[d],_th_derivation_name[d]) ;

    printf("OK\n") ;
}

static void _save_as()
{
    char s[80] ;
    char name[200] ;
    int d ;

    inputline(s) ;
    inputline(name) ;

    d = atoi(s) ;

    _th_save_derivation(_th_derivation[d],name) ;

    FREE(_th_derivation_name[d]) ;
    _th_derivation_name[d] = strdup(name) ;
}

static void _load()
{
    int space ;
    char name[200] ;

    inputline(name) ;

    if (_th_derivation_count==MAX_DERIVATIONS) {
        printf("*END\nError: Maximum number of derivations reached.\n") ;
        return ;
    }

    space = _th_derivation_space[_th_derivation_count] = _th_find_space() ;
    _th_derivation[_th_derivation_count] = _th_load_derivation(space,name) ;
    _th_derivation_name[_th_derivation_count] = strdup(name) ;

    if (_th_errno) {
        printf("\n*END\nError: loading file\n") ;
        _th_errno = 0 ;
    } else {
        printf("\n*END\nOK\n%d\n", _th_derivation_count++) ;
    }
}

static void _print_header(struct env *env, struct node *d)
{
    if (!d->valid) printf("Invalid ") ;
    if (d->exported) printf("Exported ") ;
    switch(d->type) {
        case COMMENT_NODE:
            printf("COMMENT %s\n", d->u.comment.text) ;
            break ;
        case IMPORT_NODE:
            printf("IMPORT %s\n", d->u.import.text) ;
            break ;
        case ATTRIB_NODE:
            printf("ATTRIB ") ;
            _th_print_attrib(stdout, d) ;
            printf("\n") ;
            break ;
        case PP_DIRECTIVE_NODE:
            printf("PP %s\n", d->u.comment.text) ;
            break ;
        case TYPE_NODE:
            printf("TYPEDEF %s =", _th_pp_print(env,INTERN_DEFAULT,2000,d->u.type_definition.ttype)) ;
            printf(" %s\n", _th_pp_print(env,INTERN_DEFAULT,2000,d->u.type_definition.ttypedef)) ;
            break ;
        case PRECEDENCE_NODE:
            switch(d->u.precedence.type) {
                 case PREC_EQUAL:
                     printf("Precedence: %s = %s\n",
                            _th_intern_decode(d->u.precedence.left),
                            _th_intern_decode(d->u.precedence.right)) ;
                     break ;
                 case PREC_LESS:
                     printf("Precedence: %s < %s\n",
                            _th_intern_decode(d->u.precedence.left),
                            _th_intern_decode(d->u.precedence.right)) ;
                     break ;
                 default:
                     printf("Precedence: Unknown %d\n", d->u.precedence.type) ;
            }
            break ;
        case DEFINITION_NODE:
            printf("DEFINITION %s\n", _th_pp_print(env,INTERN_DEFAULT,2000,d->u.definition.template)) ;
            break ;
        case PROOF_NODE:
            if (_th_unfinished_node_count(d) > 0) {
                printf("Incomplete ") ;
            }
            printf("Proof of %s\n", _th_pp_print(env,INTERN_DEFAULT,2000,d->u.proof.property)) ;
            break ;
        case MODULE_NODE:
            printf("Proofs related to %s\n", _th_intern_decode(d->u.module.module)) ;
            break ;
        default:
            printf("Undefined node\n") ;
    }
}

static void _print_detailed_header(struct env *env, struct node *d)
{
    int i;

    /**********/

    if (d && d->type==DEFINITION_NODE) {
        printf("%d\n", d->u.definition.count+3);
        printf("FUNCTION %s\n", _th_pp_print(env,INTERN_DEFAULT,2000,d->u.definition.template));
        printf("TYPE %s\n", _th_pp_print(env,INTERN_DEFAULT,2000,d->u.definition.type));
        printf("PRECONDITION %s\n", _th_pp_print(env,INTERN_DEFAULT,2000,d->u.definition.precondition));
        for (i = 0; i < d->u.definition.count; ++i) {
            printf("    %s\n", _th_pp_print(env,INTERN_DEFAULT,2000,d->u.definition.rules[i]));
        }
    } else {
        printf("1\n");
        _print_header(env,d);
    }
}

static void _get_detail()
{
    char s[80] ;
    struct node *d ;
    int der ;
    void *mark = _th_alloc_mark(ENVIRONMENT_SPACE);
    struct env *env = _th_copy_env(ENVIRONMENT_SPACE,_th_base_env);

    inputline(s) ;
    der = atoi(s) ;
    inputline(s) ;
    if (der >= _th_derivation_count) {
        printf("Error: illegal derivation\n0\n") ;
        _th_alloc_release(ENVIRONMENT_SPACE, mark);
        return ;
    }
    d = _th_h_find_node(_th_derivation[der], s) ;
    if (d==NULL) {
        printf("OK\n0\n") ;
        _th_alloc_release(ENVIRONMENT_SPACE, mark);
        return ;
    }
    env = _th_h_build_env(s, env, _th_derivation[der]);
    printf("OK\n") ;
    _print_detailed_header(env, d) ;
}

static void _get_node_type()
{
    char s[80] ;
    struct node *d ;
    int der ;

    inputline(s) ;
    der = atoi(s) ;
    inputline(s) ;
    if (der >= _th_derivation_count) {
        printf("Error: illegal derivation\n0\n") ;
        return ;
    }
    d = _th_h_find_node(_th_derivation[der], s) ;
    if (d==NULL) {
        printf("Error: illegal position\n0\n") ;
        return ;
    }
    printf("OK\n") ;
    switch (d->type) {
        case DEFINITION_NODE:
            printf("Definition\n") ;
            break ;
        case PROOF_NODE:
            printf("Proof\n") ;
            break ;
        case ATTRIB_NODE:
            printf("Attrib\n") ;
            break ;
        case TYPE_NODE:
            printf("TypeDef\n") ;
            break ;
        case PRECEDENCE_NODE:
            printf("Precedence\n") ;
            break ;
        case IMPORT_NODE:
            printf("Import\n") ;
            break ;
        case COMMENT_NODE:
            printf("Comment\n") ;
            break ;
        case PP_DIRECTIVE_NODE:
            printf("PP\n") ;
            break ;
        case MODULE_NODE:
            printf("Module\n");
            break;
        default:
            printf("Other\n") ;
            break ;
    }
}

static void _get_header()
{
    char s[80] ;
    struct node *d ;
    int der ;
    void *mark = _th_alloc_mark(ENVIRONMENT_SPACE);
    struct env *env = _th_copy_env(ENVIRONMENT_SPACE, _th_base_env);

    inputline(s) ;
    der = atoi(s) ;
    inputline(s) ;
    if (der >= _th_derivation_count) {
        printf("Error: illegal derivation\n0\n") ;
        _th_alloc_release(ENVIRONMENT_SPACE, mark);
        return ;
    }
    d = _th_h_find_node(_th_derivation[der], s) ;
    if (d==NULL) {
        printf("Error: illegal position\n0\n") ;
        _th_alloc_release(ENVIRONMENT_SPACE, mark);
        return ;
    }
    printf("OK\n") ;
    env = _th_h_build_env(s, env, _th_derivation[der]);
    _print_header(env, d) ;

    _th_alloc_release(ENVIRONMENT_SPACE, mark);
}

static void _toggle_export()
{
    char s[80] ;
    struct node *d ;
    int der ;

    inputline(s) ;
    der = atoi(s) ;
    inputline(s) ;
    if (der >= _th_derivation_count || der == 0) {
        printf("Error: illegal derivation\n") ;
        return ;
    }
    d = _th_h_find_node(_th_derivation[der], s) ;
    if (d==NULL) {
        printf("Error: illegal position\n") ;
        return ;
    }
    printf("OK\n") ;
    d->exported = !d->exported ;
}

static void _insert_comment()
{
    char s[200] ;
    int der ;
    char pos[200] ;

    inputline(s) ;
    der = atoi(s) ;
    inputline(pos) ;
    inputline(s) ;
    if (der >= _th_derivation_count) {
        printf("Error: illegal derivation\n") ;
        return ;
    }
    printf("OK\n") ;
    _th_derivation[der] = _th_insert_comment(_th_derivation_space[der],_th_derivation[der],pos,s,1,0) ;
}

static void _insert_attrib()
{
    char s[200], pos[200] ;
    int der ;

    inputline(s) ;
    der = atoi(s) ;
    inputline(pos) ;
    inputline(s) ;
    if (der >= _th_derivation_count) {
        printf("Error: illegal derivation\n") ;
        return ;
    }
    _th_derivation[der] = _th_insert_attrib(_th_derivation_space[der],_th_derivation[der],pos,s,1,0) ;
    printf("OK\n") ;
}

static void _insert_import()
{
    char s[200], pos[200] ;
    int der ;

    inputline(s) ;
    der = atoi(s) ;
    inputline(pos) ;
    inputline(s) ;
    if (der >= _th_derivation_count) {
        printf("Error: illegal derivation\n") ;
        return ;
    }
    _th_derivation[der] = _th_insert_import(_th_derivation_space[der],_th_derivation[der],pos,s,1,0) ;
    printf("OK\n");
}

static void _insert_definition()
{
    char s[200], *c, pos[200] ;
    int der ;
    int count ;
    void *mark = _th_alloc_mark(ENVIRONMENT_SPACE);
    struct env *env = _th_copy_env(ENVIRONMENT_SPACE,_th_base_env);
    int error = 0, e;

    inputline(s) ;
    der = atoi(s) ;
    inputline(pos) ;
    env = _th_h_build_env(s,env,_th_derivation[der]);
    inputline(s) ;
    count = atoi(s) ;
    _th_start_definition();
    while(count-- > 0) {
        inputline(s) ;
        c = s;
        while (*c==' ') ++c;
        if (*c) {
            e = _th_add_definition_line(env,s);
            if (e) printf("Error: syntax error in '%s'\n", s);
            error = (error || e);
        }
    }
    if (der >= _th_derivation_count) {
        error = 1;
        printf("Error: illegal derivation\n") ;
    }
    error = (error || _th_incomplete_definition());
    if (error) {
        printf("BAD\n");
    } else {
        printf("OK\n") ;
        _th_derivation[der] = _th_insert_definition(_th_derivation_space[der],_th_derivation[der],pos,1,0) ;
    }
    _th_alloc_release(ENVIRONMENT_SPACE, mark);
}

static void _insert_precedence()
{
    char s[200], pos[200] ;
    int der ;

    inputline(s) ;
    der = atoi(s) ;
    inputline(pos) ;
    inputline(s) ;
    if (der >= _th_derivation_count) {
        printf("Error: illegal derivation\n") ;
        return ;
    }
    printf("OK\n") ;
    _th_derivation[der] = _th_insert_precedence(_th_derivation_space[der],_th_derivation[der],pos,s,1,0) ;
}

static void _insert_pp_directive()
{
    char s[200], pos[200] ;
    int der ;

    inputline(s) ;
    der = atoi(s) ;
    inputline(pos) ;
    inputline(s) ;
    if (der >= _th_derivation_count) {
        printf("Error: illegal derivation\n") ;
        return ;
    }
    printf("OK\n") ;
    _th_derivation[der] = _th_insert_pp_directive(_th_derivation_space[der],_th_derivation[der],pos,s,1,0) ;
}

static void _insert_typedef()
{
    char s[200], pos[200] ;
    struct node *d ;
    int der ;
    void *mark = _th_alloc_mark(ENVIRONMENT_SPACE);
    struct env *env = _th_copy_env(ENVIRONMENT_SPACE,_th_base_env);

    inputline(s) ;
    der = atoi(s) ;
    inputline(pos) ;
    inputline(s) ;
    if (der >= _th_derivation_count) {
        printf("Error: illegal derivation\n") ;
        _th_alloc_release(ENVIRONMENT_SPACE, mark);
        return ;
    }
    env = _th_h_build_env(s,env,_th_derivation[der]);
    d = _th_insert_type_env(_th_derivation_space[der],env,_th_derivation[der],pos,s,1,0) ;
    if (d==NULL) {
        printf("Error: Syntax of typedef\n") ;
        _th_alloc_release(ENVIRONMENT_SPACE, mark);
        return ;
    }
    _th_derivation[der] = d ;
    _th_alloc_release(ENVIRONMENT_SPACE, mark);
    printf("OK\n") ;
}

static void _insert_proof()
{
    char s[200] ;
    char t[200], pos[200] ;
    struct node *d ;
    int der ;
    void *mark = _th_alloc_mark(ENVIRONMENT_SPACE);
    struct env *env = _th_copy_env(ENVIRONMENT_SPACE,_th_base_env);

    inputline(s) ;
    der = atoi(s) ;
    inputline(pos) ;
    inputline(s) ;
    inputline(t) ;
    if (der >= _th_derivation_count) {
        printf("Error: illegal derivation\n") ;
        _th_alloc_release(ENVIRONMENT_SPACE, mark);
        return ;
    }
    env = _th_h_build_env(s,env,_th_derivation[der]);
    d = _th_insert_proof_env(_th_derivation_space[der],env,_th_derivation[der],pos,s,t,1,0) ;
    if (d==NULL) {
        printf("Error: Syntax of proof or type error\n") ;
        _th_alloc_release(ENVIRONMENT_SPACE, mark);
        return ;
    }
    _th_derivation[der] = d ;
    _th_alloc_release(ENVIRONMENT_SPACE, mark);
    printf("OK\n") ;
}

#define MAX_PROOFS 50

static struct proof_info {
    struct node *proof ;
    struct env *env ;
    int space ;
    int derivation ;
    char pos[200] ;
} proofs[MAX_PROOFS] ;

static int proof_count ;

static int get_proof(int der, char *node)
{
    int i ;

    for (i = 0; i < proof_count; ++i) {
        if (proofs[i].derivation==der && !strcmp(proofs[i].pos,node)) return i ;
    }
    return -1 ;
}

static void _get_proof_node()
{
    struct node *d ;
    int der ;
    char s[200], pos[200] ;

    inputline(s) ;
    der = atoi(s) ;
    inputline(pos) ;

    if (proof_count < MAX_PROOFS) {
        d = _th_get_proof(_th_derivation_space[der],_th_derivation[der],pos) ;
        if (d==NULL || d->type != PROOF_NODE) {
            printf("Error: Illegal proof node\n") ;
        } else {
            struct env *env = _th_copy_env(ENVIRONMENT_SPACE,_th_base_env);
            printf("OK\n") ;
            d->next = NULL ;
            proofs[proof_count].proof = d ;
            proofs[proof_count].env = _th_h_build_env(s, env, _th_derivation[der]) ;
            proofs[proof_count].space = _th_derivation_space[der] ;
            proofs[proof_count].derivation = der ;
            strcpy(proofs[proof_count].pos, pos) ;
            ++proof_count ;
        }
    } else {
        printf("Error: Too many proof nodes\n") ;
    }
}

static void _copy_proof_nodes(int space, int space2)
{
    int i ;

    for (i = 0; i < proof_count; ++i) {
        if (proofs[i].space==space) {
            proofs[i].proof = _th_copy_derivation(space2, proofs[i].proof) ;
            proofs[i].space = space2 ;
        }
    }
}

static void _clear_cut_buffer()
{
    _th_alloc_clear(_th_cut_space) ;
    _th_cut_space = 0 ;
    _th_cut_buffer = NULL ;
}

static void _move_nodes_to_cut_buffer()
{
    char line[200], line2[200] ;
    int der, start, end ;

    if (_th_cut_buffer != NULL) _clear_cut_buffer() ;

    inputline(line) ;
    der = atoi(line) ;
    inputline(line2) ;
    start = _th_get_suffix(line2) ;
    inputline(line) ;
    end = _th_get_suffix(line) ;
    _th_strip_suffix(line);
    _th_strip_suffix(line2);

    if (strcmp(line,line2)) {
        printf("Error: Selected nodes must be in the same hierarchy\n");
    } else {
        struct node *node;
        if (line[0]) {
            node = _th_h_find_node(_th_derivation[der], line);
            node = node->u.module.branch_nodes;
        } else {
            node = _th_derivation[der];
        }
        _th_cut_space = _th_find_space () ;
        _th_cut_buffer = _th_copy_derivation_range(_th_cut_space, node, start, end-start+1) ;
    }

    printf("OK\n") ;
}

static void _move_nodes_from_cut_buffer()
{
    char line[200], line2[200] ;
    int der, start ;
    struct node *tmp, *node ;

    inputline(line) ;
    der = atoi(line) ;
    inputline(line) ;
    strcpy(line2,line) ;
    start = _th_get_suffix(line) ;
    _th_strip_suffix(line) ;

    if (_th_cut_buffer==NULL) {
        printf("OK\n") ;
        return ;
    }

    node = _th_derivation[der] ;
    if (line[0]) {
        node = _th_h_find_node(node, line) ;
        if (node==NULL) {
            printf("OK\n") ;
            return ;
        }
        node = node->u.module.branch_nodes ;
    }
    tmp = _th_copy_derivation(_th_derivation_space[der], _th_cut_buffer) ;
    _th_derivation[der] = _th_insert_nodes(node, tmp, start) ;
    _th_invalidate_derivation(_th_derivation[der], line2) ;

    printf("OK\n") ;
}

void _delete_nodes()
{
    char line[200], line2[200], line3[200] ;
    int der, start, end ;
    int space ;

    inputline(line) ;
    der = atoi(line) ;
    inputline(line) ;
    start = _th_get_suffix(line) ;
    inputline(line2) ;
    end = _th_get_suffix(line2) ;
    strcpy(line3,line) ;
    _th_strip_suffix(line) ;
    _th_strip_suffix(line2) ;

    if (!strcmp(line,line2)) {
        space = _th_find_space () ;
        _copy_proof_nodes(_th_derivation_space[der],space) ;
        _th_derivation[der] = _th_copy_derivation_except_range(space, _th_derivation[der], line, start, end-start+1) ;
        _th_alloc_clear(_th_derivation_space[der]) ;
        _th_derivation_space[der] = space ;
        _th_invalidate_derivation(_th_derivation[der], line3) ;
    }

    printf("OK\n") ;
}

void _cancel_proof_node()
{
    char line[40] ;
    int der, i ;
    int space ;

    inputline(line) ;
    der = atoi(line) ;
    inputline(line) ;

    for (i = 0; i < proof_count; ++i) {
        if (proofs[i].derivation==der && !strcmp(proofs[i].pos,line)) break ;
    }
    if (i==proof_count) {
        printf("Error: illegal node\n") ;
        return ;
    }
    proofs[i] = proofs[--proof_count] ;
    space = _th_find_space () ;
    _copy_proof_nodes(_th_derivation_space[der],space) ;
    _th_derivation[der] = _th_copy_derivation(space, _th_derivation[der]) ;
    _th_alloc_clear(_th_derivation_space[der]) ;
    _th_derivation_space[der] = space ;

    printf("OK\n") ;
}

void _return_proof_node()
{
    char line[40] ;
    int der, i ;
    int space ;

    inputline(line) ;
    der = atoi(line) ;
    inputline(line) ;

    for (i = 0; i < proof_count; ++i) {
        if (proofs[i].derivation==der && !strcmp(proofs[i].pos,line)) break ;
    }
    if (i==proof_count) {
        printf("Error: illegal node\n") ;
        return ;
    }
    _th_return_proof(_th_derivation[der],proofs[i].proof,line) ;
    proofs[i] = proofs[--proof_count] ;
    space = _th_find_space () ;
    _copy_proof_nodes(_th_derivation_space[der],space) ;
    _th_derivation[der] = _th_copy_derivation(space, _th_derivation[der]) ;
    _th_alloc_clear(_th_derivation_space[der]) ;
    _th_derivation_space[der] = space ;

    printf("OK\n") ;
}

void rec_print_headers(struct env *env, struct node *d)
{
    struct node *d1 = d;
    int count;

    count = 0 ;
    while(d1 != NULL) {
        ++count ;
        d1 = d1->next ;
    }

    printf("%d\n", count);

    while(d != NULL) {
        _print_header(env, d) ;
        _th_add_to_env(ENVIRONMENT_SPACE,env,d);
        if (d->type==MODULE_NODE) {
            rec_print_headers(env,d->u.module.branch_nodes);
        } else {
            printf("0\n");
        }
        d = d->next ;
    }
}

void _headers()
{
    char line[40] ;
    struct node *d ;
    char *mark = _th_alloc_mark(ENVIRONMENT_SPACE);
    struct env *env;

    inputline(line) ;

    if (atoi(line) >= _th_derivation_count) {
        printf("Error: Illegal derivation\n") ;
        return ;
    }

    d = _th_derivation[atoi(line)] ;

    printf("OK\n") ;
    env = _th_copy_env(ENVIRONMENT_SPACE,_th_base_env);

    rec_print_headers(env, d);

    _th_alloc_release(ENVIRONMENT_SPACE, mark);
}

void print_proof_header(struct env *env, int indent, int operation, struct proof *p)
{
    int i ;

    for (i = 0; i < indent; ++i) printf(" ") ;

    switch (operation) {
        case REWRITE:
            printf("Rewrite: ") ;
            break ;
        case EXPAND:
        case UNIVERSAL:
            printf("Case %s: ", _th_pp_print(env,INTERN_DEFAULT,2000,p->choice)) ;
            break ;
        case SPECIAL_REWRITE:
        case COND_SPECIAL_REWRITE:
            printf("Special: ") ;
            break ;
    }
    printf("%s\n", _th_pp_print(env, INTERN_DEFAULT, 2000, p->term)) ;
}

void print_proof_header_detail(struct env *env, int indent, int operation, struct proof *p)
{
    int i ;

    char *c, *pp;

    c = _th_pp_print(env, INTERN_DEFAULT, 80, p->term);

    i = 1;
    pp = c;
    while (*pp) {
        if (*pp++=='\n') ++i;
    }
    printf("%d\n%s\n", i, c);
}

void _toggle_display_mode()
{
    char line[40] ;
    int der ;
    int n ;
    struct node *proof ;
    inputline(line) ;
    der = atoi(line) ;
    inputline(line) ;
    n = get_proof(der,line) ;
    if (n >= 0) {
        printf("OK\n") ;
        proof = proofs[n].proof ;
        proof->u.proof.display_all = !proof->u.proof.display_all ;
    } else {
        printf("Error: illegal node\n") ;
    }
}

static void _get_display_mode()
{
    char line[40] ;
    int der ;
    int n ;
    struct node *proof ;

    inputline(line) ;
    der = atoi(line) ;
    inputline(line) ;
    n = get_proof(der,line) ;
    if (n >= 0) {
        printf("OK\n") ;
        proof = proofs[n].proof ;
        if (proof->u.proof.display_all) {
            printf("All\n") ;
        } else {
            printf("Unfinished\n") ;
        }
    } else {
        printf("Error: illegal node\n") ;
    }
}

static void _print_proof_headers(struct env *env, struct node *proof)
{
    int i, n, indent ;
    struct proof *p ;

    if (proof->u.proof.display_all) {
        int operations[100] ;
        n = _th_total_node_count(proof) ;
        printf("OK\n%d\n", n) ;
        for (i = 0; i < n; ++i) {
            p = _th_get_node(i,&indent,proof) ;
            operations[indent] = p->operation ;
            if (indent > 0) {
                print_proof_header(env,indent*2,operations[indent-1],p) ;
            } else {
                print_proof_header(env,indent*2,0,p) ;
            }
        }
    } else {
        n = _th_unfinished_node_count(proof) ;
        printf("OK\n%d\n", n) ;
        for (i = 0; i < n; ++i) {
            p = _th_get_unfinished_node(i,proof) ;
            print_proof_header(env,2,0,p) ;
        }
    }
}

static void _get_proof_headers()
{
    char line[40] ;
    int der ;
    int n ;
    struct node *proof ;
 
    inputline(line) ;
    der = atoi(line) ;
    inputline(line) ;
    n = get_proof(der,line) ;
    if (n < 0) {
        printf("Error: Illegal proof\n") ;
        return ;
    }
    proof = proofs[n].proof ;

    _print_proof_headers(proofs[n].env, proof) ;
}

static void _get_ind_exp()
{
    char line[40] ;
    int der ;
    int n ;
    struct node *proof ;

    inputline(line) ;
    der = atoi(line) ;
    inputline(line) ;
    n = get_proof(der,line) ;
    if (n < 0) {
        printf("Error: Illegal proof\n") ;
        return ;
    }
    proof = proofs[n].proof ;
    if (proof->u.proof.order==NULL) {
        printf("OK\nNOEXP\n") ;
    } else {
        printf("OK\n%s\n", _th_print_exp(proof->u.proof.order)) ;
    }
}

static void _get_proof_detail()
{
    char line[40], node[200] ;
    int der ;
    int n, i, indent ;
    struct node *proof ;
    struct proof *p ;
    struct env *env;

    inputline(line) ;
    der = atoi(line) ;
    inputline(node) ;
    inputline(line) ;
    i = atoi(line) ;
    n = get_proof(der,node) ;
    if (n < 0) {
        printf("Error: illegal node\n") ;
        return ;
    }
    proof = proofs[n].proof;
    env = proofs[n].env;

    if (proof->u.proof.display_all) {
        n = _th_total_node_count(proof) ;
        if (i >= n) {
            printf("Error: Illegal line\n") ;
        } else {
            printf("OK\n") ;
            p = _th_get_node(i,&indent,proof) ;
            print_proof_header_detail(env,0,0,p) ;
        }
    } else {
        n = _th_unfinished_node_count(proof) ;
        if (i >= n) {
            printf("Error: Illegal line\n") ;
        } else {
            printf("OK\n") ;
            p = _th_get_unfinished_node(i,proof) ;
            print_proof_header_detail(env,0,0,p) ;
        }
    }
}

static void _print_positions()
{
    char line[40], node[200] ;
    int der ;
    int n, i, indent ;
    struct node *proof ;
    struct proof *p ;

    inputline(line) ;
    der = atoi(line) ;
    inputline(node) ;
    inputline(line) ;
    i = atoi(line) ;
    n = get_proof(der,node) ;
    if (n < 0) {
        printf("Error: illegal node\n") ;
        return ;
    }
    proof = proofs[n].proof ;

    if (proof->u.proof.display_all) {
        n = _th_total_node_count(proof) ;
        if (i >= n) {
            printf("Error: Illegal line\n") ;
        } else {
            p = _th_get_node(i,&indent,proof) ;
            if (p->parent==NULL) {
                printf("OK\n0\n") ;
            } else {
                printf("OK\n%d\n", _difference_count(p->term, p->parent->term));
                _print_differences(NULL, p->term, p->parent->term);
            }
        }
    } else {
        n = _th_unfinished_node_count(proof) ;
        if (i >= n) {
            printf("Error: Illegal line\n") ;
        } else {
            p = _th_get_unfinished_node(i,proof) ;
            if (p->parent==NULL) {
                printf("OK\n0\n") ;
            } else {
                printf("OK\n%d\n", _difference_count(p->term, p->parent->term));
                _print_differences(NULL, p->term, p->parent->term);
            }
        }
    }
}

static void _cancel_operation()
{
    char line[40], node[200] ;
    int der ;
    int n, i, indent ;
    struct node *proof ;
    struct proof *p ;
    int x ;

    inputline(line) ;
    der = atoi(line) ;
    inputline(node) ;
    inputline(line) ;
    i = atoi(line) ;
    n = get_proof(der,node) ;
    proof = proofs[n].proof ;

    p = _th_get_node(i,&indent,proof) ;
    x = _th_cancel_operation(p) ;
    printf("OK\n%d\n", x) ;
}

static void _get_inner_rewrites()
{
    char line[40], node[200] ;
    int der ;
    int n, i, indent ;
    struct node *proof ;
    struct proof *p ;

    inputline(line) ;
    der = atoi(line) ;
    inputline(node) ;
    inputline(line) ;
    i = atoi(line) ;
    n = get_proof(der,node) ;
    if (n < 0) {
        printf("Error: Illegal proof\n") ;
        return ;
    }
    proof = proofs[n].proof ;

    if (proof->u.proof.display_all) {
        p = _th_get_node(i,&indent,proof) ;
    } else {
        p = _th_get_unfinished_node(i,proof) ;
    }
    if (_th_rewrite_operation(_th_derivation_space[der], proofs[n].env, proof, p)) {
        printf("Error\n") ;
        return ;
    }
    printf("OK\n") ;
    printf("%d\n", _th_possibility_count) ;
    for (i = 0; i < _th_possibility_count; ++i) {
        printf("%s\n", _th_print_exp(_th_possible_rewrites[i])) ;
    }
}

static void _get_specializations()
{
    char line[40], node[200] ;
    int der ;
    unsigned n, i, indent, count, j ;
    struct node *proof ;
    struct proof *p ;
    char *mark ;
    unsigned **vars ;

    inputline(line) ;
    der = atoi(line) ;
    inputline(node) ;
    inputline(line) ;
    i = atoi(line) ;
    n = get_proof(der,node) ;
    if (n < 0) {
        printf("Error: Illegal proof\n") ;
        return ;
    }
    proof = proofs[n].proof ;

    if (proof->u.proof.display_all) {
        p = _th_get_node(i,&indent,proof) ;
    } else {
        p = _th_get_unfinished_node(i,proof) ;
    }
    printf("OK\n") ;

    mark = _th_alloc_mark(ENVIRONMENT_SPACE) ;
    vars = _th_get_expandable_variables(ENVIRONMENT_SPACE,p->term,&count) ;
    printf("%d\n", count) ;
    for (i = 0; i < count; ++i) {
        printf("%s ", _th_intern_decode(vars[i][0])) ;
        if (vars[i][1]==0) {
            printf("which is free\n") ;
        } else {
            printf("in") ;
            for (j = 2; j < vars[i][1]+2; ++j) {
                 printf(" %d", vars[i][j]) ;
            }
            printf("\n") ;
        }
    }
    _th_alloc_release(ENVIRONMENT_SPACE, mark) ;
}

static void _incorporate_specialization()
{
    char line[40], node[200] ;
    int der ;
    int n, i, indent, j ;
    struct node *proof ;
    struct proof *p ;

    inputline(line) ;
    der = atoi(line) ;
    inputline(node) ;
    inputline(line) ;
    i = atoi(line) ;
    inputline(line) ;
    j = atoi(line) ;
    n = get_proof(der,node) ;
    if (n < 0) {
        printf("Error: Illegal proof\n") ;
        return ;
    }
    proof = proofs[n].proof ;

    if (proof->u.proof.display_all) {
        p = _th_get_node(i,&indent,proof) ;
    } else {
        p = _th_get_unfinished_node(i,proof) ;
    }
    printf("OK\n") ;

    _th_incorporate_expansion(_th_derivation_space[der], proofs[n].env, proof, p, j) ;
}

static void _get_universal_positions()
{
    char line[40], node[200] ;
    int der ;
    int n, i, indent, count ;
    struct node *proof ;
    struct proof *p ;
    char *mark ;
    char *s ;
    unsigned **terms ;
    int start, end ;

    inputline(line) ;
    der = atoi(line) ;
    inputline(node) ;
    inputline(line) ;
    i = atoi(line) ;
    n = get_proof(der,node) ;
    if (n < 0) {
        printf("Error: Illegal proof\n") ;
        return ;
    }
    proof = proofs[n].proof ;

    if (proof->u.proof.display_all) {
        p = _th_get_node(i,&indent,proof) ;
    } else {
        p = _th_get_unfinished_node(i,proof) ;
    }
    printf("OK\n") ;

    mark = _th_alloc_mark(ENVIRONMENT_SPACE) ;
    printf("1\n%s\n", s = _th_print_exp(p->term)) ;
    terms = _th_get_universal_positions(ENVIRONMENT_SPACE, p->term, &count) ;
    printf("%d\n", count) ;
    for (i = 0; i < count; ++i) {
        _th_get_position(s, terms[i][0], terms[i]+1, 0, &start, &end) ;
        printf("%d\n0\n%d\n0\n", start, end) ;
    }
    _th_alloc_release(ENVIRONMENT_SPACE, mark) ;
}

static void _incorporate_universal()
{
    char line[40], node[200] ;
    int der ;
    int n, i, indent, count, j ;
    struct node *proof ;
    struct proof *p ;
    char *mark ;
    unsigned **terms ;
    struct _ex_intern *exp ;

    inputline(line) ;
    der = atoi(line) ;
    inputline(node) ;
    inputline(line) ;
    i = atoi(line) ;
    inputline(line) ;
    j = atoi(line) ;
    inputline(line) ;
    n = get_proof(der,node) ;
    exp = _th_parse(proofs[n].env,line) ;
    if (n < 0) {
        printf("Error: Illegal proof\n") ;
        return ;
    }
    proof = proofs[n].proof ;

    if (proof->u.proof.display_all) {
        p = _th_get_node(i,&indent,proof) ;
    } else {
        p = _th_get_unfinished_node(i,proof) ;
    }

    mark = _th_alloc_mark(ENVIRONMENT_SPACE) ;
    terms = _th_get_universal_positions(ENVIRONMENT_SPACE, p->term, &count) ;
    _th_incorporate_universal(_th_derivation_space[der], proofs[n].env, proof, p, exp, j, terms[j][0], terms[j]+1) ;
    _th_alloc_release(ENVIRONMENT_SPACE, mark) ;
    _print_proof_headers(proofs[n].env, proof) ;
}

static struct env *result_env;

static void _get_result_details()
{
    char line[40] ;
    int i ;
    int count ;
    char *p, *pp ;

    inputline(line) ;
    i = atoi(line) ;

    pp = _th_pp_print(result_env,INTERN_DEFAULT,80,_th_possible_rewrites[i]);
    p = pp;
    count = 1;
    while (*p) {
        if (*p++=='\n') ++count;
    }
    printf("OK\n%d\n%s\n0\n0\n0\n0\n", count, pp);
}

static void _get_special_rewrite_positions()
{
    char line[40], node[200] ;
    int der ;
    int n, i, indent ;
    struct node *proof ;
    struct proof *p ;
    char *mark ;
    int lines ;
    char *pp, *c;

    inputline(line) ;
    der = atoi(line) ;
    inputline(node) ;
    inputline(line) ;
    i = atoi(line) ;
    n = get_proof(der,node) ;
    if (n < 0) {
        printf("Error: Illegal proof\n") ;
        return ;
    }
    proof = proofs[n].proof ;

    if (proof->u.proof.display_all) {
        p = _th_get_node(i,&indent,proof) ;
    } else {
        p = _th_get_unfinished_node(i,proof) ;
    }
    printf("OK\n") ;

    mark = _th_alloc_mark(ENVIRONMENT_SPACE) ;
    pp = _th_pp_print(proofs[n].env, INTERN_DEFAULT, 80, p->term);
    c = pp;
    lines = 1;
    while (*c) {
        if (*c++=='\n') ++lines;
    }
    printf("%d\n%s\n", lines, pp) ;
    printf("%d\n", _th_index_count) ;
    for (i = _th_index_count-1; i >= 0; --i) {
        printf("%d\n%d\n%d\n%d\n", _th_index[i][0], _th_index[i][1]-1, _th_index[i][2], _th_index[i][3]-1) ;
    }
    _th_alloc_release(ENVIRONMENT_SPACE, mark) ;
}

static void _get_rewrite_fill_vars()
{
    char line[40] ;
    struct _ex_intern *args[2], *e ;
    int i, count ;
    unsigned *mv ;

    inputline(line) ;
    i = atoi(line) ;

    args[0] = _th_possible_conditions[i] ;
    args[1] = _th_possible_rewrites[i] ;
    e = _ex_intern_appl(INTERN_AND,2,args) ;

    mv = _th_get_marked_vars(e, &count) ;
    printf("OK\n%d\n", count) ;
    for (i = 0; i < count; ++i) {
        printf("%s\n", _th_intern_decode(mv[i])) ;
    }
}

static void _get_special_rewrites()
{
    char line[40], node[200] ;
    int der ;
    int n, i, indent ;
    struct node *proof ;
    struct proof *p ;
    int pos, count ;
    unsigned **terms ;
    char *mark ;
 
    inputline(line) ;
    der = atoi(line) ;
    inputline(node) ;
    inputline(line) ;
    i = atoi(line) ;
    inputline(line) ;
    pos = atoi(line) ;

    mark = _th_alloc_mark(ENVIRONMENT_SPACE) ;

    n = get_proof(der,node) ;
    if (n < 0) {
        printf("Error: Illegal proof\n") ;
        return ;
    }
    proof = proofs[n].proof ;

    if (proof->u.proof.display_all) {
        p = _th_get_node(i,&indent,proof) ;
    } else {
        p = _th_get_unfinished_node(i,proof) ;
    }
    terms = _th_get_all_positions(ENVIRONMENT_SPACE, p->term, &count) ;
    _th_special_rewrite_operation(_th_derivation_space[der], proofs[n].env, proof, p, _th_index[_th_index_count-1-pos][5], _th_index[_th_index_count-1-pos]+6) ;
    printf("OK\n") ;
    printf("%d\n", _th_possibility_count) ;
    for (i = 0; i < _th_possibility_count; ++i) {
        printf("%s\n", _th_pp_print(proofs[n].env,INTERN_DEFAULT,2000,_th_possible_rewrites[i])) ;
    }
    result_env = proofs[n].env;
    _th_alloc_release(ENVIRONMENT_SPACE, mark) ;
}

static void _get_condition_special_rewrites()
{
    char line[40], node[200] ;
    int der ;
    int n, i, indent ;
    struct node *proof ;
    struct proof *p ;
    int pos, count ;
    unsigned **terms ;
    char *mark ;
 
    inputline(line) ;
    der = atoi(line) ;
    inputline(node) ;
    inputline(line) ;
    i = atoi(line) ;
    inputline(line) ;
    pos = atoi(line) ;

    mark = _th_alloc_mark(ENVIRONMENT_SPACE) ;

    n = get_proof(der,node) ;
    if (n < 0) {
        printf("Error: Illegal proof\n") ;
        return ;
    }
    proof = proofs[n].proof ;

    if (proof->u.proof.display_all) {
        p = _th_get_node(i,&indent,proof) ;
    } else {
        p = _th_get_unfinished_node(i,proof) ;
    }
    terms = _th_get_all_positions(ENVIRONMENT_SPACE, p->term, &count) ;
    _th_condition_special_rewrite_operation(_th_derivation_space[der], proofs[n].env, proof, p, _th_index[_th_index_count-1-pos][5], _th_index[_th_index_count-1-pos]+6) ;
    printf("OK\n") ;
    printf("%d\n", _th_possibility_count) ;
    for (i = 0; i < _th_possibility_count; ++i) {
        printf("%s\n", _th_pp_print(proofs[n].env,INTERN_DEFAULT,2000,_th_possible_rewrites[i])) ;
    }
    result_env = proofs[n].env;
    _th_alloc_release(ENVIRONMENT_SPACE, mark) ;
}

static void _incorporate_rewrite()
{
    char line[40], node[200] ;
    int der ;
    int n, i, j ;
    struct node *proof ;
    struct _ex_intern *args[2], *e ;
    struct _ex_unifier *u ;
    unsigned *mv ;
    int count ;

    inputline(line) ;
    der = atoi(line) ;
    inputline(node) ;
    inputline(line) ;
    i = atoi(line) ;
    n = get_proof(der,node) ;
    proof = proofs[n].proof ;

    args[0] = _th_possible_conditions[i] ;
    args[1] = _th_possible_rewrites[i] ;
    e = _ex_intern_appl(INTERN_AND,2,args) ;

    mv = _th_get_marked_vars(e, &count) ;
    u = _th_new_unifier(_th_derivation_space[der]) ;
    for (j = 0; j < count; ++j) {
        inputline(line) ;
        u = _th_add_pair(_th_derivation_space[der],u,mv[j],_th_parse(proofs[n].env,line)) ;
    }

    _th_incorporate_rewrite(proofs[n].env, _th_derivation_space[der], i, u) ;

    _print_proof_headers(proofs[n].env, proof) ;
}

static int is_state_var(struct module_list *ml, char *s)
{
    struct add_list *d = ml->declarations;

    while (d != NULL) {
        if (d->e->type==EXP_APPL && d->e->u.appl.functor==INTERN_STATE_VAR &&
            d->e->u.appl.count==1 && d->e->u.appl.args[0]->type==EXP_STRING &&
            !strcmp(s,d->e->u.appl.args[0]->u.string)) return 1;
        d = d->next;
    }

    return 0;
}

static void print_condition_tree(struct module_list *ml, int pos)
{
    struct child_edge_list *children;
    if (ml->condition_nodes[pos].condition==NULL) {
        printf("Root %d\n", pos);
    } else {
        printf("Condition %d %s\n", pos, _th_pp_print(verilog_env,INTERN_DEFAULT,2000,ml->condition_nodes[pos].condition));
    }
    printf("*SUB\n");
    children = ml->condition_nodes[pos].children;
    while (children != NULL) {
        print_condition_tree(ml,children->child);
        children = children->next;
    }
    printf("*ENDSUB\n");
}

static void print_defs(struct module_list *ml)
{
    struct add_list *d = ml->declarations, *m;
    struct assign_group *a;
    struct module_pointer_list *child;
    int i;

    printf("Modules\n");
    printf("*SUB\n");
    while (d != NULL) {
        if (d->e->type==EXP_APPL && d->e->u.appl.functor==INTERN_INSTANCE &&
            d->e->u.appl.count > 2 && d->e->u.appl.args[0]->type==EXP_STRING) {
            printf("Module %s\n", d->e->u.appl.args[0]->u.string);
            printf("*SUB\n");
            printf("Connections\n");
            printf("*SUB\n");
            m = ml->declarations;
            while(m != NULL) {
                if (m->e->type==EXP_APPL && m->e->u.appl.functor==INTERN_CONNECT &&
                    m->e->u.appl.count >= 3 && m->e->u.appl.args[0]->type==EXP_STRING &&
                    !strcmp(m->e->u.appl.args[0]->u.string,d->e->u.appl.args[0]->u.string)) {
                    printf("%s\n", _th_pp_print(verilog_env,INTERN_DEFAULT,2000,m->e));
                }
                m = m->next;
            }
            printf("*ENDSUB\n");
            child = ml->children;
            while (child != NULL && child->instance != (unsigned)_th_intern(d->e->u.appl.args[0]->u.string)) {
                child = child->next;
            }
            if (child != NULL) {
                printf("Instantiation\n");
                printf("*SUB\n");
                m = child->instantiation;
                while (m != NULL) {
                    printf("%s\n", _th_pp_print(verilog_env,INTERN_DEFAULT,2000,m->e));
                    m = m->next;
                }
                printf("*ENDSUB\n");
            }
            printf("*ENDSUB\n");
        }
        d = d->next;
    }
    printf("*ENDSUB\n");

    printf("Raw assignments\n");
    printf("*SUB\n");
    d = ml->declarations;
    while (d != NULL) {
        if (d->e->type==EXP_APPL && d->e->u.appl.functor==INTERN_ASSIGN) {
            printf("%s\n", _th_pp_print(verilog_env,INTERN_DEFAULT,2000,d->e));
        }
        d = d->next;
    }
    printf("*ENDSUB\n");

    printf("Compiled assignments\n");
    printf("*SUB\n");
    a = ml->groups;
    while (a != NULL) {
        if (is_state_var(ml,_th_intern_decode(a->variable))) printf("STATE VAR ");
        if (a->high >= 0) {
            unsigned decl;
            switch (a->decl) {
                case INTERN_REG_VECTOR:
                    decl = INTERN_REG;
                    break;
                case INTERN_WIRE_VECTOR:
                    decl = INTERN_WIRE;
                    break;
                case INTERN_INPUT_VECTOR:
                    decl = INTERN_INPUT;
                    break;
                case INTERN_OUTPUT_VECTOR:
                    decl = INTERN_OUTPUT;
                    break;
                case INTERN_INOUT_VECTOR:
                    decl = INTERN_INOUT;
                    break;
                default:
                    decl = a->decl;
            }
            printf("%s %s[%d:%d]\n", _th_intern_decode(decl), _th_intern_decode(a->variable),
                a->high,a->low);
        } else {
            printf("%s %s\n", _th_intern_decode(a->decl), _th_intern_decode(a->variable));
        }
        d = a->assigns;
        printf("*SUB\n");
        while (d != NULL) {
            printf("%s\n", _th_pp_print(verilog_env,INTERN_DEFAULT,2000,d->e));
            d = d->next;
        }
        printf("*ENDSUB\n");
        a = a->next;
    }
    printf("*ENDSUB\n");

    printf("Condition trees\n");
    printf("*SUB\n");
    for (i = 0; i < ml->condition_node_count; ++i) {
        if (ml->condition_nodes[i].condition==NULL) {
            print_condition_tree(ml, i);
        }
    }
    printf("*ENDSUB\n");

    printf("Parameters\n");
    printf("*SUB\n");
    d = ml->declarations;
    while (d != NULL) {
        if (d->e->type==EXP_APPL && d->e->u.appl.functor==INTERN_PARAMETER) {
            printf("%s\n", _th_pp_print(verilog_env,INTERN_DEFAULT,2000,d->e));
        }
        d = d->next;
    }
    printf("*ENDSUB\n");

    printf("Inputs and Outputs\n");
    printf("*SUB\n");
    d = ml->declarations;
    while (d != NULL) {
        if (d->e->type==EXP_APPL &&
            (d->e->u.appl.functor==INTERN_INPUT ||
             d->e->u.appl.functor==INTERN_INPUT_VECTOR ||
             d->e->u.appl.functor==INTERN_OUTPUT ||
             d->e->u.appl.functor==INTERN_OUTPUT_VECTOR ||
             d->e->u.appl.functor==INTERN_INOUT ||
             d->e->u.appl.functor==INTERN_INOUT_VECTOR)) {
            printf("%s\n", _th_pp_print(verilog_env,INTERN_DEFAULT,2000,d->e));
        }
        d = d->next;
    }
    printf("*ENDSUB\n");

    printf("Registers and wires\n");
    printf("*SUB\n");
    d = ml->declarations;
    while (d != NULL) {
        if (d->e->type==EXP_APPL &&
            (d->e->u.appl.functor==INTERN_REG ||
             d->e->u.appl.functor==INTERN_REG_VECTOR ||
             d->e->u.appl.functor==INTERN_WIRE ||
             d->e->u.appl.functor==INTERN_WIRE_VECTOR)) {
            if (d->e->u.appl.args[0]->type==EXP_STRING &&
                is_state_var(ml,d->e->u.appl.args[0]->u.string)) printf("STATE VAR ");
            printf("%s\n", _th_pp_print(verilog_env,INTERN_DEFAULT,2000,d->e));
        }
        d = d->next;
    }
    printf("*ENDSUB\n");
}

static void print_asserts(struct module_list *ml)
{
    struct add_list *d = ml->assertions;

    while (d != NULL) {
        printf("%s\n", _th_pp_print(verilog_env,INTERN_DEFAULT,2000,d->e));
        d = d->next;
    }
}

static void _print_definitions()
{
    char line[1000];
    unsigned mod;
    struct module_list *ml = modules;

    inputline(line);
    mod = _th_intern(line);

    while (ml != NULL) {
        if (ml->name==mod) {
            print_defs(ml);
            printf("*END\n");
            print_asserts(ml);
            break;
        }
        ml = ml->next;
    }

    printf("*END\n");
}

static void _verify_assertion()
{
    char line[1000];
    char local[1000];
    char show_rewrites[1000];

    unsigned mod;
    struct module_list *ml = modules;

    inputline(line);
    mod = _th_intern(line);
    inputline(line);
    inputline(local);
    inputline(show_rewrites);

    while (ml != NULL) {
        if (ml->name==mod) {
            struct _ex_intern *e;
            e = _th_flatten(verilog_env,_th_pp_parse("stdin",verilog_env,line));
            if (e != NULL) {
#ifndef FAST
                if (show_rewrites[0]) {
                    _tree_mute = 0;
                    _tree_start = 0;
                    _tree_end = 20000000;
                    _tree_sub = _tree_sub2 = -1;
                } else {
                    _tree_mute = 1;
                }
                //_tree_mute = 0;
                //_tree_start = 2135;
                //_tree_end = 2137;
                //_tree_sub = _tree_sub2 = -1;
#endif
                if (local[0]) {
                    e = _th_verify_assertion(ml,e,local);
                } else {
                    e = _th_verify_assertion(ml,e,NULL);
                }
            }
            if (e==_ex_true) {
                printf("*GOOD\n");
            } else {
                printf("*BAD\n%s\n", _th_print_exp(e));
            }
#ifndef FAST
            _tree_mute = 0;
#endif
            return;
        }
        ml = ml->next;
    }
    printf("*BAD\nNo module\n");
}

static void print_tree(struct module_list *module)
{
    int count = 0;
    struct module_pointer_list *children = module->children;
    while (children != NULL) {
        ++count;
        children = children->next;
    }

    printf("%s\n%d\n", _th_intern_decode(module->name), count);

    children = module->children;
    while (children != NULL) {
        printf("%s\n", _th_intern_decode(children->instance));
        print_tree(children->module);
        children = children->next;
    }
}

static void _print_hierarchy()
{
    struct module_list *ml = modules;

    while (ml != NULL) {
        if (ml->is_root_module) {
            print_tree(ml);
        }
        ml = ml->next;
    }

    printf("*END\n");
}

static void _load_model()
{
    char line[1000];
    char prefix[1000];
    int len;

    if (module_space==-1) {
        module_space = _th_find_space();
    }

    if (verilog_env==NULL) {
        char *x = "C:\\c-engine" ;
        char name[30];
        FILE *file ;

        verilog_env = _th_default_env(ENVIRONMENT_SPACE);

#ifndef FAST
        _debug_print("Reading initialization files") ;
#endif
        _tree_indent() ;
        sprintf(name, "%s\\defs\\basic.ld", x) ;
        file = fopen(name, "r") ;
        if (file==NULL) {
            printf("Error: File %s not found\n", name) ;
        } else {
            verilog_env = _th_process_file(verilog_env, name, file) ;
        }
        fclose(file) ;

        sprintf(name, "%s\\defs\\verilog.ld", x) ;
        file = fopen(name, "r") ;
        if (file==NULL) {
            printf("Error: File %s not found\n", name) ;
        } else {
            verilog_env = _th_process_file(verilog_env, name, file) ;
        }
        fclose(file) ;
        _tree_undent() ;
        _th_base_env = verilog_env;
    }

    inputline(line);

    strcpy(prefix,line);
    len = strlen(prefix)-1;
    while (len >= 0 && prefix[len] != '/' && prefix[len] != '\\') --len;
    if (len < 0) len = 0;
    prefix[len] = 0;

    verilog_derivation = load_model(line);

    printf("*END\n");
    printf("%d\n", verilog_derivation);
}

static void _pretty_print()
{
    char line[1000];

    inputline(line);
    if (verilog_env==NULL) {
        printf("1\n%s\n", line);
    } else {
        struct _ex_intern *e = _th_pp_parse("stdin",verilog_env, line);
        if (e==NULL) {
            printf("1\n%s\n", line);
        } else {
            char *c = _th_pp_print(verilog_env,INTERN_DEFAULT,80,e);
            char *s = c;
            int lc = 0;
            while (*s) {
                if (*s=='\n') ++lc;
                ++s;
            }
            printf("%d\n%s\n", lc+2, c);
            printf("%s\n", _th_print_exp(e));
        }
    }
}

void _insert_theorem()
{
    char line[1000] ;
    unsigned module ;
    struct _ex_intern *e ;
    struct node *d ;

    inputline(line) ;
    module = _th_intern(line) ;
    inputline(line) ;
    e = _th_pp_parse("stdin",verilog_env, line);
    d = _th_insert_theorem(_th_derivation_space[verilog_derivation],_th_derivation[verilog_derivation],module,e) ;
    if (d != NULL) {
        _th_derivation[verilog_derivation] = d ;
    } else {
        printf("Error: bad derivation\n") ;
    }
    printf("OK\n") ;
}

int _th_process(char *command)
{
    if (log_file) {
        fprintf(log_file, "%s\n", command) ;
        fflush(log_file) ;
    }

    if (!strcmp(command,"quit")) return 1 ;

    if (!strcmp(command,"load")) {
        _load() ;
    } else if (!strcmp(command,"save")) {
        _save() ;
    } else if (!strcmp(command,"saveAs")) {
        _save_as() ;
    } else if (!strcmp(command,"headers")) {
        _headers() ;
    } else if (!strcmp(command,"getDetail")) {
        _get_detail() ;
    } else if (!strcmp(command,"insertComment")) {
        _insert_comment() ;
    } else if (!strcmp(command,"insertAttrib")) {
        _insert_attrib() ;
    } else if (!strcmp(command,"insertImport")) {
        _insert_import() ;
    } else if (!strcmp(command,"insertPpDirective")) {
        _insert_pp_directive() ;
    } else if (!strcmp(command,"insertPrecedence")) {
        _insert_precedence() ;
    } else if (!strcmp(command,"insertDefinition")) {
        _insert_definition() ;
    } else if (!strcmp(command,"insertTypeDef")) {
        _insert_typedef() ;
    } else if (!strcmp(command,"insertProof")) {
        _insert_proof() ;
    } else if (!strcmp(command,"deleteNodes")) {
        _delete_nodes() ;
    } else if (!strcmp(command,"toggleExport")) {
        _toggle_export() ;
    } else if (!strcmp(command,"clearCutBuffer")) {
        _clear_cut_buffer() ;
    } else if (!strcmp(command,"moveNodesToCutBuffer")) {
        _move_nodes_to_cut_buffer() ;
    } else if (!strcmp(command,"moveNodesFromCutBuffer")) {
        _move_nodes_from_cut_buffer() ;
    } else if (!strcmp(command,"getProofNode")) {
        _get_proof_node() ;
    } else if (!strcmp(command,"cancelProofNode")) {
        _cancel_proof_node() ;
    } else if (!strcmp(command,"returnProofNode")) {
        _return_proof_node() ;
    } else if (!strcmp(command,"getProofHeaders")) {
        _get_proof_headers() ;
    } else if (!strcmp(command,"getDisplayMode")) {
        _get_display_mode() ;
    } else if (!strcmp(command,"toggleDisplayMode")) {
        _toggle_display_mode() ;
    } else if (!strcmp(command,"cancelOperation")) {
        _cancel_operation() ;
    } else if (!strcmp(command,"getInnerRewrites")) {
        _get_inner_rewrites() ;
    } else if (!strcmp(command,"getSpecialRewrites")) {
        _get_special_rewrites() ;
    } else if (!strcmp(command,"getResultDetails")) {
        _get_result_details() ;
    } else if (!strcmp(command,"getConditionSpecialRewrites")) {
        _get_condition_special_rewrites() ;
    } else if (!strcmp(command,"getRewriteFillVars")) {
        _get_rewrite_fill_vars() ;
    } else if (!strcmp(command,"incorporateRewrite")) {
        _incorporate_rewrite() ;
    } else if (!strcmp(command,"getSpecializations")) {
        _get_specializations() ;
    } else if (!strcmp(command,"incorporateSpecialization")) {
        _incorporate_specialization() ;
    } else if (!strcmp(command,"getUniversalPositions")) {
        _get_universal_positions() ;
    } else if (!strcmp(command,"getSpecialRewritePositions")) {
        _get_special_rewrite_positions() ;
    } else if (!strcmp(command,"incorporateUniversal")) {
        _incorporate_universal() ;
    } else if (!strcmp(command,"getNodeType")) {
        _get_node_type() ;
    } else if (!strcmp(command,"getHeader")) {
        _get_header() ;
    } else if (!strcmp(command,"getIndExp")) {
        _get_ind_exp() ;
    } else if (!strcmp(command,"getProofDetail")) {
        _get_proof_detail() ;
    } else if (!strcmp(command,"printPositions")) {
        _print_positions() ;
    } else if (!strcmp(command,"toggleDisplayMode")) {
        _toggle_display_mode() ;
    } else if (!strcmp(command, "loadModel")) {
        _load_model();
    } else if (!strcmp(command, "printHierarchy")) {
        _print_hierarchy();
    } else if (!strcmp(command, "printDefinitions")) {
        _print_definitions();
    } else if (!strcmp(command, "verifyAssertion")) {
        _verify_assertion();
    } else if (!strcmp(command, "prettyPrint")) {
        _pretty_print();
    } else if (!strcmp(command, "insertTheorem")) {
        _insert_theorem();
    } else {
        printf("Error: illegal command\n") ;
    }
    return 0 ;
}
