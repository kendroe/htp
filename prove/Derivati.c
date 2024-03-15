/*
 * derivation.c
 *
 * Routines for maintaining a derivation
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h>
#include "Globalsp.h"

struct node *_th_find_node(struct node *der, int pos)
{
    while(der != NULL && pos > 0) {
        --pos ;
        der = der->next ;
    }
    return der ;
}

struct node *_th_h_find_node(struct node *der, char *pos)
{
    struct node *n;
    while (*pos) {
        n = _th_find_node(der, atoi(pos));
        while (*pos && *pos != '.') ++pos;
        if (*pos) {
            ++pos;
            if (n->type != MODULE_NODE) {
                printf("Error: Module node expected\n");
                return n;
            }
            der = n->u.module.branch_nodes;
        }
    }
    return n;        
}

#define MAX_PARAMETERS 20

void _th_print_attrib(FILE *f, struct node *node)
{
    int i ;

    fprintf(f, "%s ", _th_intern_decode(node->u.attrib.param)) ;
    for (i = 0; i < node->u.attrib.count; ++i) {
        switch (node->u.attrib.parameter[i].type) {
            case SYMBOL_PARAMETER:
                fprintf(f, "%s", _th_intern_decode(node->u.attrib.parameter[i].u.symbol)) ;
                break ;
            case INTEGER_PARAMETER:
                fprintf(f, "%d", node->u.attrib.parameter[i].u.integer) ;
                break ;
            case EXP_PARAMETER:
                fprintf(f, "%s", _th_print_exp(node->u.attrib.parameter[i].u.exp)) ;
                break ;
        }
        if (i < node->u.attrib.count - 1) fprintf(f, ",") ;
    }
}

static struct node *insert(struct node *der, struct node *n, char *pos)
{
    struct node *node;
    int p =  atoi(pos);

    while (*pos && *pos != '.') ++pos;
    if (*pos) {
        ++pos;
    } else if (p == 0) {
        n->next = der ;
        return n ;
    } else {
        --p ;
        node = der ;
        while(p > 0) {
            node = node->next ;
            --p ;
        }
        n->next = node->next ;
        node->next = n ;
        return der ;
    }

    node = der;
    while (*pos) {
        int nextp = atoi(pos);
        while (*pos && *pos != '.') ++pos;
        node = _th_find_node(node, p);
        p = nextp;
        if (!*pos) {
            if (p == 0) {
                n->next = node->u.module.branch_nodes ;
                node->u.module.branch_nodes = n ;
            } else {
                --p ;
                node = node->u.module.branch_nodes ;
                while(p > 0) {
                    node = node->next ;
                    --p ;
                }
                n->next = node->next ;
                node->next = n ;
            }
            return der ;
        } else {
            if (node->type != MODULE_NODE) {
                printf("Error: module node expected, cannot insert.\n");
                return der;
            }
            ++pos;
            node = node->u.module.branch_nodes;
        }
    }
    return NULL;
}

struct node *_th_insert_attrib(int space, struct node *node, char *pos, char *s, int valid, int exported)
{
    struct node *n ;
    char symbol[200] ;
    unsigned key_symbol ;
    int i, count ;
    struct parameter parameter[MAX_PARAMETERS] ;

    /*
     * We need to parse the LEX specification before allocating the space.
     */
    while(*s==' ' || *s=='\t') ++s ;
    i = 0 ;
    while((isalnum(*s) || *s=='_') && i < 199) symbol[i++] = *s++ ;
    if (i==0) return NULL ;
    symbol[i++] = 0 ;
    key_symbol = _th_intern(symbol) ;

    while(*s==' ' || *s=='\t') ++s ;

    count = 0 ;
    while (*s) {
        if (count==MAX_PARAMETERS) return NULL ;
        if (isalpha(*s)) {
            i = 0 ;
            while((isalnum(*s) || *s=='_') && i < 199) symbol[i++] = *s++ ;
            if (i==0) return NULL ;
            symbol[i++] = 0 ;
            parameter[count].type = SYMBOL_PARAMETER ;
            parameter[count++].u.symbol = _th_intern(symbol) ;
        } else if (isdigit(*s) || *s=='-') {
            parameter[count].type = INTEGER_PARAMETER ;
            parameter[count++].u.integer = atoi(s) ;
            while (*s==' '||*s=='\t'||*s=='-'||isdigit(*s)) ++ s ;
        } else if (*s=='(') {
            parameter[count].type = EXP_PARAMETER ;
            parameter[count].u.exp = _th_parse(NULL,s) ;
            if (parameter[count++].u.exp==NULL) return NULL ;
            ++s ;
            i = 1 ;
            while (*s && i > 0) {
                if (*s=='(') ++i ;
                else if (*s==')') --i ;
                ++s ;
            }
            if (i != 0) return NULL ;
        } else {
            return NULL ;
        }
        while(*s==' ' || *s=='\t') ++s ;
        if (*s && *s != ',') return NULL ;
        if (*s) {
            ++s ;
            while(*s==' ' || *s=='\t') ++s ;
        }
    }

    n = (struct node *)_th_alloc(space, sizeof(struct node_root) + sizeof(int) * 2 + sizeof(struct parameter) * count) ;

    n->exported = exported ;
    n->valid = valid ;
    n->type = ATTRIB_NODE ;

    n->u.attrib.count = count ;
    n->u.attrib.param = key_symbol ;
    for (i = 0; i < count; ++i) {
        n->u.attrib.parameter[i] = parameter[i] ;
    }

    return insert(node, n, pos) ;
}

static struct _ex_intern *precondition ;
static struct _ex_intern *type ;
static struct _ex_intern *function ;
static int rule_count ;
#define MAX_RULES 2000
static struct _ex_intern *rules[MAX_RULES] ;

void _th_start_definition()
{
    precondition = type = function = NULL ;
    rule_count = 0 ;
}

int _th_add_definition_line(struct env *env, char *s)
{
    if (!strncmp(s,"FUNCTION",8)) {
        if (env==NULL) {
            function = _th_parse(env, s+8);
        } else {
            function = _th_pp_parse("stdin", env, s+8) ;
        }
        if (function==NULL || function->type != EXP_APPL) return 1;
    } else if (!strncmp(s,"TYPE",4)) {
        if (env==NULL) {
            type = _th_parse(env,s+4);
        } else {
            type = _th_pp_parse("stdin", env, s+4) ;
        }
        if (type==NULL || type->type != EXP_APPL) return 1;
    } else if (!strncmp(s,"PRECONDITION",12)) {
        if (env==NULL) {
            precondition = _th_parse(env,s+12);
        } else {
            precondition = _th_pp_parse("stdin", env, s+12) ;
        }
        if (precondition==NULL) return 1;
    } else {
        struct _ex_intern *e ;
        if (env==NULL) {
            e = _th_parse(env, s) ;
        } else {
            e = _th_pp_parse("stdin", env, s) ;
        }
        if (e == NULL) return 1;
        rules[rule_count++] = e;
    }
    return 0;
}

int _th_incomplete_definition()
{
    int error = 0;

    if (function==NULL) {
        printf("Error: No function specified");
        error = 1;
    }

    if (type==NULL) {
        printf("Error: No type specified");
        error = 1;
    }

    return error;
}

struct node *_th_insert_definition(int space, struct node *node, char *pos, int valid, int exported)
{
    struct node *n = (struct node *)_th_alloc(space, sizeof(struct node_root) + sizeof(int) + (3+rule_count) * sizeof(struct _ex_intern *)) ;
    int i ;

    n->exported = exported ;
    n->valid = valid ;
    n->type = DEFINITION_NODE ;

    if (precondition==NULL) precondition = _ex_true;

    n->u.definition.template = function ;
    n->u.definition.type = type ;
    n->u.definition.precondition = precondition ;
    n->u.definition.count = rule_count ;
    for (i = 0; i < rule_count; ++i) {
        n->u.definition.rules[i] = rules[i] ;
    }

    return insert(node, n, pos) ;
}

struct node *_th_insert_comment(int space, struct node *node, char *pos, char *s, int valid, int exported)
{
    struct node *n = (struct node *)_th_alloc(space, sizeof(struct node_root) + strlen(s) + 1) ;

    n->exported = exported ;
    n->valid = valid ;
    n->type = COMMENT_NODE ;
    
    strcpy(n->u.comment.text,s) ;
    return insert(node, n, pos) ;

#ifdef XX
    if (pos == 0) {
        n->next = node ;
        return n ;
    } else {
        --pos ;
        base = node ;
        while(pos > 0) {
            node = node->next ;
            --pos ;
        }
        n->next = node->next ;
        node->next = n ;
        return base ;
    }
#endif
}

static struct _ex_intern *build_def_cond(struct env *env, struct _ex_intern *e)
{
    int count ;
    unsigned *fv = _th_get_free_vars(e, &count) ;
    struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * (count+1)) ;
    struct _ex_intern *args2[2] ;
    int i ;

    for (i = 0; i < count; ++i) {
         args2[0] = _ex_intern_var(fv[i]) ;
         args2[1] = _ex_intern_marked_var(fv[i],0) ;
         args2[0] = _ex_intern_appl_env(env,INTERN_EQUAL,2,args2) ;
         args[i] = _ex_intern_appl_env(env,INTERN_NOT,1,args2) ;
    }
    args[count] = _ex_intern_appl_env(env,INTERN_OR,count,args) ;
    for (i = 0; i < count; ++i) {
         args2[0] = _ex_intern_var(fv[i]) ;
         args2[1] = _ex_intern_marked_var(fv[i],0) ;
         args[i] = _ex_intern_appl_env(env,INTERN_PRECEQ,2,args2) ;
    }
    return _ex_intern_appl_env(env,INTERN_AND,count+1,args) ;
}

static struct _ex_intern *_build_ind_exp(struct env *env, struct _ex_intern *rule, struct _ex_intern *key)
{
    struct _ex_intern *and, *keym ;
    struct _ex_intern *args1[2], *args2[3] ;
    if (rule==_ex_true) return _ex_true;
    if (rule->type != EXP_APPL || rule->u.appl.count != 3 ||
        (rule->u.appl.functor != INTERN_ORIENTED_RULE && rule->u.appl.functor != INTERN_UNORIENTED_RULE &&
        rule->u.appl.functor != INTERN_FORCE_ORIENTED)) {
        rule = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE, rule, _ex_true, _ex_true);
    }
    if (key==NULL) {
        and = build_def_cond(env, rule) ;
    } else {
        keym = _th_mark_vars(env, key) ;
        args1[0] = key;
        args1[1] = keym;
        args2[0] = _ex_intern_appl_env(env,INTERN_EQUAL,2,args1) ;
        args2[0] = _ex_intern_appl_env(env,INTERN_NOT,1,args2) ;
        args2[1] = _ex_intern_appl_env(env,INTERN_PRECEQ,2,args1) ;
        and = _ex_intern_appl_env(env,INTERN_AND,2,args2) ;
    }
    args1[0] = and ;
    args1[1] = rule->u.appl.args[2] ;
    args2[0] = rule->u.appl.args[0] ;
    args2[1] = rule->u.appl.args[1] ;
    args2[2] = _th_flatten_top(env,_ex_intern_appl_env(env,INTERN_AND,2,args1)) ;

    return _ex_intern_appl_env(env,rule->u.appl.functor,3,args2) ;
}

struct node *_th_insert_proof(int space, struct node *node, char *pos, char *proof, char *order, int valid, int exported)
{
    struct node *n = (struct node *)_th_alloc(space, sizeof(struct node_root) + sizeof(struct _ex_intern *) * 2 + sizeof(struct proof *) + sizeof(int)) ;
    struct env *env ;
    char *mark ;

    n->exported = exported ;
    n->valid = valid ;
    n->type = PROOF_NODE ;
   
    n->u.proof.property = _th_parse(NULL,proof) ;
    n->u.proof.proof = (struct proof *)_th_alloc(space, sizeof(struct proof)) ;
    n->u.proof.proof->term = n->u.proof.property ;
    n->u.proof.proof->operation = 0 ;
    n->u.proof.proof->child_count = 0 ;
    n->u.proof.display_all = 0 ;
    n->u.proof.proof->parent = NULL;
    if (order[0]) {
        n->u.proof.order = _th_parse(NULL,order) ;
    } else {
        n->u.proof.order = NULL ;
    }

    mark = _th_alloc_mark(TYPE_SPACE) ;
    env = _th_default_env(TYPE_SPACE) ;
    n->u.proof.proof->ind_exp = _build_ind_exp(env,n->u.proof.property,n->u.proof.order) ;
    if (_th_checkTyping(env, _th_parse(env, "(Bool)"), n->u.proof.property)==NULL) {
        _th_alloc_release(TYPE_SPACE,mark);
        return NULL;
    }

    _th_alloc_release(TYPE_SPACE,mark) ;

    if (n->u.proof.property==NULL || (n->u.proof.order==NULL && order[0])) return NULL ;

    return insert(node, n, pos) ;
}

struct node *_th_insert_proof_env(int space, struct env *env, struct node *node, char *pos, char *proof, char *order, int valid, int exported)
{
    struct node *n = (struct node *)_th_alloc(space, sizeof(struct node_root) + sizeof(struct _ex_intern *) * 2 + sizeof(struct proof *) + sizeof(int)) ;
    void *mark;

    n->exported = exported ;
    n->valid = valid ;
    n->type = PROOF_NODE ;
   
    n->u.proof.property = _th_pp_parse("stdin",env,proof) ;
    n->u.proof.proof = (struct proof *)_th_alloc(space, sizeof(struct proof)) ;
    n->u.proof.proof->term = n->u.proof.property ;
    n->u.proof.proof->operation = 0 ;
    n->u.proof.proof->child_count = 0 ;
    n->u.proof.display_all = 0 ;
    n->u.proof.proof->parent = NULL ;
    if (order[0]) {
        n->u.proof.order = _th_pp_parse("stdin",env,order) ;
    } else {
        n->u.proof.order = NULL ;
    }
    mark = _th_alloc_mark(TYPE_SPACE);
    if (_th_checkTyping(env, _th_parse(env, "(Bool)"), n->u.proof.property)==NULL) {
        _th_alloc_release(TYPE_SPACE,mark);
        return NULL;
    }
    _th_alloc_release(TYPE_SPACE,mark);

    if (n->u.proof.property==NULL || (n->u.proof.order==NULL && order[0])) return NULL ;

    n->u.proof.proof->ind_exp = _build_ind_exp(env,n->u.proof.property,n->u.proof.order) ;

    return insert(node, n, pos) ;
}

struct node *_th_insert_pp_directive(int space, struct node *node, char *pos, char *s, int valid, int exported)
{
    struct node *n = (struct node *)_th_alloc(space, sizeof(struct node_root) + strlen(s) + 1) ;

    n->exported = exported ;
    n->valid = valid ;
    n->type = PP_DIRECTIVE_NODE ;
    strcpy(n->u.pp_directive.text,s) ;
    return insert(node, n, pos) ;
}

#define MAX_ORDER 200

struct node *_th_insert_precedence(int space, struct node *node, char *pos, char *s, int valid, int exported)
{
    struct node *n ;
    char symbol[200] ;
    unsigned key_symbol ;
    int i ;

    /*
     * We need to parse the LEX specification before allocating the space.
     */
    while(*s==' ' || *s=='\t') ++s ;
    i = 0 ;
    while((isalnum(*s) || *s=='_') && i < 199) symbol[i++] = *s++ ;
    if (i==0) return NULL ;
    symbol[i++] = 0 ;
    key_symbol = _th_intern(symbol) ;

    while(*s==' ' || *s=='\t') ++s ;

    if (*s=='<' || *s=='=') {
        n = (struct node *)_th_alloc(space, sizeof(struct node_root) + sizeof(int) + sizeof(unsigned) * 2) ;
        n->u.precedence.type = ((*s=='<')?PREC_LESS:PREC_EQUAL) ;
        n->u.precedence.left = key_symbol ;

        ++s ;
        while(*s==' ' || *s=='\t') ++s ;
        i = 0 ;
        while((isalnum(*s) || *s=='_') && i < 199) symbol[i++] = *s++ ;
        if (i==0) return NULL ;
        while(*s==' ' || *s=='\t') ++s ;
        if (*s) return NULL ; /* Nothing alowed after the symbol except spaces */
        symbol[i++] = 0 ;
        n->u.precedence.right = _th_intern(symbol) ;
    } else {
        return NULL ;
    }

    n->exported = exported ;
    n->valid = valid ;
    n->type = PRECEDENCE_NODE ;

    return insert(node, n, pos) ;
}

struct node *_th_insert_type(int space, struct node *node, char *pos, char *s, int valid, int exported)
{
    struct node *n = (struct node *)_th_alloc(space, sizeof(struct node_root) + 2 * sizeof(struct _ex_intern *)) ;
    struct _ex_intern *ttype, *ttypedef ;
    char *e ;

    n->exported = exported ;
    n->valid = valid ;
    n->type = TYPE_NODE ;

    e = s ;
    while (*e && *e!='=') ++e ;
    if (!*e) return NULL ;
    *e = 0 ;
    ++e ;

    ttype = _th_parse(NULL,s) ;
    ttypedef = _th_parse(NULL,e) ;
    if (ttype==NULL || ttypedef == NULL) return NULL ;

    n->u.type_definition.ttype = ttype ;
    n->u.type_definition.ttypedef = ttypedef ;

    return insert(node, n, pos) ;
}

struct node *_th_insert_type_env(int space, struct env *env, struct node *node, char *pos, char *s, int valid, int exported)
{
    struct node *n = (struct node *)_th_alloc(space, sizeof(struct node_root) + 2 * sizeof(struct _ex_intern *)) ;
    struct _ex_intern *ttype, *ttypedef ;
    char *e ;

    n->exported = exported ;
    n->valid = valid ;
    n->type = TYPE_NODE ;

    e = s ;
    while (*e && *e!='=') ++e ;
    if (!*e) return NULL ;
    *e = 0 ;
    ++e ;

    ttype = _th_pp_parse("stdin",env,s) ;
    ttypedef = _th_pp_parse("stdin",env,e) ;
    if (ttype==NULL || ttypedef == NULL) return NULL ;
    if (ttype->type != EXP_APPL || ttypedef->type != EXP_APPL) return NULL;

    n->u.type_definition.ttype = ttype ;
    n->u.type_definition.ttypedef = ttypedef ;

    return insert(node, n, pos) ;
}

struct node *insert_module_node(int space, struct node *node, int pos, unsigned module, int valid, int exported, struct node **ret)
{
    struct node *n = (struct node *)_th_alloc(space, sizeof(struct node_root) + 4 * sizeof(struct _ex_intern *)) ;
    struct node *base ;

    n->exported = exported ;
    n->valid = valid ;
    n->type = MODULE_NODE ;

    n->u.module.module = module;

    *ret = n;

    if (pos == 0) {
        n->next = node ;
        return n ;
    } else {
        --pos ;
        base = node ;
        while(pos > 0) {
            node = node->next ;
            --pos ;
        }
        n->next = node->next ;
        node->next = n ;
        return base ;
    }
}

struct node *_th_insert_theorem(int space, struct node *node, unsigned module, struct _ex_intern *theorem)
{
    struct node *proof, *n;
    struct node *base ;

    n = node;
    if (n == NULL) {
        n = (struct node *)_th_alloc(space, sizeof(struct node_root) + 2 * sizeof(struct _ex_intern *)) ;
        n->exported = 0 ;
        n->valid = 1 ;
        n->type = MODULE_NODE ;
        n->next = NULL ;

        n->u.module.module = module ;
        n->u.module.branch_nodes = NULL ;
        node = n;
    } else {
        if (n->type==MODULE_NODE && n->u.module.module==module) goto cont;
        while (n->next != NULL) {
            n = n->next;
            if (n->type==MODULE_NODE && n->u.module.module==module) goto cont;
        }
        n->next = (struct node *)_th_alloc(space, sizeof(struct node_root) + 3 * sizeof(struct _ex_intern *)) ;
        n = n->next ;
        n->next = NULL ;
        n->exported = 0 ;
        n->valid = 1 ;
        n->type = MODULE_NODE ;

        n->u.module.module = module ;
        n->u.module.branch_nodes = NULL ;
    }

cont:
    base = n->u.module.branch_nodes ;
    while (base != NULL && base->next != NULL) {
        base = base->next ;
    }

    proof = (struct node *)_th_alloc(space, sizeof(struct node_root) + 3 * sizeof(struct _ex_intern *) + sizeof(int)) ;

    proof->exported = 0;
    proof->valid = 1;
    proof->type = PROOF_NODE;
    proof->next = NULL;

    proof->u.proof.proof = (struct proof *)_th_alloc(space, sizeof(struct proof)) ;
    proof->u.proof.property = theorem ;
    proof->u.proof.order = NULL ;
    proof->u.proof.proof->ind_exp = _build_ind_exp(verilog_env,proof->u.proof.property,proof->u.proof.order) ;
    proof->u.proof.proof->term = proof->u.proof.property ;
    proof->u.proof.proof->operation = 0 ;
    proof->u.proof.proof->child_count = 0 ;
    proof->u.proof.display_all = 0 ;
    proof->u.proof.proof->parent = NULL ;

    if (base==NULL) {
        n->u.module.branch_nodes = proof;
    } else {
        base->next = proof;
    }

    return node;
}

struct proof *copy_proof(int space, struct proof *proof)
{
    struct proof *copy ;
    int i ;

    if (proof==NULL) return NULL ;

    copy = (struct proof *)_th_alloc(space,sizeof(struct proof) + (proof->child_count-1) * sizeof(struct proof *)) ;
    copy->term = proof->term ;
    copy->operation = proof->operation ;
    copy->condition = proof->condition ;
    copy->selection = proof->selection ;
    copy->fill_in = proof->fill_in ;
    copy->ind_exp = proof->ind_exp ;
    copy->child_count = proof->child_count ;
    copy->choice = proof->choice ;
    copy->parent = NULL ;
    for (i = 0; i < copy->child_count; ++i) {
        copy->children[i] = copy_proof(space,proof->children[i]) ;
        copy->children[i]->parent = copy ;
    }
	return copy ;
}

int _th_get_suffix(char *pos)
{
    int i;

    i = strlen(pos) - 1;
    while (i > 0 && pos[i] != '.') --i;
    if (pos[i]=='.') ++i ;
    return atoi(pos+i);
}

void _th_strip_suffix(char *pos)
{
    int i;

    i = strlen(pos) - 1;
    while (i > 0 && pos[i] != '.') --i;
    pos[i] = 0;
}

struct node *_th_copy_node(int space, struct node *node)
{
    struct node *copy ;
    int i ;

    if (node==NULL) return NULL ;

    switch (node->type) {
        case DEFINITION_NODE:
            copy = (struct node *)_th_alloc(space,sizeof(struct node_root)+sizeof(struct _ex_intern *) * (3 + node->u.definition.count) + sizeof(int)) ;
            copy->u.definition.template = node->u.definition.template ;
            copy->u.definition.type = node->u.definition.type ;
            copy->u.definition.precondition = node->u.definition.precondition ;
            copy->u.definition.count = node->u.definition.count ;
            for (i = 0; i < node->u.definition.count; ++i) {
                copy->u.definition.rules[i] = node->u.definition.rules[i] ;
            }
            break ;

        case TYPE_NODE:
            copy = (struct node *)_th_alloc(space,sizeof(struct node_root)+sizeof(struct _ex_intern *) * 2) ;
            copy->u.type_definition.ttype = node->u.type_definition.ttype ;
            copy->u.type_definition.ttypedef = node->u.type_definition.ttypedef ;
            break ;

        case COMMENT_NODE:
            copy = (struct node *)_th_alloc(space,sizeof(struct node_root)+strlen(node->u.comment.text)+1) ;
            strcpy(copy->u.comment.text,node->u.comment.text) ;
            break ;

        case PP_DIRECTIVE_NODE:
            copy = (struct node *)_th_alloc(space,sizeof(struct node_root)+strlen(node->u.pp_directive.text)+1) ;
            strcpy(copy->u.pp_directive.text,node->u.pp_directive.text) ;
            break ;

        case IMPORT_NODE:
            copy = (struct node *)_th_alloc(space,sizeof(struct node_root)+strlen(node->u.import.text)+sizeof(struct node *)+1) ;
            copy->u.import.item_list = _th_copy_derivation(space,node->u.import.item_list) ;
            strcpy(copy->u.import.text,node->u.import.text) ;
            break ;

        case PROOF_NODE:
            copy = (struct node *)_th_alloc(space,sizeof(struct node_root)+sizeof(struct _ex_intern *) * 2 + sizeof(struct proof *) + sizeof(int)) ;
            copy->u.proof.display_all = node->u.proof.display_all ;
            copy->u.proof.property = node->u.proof.property ;
            copy->u.proof.order = node->u.proof.order ;
            copy->u.proof.proof = copy_proof(space,node->u.proof.proof) ;
            break ;

        case ATTRIB_NODE:
            copy = (struct node *)_th_alloc(space,sizeof(struct node_root)+sizeof(int) * 2 + sizeof(struct parameter) * node->u.attrib.count) ;
            copy->u.attrib.count = node->u.attrib.count ;
            copy->u.attrib.param = node->u.attrib.param ;
            for (i = 0; i < node->u.attrib.count; ++i) {
                 copy->u.attrib.parameter[i] = node->u.attrib.parameter[i] ;
            }
            break ;

        case PRECEDENCE_NODE:

            switch (node->u.precedence.type) {

                case PREC_LESS:
                case PREC_EQUAL:
                case PREC_MINOR:
                    copy = (struct node *)_th_alloc(space,sizeof(struct node_root)+2*sizeof(unsigned)+sizeof(int)) ;
                    copy->u.precedence.left = node->u.precedence.left ;
                    copy->u.precedence.right = node->u.precedence.right ;
                    break ;

                case PREC_LEX:
                case PREC_GROUP:
                    copy = (struct node *)_th_alloc(space,sizeof(struct node_root)+sizeof(unsigned)*(1+node->u.precedence_list.count)+sizeof(int)*2) ;
                    copy->u.precedence_list.left = node->u.precedence_list.left ;
                    copy->u.precedence_list.count = node->u.precedence_list.count ;
                    for (i = 0; i < node->u.precedence_list.count; ++i) {
                        copy->u.precedence_list.list[i] = node->u.precedence_list.list[i] ;
                    }
                    break ;

                case PREC_BLOCK:
                    copy = (struct node *)_th_alloc(space,sizeof(struct node_root)+sizeof(int)*2+sizeof(unsigned)+sizeof(struct _ex_intern *)) ;
                    copy->u.precedence_block.left = node->u.precedence_block.left ;
                    copy->u.precedence_block.pos = node->u.precedence_block.pos ;
                    copy->u.precedence_block.block = node->u.precedence_block.block ;
                    break ;

                default:
                    printf("Illegal node in derivation.\n") ;
                    exit(1) ;
            }
            break ;

        case MODULE_NODE:
            copy = (struct node *)_th_alloc(space,sizeof(struct node_root)+sizeof(struct _ex_intern *) * 3) ;
            copy->u.module.module = node->u.module.module ;
            copy->u.module.branch_nodes = _th_copy_derivation(space, node->u.module.branch_nodes) ;
            break ;

        default:
            printf("Illegal node in derivation.\n") ;
            exit(1) ;
    }

    copy->type = node->type ;
    copy->exported = node->exported ;
    copy->valid = node->valid ;
    copy->next = NULL ;
    return copy ;
}

struct node *_th_copy_derivation(int space, struct node *node)
{
    struct node *result = _th_copy_node(space, node) ;

    if (node != NULL) {
        result->next = _th_copy_derivation(space,node->next) ;
    }
    return result ;
}

struct node *_th_copy_derivation_range(int space, struct node *node, int start, int count)
{
    if (start > 0 && node != NULL) {
        return _th_copy_derivation_range(space, node->next, start-1, count) ;
    } else if (count > 0 && node != NULL) {
        struct node *result = _th_copy_node(space, node) ;

        if (node != NULL) {
            result->next = _th_copy_derivation_range(space,node->next,0,count-1) ;
        }
        return result ;
    } else {
        return NULL ;
    }
}

struct node *_th_copy_derivation_except_range(int space, struct node *node, char *prefix, int start, int count)
{
    if (prefix[0]) {
        struct node *current, *prev, *sub, *result, *n ;
        int pos = atoi(prefix) ;
        while (*prefix && *prefix != '.') ++prefix ;
        if (*prefix) ++prefix ;
        current = node ;
        prev = NULL ;
        while (current) {
            struct node *next = current->next ;
            if (pos==0) {
                sub = current ;
                if (current->type != MODULE_NODE) {
                    current = _th_copy_node(space, current) ;
                } else {
                    n = (struct node *)_th_alloc(space,sizeof(struct node_root) + 2 * sizeof(struct _ex_intern *)) ;
                    n->valid = current->valid ;
                    n->exported = current->exported ;
                    n->type = MODULE_NODE ;
                    n->u.module.module = current->u.module.module ;
                    n->u.module.branch_nodes =
                        _th_copy_derivation_except_range(space,
                                                         current->u.module.branch_nodes,
                                                         prefix,start,count) ;
                    current = n ;
                }
            } else {
                current = _th_copy_node(space, current) ;
            }
            if (prev) {
                prev->next = current ;
            } else {
                result = current ;
            }
            prev = current ;
            current = next ;
            --pos ;
        }
        return result ;
    } else if (start > 0 && node != NULL) {
        struct node *result = _th_copy_node(space, node) ;

        if (node != NULL) {
            result->next = _th_copy_derivation_except_range(space,node->next,prefix,start-1,count) ;
        }
        return result ;
    } else if (count > 0 && node != NULL) {
        return _th_copy_derivation_except_range(space,node->next,prefix,0,count-1) ;
    } else {
        return _th_copy_derivation(space, node) ;
    }
}

struct node *_th_insert_nodes(struct node *derivation, struct node *insert, int pos)
{
    struct node *base, *dn ;
    if (pos == 0) {
        base = insert ;
    } else {
        base = derivation ;
        while (pos > 1) {
            --pos ;
            derivation = derivation->next ;
        }
        dn = derivation->next ;
        derivation->next = insert ;
        derivation = dn ;
    }
    while (insert->next != NULL) {
        insert = insert->next ;
    }
    insert->next = derivation ;
    return base ;
}

void _th_invalidate_derivation(struct node *node, char *pos)
{
    node = _th_h_find_node(node, pos) ;
    while (node != NULL) {
        if (node->type != COMMENT_NODE) node->valid = 0 ;
        node = node->next ;
    }
}

struct node *_th_load_derivation(unsigned s, char *name) ;

struct node *_th_insert_import(int space, struct node *node, char *pos, char *s, int valid, int exported)
{
    struct node *n = (struct node *)_th_alloc(space, sizeof(struct node_root) + sizeof(struct node *) + strlen(s) + 1) ;
    char name[200] ;

    n->exported = exported ;
    n->valid = valid ;
    n->type = IMPORT_NODE ;
    strcpy(n->u.import.text,s) ;
    sprintf(name, "%s.def", s) ;
    n->u.import.item_list = _th_load_derivation(space, name) ;

    return insert(node, n, pos) ;
}

struct _ex_unifier *get_fill(int space, FILE *f, struct env *env)
{
    char line[2000] ;
    int l ;
    unsigned sym ;

    struct _ex_unifier *u = _th_new_unifier(space) ;

    fgets(line, 100000, f) ;

    l = atoi(line) ;
    while(l > 0) {
        fgets(line, 100000, f) ;
        line[strlen(line)-1] = 0 ;
        sym = _th_intern(line) ;
        fgets(line, 100000, f) ;
        u = _th_add_pair(space,u,sym,_th_parse(env,line)) ;
        --l ;
    }

    return u ;
}

struct _ex_intern *replace_var(struct env *env, struct _ex_intern *e, unsigned var, struct _ex_intern *sub)
{
    struct _ex_intern **args ;
    int i ;

    switch (e->type) {
        case EXP_APPL:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count) ;
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = replace_var(env,e->u.appl.args[i],var,sub) ;
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args) ;
        case EXP_MARKED_VAR:
            if (e->u.marked_var.var==var) {
                return sub ;
            }
            /* Fall through to default case */
        default:
            return e ;
    }
}

static struct proof *load_proof(int space, FILE *f, struct env *env, struct _ex_intern *ind_exp)
{
    char data[2000], *line ;
    int children ;
    struct proof *p ;
    int i, l ;

    fgets(data, 100000, f) ;
    line = data ;
    if (feof(f)) return NULL;
    l = strlen(line) - 1 ;
    if (line[l]=='\n') line[l] = 0 ;

    line = data ;
    line += 5 ;

    children = atoi(line) ;
    p = (struct proof *)_th_alloc(space,sizeof(struct proof) + (children-1) * sizeof(struct proof *)) ;
    p->parent = NULL ;

    while (*line != ' ' && *line) ++line ;

    p->term = _th_parse(NULL, line) ;
    p->child_count = children ;
    p->ind_exp = ind_exp ;

    if (children > 0) {
        fgets(data, 100000, f) ;
        line = data ;
        if (feof(f)) return NULL;
        l = strlen(line) - 1 ;
        if (line[l]=='\n') line[l] = 0 ;

        line = data ;
        if (!strncmp(line,"EXPAND",6)) {
            p->operation = EXPAND ;
            p->selection = atoi(line+7) ;
        } else if (!strncmp(line,"REWRITE",7)) {
            p->operation = REWRITE ;
        } else if (!strncmp(line,"UNIVERSAL",9)) {
            line += 10 ;
            p->operation = UNIVERSAL ;
            p->selection = atoi(line) ;
            while (*line != ' ' && *line) ++line ;
            p->condition = _th_parse(env,line) ;
        } else if (!strncmp(line,"SPECIAL",7)) {
            line += 8 ;
            p->operation = SPECIAL_REWRITE ;
            p->selection = atoi(line) ;
            while (*line != ' ' && *line) ++line ;
            p->condition = (struct _ex_intern *)atoi(line) ;
            p->fill_in = get_fill(space, f, env) ;
        } else if (!strncmp(line,"COND_SPECIAL",12)) {
            line += 13 ;
            p->operation = COND_SPECIAL_REWRITE ;
            p->selection = atoi(line) ;
            while (*line != ' ' && *line) ++line ;
            p->condition = (struct _ex_intern *)atoi(line) ;
            p->fill_in = get_fill(space, f, env) ;
        }

        p->choice = NULL ;

        if (p->operation==EXPAND) {
            char *mark ;
            int count ;
            unsigned **vars, v ;
            struct _ex_intern **res ;
            mark = _th_alloc_mark(ENVIRONMENT_SPACE) ;
            vars = _th_get_expandable_variables(ENVIRONMENT_SPACE, p->term, &count) ;
            v = p->selection ;
            res = _th_expand_var(ENVIRONMENT_SPACE, env, p->term, vars[v][0], vars[v][1],vars[v]+2) ;
            for (i = 0; i < children; ++i) {
                struct _ex_intern *e ;
                if (res[i*2+1]->u.appl.args[0]->type==EXP_VAR) {
                    e = replace_var(env,p->ind_exp,res[i*2+1]->u.appl.args[0]->u.var,_th_mark_vars(env,res[i*2+1]->u.appl.args[1])) ;
                } else {
                    e = replace_var(env,p->ind_exp,res[i*2+1]->u.appl.args[1]->u.var,_th_mark_vars(env,res[i*2+1]->u.appl.args[0])) ;
                }
                p->children[i] = load_proof(space, f, env, e) ;
                p->children[i]->parent = p ;
                p->children[i]->choice = res[i*2+1] ;
                /*printf("IND: %s\n", _th_print_exp(p->ind_exp)) ;*/
            }
            _th_alloc_release(ENVIRONMENT_SPACE,mark) ;
        } else {
            for (i = 0; i < children; ++i) {
                p->children[i] = load_proof(space, f, env, ind_exp) ;
            }
        }
        if (p->operation==UNIVERSAL) {
            p->children[0]->choice = p->condition ;
            p->children[1]->choice = _ex_intern_appl(INTERN_NOT,1,&p->condition) ;
        }
    }

    return p ;
}

struct node *_th_load_proof(int space, FILE *f, struct env *env, struct node *node, int pos, struct _ex_intern *proof, struct _ex_intern *order, int valid, int exported)
{
    struct node *n = (struct node *)_th_alloc(space, sizeof(struct node_root) + sizeof(struct _ex_intern *) * 2 + sizeof(struct proof *) + sizeof(int)) ;
    struct node *base ;

    n->exported = exported ;
    n->valid = valid ;
    n->type = PROOF_NODE ;
   
    n->u.proof.property = proof ;
    n->u.proof.order = order ;
    n->u.proof.proof = load_proof(space, f, env, _build_ind_exp(env,proof,order)) ;
    n->u.proof.display_all = 0 ;

    if (n->u.proof.property==NULL || (n->u.proof.order==NULL && order)) return NULL ;
    if (pos == 0) {
        n->next = node ;
        return n ;
    } else {
        --pos ;
        base = node ;
        while(pos > 0) {
            node = node->next ;
            --pos ;
        }
        n->next = node->next ;
        node->next = n ;
        return base ;
    }
}

struct env *_th_add_to_env(int s, struct env *env, struct node *der)
{
    int i ;
    switch (der->type) {

        case ATTRIB_NODE:
            _th_add_attrib(env,der->u.attrib.param,der->u.attrib.count,der->u.attrib.parameter) ;
            break ;

        case TYPE_NODE:
            _th_add_type_definition(env,der->u.type_definition.ttype,der->u.type_definition.ttypedef) ;
            break ;

        case IMPORT_NODE:
            _th_build_env(-1, env, der->u.import.item_list) ;
            break ;

        case PROOF_NODE:
            _th_derive_and_add(env, _th_derive_simplify(env,der->u.proof.property));
            break ;

        case DEFINITION_NODE:
            _th_add_function(env,
                             der->u.definition.template,
                             der->u.definition.type,
                             der->u.definition.precondition,
                             der->u.definition.count,
                             der->u.definition.rules) ;
            for (i = 0; i < der->u.definition.count; ++i) {
                 _th_derive_and_add_property(s, env, der->u.definition.rules[i]) ;
            }
            break ;

        case PRECEDENCE_NODE:
            switch (der->u.precedence.type) {
                case PREC_LESS:
                    _th_add_precedence(s,env,der->u.precedence.left,der->u.precedence.right) ;
                    break ;
                case PREC_EQUAL:
                    _th_add_equal_precedence(s,env,der->u.precedence.left,der->u.precedence.right) ;
                    break ;
            }
            break ;
    }

    return env ;
}

struct node *read_nodes(unsigned s, struct env *env, FILE *f, int count)
{
    char data[100000], *line ;
    struct node *der = NULL, *d ;
    int n = 0 ;
    int l ;
    int exported, valid ;
    struct _ex_intern *e, *order ;
    char pos[20] ;

    while (count != 0) {
        --count;
        fgets(data, 100000, f) ;
        line = data ;
        if (feof(f)) break ;
        l = strlen(line) -1 ;
        if (line[l]=='\n') line[l] = 0 ;

        exported = 0 ;
        valid = 1 ;

        if (!strncmp(line,"INVALID",7)) {
            line += 8 ;
            valid = 0 ;
        }

        if (!strncmp(line,"EXPORTED",8)) {
            line += 9 ;
            exported = 1 ;
        }

        if (strncmp(line,"PROOF",5)==0) {
            e = _th_parse(env,line+6) ;
            fgets(data, 100000, f) ;
            line = data ;
            if (feof(f)) break ;
            l = strlen(line) -1 ;
            if (line[l]=='\n') line[l] = 0 ;
            if (line[0]=='N') {
                order = NULL ;
            } else {
                order = _th_parse(env,line + 6) ;
            }
            der = _th_load_proof(s, f, env, der, n++, e, order, valid, exported) ;
        } else if (strncmp(line,"COMMENT",7)==0) {
            sprintf(pos, "%d", n++);
            der = _th_insert_comment(s,der,pos,line+8, valid, exported) ;
        } else if (strncmp(line,"PP",2)==0) {
            sprintf(pos, "%d", n++);
            der = _th_insert_pp_directive(s,der,pos,line+13, valid, exported) ;
        } else if (strncmp(line,"TYPEDEF",7)==0) {
            sprintf(pos, "%d", n++);
            der = _th_insert_type(s,der,pos,line+5, valid, exported) ;
        } else if (strncmp(line,"IMPORT",6)==0) {
            sprintf(pos, "%d", n++);
            der = _th_insert_import(s,der,pos,line+7, valid, exported) ;
        } else if (strncmp(line,"ATTRIB",6)==0) {
            sprintf(pos, "%d", n++) ;
            der = _th_insert_attrib(s,der,pos,line+7, valid, exported) ;
        } else if (strncmp(line,"PRECEDENCE",10)==0) {
            sprintf(pos, "%d", n++);
            der = _th_insert_precedence(s,der,pos,line+11, valid, exported) ;
        } else if (strncmp(line,"DEFINITION",10)==0) {
            int count = atoi(line+11) ;
            count += 3 ;
            _th_start_definition();
            while(count-- > 0) {
                fgets(data, 100000, f) ;
                _th_add_definition_line(env,data) ;
            }
            sprintf(pos, "%d", n++);
            der = _th_insert_definition(s, der, pos, valid, exported) ;
        } else if (strncmp(line,"MODULE",6)==0) {
            int total;
            struct env *cenv = _th_copy_env(ENVIRONMENT_SPACE, env) ;
            fgets(data, 100000, f);
            total = atoi(data);
            der = insert_module_node(s,der,n++,_th_intern(line+7),valid,exported, &d);
            d->u.module.branch_nodes = read_nodes(s,cenv,f,total);
        }
        d = der ;
        while (d->next != NULL) d = d->next ;
        env = _th_add_to_env(ENVIRONMENT_SPACE, env, d) ;
    }
    return der ;
}

struct node *_th_load_derivation(unsigned s, char *name)
{
    FILE *f = fopen(name, "r") ;
    struct node *der = NULL ;
    int n = 0 ;
    char *mark ;
    struct env *env ;

    if (f==NULL) {
        printf("Error: file %s not found\n", name);
        return NULL;
    }

    mark = _th_alloc_mark(ENVIRONMENT_SPACE) ;
    env = _th_copy_env(ENVIRONMENT_SPACE, _th_base_env) ;

    der = read_nodes(s, env, f, -1) ;

    _th_alloc_release(ENVIRONMENT_SPACE, mark) ;
    return der ;
}

static void print_unifier(FILE *f, struct _ex_unifier *fill_in)
{
    char *mark = _th_alloc_mark(ENVIRONMENT_SPACE) ;
    char *dom ;
    unsigned v, count=0 ;
    dom = _th_dom_init(ENVIRONMENT_SPACE, fill_in) ;
    while (v = _th_dom_next(dom)) {
        ++count ;
    }
    fprintf(f, "%d\n", count) ;
    dom = _th_dom_init(ENVIRONMENT_SPACE, fill_in) ;
    while (v = _th_dom_next(dom)) {
        fprintf(f, "%s\n%s\n", _th_intern_decode(v), _th_print_exp(_th_apply(fill_in,v))) ;
    }
    _th_alloc_release(ENVIRONMENT_SPACE,mark) ;
}

static void print_proof_nodes(FILE *f, struct proof *proof)
{
    int i ;

    fprintf(f, "NODE %d %s\n", proof->child_count, _th_print_exp(proof->term)) ;
    if (proof->child_count > 0) {
        switch (proof->operation) {
            case REWRITE:
                fprintf(f, "REWRITE\n") ;
                break ;
            case EXPAND:
                fprintf(f, "EXPAND %d\n", proof->selection) ;
                break ;
            case UNIVERSAL:
                fprintf(f, "UNIVERSAL %d %s\n", proof->selection, _th_print_exp(proof->condition)) ;
                break ;
            case SPECIAL_REWRITE:
                fprintf(f, "SPECIAL %d %d\n", proof->selection, proof->condition) ;
                print_unifier(f, proof->fill_in) ;
                break ;
            case COND_SPECIAL_REWRITE:
                fprintf(f, "COND_SPECIAL %d %d\n", proof->selection, proof->condition) ;
                print_unifier(f, proof->fill_in) ;
                break ;
        }
    }

    for (i = 0; i < proof->child_count; ++i) {
        print_proof_nodes(f,proof->children[i]) ;
    }
}

int save_nodes(struct node *der, FILE *f)
{
    int save_definition = 0;
    struct node *sub;
    int count;
    int i;

    while(der != NULL) {

        if (!der->valid) {
            fprintf(f, "INVALID ") ;
        }

        if (der->exported) {
            save_definition = 1 ;
            fprintf(f, "EXPORTED ") ;
        }

        switch (der->type) {

            case DEFINITION_NODE:
                fprintf(f, "DEFINITION %d\n", der->u.definition.count) ;
                fprintf(f, "FUNCTION %s\n", _th_print_exp(der->u.definition.template)) ;
                fprintf(f, "TYPE %s\n", _th_print_exp(der->u.definition.type)) ;
                fprintf(f, "PRECONDITION %s\n", _th_print_exp(der->u.definition.precondition)) ;
                for (i = 0; i < der->u.definition.count; ++i) {
                    fprintf(f, "%s\n", _th_print_exp(der->u.definition.rules[i])) ;
                }
                break ;
            case TYPE_NODE:
                fprintf(f, "TYPEDEF %s=", _th_print_exp(der->u.type_definition.ttype)) ;
                fprintf(f, "%s\n", _th_print_exp(der->u.type_definition.ttypedef)) ;
                break ;
            case PROOF_NODE:
                fprintf(f, "PROOF %s\n", _th_print_exp(der->u.proof.property)) ;
                if (der->u.proof.order != NULL) {
                    fprintf(f, "ORDER %s\n", _th_print_exp(der->u.proof.order)) ;
                } else {
                    fprintf(f, "NO ORDER\n") ;
                }
                print_proof_nodes(f, der->u.proof.proof) ;
                break ;
            case ATTRIB_NODE:
                fprintf(f, "ATTRIB ") ;
                _th_print_attrib(f, der) ;
                fprintf(f, "\n") ;
                break ;
            case PRECEDENCE_NODE:
                switch (der->u.precedence.type) {
                    case PREC_EQUAL:
                        fprintf(f,"PRECEDENCE %s = %s\n",
                                _th_intern_decode(der->u.precedence.left),
                                _th_intern_decode(der->u.precedence.right)) ;
                        break ;
                    case PREC_LESS:
                        fprintf(f,"PRECEDENCE %s < %s\n",
                                _th_intern_decode(der->u.precedence.left),
                                _th_intern_decode(der->u.precedence.right)) ;
                        break ;
                }
                break ;
            case COMMENT_NODE:
                fprintf(f, "COMMENT %s\n", der->u.comment.text) ;
                break ;
            case IMPORT_NODE:
                fprintf(f, "IMPORT %s\n", der->u.import.text) ;
                break ;
            case PP_DIRECTIVE_NODE:
                fprintf(f, "PP %s\n", der->u.pp_directive.text) ;
                break ;
            case MODULE_NODE:
                fprintf(f, "MODULE %s\n", _th_intern_decode(der->u.module.module)) ;
                sub = der->u.module.branch_nodes ;
                count = 0 ;
                while (sub) {
                    sub = sub->next ;
                    ++count ;
                }
                fprintf(f, "%d\n", count) ;
                save_nodes(der->u.module.branch_nodes, f) ;
                break ;
        }
        der = der->next ;
    }
    return save_definition ;
}

void _th_save_derivation(struct node *der, char *name)
{
    FILE *f = fopen(name,"w") ;
    int save_definition = 0 ;
    char ex_name[200] ;
    int n, i ;

    save_definition = save_nodes(der, f);
    fclose(f) ;

    if (save_definition) {
        strcpy(ex_name, name) ;
        n = strlen(ex_name) ;
        if (strcmp(ex_name+n-4,".der")) {
            strcat(ex_name,".def") ;
        } else {
            ex_name[n-1] = 'f' ;
        }

        f = fopen(ex_name, "w") ;

        while(der != NULL && der->type != MODULE_NODE) {

            if (der->exported) {
                switch (der->type) {

                    case DEFINITION_NODE:
                        fprintf(f, "DEFINITION %d\n", der->u.definition.count) ;
                        fprintf(f, "FUNCTION %s\n", _th_print_exp(der->u.definition.template)) ;
                        fprintf(f, "TYPE %s\n", _th_print_exp(der->u.definition.type)) ;
                        fprintf(f, "PRECONDITION %s\n", _th_print_exp(der->u.definition.precondition)) ;
                        for (i = 0; i < der->u.definition.count; ++i) {
                            fprintf(f, "%s\n", _th_print_exp(der->u.definition.rules[i])) ;
                        }
                        break ;
                    case TYPE_NODE:
                        fprintf(f, "TYPEDEF %s=", _th_print_exp(der->u.type_definition.ttype)) ;
                        fprintf(f, "%s\n", _th_print_exp(der->u.type_definition.ttypedef)) ;
                        break ;
                    case PROOF_NODE:
                        fprintf(f, "PROPERTY %s\n", _th_print_exp(der->u.proof.property)) ;
                        break ;
                    case ATTRIB_NODE:
                        fprintf(f, "ATTRIB ") ;
                        _th_print_attrib(f, der) ;
                        fprintf(f, "\n") ;
                        break ;
                    case PRECEDENCE_NODE:
                        switch (der->u.precedence.type) {
                            case PREC_EQUAL:
                                fprintf(f,"PRECEDENCE %s = %s\n",
                                        _th_intern_decode(der->u.precedence.left),
                                        _th_intern_decode(der->u.precedence.right)) ;
                                break ;
                            case PREC_LESS:
                                fprintf(f,"PRECEDENCE %s < %s\n",
                                        _th_intern_decode(der->u.precedence.left),
                                        _th_intern_decode(der->u.precedence.right)) ;
                                break ;
                        }
                        break ;
                    case IMPORT_NODE:
                        fprintf(f, "IMPORT %s\n", der->u.import.text) ;
                        break ;
                    case PP_DIRECTIVE_NODE:
                        fprintf(f, "PP %s\n", der->u.pp_directive.text) ;
                        break ;
                }
            }
            der = der->next ;
        }
        fclose(f) ;
    }
}

struct env *_th_build_env(int count, struct env *env, struct node *der)
{
    while (count > 0) {
        env = _th_add_to_env(ENVIRONMENT_SPACE, env, der) ;
        der = der->next ;
        --count ;
    }

    return env ;
}

struct env *_th_h_build_env(char *pos, struct env *env, struct node *der)
{
    struct node *n;
    while (*pos) {
        env = _th_build_env(atoi(pos), env, der);
        n = _th_find_node(der, atoi(pos));
        while (*pos && *pos != '.') ++pos;
        if (*pos) {
            struct module_list *ml ;
            ++pos;
            if (n->type != MODULE_NODE) {
                _th_add_to_env(ENVIRONMENT_SPACE, env, n);
                printf("Error: Module node expected\n");
                return env;
            }
            ml = find_module(n->u.module.module) ;
            _th_add_verilog_assertions(env, ml) ;
            der = n->u.module.branch_nodes;
        }
    }
    return env ;
}

struct env *_th_build_module_env(struct env *env, unsigned module, struct node *der)
{
    while (der != NULL) {
        if (der->type==MODULE_NODE && der->u.module.module==module) {
            der = der->u.module.branch_nodes;
        } else {
            env = _th_add_to_env(ENVIRONMENT_SPACE, env, der);
            der = der->next;
        }
    }
    return env;
}

struct node *_th_get_proof(int s, struct node *der, char *n)
{
    der = _th_h_find_node(der, n) ;
    if (der->type != PROOF_NODE) return NULL ;
    return _th_copy_node(s,der) ;
}

struct node *_th_return_proof(struct node *der, struct node *node, char *n)
{
    der = insert(der, node, n) ;
    node->next = node->next->next ;
    return der ;
}

static int _total_node_count(struct proof *proof)
{
    int count, i ;

    count = 1 ;
    for (i = 0; i < proof->child_count; ++i) {
        count += _total_node_count(proof->children[i]) ;
    }
    return count ;
}

int _th_total_node_count(struct node *node)
{
    return _total_node_count(node->u.proof.proof) ;
}

static struct proof *_get_unfinished_node(int *num, struct proof *proof)
{
    int i ;

    if (proof->child_count==0 && proof->term!=_ex_true) {
        if (*num==0) {
            *num = -1 ;
            return proof ;
        } else {
            --*num ;
        }
    }

    for (i = 0; i < proof->child_count; ++i) {
        struct proof *r = _get_unfinished_node(num, proof->children[i]) ;
        if (*num < 0) return r ;
    }

    return NULL ;
}

struct proof *_th_get_unfinished_node(int num, struct node *node)
{
    return _get_unfinished_node(&num, node->u.proof.proof) ;
}

static struct proof *_get_node(int *num, int *depth, struct proof *proof)
{
    int i ;

    if (*num==0) {
        *num = -1 ;
        return proof ;
    }

    --*num ;

    ++*depth ;
    for (i = 0; i < proof->child_count; ++i) {
        struct proof *r = _get_node(num, depth, proof->children[i]) ;
        if (*num < 0) return r ;
    }
    --*depth ;

    return NULL ;
}

struct proof *_th_get_node(int num, int *depth, struct node *node)
{
    *depth = 0;
    return _get_node(&num, depth, node->u.proof.proof) ;
}

static int _unfinished_node_count(struct proof *proof)
{
    int count, i ;

    if (proof->child_count == 0 && proof->term != _ex_true) {
        count = 1;
    } else {
        count = 0 ;
        for (i = 0; i < proof->child_count; ++i) {
            count += _unfinished_node_count(proof->children[i]) ;
        }
    }
    return count;
}

int _th_unfinished_node_count(struct node *node)
{
    return _unfinished_node_count(node->u.proof.proof) ;
}

int node_count(struct proof *p)
{
    int r = 1 ;
    int i ;
    for (i = 0; i < p->child_count; ++i) {
        r += node_count(p->children[i]) ;
    }
    return r ;
}

int _th_cancel_operation(struct proof *p)
{
    int r = node_count(p) ;
    p->child_count = 0 ;
    return r ;
}

static struct proof *_replace_node(struct proof *proof,
                                   struct proof *old, struct proof *new)
{
    int i ;

    if (proof==old) return new ;

    for (i = 0; i < proof->child_count; ++i) {
        proof->children[i] = _replace_node(proof->children[i],old,new) ;
    }

    return proof ;
}

static struct proof *rewrite_proof ;
static struct node *rewrite_node ;
static int operation ;

void _th_special_rewrite_operation(int s, struct env *env, struct node *node,
                                   struct proof *proof, unsigned c, unsigned *sub)
{
    char *mark ;
    rewrite_proof = proof ;
    rewrite_node = node ;

    mark = _th_alloc_mark(REWRITE_SPACE) ;
    _th_push_context_rules(env) ;
    if (proof->ind_exp) _th_add_context_property(env,proof->ind_exp) ;
    _th_special_rewrite_rule(s, env, proof->term, c, sub) ;
    _th_pop_context_rules(env) ;
    _th_alloc_release(REWRITE_SPACE,mark) ;
}

void _th_condition_special_rewrite_operation(int s, struct env *env, struct node *node,
                                             struct proof *proof, unsigned c, unsigned *sub)
{
    char *mark ;
    rewrite_proof = proof ;
    rewrite_node = node ;

    mark = _th_alloc_mark(REWRITE_SPACE) ;
    _th_push_context_rules(env) ;
    if (proof->ind_exp) _th_add_context_property(env,proof->ind_exp) ;
    _th_cond_special_rewrite_rule(s, env, proof->term, c, sub) ;
    _th_pop_context_rules(env) ;
    _th_alloc_release(REWRITE_SPACE,mark) ;
}

int _th_rewrite_operation(int s, struct env *env, struct node *node,
                          struct proof *proof)
{
    struct _ex_intern *result ;
    char *mark ;

    if (proof->child_count != 0) return 1 ;

    mark = _th_alloc_mark(REWRITE_SPACE) ;
    _th_push_context_rules(env) ;
    if (proof->ind_exp) _th_add_context_property(env,proof->ind_exp) ;
    result = _th_rewrite(env,proof->term) ;
    _th_pop_context_rules(env) ;
    _th_alloc_release(REWRITE_SPACE,mark) ;

    if (result==proof->term) {
        _th_possibility_count = 0 ;
        return 0 ;
    }

    _th_possibility_count = 1 ;
    _th_check_possible_rewrites(1) ;
    _th_possible_rewrites[0] = result ;
    _th_possible_conditions[0] = _ex_true ;

    rewrite_node = node ;
    rewrite_proof = proof ;
    operation = REWRITE ;

    return 0 ;
}

void _th_incorporate_expansion(int s, struct env *env, struct node *n, struct proof *p, int v)
{
    unsigned **vars ;
    struct _ex_intern **res ;
    char *mark ;
    struct proof *np ;
    int i, count = 0;

    mark = _th_alloc_mark(ENVIRONMENT_SPACE) ;

    vars =  _th_get_expandable_variables(ENVIRONMENT_SPACE, p->term, &count) ;
    res = _th_expand_var(ENVIRONMENT_SPACE, env, p->term, vars[v][0],vars[v][1],vars[v]+2) ;
    if (res==NULL) return ;

    count = 0 ;
    while (res[count*2]) ++count ;

    np = (struct proof *)_th_alloc(s,sizeof(struct proof)+count*sizeof(struct proof *)) ;
    *np = *p ;
    n->u.proof.proof = _replace_node(n->u.proof.proof, p, np) ;
    np->child_count = count ;
    np->operation = EXPAND ;
    np->selection = v ;
    for (i = 0; i < count; ++i) {
        p = np->children[i] = (struct proof *)_th_alloc(s,sizeof(struct proof)) ;
        np->parent = p ;
        p->child_count = 0 ;
        p->term = res[i*2] ;
        p->choice = res[i*2+1] ;
        if (p->choice->u.appl.functor==INTERN_EQUAL) {
            if (p->choice->u.appl.args[0]->type==EXP_VAR) {
                p->ind_exp = replace_var(env,np->ind_exp,p->choice->u.appl.args[0]->u.var,_th_mark_vars(env,p->choice->u.appl.args[1])) ;
            } else {
                p->ind_exp = replace_var(env,np->ind_exp,p->choice->u.appl.args[1]->u.var,_th_mark_vars(env,p->choice->u.appl.args[0])) ;
            }
            /*printf("IND: %s\n", _th_print_exp(p->ind_exp)) ;*/
        }
    }

    _th_alloc_release(ENVIRONMENT_SPACE,mark) ;
}

void _th_incorporate_universal(int s, struct env *env, struct node *n, struct proof *p, struct _ex_intern *cond, int selection, unsigned c, unsigned *terms)
{
    struct _ex_intern **res ;
    char *mark ;
    struct proof *np ;
    int i, count = 0;

    mark = _th_alloc_mark(ENVIRONMENT_SPACE) ;

    res = _th_expand_universal(ENVIRONMENT_SPACE, env, p->term, cond, c, terms) ;
    if (res==NULL) return ;

    count = 0 ;
    while (res[count*2]) ++count ;

    np = (struct proof *)_th_alloc(s,sizeof(struct proof)+count*sizeof(struct proof *)) ;
    *np = *p ;
    n->u.proof.proof = _replace_node(n->u.proof.proof, p, np) ;
    np->child_count = count ;
    np->operation = UNIVERSAL ;
    np->condition = cond ;
    np->selection = selection ;
    for (i = 0; i < count; ++i) {
        p = np->children[i] = (struct proof *)_th_alloc(s,sizeof(struct proof)) ;
        p->parent = np ;
        p->child_count = 0 ;
        p->term = res[i*2] ;
        p->choice = res[i*2+1] ;
        p->ind_exp = np->ind_exp ;
    }

    _th_alloc_release(ENVIRONMENT_SPACE,mark) ;
}

void _th_incorporate_rewrite(struct env *env, int s, int r, struct _ex_unifier *u)
{
    struct proof *p, *q ;

    if (_th_possible_conditions[r] != _ex_true) {
        p = (struct proof *)_th_alloc(s,sizeof(struct proof) + sizeof(struct proof *)) ;
    } else {
        p = (struct proof *)_th_alloc(s,sizeof(struct proof)) ;
    }
    *p = *rewrite_proof ;
    rewrite_node->u.proof.proof = _replace_node(rewrite_node->u.proof.proof, rewrite_proof, p) ;
    p->children[0] = (struct proof *)_th_alloc(s,sizeof(struct proof)) ;
    p->children[0]->parent = p ;
    p->operation = operation ;
    p->selection = r ;
    if (_th_possible_conditions[r] != _ex_true) {
        p->child_count = 2 ;
        p->children[1] = (struct proof *)_th_alloc(s,sizeof(struct proof)) ;
        q = p->children[1] ;
        q->parent = p ;
        if (_th_keep_inductive) {
            q->ind_exp = p->ind_exp ;
        } else {
            q->ind_exp = 0 ;
        }
        q->term = _th_marked_subst(env,u,_th_possible_conditions[r]) ;
        q->child_count = 0 ;
    } else {
        p->child_count = 1 ;
    }
    p->children[0]->ind_exp = p->ind_exp ;
    p = p->children[0] ;
    p->term = _th_marked_subst(env,u,_th_possible_rewrites[r]) ;
    p->child_count = 0 ;
}
