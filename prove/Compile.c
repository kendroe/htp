/*
 * compile.c
 *
 * A compiler that converts C code into the intermediate form of the
 * verification tool.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Globalsp.h"
#include "../rewlib/RewriteLog.h"

static void print_indent(int i)
{
    while(i--) printf(" ") ;
}

static void print_member_function(int indent, struct member_function *mf)
{
    int i ;
    
    while(mf != NULL) {
        print_indent(indent) ;
#ifndef FAST
        _d_print2("Function %s %s\n", _th_print_exp(mf->return_type), _th_intern_decode(mf->name)) ;
#endif
        for (i = 0; i < mf->param_count; ++i) {
            print_indent(indent+4) ;
            printf("%s\n", _th_print_exp(mf->param_type[i]))  ;
        }
        mf = mf->next ;
    }
}

static void print_field_info(int indent, struct record_field *r)
{
    while (r != NULL) {
        print_indent(indent) ;
        printf("field %s %s (%d)\n", _th_print_exp(r->type),
            _th_intern_decode(r->name), r->ref_num) ;
        r = r->next ;
    }
}

static void print_parent_info(int indent, struct record_list *r)
{
    while (r != NULL) {
        print_indent(indent) ;
        printf("Parent: %s %d\n", _th_intern_decode(r->record->name), r->start_point) ;
        r = r-> next ;
    }
}

static void print_record_info(int indent, struct record_info *r)
{
    while (r != NULL) {
        print_indent(indent) ;
        printf("Class %s\n", _th_intern_decode(r->name)) ;
        print_parent_info(indent+4,r->parents) ;
        print_field_info(indent+4,r->field) ;
        print_member_function(indent+4, r->functions) ;
        r = r->next ;
    }
}

static void print_variables(int indent, struct record_field *rf)
{
    while (rf != NULL) {
        printf("var %s %s (%d) = ",
            _th_print_exp(rf->type),
            _th_intern_decode(rf->name),
            rf->ref_num) ;
        printf("%s\n", _th_print_exp(rf->initialization)) ;
        rf = rf->next ;
    }
}

static void print_typedefs(int indent, struct typedefs *t)
{
    while (t != NULL) {
        print_indent(indent) ;
        printf("typedef %s %s\n", _th_print_exp(t->type), _th_intern_decode(t->name)) ;
        t = t->next ;
    }
}

static void print_name_space(int indent, struct name_space *ns)
{
    while (ns != NULL) {
        print_indent(indent) ;
        printf("name space %s\n", _th_intern_decode(ns->name)) ;
        print_name_space(indent+4,ns->child) ;
        print_record_info(indent+4,ns->records) ;
        print_variables(indent+4,ns->variables) ;
        print_typedefs(indent+4,ns->typedefs) ;
        ns = ns->next ;
    }
}

struct name_space *_th_name_space ;

struct _ex_intern *find_field_type(struct _ex_intern *type, char *field)
{
    struct name_space *ns ;
    unsigned f = _th_intern(field) ;
    
    //printf("find_field_type %s %s\n", _th_print_exp(type), field) ;

    type = type->u.appl.args[0] ;
    
    ns = _th_name_space ;
    
    while (type->u.appl.count > 0) {
        unsigned name = _th_intern(type->u.appl.args[0]->u.appl.args[0]->u.string) ;
        if (type->u.appl.args[1]->u.appl.count==0) {
            struct record_info *ri = ns->records ;
            struct record_field *r ;
            while (ri && name != ri->name) {
                ri = ri->next ;
            }
            if (ri==NULL) return NULL ;
            r = ri->field ;
            while (r && r->name != f) r = r->next ;
            if (r==NULL) return NULL ;
            return r->type ;
        } else {
            ns = ns->child ;
            while (ns && name != ns->name) ns = ns->next ;
            if (ns==NULL) return NULL ;
            type = type->u.appl.args[1] ;
        }
    }
    return NULL ;
}


static int cons_count(struct _ex_intern *e)
{
    if (e->u.appl.functor==INTERN_NIL) return 0 ;
    return 1+cons_count(e->u.appl.args[1]) ;
}

char name[2000] ;

static void get_name(struct _ex_intern *e)
{
    if (e->u.appl.count==1) {
        strcpy(name, e->u.appl.args[0]->u.string) ;
    } else {
        strcpy(name, _th_print_exp(e)) ;
    }
}

static struct name_space *find_name_space(int space, struct name_space *ns, struct _ex_intern *id)
{
    struct name_space *n ;
    
    while (id->u.appl.args[1]->type==EXP_APPL &&
        id->u.appl.count > 0) {
        unsigned iname ;
        get_name(id->u.appl.args[0]) ;
        if (id->u.appl.args[1]->type != EXP_APPL || id->u.appl.args[1]->u.appl.count < 2) return ns ;
        n = ns->child ;
        iname = _th_intern(name) ;
        while (n != NULL) {
            if (n->name==iname) break ;
            n = n->next ;
        }
        if (n == NULL) {
            if (space < 0) return NULL ;
            n = (struct name_space *)_th_alloc(space, sizeof(struct name_space)) ;
            n->next = ns->child ;
            ns->child = n ;
            n->parent = ns ;
            n->name = _th_intern(name) ;
            n->records = NULL ;
            n->typedefs = NULL ;
            n->variables = NULL ;
        }
        id = id->u.appl.args[1] ;
    }
    return n ;
}

static char *get_complete_name_string(struct _ex_intern *id)
{
    static char complete_name[2000] ;
    
    complete_name[0] = 0 ;
    
    while (id->type==EXP_APPL &&
        id->u.appl.count > 0) {
        get_name(id->u.appl.args[0]) ;
        if (complete_name[0]) strcat(complete_name, "::") ;
        strcat(complete_name, name) ;
        id = id->u.appl.args[1] ;
    }
    return complete_name ;
}

static void add_typedef(int space, struct name_space *ns, struct _ex_intern *t, struct _ex_intern *i)
{
    struct typedefs *ts ;
    
    ns = find_name_space(space,ns, i) ;
    ts = (struct typedefs *)_th_alloc(space, sizeof(struct typedefs)) ;
    ts->next = ns->typedefs ;
    ns->typedefs = ts ;
    ts->name = _th_intern(name) ;
    ts->type = t ;
}

static void add_variable(int space, struct name_space *ns, struct _ex_intern *n, struct _ex_intern *i, struct _ex_intern *t)
{
    struct record_field *r ;
    
    ns = find_name_space(space,ns, n) ;
    r = (struct record_field *)_th_alloc(space, sizeof(struct record_field)) ;
    r->next = ns->variables ;
    ns->variables = r ;
    r->name = _th_intern(name) ;
    r->type = t ;
    r->initialization = i ;
    if (r->next==NULL) {
        r->ref_num = 0 ;
    } else {
        r->ref_num = r->next->ref_num + 1 ;
    }
}

static void add_field(int space, struct record_info *ri, unsigned name, struct _ex_intern *t)
{
    struct record_field *r ;
    
    r = (struct record_field *)_th_alloc(space, sizeof(struct record_field)) ;
    r->next = ri->field ;
    ri->field = r ;
    r->name = name;
    r->type = t ;
    if (r->next==NULL) {
        r->ref_num = 0 ;
    } else {
        r->ref_num = r->next->ref_num + 1 ;
    }
}

struct record_info *find_class_def(struct name_space *ns, struct _ex_intern *id)
{
    struct name_space *n ;
    struct record_info *ri ;
    unsigned iname ;
retry:
    if (ns==NULL) return NULL ;
    n = find_name_space(-1, ns, id) ;
    if (n==NULL) {
        ns = ns->parent ;
        goto retry ;
    }
    ri = n->records ;
    iname = _th_intern(name) ;
    while (ri != NULL) {
        if (iname == ri->name) return ri ;
        ri = ri->next ;
    }
    ns = ns->parent ;
    goto retry ;
}

void add_fields(int space, struct record_info *ri, struct record_field *f)
{
    if (f == NULL) return ;
    
    add_fields(space, ri, f->next) ;
    add_field(space, ri, f->name, f->type) ;
}

void add_class_proc(int space, struct record_info *ri, unsigned name, int is_virtual, struct _ex_intern *rtype, struct _ex_intern *params)
{
    struct member_function *mf ;
    int count = cons_count(params) ;
    int i ;
    
    mf = (struct member_function *)_th_alloc(space, sizeof(struct member_function) + (count-1) * sizeof(struct _ex_intern *)) ;
    for (i = 0; i < count; ++i) {
        mf->param_type[i] = params->u.appl.args[0] ;
        params = params->u.appl.args[1] ;
    }
    mf->param_count = count ;
    mf->next = ri->functions ;
    ri->functions = mf ;
    mf->name = name ;
    mf->return_type = rtype ;
}

static void process_class(int space, struct name_space *ns, struct _ex_intern *e)
{
    struct record_info *ri = (struct record_info *)_th_alloc(space, sizeof(struct record_info)) ;
    struct _ex_intern *id ;
    struct _ex_intern *f ;
    printf("Processing class %s\n", _th_print_exp(e)) ;
    fflush(stdout) ;
    ri->next = ns->records ;
    ns->records = ri ;
    
    ri->field = NULL ;
    ri->name = _th_intern(e->u.appl.args[0]->u.appl.args[0]->u.appl.args[0]->u.string) ;
    ri->parents = ri->children = NULL ;
    ri->functions = NULL ;
    
    f = e->u.appl.args[1] ;
    while (f->type == EXP_APPL && f->u.appl.count > 1) {
        struct record_info *p ;
        printf("parent list %s\n", _th_print_exp(f)) ;
        printf("    class %s\n", _th_intern_decode(ri->name)) ;
        id = f->u.appl.args[0]->u.appl.args[2] ;
        f = f->u.appl.args[1] ;
        p = find_class_def(ns, id) ;
        if (p != NULL) {
            struct record_list *l ;
            l = (struct record_list *)_th_alloc(space,sizeof(struct record_list)) ;
            l->next = p->children ;
            p->children = l ;
            l->record = ri ;
            l = (struct record_list *)_th_alloc(space,sizeof(struct record_list)) ;
            l->next = ri->parents ;
            ri->parents = l ;
            l->record = p ;
            if (ri->field==NULL) {
                l->start_point = 0 ;
            } else {
                l->start_point = ri->field->ref_num ;
            }
            add_fields(space, ri, p->field) ;
        }
    }
    e = e->u.appl.args[2] ;
    while (e->type==EXP_APPL && e->u.appl.count > 0) {
        printf("Processing members %s\n", _th_print_exp(e)) ;
        f = e->u.appl.args[0] ;
        e = e->u.appl.args[1] ;
        printf("f = %s\n", _th_print_exp(f)) ;
        fflush(stdout) ;
        if (f->type==EXP_APPL) {
            switch (f->u.appl.functor) {
            case INTERN_CCLASS_VARIABLE:
                printf("    Var = %s\n", _th_print_exp(f)) ;
                fflush(stdout) ;
                add_field(space, ri, _th_intern(f->u.appl.args[3]->u.string), f->u.appl.args[2]) ;
                break ;
            case INTERN_CCLASS_PROC:
                printf("params = %s\n", _th_print_exp(f->u.appl.args[4]));
                add_class_proc(space, ri, _th_intern(f->u.appl.args[2]->u.string),
                    f->u.appl.args[0]->u.appl.functor==INTERN_CVIRTUAL,
                    f->u.appl.args[3], f->u.appl.args[4]) ;
                break ;
            }
        }
    }
}

static void process_proc(int space, struct name_space *ns, struct _ex_intern *stmts)
{
    /* Not implemented for now--do nothing */
}

static void process_defs(int space, struct name_space *ns, struct _ex_intern *prog)
{
    while (prog->type==EXP_APPL && prog->u.appl.count==2) {
        struct _ex_intern *decl = prog->u.appl.args[0] ;
        if (decl->u.appl.functor==INTERN_CTYPEDEF) {
            add_typedef(space, ns, decl->u.appl.args[0], decl->u.appl.args[1]) ;
        } else if (decl->u.appl.functor==INTERN_CGLOBAL || decl->u.appl.functor==INTERN_CSTATIC) {
            printf("adding variable %s ", _th_print_exp(decl->u.appl.args[0])) ;
            printf("%s ", _th_print_exp(decl->u.appl.args[1])) ;
            printf("%s\n", _th_print_exp(decl->u.appl.args[2])) ;
            fflush(stdout) ;
            add_variable(space, ns, decl->u.appl.args[0], decl->u.appl.args[1], decl->u.appl.args[2]) ;
        } else if (decl->u.appl.functor==INTERN_CLASS_DECL) {
            process_class(space, ns, decl->u.appl.args[0]) ;
        } else if (decl->u.appl.functor==INTERN_CPROC) {
            process_proc(space, ns, decl->u.appl.args[3]) ;
        }
        prog = prog->u.appl.args[1] ;
    }
}

static struct name_space *build_root_space(int space, struct _ex_intern *prog)
{
    struct name_space *root = (struct name_space *)_th_alloc(space, sizeof(struct name_space)) ;
    root->parent = root->next = root->child = NULL ;
    root->name = 0 ;
    root->records = NULL ;
    root->variables = NULL ;
    root->typedefs = NULL ;
    
    process_defs(space, root, prog) ;
    
    return root ;
}

static struct entry *entries, *parent_ent ;

static int inst_length(struct instruction *inst)
{
    if (inst==NULL) return 0 ;
    return 1+inst_length(inst->next) ;
}

static struct instruction *inst_append(struct instruction *inst1, struct instruction *inst2)
{
    if (inst1==NULL) return inst2 ;
    if (inst1->next==NULL) {
        inst1->next = inst2 ;
        return inst1 ;
    }
    inst_append(inst1->next, inst2) ;
    return inst1 ;
}

#define SIGNED_INTEGER   1
#define UNSIGNED_INTEGER 2
#define FLOAT            3
#define POINTER          4
#define CLASS            5

static int type_category(struct _ex_intern *t)
{
    switch (t->u.appl.functor) {
    case INTERN_CCHAR:
    case INTERN_CINT:
    case INTERN_CLONG:
    case INTERN_CSHORT:
    case INTERN_CLONGLONG:
        return SIGNED_INTEGER ;
    case INTERN_CUNSIGNED_CHAR:
    case INTERN_CUNSIGNED_INT:
    case INTERN_CUNSIGNED_LONG:
    case INTERN_CUNSIGNED_SHORT:
    case INTERN_CUNSIGNED_LONG_LONG:
        return UNSIGNED_INTEGER ;
    case INTERN_CPOINTER_TYPE:
        return POINTER ;
    case INTERN_CFLOAT:
    case INTERN_CDOUBLE:
        return FLOAT ;
    case INTERN_CCLASS:
        return CLASS ;
    default:
        return -1 ;
    }
}

static unsigned signed_types[] = { INTERN_CCHAR,
INTERN_CSHORT,
INTERN_CINT,
INTERN_CLONG,
INTERN_CLONGLONG, 0 } ;

static unsigned unsigned_types[] = { INTERN_CUNSIGNED_CHAR,
INTERN_CUNSIGNED_SHORT,
INTERN_CUNSIGNED_INT,
INTERN_CUNSIGNED_LONG,
INTERN_CUNSIGNED_LONG_LONG, 0 } ;

static unsigned float_types[] = { INTERN_CFLOAT,
INTERN_CDOUBLE,
0 } ;

static int get_type_index(unsigned info[], struct _ex_intern *t)
{
    int i ;
    
    for (i = 0; info[i]; ++i) {
        if (t->u.appl.functor==info[i]) return i ;
    }
    return -1 ;
}

static struct _ex_intern *bigger_type(unsigned info[], struct _ex_intern *t1, struct _ex_intern *t2)
{
    if (get_type_index(info,t1) > get_type_index(info,t2)) {
        return t1 ;
    } else {
        return t2 ;
    }
}

static struct _ex_intern *bigger_ptype(unsigned info[], unsigned info2[], struct _ex_intern *t1, struct _ex_intern *t2)
{
    if (get_type_index(info,t1) > get_type_index(info2,t2)) {
        return t1 ;
    } else {
        return _ex_intern_appl(get_type_index(info,t2), 0, 0) ;
    }
}

static struct _ex_intern *common_type(struct _ex_intern *t1, struct _ex_intern *t2)
{
    if (type_category(t1) > type_category(t2)) return common_type(t2,t1) ;
    switch (type_category(t1)) {
    case SIGNED_INTEGER:
        switch (type_category(t2)) {
        case SIGNED_INTEGER:
            return bigger_type(signed_types, t1, t2) ;
        case UNSIGNED_INTEGER:
            return bigger_ptype(signed_types, unsigned_types, t1, t2) ;
        case FLOAT:
            return t2 ;
        /*case POINTER:
            return t2 ;*/
        default:
            return NULL ;
        }
    case UNSIGNED_INTEGER:
        switch (type_category(t2)) {
        case UNSIGNED_INTEGER:
            return bigger_type(unsigned_types, t1, t2) ;
        case FLOAT:
            return t2 ;
        /*case POINTER:
            return t2 ;*/
        default:
            return NULL ;
        }
    case FLOAT:
        switch (type_category(t2)) {
        case FLOAT:
             return bigger_type(float_types, t1, t2) ;
        default:
             return NULL ;
        }
        break ;
    case POINTER:
        if (t1 != t2 /*&& t2 != SIGNED_INTEGER && t2 != UNSIGNED_INTEGER*/) return NULL ;
            return t1 ;
    case CLASS:
        if (t1 != t2) return NULL ;
            return t1 ;
        default:
            return NULL ;
    }
}

static void free_local_vars(struct local_vars *lv)
{
    if (lv==NULL) return ;
    free_local_vars(lv->next) ;
    FREE(lv) ;
}

static struct _ex_intern *find_global_var(unsigned name)
{
    struct entry *e = entries ;
    
    while (e != NULL) {
        printf("Testing %s on %s\n", _th_intern_decode(name), _th_intern_decode(e->u.global_var.var)) ;
        if (e->type == ENTRY_GLOBAL_VARIABLE && e->u.global_var.var==name) {
            return e->u.global_var.type ;
        }
        e = e->next ;
    }
    
    return NULL ;
}

static struct local_vars *find_var(struct local_vars *lv, unsigned name)
{
    if (lv==NULL) return NULL ;
    if (name==lv->name && !lv->disabled) return lv ;
    return find_var(lv->next, name) ;
}

void disable_scope(struct local_vars *lv, unsigned scope)
{
    if (lv==NULL) return ;
    if (lv->scope==scope) lv->disabled = 1 ;
    disable_scope(lv->next, scope) ;
}

static unsigned scope ;
static struct local_vars *local_vars ;

static void add_local_var(int space, unsigned scope, unsigned name, struct _ex_intern *type)
{
    struct local_vars *lv = (struct local_vars *)_th_alloc(space, sizeof(struct local_vars)) ;
    lv ->next = local_vars ;
    local_vars = lv ;
    lv->scope = scope ;
    lv->name = name ;
    lv->type = type ;
    lv->disabled = 0 ;
    printf("Added var %s %s\n", _th_intern_decode(name), _th_print_exp(type)) ;
}

static struct instruction *compile_lvalue(int space, struct env *env, struct _ex_intern *e) ;

static int translate_op(struct _ex_intern *ctype, int op)
{
    if (ctype->u.appl.functor==INTERN_CFLOAT ||
        ctype->u.appl.functor==INTERN_CDOUBLE) {
        switch (op) {
        case INTERN_CPLUS:   return INTERN_RAT_PLUS ;   break ;
        case INTERN_CMINUS:  return INTERN_RAT_MINUS ;  break ;
        case INTERN_CTIMES:  return INTERN_RAT_TIMES ;  break ;
        case INTERN_CDIVIDE: return INTERN_RAT_DIVIDE ; break ;
        case INTERN_CLESS:   return INTERN_RAT_LESS ;   break ;
        case INTERN_CEQUAL:  return INTERN_EQUAL ;      break ;
        default: return 0 ;
        }
    } else {
        switch (op) {
        case INTERN_CPLUS:   return INTERN_NAT_PLUS ;   break ;
        case INTERN_CMINUS:  return INTERN_NAT_MINUS ;  break ;
        case INTERN_CTIMES:  return INTERN_NAT_TIMES ;  break ;
        case INTERN_CDIVIDE: return INTERN_NAT_DIVIDE ; break ;
        case INTERN_CLESS:   return INTERN_NAT_LESS ;   break ;
        case INTERN_CEQUAL:  return INTERN_EQUAL ;      break ;
        case INTERN_CNOT:    return INTERN_NOT ;        break ;
        default: return 0 ;
        }
    }
}

struct instruction *emit_operation(int space, struct instruction *inst, unsigned op, struct _ex_intern *param)
{
    struct instruction *op_inst = (struct instruction *)_th_alloc(space, sizeof(struct instruction)) ;
    op_inst->next = NULL ;
    op_inst->operation = Operation ;
    op_inst->u.op.operation = op ;
    op_inst->u.op.param = param ;
    op_inst->file = _th_find_position(&op_inst->line, NULL) ;
    return inst_append(inst, op_inst) ;
}

struct instruction *emit_jump(int space, struct instruction *inst, unsigned op)
{
    struct instruction *op_inst = (struct instruction *)_th_alloc(space, sizeof(struct instruction)) ;
    op_inst->next = NULL ;
    op_inst->operation = Jump ;
    op_inst->u.arg = op ;
    op_inst->file = _th_find_position(&op_inst->line, NULL) ;
    return inst_append(inst, op_inst) ;
}

struct instruction *emit_jumpsub(int space, struct instruction *inst, unsigned sub, int count)
{
    struct instruction *op_inst = (struct instruction *)_th_alloc(space, sizeof(struct instruction)) ;
    op_inst->next = NULL ;
    op_inst->operation = JumpSub ;
    op_inst->u.jumpsub.function = sub ;
    op_inst->u.jumpsub.count = count ;
    op_inst->file = _th_find_position(&op_inst->line, NULL) ;
    return inst_append(inst, op_inst) ;
}

struct instruction *emit_ifzero(int space, struct instruction *inst, unsigned op)
{
    struct instruction *op_inst = (struct instruction *)_th_alloc(space, sizeof(struct instruction)) ;
    op_inst->next = NULL ;
    op_inst->operation = IfZero ;
    op_inst->u.arg = op ;
    op_inst->file = _th_find_position(&op_inst->line, NULL) ;
    return inst_append(inst, op_inst) ;
}

struct instruction *emit_store(int space, struct instruction *inst, struct _ex_intern *e)
{
    struct instruction *op_inst = (struct instruction *)_th_alloc(space, sizeof(struct instruction)) ;
    op_inst->next = NULL ;
    op_inst->operation = Store ;
    op_inst->u.exp = e ;
    op_inst->file = _th_find_position(&op_inst->line, NULL) ;
    return inst_append(inst, op_inst) ;
}

struct instruction *emit_load(int space, struct instruction *inst, struct _ex_intern *e)
{
    struct instruction *op_inst = (struct instruction *)_th_alloc(space, sizeof(struct instruction)) ;
    op_inst->next = NULL ;
    op_inst->operation = Load ;
    op_inst->u.exp = e ;
    op_inst->file = _th_find_position(&op_inst->line, NULL) ;
    return inst_append(inst, op_inst) ;
}

struct instruction *emit_push_constant(int space, struct instruction *inst, struct _ex_intern *e)
{
    struct instruction *op_inst = (struct instruction *)_th_alloc(space, sizeof(struct instruction)) ;
    op_inst->next = NULL ;
    op_inst->operation = PushConstant ;
    op_inst->u.exp = e ;
    op_inst->file = _th_find_position(&op_inst->line, NULL) ;
    return inst_append(inst, op_inst) ;
}

struct instruction *emit_return(int space, struct instruction *inst)
{
    struct instruction *op_inst = (struct instruction *)_th_alloc(space, sizeof(struct instruction)) ;
    op_inst->next = NULL ;
    op_inst->operation = Return ;
    op_inst->file = _th_find_position(&op_inst->line, NULL) ;
    return inst_append(inst, op_inst) ;
}

struct instruction *emit_pop(int space, struct instruction *inst, unsigned arg)
{
    struct instruction *op_inst = (struct instruction *)_th_alloc(space, sizeof(struct instruction)) ;
    op_inst->next = NULL ;
    op_inst->operation = Pop ;
    op_inst->u.arg = arg ;
    op_inst->file = _th_find_position(&op_inst->line, NULL) ;
    return inst_append(inst, op_inst) ;
}

struct instruction *emit_assert(int space, struct instruction *inst, struct _ex_intern *e)
{
    struct instruction *op_inst = (struct instruction *)_th_alloc(space, sizeof(struct instruction)) ;
    op_inst->next = NULL ;
    op_inst->operation = Assert ;
    op_inst->u.exp = e ;
    op_inst->file = _th_find_position(&op_inst->line, NULL) ;
    return inst_append(inst, op_inst) ;
}

struct instruction *emit_invariant(int space, struct instruction *inst, struct _ex_intern *e)
{
    struct instruction *op_inst = (struct instruction *)_th_alloc(space, sizeof(struct instruction)) ;
    op_inst->next = NULL ;
    op_inst->operation = Invariant ;
    op_inst->u.exp = e ;
    op_inst->file = _th_find_position(&op_inst->line, NULL) ;
    return inst_append(inst, op_inst) ;
}

struct instruction *emit_label(int space, struct instruction *inst, unsigned label)
{
    struct instruction *op_inst = (struct instruction *)_th_alloc(space, sizeof(struct instruction)) ;
    op_inst->next = NULL ;
    op_inst->operation = Label ;
    op_inst->u.label = label ;
    op_inst->file = _th_find_position(&op_inst->line, NULL) ;
    return inst_append(inst, op_inst) ;
}

static struct instruction *emit_conversion_op(int space, struct instruction *inst, struct _ex_intern *from, struct _ex_intern *to)
{
    int fti = type_category(from) ;
    int tti = type_category(to) ;
    
    if (from==to) return inst ;
    
    if (fti <= UNSIGNED_INTEGER && tti <= UNSIGNED_INTEGER) return NULL ;
    
    if ((fti == UNSIGNED_INTEGER || fti == SIGNED_INTEGER) && tti == FLOAT) {
        inst = emit_operation(space,inst,INTERN_NAT_TO_RAT, NULL) ;
        return inst ;
    } else if ((tti == UNSIGNED_INTEGER || tti == SIGNED_INTEGER) && fti == FLOAT) {
        inst = emit_operation(space,inst,INTERN_RAT_TO_NAT, NULL) ;
        return inst ;
    } else return inst ;
}

static struct _ex_intern *return_type ;
static struct instruction *compile_expression(int space, struct env *env, struct _ex_intern *e)
{
    struct instruction *inst, *inst1, *inst2 ;
    struct _ex_intern *type1, *type2, *ctype ;
    struct _ex_intern *f ;
    struct local_vars *lv ;
    int i, c ;
    int tc1, tc2 ;

    printf("exp %s\n", _th_print_exp(e)) ;
    fflush(stdout) ;
    
    switch (e->u.appl.functor) {
    case INTERN_CALL:
        inst = NULL ;
        f = e->u.appl.args[1] ;
        c = cons_count(f) ;
        for (i = 0; i < c; ++i) {
            inst = inst_append(inst,compile_expression(space,env,f->u.appl.args[0])) ;
            f = f->u.appl.args[1] ;
        }
        inst = emit_jumpsub(space,inst,_th_intern(e->u.appl.args[0]->u.string),c) ;
        break ;
    case INTERN_CCOMPLEMENT:
    case INTERN_CUPLUS:
    case INTERN_CUMINUS:
    case INTERN_CNOT:
        inst = compile_expression(space, env, e->u.appl.args[0]) ;
        inst = emit_operation(space,inst,e->u.appl.functor, NULL) ;
        break ;
    case INTERN_CPLUS:
    case INTERN_CMINUS:
    case INTERN_CTIMES:
    case INTERN_CDIVIDE:
    case INTERN_CEQUAL:
    case INTERN_CLESS:
        inst1 = compile_expression(space, env, e->u.appl.args[0]) ;
        type1 = return_type ;
        inst2 = compile_expression(space, env, e->u.appl.args[1]) ;
        type2 = return_type ;
        ctype = common_type(type1, type2) ;
        if (ctype==NULL) {
            tc1 = type_category(type1) ;
            tc2 = type_category(type2) ;
            if (tc1 == POINTER && (tc2 == UNSIGNED_INTEGER || tc2 == SIGNED_INTEGER)) {
                emit_operation(space,inst1,INTERN_POINTER_TO_NAT, NULL) ;
                ctype = _ex_intern_appl_env(env,INTERN_CINT,0,NULL) ;
                goto cont_gen ;
            }
            if (tc2 == POINTER && (tc1 == UNSIGNED_INTEGER || tc1 == SIGNED_INTEGER)) {
                emit_operation(space,inst2,INTERN_POINTER_TO_NAT, NULL) ;
                ctype = _ex_intern_appl_env(env,INTERN_CINT,0,NULL) ;
                goto cont_gen ;
            }
            fprintf(stderr,"Illegal type for Cgreater\n") ;
            exit(1) ;
        }
        inst1 = emit_conversion_op(space, inst1, type1, ctype) ;
        inst2 = emit_conversion_op(space, inst2, type2, ctype) ;
cont_gen:
        inst = inst_append(inst1, inst2) ;
        emit_operation(space,inst,translate_op(ctype,e->u.appl.functor), NULL) ;
        return_type = ctype ;
        break ;
    case INTERN_CGREATER:
        inst1 = compile_expression(space, env, e->u.appl.args[1]) ;
        type1 = return_type ;
        inst2 = compile_expression(space, env, e->u.appl.args[0]) ;
        type2 = return_type ;
        ctype = common_type(type1, type2) ;
        if (ctype==NULL) {
            fprintf(stderr,"Illegal type for Cgreater\n") ;
            exit(1) ;
        }
        inst1 = emit_conversion_op(space, inst1, type1, ctype) ;
        inst2 = emit_conversion_op(space, inst2, type2, ctype) ;
        inst = inst_append(inst1, inst2) ;
        emit_operation(space,inst,translate_op(ctype,INTERN_CLESS), NULL) ;
        return_type = ctype ;
        break ;
    case INTERN_CGREATEREQUAL:
        inst1 = compile_expression(space, env, e->u.appl.args[0]) ;
        type1 = return_type ;
        inst2 = compile_expression(space, env, e->u.appl.args[1]) ;
        type2 = return_type ;
        ctype = common_type(type1, type2) ;
        if (ctype==NULL) {
            fprintf(stderr,"Illegal type for CgreaterEqual\n") ;
            exit(1) ;
        }
        inst1 = emit_conversion_op(space, inst1, type1, ctype) ;
        inst2 = emit_conversion_op(space, inst2, type2, ctype) ;
        inst = inst_append(inst1, inst2) ;
        emit_operation(space,inst,translate_op(ctype,INTERN_CLESS), NULL) ;
        emit_operation(space,inst,translate_op(ctype,INTERN_CNOT), NULL) ;
        return_type = ctype ;
        break ;
    case INTERN_CLESSEQUAL:
        inst1 = compile_expression(space, env, e->u.appl.args[1]) ;
        type1 = return_type ;
        inst2 = compile_expression(space, env, e->u.appl.args[0]) ;
        type2 = return_type ;
        ctype = common_type(type1, type2) ;
        if (ctype==NULL) {
            fprintf(stderr,"Illegal type for ClessEqual\n") ;
            exit(1) ;
        }
        inst1 = emit_conversion_op(space, inst1, type1, ctype) ;
        inst2 = emit_conversion_op(space, inst2, type2, ctype) ;
        inst = inst_append(inst1, inst2) ;
        emit_operation(space,inst,translate_op(ctype,INTERN_CLESS), NULL) ;
        emit_operation(space,inst,translate_op(ctype,INTERN_CNOT), NULL) ;
        return_type = ctype ;
        break ;
    case INTERN_CNOTEQUAL:
        inst1 = compile_expression(space, env, e->u.appl.args[0]) ;
        type1 = return_type ;
        inst2 = compile_expression(space, env, e->u.appl.args[1]) ;
        type2 = return_type ;
        ctype = common_type(type1, type2) ;
        if (ctype==NULL) {
            tc1 = type_category(type1) ;
            tc2 = type_category(type2) ;
            if (tc1 == POINTER && (tc2 == UNSIGNED_INTEGER || tc2 == SIGNED_INTEGER)) {
                emit_operation(space,inst1,INTERN_POINTER_TO_NAT, NULL) ;
                ctype = _ex_intern_appl_env(env,INTERN_CINT,0,NULL) ;
                goto cont_ne ;
            }
            if (tc2 == POINTER && (tc1 == UNSIGNED_INTEGER || tc1 == SIGNED_INTEGER)) {
                emit_operation(space,inst2,INTERN_POINTER_TO_NAT, NULL) ;
                ctype = _ex_intern_appl_env(env,INTERN_CINT,0,NULL) ;
                goto cont_ne ;
            }
            fprintf(stderr,"Illegal type for CnotEqual\n") ;
            exit(1) ;
        }
        inst1 = emit_conversion_op(space, inst1, type1, ctype) ;
        inst2 = emit_conversion_op(space, inst2, type2, ctype) ;
cont_ne:
        inst = inst_append(inst1, inst2) ;
        emit_operation(space,inst,translate_op(ctype,INTERN_CEQUAL), NULL) ;
        emit_operation(space,inst,translate_op(ctype,INTERN_CNOT), NULL) ;
        return_type = ctype ;
        break ;
    case INTERN_CAND:
    case INTERN_COR:
    case INTERN_CLAND:
    case INTERN_CLOR:
    case INTERN_CMOD:
    case INTERN_CLSHIFT:
    case INTERN_CRSHIFT:
    case INTERN_CXOR:
        inst1 = compile_expression(space, env, e->u.appl.args[0]) ;
        inst2 = compile_expression(space, env, e->u.appl.args[1]) ;
        inst = inst_append(inst1, inst2) ;
        emit_operation(space,inst,e->u.appl.functor, NULL) ;
        break ;
    case INTERN_CAST:
        inst = compile_expression(space, env, e->u.appl.args[1]) ;
        return_type = e->u.appl.args[0] ;
        break ;
    case INTERN_CSIZEOF:
        inst = emit_push_constant(space,NULL,_ex_intern_appl1_env(env,INTERN_SIZEOF,e->u.appl.args[0])) ;
        return_type = _ex_intern_appl_env(env,INTERN_CINT,0,NULL) ;
        break ;
    case INTERN_CASSIGN:
        inst1 = compile_lvalue(space, env, e->u.appl.args[0]) ;
        type1 = return_type ;
        inst2 = compile_expression(space, env, e->u.appl.args[1]) ;
        type2 = return_type ;
        return_type = type1 ;
        ctype = common_type(type1, type2) ;
        if (ctype==NULL || ctype != type1) {
            tc1 = type_category(type1) ;
            tc2 = type_category(type2) ;
            if (tc1==POINTER && (tc2==SIGNED_INTEGER || tc2==UNSIGNED_INTEGER)) {
                inst2 = emit_operation(space, inst2, INTERN_NAT_TO_POINTER,type1) ;
                goto assign_cont ;
            }
            fprintf(stderr,"Illegal type for CnotEqual\n") ;
            exit(1) ;
        }
        inst2 = emit_conversion_op(space, inst2, type2, ctype) ;
assign_cont:
        inst = inst_append(inst1, inst2) ;
        inst = emit_store(space,inst,return_type) ;
        break ;
    case INTERN_CNAT:
        return_type = _th_parse(NULL, "(Cint)") ;
        type2 = e->u.appl.args[0] ;
        goto cont ;
    case INTERN_CFLOAT:
        return_type = _th_parse(NULL, "(Cfloat)") ;
        type2 = _ex_intern_appl(INTERN_SRATIONAL,1,&e->u.appl.args[0]) ;
        goto cont ;
    case INTERN_CDOUBLE:
        return_type = _th_parse(NULL, "(Cdouble)") ;
        type2 = _ex_intern_appl(INTERN_SRATIONAL,1,&e->u.appl.args[0]) ;
        goto cont ;
    case INTERN_CSTRING:
        return_type = _th_parse(NULL, "(CpointerType (Cchar))") ;
        type2 = e->u.appl.args[0] ;
cont:
        inst = emit_push_constant(space,NULL,type2) ;
        break ;
    case INTERN_CVAR:
        lv = find_var(local_vars, _th_intern(e->u.appl.args[0]->u.string)) ;
        if (lv != NULL) {
            f = _ex_intern_appl2_env(env,INTERN_LOCAL_LOC,e->u.appl.args[0],_ex_intern_small_integer(lv->scope)) ;
            if (lv->type->u.appl.functor==INTERN_CARRAY ||
                lv->type->u.appl.functor==INTERN_CFLEXARRAY) {
                //f = _ex_intern_appl1_env(env,INTERN_CINTDATUM, f) ;
            } else {
                f = _ex_intern_appl3_env(env,INTERN_GETVAL,_ex_intern_appl(INTERN_STATE,0,NULL),f,lv->type) ;
            }
            return_type = lv->type ;
        } else {
            return_type = find_global_var(_th_intern(e->u.appl.args[0]->u.string)) ;
            if (return_type != NULL) {
                f = _ex_intern_appl1_env(env,INTERN_GLOBAL_LOC,e->u.appl.args[0]) ;
                if (return_type->u.appl.functor==INTERN_CARRAY || return_type->u.appl.functor==INTERN_CFLEXARRAY) {
                    //f = _ex_intern_appl1_env(env,INTERN_CINTDATUM, f) ;
                } else {
                    f = _ex_intern_appl3_env(env,INTERN_GETVAL,_ex_intern_appl(INTERN_STATE,0,NULL),f,return_type) ;
                }
            } else {
                f = _ex_intern_small_integer(0) ;
                return_type = _ex_intern_appl_env(env,INTERN_CINT,0,NULL) ;
            }
        }
        inst = emit_push_constant(space,NULL,f) ;
        break ;
    case INTERN_CSUB:
        inst1 = compile_expression(space, env, e->u.appl.args[0]) ;
        type1 = return_type ;
        inst2 = compile_expression(space, env, e->u.appl.args[1]) ;
        type2 = return_type ;
        switch (type1->u.appl.functor) {
        case INTERN_CARRAY:
            return_type = type1->u.appl.args[0] ;
            inst1 = emit_push_constant(space,inst1,
                _ex_intern_appl1_env(env, INTERN_SIZEOF,type1->u.appl.args[0])) ;
            inst = inst_append(inst1,inst2) ;
            inst = emit_assert(space,inst,
                _ex_intern_appl2_env(env,INTERN_AND,
                _ex_intern_appl1_env(env,INTERN_NOT,
                _ex_intern_appl2_env(env,INTERN_NAT_LESS,
                _ex_intern_appl2_env(env,INTERN_GETSTACK,
                _ex_intern_appl_env(env,INTERN_STATE,0,NULL),
                _ex_intern_small_integer(0)),
                _ex_intern_small_integer(0))),
                _ex_intern_appl2_env(env,INTERN_NAT_LESS,
                _ex_intern_appl2_env(env,INTERN_GETSTACK,
                _ex_intern_appl_env(env,INTERN_STATE,0,NULL),
                _ex_intern_small_integer(0)),
                _ex_intern_small_integer(type1->u.appl.args[1]->u.appl.args[0]->u.integer[1])))) ;
            inst = emit_operation(space,inst,INTERN_NAT_TIMES, NULL) ;
            inst = emit_operation(space,inst,INTERN_NAT_PLUS, NULL) ;
            if (type1->u.appl.args[0]->u.appl.functor!=INTERN_CARRAY &&
                type1->u.appl.args[0]->u.appl.functor!=INTERN_CFLEXARRAY) {
                inst = emit_load(space, inst, return_type) ;
            }
            break ;
        case INTERN_CFLEXARRAY:
        default:
            inst = NULL ;
        }
        break ;
    case INTERN_CREF:
        inst = compile_expression(space,env,e->u.appl.args[0]) ;
        if (return_type==NULL || return_type->type != EXP_APPL || return_type->u.appl.functor != INTERN_CPOINTER_TYPE) {
            printf("Illegal pointer dereference\n") ;
            exit(1) ;
        }
        return_type = return_type->u.appl.args[0] ;
        inst = emit_load(space, inst, return_type) ;
        break ;
    case INTERN_CGETFIELD:
        inst = compile_lvalue(space,env,e->u.appl.args[0]) ;
        inst = emit_push_constant(space,inst,
            _ex_intern_appl2_env(env,INTERN_FIELD_OFFSET,
            return_type->u.appl.args[0],e->u.appl.args[1])) ;
        inst = emit_operation(space, inst, INTERN_NAT_PLUS, NULL) ;
        return_type = find_field_type(return_type,e->u.appl.args[1]->u.string) ;
        if (return_type==NULL) {
            printf("Illegal field dereference\n") ;
            exit(1) ;
        }
        inst = emit_load(space, inst, return_type) ;
        break ;
    default:
        inst = emit_push_constant(space,NULL,e) ;
    }
    return inst ;
}

static struct instruction *compile_lvalue(int space, struct env *env, struct _ex_intern *e)
{
    struct local_vars *lv ;
    struct instruction *inst, *inst1, *inst2 ;
    struct _ex_intern *type1, *type2 ;
    
    printf("lvalue %s\n", _th_print_exp(e)) ;
    fflush(stdout) ;
    
    switch (e->u.appl.functor) {
    case INTERN_CVAR:
        lv = find_var(local_vars, _th_intern(e->u.appl.args[0]->u.string)) ;
        if (lv != NULL) {
            inst = emit_push_constant(space,NULL,
                _ex_intern_appl2_env(env,INTERN_LOCAL_LOC,
                e->u.appl.args[0],
                _ex_intern_small_integer(lv->scope))) ;
            return_type = lv->type ;
        } else {
            return_type = find_global_var(_th_intern(e->u.appl.args[0]->u.string)) ;
            if (return_type != NULL) {
                inst = emit_push_constant(space,NULL,
                    _ex_intern_appl1_env(env,INTERN_GLOBAL_LOC,
                    e->u.appl.args[0])) ;
            } else {
                inst = emit_push_constant(space,NULL,_ex_intern_small_integer(0)) ;
                return_type = _ex_intern_appl_env(env,INTERN_CINT,0,NULL) ;
            }
        }
        break ;
    case INTERN_CSUB:
        inst1 = compile_expression(space, env, e->u.appl.args[0]) ;
        type1 = return_type ;
        inst2 = compile_expression(space, env, e->u.appl.args[1]) ;
        type2 = return_type ;
        switch (type1->u.appl.functor) {
        case INTERN_CARRAY:
            return_type = type1->u.appl.args[0] ;
            inst1= emit_push_constant(space, inst1,
                _ex_intern_appl1_env(env,INTERN_SIZEOF,return_type)) ;
            inst = inst_append(inst1,inst2) ;
            inst = emit_assert(space,inst,
                _ex_intern_appl2_env(env,INTERN_AND,
                _ex_intern_appl1_env(env,INTERN_NOT,
                _ex_intern_appl2_env(env,INTERN_NAT_LESS,
                _ex_intern_appl2_env(env,INTERN_GETSTACK,
                _ex_intern_appl_env(env,INTERN_STATE,0,NULL),
                _ex_intern_small_integer(0)),
                _ex_intern_small_integer(0))),
                _ex_intern_appl2_env(env,INTERN_NAT_LESS,
                _ex_intern_appl2_env(env,INTERN_GETSTACK,
                _ex_intern_appl_env(env,INTERN_STATE,0,NULL),
                _ex_intern_small_integer(0)),
                _ex_intern_small_integer(type1->u.appl.args[1]->u.appl.args[0]->u.integer[1])))) ;
            inst = emit_operation(space,inst,INTERN_NAT_TIMES, NULL) ;
            inst = emit_operation(space,inst,INTERN_NAT_PLUS, NULL) ;
            break ;
        case INTERN_CFLEXARRAY:
        default:
            inst = NULL ;
        }
        break ;
    case INTERN_CREF:
        inst = compile_expression(space,env,e->u.appl.args[0]) ;
        if (return_type==NULL || return_type->type != EXP_APPL || return_type->u.appl.functor != INTERN_CPOINTER_TYPE) {
            printf("Illegal pointer dereference\n") ;
            exit(1) ;
        }
        return_type = return_type->u.appl.args[0] ;
        break ;
    case INTERN_CGETFIELD:
        inst = compile_lvalue(space,env,e->u.appl.args[0]) ;
        inst = emit_push_constant(space,inst,
            _ex_intern_appl2_env(env,INTERN_FIELD_OFFSET,
            return_type->u.appl.args[0],e->u.appl.args[1])) ;
        inst = emit_operation(space, inst, INTERN_NAT_PLUS, NULL) ;
        return_type = find_field_type(return_type,e->u.appl.args[1]->u.string) ;
        if (return_type==NULL) {
            printf("Illegal field dereference\n") ;
            exit(1) ;
        }
        break ;
    default:
        inst = emit_push_constant(space,NULL,e) ;
    }
    return inst ;
}

struct inst_link {
    struct inst_link *next ;
    struct instruction *inst ;
    int pos ;
} ;
struct goto_link {
    struct goto_link *next ;
    struct inst_link *link ;
    int pos ;
    char *name ;
} ;

struct goto_link *find_position(struct goto_link *gto, char *s)
{
    if (gto==NULL) return gto ;
    
    if (!strcmp(gto->name, s)) return gto ;
    
    return find_position(gto->next, s) ;
}

struct goto_link *add_goto(struct goto_link *gto, char *s, int pos)
{
    struct goto_link *ngto = (struct goto_link *)MALLOC(sizeof(struct goto_link)) ;
    ngto->next = gto ;
    gto = ngto ;
    gto->name = strdup(s) ;
    gto->link = NULL ;
    gto->pos = pos ;
    return gto ;
}

struct goto_link *add_link(struct goto_link *gto, struct instruction *inst, char *name, int count)
{
    struct goto_link *ngto = find_position(gto, name) ;
    struct inst_link *link ;
    
    if (ngto == NULL) {
        gto = add_goto(gto, name, -1) ;
    }
    
    link = (struct inst_link *)MALLOC(sizeof(struct inst_link)) ;
    link->next = gto->link ;
    gto->link = link ;
    link->inst = inst ;
    link->pos = count ;
    
    return gto ;
}

void free_goto_list(struct goto_link *gto)
{
    struct inst_link *inst, *instn ;
    struct goto_link *gton ;
    while (gto != NULL) {
        gton = gto->next ;
        inst = gto->link ;
        while (inst != NULL) {
            instn = inst->next ;
            FREE(inst) ;
            inst = inst->next ;
        }
        FREE(gto) ;
        gto = gton ;
    }
}

static struct instruction *compile(int space, struct env *env, struct _ex_intern *e, int start, struct goto_link **gtop)
{
    struct instruction *inst, *rest, *inst1, *inst2, *inst3 ;
    struct goto_link *ngto, *gto ;
    int count ;
    struct inst_link *link ;
    unsigned current_scope = scope ;
    unsigned label ;

    //printf("%s\n", _th_print_exp(e)) ;
    //printf("compiling %s\n", _th_print_exp(env,INTERN_DEFAULT,80,e)) ;
    //fflush(stdout) ;

    if (e->u.appl.functor == INTERN_NIL) return NULL ;
    if (e->u.appl.args[0]->u.appl.functor==INTERN_CDECL) {
        add_local_var(space, current_scope, _th_intern(e->u.appl.args[0]->u.appl.args[0]->u.string), e->u.appl.args[0]->u.appl.args[1]) ;
    }
    if (e->u.appl.args[0]->u.appl.functor==INTERN_CLOOP_LABEL) {
        struct _ex_intern *x, *r ;
        label = _th_intern(e->u.appl.args[0]->u.appl.args[0]->u.string) ;
        _th_add_function(env,_ex_intern_appl_env(env,label,0,NULL),_th_parse(env,"(-> (Tuple) (State))"),_ex_true,0,NULL) ;
        r = _ex_intern_appl_env(env,label,0,NULL) ;
        x = _ex_intern_appl1_env(env,INTERN_VALID_STATE,r) ;
        _th_log_derive_and_add(env, _th_derive_simplify(env,x)) ;
        x = _ex_intern_appl1_env(env,INTERN_IMPORTANT_STATE,r) ;
        _th_log_derive_and_add(env, _th_derive_simplify(env,x)) ;
    }
    _th_push_current(1) ;
    rest = compile(space, env, e->u.appl.args[1], start, gtop) ;
    gto = *gtop ;
    count = inst_length(rest) + start ;
    _th_pop_current() ;
    e = e->u.appl.args[0] ;
    _th_push_current(0) ;
    printf("Compiling statement %s\n", _th_print_exp(e)) ;
    fflush(stdout) ;
    switch (e->u.appl.functor) {
    case INTERN_CGOTO:
        inst = emit_jump(space,NULL,0) ;
        ngto = find_position(gto, e->u.appl.args[0]->u.string) ;
        if (ngto != NULL && ngto->pos >= 0) {
            printf("Adding goto1 %d %d\n", count, ngto->pos) ;
            inst->u.arg = count - ngto->pos ;
        } else {
            *gtop = gto = add_link(gto, inst, e->u.appl.args[0]->u.string, count) ;
        }
        break ;
    case INTERN_CLABEL:
        ngto = find_position(gto, e->u.appl.args[0]->u.string) ;
        if (ngto != NULL) {
            link = ngto->link ;
            while (link != NULL) {
            printf("Adding goto2 %d %d\n", count, link->pos) ;
                link->inst->u.arg = link->pos - count ;
                link = link->next ;
            }
        } else {
            *gtop = gto = add_goto(gto, e->u.appl.args[0]->u.string, count) ;
        }
        inst = NULL ;
        break ;
    case INTERN_CRETURN:
        inst = emit_return(space,NULL);
        break ;
    case INTERN_CASSERT:
        _th_check(env,_ex_bool,e->u.appl.args[0]) ;
        inst = emit_assert(space, NULL, e->u.appl.args[0]) ;
        break ;
    case INTERN_CLOOP_INVARIANT:
        _th_check(env,_ex_bool,e->u.appl.args[0]) ;
        inst = emit_invariant(space, NULL, e->u.appl.args[0]) ;
        break ;
    case INTERN_CLOOP_LABEL:
        inst = emit_label(space, NULL, label) ;
        _th_log_add_precedence(ENVIRONMENT_SPACE,env,INTERN_PRE,label) ;
        break ;
    case INTERN_CEXPR:
        inst = compile_expression(space, env, e->u.appl.args[0]);
        inst = emit_pop(space,inst,1) ;
        break;
    case INTERN_CBLOCK:
        _th_push_current(0) ;
        ++scope ;
        inst = compile(space, env, e->u.appl.args[0], count, gtop) ;
        disable_scope(local_vars, scope) ;
        _th_pop_current() ;
        break ;
    case INTERN_CWHILE:
        _th_push_current(0) ;
        _th_push_current(1) ;
        inst2 = compile(space, env, e->u.appl.args[1]->u.appl.args[0], count + 1, gtop) ;
        printf("while = %s\n", _th_print_exp(e)) ;
        _th_pop_current() ;
        _th_push_current(0) ;
        inst1 = compile_expression(space, env, e->u.appl.args[0]) ;
        _th_pop_current() ;
        _th_pop_current() ;
        inst1 = emit_ifzero(space,inst1,1+inst_length(inst2)) ;
        inst = inst_append(inst1,inst2) ;
        inst = emit_jump(space,inst1, -1 - inst_length(inst)) ;
        break ;
    case INTERN_CIF:
        _th_push_current(0) ;
        inst1 = compile_expression(space, env, e->u.appl.args[0]) ;
        _th_pop_current() ;
        _th_push_current(1) ;
        _th_push_current(0) ;
        inst2 = compile(space, env, e->u.appl.args[1]->u.appl.args[0], count, gtop) ;
        _th_pop_current() ;
        _th_pop_current() ;
        inst1 = emit_ifzero(space,inst1,inst_length(inst2)) ;
        inst = inst_append(inst1, inst2) ;
        break ;
    case INTERN_CIFELSE:
        _th_push_current(0) ;
        inst1 = compile_expression(space, env, e->u.appl.args[0]) ;
        _th_pop_current() ;
        _th_push_current(1) ;
        _th_push_current(0) ;
        inst3 = compile(space, env, e->u.appl.args[2]->u.appl.args[0], count + 1, gtop) ;
        _th_pop_current() ;
        _th_pop_current() ;
        _th_push_current(2) ;
        _th_push_current(0) ;
        inst2 = compile(space, env, e->u.appl.args[1]->u.appl.args[0], count + 2 + inst_length(inst3), gtop) ;
        _th_pop_current() ;
        _th_pop_current() ;
        _th_push_current(0) ;
        inst1 = emit_ifzero(space,inst1,inst_length(inst2)+1) ;
        inst = inst_append(inst1, inst2) ;
        inst = emit_jump(space,inst,inst_length(inst3)) ;
        inst = inst_append(inst, inst3) ;
        break ;
    default:
        inst = NULL;
    }
    _th_pop_current() ;
    printf("Returning from compile %s\n", _th_print_exp(e)) ;
    fflush(stdout) ;
    inst = inst_append(inst, rest);
    return inst ;
}

char *pi(int pos, struct instruction *inst)
{
    char file[80] ;
    static char ret[200] ;
    if (inst==NULL) return NULL ;
    sprintf(file, "%s(%d)%5d ", _th_intern_decode(inst->file),inst->line, pos) ;
    switch (inst->operation) {
    case Return:
        sprintf(ret, "%sReturn", file) ;
        break ;
    case PushConstant:
        sprintf(ret, "%sPushConstant %s", file, _th_print_exp(inst->u.exp)) ;
        break ;
    case PushCond:
        sprintf(ret, "%sPushCond %s", file, _th_print_exp(inst->u.exp)) ;
        break ;
    case JumpSub:
        sprintf(ret, "%sJumpSub %s,%d", file, _th_intern_decode(inst->u.jumpsub.function), inst->u.jumpsub.count) ;
        break ;
    case Jump:
        sprintf(ret, "%sJump %d", file, inst->u.arg) ;
        break ;
    case IfZero:
        sprintf(ret, "%sIfZero %d", file, inst->u.arg) ;
        break ;
    case Operation:
        sprintf(ret, "%sOperation %s", file, _th_intern_decode(inst->u.arg)) ;
        break ;
    case Load:
        sprintf(ret, "%sLoad %s", file, _th_print_exp(inst->u.exp)) ;
        break ;
    case Store:
        sprintf(ret, "%sStore %s", file, _th_print_exp(inst->u.exp)) ;
        break ;
    case StorePop:
        sprintf(ret, "%sStorePop %s", file, _th_print_exp(inst->u.exp)) ;
        break ;
    case Pop:
        sprintf(ret, "%sPop %d", file, inst->u.arg) ;
        break ;
    case Rotate:
        sprintf(ret, "%sRotate %d", file, inst->u.arg) ;
        break ;
    case Assert:
        sprintf(ret, "%sAssert %s", file, _th_print_exp(inst->u.exp)) ;
        break ;
    case Invariant:
        sprintf(ret, "%sInvariant %s", file, _th_print_exp(inst->u.exp)) ;
        break ;
        //		case Block:
        //			_tree_print1("%sBlock", file) ;
        //			print_instructions(indent+4,0,inst->u.block) ;
        //			break ;
        //		case ParBlock:
        //			_tree_print1("%sParBlock", file) ;
        //			print_instructions(indent+4,0,inst->u.block) ;
        //			break ;
    case Declare:
        sprintf(ret, "%sDeclare %s %s", file,
            _th_intern_decode(inst->u.declare.var),
            _th_print_exp(inst->u.declare.type)) ;
        break ;
    case StaticEnv:
        sprintf(ret, "%sStaticEnv", file) ;
        break ;
    case Noop:
        sprintf(ret, "%sNoop", file) ;
        break ;
    case Dup:
        sprintf(ret, "%sDup",  file) ;
        break ;
    }
    
    return ret ;
}

void _th_print_instruction(int pos, struct instruction *inst)
{
    char *x = pi(pos,inst) ;
    if (x) _tree_print1("%s",x) ;
}

void print_instruction(int pos, struct instruction *inst)
{
    char *x = pi(pos,inst) ;
    if (x) printf("%s\n",x) ;
}

void _th_print_assembly(struct entry *e)
{
    int i ;
    struct instruction *inst ;
    if (e==NULL) return;
    
    switch (e->type) {
    case ENTRY_FUNCTION:
        printf("FUNCTION: %s", e->u.function.name) ;
        printf(" returns %s\n", _th_print_exp(e->u.function.return_type)) ;
        printf("    Parameters:\n") ;
        for (i = 0; i < e->u.function.count; ++i) {
            printf("        %s %s\n",
                _th_intern_decode(e->u.function.parameters[i].name),
                _th_print_exp(e->u.function.parameters[i].type)) ;
        }
        inst = e->u.function.code  ;
        i = 0 ;
        while (inst != NULL) {
            print_instruction(i,inst) ;
            inst = inst->next ;
            ++i ;
        }
        break ;
    case ENTRY_GLOBAL_VARIABLE:
        printf("GLOBAL %s %s\n",
            _th_intern_decode(e->u.global_var.var),
            _th_print_exp(e->u.global_var.type)) ;
        break ;
    case ENTRY_PRECONDITION:
        printf("PRECONDITION %s %s\n",
            _th_intern_decode(e->u.cond.function),
            _th_print_exp(e->u.cond.condition)) ;
        break ;
    case ENTRY_POSTCONDITION:
        printf("POSTCONDITION %s %s\n",
            _th_intern_decode(e->u.cond.function),
            _th_print_exp(e->u.cond.condition)) ;
        break ;
    default:
        printf("Unknown entry type\n") ;
    }
    _th_print_assembly(e->next) ;
}

struct entry *compile_proc(int space, struct env *env, struct _ex_intern *e)
{
    int count, i ;
    struct _ex_intern *p ;
    struct goto_link *gto ;
    struct entry *entry ;
    
    count = cons_count(e->u.appl.args[2]) ;
    entry = (struct entry *)_th_alloc(space, sizeof(struct entry) + sizeof(struct cparameter) * (count - 1)) ;
    entry->type = ENTRY_FUNCTION ;
    entry->u.function.name = strdup(get_complete_name_string(e->u.appl.args[0])) ;
    printf("Compiling %s\n", entry->u.function.name) ;
    entry->u.function.return_type = e->u.appl.args[1] ;
    p = e->u.appl.args[2] ;
    entry->u.function.count = count ;
    local_vars = NULL ;
    scope = 0 ;
    for (i = 0; i < count; ++i) {
        entry->u.function.parameters[i].name = _th_intern(p->u.appl.args[0]->u.appl.args[0]->u.string) ;
        entry->u.function.parameters[i].type = p->u.appl.args[0]->u.appl.args[1] ;
        add_local_var(space, scope, entry->u.function.parameters[i].name,
            entry->u.function.parameters[i].type) ;
        p = p->u.appl.args[1] ;
    }
    _th_push_current(3) ;
    gto = NULL ;
    entry->u.function.code = compile(space, env, e->u.appl.args[4], 0, &gto) ;
    entry->u.function.local_vars = local_vars ;
    printf("entry, entry->u.function.count = %x %d\n", entry, entry->u.function.count) ;
    _th_pop_current() ;
    
    return entry ;
}

struct entry *compile_extern_proc(int space, struct env *env, struct _ex_intern *e)
{
    int count, i ;
    struct _ex_intern *p ;
    struct goto_link *gto ;
    struct entry *entry ;
    
    count = cons_count(e->u.appl.args[2]) ;
    entry = (struct entry *)_th_alloc(space, sizeof(struct entry) + sizeof(struct cparameter) * (count - 1)) ;
    entry->type = ENTRY_EXTERN_FUNCTION ;
    entry->u.function.name = strdup(get_complete_name_string(e->u.appl.args[0])) ;
    printf("Compiling %s\n", entry->u.function.name) ;
    entry->u.function.return_type = e->u.appl.args[1] ;
    p = e->u.appl.args[2] ;
    entry->u.function.count = count ;
    local_vars = NULL ;
    scope = 0 ;
    for (i = 0; i < count; ++i) {
        entry->u.function.parameters[i].name = _th_intern(p->u.appl.args[0]->u.appl.args[0]->u.string) ;
        entry->u.function.parameters[i].type = p->u.appl.args[0]->u.appl.args[1] ;
        add_local_var(space, scope, entry->u.function.parameters[i].name,
            entry->u.function.parameters[i].type) ;
        p = p->u.appl.args[1] ;
    }
    gto = NULL ;
    
    return entry ;
}

struct entry *compile_extern_proc_fun(int space, struct env *env, struct _ex_intern *e)
{
    int count, i ;
    struct _ex_intern *p ;
    struct goto_link *gto ;
    struct entry *entry ;
    
    printf("Compiling extern function %s\n", _th_print_exp(e)) ;
    fflush(stdout) ;
    
    count = cons_count(e->u.appl.args[1]->u.appl.args[1]) ;
    entry = (struct entry *)_th_alloc(space, sizeof(struct entry) + sizeof(struct cparameter) * (count - 1)) ;
    entry->type = ENTRY_EXTERN_FUNCTION ;
    entry->u.function.name = strdup(get_complete_name_string(e->u.appl.args[0])) ;
    printf("Compiling %s\n", entry->u.function.name) ;
    entry->u.function.return_type = e->u.appl.args[1]->u.appl.args[0] ;
    p = e->u.appl.args[1]->u.appl.args[1] ;
    entry->u.function.count = count ;
    local_vars = NULL ;
    scope = 0 ;
    for (i = 0; i < count; ++i) {
        entry->u.function.parameters[i].name = _th_intern(p->u.appl.args[0]->u.appl.args[0]->u.string) ;
        entry->u.function.parameters[i].type = p->u.appl.args[0]->u.appl.args[1] ;
        add_local_var(space, scope, entry->u.function.parameters[i].name,
            entry->u.function.parameters[i].type) ;
        p = p->u.appl.args[1] ;
    }
    gto = NULL ;
    
    return entry ;
}

static struct _ex_intern *function, *last_function, *type ;

static void add_fun(struct env *env)
{
    if (function != NULL) {
        printf("Adding function %s with type", _th_print_exp(function)) ;
        printf(" %s\n", _th_print_exp(type)) ;
        _th_add_function(env,function,type,_ex_true,0,NULL) ;
    }
    function = type = NULL ;
}

void add_all_symbols_smaller(struct env *env, unsigned symbol, struct _ex_intern *e)
{
    int i ;
    
    switch (e->type) {
    case EXP_APPL:
        printf("*** Adding %s %s\n", _th_intern_decode(e->u.appl.functor), _th_intern_decode(symbol)) ;
        fflush(stdout) ;
        _th_log_add_precedence(ENVIRONMENT_SPACE,env,e->u.appl.functor,symbol) ;
        for (i = 0; i < e->u.appl.count; ++i) {
            add_all_symbols_smaller(env,symbol,e->u.appl.args[i]) ;
        }
        break ;
    case EXP_QUANT:
        printf("*** Adding %s %s\n", _th_intern_decode(e->u.quant.quant), _th_intern_decode(symbol)) ;
        fflush(stdout) ;
        _th_log_add_precedence(ENVIRONMENT_SPACE,env,e->u.quant.quant,symbol) ;
        add_all_symbols_smaller(env,symbol,e->u.quant.exp) ;
        add_all_symbols_smaller(env,symbol,e->u.quant.cond) ;
        break ;
    case EXP_CASE:
        add_all_symbols_smaller(env,symbol,e->u.case_stmt.exp) ;
        for (i = 0; i < e->u.case_stmt.count*2; ++i) {
            add_all_symbols_smaller(env,symbol,e->u.case_stmt.args[i]) ;
        }
        break ;
    }
}

void add_prop_prec(struct env *env, struct _ex_intern *rule)
{
    unsigned symbol = last_function->u.appl.functor ;
    struct _ex_intern *e ;
    printf("***Precedence for rule %s\n", _th_print_exp(rule)) ;
    if (rule->type != EXP_APPL ||
        (rule->u.appl.functor != INTERN_ORIENTED_RULE &&
        rule->u.appl.functor != INTERN_FORCE_ORIENTED &&
        rule->u.appl.functor != INTERN_UNORIENTED_RULE &&
        rule->u.appl.functor != INTERN_EQUAL)) {
        rule = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,rule,_ex_true,_ex_true) ;
    }
    
    if (rule->u.appl.args[0]->type==EXP_APPL &&
        rule->u.appl.args[0]->u.appl.functor==symbol) {
        e = rule->u.appl.args[1] ;
    } else {
        e = rule->u.appl.args[0] ;
    }
    
    add_all_symbols_smaller(env,symbol,e) ;
    if (rule->u.appl.functor != INTERN_EQUAL) add_all_symbols_smaller(env,symbol,rule->u.appl.args[2]) ;
    
}

static struct entry *icompile(int space, struct env *env, struct name_space *ns, struct _ex_intern *program)
{
    struct _ex_intern *f, *prop ;
    struct parameter parameters[5] ;
    
restart:
    if (program->type==EXP_APPL && program->u.appl.functor==INTERN_NIL) return NULL ;
    
    if (program->type==EXP_APPL && program->u.appl.functor==INTERN_CONS) {
        struct _ex_intern *e = program->u.appl.args[0] ;
        struct entry *entry ;
        struct state_checks *ch ;
        printf("compiling 'e' = %s\n", _th_print_exp(e)) ;
        fflush(stdout) ;
        if (e->type==EXP_APPL) {
            printf("e->u.appl.functor = %d\n", e->u.appl.functor);
            switch (e->u.appl.functor) {
            case INTERN_CMACRO:
                program = _th_macro_expand(env, e->u.appl.args[0], program->u.appl.args[1]) ;
                goto restart ;
            case INTERN_CFUNCTION:
                add_fun(env) ;
                last_function = function = e->u.appl.args[0] ;
                entry = NULL ;
                break ;
            case INTERN_CTYPE:
                type = e->u.appl.args[0] ;
                entry = NULL ;
                break ;
            case INTERN_CPROC:
                _th_push_current(0) ;
                printf("Compiling procedure\n") ;
                entry = compile_proc(space, env, e) ;
                _th_pop_current() ;
                break ;
            case INTERN_CEXTERN_PROC:
                entry = compile_extern_proc(space, env, e) ;
                break ;
            case INTERN_CEXTERN_VAR:
            case INTERN_CGLOBAL:
                if (e->u.appl.args[1]->u.appl.functor==INTERN_CFUNCTION_TYPE) {
                    entry = compile_extern_proc_fun(space, env, e) ;
                } else {
                    entry = (struct entry *)_th_alloc(space, sizeof(struct entry)) ;
                    entry->u.global_var.var = _th_intern(e->u.appl.args[0]->u.appl.args[0]->u.appl.args[0]->u.string) ;
                    entry->u.global_var.type = e->u.appl.args[1] ;
                    entry->type = ENTRY_GLOBAL_VARIABLE ;
                    printf("Adding global %s %s\n", _th_intern_decode(entry->u.global_var.var), _th_print_exp(entry->u.global_var.type)) ;
                    // Add the properties
                    _tree_print0("Global var") ;
                    _tree_indent() ;
                    prop = _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE,
                        _ex_intern_appl1_env(env,INTERN_GLOBAL,
                            _ex_intern_string(_th_intern_decode(entry->u.global_var.var))),
                        _ex_true,
                        _ex_true) ;
#ifndef FAST
                    _th_pp_tree_print(env,INTERN_DEFAULT,200,prop) ;
#endif
                    _th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,prop))) ;
                    prop = _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE,
                        _ex_intern_appl1_env(env, INTERN_GETGLOBALTYPE,
                            _ex_intern_string(_th_intern_decode(entry->u.global_var.var))),
                        entry->u.global_var.type,
                        _ex_true) ;
#ifndef FAST
                    _th_pp_tree_print(env,INTERN_DEFAULT,200,prop) ;
#endif
                    _th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,prop))) ;
                    _tree_undent() ;
                }
                break ;
            case INTERN_CPRE:
                add_fun(env) ;
                entry = (struct entry *)_th_alloc(space, sizeof(struct entry)) ;
                entry->u.cond.function = _th_intern(e->u.appl.args[0]->u.string) ;
                entry->u.cond.condition = e->u.appl.args[1] ;
                entry->type = ENTRY_PRECONDITION ;
                printf("Precondition for function %s\n", _th_intern_decode(entry->u.cond.function)) ;
                printf("%s\n", _th_print_exp(entry->u.cond.condition)) ;
                _th_check(env,_ex_bool,entry->u.cond.condition) ;
                break ;
            case INTERN_CPOST:
                add_fun(env) ;
                entry = (struct entry *)_th_alloc(space, sizeof(struct entry)) ;
                entry->u.cond.function = _th_intern(e->u.appl.args[0]->u.string) ;
                entry->u.cond.condition = e->u.appl.args[1] ;
                entry->type = ENTRY_POSTCONDITION ;
                printf("Postcondition for function %s\n", _th_intern_decode(entry->u.cond.function)) ;
                printf("%s\n", _th_print_exp(entry->u.cond.condition)) ;
                _th_check(env,_ex_bool,entry->u.cond.condition) ;
                break ;
            case INTERN_CMODIFIES:
                add_fun(env) ;
                entry = (struct entry *)_th_alloc(space, sizeof(struct entry)) ;
                entry->u.cond.function = _th_intern(e->u.appl.args[0]->u.string) ;
                entry->u.cond.variable = e->u.appl.args[1] ;
                entry->u.cond.type = e->u.appl.args[2] ;
                entry->u.cond.condition = e->u.appl.args[3] ;
                entry->type = ENTRY_MODIFIES ;
                printf("function %s modifies\n", _th_intern_decode(entry->u.cond.function)) ;
                printf("variable %s\n", _th_print_exp(entry->u.cond.variable)) ;
                printf("type %s\n", _th_print_exp(entry->u.cond.type)) ;
                printf("condition %s\n", _th_print_exp(entry->u.cond.condition)) ;
                _th_check(env,_ex_bool,entry->u.cond.condition) ;
                break ;
            case INTERN_CINVARIANT:
                add_fun(env) ;
                entry = (struct entry *)_th_alloc(space, sizeof(struct entry)) ;
                entry->u.cond.condition = e->u.appl.args[0] ;
                entry->type = ENTRY_INVARIANT ;
                printf("invariant\n", _th_intern_decode(entry->u.cond.function)) ;
                printf("%s\n", _th_print_exp(entry->u.cond.condition)) ;
                _th_check(env,_ex_bool,entry->u.cond.condition) ;
                break ;
            case INTERN_CPREC_LESS:
                entry = NULL ;
                printf("Adding precedence %s %s\n", e->u.appl.args[0]->u.string,
                    e->u.appl.args[1]->u.string) ;
                _th_log_add_precedence(ENVIRONMENT_SPACE,env,
                    _th_intern(e->u.appl.args[0]->u.string),
                    _th_intern(e->u.appl.args[1]->u.string)) ;
                break ;
            case INTERN_CPREC_EQUAL:
                entry = NULL ;
                printf("Adding equal precedence %s %s\n", e->u.appl.args[0]->u.string,
                    e->u.appl.args[1]->u.string) ;
                _th_log_add_equal_precedence(ENVIRONMENT_SPACE,env,
                    _th_intern(e->u.appl.args[0]->u.string),
                    _th_intern(e->u.appl.args[1]->u.string)) ;
                break ;
            case INTERN_CMAX_PREC:
                entry = NULL ;
                printf("Adding maxprec %s\n", e->u.appl.args[0]->u.string) ;
                _th_log_add_max_precedence(ENVIRONMENT_SPACE,env,
                    _th_intern(e->u.appl.args[0]->u.string)) ;
                break ;

            case INTERN_CORDER:
                entry = NULL ;
                printf("Adding order %s %s %s\n",
                    e->u.appl.args[0]->u.string,
                    e->u.appl.args[1]->u.string,
                    e->u.appl.args[2]->u.string) ;
                parameters[0].type = SYMBOL_PARAMETER ;
                parameters[0].u.symbol = _th_intern(e->u.appl.args[1]->u.string) ;
                parameters[1].type = SYMBOL_PARAMETER ;
                parameters[1].u.symbol = _th_intern(e->u.appl.args[2]->u.string) ;
                _th_log_add_attrib(ENVIRONMENT_SPACE,env,_th_intern(e->u.appl.args[0]->u.string),2,parameters) ;
                break ;
            case INTERN_C_MI:
                entry = NULL;
                printf("**CMI** %s\n", _th_print_exp(e));
                parameters[0].type = EXP_PARAMETER;
                parameters[0].u.exp = e->u.appl.args[0];
                parameters[1].type = EXP_PARAMETER;
                parameters[1].u.exp = e->u.appl.args[1];
                parameters[2].type = SYMBOL_PARAMETER;
                parameters[2].u.symbol = _th_intern(e->u.appl.args[2]->u.string);
                parameters[3].type = SYMBOL_PARAMETER;
                parameters[3].u.symbol = _th_intern(e->u.appl.args[3]->u.string);
                _th_log_add_attrib(ENVIRONMENT_SPACE,env,INTERN_MI,4,parameters);
                break ;
            case INTERN_C_SMI:
                entry = NULL;
                printf("**CSMI** %s\n", _th_print_exp(e));
                parameters[0].type = EXP_PARAMETER;
                parameters[0].u.exp = e->u.appl.args[0];
                parameters[1].type = EXP_PARAMETER;
                parameters[1].u.exp = e->u.appl.args[1];
                parameters[2].type = SYMBOL_PARAMETER;
                parameters[2].u.symbol = _th_intern(e->u.appl.args[2]->u.string);
                parameters[3].type = SYMBOL_PARAMETER;
                parameters[3].u.symbol = _th_intern(e->u.appl.args[3]->u.string);
                _th_log_add_attrib(ENVIRONMENT_SPACE,env,INTERN_SMI,4,parameters);
                break ;
            case INTERN_C_MD:
                entry = NULL;
                printf("**CMD** %s\n", _th_print_exp(e));
                parameters[0].type = EXP_PARAMETER;
                parameters[0].u.exp = e->u.appl.args[0];
                parameters[1].type = EXP_PARAMETER;
                parameters[1].u.exp = e->u.appl.args[1];
                parameters[2].type = SYMBOL_PARAMETER;
                parameters[2].u.symbol = _th_intern(e->u.appl.args[2]->u.string);
                parameters[3].type = SYMBOL_PARAMETER;
                parameters[3].u.symbol = _th_intern(e->u.appl.args[3]->u.string);
                _th_log_add_attrib(ENVIRONMENT_SPACE,env,INTERN_MD,4,parameters);
                break ;
            case INTERN_C_SMD:
                entry = NULL;
                printf("**CSMD** %s\n", _th_print_exp(e));
                parameters[0].type = EXP_PARAMETER;
                parameters[0].u.exp = e->u.appl.args[0];
                parameters[1].type = EXP_PARAMETER;
                parameters[1].u.exp = e->u.appl.args[1];
                parameters[2].type = SYMBOL_PARAMETER;
                parameters[2].u.symbol = _th_intern(e->u.appl.args[2]->u.string);
                parameters[3].type = SYMBOL_PARAMETER;
                parameters[3].u.symbol = _th_intern(e->u.appl.args[3]->u.string);
                _th_log_add_attrib(ENVIRONMENT_SPACE,env,INTERN_SMD,4,parameters);
                break ;
            case INTERN_CPROPP:
            case INTERN_CDEF:
                add_prop_prec(env,e->u.appl.args[0]) ;
            case INTERN_CPROP:
                add_fun(env) ;
                entry = NULL ;
                _th_clear_cache() ;
                _th_check(env,_ex_bool,e->u.appl.args[0]) ;
                f = _th_log_rewrite(env,e->u.appl.args[0]) ;
                printf("prop %s\n", _th_print_exp(e->u.appl.args[0])) ;
                printf("prop2 %s\n", _th_print_exp(f)) ;
                _th_log_derive_and_add_property(ENVIRONMENT_SPACE,env,f) ;
                break ;
            case INTERN_CSTATE_CHECK:
                entry = NULL;
                ch = (struct state_checks *)_th_alloc(ENVIRONMENT_SPACE,sizeof(struct state_checks)) ;
                ch->next = _th_get_state_checks(env) ;
                _th_set_state_checks(env,ch) ;
                ch->condition = e->u.appl.args[1] ;
                if (ch->condition->type==EXP_APPL && ch->condition->u.appl.functor==INTERN_QUOTE) {
                    ch->condition = ch->condition->u.appl.args[0] ;
                }
                ch->name = e->u.appl.args[0]->u.string ;
                printf("Adding state check %s %s\n", ch->name, _th_print_exp(ch->condition)) ;
                break ;
            default:
                printf("Unknown program construct\n");
                entry = NULL ;
                        }
                } else {
                    entry = NULL ;
                }
                _th_push_current(1) ;
                program = program->u.appl.args[1] ;
                if (entry==NULL) {
                    entry = icompile(space, env, ns, program) ;
                } else {
                    if (entries==NULL) {
                        entries = entry ;
                        printf("*** Adding entries %d\n", entries) ;
                    } else {
                        parent_ent->next = entry ;
                    }
                    parent_ent = entry ;
                    entry->next = NULL ;
                    icompile(space, env, ns, program) ;
                }
                _th_pop_current() ;
                return entry ;
        }
        return NULL;
}

void create_global_assertions(int space, struct env *env, struct entry *list)
{
    struct entry *l ;
    struct _ex_intern *e ;
    struct _ex_intern *args2[3] ;
    struct record_info *info ;
    struct record_field *field ;
    
    _tree_print0("Global environment rules") ;
    _tree_indent() ;
    
    args2[2] = _ex_true ;
    l = list ;
    
    info = _th_name_space->records ;
    while (info != NULL) {
        struct _ex_intern **args ;
        int count = 0 ;
        field = info->field ;
        while(field != NULL) {
            field = field->next ;
            ++count ;
        }
        args = ALLOCA(sizeof(struct _ex_intern *) * count) ;
        count = 0 ;
        field = info->field ;
        while(field != NULL) {
            struct _ex_intern *name = _ex_intern_appl2_env(env,INTERN_CONS,
                _ex_intern_appl1_env(env,INTERN_CNAME,
                _ex_intern_string(_th_intern_decode(info->name))),
                _ex_intern_appl_env(env,INTERN_NIL,0,NULL)) ;
            args[count++] = _ex_intern_string(_th_intern_decode(field->name)) ;
            e = _ex_intern_appl2_env(env,INTERN_FIELD,
                name,
                _ex_intern_string(_th_intern_decode(field->name))) ;
#ifndef FAST
            _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
#endif
            _th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,e))) ;
            e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,
                _ex_intern_appl2_env(env,INTERN_FIELD_TYPE,
                name,
                _ex_intern_string(_th_intern_decode(field->name))),
                field->type,
                _ex_true) ;
#ifndef FAST
            _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
#endif
            _th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,e))) ;
            e = _ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,
                _ex_intern_appl2_env(env,INTERN_FIELD_NUM,
                name,
                _ex_intern_string(_th_intern_decode(field->name))),
                _ex_intern_small_integer(field->ref_num),
                _ex_true) ;
#ifndef FAST
            _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
#endif
            _th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,e))) ;
            field = field->next ;
        }
        e = _ex_intern_appl3_env(env, INTERN_ORIENTED_RULE,
                _ex_intern_appl1_env(env, INTERN_FIELD_SET,
                    _ex_intern_appl2_env(env,INTERN_CONS,
                        _ex_intern_appl1_env(env,INTERN_CNAME,
                            _ex_intern_string(_th_intern_decode(info->name))),
                        _ex_intern_appl_env(env,INTERN_NIL,0,NULL))),
                _ex_intern_appl_env(env,INTERN_SET,count,args),_ex_true) ;
#ifndef FAST
        _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
#endif
        _th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,e))) ;
        info = info->next ;
    }
#ifdef XX
    while(l != NULL) {
        _tree_print2("%x %d", l, l->type) ;

        switch (l->type) {
            
        case ENTRY_GLOBAL_VARIABLE:
            args[0] = _ex_intern_string(_th_intern_decode(l->u.global_var.var)) ;
            args2[0] = _ex_intern_appl(INTERN_GLOBAL,1,args) ;
            args2[1] = _ex_true ;
            e = _ex_intern_appl(INTERN_ORIENTED_RULE,3,args2) ;
#ifndef FAST
            _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
#endif
            _th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,e))) ;
            args2[0] = _ex_intern_appl(INTERN_GETGLOBALTYPE,1,args) ;
            args2[1] = l->u.global_var.type ;
            e = _ex_intern_appl(INTERN_ORIENTED_RULE,3,args2) ;
#ifndef FAST
            _th_pp_tree_print(env,INTERN_DEFAULT,200,e) ;
#endif
            _th_log_derive_and_add(env, _th_derive_simplify(env,_th_mark_vars(env,e))) ;
            break ;
        }
        l = l->next ;
    }
#endif

    _tree_undent() ;
}

struct entry *_th_compile(int space, struct env *env, struct _ex_intern *program)
{
    struct entry *r ;
    
    _tree_print0("Compiling") ;
    _tree_indent() ;

    function = type = NULL ;
    
    entries = NULL ;
    
    program = _th_flatten(env,program) ;
    
    _th_name_space = build_root_space(space, program) ;
    print_name_space(0, _th_name_space) ;
    
    printf("program = %s\n", _th_pp_print(env,INTERN_DEFAULT,80,program)) ;
    
    _th_log_derive_push(env) ;

    _th_log_derive_and_add_property(ENVIRONMENT_SPACE,env,_ex_intern_appl3_env(env,INTERN_ORIENTED_RULE,_ex_intern_appl_env(env,INTERN_CURRENT_LEVEL,0,NULL),_ex_intern_small_integer(0),_ex_true)) ;

    _th_reset_context() ;
    _th_clear_cache() ;

    r = icompile(space, env, _th_name_space, program) ;
    create_global_assertions(ENVIRONMENT_SPACE, env, entries) ;
    add_fun(env) ;

    //_th_log_derive_push(env) ;

    _tree_undent() ;
    
    return r ;
}
