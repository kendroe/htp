/*
 * intern.c
 *
 * Symbol intern package
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "Globals.h"

static int next_intern ;

int _th_intern_count()
{
    return next_intern ;
}

#define HASH_TABLE_SIZE 4093

#define MALLOC_SIZE 1024

struct malloc_block {
    struct malloc_block *next ;
    char data[MALLOC_SIZE] ;
} ;
/*# dataSet(malloc_block,|struct malloc_block|,<<<next*>>>) */

static struct malloc_block *memory ;
static unsigned offset ;
/*# abstraction internAlloc() */
/*# involves internAlloc memory, offset, { *s [s]: s in malloc_blockSet(state,{memory}) } */
/*# memoryBlocks internAlloc */

/*# prop internAlloc ALL(x: x in internAllocSet(state)) EXISTS(y) y in malloc_blockSet(state,{memory}) &&
                                         {x..x+allocSize(state,x)-1} subset {y->data..y->data+(y==memory?offset-1:MALLOC_SIZE-1)) */
/*# prop internAlloc offset <= MALLOC_SIZE */
/*# prop internAlloc offset >= 0 */

struct quant_link {
    struct quant_link *next ;
    int level ;
} ;

struct intern_link {
    struct intern_link *next ;
    int intern ;
    unsigned data ;
    unsigned data2 ;
    struct quant_link *quant_level ;
    char name[1] ;
} ;

/*# dataSet("intern_link",struct intern_link,<<<next*>>>) */
/*# dataSet("quant_link",struct quant_link,<<<next*>>>) */

static struct intern_link *symbol_table[HASH_TABLE_SIZE] ;
static struct intern_link **decode_table ;
static int decode_size = 0 ;
/*# abstraction internSet */
/*# usesAbstraction internSet internAlloc */
/*# involves symbol_table, decode_table, { *decode_table[x] [x]: x in [1..next_intern-1] } },
             internAlloc { *x, [x,y]: x in intern_linkSet(state,{symbol_table[y]}) && y in {0..HASH_TABLE_SIZE-1} },
             alloc { *z, [x,y,z]: x in intern_linkSet(state,{symbol_table[y]}) && y in {0..HASH_TABLE_SIZE-1} &&
                                  z in quant_linkSet(state,{x}) } */
/*# domainSet internSet interns String() */
/*# domainSet internSet values Integer() */
/*# map oneToOne internMap: interns -> values */
/*# map quantLevel: interns -> List(Integer()) */
/*# map data: interns -> Integer() */
/*# map data2: interns -> Integer() */

/*# prop internAllocSet()=={ x [x,i]: i in {0..HASH_TABLE_SIZE-1} && x in intern_linkSet(state,{symbol_table[i])) } */
/*# prop internSet_interns(state) -> { x->name [x,i]: i in {0..HASH_TABLE_SIZE-1} && x in intern_linkSet(state,{symbol_table[i]}) } */
/*# prop internSet_values(state) -> {1..decode_size-1} */
/*# prop internSet_internMap(x->name) { EXISTS(y) x in intern_linkSet(state,{symbol_table[y]}) && y in {0..HASH_TABLE_SIZE-1} } -> x->intern */

/*# allPathsDistinct("interns", [0..HASH_TABLE_SIZE-1](lambda(x) intern_linkSet(state,{x})){(lambda (x) quant_linkSet(state,{x}))})

/*# function hash(state,loc) */
/*# type State() * Integer() -> Integer() */
/*#     hash(state,loc) -> (fold (lambda (sum,x) sum+*x * *x)
                                 0 { x [x]: x >= loc && x < loc + endofstring(state,loc) })%HASH_SIZE */

/*# function symbol_table_valid(state) */
/*# type State() -> Bool() */
/*# prop symbol_table_valid(state) ->
    next_intern <= decode_size+1 &&
    (decode_size==0 || (decode_table in allocSet(state()) &&
                        allocSize(decode_table)==decode_size*sizeof(int *))) &&
    { x [x,i]: i in {0..HASH_TABLE_SIZE-1} && x in intern_linkSet(state,{symbol_table[i]}) } ==
    { decode_table[i] [i]: i in {1..next_intern-1} } &&
    quantLevel(decode_table[i]->name) -> makeList(decode_table[i]->quant_level,q,q->level,<<<next>>>) &&
    data(decode_table[i]->name)==decode_table[i]->data &&
    data2(decode_table[i]->name)==decode_table[i]->data2 &&
    ALL(i: i > 0 && i < next_intern)
        (decode_table[i]->intern==i &&
         (ALL(j: j > 0 && j < next_intern && i != j) decode_table[i] != decode_table[j]) &&
         decode_table[i] in intern_linkSet(state,{symbol_table[hash(state,decode_table[i]->name)]})
        ) */

/*# validAbstraction internSet symbol_table_valid symbol_table_valid(state) */

/*# post hash_function return==hash(pre,name') */
/*# no_modifications hash_function */
static int hash_function(char *name)
/*
 * Function for deciding which bin in the hash table the symbol belongs in.
 */
{
    int hash = 0 ;

    /*# invariant hash==fold (lambda (sum,x) sum+ *x* *x) 0
                             { x [x]: x >= name' && x <= name } */
    /*# modifies hash, name */
    while(*name) {
        hash += (*name) * (*name) ;
        ++name ;
    }

    return hash % HASH_TABLE_SIZE ;
}

/*# post _th_intern_shutdown internAllocSet(state) == {} */
/*# post _th_intern_shutdown malloc_blockSet(state(),{memory})=={} */
/*# usesAbstraction _th_intern_shutdown internAlloc */
/*# modifies _th_intern_shutdown internAllocSet */ 
void _th_intern_shutdown()
/*
 * Deallocate all data structures
 */
{
    struct malloc_block *m ;

#ifdef _DEBUG
    printf("\n*** Symbols allocated: %d\n\n", next_intern) ;
#endif

    /* Free up the memory */
    /*# invariant allocSet(state) diff malloc_blockSet(state,{memory}) ->
                  allocSet(loop) diff malloc_blockSet(loop,{memory''}) */
    /*# invariant malloc_blockSet(state,{memory}) subset allocSet(state) */
    /*# modifies allocSet(state()), m, memory, *x:x in malloc_blockSet(state,{memory}) */
    while (memory != NULL) {
        m = memory->next ;
        FREE(memory) ;
        memory = m ;
    }
}

/*# usesAbstraction _th_intern internAlloc, internSet */
/*# modifies interns, values, internMap */
/*# post internSet == internSet' union getstring(pre,symbol) */
/*# post ALL(x: x in internSet(pre)) internMap(state,x)==internMap(pre,x) */
/*# post ALL(x: x in internSet(state) && x != getstring(pre,symbol))
             internVal(state,getstring(pre,symbol))==internVal(state,x) */
/*# post return = internMap(symbol) */
int _th_intern(char *symbol)
/*
 * Find the intern value of a symbol.  If it is not in the table, then allocate
 * it.
 */
{
    int hash = hash_function(symbol) ;
    struct intern_link *l ;

    /* First try and find it */
    l = symbol_table[hash] ;

    /*# modifies l */
    while(l != NULL) {
        if (!strcmp(l->name, symbol)) break ;
        l = l->next ;
    }

     /* Allocate it if it does not exist */
    if (l == NULL) {
        /*# mark mark */
        if (MALLOC_SIZE - offset > sizeof(struct intern_link)+strlen(symbol)) {
            l = (struct intern_link *)(memory->data+offset) ;
            offset += ((sizeof(struct intern_link)+strlen(symbol)+3)&0xfffffffc) ;
        } else {
            struct malloc_block *m =
                   (struct malloc_block *)MALLOC(sizeof(struct malloc_block)) ;
            m->next = memory ;
            memory = m ;
            offset = (sizeof(struct intern_link)+strlen(symbol)+3)&0xfffffffc ;
            l = (struct intern_link *)m->data ;
        }
        /*# define internAllocSet(state) -> internAllocSet(pre) union l */
        /*# define internAllocSize(state,l)==sizeof(struct intern_link) */
        /*# define ALL(x: x in internAllocSet(mark) internAllocSize(state,x) -> internAllocSize(mark,x) */
        l->next = symbol_table[hash] ;
        symbol_table[hash] = l ;
        strcpy(l->name, symbol) ;
        l->quant_level = NULL ;
        l->data = 0 ;
        l->data2 = 0 ;
        l->intern = next_intern++ ;

        if (l->intern >= decode_size) {
            if (decode_size < 4000) {
                decode_table = (struct intern_link **)MALLOC(sizeof(struct intern_link *) * 4000) ;
                decode_size = 4000 ;
            } else {
                decode_size *= 2 ;
                decode_table = (struct intern_link **)REALLOC(decode_table,
                                       sizeof(struct intern_link *) * decode_size) ;
            }
        }
        decode_table[l->intern] = l ;
    }
    return l->intern ;
}

/*# no_modifications _th_intern_decode */
/*# post _th_intern_decode internMap(return)==i */
char *_th_intern_decode(int i)
{
    if (i<=0 || i>=next_intern) {
        static char x[20] ;
        sprintf(x, "undef #%d", i) ;
        return x ;
    }
    return decode_table[i]->name ;
}

int _th_intern_concat(int a, int b)
{
    char *x = _th_intern_decode(a);
    char *y = _th_intern_decode(b);
    char *z = ALLOCA(strlen(x)+strlen(y)+1);
    strcpy(z,x);
    strcat(z,y);
    return _th_intern(z);
}

int _th_intern_is_legal(int i)
{
    return i> 0 && i < next_intern;
}

/*# no_modifications _th_intern_get_data */
unsigned _th_intern_get_data(int i)
{
    return decode_table[i]->data ;
}

/*# modifies _th_intern_set_data decode_table[i]->data */
void _th_intern_set_data(int i,unsigned d)
{
    decode_table[i]->data = d ;
}

/*# no_modifications _th_intern_get_data2 */
unsigned _th_intern_get_data2(int i)
{
    return decode_table[i]->data2 ;
}

/*# modifies _th_intern_set_data2 decode_table[i]->data2 */
void _th_intern_set_data2(int i,unsigned d)
{
    decode_table[i]->data2 = d ;
}

/*# usesAbstraction _th_intern_init internAlloc, internSet */
/*# modifies interns, values, internMap */
/*# uninitialized internAlloc, internSet */
void _th_intern_init ()
/*
 * Initialize the symbol hash table.
 */
{
    int i ;

    /**********/

    for (i = 0; i < HASH_TABLE_SIZE; ++i) {
        symbol_table[i] = 0 ;
    }

    memory = (struct malloc_block *)MALLOC(sizeof(struct malloc_block)) ;
    memory->next = NULL ;
    offset = 0 ;
    next_intern = 1 ;

    _th_intern("->") ;
    _th_intern("=") ;
    _th_intern("Bool") ;
    _th_intern("True") ;
    _th_intern("False") ;
    _th_intern("Unit") ;
    _th_intern("Identity") ;
    _th_intern("Trivial") ;
    _th_intern("&&") ;
    _th_intern("||") ;
    _th_intern("==") ;
    _th_intern("preceq") ;
    _th_intern("defined") ;
    _th_intern("ALL") ;
    _th_intern("EXISTS") ;
    _th_intern("*") ;
    _th_intern("not") ;
    _th_intern("ite") ;
    _th_intern("Undef") ;
    _th_intern("Set") ;
    _th_intern("Cons") ;
    _th_intern("Nil") ;
    _th_intern("attr") ;
    _th_intern("AC") ;
    _th_intern("A") ;
    _th_intern("C") ;
    _th_intern("EPO") ;
    _th_intern("EQ") ;
    _th_intern("DERIVE") ;
    _th_intern("TO") ;
    _th_intern("ETO") ;
    _th_intern("PO") ;
    _th_intern("SMI") ;
    _th_intern("CSMI") ;
    _th_intern("OMI") ;
    _th_intern("COMI") ;
    _th_intern("SMD") ;
    _th_intern("CSMD") ;
    _th_intern("OMD") ;
    _th_intern("COMD") ;
    _th_intern("MI") ;
    _th_intern("CMI") ;
    _th_intern("MD") ;
    _th_intern("CMD") ;
    _th_intern("Solved") ;
    _th_intern("T") ;
    _th_intern("goal") ;
    _th_intern("node") ;
    _th_intern("branch") ;
    _th_intern("subterm") ;
    _th_intern("pattern") ;
    _th_intern("down") ;
    _th_intern("top_goal") ;
    _th_intern("top_node") ;
    _th_intern("top_branch") ;
    _th_intern("top_subterm") ;
    _th_intern("top_pattern") ;
    _th_intern("top_down") ;
    _th_intern("subgoals") ;
    _th_intern("decomp") ;
    _th_intern("<") ;
    _th_intern("+") ;
    _th_intern("/") ;
    _th_intern("%") ;
    _th_intern("-") ;
    _th_intern("size") ;
    _th_intern("char") ;
    _th_intern("concat") ;
    _th_intern("chr") ;
    _th_intern("asc") ;
    _th_intern("def") ;
    _th_intern("default") ;
    _th_intern("lambda") ;
    _th_intern("fn") ;
    _th_intern("apply") ;
    _th_intern("nplus") ;
    _th_intern("nminus") ;
    _th_intern("ntimes") ;
    _th_intern("ndivide") ;
    _th_intern("nless") ;
    _th_intern("nmod") ;
    _th_intern("rplus") ;
    _th_intern("rminus") ;
    _th_intern("rtimes") ;
    _th_intern("rdivide") ;
    _th_intern("rless") ;
    _th_intern("rmod") ;
    _th_intern("ratnat") ;
    _th_intern("natrat") ;
    _th_intern("case") ;
    _th_intern("INDEX") ;
    _th_intern("of") ;
    _th_intern("=>") ;
    _th_intern("v") ;
    _th_intern("Tuple") ;
    _th_intern("Function") ;
    _th_intern("member") ;
    _th_intern("union") ;
    _th_intern("intersect") ;
    _th_intern("EF") ;
    _th_intern("NE") ;
    _th_intern("CS") ;
    _th_intern("ACS") ;
    _th_intern("RC") ;
    _th_intern("QC") ;
    _th_intern("QP") ;
    _th_intern("AQC") ;
    _th_intern("q_nat") ;
    _th_intern("q_rat") ;
    _th_intern("Int") ;
    _th_intern("Real") ;
    _th_intern("String") ;
    _th_intern("SET") ;
    _th_intern("QUOTE") ;
    _th_intern("Quant") ;
    _th_intern("Appl") ;
    _th_intern("Var") ;
    _th_intern("?") ;
    _th_intern("//#") ;
    _th_intern("//") ;
    _th_intern("/*#") ;
    _th_intern("/*") ;
    _th_intern("\\") ;
    _th_intern("(") ;
    _th_intern(")") ;
    _th_intern("[") ;
    _th_intern("]") ;
    _th_intern("{") ;
    _th_intern("}") ;
    _th_intern(":") ;
    _th_intern(",") ;
    _th_intern("'") ;
    _th_intern(";") ;
    _th_intern(" ") ;
    _th_intern("input") ;
    _th_intern("output") ;
    _th_intern("mode") ;
    _th_intern("infix") ;
    _th_intern("infixMode") ;
    _th_intern("permit") ;
    _th_intern("break") ;
    _th_intern("mark") ;
    _th_intern("#") ;
    _th_intern("fb") ;
    _th_intern("fbm") ;
    _th_intern("ob") ;
    _th_intern("obm") ;
    _th_intern("rb") ;
    _th_intern("rbm") ;
    _th_intern("ml") ;
    _th_intern("ol") ;
    _th_intern("identifier") ;
    _th_intern("natural") ;
    _th_intern("Cint") ;
    _th_intern("Cchar") ;
    _th_intern("Carray") ;
    _th_intern("CflexArray") ;
    _th_intern("Cstruct") ;
    _th_intern("Cunion") ;
    _th_intern("DPointer") ;
    _th_intern("VPointer") ;
    _th_intern("SPointer") ;
    _th_intern("NPointer") ;
    _th_intern("Ccomplement") ;
    _th_intern("Cuplus") ;
    _th_intern("Cplus") ;
    _th_intern("Cuminus") ;
    _th_intern("Cminus") ;
    _th_intern("Ctimes") ;
    _th_intern("Cdivide") ;
    _th_intern("Cmod") ;
    _th_intern("Cand") ;
    _th_intern("Cor") ;
    _th_intern("Cxor") ;
    _th_intern("Cland") ;
    _th_intern("Clor") ;
    _th_intern("Cnot") ;
    _th_intern("Clshift") ;
    _th_intern("Crshift") ;
    _th_intern("Cref") ;
    _th_intern("Csub") ;
    _th_intern("Cderef") ;
    _th_intern("Cequal") ;
    _th_intern("Cless") ;
    _th_intern("CnotEqual") ;
    _th_intern("Cgreater") ;
    _th_intern("ClessEqual") ;
    _th_intern("CgreaterEqual") ;
    _th_intern("Cassign") ;
    _th_intern("CplusAssign") ;
    _th_intern("CminusAssign") ;
    _th_intern("CtimesAssign") ;
    _th_intern("CdivideAssign") ;
    _th_intern("CmodAssign") ;
    _th_intern("CandAssign") ;
    _th_intern("CorAssign") ;
    _th_intern("CxorAssign") ;
    _th_intern("CpreIncrement") ;
    _th_intern("CpreDecrement") ;
    _th_intern("CpostIncrement") ;
    _th_intern("CpostDecrement") ;
    _th_intern("Cindex") ;
    _th_intern("Call") ;
    _th_intern("Cvar") ;
    _th_intern("CvarState") ;
    _th_intern("Cstack") ;
    _th_intern("Cnat") ;
    _th_intern("Cfloat") ;
    _th_intern("Cdouble") ;
    _th_intern("Cstring") ;
    _th_intern("Core") ;
    _th_intern("Cpointer") ;
    _th_intern("CgetField") ;
    _th_intern("Cast") ;
    _th_intern("Csizeof") ;
    _th_intern("Cdecl") ;
    _th_intern("CstaticDecl") ;
    _th_intern("Cexpr") ;
    _th_intern("Cblock") ;
    _th_intern("CifElse") ;
    _th_intern("Cwhile") ;
    _th_intern("Cfor") ;
    _th_intern("Creturn") ;
    _th_intern("Cproc") ;
    _th_intern("Cglobal") ;
    _th_intern("Cstatic") ;
    _th_intern("Cpre") ;
    _th_intern("Cinvariant") ;
    _th_intern("Cload") ;
    _th_intern("Cpost") ;
    _th_intern("CstructDecl") ;
    _th_intern("CunionDecl") ;
    _th_intern("CexportValid") ;
    _th_intern("CintDatum") ;
    _th_intern("CfloatDatum") ;
    _th_intern("CcharDatum") ;
    _th_intern("CstructDatum") ;
    _th_intern("CarrayDatum") ;
    _th_intern("CpointerDatum") ;
    _th_intern("Ctypedef") ;
    _th_intern("CclassDecl") ;
    _th_intern("CclassVariable") ;
    _th_intern("CclassProc") ;
    _th_intern("Cvirtual") ;
    _th_intern("Cif") ;
    _th_intern("Clabel") ;
    _th_intern("Cgoto") ;
    _th_intern("Clong") ;
    _th_intern("Cshort") ;
    _th_intern("ClongLong") ;
    _th_intern("CunsignedChar") ;
    _th_intern("CunsignedInt") ;
    _th_intern("CunsignedLong") ;
    _th_intern("CunsignedLongLong") ;
    _th_intern("CunsignedShort") ;
    _th_intern("CpointerType") ;
    _th_intern("Cclass") ;
    _th_intern("global") ;
    _th_intern("local") ;
    _th_intern("getType") ;
    _th_intern("stack") ;
    _th_intern("stack1") ;
    _th_intern("state") ;
    _th_intern("state1") ;
    _th_intern("getStack") ;
    _th_intern("getState") ;
    _th_intern("disjoint") ;
    _th_intern("globalLoc") ;
    _th_intern("localLoc") ;
    _th_intern("getval") ;
    _th_intern("sizeof") ;
    _th_intern("getStackNatural") ;
    _th_intern("stripStackNatural") ;
    _th_intern("getStackRational") ;
    _th_intern("stripStackRational") ;
    _th_intern("getStackString") ;
    _th_intern("stripStackString") ;
    _th_intern("Snatural") ;
    _th_intern("Srational") ;
    _th_intern("Sstring") ;
    _th_intern("pre") ;
    _th_intern("loop") ;
    _th_intern("compatible_prec") ;
    _th_intern("marked_subset") ;
    _th_intern("induce") ;
    _th_intern("low") ;
    _th_intern("and") ;
    _th_intern("or") ;
    _th_intern("Cmodifies") ;
    _th_intern("return") ;
    _th_intern("field") ;
    _th_intern("fieldNum") ;
    _th_intern("fieldType") ;
    _th_intern("Cprop");
    _th_intern("Cfunction");
    _th_intern("Cdef");
    _th_intern("Ctype");
    _th_intern("Cdeforder");
    _th_intern("subset");
    _th_intern("fieldOffset") ;
    _th_intern("getGlobalType") ;
    _th_intern("CprecLess") ;
    _th_intern("CmaxPrec") ;
    _th_intern("CexternProc") ;
    _th_intern("CexternVar") ;
    _th_intern("CfunctionType") ;
    _th_intern("SETQ") ;
    _th_intern("Cname") ;
    _th_intern("difference") ;
    _th_intern("validState") ;
    _th_intern("Cpropp") ;
    _th_intern("RCS") ;
    _th_intern("smaller") ;
    _th_intern("cut") ;
    _th_intern("priority") ;
    _th_intern("matchClosure") ;
    _th_intern("AnyType") ;
    _th_intern("testMatchClosure") ;
    _th_intern("subst") ;
    _th_intern("firstMatchClosure") ;
    _th_intern("replace") ;
    _th_intern("q_var") ;
    _th_intern("choose") ;
    _th_intern("specialRewrites") ;
    _th_intern("andq") ;
    _th_intern("specialRewritesUsing") ;
    _th_intern("getContextRules") ;
    _th_intern("match") ;
    _th_intern("-->") ;
    _th_intern("notl") ;
    _th_intern("add") ;
    _th_intern("delete") ;
    _th_intern("change") ;
    _th_intern("cutLocal") ;
    _th_intern("getTerms") ;
    _th_intern("getCurrentTerm") ;
    _th_intern("unquantify") ;
    _th_intern("quantify") ;
    _th_intern("unquote") ;
    _th_intern("typeClosure") ;
    _th_intern("fireOnChange") ;
    _th_intern("illegalTerm") ;
    _th_intern("normal_condition") ;
    _th_intern("rewritable") ;
    _th_intern("excludeSet") ;
    _th_intern("applyContext") ;
    _th_intern("useContext") ;
    _th_intern("evalCond") ;
    _th_intern("simplifyCond") ;
    _th_intern("mainContext") ;
    _th_intern("inContext") ;
    _th_intern("backchain") ;
    _th_intern("orderCache") ;
    _th_intern("+>") ;
    _th_intern("@>") ;
    _th_intern("Cmacro") ;
    _th_intern("buildFunctor") ;
    _th_intern("natstring") ;
    _th_intern("append") ;
    _th_intern("mapSet") ;
    _th_intern("andSet") ;
    _th_intern("unionSet") ;
    _th_intern("filterSet") ;
    _th_intern("setlist") ;
    _th_intern("listset") ;
    _th_intern("orSet") ;
    _th_intern("currentLevel") ;
    _th_intern("macroContext") ;
    _th_intern("Cassert") ;
    _th_intern("CloopInvariant") ;
    _th_intern("pointernat") ;
    _th_intern("natpointer") ;
    _th_intern("getLimitTerm") ;
    _th_intern("CprecEqual") ;
    _th_intern("NPO") ;
    _th_intern("NEPO") ;
    _th_intern("AnySubterm") ;
    _th_intern("uncompose") ;
    _th_intern("CloopLabel") ;
    _th_intern("separate") ;
    _th_intern("importantState") ;
    _th_intern("chooseContextRule") ;
    _th_intern("kb_rules") ;
    _th_intern("Corder") ;
    _th_intern("context") ;
    _th_intern("nestingLimit") ;
    _th_intern("prune") ;
    _th_intern("q_unusedVar") ;
    _th_intern("blockContext") ;
    _th_intern("fieldSet") ;
    _th_intern("markVars") ;
    _th_intern("hasFreeVars") ;
    _th_intern("checkMode") ;
    _th_intern("checkState") ;
    _th_intern("checkValidity") ;
    _th_intern("checkValidityTerm") ;
    _th_intern("functorArgs") ;
    _th_intern("isAppl") ;
    _th_intern("argCount") ;
    _th_intern("Ccmi");
    _th_intern("Ccsmi");
    _th_intern("Ccmd");
    _th_intern("Ccsmd");
    _th_intern("isFreeIn");
    _th_intern("removeAnd");
    _th_intern("CstateCheck");
    _th_intern("Cmi");
    _th_intern("Cmd");
    _th_intern("Csmi");
    _th_intern("Csmd");
    _th_intern("use_rule");
    _th_intern("varAsString");
    _th_intern("typeOf");
    _th_intern("specialType");
    _th_intern("expressionType");
    _th_intern("Type");
    _th_intern("module");
    _th_intern("instance");
    _th_intern("connect");
    _th_intern("assign");
    _th_intern("parameter");
    _th_intern("register");
    _th_intern("register_vector");
    _th_intern("wire");
    _th_intern("wire_vector");
    _th_intern("input_vector");
    _th_intern("output_vector");
    _th_intern("inout");
    _th_intern("inout_vector");
    _th_intern("nospec");
    _th_intern("reference");
    _th_intern("vec_index");
    _th_intern("delay");
    _th_intern("current");
    _th_intern("par");
    _th_intern("next");
    _th_intern("heuristic");
    _th_intern("npower");
    _th_intern("stateVar");
    _th_intern("noAugment");
    _th_intern("noFunctor");
    _th_intern("edge");
    _th_intern("posedge");
    _th_intern("negedge");
    _th_intern("conditionEdge");
    _th_intern("conditionRoot");
    _th_intern("conditionVariable");
    _th_intern("setsize");
    _th_intern("signalWidth");
    _th_intern("solveFor");
    _th_intern("gcd");
    _th_intern("nmin");
    _th_intern("nmax");
    _th_intern("nintegrate");
    _th_intern("nsolveintegrate");
    _th_intern("normal");
    _th_intern("nintegrateset");
	_th_intern("fd_dom");
	_th_intern("fd_min");
	_th_intern("fd_max");
	_th_intern("fd_filled");
	_th_intern("fd_range");
	_th_intern("bitsel");
    _th_intern("bitplus");
	_th_intern("bitconst");
	_th_intern("bitvec");
	_th_intern("bitnot");
	_th_intern("bitcat");
	_th_intern("true");
	_th_intern("false");
	_th_intern("read");
	_th_intern("write");
	_th_intern("barray");
	_th_intern("bit");
	_th_intern("<=");
	_th_intern("<=>");
	_th_intern("xor");
	_th_intern("array");
	_th_intern("unknown");
    _th_intern(">");
    _th_intern(">=");
    _th_intern("/=");
    _th_intern("$");
    _th_intern("sat");
    _th_intern("unsat");
    _th_intern("~");
    _th_intern("store");
    _th_intern("select");
    _th_intern("Array");
    _th_intern("U");
    _th_intern("EE");
    _th_intern("iff");
    _th_intern("QF_IDL");
    _th_intern("QF_UF");
    _th_intern("QF_UFIDL");
    _th_intern("QF_RDL");
    _th_intern("QF_LRA");
    _th_intern("QF_LIA");
    _th_intern("QF_UFLIA");
    _th_intern("QF_UFBV32");
    _th_intern("QF_AUFLIA");
    _th_intern("AUFLIA");
    _th_intern("AUFLIRA");
    _th_intern("struct_primary_pointer");
    _th_intern("invariant");
    _th_intern("struct_space");
    _th_intern("in");
    _th_intern("..");
    _th_intern(".");
    _th_intern("PathSet");
    _th_intern("PathOr");
    _th_intern("PathStar");
    _th_intern("|") ;
    _th_intern("unsigned");
    _th_intern("int");
    _th_intern("long");
    _th_intern("signed");
    _th_intern("short");
    _th_intern("__attribute__") ;
	_th_intern("Cfun");
	_th_intern("Cvoid");
	_th_intern("void");
	_th_intern("struct");
	_th_intern("const");
	_th_intern("CbitField");
	_th_intern("CintTimesAssign");
	_th_intern("CintPlusAssign");
	_th_intern("CrefAssign");
	_th_intern("CAssignRef");
	_th_intern("while");
	_th_intern("if");
	_th_intern("else");
	_th_intern("!");
	_th_intern("!=");
	_th_intern("extern");
	_th_intern("goto");
	_th_intern("LDEF");
	_th_intern("SigmaPi");
}

/*# usesAbstraction _th_intern_push_quant internAlloc, internSet */
/*# modifies quantLevel(reverseInternMap(symbol)) */
/*# pre _th_intern_pop_quant symbol in values */
void _th_intern_push_quant(unsigned space, unsigned symbol, int level)
{
    struct quant_link *ql = (struct quant_link *)_th_alloc(space,sizeof(struct quant_link)) ;
    ql->next = decode_table[symbol]->quant_level ;
    decode_table[symbol]->quant_level = ql ;
    ql->level = level ;
}

/*# usesAbstraction _th_intern_pop_quant internAlloc, internSet */
/*# modifies _th_intern_pop_quant quantLevel(reverseInternMap(symbol)) */
/*# pre _th_intern_pop_quant quantLevel(reverseInternMap(symbol)) != Nil() */
/*# pre _th_intern_pop_quant symbol in values */
void _th_intern_pop_quant(unsigned symbol)
{
    decode_table[symbol]->quant_level = decode_table[symbol]->quant_level->next ;
}

/*# usesAbstraction _th_intern_get_quant_level internAlloc, internSet */
/*# post return==hd(quantLevel(reverseInternMap(symbol))) */
/*# pre _th_intern_pop_quant symbol in values */
/*# no_modifications */
int _th_intern_get_quant_level(unsigned symbol)
{
    if (decode_table[symbol]->quant_level==NULL) {
        return 0 ;
    } else {
        return decode_table[symbol]->quant_level->level ;
    }
}

#ifdef INTERNTEST
main()
{
    _th_intern_init () ;
    printf("test %d %d %d %d\n",
           _th_intern("a"),_th_intern("b"),_th_intern("c"),_th_intern("b")) ;
}
#endif
