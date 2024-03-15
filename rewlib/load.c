#define PRINT_CORRECTNESS
/*
 * load.c
 *
 * Functions for loading ".def" files
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include "Globals.h"
#include "Intern.h"
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

struct path {
    struct path *next;
    int f;
    int p;
};

static void print_path(struct path *path)
{
    printf("Path:");
    while (path) {
        printf(" %d (%s)", path->p, _th_intern_decode(path->f));
        path = path->next;
    }
}

int similar_names(int n1, int n2)
{
    char *c1 = _th_intern_decode(n1);
    char *c2 = _th_intern_decode(n2);

    while (*c1 && *c2) {
        if (*c1=='B' || *c1=='.' || *c1=='_' || *c1=='4' || *c1=='6') {
            ++c1;
        } else if (*c2=='B' || *c2=='.' || *c2=='_' || *c2=='4' || *c2=='6') {
            ++c2;
        } else if (toupper(*c1)==toupper(*c2)) {
            ++c1;
            ++c2;
        } else {
            return 0;
        }
    }
    return 1;
}

static void diff(struct _ex_intern *e, struct _ex_intern *e2, struct path *path)
{
    int i;
    struct path p;

    if (e==e2) return;

    if (e->type != e2->type) {
        printf("\n\n***************************DIFF:\n");
        printf("e = %s\n\n", _th_print_exp(e));
        printf("e2 = %s\n\n", _th_print_exp(e2));
        print_path(path);
    }

    if (e->type==EXP_APPL) {
        if (!similar_names(e->u.appl.functor, e2->u.appl.functor) || e->u.appl.count != e2->u.appl.count) {
            printf("\n\n***************************DIFF:\n");
            printf("e = %s\n\n", _th_print_exp(e));
            printf("e2 = %s\n\n", _th_print_exp(e2));
            print_path(path);
        } else {
            p.next = path;
            p.f = e->u.appl.functor;
            for (i = 0; i < e->u.appl.count; ++i) {
                p.p = i;
                diff(e->u.appl.args[i],e2->u.appl.args[i], &p);
            }
        }
    } else if (e->type==EXP_VAR && similar_names(e->u.var, e2->u.var)) {
        return;
    } else {
        printf("\n\n***************************DIFF:\n");
        printf("e = %s\n\n", _th_print_exp(e));
        printf("e2 = %s\n\n", _th_print_exp(e2));
        print_path(path);
    }
}

static int is_boolean(struct _ex_intern *rule)
{
    return rule->u.appl.args[0]->type==EXP_MARKED_VAR &&
           rule->u.appl.args[2]==_ex_true &&
           (rule->u.appl.args[1]==_ex_true || rule->u.appl.args[1]==_ex_false);
}

static int is_assignment(struct _ex_intern *rule)
{
    return rule->u.appl.args[0]->type==EXP_MARKED_VAR &&
           rule->u.appl.args[2]==_ex_true &&
           (rule->u.appl.args[1]->type==EXP_INTEGER || rule->u.appl.args[1]->type==EXP_RATIONAL);
}

static int is_join(struct _ex_intern *rule)
{
    return rule->u.appl.args[0]->type==EXP_MARKED_VAR &&
           rule->u.appl.args[2]==_ex_true &&
           rule->u.appl.args[1]->type==EXP_VAR;
}

static int is_disjoin(struct _ex_intern *rule)
{
    return rule->u.appl.args[0]->type==EXP_APPL &&
           rule->u.appl.args[0]->u.appl.functor==INTERN_EQUAL &&
           rule->u.appl.args[2]==_ex_true &&
           rule->u.appl.args[1]==_ex_false;
}

static int is_equation(struct _ex_intern *rule)
{
    return rule->u.appl.args[1] != _ex_true && rule->u.appl.args[1] != _ex_false &&
           rule->u.appl.args[2]==_ex_true;
}

static int is_inequality(struct _ex_intern *rule)
{
    return rule->u.appl.args[0]->type==EXP_APPL &&
           (rule->u.appl.args[0]->u.appl.functor==INTERN_NAT_LESS ||
            rule->u.appl.args[0]->u.appl.functor==INTERN_RAT_LESS) &&
           rule->u.appl.args[2]==_ex_true &&
           (rule->u.appl.args[1]==_ex_true ||
            rule->u.appl.args[1]==_ex_false);
}

void print_conditions(struct fail_list *f)
{
#ifndef FAST
    struct parent_list *a;

    while (f != NULL) {
        _tree_print_exp("exp", f->e);
        _tree_indent();
        a = f->conditions;
        _tree_print0("conditions");
        _tree_indent();
        while (a != NULL) {
            _tree_print_exp("cond", a->split);
            a = a->next;
        }
        _tree_undent();
        a = f->reduced_form;
        _tree_print0("reduced conditions");
        _tree_indent();
        _tree_print("Booleans");
        _tree_indent();
        while (a != NULL) {
            if (is_boolean(a->split)) {
                _tree_print_exp("cond", a->split);
            }
            a = a->next;
        }
        _tree_undent();
        _tree_print("Assignments");
        a = f->reduced_form;
        _tree_indent();
        while (a != NULL) {
            if (is_assignment(a->split)) {
                _tree_print_exp("cond", a->split);
            }
            a = a->next;
        }
        _tree_undent();
        _tree_print("Joins");
        a = f->reduced_form;
        _tree_indent();
        while (a != NULL) {
            if (is_join(a->split)) {
                _tree_print_exp("cond", a->split);
            }
            a = a->next;
        }
        _tree_undent();
        _tree_print("Disjoins");
        a = f->reduced_form;
        _tree_indent();
        while (a != NULL) {
            if (is_disjoin(a->split)) {
                _tree_print_exp("cond", a->split);
            }
            a = a->next;
        }
        _tree_undent();
        _tree_print("Equations");
        a = f->reduced_form;
        _tree_indent();
        while (a != NULL) {
            if (is_equation(a->split) && !is_assignment(a->split) && !is_join(a->split)) {
                _tree_print_exp("cond", a->split);
            }
            a = a->next;
        }
        _tree_undent();
        _tree_print("Inequalities");
        a = f->reduced_form;
        _tree_indent();
        while (a != NULL) {
            if (is_inequality(a->split)) {
                _tree_print_exp("cond", a->split);
            }
            a = a->next;
        }
        _tree_undent();
        _tree_print("Other");
        a = f->reduced_form;
        _tree_indent();
        while (a != NULL) {
            if (!is_boolean(a->split) && !is_assignment(a->split) && !is_equation(a->split) &&
                !is_inequality(a->split) && !is_join(a->split) && !is_disjoin(a->split)) {
                _tree_print_exp("cond", a->split);
            }
            a = a->next;
        }
        _tree_undent();
        _tree_undent();
        _tree_undent();
        f = f->next;
    }
#endif
}

int _th_svcs(struct env *env, char *file)
{
    struct _ex_intern *e;
    int ret;
    _th_derive_push(env);
    e = _th_process_svc_script(env, file);
    //e2 = _th_parse_smt();
    //e2 = e2->u.appl.args[0]->u.appl.args[0];
    //diff(e,e2,NULL);
    //exit(1);
    if (e != NULL) {
        struct fail_list *f;
        //printf("*** Initial: %s\n", _th_print_exp(e));
        //e = _th_nc_rewrite(env,e);
        //e = _th_bit_blast(env,e);
        //printf("*** bit_blast %s\n", _th_print_exp(e));
        f = _th_prove(env,e);
        if (f) {
            _tree_print0("Failed nodes");
            printf("INVALID\n");
        } else {
            _tree_print0("VALID proof");
            printf("VALID\n");
        }
        _tree_indent();
        print_conditions(f);
        _tree_undent();
        //printf("*** Rewrite: %s\n", _th_print_exp(_th_rewrite(env,e)));
        ret = 0;
    } else {
        printf("Illegal SVC script file\n");
        ret = 1;
    }
    _th_derive_pop(env);
    return ret;
}

int _th_smt(struct env *env, char *name, int print_failures)
{
    struct _ex_intern *e;
    int ret;
    _th_derive_push(env);
    e = _th_parse_smt(env,name);
    //_th_parse_yices_ce(env,fopen("yices.ce","r"));
    if (e != NULL) {
        struct fail_list *f;
        //printf("*** Initial: %s\n", _th_print_exp(e));
        //e = _th_nc_rewrite(env,e);
        //e = _th_bit_blast(env,e);
        //printf("*** bit_blast %s\n", _th_print_exp(e));
        //fprintf(stderr, "_th_smt: env = %x\n", env);
        f = _th_prove(env,e);
		if (f) {
			if (print_failures) {
				while (f) {
					struct parent_list *c = f->conditions;
					printf("Case\n");
					while (c) {
						printf("    %s\n", _th_print_exp(c->split));
						c = c->next;
					}
					f = f->next;
				}
			}
            _tree_print0("Failed nodes");
            if (_th_unknown) {
                printf("unknown\n");
#ifdef PRINT_CORRECTNESS
                //if (_th_get_status() != INTERN_UNKNOWN) printf("Should get answer!!!\n");
#endif
            } else {
                printf("sat\n");
#ifdef PRINT_CORRECTNESS
                if (_th_get_status() == INTERN_UNKNOWN) {
                    //printf("Warning: result not entered\n");
                } else if (_th_get_status() != INTERN_SAT) {
                    printf("WRONG!!!\n");
                }
#endif
            }
        } else {
            _tree_print0("VALID proof");
            printf("unsat\n");
#ifdef PRINT_CORRECTNESS
            if (_th_get_status() == INTERN_UNKNOWN) {
                //printf("Warning: result not entered\n");
            } else if (_th_get_status() != INTERN_UNSAT) {
                printf("WRONG!!!\n");
            }
#endif
        }
        _tree_indent();
        print_conditions(f);
        _tree_undent();
        //printf("*** Rewrite: %s\n", _th_print_exp(_th_rewrite(env,e)));
        ret = 0;
    } else {
        printf("Illegal SMT input\n");
        ret = 1;
    }
    _th_derive_pop(env);
    return ret;
}

int run_minisat(char *file)
{
    char command[200];
    FILE *f;

    sprintf(command, "MiniSat_v1.14_linux %s >& xx", file);
    system(command);

    f = fopen("xx", "r");
    while (!feof(f)) {
        command[0] = 0;
        fgets(command,199,f);
        command[strlen(command)-1] = 0;
        if (command[0]=='U' && command[1]=='N' && command[2]=='S') {
            fclose(f);
            return PREPROCESS_UNSAT;
        }
        if (command[0]=='S' && command[1]=='A' && command[2]=='T') {
            fclose(f);
            return PREPROCESS_SAT;
        }
    }
    return PREPROCESS_DEFAULT;
}

int run_yices(char *file)
{
    char command[200];
    FILE *f;

    sprintf(command, "yices %s >& xx", file);
    //printf("Before command '%s'\n", command);
    system(command);
    //printf("After command\n");

    f = fopen("xx", "r");
    while (!feof(f)) {
        command[0] = 0;
        fgets(command,199,f);
        command[strlen(command)-1] = 0;
        //printf("command: %s\n", command);
        if (command[0]=='u' && command[1]=='n' && command[2]=='s') {
            fclose(f);
            return PREPROCESS_UNSAT;
        }
        if (command[0]=='s' && command[1]=='a' && command[2]=='t') {
            fclose(f);
            return PREPROCESS_SAT;
        }
    }
    return PREPROCESS_DEFAULT;
}

int run_bclt(char *file)
{
    char command[200];
    FILE *f;

    sprintf(command, "bclt %s >& xx", file);
    //printf("Before command '%s'\n", command);
    system(command);
    //printf("After command\n");

    f = fopen("xx", "r");
    while (!feof(f)) {
        command[0] = 0;
        fgets(command,199,f);
        command[strlen(command)-1] = 0;
        //printf("command: %s\n", command);
        if (command[0]=='u' && command[1]=='n' && command[2]=='s') {
            fclose(f);
            return PREPROCESS_UNSAT;
        }
        if (command[0]=='s' && command[1]=='a' && command[2]=='t') {
            fclose(f);
            return PREPROCESS_SAT;
        }
        if (command[0]=='U' && command[1]=='N' && command[2]=='S') {
            fclose(f);
            return PREPROCESS_UNSAT;
        }
        if (command[0]=='S' && command[1]=='A' && command[2]=='T') {
            fclose(f);
            return PREPROCESS_SAT;
        }
    }
    return PREPROCESS_DEFAULT;
}

int _th_smt_autorun(struct env *env, char *name)
{
    struct _ex_intern *e;
    int ret;
    char *f, *d;
    char write_file[200], write_d_file[200];
    int state;
    _th_derive_push(env);

    e = _th_parse_smt(env,name);
    //_th_parse_yices_ce(env,fopen("yices.ce","r"));
    if (e != NULL) {
        //printf("*** Initial: %s\n", _th_print_exp(e));
        //e = _th_nc_rewrite(env,e);
        //e = _th_bit_blast(env,e);
        //printf("*** bit_blast %s\n", _th_print_exp(e));
        //fprintf(stderr, "_th_smt: env = %x\n", env);
        if (name==NULL) {
            f = NULL;
            d = NULL;
        } else {
            sprintf(write_file, "%s.out", name);
            f = write_file;
            sprintf(write_d_file, "%s.cnf", name);
            d = write_d_file;
        }
        if (_th_is_symmetry_logic()) {
            printf("Here1\n");
            _th_do_symmetry = 1;
        }
        state = _th_preprocess(env,e,f,d);
        //printf("state = %d\n", state);
        if (state==PREPROCESS_CNF) {
            state = run_minisat(write_d_file);
        } else if (state==PREPROCESS_DEFAULT) {
            if (_th_is_bclt_logic()) {
                state = run_bclt(write_file);
            } else {
                state = run_yices(write_file);
            }
        }
        if (state==PREPROCESS_SAT) {
            _tree_print0("Invalid proof");
            printf("sat\n");
#ifdef PRINT_CORRECTNESS
            if (_th_get_status() == INTERN_UNKNOWN) {
                //printf("Warning: result not entered\n");
            } else if (_th_get_status() != INTERN_SAT) {
                printf("WRONG!!!\n");
            }
#endif
        } else if (state==PREPROCESS_UNSAT) {
            _tree_print0("VALID proof");
            printf("unsat\n");
#ifdef PRINT_CORRECTNESS
            if (_th_get_status() == INTERN_UNKNOWN) {
                //printf("Warning: result not entered\n");
            } else if (_th_get_status() != INTERN_UNSAT) {
                printf("WRONG!!!\n");
            }
#endif
        } else if (state==PREPROCESS_NORUN) {
            _tree_print0("norun");
            printf("unknown\n");
            printf("*** NO RUN ***\n");
        } else {
            _tree_print0("unknown: subordinate process failure");
            printf("unknown\n");
        }
        ret = 0;
    } else {
        printf("Illegal SMT input\n");
        ret = 1;
    }
    _th_derive_pop(env);
    return ret;
}

int _th_preprocess_smt(struct env *env, char *name)
{
    struct _ex_intern *e;
    char *f, *d;
    char write_file[200], write_d_file[200];
    int ret;
    _th_derive_push(env);

    e = _th_parse_smt(env,name);

    //_th_parse_yices_ce(env,fopen("yices.ce","r"));
    if (e != NULL) {
        //printf("*** Initial: %s\n", _th_print_exp(e));
        //e = _th_nc_rewrite(env,e);
        //e = _th_bit_blast(env,e);
        //printf("*** bit_blast %s\n", _th_print_exp(e));
        //fprintf(stderr, "_th_smt: env = %x\n", env);
        if (name==NULL) {
            f = NULL;
            d = NULL;
        } else {
            sprintf(write_file, "%s.out", name);
            f = write_file;
            sprintf(write_d_file, "%s.cnf", name);
            d = write_d_file;
        }
        _th_preprocess(env,e,f,d);
        ret = 0;
    } else {
        printf("Illegal SMT input\n");
        ret = 1;
    }
    _th_derive_pop(env);
    return ret;
}

static void print_difference(struct _ex_intern *e, struct _ex_intern *r)
{
    int i;

    if (e->type != EXP_APPL || r->type != EXP_APPL) {
        printf("e = %s\n", _th_print_exp(e));
        printf("r = %s\n", _th_print_exp(r));
        return ;
    }

    if (e->u.appl.functor != r->u.appl.functor || e->u.appl.count != r->u.appl.count) {
        printf("e = %s\n", _th_print_exp(e));
        printf("r = %s\n", _th_print_exp(r));
        return ;
    }

    for (i = 0; i < e->u.appl.count; ++i) {
        if (e->u.appl.args[i] != r->u.appl.args[i]) {
            print_difference(e->u.appl.args[i],r->u.appl.args[i]);
        }
    }
}

int _th_print_smt(struct env *env, char *name)
{
    struct _ex_intern *e;
    FILE *f;
    char write_file[200];
    int ret;
    _th_derive_push(env);
    e = _th_parse_smt(env,name);
    if (e != NULL) {
        //struct _ex_intern *nenv = _th_default_env(ENVIRONMENT_SPACE);
        if (name==NULL) {
            f = stdout;
        } else {
            sprintf(write_file, "%s.out", name);
            f = fopen(write_file,"w");
        }
        _th_print_state(env,NULL,NULL,e->u.appl.args[0],f,_th_get_name(),_th_get_status_name(),_th_get_logic_name());
        fclose(f);
        //r = _th_parse_smt(nenv,write_file);
        //r = r->u.appl.args[0];
        //if (e != r) {
        //    fprintf(stderr, "Different\n");
        //    print_difference(e,r);
        //    exit(1);
        //}
        ret = 0;
    } else {
        printf("Illegal SMT input\n");
        ret = 1;
    }
    _th_derive_pop(env);
    return ret;
}

struct env *_th_process_file(struct env *env, char *file_name, FILE *f)
{
    char line[2001] ;
    struct _ex_intern *pat = NULL ;
    int x ;
    int row = 0 ;
    int i, j ;
    int in_function = 0 ;
    struct _ex_intern *function_pat, *function_type, *function_pre ;
    
    while (!feof(f)) {
        struct _ex_intern *e ;
        fgets(line, 2000, f) ;
        ++row ;
        x = strlen(line) - 1 ;
        while(line[x]<32 && x >= 0) line[x--] = 0 ;
        printf("Processing '%s'\n", line);
        
cont:
        if (line[0]==0 || line[0]=='#')  {
        } else if (in_function) {
            if (!strncmp(line,"type",4)) {
                function_type = _th_pp_parse(file_name, env, line+4) ;
            } else if (!strncmp(line,"precondition",11)) {
                function_pre = _th_pp_parse(file_name, env, line+11) ;
            } else {
                in_function = 0 ;
                _th_add_function(env,function_pat,function_type,function_pre,0,0) ;
                goto cont ;
            }
        } else if (!strncmp(line,"ac",2)) {
            char *c = line+2;
            struct parameter parameters[5] ;
            while (*c==' ') ++c;
            parameters[0].type = SYMBOL_PARAMETER ;
            parameters[0].u.symbol = _th_intern(c) ;
            printf("*AC* '%s'\n", c);
            _th_add_attrib(env,INTERN_AC,1,parameters) ;
        } else if (!strncmp(line,"c",1)) {
            char *c = line+1;
            struct parameter parameters[5] ;
            while (*c==' ') ++c;
            parameters[0].type = SYMBOL_PARAMETER ;
            parameters[0].u.symbol = _th_intern(c) ;
            printf("*C* '%s'\n", c);
            _th_add_attrib(env,INTERN_C,1,parameters) ;
        } else if (!strncmp(line,"function",8)) {
            in_function = 1 ;
            function_type = function_pre = NULL ;
            function_pat = _th_pp_parse(file_name, env, line+8) ;
        } else if (!strncmp(line,"pattern",7)) {
            e = _th_parse(env, line+7) ;
            if (e==NULL) {
                _tree_print0("Illegal expression") ;
            } else {
                pat = e ;
            }
        } else if (!strncmp(line,"normalize",9)) {
            if (pat != NULL) {
                e = _th_parse(env, line + 9) ;
                if (e==NULL) {
                    _tree_print1("Illegal expression at %d", row) ;
                } else {
                    //if (f==stdin) _tree_print("%s", _th_print_exp(_th_normalize(env, pat, e))) ;
                }
            } else {
                _tree_print0("No pattern entered") ;
            }
        } else if (!strncmp(line,"load",4)) {
            FILE *file = fopen(line+5,"r") ;
            if (file==NULL) {
                _tree_print1("Illegal file at line %d", row) ;
            } else {
                env = _th_process_file(env, line+5, file) ;
            }
        } else if (!strncmp(line,"pp",2)) {
            struct directive *d = _th_get_pp_directives(env) ;
            d = _th_tokenize_line(ENVIRONMENT_SPACE,line+2,d) ;
            if (d==NULL) {
                _tree_print1("Illegal directive at %d", row) ;
            } else {
                _th_set_pp_directives(env,d) ;
            }
        } else if (!strncmp(line,"type",4)) {
            char *c ;
            struct _ex_intern *l, *r ;
            c = line + 4 ;
            while (*c && *c !='=') ++c ;
            if (*c) {
                *c = 0;
                ++c ;
            }
            l = _th_pp_parse(file_name,env,line+4) ;
            r = _th_flatten_top(env,_th_pp_parse(file_name,env,c)) ;
            /*printf("c = '%s'\n",c) ;
            printf("line+4 = '%s'\n",line+4) ;*/
            if (l==NULL || r==NULL) {
                _tree_print2("Illegal type: \"%s\" at %d\n", line, row) ;
            } else {
            /*printf("type %s ", _th_print_exp(l)) ;
                _treeprint(" = %s\n", _th_print_exp(r)) ;*/
                _th_add_type_definition(env,l,r) ;
            }
        } else if (!strncmp(line,"eval",4)) {
            e = _th_parse(env, line + 4) ;
            if (e != NULL) {
                e = _th_rewrite(env, e) ;
                if (f==stdin) printf("%s\n", _th_print_exp(e)) ;
            } else {
                _tree_print2("Illegal expression, \"%s\" at %d\n", line, row) ;
            }
        } else if (!strncmp(line, "parse", 5)) {
            e = _th_pp_parse(file_name, env, line+5) ;
            _tree_print_exp("result", e);
            for (i = 0; i < _th_index_count; ++i) {
                _tree_print5("    start: %d %d end: %d %d (file %s)\n       ",
                    _th_index[i][0],
                    _th_index[i][1],
                    _th_index[i][2],
                    _th_index[i][3],
                    _th_intern_decode(_th_index[i][4])) ;
                for (j = 0; j < _th_index[i][5]; ++j) {
                    _tree_print1(" %d", _th_index[i][j+6]) ;
                }
                _tree_print0("\n") ;
            }
        } else if (!strncmp(line, "match", 5)) {
            fgets(line, 2000, f) ;
            x = strlen(line) - 1 ;
            while(line[x]<32 && x >= 0) line[x--] = 0 ;
            e = _th_parse(env, line) ;
            fgets(line, 2000, f) ;
            x = strlen(line) - 1 ;
            while(line[x]<32 && x >= 0) line[x--] = 0 ;
            pat = _th_parse(env, line) ;
            printf("*** MATCHING ***\n") ;
            if (e==NULL || pat==NULL) {
                printf("Bad args %d %d\n", e, pat) ;
            } else {
                struct match_return *mr ;
                printf("result %d\n", mr = _th_match(env, e, pat)) ;
                while (mr != NULL) {
                    printf("UNIFIER:\n") ;
                    _th_print_unifier(mr->theta) ;
                    mr = mr->next ;
                }
            }
        } else if (!strncmp(line,"prec ",5)) {
            int count = _th_tokenize_string(line+4,"") ;
            if (count != 2) {
                _tree_print0("Illegal precedence") ;
            } else {
                _th_add_precedence(ENVIRONMENT_SPACE, env, _th_tokens[0], _th_tokens[1]) ;
            }
        } else if (!strncmp(line,"maxprec ",8)) {
            unsigned count = _th_tokenize_string(line+7,"") ;
            if (count != 1) {
                _tree_print0("Illegal precedence") ;
            } else {
                _th_add_max_precedence(ENVIRONMENT_SPACE, env, _th_tokens[0]) ;
            }
        } else if (!strncmp(line,"lex ",4)) {
            int count = _th_tokenize_string(line+3,"") ;
            if (count < 2) {
                _tree_print0("Illegal lex") ;
            } else {
                unsigned *lex = (unsigned *)ALLOCA(sizeof(unsigned) * (count-1)) ;
                int i ;
                for (i = 1; i < count; ++i) {
                    char *s = _th_intern_decode(_th_tokens[i]) ;
                    if (!isdigit(*s)) {
                        _tree_print0("Illegal lex") ;
                        break ;
                    }
                    lex[i-1] = atoi(s) ;
                }
                if (i==count) _th_add_lex_info(ENVIRONMENT_SPACE, env, _th_tokens[0], count-1, lex) ;
            }
		} else if (!strncmp(line,"svc ", 4)) {
			_th_derive_push(env);
			e = _th_process_svc_file(env, line+4);
			if (e != NULL) {
                struct fail_list *f;
				struct parent_list *a;
			    printf("*** Initial: %s\n", _th_print_exp(e));
				//e = _th_nc_rewrite(env,e);
				//e = _th_bit_blast(env,e);
				//printf("*** bit_blast %s\n", _th_print_exp(e));
				f = _th_prove(env,e);
                if (f) {
                    printf("INVALID\n");
                    _tree_print0("Failed nodes");
                } else {
                    printf("VALID\n");
                    _tree_print0("VALID proof");
                }
                _tree_indent();
				while (f != NULL) {
                    _tree_print_exp("exp", f->e);
                    _tree_indent();
                    a = f->conditions;
                    _tree_print0("conditions");
                    _tree_indent();
                    while (a != NULL) {
                        _tree_print_exp("cond", a->split);
                        a = a->next;
                    }
                    _tree_undent();
                    a = f->reduced_form;
                    _tree_print0("reduced conditions");
                    _tree_indent();
                    while (a != NULL) {
                        _tree_print_exp("cond", a->split);
                        a = a->next;
                    }
                    _tree_undent();
                    _tree_undent();
					f = f->next;
				}
                _tree_undent();
			    //printf("*** Rewrite: %s\n", _th_print_exp(_th_rewrite(env,e)));
			} else {
				printf("Illegal SVC file\n");
			}
			_th_derive_pop(env);
		} else if (!strncmp(line,"svcs ", 5)) {
            _th_svcs(env,line+5);
        } else if (strncmp(line, "quit", 4)) {
            e = _th_pp_parse(file_name, env, line) ;
            //printf("Processing property %s\n", _th_print_exp(e)) ;
            if (e != NULL) {
                if (e->type == EXP_APPL && e->u.appl.count == 1 &&
                    e->u.appl.functor == INTERN_QUOTE) {

                    _th_add_property(env,e->u.appl.args[0]) ;
                } else if (e->type == EXP_APPL && e->u.appl.count == 3 &&
                    (e->u.appl.functor == INTERN_ORIENTED_RULE ||
                    e->u.appl.functor == INTERN_DOUBLE_ARROW ||
                    e->u.appl.functor == INTERN_FORCE_ORIENTED ||
                    e->u.appl.functor == INTERN_INFERENCE ||
                    e->u.appl.functor == INTERN_MACRO_ARROW ||
                    e->u.appl.functor == INTERN_UNORIENTED_RULE)) {
                    _th_check(env,_ex_bool,e) ;
                    _th_derive_and_add_property(ENVIRONMENT_SPACE,env,e) ;
                } else if (e->type == EXP_APPL && e->u.appl.count == 2 &&
                    e->u.appl.functor == INTERN_PRIORITY &&
                    e->u.appl.args[0]->type == EXP_INTEGER) {
                    _th_derive_and_add_property(ENVIRONMENT_SPACE,env,e) ;
                } else if (e->type == EXP_APPL && e->u.appl.count == 4 &&
                    e->u.appl.functor == INTERN_HEURISTIC) {
                    _th_derive_and_add_property(ENVIRONMENT_SPACE,env,e) ;
                } else {
                    e = _th_rewrite(env, e) ;
                    if (f==stdin) {
                        _tree_print_exp("", e);
                    } else {
                        _tree_print2("Error: Illegal property: \"%s\" at %d", line, row) ;
                    }
                }
            } else {
                _tree_print2("Error: Illegal property: \"%s\" at %d", line, row) ;
            }
        } else {
            break ;
        }
        }
        
        if (in_function) {
            _th_add_function(env,function_pat,function_type,function_pre,0,0) ;
        }
        
        return env ;
}

char _th_source_buffer[400000] ;

void _th_read_file(FILE *f)
{
	char *l ;
	l = _th_source_buffer ;

	while(!feof(f)) {
		l[0] = 0 ;
		fgets(l, 1000, f) ;
		l += strlen(l) ;
	}
}

