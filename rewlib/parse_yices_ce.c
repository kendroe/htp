/*
 * parse_yices_ce.c
 *
 * Routines for parsing a Yices counter example.  This is being used to
 * debug HTP.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include "Globals.h"
#include "Intern.h"

struct ce_list {
    struct ce_list *next;
    struct _ex_intern *e;
    char *text;
    struct _ex_intern *assignment;
    int invert;
    int index;
};

#define CE_HASH_SIZE 511

struct ce_list *ce_table[CE_HASH_SIZE];

#ifdef XX
void print_smt_model(struct env *env)
{
    int i;
    struct ce_list *n;
    FILE *f;

    f = fopen("d.smt", "w");
    for (i = 0; i < CE_HASH_SIZE; ++i) {
        n = ce_table[i];
        while (n) {
            if (n->assignment==_ex_true) {
                print_as_smt(f,env,n->e);
            } else {
                print_as_smt(f,env,_ex_intern_appl1_env(env,INTERN_NOT,n->e));
            }
            n = n->next;
        }
    }
    fclose(f);
    exit(1);
}
#endif

struct _ex_intern *convert_rat(struct env *env, struct _ex_intern *e)
{
    unsigned one[2] = { 1, 1 };
    int i;
    struct _ex_intern **args, *r;

    switch (e->type) {
        case EXP_INTEGER:
            return _ex_intern_rational(e->u.integer,one);
        case EXP_APPL:
            switch (e->u.appl.functor) {
                case INTERN_MINUS:
                    return _ex_intern_appl2_env(env,INTERN_RAT_MINUS,convert_rat(env,e->u.appl.args[0]),convert_rat(env,e->u.appl.args[1]));
                case INTERN_PLUS:
                    return _ex_intern_appl2_env(env,INTERN_RAT_PLUS,convert_rat(env,e->u.appl.args[0]),convert_rat(env,e->u.appl.args[1]));
                case INTERN_STAR:
                    return _ex_intern_appl2_env(env,INTERN_RAT_TIMES,convert_rat(env,e->u.appl.args[0]),convert_rat(env,e->u.appl.args[1]));
                case INTERN_LESS:
                    return _ex_intern_appl2_env(env,INTERN_RAT_LESS,convert_rat(env,e->u.appl.args[0]),convert_rat(env,e->u.appl.args[1]));
                case INTERN_GREATER:
                    return _ex_intern_appl2_env(env,INTERN_RAT_LESS,convert_rat(env,e->u.appl.args[1]),convert_rat(env,e->u.appl.args[0]));
                case INTERN_LESS_EQUAL:
                    return _ex_intern_appl1_env(env,INTERN_NOT,
                               _ex_intern_appl2_env(env,INTERN_RAT_LESS,
                                   convert_rat(env,e->u.appl.args[1]),
                                   convert_rat(env,e->u.appl.args[0])));
                case INTERN_GREATER_EQUAL:
                    return _ex_intern_appl1_env(env,INTERN_NOT,
                               _ex_intern_appl2_env(env,INTERN_RAT_LESS,
                                   convert_rat(env,e->u.appl.args[0]),
                                   convert_rat(env,e->u.appl.args[1])));
                case INTERN_UNORIENTED_RULE:
                    r = _ex_intern_equal(env,_ex_real,convert_rat(env,e->u.appl.args[0]),convert_rat(env,e->u.appl.args[1]));
                    return r;
                default:
                    args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
                    for (i = 0; i < e->u.appl.count; ++i) {
                        args[i] = convert_rat(env,e->u.appl.args[i]);
                    }
                    return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
            }
        default:
            return e;
    }
}

static int case_parsed = 0;

static int has_app(struct _ex_intern *e)
{
    int i;
    char *s;

    switch (e->type) {
        case EXP_VAR:
            s = _th_intern_decode(e->u.var);
            while (*s) {
                if (*s=='!') return 1;
                ++s;
            }
            return 0;
        case EXP_APPL:
            for (i = 0; i < e->u.appl.count; ++i) {
                if (has_app(e->u.appl.args[i])) return 1;
            }
            return 0;
    }

    return 0;
}

static struct _ex_intern *find_term(int v)
{
    int i;

    for (i = 0; i < CE_HASH_SIZE; ++i) {
        struct ce_list *n = ce_table[i];
        while (n) {
            if (n->index==v) return n->e;
            n = n->next;
        }
    }
    return NULL;
}

static struct _ex_intern *sub_apps(struct env *env, struct _ex_intern *e)
{
    struct _ex_intern **args;
    int i;
    char *s;

    switch (e->type) {
        case EXP_APPL:
            args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
            for (i = 0; i < e->u.appl.count; ++i) {
                args[i] = sub_apps(env,e->u.appl.args[i]);
            }
            return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
        case EXP_VAR:
            s = _th_intern_decode(e->u.var);
            while (*s) {
                if (*s=='!') {
                    ++s;
                    return find_term(atoi(s));
                }
                ++s;
            }
        default:
            return e;
    }
}

static void do_all_subs(struct env *env)
{
    int i;
    int change;
    
    do {
        change = 0;
        for (i = 0; i < CE_HASH_SIZE; ++i) {
            struct ce_list *n = ce_table[i];
            while (n) {
                if (has_app(n->e)) {
                    n->e = sub_apps(env,n->e);
                    change = 1;
                }
                n = n->next;
            }
        }
    } while (change);

    for (i = 0; i < CE_HASH_SIZE; ++i) {
        struct ce_list *n = ce_table[i];
        while (n) {
            printf("!%d = %s ", n->index, _th_print_exp(n->e));
            printf("(assigned %s)\n", _th_print_exp(n->assignment));
            n = n->next;
        }
    }
}

void _th_parse_yices_ce(struct env *env, FILE *file)
{
    char line[20000], name[10];
    int i;
    struct _ex_intern *e;
    struct ce_list *n;
    int hash;

    case_parsed = 1;

    if (file==NULL) {
        fprintf(stderr, "Error opening yices counter example\n");
        exit(1);
    }

    for (i = 0; i < CE_HASH_SIZE; ++i){
        ce_table[i] = NULL;
    }

    while (!feof(file)) {
        line[0] = 0;
        fgets(line,19998,file);
        _tree_print1("Processing %s", line);
        _tree_indent();
        if (line[0]=='x' && line[1]=='_') {
            char *c = line+2;
            int x = atoi(line+2);
            sprintf(name, "x_%d", x);
            e = _th_parse(env,name);
            hash = (((int)e)/4)%CE_HASH_SIZE;
            n = (struct ce_list *)malloc(sizeof(struct ce_list));
            n->text = strdup(name);
            n->next = ce_table[hash];
            ce_table[hash] = n;
            n->e = _th_int_rewrite(env,e,0);
            //printf("Adding %d %s\n", -1-x, _th_print_exp(n->e));
            n->index = -1-x;
            n->assignment = NULL;
            n->invert = 0;
            while (*c && *c != ' ') {
                ++c;
            }
            while (*c==' ') ++c;
            if (!strncmp(c,"= true",6)) {
                n->assignment = _ex_true;
            } else if (!strncmp(c,"= false",7)) {
                n->assignment = _ex_false;
            }
            //printf("Assigning %s", _th_print_exp(n->e));
            printf(" the value %s\n", _th_print_exp(n->assignment));
        } else if ((line[0]=='b' || line[0]=='x') && isdigit(line[1])) {
            char *c = line+2;
            int x = atoi(line+1);
            sprintf(name, "%c%d", line[0], x);
            e = _th_parse(env,name);
            hash = (((int)e)/4)%CE_HASH_SIZE;
            n = (struct ce_list *)malloc(sizeof(struct ce_list));
            n->text = strdup(name);
            n->next = ce_table[hash];
            ce_table[hash] = n;
            n->e = _th_int_rewrite(env,e,0);
            //printf("Adding %d %s\n", -1-x, _th_print_exp(n->e));
            n->index = -1-x;
            n->assignment = NULL;
            n->invert = 0;
            while (*c && *c != ' ') {
                ++c;
            }
            while (*c==' ') ++c;
            if (!strncmp(c,"= true",6)) {
                n->assignment = _ex_true;
            } else if (!strncmp(c,"= false",7)) {
                n->assignment = _ex_false;
            }
            //printf("Assigning %s", _th_print_exp(n->e));
            //printf(" the value %s\n", _th_print_exp(n->assignment));
        } else if ((line[0]=='l' && line[1]=='a' && line[2]=='p' && line[3]=='!') ||
                   (line[0]=='i' && line[1]=='t' && line[2]=='e' && line[3]=='!') ||
                   (line[0]=='i' && line[1]=='f' && line[2]=='f' && line[3]=='!')) {
            int x = atoi(line+4);
            char *c = line+4;
            while (*c != ' ' && *c) ++c;
            while (*c==' ') ++c;
            if (*c==':' && *(c+1)=='=') {
                c += 2;
                while (*c==' ') ++c;
                e = convert_rat(env,_th_parse(env,c));
                hash = (((int)e)/4)%CE_HASH_SIZE;
                n = (struct ce_list *)malloc(sizeof(struct ce_list));
                n->text = strdup(c);
                n->next = ce_table[hash];
                ce_table[hash] = n;
                n->e = _th_int_rewrite(env,e,0);
                //printf("Adding %d %s\n", x, _th_print_exp(n->e));
                n->index = x;
                n->assignment = NULL;
                if (n->e->type==EXP_APPL && n->e->u.appl.functor==INTERN_NOT) {
                    n->e = n->e->u.appl.args[0];
                    n->invert = 1;
                } else {
                    n->invert = 0;
                }
            } else if (!strncmp(c,"= true",6)) {
                for (i = 0; i < CE_HASH_SIZE; ++i) {
                    n = ce_table[i];
                    while (n) {
                        if (n->index==x) {
                            printf("Making true %d %s\n", x, _th_print_exp(n->e));
                            if (n->invert) {
                                n->assignment = _ex_false;
                            } else {
                                n->assignment = _ex_true;
                            }
                            goto cont;
                        }
                        n = n->next;
                    }
                }
            } else if (!strncmp(c,"= false",7)) {
                for (i = 0; i < CE_HASH_SIZE; ++i) {
                    n = ce_table[i];
                    while (n) {
                        if (n->index==x) {
                            printf("Making false %d %s\n", x, _th_print_exp(n->e));
                            if (n->invert) {
                                n->assignment = _ex_true;
                            } else {
                                n->assignment = _ex_false;
                            }
                            goto cont;
                        }
                        n = n->next;
                    }
                }
            }
        } else if (line[0]=='a' && line[1]=='p' && line[2]=='p' && line[3]=='!') {
            int x = atoi(line+4);
            char *c = line+4;
            while (*c != ' ' && *c) ++c;
            while (*c==' ') ++c;
            if (*c==':' && *(c+1)=='=') {
                c += 2;
                while (*c==' ') ++c;
                e = convert_rat(env,_th_parse(env,c));
                hash = (((int)e)/4)%CE_HASH_SIZE;
                n = (struct ce_list *)malloc(sizeof(struct ce_list));
                n->text = strdup(c);
                n->next = ce_table[hash];
                ce_table[hash] = n;
                n->e = _th_int_rewrite(env,e,0);
                //printf("Adding %d %s\n", x, _th_print_exp(n->e));
                n->index = x;
                n->assignment = NULL;
                if (n->e->type==EXP_APPL && n->e->u.appl.functor==INTERN_NOT) {
                    n->e = n->e->u.appl.args[0];
                    n->invert = 1;
                } else {
                    n->invert = 0;
                }
            }
        } else if ((line[0]=='e' && line[1]=='q' && line[2]=='!') ||
                   (line[0]=='s' && line[1]=='l' && line[2]=='!') ||
                   (line[0]=='o' && line[1]=='r' && line[2]=='!')) {
            int x = atoi(line+3);
            char *c = line+3;
            while (*c != ' ' && *c) ++c;
            while (*c==' ') ++c;
            if (*c==':' && *(c+1)=='=') {
                c += 2;
                while (*c==' ') ++c;
                e = convert_rat(env,_th_parse(env,c));
                hash = (((int)e)/4)%CE_HASH_SIZE;
                n = (struct ce_list *)malloc(sizeof(struct ce_list));
                n->text = strdup(c);
                n->next = ce_table[hash];
                ce_table[hash] = n;
                n->e = _th_int_rewrite(env,e,0);
                //printf("Adding %d %s\n", x, _th_print_exp(n->e));
                n->index = x;
                n->assignment = NULL;
                if (n->e->type==EXP_APPL && n->e->u.appl.functor==INTERN_NOT) {
                    n->e = n->e->u.appl.args[0];
                    n->invert = 1;
                } else {
                    n->invert = 0;
                }
            } else if (!strncmp(c,"= true",6)) {
                for (i = 0; i < CE_HASH_SIZE; ++i) {
                    n = ce_table[i];
                    while (n) {
                        if (n->index==x) {
                            printf("Making true %d %s\n", x, _th_print_exp(n->e));
                            if (n->invert) {
                                n->assignment = _ex_false;
                            } else {
                                n->assignment = _ex_true;
                            }
                            goto cont;
                        }
                        n = n->next;
                    }
                }
            } else if (!strncmp(c,"= false",7)) {
                for (i = 0; i < CE_HASH_SIZE; ++i) {
                    n = ce_table[i];
                    while (n) {
                        if (n->index==x) {
                            printf("Making false %d %s\n", x, _th_print_exp(n->e));
                            if (n->invert) {
                                n->assignment = _ex_true;
                            } else {
                                n->assignment = _ex_false;
                            }
                            goto cont;
                        }
                        n = n->next;
                    }
                }
            }
        }
cont:
        _tree_undent();
    }

    do_all_subs(env);
}

void _th_parse_ce(struct env *env, FILE *file)
{
    char line[20000], name[10];
    int i;
    struct _ex_intern *e;
    struct ce_list *n;
    int hash;

    case_parsed = 1;

    if (file==NULL) {
        fprintf(stderr, "Error opening yices counter example\n");
        exit(1);
    }

    for (i = 0; i < CE_HASH_SIZE; ++i){
        ce_table[i] = NULL;
    }

    while (!feof(file)) {
		struct _ex_intern *t, *var, *val;
        line[0] = 0;
        fgets(line,19998,file);
        _tree_print1("Processing %s", line);
        t = _th_parse(env,line);
        printf("t = %s\n", _th_print_exp(t));
		if (t) {
			unsigned one[2] = { 1, 1 };
			if (t->u.appl.args[0]->type==EXP_VAR) {
				var = t->u.appl.args[0];
				val = t->u.appl.args[1];
			} else {
				var - t->u.appl.args[1];
				val = t->u.appl.args[0];
			}
			if (val->type==EXP_INTEGER) {
				val = _ex_intern_rational(val->u.integer,one);
			}
			hash = (((int)var)/4)%CE_HASH_SIZE;
			n = (struct ce_list *)malloc(sizeof(struct ce_list));
			n->text = strdup(line);
			n->next = ce_table[hash];
			ce_table[hash] = n;
			n->e = var;
			n->assignment = val;
		}
    }
	printf("Finished\n");
}

static struct env *env;

void _th_build_yices_env()
{
    int i;

    env = _th_default_env(MATCH_SPACE);
    _th_initialize_difference_table(env);

    _tree_print0("Phase 1");
    _tree_indent();
    for (i = 0; i < CE_HASH_SIZE; ++i) {
        struct ce_list *n = ce_table[i];
        while (n) {
            struct _ex_intern *e;
            _tree_print_exp("Processing", n->e);
            if (n->assignment != _ex_true) _tree_print_exp("assignment", n->assignment);
            _tree_indent();
            if (n->assignment==_ex_true) {
                e = n->e;
            } else {
                e = _ex_intern_appl1_env(env,INTERN_NOT,n->e);
            }
            if (e->type==EXP_APPL && e->u.appl.functor==INTERN_EQUAL) {
                _th_assert_predicate(env,_th_simp(env,e));
            } else if (e->type==EXP_VAR) {
                _th_assert_predicate(env,_th_simp(env,e));
            } else if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT && e->u.appl.args[0]->type==EXP_VAR) {
                _th_assert_predicate(env,_th_simp(env,e));
            }
            _tree_undent();
            n = n->next;
        }
    }
    _tree_undent();

    _tree_print0("Phase 2");
    _tree_indent();
    for (i = 0; i < CE_HASH_SIZE; ++i) {
        struct ce_list *n = ce_table[i];
        while (n) {
            struct _ex_intern *s = _th_simp(env,n->e);

            _zone_print1("pos %d", n->index);
            if (s != n->e) {
                struct ce_list *m = (struct ce_list *)malloc(sizeof(struct ce_list));
                int hash;

                m->text = n->text;
                m->assignment = n->assignment;
                m->e = s;
                m->text = n->text;

                if ((s==_ex_true || s==_ex_false) && m->assignment != s) {
                    fprintf(stderr, "Yices contradiction %s\n", _th_print_exp(m->e));
                    exit(1);
                }
                hash = (((int)s)/4)%CE_HASH_SIZE;
                m->next = ce_table[hash];
                ce_table[hash] = m;
            }

            n = n->next;
        }
    }
    _tree_undent();
}

struct _ex_intern *vexp(struct env *env, struct _ex_intern *e)
{
	struct _ex_intern **args;
	int i;

	if (e->user2) return e->user2;

    if (e->type != EXP_APPL) return e;

	args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
	for (i = 0; i < e->u.appl.count; ++i) {
		args[i] = vexp(env,e->u.appl.args[i]);
	}

	return _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args);
}

struct _ex_intern *yices_ce_value(struct env *env, struct _ex_intern *e)
{
	int i;
    struct ce_list *n;
    struct _ex_intern *r;

	for (i = 0; i < CE_HASH_SIZE; ++i) {
		n = ce_table[i];
		while (n) {
			n->e->user2 = n->assignment;
			n = n->next;
		}
	}

	r = vexp(env,e);
    //printf("e = %s\n", _th_print_exp(e));
	//printf("r = %s\n", _th_print_exp(r));
    //printf("res = %s\n", _th_print_exp(_th_int_rewrite(env,r,0)));
	for (i = 0; i < CE_HASH_SIZE; ++i) {
		n = ce_table[i];
		while (n) {
			n->e->user2 = NULL;
			n = n->next;
		}
	}

	return _th_int_rewrite(env,r,0);
#ifdef XX
	int hash;
    struct ce_list *n;

    _tree_print_exp("yices ce value", e);
    _tree_indent();

    if (e->type==EXP_APPL && (e->u.appl.functor==INTERN_AND || e->u.appl.functor==INTERN_OR || e->u.appl.functor==INTERN_NOT || e->u.appl.functor==INTERN_ITE)) {
        struct _ex_intern **args = (struct _ex_intern **)ALLOCA(sizeof(struct _ex_intern *) * e->u.appl.count);
        struct _ex_intern *b;
        int i;
        for (i = 0; i < e->u.appl.count; ++i) {
            args[i] = yices_ce_value(e->u.appl.args[i]);
        }
        e = _th_nc_rewrite(env,b = _ex_intern_appl_env(env,e->u.appl.functor,e->u.appl.count,args));
        _tree_print_exp("before", b);
        _tree_undent();
        _tree_print_exp("is", e);
        return e;
    }

    e = _th_simp(env,e);

    //printf("Split = %s\n", _th_print_exp(p->split));
    hash = (((int)e)/4)%CE_HASH_SIZE;
    n = ce_table[hash];
    while (n && n->e != e) {
        n = n->next;
    }

    if (n==NULL) {
        _tree_undent();
        _tree_print_exp("is 2", e);
        return e;
    }

    _tree_print_exp("exp", e);
    _tree_undent();
    _tree_print_exp("is 3", n->assignment);
    return n->assignment;
#endif
}

#ifdef XX
struct _ex_intern *_th_yices_ce_value(struct env *penv, struct _ex_intern *e)
{
    struct _ex_intern *res;
    static int in_yices_ce = 0;

    if (in_yices_ce) return NULL;

    in_yices_ce = 1;

    _th_remove_cache(penv);
    if (case_parsed) {
        _th_install_cache(env);
    } else {
        _tree_print("Initializing");
        _tree_indent();
        _th_parse_ce(penv,fopen("yices.ce","r"));
        _tree_undent();
        _tree_print("Building environment");
        _tree_indent();
        //_th_build_yices_env(penv);
        _tree_undent();
    }

    res = yices_ce_value(e);

    _th_remove_cache(env);
    _th_install_cache(penv);

    in_yices_ce = 0;

    return res;
}
#endif

int _th_matches_yices_ce(struct env *env, struct parent_list *p, struct _ex_intern *e)
{
	if (!case_parsed) {
        _tree_print0("Initializing");
        _tree_indent();
        _th_parse_ce(env,fopen("yices.ce","r"));
        _tree_undent();
		_tree_print0("Building environment");
        _tree_indent();
        //_th_build_yices_env(penv);
        _tree_undent();
	}

    while (p) {
		if (yices_ce_value(env,p->split)!=_ex_true) return 0;
		p = p->next;
    }

	if (e && yices_ce_value(env,e)!=_ex_true) return 0;

    return 1;
}
