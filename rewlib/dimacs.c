/*
 * dimacs.c
 *
 * Routines for printing problems in dimacs format
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <string.h>
#include "Globals.h"
#include "Intern.h"

int _th_is_sat(struct learn_info *info)
{
    struct _ex_intern *t, *e;
    int i;

    t = _th_get_first_neg_tuple(info);
    while (t) {
        if (t->type==EXP_APPL && t->u.appl.functor==INTERN_OR) {
            for (i = 0; i < t->u.appl.count; ++i) {
                e = t->u.appl.args[i];
                if (e->type != EXP_VAR && (e->type != EXP_APPL || e->u.appl.functor != INTERN_NOT || e->u.appl.args[0]->u.var==EXP_VAR)) {
                    //printf("Violation %s\n", _th_print_exp(e));
                    return 0;
                }
            }
        } else {
            return 0;
        }
        t = _th_get_next_neg_tuple(info);
    }

    return 1;
}

struct _ex_intern *trail = NULL;

void _th_print_dimacs(struct learn_info *info, FILE *file)
{
    struct _ex_intern *t, *e;
    int i, count, vars, neg;

    t = _th_get_first_neg_tuple(info);
    while (t) {
        if (t->type==EXP_APPL && t->u.appl.functor==INTERN_OR) {
            for (i = 0; i < t->u.appl.count; ++i) {
                e = t->u.appl.args[i];
                if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) e = e->u.appl.args[0];
                e->user2 = 0;
            }
        }
        t = _th_get_next_neg_tuple(info);
    }

    count = 0;
    trail = NULL;
    vars = 0;

    t = _th_get_first_neg_tuple(info);
    while (t) {
        ++count;
        if (t->type==EXP_APPL && t->u.appl.functor==INTERN_OR) {
            for (i = 0; i < t->u.appl.count; ++i) {
                e = t->u.appl.args[i];
                if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) e = e->u.appl.args[0];
                if (!e->user2) {
                    e->next_cache = trail;
                    trail = e;
                    e->user2 = (struct _ex_intern *)++vars;
                }
            }
        }
        t = _th_get_next_neg_tuple(info);
    }
    fprintf(file, "c HTP generated dimacs file\n");
    fprintf(file, "p cnf %d %d\n", vars, count);

    t = _th_get_first_neg_tuple(info);
    while (t) {
        ++count;
        if (t->type==EXP_APPL && t->u.appl.functor==INTERN_OR) {
            for (i = 0; i < t->u.appl.count; ++i) {
                e = t->u.appl.args[i];
                if (e->type==EXP_APPL && e->u.appl.functor==INTERN_NOT) {
                    e = e->u.appl.args[0];
                    neg = -1;
                    fprintf(file, "-");
                } else {
                    neg = 1;
                }
                fprintf(file, "%d ", ((int)e->user2));
            }
            fprintf(file, "0\n");
        }
        t = _th_get_next_neg_tuple(info);
    }

    while (trail) {
        trail->user2 = NULL;
        trail = trail->next_cache;
    }
}

