/*
 * memory.c
 *
 * Routines for saving rewrite results to the disk to speed up
 * execution.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include "Globals.h"
#include <string.h>

struct memory {
    struct _ex_intern *input ;
    struct _ex_intern *output ;
    struct memory *next ;
} ;

static struct memory *memory = NULL, *current = NULL, *last, *lcurrent ;

static int is_initialized = 0 ;

static struct _ex_intern *last_check ;

struct _ex_intern *_th_check_rewrite(struct _ex_intern *e)
{
    if (!is_initialized) return NULL ;

    last_check = e ;

    if (current==NULL) return NULL ;

#ifndef FAST
    if (e==current->input && !_zone_active()) {
        e = current->output ;
    } else {
        e = NULL ;
    }
#endif

    lcurrent = current ;
    current = current->next ;

    return e ;
}

void _th_set_rewrite(struct _ex_intern *e)
{
    if (!is_initialized) return ;

    if (lcurrent==NULL) {
        if (last==NULL) {
            memory = last = (struct memory *)MALLOC(sizeof(struct memory)) ;
        } else {
            last->next = (struct memory *)MALLOC(sizeof(struct memory)) ;
            last = last->next ;
        }
        last->input = last_check ;
        last->output = e ;
        last->next = NULL ;
    } else {
        lcurrent->input = last_check ;
        lcurrent->output = e ;
    }

    _th_write_memory() ;
}

void _th_write_memory()
{
    FILE *f = fopen("memory","w") ;
    struct memory *m = memory ;

    while (m != NULL) {
        fprintf(f, "%s\n", _th_print_exp(m->input)) ;
        fprintf(f, "%s\n", _th_print_exp(m->output)) ;
        m = m->next ;
    }

    fclose(f) ;
}

void _th_init_memory(struct env *env)
{
    FILE *f = fopen("memory","r") ;
    char line[100000] ;
    int x ;

    is_initialized = 1 ;
    fprintf(stderr, "Initialized memory module\n") ;

    if (f==NULL) return ;

    while (!feof(f)) {
        line[0] = 0 ;
        fgets(line,99999,f) ;
        x = strlen(line)-1 ;
        while (line[x] < ' ' && x >= 0) line[x--] = 0 ;

        if (!line[0]) break ;

        if (current==NULL) {
            memory = current = (struct memory *)MALLOC(sizeof(struct memory)) ;
            current->next = NULL ;
        } else {
            current->next =(struct memory *)MALLOC(sizeof(struct memory)) ;
            current = current->next ;
        }

        current->input = _th_parse(env,line) ;

        line[0] = 0 ;
        fgets(line,99999,f) ;
        x = strlen(line)-1 ;
        while (line[x] < ' ' && x >= 0) line[x--] = 0 ;

        current->output = _th_parse(env,line) ;
        current->next = NULL ;
    }

    last = current ;
    current = memory ;

    fclose(f) ;
}
