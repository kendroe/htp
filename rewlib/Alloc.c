/*
 * alloc.c
 *
 * Memory allocation routines
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */

#ifdef _DEBUG
#define STATISTICS
#endif

#include <stdlib.h>
#include <stdio.h>
#include <memory.h>
#include "Globals.h"
#include "Doc.h"

#define MEM_BLOCK_SIZE 65536

#define SPACE_COUNT 200

GDEF("struct_primary_pointer main mem_block next main_memblock");
GDEF("struct_space main mem_block malloc");

struct mem_block {
    struct mem_block *next ;
    int oversized;
    char data[MEM_BLOCK_SIZE] ;
} ;

GDEF("struct_primary_pointer main mem_table current main mem_block");
GDEF("struct_space main mem_table static");
GDEF("invariant ALL(i in 0..SPACE_COUNT-1) mem_table[i].tail in PathSet(mem_table[i] current next *)");
GDEF("invariant ALL(i in 0..SPACE_COUNT-1) mem_table[i].tail->next==NULL");

struct mem_table {
    int offset ;
#ifdef STATISTICS
    int count ;
    int max_count ;
#endif
    struct mem_block *current ;
    struct mem_block *tail ;
} ;

GDEF("global *reclaim main mem_block");

static struct mem_block *reclaim ;

GDEF("global table[0..SPACE_COUNT-1] main mem_table");

GDEF("abstraction mem_space space[SPACE_COUNT]");
GDEF("abstraction Set(int) valid_releases[SPACE_COUNT]");
GDEF("abstraction Map(int,state) release_source[SPACE_COUNT]");

GDEF("invariant ALL(i in 0..SPACE_COUNT-1), ALL(block in blocks(space[i])) EXISTS(l in mem_space[i].(current*)) block >= l->data  && block+size(space[i],block) < l->data+MEM_BLOCK_SIZE))");

static struct mem_table table[SPACE_COUNT] ;

void _th_alloc_init()
{
    int i ;

    for (i = 0; i < SPACE_COUNT; ++i) {
        table[i].offset = 0 ;
        table[i].current = NULL ;
#ifdef STATISTICS
        table[i].count = table[i].max_count = 0 ;
#endif
    }
}

int _th_check_alloc_block(int space, char *c)
{
    struct mem_block *m = table[space].current;

    if (m==NULL) return 1;

    if (c>=m->data && c<m->data+table[space].offset) return 0;

    m = m->next;

    while (m) {
        if (c>=m->data && c<m->data+MEM_BLOCK_SIZE) return 0;
        m = m->next;
    }

    return 1;
}

GDEF("modifies _th_alloc_clear mem_space[i]");
GDEF("post _th_alloc_clear ALL(x) not(x in blocks(mem_space))");

void _th_alloc_clear(int i)
{
    table[i].tail->next = reclaim ;
    reclaim = table[i].current ;
    table[i].current = table[i].tail = NULL ;
}

GDEF("modifies _th_alloc_delete mem_space[i]");
GDEF("post _th_alloc_delete ALL(x) not(x in blocks(mem_space))");

void _th_alloc_delete(int i)
{
    struct mem_block *n ;
    while (table[i].current != NULL) {
        n = table[i].current->next ;
        FREE(table[i].current) ;
        table[i].current = n ;
    }
    table[i].tail = NULL ;
}

void _th_alloc_shutdown()
{
    int i ;
    struct mem_block *n ;

    /**********/

#ifdef STATISTICS
    printf("\n*** alloc statistics\n\n") ;
#endif

    for (i = 0; i < SPACE_COUNT; ++i) {
#ifdef STATISTICS
        if (table[i].max_count > 0) {
            printf("    %3d: usage: %5d max usage: %5d\n", i, table[i].count, table[i].max_count) ;
        }
#endif
        //_th_alloc_delete(i) ;
    }
    _th_print_results();
    while(reclaim != NULL) {
        n = reclaim ;
        reclaim = reclaim->next ;
        FREE(n) ;
    }
}

GDEF("modifies _th_alloc_mark valid_releases(space)");
GDEF("modifies _th_alloc_mark release_source(space)");

GDEF("post _th_alloc_mark valid_releases(space)@post==valid_releases(space)@pre union pre");
GDEF("post _th_alloc_mark release_source(space,v)@post==if v==ret then post else release_source(space,v)@pre");

char *_th_alloc_mark(int space)
{
    if (table[space].current==NULL) return NULL ;
    return table[space].current->data+table[space].offset ;
}

GDEF("modifies _th_alloc_release valid_releases(space)");
GDEF("modifies _th_alloc_release release_source(space)");
GDEF("modifies _th_alloc_release space(space)");

GDEF("pre _th_alloc_release pos in valid_releases(space)");
GDEF("post _th_alloc_release space(space)@post==space(space)@release_source(space,pos)");

void _th_alloc_release(int space, char *pos)
{
    struct mem_block *n ;

    if (pos==NULL) {
        while (table[space].current != NULL) {
            n = table[space].current ;
            table[space].current = table[space].current->next ;
            n->next = reclaim ;
            reclaim = n ;
        }
#ifdef STATISTICS
        table[space].count = 0 ;
#endif
    } else {
        while ((pos < table[space].current->data || pos > table[space].current->data+MEM_BLOCK_SIZE) &&
               pos != table[space].current->data+table[space].current->oversized) {
            n = table[space].current ;
            table[space].current = table[space].current->next ;
            if (n->oversized) {
                FREE(n);
            } else {
                n->next = reclaim ;
                reclaim = n ;
            }
            if (table[space].current==NULL) {
                printf("Illegal release point passed %d\n", pos) ;
                _th_alloc_shutdown() ;
                exit(1) ;
            }
        }
        table[space].offset = pos-table[space].current->data ;
#ifdef STATISTICS
        table[space].count = 0 ;
        n = table[space].current ;
        while (n != NULL) {
            ++table[space].count ;
            n = n->next ;
        }
#endif
    }
}

int _th_alloc_check_release(int space, char *pos)
{
    struct mem_block *n ;

    if (pos==NULL) return 0;

    n = table[space].current;
    while (n && (pos < n->data || pos > n->data+MEM_BLOCK_SIZE) &&
           pos != n->data+n->oversized) {
        n = n->next;
    }
    if (n==NULL) {
        fprintf(stderr, "%x %x %x\n", table[space].current->data, table[space].offset, pos);
    }
    return n==NULL;
}

GDEF("modifies _th_alloc space(space)");
GDEF("post _th_alloc x in space(space)@pre => x in space(space)@post");
GDEF("post _th_alloc x in space(space)@pre => size(x)@pre==size(x)@post");
GDEF("post _th_alloc ret in space(space)@post");
GDEF("post _th_alloc size(ret)@post==size");
GDEF("post _th_alloc not(ret in space(space)@pre)");

char *_th_alloc(int space, int size)
{
    int y=size%4 ;
#ifdef USE_MALLOC
    if (_tree_zone==2) return MALLOC(size);
#endif

    //if (space==TERM_CACHE_SPACE && _tree_zone >= 1697000) {
    //    printf("size, offset = %d %d\n", size, table[space].offset);
    //}

    if (y!=0) size+=(4-y) ;

    if (size >= MEM_BLOCK_SIZE) {
        struct mem_block *n ;
        n = (struct mem_block *)MALLOC(sizeof(struct mem_block)-MEM_BLOCK_SIZE+size) ;
        n->oversized = size;
        if (n==NULL) {
            fprintf(stderr, "Error in malloc\n");
            _th_alloc_shutdown();
            exit(1);
        }
        n->next = table[space].current ;
        if (table[space].current==NULL) table[space].tail = n;
        table[space].offset = size ;
        table[space].current = n ;
#ifdef STATISTICS
        ++table[space].count ;
        if (table[space].count > table[space].max_count) table[space].max_count = table[space].count ;
#endif
        //memset(table[space].current->data, 0, size) ;
        return table[space].current->data ;
    } else if (table[space].current == NULL) {
        if (reclaim == NULL) {
            table[space].tail = table[space].current =
                (struct mem_block *)MALLOC(sizeof(struct mem_block)) ;
            table[space].tail->oversized = 0;
            if (table[space].tail==NULL) {
                fprintf(stderr,"Error in MALLOC\n") ;
                _th_alloc_shutdown() ;
                exit(1) ;
            }
        } else {
            table[space].tail = table[space].current = reclaim ;
            reclaim = reclaim->next ;
        }
        table[space].current->next = NULL ;
        table[space].offset = size ;
#ifdef STATISTICS
        table[space].count = 1 ;
        if (table[space].count > table[space].max_count) table[space].max_count = table[space].count ;
#endif
        return table[space].current->data ;
    } else if (MEM_BLOCK_SIZE < table[space].offset + size) {
        struct mem_block *n ;
        //if (space==TERM_CACHE_SPACE && _tree_zone >= 1697000) {
        //    printf("new block\n");
        //}
        if (reclaim == NULL) {
            n = (struct mem_block *)MALLOC(sizeof(struct mem_block)) ;
            if (n==NULL) {
                fprintf(stderr,"Error in MALLOC\n") ;
                _th_alloc_shutdown() ;
                exit(1) ;
            }
            n->oversized = 0;
        } else {
            n = reclaim ;
            reclaim = reclaim->next ;
        }
        n->next = table[space].current ;
        table[space].offset = size ;
        table[space].current = n ;
#ifdef STATISTICS
        ++table[space].count ;
        if (table[space].count > table[space].max_count) table[space].max_count = table[space].count ;
#endif
        //memset(table[space].current->data, 0, size) ;
        return table[space].current->data ;
    } else {
        int o = table[space].offset ;
        table[space].offset += size ;
        //memset(table[space].current->data+o, 0, size) ;
        return table[space].current->data+o ;
    }
}

