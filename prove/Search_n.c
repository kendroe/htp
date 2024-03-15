/*
 * search_node.c
 *
 * Search routines
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include "Globalsp.h"

#define CLOSE_HASH_SIZE 10007
#define OPEN_HASH_SIZE 1009

static struct search_node *open_list[OPEN_HASH_SIZE] ;

static struct search_node *close_list[CLOSE_HASH_SIZE] ;

static int compute_hash(int count, struct _ex_intern **exps)
{
    int hash = 0 ;
    int i ;

    for (i = 0; i < count * 2; ++i) hash += (((unsigned)exps[i])/4) ;

    return hash ;
}

static int cmp(const void *a, const void *b)
{
    return *((int *)b) - *((int *)a) ;
}

struct search_node *_th_find_search_node(unsigned count, struct _ex_intern **exps)
{
    int hash = compute_hash(count, exps) ;
    unsigned i ;
    struct search_node *node = close_list[hash%CLOSE_HASH_SIZE] ;

    qsort(exps, count, 2 * sizeof(struct _ex_intern *), cmp) ;

    while (node != NULL) {
        for (i = 0; i < count; ++i) {
             if (exps[i] != node->goals[i]) goto next1 ;
        }
        return node ;
next1:
        node = node->next ;
    }

    node = open_list[hash%OPEN_HASH_SIZE] ;

    while (node != NULL) {
        for (i = 0; i < count; ++i) {
             if (exps[i] != node->goals[i]) goto next2 ;
        }
        return node ;
next2:
        node = node->next ;
    }

    return NULL ;
}

struct search_node *_th_add_successor(struct search_node *parent, int count, struct _ex_intern **exps)
{
    struct search_node *node = (struct search_node *)_th_alloc(SEARCH_SPACE, sizeof(struct search_node *) + count * sizeof(struct _ex_intern *)) ;
    int hash = compute_hash(count, exps) ;
    int i ;

    node->next_sibling = parent->children ;
    parent->children = node ;
    node->next = open_list[hash%OPEN_HASH_SIZE] ;
    open_list[hash] = node ;
    node->goal_count = count ;
    for (i = 0; i < count * 2; ++i) {
        node->goals[i] = exps[i] ;
    }
	return node ;
}

void _th_close_node(struct search_node *n)
{
    int hash = compute_hash(n->goal_count, n->goals) ;
    struct search_node *p = open_list[hash%OPEN_HASH_SIZE], *prev = NULL ;

    while (p != NULL) {
        if (p==n) {
            prev->next = n->next ;
            break ;
        }
    }
    n->next = close_list[hash%CLOSE_HASH_SIZE] ;
    close_list[hash%CLOSE_HASH_SIZE] = n ;
}

void _th_clear_lists()
{
    int i ;

    for (i = 0; i < OPEN_HASH_SIZE; ++i) {
        open_list[i] = NULL ;
    }
    for (i = 0; i < CLOSE_HASH_SIZE; ++i) {
        close_list[i] = NULL ;
    }
}

