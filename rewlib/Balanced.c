/*
 * balanced.c
 *
 * Balanced tree routines
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "Globals.h"

struct Node {
    struct Node *left, *right ;
    int bal : 2 ;
    unsigned value : 30 ;
    unsigned size ;
} ;

struct Node1 {
    struct Node *left, *right ;
    int bal : 2 ;
    unsigned value : 30 ;
    unsigned size ;
    unsigned data[1] ;
} ;

struct Node2 {
    struct Node *left, *right ;
    int bal : 2 ;
    unsigned value : 30 ;
    char data[1] ;
} ;

#define FIND(compare,name,key_type) \
unsigned name(tree, key) \
struct Node *tree ; \
key_type key ; \
{ \
    int c ; \
\
    while (1) { \
        if (tree==NULL) return 0 ; \
\
        compare(key,tree,c) ; \
\
        if (c==0) return tree->value ; \
\
        if (c > 0) tree = tree->left ; \
        else tree = tree->right ; \
    } \
}

static struct Node *_bl_last ;

void _bl_save_value(unsigned x)
{
    _bl_last->value = x ;
}

#define INSERT(compare,size,save,name,group,key_type) \
unsigned name(treep, key) \
struct Node **treep ; \
key_type key ; \
{ \
    static struct Node *stack[300] ; \
    static char dir_stack[300] ; \
    int pos = 0 ; \
    struct Node *parent ; \
    struct Node *tree = *treep, *tree2 ; \
\
    while(1) { \
        if (tree==NULL) { \
            tree = (struct Node *)_th_alloc(group,sizeof(struct Node)+size(key)) ; \
            tree->left = tree->right = NULL ; \
            tree->bal = 0 ; \
            save(tree, key) ; \
            _bl_last = tree ; \
            break ; \
        } else { \
            int c ; \
            compare(key,tree,c) ; \
            if (c > 0) { \
                dir_stack[pos] = 1 ; \
                stack[pos++] = tree ; \
                tree = tree->left ; \
            } else if (c==0) { \
                return tree->value ; \
            } else { \
                dir_stack[pos] = 0 ; \
                stack[pos++] = tree ; \
                tree = tree->right ; \
            } \
        } \
    } \
\
    if (pos==0) { \
        *treep = tree ; \
        return 0 ; \
    } else { \
        --pos ; \
        if (dir_stack[pos]) { \
            stack[pos]->left = tree ; \
        } else { \
            stack[pos]->right = tree ; \
        }  \
    } \
\
    do { \
        parent = stack[pos] ; \
        if (dir_stack[pos]) { \
            switch(parent->bal) { \
                case 1: \
                    parent->bal = 0 ; \
                    return 0 ; \
                case 0: \
                    parent->bal = -1 ; \
                    break ; \
                case -1: \
                    if (tree->bal==-1) { \
                        parent->left = tree->right ; \
                        tree->right = parent ; \
                        parent->bal = 0 ; \
                        parent = tree ; \
                    } else { \
                        tree2 = tree->right ; \
                        tree->right = tree2->left ; \
                        tree2->left = tree ; \
                        parent->left = tree2->right ; \
                        tree2->right = parent ; \
                        switch (tree2->bal) { \
                            case 1: \
                                parent->bal = 0 ; \
                                tree->bal = -1 ; \
                                break ; \
                            case 0: \
                                parent->bal = 0 ; \
                                tree->bal = 0 ; \
                                break ; \
                            case -1: \
                                parent->bal = 1 ; \
                                tree->bal = 0 ; \
                        } \
                        parent = tree2 ; \
                    } \
                    parent->bal = 0 ; \
                    if (pos > 0) { \
                        if (dir_stack[--pos]) { \
                            stack[pos]->left = parent ;  \
                        } else { \
                            stack[pos]->right = parent ; \
                        } \
                    } else { \
                        *treep = parent ; \
                    } \
                    return 0 ; \
            } \
        } else { \
            switch(parent->bal) { \
                case -1: \
                    parent->bal = 0 ; \
                    return 0 ; \
                case 0: \
                    parent->bal = 1 ; \
                    break ; \
                case 1: \
                    if (tree->bal==1) { \
                        parent->right = tree->left ; \
                        tree->left = parent ; \
                        parent->bal = 0 ; \
                        parent = tree ; \
                    } else { \
                        tree2 = tree->left ; \
                        tree->left = tree2->right ; \
                        tree2->right = tree ; \
                        parent->right = tree2->left ; \
                        tree2->left = parent ; \
                        switch (tree2->bal) { \
                            case -1: \
                                parent->bal = 0 ; \
                                tree->bal = 1 ; \
                                break ; \
                            case 0: \
                                parent->bal = 0 ; \
                                tree->bal = 0 ; \
                                break ; \
                            case 1: \
                                parent->bal = -1 ; \
                                tree->bal = 0 ; \
                        } \
                        parent = tree2 ; \
                    } \
                    parent->bal = 0 ; \
                    if (pos > 0) { \
                        if (dir_stack[--pos]) { \
                            stack[pos]->left = parent ;  \
                        } else { \
                            stack[pos]->right = parent ; \
                        } \
                    } else { \
                        *treep = parent ; \
                    } \
                    return 0 ; \
            } \
        } \
        tree = parent ; \
        --pos ; \
    } while (pos >= 0) ; \
    return 0 ; \
}

#define int_compare(key,node,c) c=node->size-key
#define int_save(tree,key) tree->size = key
#define int_size(key) 0

#define int3_compare(key,node,c) \
     if (((unsigned *)key)[0]==node->size) { \
         if (((unsigned *)key)[1]==((struct Node1 *)node)->data[0]) { \
             c = ((struct Node1 *)node)->data[0]-((unsigned *)key)[2] ; \
         } else { \
             c = ((struct Node1 *)node)->data[0]-((unsigned *)key)[1] ; \
         } \
     } else { \
         c = node->size-((unsigned *)key)[0] ; \
     }
#define int3_save(tree,key) \
    { \
        tree->size = ((unsigned *)key)[0] ; \
        ((struct Node1 *)tree)->data[0] = ((unsigned *)key)[1] ; \
        ((struct Node1 *)tree)->data[1] = ((unsigned *)key)[2] ; \
    }
#define int3_size(key) sizeof(unsigned) * 2

#define int2_compare(key,node,c) \
     if (((unsigned *)key)[0]==node->size) { \
         c = ((struct Node1 *)node)->data[0]-((unsigned *)key)[1] ; \
     } else { \
         c = node->size-((unsigned *)key)[0] ; \
     }
#define int2_save(tree,key) \
    { \
        tree->size = ((unsigned *)key)[0] ; \
        ((struct Node1 *)tree)->data[0] = ((unsigned *)key)[1] ; \
    }
#define int2_size(key) sizeof(unsigned)

#define ints_compare(key,node,c) \
     { \
         int i; \
         i = 0 ; \
         do { \
             c = ((struct Node1 *)node)->data[i]-key[i+1] ; \
             ++i ; \
         } while (c==0 && i < (int)node->size && i < (int)key[0]) ; \
         if (c==0) { \
             c = (int)(node->size) - (int)(key[0]) ; \
         } \
    }
#define ints_save(tree,key) \
    { \
        int i ; \
        tree->size = key[0] ; \
        for (i = 0; i < (int)tree->size; ++i) { \
            ((struct Node1 *)tree)->data[i] = ((unsigned *)key)[i+1] ; \
        } \
    }
#define ints_size(key) (*key) * sizeof(unsigned)

#define intc_compare(key,tree,c) c=strcmp(((struct Node2 *)tree)->data,key) ;
#define intc_save(tree,key) \
    strcpy(((struct Node2 *)tree)->data,key) ;
#define intc_size(key) strlen(key)+1

FIND(int_compare,_bl_find_int,unsigned) ;
INSERT(int_compare,int_size,int_save,_bl_insert_int,0,unsigned) ;
FIND(int2_compare,_bl_find_int2,unsigned *) ;
INSERT(int2_compare,int2_size,int2_save,_bl_insert_int2,0,unsigned *) ;
FIND(int3_compare,_bl_find_int3,unsigned *) ;
INSERT(int3_compare,int3_size,int3_save,_bl_insert_int3,0,unsigned *) ;
FIND(ints_compare,_bl_find_ints,unsigned *) ;
INSERT(ints_compare,ints_size,ints_save,_bl_insert_ints,0,unsigned *) ;
FIND(intc_compare,_bl_find_intc,char *) ;
INSERT(intc_compare,intc_size,intc_save,_bl_insert_intc,0,char *) ;

#ifdef XXX
int check_left_value(tree, val)
struct Node *tree ;
int val ;
{
    if (tree==NULL) return 1 ;
    if (tree->size >= val) return 0 ;
    if (!check_left_value(tree->left, val)) return 0 ;
    return check_left_value(tree->right, val) ;
}

int check_right_value(tree, val)
struct Node *tree ;
int val ;
{
    if (tree==NULL) return 1 ;
    if (tree->size <= val) return 0 ;
    if (!check_right_value(tree->left, val)) return 0 ;
    return check_right_value(tree->right, val) ;
}

int check_tree(tree)
struct Node *tree ;
{
    if (tree==NULL) return 1 ;
    if (!check_left_value(tree->left, tree->size)) return 0 ;
    if (!check_right_value(tree->right, tree->size)) return 0 ;
    if (!check_tree(tree->left)) return 0 ;
    return check_tree(tree->right) ;
}

int height(tree)
struct Node *tree ;
{
    int l,r ;
    if (tree==NULL) return 0 ;
    l = height(tree->left) ;
    r = height(tree->right) ;
    if (l>r) return 1+l ; else return 1+r ;
}

int check_balance(tree)
struct Node *tree ;
{
    if (tree==NULL) return 1 ;
    if (tree->bal != height(tree->right)-height(tree->left)) return 0 ;
    return (check_balance(tree->left) && check_balance(tree->right)) ;
}

void print_tree(tree, indent)
struct Node *tree ;
int indent ;
{
    int i ;
    for (i = 0; i < indent; ++i) printf(" ") ;
    if (tree == NULL) {
        printf("Leaf\n") ;
    } else {
        printf("Key: %d Value: %d Balance: %d\n", tree->size, tree->value, tree->bal) ;
        print_tree(tree->left,indent+2) ;
        print_tree(tree->right,indent+2) ;
    }
}

int int_cmp(x,y)
int x,y ;
{
    return y-x ;
}

static int next(elements, size)
int elements[] ;
int size ;
{
    int i, j, current, pos ;
    for (i = size-2; i >= 0; --i) {
         pos = i ;
         current = size ;
         for (j=i+1; j < size; ++j) {
             if (elements[j] < current && elements[j] > elements[i]) {
                 current = elements[j] ;
                 pos = j ;
             }
         }
         if (pos != i) {
             elements[pos] = elements[i] ;
             elements[i] = current ;
             qsort(elements+i+1,size-i-1,sizeof(int),int_cmp) ;
             return 1 ;
         }
    }
    return 0 ;
}

main()
{
    int elements[6] ;
    int i ;
    _th_alloc_init() ;
    for (i = 0; i < 6; ++i) {
        elements[i] = i ;
    }
    do {
        struct Node *tree ;
        tree = NULL ;
        for (i = 0; i < 6; ++i) {
            printf("%d ", elements[i]) ;
        }
        printf("\n") ;
        for (i = 0; i < 6; ++i) {
             insert_int(&tree, elements[i], i) ;
        }
        if (!check_tree(tree)) printf("Value error\n") ;
        if (!check_balance(tree)) printf("Balance error\n") ;
        print_tree(tree, 0) ;
    } while(next(elements,6)) ;
    //printf("This is a test\n") ;
}
#endif

