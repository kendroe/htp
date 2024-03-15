/*
 * mymalloc.c
 *
 * Debug routines for malloc
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include "Globals.h"
#include <stdlib.h>
#include <string.h>

#define MALLOC_HASH_SIZE 1023
#define MALLOC_HASH(x) ((((int)x)>>4)%MALLOC_HASH_SIZE)

int file_line_hash(char *file, int line)
{
    int hash =0;

    while (*file) {
        hash += ((unsigned)(*file++));
    }
    hash += line;
    return hash%MALLOC_HASH_SIZE;
}

struct call_rec {
    struct call_rec *next;
    struct call_rec *cr_next;
    int size;
    int freed;
    void *location;
    struct malloc_rec *malloc;
};

struct malloc_rec {
    struct malloc_rec *next;
    char *file;
    int line;
    struct call_rec *calls;
    int total_bytes;
    int max_bytes;
    int final_bytes;
    int total_blocks;
    int max_blocks;
    int final_blocks;
};

struct malloc_rec *mallocs[MALLOC_HASH_SIZE];
struct call_rec *calls[MALLOC_HASH_SIZE];

void *_th_malloc(char *file,int line,int size)
{
    void *res = malloc(size);
    int flhash = file_line_hash(file,line);
    int chash = MALLOC_HASH(res);
    struct malloc_rec *mr = mallocs[flhash];
    struct call_rec *cr = (struct call_rec *)malloc(sizeof(struct call_rec));

    while(mr) {
        if (!strcmp(mr->file,file) && line==mr->line) break;
        mr = mr->next;
    }
    if (!mr) {
        mr = (struct malloc_rec *)malloc(sizeof(struct malloc_rec));
        mr->total_bytes = mr->max_bytes = mr->final_bytes = mr->total_blocks = mr->max_blocks = mr->final_blocks = 0;
        mr->calls = NULL;
        mr->next = mallocs[flhash];
        mallocs[flhash] = mr;
        mr->file = file;
        mr->line = line;
    }

    cr->next = mr->calls;
    mr->calls = cr;

    mr->total_blocks++;
    mr->final_blocks++;
    if (mr->final_blocks > mr->max_blocks) mr->max_blocks = mr->final_blocks;

    mr->total_bytes += size;
    mr->final_bytes += size;
    if (mr->final_bytes > mr->max_bytes) mr->max_bytes = mr->final_bytes;

    cr->cr_next = calls[chash];
    calls[chash] = cr;
    cr->location = res;
    cr->freed = 0;
    cr->size = size;
    cr->malloc = mr;
    cr->next = mr->calls;
    mr->calls = cr;

    return res;
}

void _th_free(char *file,int line,void *data)
{
    struct call_rec *cr = calls[MALLOC_HASH(data)];
    struct malloc_rec *mr;

    while (cr != NULL && cr->location != data) cr = cr->cr_next;
    if (!cr) {
        int i;
        printf("Error in free\n");
        i = 0;
        i = 1 / i;
        exit(1);
    }
    cr->freed = 1;

    mr = cr->malloc;
    --mr->final_blocks;
    mr->final_bytes -= cr->size;

    free(data);
}

void *_th_realloc(char *file, int line, void *data, int size)
{
    void *res = realloc(data, size);
    int flhash = file_line_hash(file,line);
    int chash = MALLOC_HASH(res);
    struct call_rec *cr = calls[MALLOC_HASH(data)];
    struct malloc_rec *mr;

    if (data != NULL) {
        while (cr != NULL && cr->location != data) cr = cr->cr_next;
        if (!cr) {
            int i;
            printf("Error in free\n");
            i = 0;
            i = 1 / i;
            exit(1);
        }
        cr->freed = 1;

        mr = cr->malloc;
        --mr->final_blocks;
        mr->final_bytes -= cr->size;
    }

    mr = mallocs[flhash];
    cr = (struct call_rec *)malloc(sizeof(struct call_rec));

    while(mr) {
        if (!strcmp(mr->file,file) && line==mr->line) break;
        mr = mr->next;
    }
    if (!mr) {
        mr = (struct malloc_rec *)malloc(sizeof(struct malloc_rec));
        mr->total_bytes = mr->max_bytes = mr->final_bytes = mr->total_blocks = mr->max_blocks = mr->final_blocks = 0;
        mr->calls = NULL;
        mr->next = mallocs[flhash];
        mallocs[flhash] = mr;
        mr->file = file;
        mr->line = line;
    }

    cr->next = mr->calls;
    mr->calls = cr;

    mr->total_blocks++;
    mr->final_blocks++;
    if (mr->final_blocks > mr->max_blocks) mr->max_blocks = mr->final_blocks;

    mr->total_bytes += size;
    mr->final_bytes += size;
    if (mr->final_bytes > mr->max_bytes) mr->max_bytes = mr->final_bytes;

    cr->cr_next = calls[chash];
    calls[chash] = cr;
    cr->location = res;
    cr->size = size;
    cr->malloc = mr;
    cr->next = mr->calls;
    mr->calls = cr;

    return res;
}

void _th_print_results()
{
#ifdef MALLOC_DEBUG
    int i;
    struct malloc_rec *mr;

    printf("MALLOC COUNTS\n\n");
    printf("                                                blocks          bytes\n");
    printf("file                 Line       max     total   final   max     total   final\n");
    printf("--------------------------------------------------------------------------------\n");
    for (i = 0; i < MALLOC_HASH_SIZE; ++i) {
        mr = mallocs[i];
        while (mr != NULL) {
            printf("%20s %10d %7d %7d %7d %7d %7d %7d\n",
                mr->file,
                mr->line,
                mr->max_blocks,
                mr->total_blocks,
                mr->final_blocks,
                mr->max_bytes,
                mr->total_bytes,
                mr->final_bytes);
            mr = mr->next;
        }
    }
    printf("--------------------------------------------------------------------------------\n");
#endif
}
