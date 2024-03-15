/*
 * tree.c
 *
 * This file contains routines to print output for creating trees.
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include "Globals.h"
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

static time_t start_time;
unsigned time_limit = TIME_LIMIT;
static time_t restart_time;

int _th_check_restart(int t)
{
    if (restart_time + t < time(NULL)) {
        restart_time = time(NULL);
        return 1;
    }

    return 0;
}

#ifdef FAST

void _tree_init(char *n)
{
    restart_time = start_time = time(NULL);
}

void _zone_increment()
{
    time_t now = time(NULL);
    unsigned diff = now-start_time;

    if (diff > time_limit) {
        printf("Time limit exceeded\n");
        _th_alloc_shutdown();
        exit(1);
    }
}

void _tree_shutdown()
{
#ifdef WIN32
    unsigned t = time(NULL) - start_time;

    if (t < 1) {
        fprintf(stderr, "Run time: < 1 second\n");
    } else if (t == 1) {
        fprintf(stderr, "Run time: 1 second\n");
    } else {
        fprintf(stderr, "Run time: %d seconds\n", t);
    }
#endif
}

void _tree_set_time_limit(unsigned t)
{
    time_limit = t;
}

#else

#include <stdarg.h>
//#include <io.h>
#include <fcntl.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

static FILE *file, *file_table ;
int indent ;
static FILE *local_file = NULL, *local_file_table = NULL;

int _info_flag ;
int _tree_interactive, _tree_core ;
int _tree_start, _tree_end ;
int _tree_zone ;
int _tree_subzone ;
int _tree_subzone_level ;
int _tree_sub ;
int _tree_sub2 ;
int _tree_mute ;
int _tree_count ;

int _tree_count = 0 ;
static int line_entry ;

#define CACHE_TABLE_SIZE 249989

int _th_get_indent()
{
	return indent;
}

void _th_set_indent(int x)
{
	indent = x;
}

static struct cache_table {
    struct cache_table *next ;
    unsigned cache_entry ;
    unsigned line_entry ;
} *cache_table[CACHE_TABLE_SIZE] ;

struct table_file_record {
    long line ;
    int indent ;
} ;

static unsigned entry_number ;

void _tree_init(char *n)
{
    char name[100] ;
    if (n==NULL) {
        file = file_table = NULL ;
    } else {
        sprintf(name, "%s", n) ;
        unlink(name);
        file = fopen(name,"w") ;
        sprintf(name, "%s.tab", n) ;
        unlink(name);
        file_table = fopen(name,"wb") ;
    }
    _tree_start = _tree_end = -1 ;
    _tree_interactive = 0 ;
    _tree_core = 1 ;
    _tree_subzone = 0 ;
    _tree_subzone_level = 0 ;
    _tree_sub = -1 ;
    _tree_sub2 = -1 ;
    _tree_count = 0 ;
    _tree_mute = 0 ;
    line_entry = 0 ;
    restart_time = start_time = time(NULL);
}

void _tree_set_time_limit(unsigned t)
{
    time_limit = t;
}

void _tree_start_local(char *n)
{
    char name[100];

    sprintf(name, "%s.tr", n);
    local_file = fopen(name,"w");
    sprintf(name, "%s.tab", n);
    local_file_table = fopen(name,"wb");
}

void _tree_finish_local()
{
    fclose(local_file);
    fclose(local_file_table);
    local_file = local_file_table = NULL;
}

void _tree_shutdown()
{
#ifdef WIN32
    unsigned t = time(NULL) - start_time;

    if (t < 1) {
        fprintf(stderr, "Run time: < 1 second\n");
    } else if (t == 1) {
        fprintf(stderr, "Run time: 1 second\n");
    } else {
        fprintf(stderr, "Run time: %d seconds\n", t);
    }
#endif

    if (file != NULL) {
        fclose(file) ;
        fclose(file_table) ;
    }
}

void _tree_indent()
{
    ++indent ;
}

int _tree_get_indent()
{
    return indent;
}

void _tree_undent()
{
    --indent ;
    if (indent < 0) {
        fprintf(stderr, "Error in indenting\n");
		indent = 0;
		indent = 1/indent;
        exit(1);
    }
}

static int last_print = 0 ;

#define LIMIT 100

void write_line(char *line, int indent)
{
    struct table_file_record tab ;

    if (file==NULL) return;

    tab.line = ftell(file) ;
    tab.indent = indent ;
    fwrite(&tab,sizeof(struct table_file_record),1,file_table) ;
    fprintf(file, "%d: %s\n", indent, line) ;
    if (_tree_core) {
        fflush(file) ;
        fflush(file_table) ;
    }
    if (local_file) {
        tab.line = ftell(local_file);
        fwrite(&tab,sizeof(struct table_file_record),1,local_file_table) ;
        fprintf(local_file, "%s\n", line);
    }
    ++line_entry ;
    ++_tree_count ;

}

void _th_save_cache(unsigned cache)
{
    if (_zone_active()) {
        struct cache_table *ct = MALLOC(sizeof(struct cache_table)) ;
        ct->next = cache_table[cache%CACHE_TABLE_SIZE] ;
        cache_table[cache%CACHE_TABLE_SIZE] = ct ;
        ct->cache_entry = cache ;
        ct->line_entry = line_entry ;
    }
}

void _th_reference_cache(unsigned cache)
{
    struct cache_table *ct;

    if (!_zone_active()) return;

    ct = cache_table[cache%CACHE_TABLE_SIZE] ;
    while (ct != NULL) {
        if (ct->cache_entry==cache) {
            char s[30] ;
            sprintf(s, "Cache entry %d", ct->line_entry) ;
            write_line(s, indent) ;
            return ;
        }
        ct = ct->next ;
    }

    write_line("Cached rewrite not in file", indent) ;
}

//extern struct _ex_intern *gtest;
//extern struct _ex_intern *gtest2;

//static struct env *check_env =  NULL;

void _tree_print(char *format, ...) 
{ 
    va_list vaList ; 
    int slen, ind;

    //the_hack_check();
    //check_explanations(NULL);
    //check_terms();

    //if (check_env) valid_env(check_env);

    va_start (vaList, format) ;
    if (_tree_interactive) {
        vprintf(format, vaList) ;
    } else {
        static char line[50000000], *l, *c ;
        int pre, details ;
        vsprintf(line, format, vaList) ;
        if (strlen(line) > 50000000) {
			fprintf(stderr, "Line too long in _tree_print\n") ;
			fflush(stderr) ;
			exit(1);
		}
        //printf("indent,line:%d,%s\n", indent, line);
        l = line ;
        while (*l) {
            pre = 0 ;
            details = 0 ;
            c = l;
            while (*c && *c != '\n') {
                ++c;
            }
            if (*c=='\n') {
                *c = 0;
                ++c;
            }
            slen = strlen(l);
            ind = indent;
            while (*l==' ') {
                ++l;
                ++ind;
            }
            while (slen > LIMIT) {
                char x = l[LIMIT] ;
                if (pre && !details) {
                    details = 1 ;
                    write_line("details", ind+1) ;
                }
                l[LIMIT] = 0 ;
                write_line(l, ind + pre) ;
                l[LIMIT] = x ;
                l += LIMIT ;
                slen -= LIMIT ;
                pre = 2 ;
            }
            if (l[0]) {
                if (pre && !details) {
                    write_line("details", ind + 1) ;
                }
                write_line(l, ind + pre) ;
            }
            l = c;
        }
    }
    va_end (vaList) ;
    last_print = indent ;
    //check_learn_env();
    //if (gtest && gtest->find==_ex_true) {
    //    fprintf(stderr, "gtest->find = _ex_true\n");
    //    exit(1);
    //}
    //if (gtest2 && gtest2->find==_ex_false) {
    //    fprintf(stderr, "gtest2->find = _ex_false\n");
    //    exit(1);
    //}
    //check_x53();
    //check_mt();
    //check_invalid_merge();
} 

void _tree_print_exp(char *c, struct _ex_intern *exp)
{
    char *s;
    s = _th_print_exp(exp);
	_tree_print("%s: %s", c, s);
}

//#define STOP_ZONE 1307

void _zone_increment()
{
    time_t now = time(NULL);
    unsigned diff = now-start_time;

    //check_learn_env();

    if (diff > time_limit) {
        printf("Time limit exceeded\n");
        _th_alloc_shutdown();
        exit(1);
    }

    ++_tree_zone ;
#ifdef _DEBUG
    //_tree_print("Zone %d (previous tree %d)",_tree_zone, _tree_count) ;
#endif

    //_tree_count = 0 ;

#ifdef _DEBUG
    fprintf(stderr, "Zone %d\n", _tree_zone);
    fflush(stderr);
#else
    if (_tree_zone < 10000 || _tree_zone%100==0) {
        fprintf(stderr, "Zone %d\n", _tree_zone);
        fflush(stderr);
    }
#endif
    fflush(file);
    fflush(file_table);
#ifdef STOP_ZONE
    if (_tree_zone==STOP_ZONE) {
        fprintf(stderr, "Hit stop zone\n");
        exit(1);
    }
#endif
    //if (_tree_zone==2278) {
    //    _tree_zone = 0 ;
    //    _tree_zone = 1 / _tree_zone ;
    //}
    //if (_tree_zone==4000000) {
    //    _ex_shutdown();
    //    _th_alloc_shutdown();
    //    exit(1);
    //}
    if (_tree_end >= 0 && _tree_zone > _tree_end) {
        _ex_shutdown() ;
        _th_alloc_shutdown() ;
        printf("End of printed zones\n");
        exit(1) ;
    }

    _tree_subzone = 0 ;
    _tree_subzone_level = 0 ;

	//if (_tree_zone==1000) {
	//	_th_alloc_shutdown();
	//	exit(1);
	//}
}

void _zone_enter_sub()
{
    ++_tree_subzone_level ;
    if (!_tree_mute && _tree_zone >= _tree_start && _tree_zone <= _tree_end && _tree_subzone_level==1) {
        fprintf(stderr,"Entering subzone %d\n", _tree_subzone) ;
        fflush(stderr) ;
        _tree_print("Entering subzone %d (previous tree = %d)", _tree_subzone, _tree_count) ;
    }
}

void _zone_exit_sub()
{
    --_tree_subzone_level ;
    if (!_tree_subzone_level) ++_tree_subzone ;
}

//void setup_check(struct env *env)
//{
//    check_env = env;
//}

void _zone_print(char *format, ...) 
{ 
    va_list vaList ; 

    //the_hack_check();
    //check_explanations(NULL);
    //check_terms();

    //if (check_env) valid_env(check_env);

    if (_zone_active()) {
        static char line[50000000], *l ;
        int pre ;
        int details = 0 ;
        while (last_print < indent - 1) {
            write_line("", last_print++) ;
        }
		pre = 0 ;
        va_start (vaList, format) ;
        vsprintf(line, format, vaList) ;
        va_end (vaList) ;
        if (strlen(line) > 50000000) {
			fprintf(stderr, "Line too long in _tree_print\n") ;
			fflush(stderr) ;
			exit(1) ;
		}
        l = line ;
        while (strlen(l) > LIMIT) {
            char x = l[LIMIT] ;
            if (pre && !details) {
                details = 1 ;
                write_line("details", indent+1) ;
            }
            l[LIMIT] = 0 ;
            write_line(l, indent+pre) ;
            l[LIMIT] = x ;
            l += LIMIT ;
            pre = 2 ;
        }
        if (l[0]) {
            if (pre && !details) {
                details = 1 ;
                write_line("details", indent+1) ;
            }
            write_line(l, indent+pre) ;
        }
        last_print = indent+pre ;
    }

    //if (gtest && gtest->find==_ex_true) {
    //    fprintf(stderr, "gtest->find = _ex_true\n");
    //    exit(1);
    //}
    //if (gtest2 && gtest2->find==_ex_false) {
    //    fprintf(stderr, "gtest2->find = _ex_false\n");
    //    exit(1);
    //}
    //check_learn_env();
    //check_x53();
    //check_mt();
    //check_invalid_merge();
}
#endif

