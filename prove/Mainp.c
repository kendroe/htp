/*
 * main.c
 *
 * Main program for the C verifier
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <signal.h>

#include <time.h>

#include "../rewlib/RewriteLog.h"
#include "Globalsp.h"

#ifdef TEST
#define MAX_TESTS 50

struct exp_test {
          char exp[200] ;
          int result ;
       } tests[MAX_TESTS] =
    {
        { "(f 1 b #2/3)", -1 },
        { "(f 1 b #2/3)", 0 },
        { "(f -1 b #-2/3)", 0 },
        { "(g 1 b \"a\\\"bc\")", -1 },
        { "(lambda x (f x))", -1 },
        { "(ALL(x : (e x)) (f x))", -1 },
        { "(ALL(x : (True)) (f x))", -1 },
        { "(ALL(x) (f x))", -1 },
        { "(EXISTS(x) (f x))", -1 },
        { "(INDEX (f x) f 0)", -1 },
        { "(case (f x) (True) (g x) (False) (h x))", -1 },
        { "(f x y z)" },
        { "(f x x0 x1)" },
        { "", 0 }
    } ;


void print_match_result(struct match_return *r)
{
    printf("Result:\n") ;
    while(r != NULL) {
        printf("    ") ;
        _th_print_unifier(r->theta) ;
        r = r->next ;
    }
    printf("end\n") ;
}

main ()
{
    int i, j, vc ;
    struct _ex_intern *exp, *exp1 ;
    char *r ;
    struct _ex_unifier *u ;
    unsigned *vl ;
    unsigned list1[2], list2[2] ;
    struct env *env, *def ;
    struct parameter parameters[5], *params ;
    struct match_return *mr ;
    struct disc *d ;
    struct small_disc *s ;
    unsigned big1[10], big2[10], *bigres ;
    char line[80] ;

    /* Initialization */
    _th_alloc_init() ;
    _th_intern_init () ;
    _th_init_bignum() ;
    _ex_init() ;
    _th_print_init() ;
    _th_cache_init() ;
    _th_transitive_init() ;
    _th_init_rewrite() ;
    _th_parse_init() ;
    _th_type_init() ;
    _th_init_term_cache() ;

    env = _th_new_empty_env(2) ;

    printf("Expression tests\n") ;

    list1[0] = _th_intern("x") ;
    list1[1] = _th_intern("y") ;

    list2[0] = _th_intern("z") ;
    list2[1] = _th_intern("y") ;

    for (i = 0; i < MAX_TESTS; ++i) {
         if (tests[i].exp[0]==0) break ;
         exp = _th_parse(env,tests[i].exp) ;
         r = _th_print_exp(exp) ;
         printf("exp %s %8lx %s\n", tests[i].exp, exp, r) ;
         vl = _th_get_free_vars(exp, &vc) ;
         printf("Free vars:") ;
         for (j = 0; j < vc; ++j) {
              printf(" %s", _th_intern_decode(vl[j])) ;
         }
         printf("\n") ;
         vl = _th_get_all_vars(exp, &vc) ;
         printf("All vars:") ;
         for (j = 0; j < vc; ++j) {
              printf(" %s", _th_intern_decode(vl[j])) ;
         }
         printf("\n") ;
         exp1 = exp = _th_mark_vars(env,exp) ;
         r = _th_print_exp(exp) ;
         printf("Marked expression: %s\n", r) ;
         vl = _th_get_marked_vars(exp, &vc) ;
         printf("Marked vars:") ;
         for (j = 0; j < vc; ++j) {
              printf(" %s", _th_intern_decode(vl[j])) ;
         }
         printf("\n") ;
         exp = _th_unmark_vars(env,exp) ;
         r = _th_print_exp(exp) ;
         printf("name away: %s\n", _th_intern_decode(_th_name_away(exp,list1[0]))) ;
         printf("Unmarked expression: %s\n", r) ;
         exp1 = _th_unmark_vars_list(env,exp1, 2, list1) ;
         r = _th_print_exp(exp1) ;
         printf("Partial unmarked expression: %s\n", r) ;
         exp = _th_mark_vars_list(env,exp, 2, list2) ;
         r = _th_print_exp(exp) ;
         printf("Partial marked expression: %s\n", r) ;
    }

    printf("name away2: %s\n", _th_intern_decode(_th_name_away_from_list(2,list1,list1[0]))) ;
    printf("name away2: %s\n", _th_intern_decode(_th_name_away_from_list(2,list2,list1[0]))) ;
    /* Substitute test */
    u = _th_new_unifier(0) ;
    u = _th_add_pair(0,u,_th_intern("v"),_th_parse(env,"(f x)")) ;
    exp = _th_subst(env,u, _th_parse(env,"(g v q)")) ;
    r = _th_print_exp(exp) ;
    printf("r = %s\n", r) ;

    u = _th_add_pair(0,u,_th_intern("x"),_th_parse(env,"(g y)")) ;
    exp = _th_parse(env,"(ALL (x : (f x v)) (g x v))") ;
    r = _th_print_exp(exp) ;
    printf("pre r = %s\n", r) ;
    exp = _th_subst(env, u, exp) ;
    r = _th_print_exp(exp) ;
    printf("r = %s\n", r) ;

    exp = _th_subst(env, u, (exp = _th_parse(env,"(ALL (v : (f x v)) (g x v))"))) ;
    r = _th_print_exp(exp) ;
    printf("r = %s\n", r) ;

    exp = _th_subst(env, u, (exp = _th_parse(env,"(case v (F x) (f x v) (G v) (f x v))"))) ;
    r = _th_print_exp(exp) ;
    printf("r = %s\n", r) ;

    exp = _th_subst(env, u, (exp = _th_parse(env,"(lambda v (f x v))"))) ;
    r = _th_print_exp(exp) ;
    printf("r = %s\n", r) ;

    exp = _th_subst(env, u, (exp = _th_parse(env,"(lambda x (f x v))"))) ;
    r = _th_print_exp(exp) ;
    printf("r = %s\n", r) ;

    /* Produce an environment for testing equal and match */
    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_UNION ;
    _th_add_attrib(2,env,INTERN_AC,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_SET ;
    _th_add_attrib(2,env,INTERN_AC,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_AND ;
    _th_add_attrib(2,env,INTERN_AC,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_OR ;
    _th_add_attrib(2,env,INTERN_AC,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_EQUAL ;
    _th_add_attrib(2,env,INTERN_C,1,parameters) ;

    exp = _th_parse(env,"(f x y)") ;
    exp1 = _th_parse(env, "(f y z)") ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;
    printf("equal1: %d\n", _th_equal(env, exp, exp)) ;

    exp = _th_parse(env,"(f y)") ;
    exp1 = _th_parse(env, "(f y)") ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(&& y z)") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env, "(&& z y)") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(ALL (x : (e x)) (f x))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(ALL (y : (e y)) (f y))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(ALL (x : (e x)) (f x))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(ALL (y : (e y)) (f x))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(ALL (x y : (e x y)) (f x y))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(ALL (x y : (e y x)) (f y x))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(ALL (x y : (e x y)) (f x y))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(ALL (y x : (e y x)) (f y x))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(ALL (x y : (e x y)) (f x y))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(ALL (y x : (e y x)) (f x y))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(EXISTS (x y) (f x y))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(EXISTS (y x) (f x y))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(EXISTS (x y) (f x y))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(EXISTS (y x) (f x x))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;
    printf("equal: %d\n", _th_equal(env, exp1, exp)) ;

    exp = _th_parse(env,"(&& x y z)") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env, "(&& z x y)") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(&& x y z)") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env, "(&& z t y)") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(&& x y z)") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env, "(&& z t y)") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(ALL (x y) (&& x (f y) y))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env, "(ALL (x y) (&& x (f x) y))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;
    printf("equal: %d\n", _th_equal(env, exp1, exp)) ;

    exp = _th_parse(env,"(ALL (x y) (&& x (f y) x))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env, "(ALL (x y) (&& x (f x) y))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(case (f y) (True) (g x) (False) (h x))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(case (f y) (False) (h x) (True) (g x))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(case (f y) (True) (g x) (False) (z x))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(case (f y) (False) (h x) (True) (g x))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(case (f y) (Cons x y) (g x) (Nil) (h x))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(case (f y) (Nil) (h x) (Cons x y) (g x))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(case (f y) (Cons x y) (g x) (Nil) (h x))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(case (f y) (Nil) (h x) (Cons x y) (g z))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(case (f y) (Cons x y) (g x) (Nil) (h x))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(case (f y) (Nil) (h x) (Cons z y) (g z))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(case (f y) (Cons x y) (g x) (Nil) (h x))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(case (f y) (Nil) (h x) (Cons z y) (g y))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(case (f y) (Null) (h x) (Cons z y) (g z))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(case (f y) (Cons a b) (g a) (Null) (h x))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(case (f y) (Null) (h x) (Cons z y) (q z))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(case (f y) (Cons a b) (g a) (Null) (h x))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    printf("exp, exp1 = %x %x\n", exp, exp1) ;
    printf("equal: %d\n", _th_equal(env, exp, exp1)) ;

    exp = _th_parse(env,"(f x y)") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(f (g a) (h b))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(f x y)") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(h (f a) (g b))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(f (f a) y)") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(f x (g b))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(f 1 y)") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(f 1 (g b))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(f 2 y)") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(f 1 (g b))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(ALL (x) (f x y))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(ALL (y) (f y x))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(ALL (x) (ALL (y) (f x y z)))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(ALL (y) (ALL (x) (f y x (g a b))))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(ALL (x) (ALL (y) (f x y z)))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(ALL (y) (ALL (x) (f x y (g a b))))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(ALL (x) (ALL (y) (f x y z)))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(ALL (y) (ALL (x) (f x (g a b) y)))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(ALL (x) (ALL (y z) (f x y z t)))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(ALL (y) (ALL (x z) (f y z x (g a b))))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(ALL (x) (ALL (y z) (f x y z t)))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(ALL (y) (ALL (x z) (f y x z (g a b))))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(ALL (x) (ALL (y z) (f x y z t)))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(ALL (y) (ALL (x z) (f y x x (g a b))))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(ALL (x) (ALL (y z) (f x y z t)))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(ALL (y) (ALL (x z) (f x y z (g a b))))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(f a a b)") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(f (g x) (g x) (h e))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(f a a b)") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(f (g x) (g y) (h e))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(ALL (x) (f a a x))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(ALL (y) (f (ALL (x) (e x)) (ALL (z) (e z)) y))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(ALL (x) (f a a x))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(ALL (y) (f (ALL (x) (e x q)) (ALL (z) (e z q)) y))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(ALL (x) (f a a x))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(ALL (y) (f (ALL (x) (e x y)) (ALL (z) (e z y)) y))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(== (f a) (g b))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(== (f a) (g b))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(== (f a) (g b))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(== (g a) (f b))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(== a b)") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(== (g a) (f b))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(&& (g b) (f a))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(&& (g a) (f b))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(&& (f b) (f a))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(&& (f a) (f b))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(&& b (f a))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(&& (g a) (f b))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(&& b a)") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(&& (g a) (f b))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(&& b a)") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(&& (g a) (f b) (h c))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(&& (f x) b a)") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(&& (g a) (f b) (h c) (f d))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(q a b (&& b a c))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(q (f x) (&& (g x) (f d)) (&& (f x) (g x) (f d) (q r) (s t)))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(q a b (&& b a c d))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(q (f x) (&& (g x) (f d)) (&& (f x) (g x) (f d) (q r) (s t) (u v)))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(case (f y) (Cons x y) (g x) (Nil) (h x))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(case (f j) (Nil) (h q) (Cons x y) (g x))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(case (f y) (Null) (h x) (Cons z y) (g z))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(case (f y) (Cons a b) (g a) (Null) (h q))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(case (f y) (Nil) (h x) (Cons z y) (g z))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(case (f y) (Cons a b) (g a) (Null) (h q))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    exp = _th_parse(env,"(case (f y) (Null) (h x) (Cons z y) (g q))") ;
    printf("exp: %s\n", _th_print_exp(exp)) ;
    exp1 = _th_parse(env,"(case (f y) (Cons a b) (g a) (Null) (h q))") ;
    printf("exp1: %s\n", _th_print_exp(exp1)) ;

    mr = _th_match(env, exp, exp1) ;
    print_match_result(mr) ;

    /* Precedence tests */
    _th_add_precedence(2,env,INTERN_OR,INTERN_AND) ;
    _th_add_precedence(2,env,INTERN_EQUAL,INTERN_OR) ;

    printf("Precedence test: %d %d %d %d %d %d %d %d %d\n",
           _th_has_smaller_precedence(env,INTERN_EQUAL,INTERN_EQUAL),
           _th_has_smaller_precedence(env,INTERN_EQUAL,INTERN_OR),
           _th_has_smaller_precedence(env,INTERN_EQUAL,INTERN_AND),
           _th_has_smaller_precedence(env,INTERN_OR,INTERN_EQUAL),
           _th_has_smaller_precedence(env,INTERN_OR,INTERN_OR),
           _th_has_smaller_precedence(env,INTERN_OR,INTERN_AND),
           _th_has_smaller_precedence(env,INTERN_AND,INTERN_EQUAL),
           _th_has_smaller_precedence(env,INTERN_AND,INTERN_OR),
           _th_has_smaller_precedence(env,INTERN_AND,INTERN_AND)) ;

    _th_add_precedence(2,env,INTERN_PLUS,INTERN_MINUS) ;
    _th_add_precedence(2,env,INTERN_MINUS,INTERN_STAR) ;

    printf("Precedence test2: %d %d %d %d %d %d %d %d %d\n",
           _th_has_smaller_precedence(env,INTERN_PLUS,INTERN_PLUS),
           _th_has_smaller_precedence(env,INTERN_PLUS,INTERN_MINUS),
           _th_has_smaller_precedence(env,INTERN_PLUS,INTERN_STAR),
           _th_has_smaller_precedence(env,INTERN_MINUS,INTERN_PLUS),
           _th_has_smaller_precedence(env,INTERN_MINUS,INTERN_MINUS),
           _th_has_smaller_precedence(env,INTERN_MINUS,INTERN_STAR),
           _th_has_smaller_precedence(env,INTERN_STAR,INTERN_PLUS),
           _th_has_smaller_precedence(env,INTERN_STAR,INTERN_MINUS),
           _th_has_smaller_precedence(env,INTERN_STAR,INTERN_STAR)) ;

    _th_add_equal_precedence(2,env,INTERN_MINUS,INTERN_PERCENT) ;

    printf("Precedence test3: %d %d %d %d %d %d %d %d %d\n",
           _th_has_smaller_precedence(env,INTERN_PLUS,INTERN_PLUS),
           _th_has_smaller_precedence(env,INTERN_PLUS,INTERN_PERCENT),
           _th_has_smaller_precedence(env,INTERN_PLUS,INTERN_STAR),
           _th_has_smaller_precedence(env,INTERN_PERCENT,INTERN_PLUS),
           _th_has_smaller_precedence(env,INTERN_PERCENT,INTERN_MINUS),
           _th_has_smaller_precedence(env,INTERN_PERCENT,INTERN_STAR),
           _th_has_smaller_precedence(env,INTERN_STAR,INTERN_PLUS),
           _th_has_smaller_precedence(env,INTERN_STAR,INTERN_PERCENT),
           _th_has_smaller_precedence(env,INTERN_STAR,INTERN_STAR)) ;

    _th_add_equal_precedence(2,env,INTERN_SLASH,INTERN_MINUS) ;

    printf("Precedence test4: %d %d %d %d %d %d %d %d %d\n",
           _th_has_smaller_precedence(env,INTERN_PLUS,INTERN_PLUS),
           _th_has_smaller_precedence(env,INTERN_PLUS,INTERN_SLASH),
           _th_has_smaller_precedence(env,INTERN_PLUS,INTERN_STAR),
           _th_has_smaller_precedence(env,INTERN_SLASH,INTERN_PLUS),
           _th_has_smaller_precedence(env,INTERN_SLASH,INTERN_MINUS),
           _th_has_smaller_precedence(env,INTERN_SLASH,INTERN_STAR),
           _th_has_smaller_precedence(env,INTERN_STAR,INTERN_PLUS),
           _th_has_smaller_precedence(env,INTERN_STAR,INTERN_SLASH),
           _th_has_smaller_precedence(env,INTERN_STAR,INTERN_STAR)) ;

    _th_add_minor_precedence(2,env,INTERN_OR,INTERN_AND) ;
    _th_add_minor_precedence(2,env,INTERN_EQUAL,INTERN_OR) ;

    printf("Precedence test5: %d %d %d %d %d %d %d %d %d\n",
           _th_has_smaller_minor_precedence(env,INTERN_EQUAL,INTERN_EQUAL),
           _th_has_smaller_minor_precedence(env,INTERN_EQUAL,INTERN_OR),
           _th_has_smaller_minor_precedence(env,INTERN_EQUAL,INTERN_AND),
           _th_has_smaller_minor_precedence(env,INTERN_OR,INTERN_EQUAL),
           _th_has_smaller_minor_precedence(env,INTERN_OR,INTERN_OR),
           _th_has_smaller_minor_precedence(env,INTERN_OR,INTERN_AND),
           _th_has_smaller_minor_precedence(env,INTERN_AND,INTERN_EQUAL),
           _th_has_smaller_minor_precedence(env,INTERN_AND,INTERN_OR),
           _th_has_smaller_minor_precedence(env,INTERN_AND,INTERN_AND)) ;

    _th_add_minor_precedence(2,env,INTERN_PLUS,INTERN_MINUS) ;
    _th_add_minor_precedence(2,env,INTERN_MINUS,INTERN_STAR) ;

    printf("Precedence test6: %d %d %d %d %d %d %d %d %d\n",
           _th_has_smaller_minor_precedence(env,INTERN_PLUS,INTERN_PLUS),
           _th_has_smaller_minor_precedence(env,INTERN_PLUS,INTERN_MINUS),
           _th_has_smaller_minor_precedence(env,INTERN_PLUS,INTERN_STAR),
           _th_has_smaller_minor_precedence(env,INTERN_MINUS,INTERN_PLUS),
           _th_has_smaller_minor_precedence(env,INTERN_MINUS,INTERN_MINUS),
           _th_has_smaller_minor_precedence(env,INTERN_MINUS,INTERN_STAR),
           _th_has_smaller_minor_precedence(env,INTERN_STAR,INTERN_PLUS),
           _th_has_smaller_minor_precedence(env,INTERN_STAR,INTERN_MINUS),
           _th_has_smaller_minor_precedence(env,INTERN_STAR,INTERN_STAR)) ;

    /* Test the discrimination net stuff */
    d = _th_new_disc(2) ;
    exp = _th_parse(env, "(-> (f (g x) y) (q r) True)") ;
    _th_add_disc(2, d, exp) ;
    exp = _th_parse(env, "(-> (g (f x) (h y)) (q r) True)") ;
    _th_add_disc(2, d, exp) ;
    exp = _th_parse(env, "(-> (f (h x) (g y)) (q r) True)") ;
    _th_add_disc(2, d, exp) ;

    exp = _th_parse(env, "(f (g x) y)") ;
    printf("Exp: %s\n", _th_print_exp(exp)) ;
    printf("Rules:\n") ;
    _th_init_find(d, exp) ;
    while(exp = _th_next_find()) {
        printf("    %s\n", _th_print_exp(exp)) ;
    }

    exp = _th_parse(env, "(f (h x) y)") ;
    printf("Exp: %s\n", _th_print_exp(exp)) ;
    printf("Rules:\n") ;
    _th_init_find(d, exp) ;
    while(exp = _th_next_find()) {
        printf("    %s\n", _th_print_exp(exp)) ;
    }

    exp = _th_parse(env, "(g (f x) (h y))") ;
    printf("Exp: %s\n", _th_print_exp(exp)) ;
    printf("Rules:\n") ;
    _th_init_find(d, exp) ;
    while(exp = _th_next_find()) {
        printf("    %s\n", _th_print_exp(exp)) ;
    }

    exp = _th_parse(env, "(f x y)") ;
    printf("Exp: %s\n", _th_print_exp(exp)) ;
    printf("Rules:\n") ;
    _th_init_find(d, exp) ;
    while(exp = _th_next_find()) {
        printf("    %s\n", _th_print_exp(exp)) ;
    }

    s = _th_new_small(2);
    exp = _th_parse(env, "(-> (f (g x) y) (q r) True)") ;
    _th_add_small(2, s, exp) ;
    exp = _th_parse(env, "(-> (g (f x) (h y)) (q r) True)") ;
    _th_add_small(2, s, exp) ;
    exp = _th_parse(env, "(-> (f (h x) (g y)) (q r) True)") ;
    _th_add_small(2, s, exp) ;

    exp = _th_parse(env, "(f (g x) y)") ;
    printf("Exp: %s\n", _th_print_exp(exp)) ;
    printf("Rules:\n") ;
    _th_init_find_small(s, exp) ;
    while(exp = _th_next_find_small()) {
        printf("    %s\n", _th_print_exp(exp)) ;
    }

    exp = _th_parse(env, "(f (h x) y)") ;
    printf("Exp: %s\n", _th_print_exp(exp)) ;
    printf("Rules:\n") ;
    _th_init_find_small(s, exp) ;
    while(exp = _th_next_find_small()) {
        printf("    %s\n", _th_print_exp(exp)) ;
    }

    exp = _th_parse(env, "(g (f x) (h y))") ;
    printf("Exp: %s\n", _th_print_exp(exp)) ;
    printf("Rules:\n") ;
    _th_init_find_small(s, exp) ;
    while(exp = _th_next_find_small()) {
        printf("    %s\n", _th_print_exp(exp)) ;
    }

    exp = _th_parse(env, "(f x y)") ;
    printf("Exp: %s\n", _th_print_exp(exp)) ;
    printf("Rules:\n") ;
    _th_init_find_small(s, exp) ;
    while(exp = _th_next_find_small()) {
        printf("    %s\n", _th_print_exp(exp)) ;
    }

    /* Test of rewriting */
    exp = _th_parse(env, "(-> (f x y) (g (h x)) (True))") ;
    printf("rule: %s\n", _th_print_exp(exp)) ;
    _th_add_property(2,env,exp) ;

    exp = _th_parse(env, "(f (g x) y)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_rewrite_rule(env, exp) ;
    printf("rewrite: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env, "(-> (&& (f x) (g y)) (h x y) (True))") ;
    printf("rule: %s\n", _th_print_exp(exp)) ;
    _th_add_property(2,env,exp) ;

    exp = _th_parse(env, "(&& (f (h x)) (g (i y)))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_rewrite_rule(env, exp) ;
    printf("rewrite: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env, "(&& (f (h x)) (g (i y)) (z q))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_rewrite_rule(env, exp) ;
    printf("rewrite: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env, "(-> (&& (f x) (h y)) (&& x y) (True))") ;
    printf("rule: %s\n", _th_print_exp(exp)) ;
    _th_add_property(2,env,exp) ;

    exp = _th_parse(env, "(&& (f (g x)) (h (i y)) (z q))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_rewrite_rule(env, exp) ;
    printf("rewrite: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env, "(-> (q x z) (g x) (True))") ;
    printf("rule: %s\n", _th_print_exp(exp)) ;
    _th_add_context_property(2,env,exp) ;

    exp = _th_parse(env, "(q (f x) (g y))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_rewrite_rule(env, exp) ;
    printf("rewrite: %s\n", _th_print_exp(exp)) ;

    /* builtin */
    exp = _th_parse(env,"(&& (False) a b c)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(|| (False) a b c)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(&& (True) a b c)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(|| (True) a b c)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(&& c a b c)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(|| c a b c)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(&& c)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(|| c)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(&&)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(||)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(not (True))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(not (False))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(not (&& a b c))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(not (|| a b c))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(== (nplus a b c) (nplus d e f))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(== (nplus a b c) x)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(== f (nplus a b c))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(== (True) (True))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(== (True) (False))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(== (Cons a b) (Cons c d))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(== (Cons a b) (Nil))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(size \"abc\")") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(char \"abc\" 0)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(char \"abc\" 4)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(concat 97 \"abc\")") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(concat 97 \"abcd\")") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(nminus 5 3)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(nminus 5 x)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(ndivide 5 2)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(nmod 5 2)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(nplus 5 2 3)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(nplus 5 2 3 x)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(ntimes 5 2 3)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(ntimes 5 2 3 x)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(rplus #5/2 #4/3)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(rtimes #5/2 #4/3)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(rdivide #5/2 #4/3)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(rminus #5/2 #4/3)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(rless #5/2 #4/3)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(rless #4/3 #5/2)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    _th_add_type_definition(2,env, _th_parse(env,"(List a)"), _th_parse(env,"(| (Nil) (Cons a (List a)))")) ;
    _th_add_type_definition(2,env, _th_parse(env,"(Bool)"), _th_parse(env,"(| (True) (False))")) ;

    printf("prec: %d\n", _th_has_smaller_precedence(env,_th_intern("Nil"),_th_intern("Cons"))) ;
    printf("prec: %d\n", _th_has_smaller_precedence(env,_th_intern("Cons"),_th_intern("Nil"))) ;

    exp = _th_parse(env,"(preceq (Nil) (Cons a b))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(preceq (a) (Cons a b))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(preceq a (Cons a b))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(preceq 4 (Cons 4 b))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(preceq a' (Cons a b))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(ALL(x : (e x)) (&& (f x) (g x)))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(ALL(x : (e x)) (not (f x)))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(EXISTS(x) (|| (f x) (g x)))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(EXISTS(x) (not (f x)))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(EXISTS(x) (== x (f y)))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(EXISTS(x) (== x (f (g x y))))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(EXISTS(x) (== (f y) x))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(EXISTS(x) (== (f (g x y)) x))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(lambda x (apply (f y) x))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(lambda x (apply (f x) x))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(apply (lambda x (f x y)) (g z))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(EXISTS(z) (== (f y) x))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(ALL(z : (f q)) (== (f y) x))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(ALL(z : (f z)) (== (f y) x))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(EXISTS (a) (&& (== a (f x)) (g a b)))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(defined (Cons a b))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    _th_add_function(2,env,_th_parse(env,"(&& a b)"),NULL,_th_parse(env,"(== a b)"),0,NULL) ;

    exp = _th_parse(env,"(defined (&& a b))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(defined (&& a b c))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(case (case (f x) (True) (q x) (False) (r x))(True) (g x) (False) (h x))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(case (True) (True) (g x) (False) (h x))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(case (False) (True) (g x) (False) (h x))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(case (Cons a b) (Nil) (g x) (Cons a b) (h x))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(case (Cons a b) (Nil) (g x) (Cons a (Cons b c)) (h x) (Cons a b) (i a))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(case (Cons a b) (Nil) (g x) (Cons a (Nil)) (h x) (Cons (Nil) c) (i c))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(case (Cons a b) (Nil) (g x) (Cons a (Nil)) (h x) (Cons (Nil) a) (i a))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(case (Cons a b) a (g a))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(case (q a b) a (g a))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(case (qr x) (True) (case (f x) (True) a (False) b) (False) c)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(case (f x) (True) (case (qr x) (True) a (False) b) (False) c)") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(union (Set a b c) (Set c d e))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(intersect (Set a b c) (Set c d e))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(intersect (Set a b x) (Set c d e))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(intersect (Set a b x q) (Set c x d q e))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(Set (x) (|| (f x) (g x)))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(Set (x) (&& (f x) (g x)))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(Set (x y) (f x))") ;
    printf("orig: %s\n", _th_print_exp(exp)) ;
    exp = _th_builtin(env, exp) ;
    printf("builtin: %s\n", _th_print_exp(exp)) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_EQUAL ;
    _th_add_attrib(2,env,INTERN_EQ,1,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_PRECEQ ;
    parameters[1].type = SYMBOL_PARAMETER ;
    parameters[1].u.symbol = INTERN_EQUAL ;
    _th_add_attrib(2,env,INTERN_ETO,2,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_EQUAL ;
    parameters[1].type = SYMBOL_PARAMETER ;
    parameters[1].u.symbol = INTERN_PRECEQ ;
    _th_add_attrib(2,env,INTERN_EF,2,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_NAT_LESS ;
    parameters[1].type = SYMBOL_PARAMETER ;
    parameters[1].u.symbol = INTERN_EQUAL ;
    _th_add_attrib(2,env,INTERN_TO,2,parameters) ;

    parameters[0].type = SYMBOL_PARAMETER ;
    parameters[0].u.symbol = INTERN_EQUAL ;
    parameters[1].type = SYMBOL_PARAMETER ;
    parameters[1].u.symbol = INTERN_NAT_LESS ;
    _th_add_attrib(2,env,INTERN_EF,2,parameters) ;

    printf("Finding1\n") ;
    _th_get_attrib(env,INTERN_EF,1,parameters) ;
    while(params = _th_get_next_attrib(&i)) {
        printf("Found %d %d %d\n", i, params[0].u.symbol,params[1].u.symbol) ;
    }
    printf("Finding2\n") ;
    _th_get_attrib(env,INTERN_EF,1,parameters) ;
    parameters[0].u.symbol = INTERN_NAT_LESS ;
    while(params = _th_get_next_attrib(&i)) {
        printf("Found %d %d %d\n", i, params[0].u.symbol,params[1].u.symbol) ;
    }

    _th_transitive_init () ;
    _th_trans_push(env) ;
    _th_add_rule(env, _th_parse(env,"(-> (preceq a b) (True) (True))")) ;
    _th_add_rule(env, _th_parse(env,"(-> (preceq b c) (True) (True))")) ;
    exp = _th_transitive(env,_th_parse(env,"(preceq a c)")) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    exp = _th_transitive(env,_th_parse(env,"(preceq c a)")) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    _th_trans_pop() ;
    _th_trans_push(env) ;
    _th_add_rule(env, _th_parse(env,"(-> (nless a 5) (True) (True))")) ;
    _th_add_rule(env, _th_parse(env,"(-> (nless b a) (True) (True))")) ;
    exp = _th_transitive(env,_th_parse(env,"(nless b 7)")) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;

    parameters[0].u.exp = _th_parse(env,"(f a)") ;
    parameters[0].type = EXP_PARAMETER ;
    parameters[1].u.exp = _th_parse(env,"a)") ;
    parameters[1].type = EXP_PARAMETER ;
    parameters[2].u.symbol = INTERN_NAT_LESS ;
    parameters[2].type = SYMBOL_PARAMETER ;
    parameters[3].u.symbol = INTERN_EQUAL ;
    parameters[3].type = SYMBOL_PARAMETER ;
    _th_add_attrib(2,env,INTERN_SMI,5,parameters) ;

    exp = _th_transitive(env,_th_parse(env,"(nless x (f x))")) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;

    exp = _th_transitive(env,_th_parse(env,"(nless (f x) x)")) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;

    _th_trans_pop() ;

    /* Test of rewriting */
    exp = _th_parse(env, "(-> (g x) (q (q x)) (True))") ;
    printf("rule: %s\n", _th_print_exp(exp)) ;
    _th_add_property(2,env,exp) ;

    exp = _th_parse(env,"(f a b)") ;
    exp = _th_rewrite(env,exp) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(&& (f a) (g (f a)))") ;
    exp = _th_rewrite(env,exp) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(&& (f a) (ALL (x) (g (f a))))") ;
    exp = _th_rewrite(env,exp) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(&& (f a) (ALL (x) (h x (g (f a)))))") ;
    exp = _th_rewrite(env,exp) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(&& (f a) (ALL (a) (h x (g (f a)))))") ;
    exp = _th_rewrite(env,exp) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(&& (f b) (ALL (b) (h x (g (f b)))))") ;
    exp = _th_rewrite(env,exp) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(&& (nless x y) (nless y x))") ;
    exp = _th_rewrite(env,exp) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(env,"(&& (nless x y) (nless y x) (f a b))") ;
    exp = _th_rewrite(env,exp) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;

    def = _th_default_env(2) ;

    exp = _th_parse(def,"(ntimes a (nplus (f x) (g y)))") ;
    exp = _th_rewrite(def,exp) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(def,"(nplus (ntimes 5 a) (ntimes 6 a))") ;
    exp = _th_rewrite(def,exp) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(def,"(nplus (ntimes 5 a) (ntimes 6 a) c)") ;
    exp = _th_rewrite(def,exp) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(def,"(nplus (ntimes 5 a) (ntimes x a))") ;
    exp = _th_rewrite(def,exp) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(def,"(nplus (ntimes 5 (f x)) (f x))") ;
    exp = _th_rewrite(def,exp) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;

    exp = _th_parse(def,"(nplus (ntimes 5 (f x)) (f x) c)") ;
    exp = _th_rewrite(def,exp) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;

    /* Big number operations */
    big1[0] = 2 ;
    big1[1] = 0xffffffff ;
    big1[2] = 0x80000001 ;
    big2[0] = 3 ;
    big2[1] = 1 ;
    big2[2] = 1 ;
    big2[3] = 1 ;
    bigres = _th_big_add(big1,big2) ;
    printf("big res #1 =") ; _th_big_print_hex(bigres) ;

    big1[0] = 2 ;
    big1[1] = 0xffffffff ;
    big1[2] = 0x80000001 ;
    big2[0] = 4 ;
    big2[1] = 1 ;
    big2[2] = 1 ;
    big2[3] = 1 ;
    big2[4] = 1 ;
    bigres = _th_big_add(big1,big2) ;
    printf("big res #2 =") ; _th_big_print_hex(bigres) ;

    bigres = _th_big_add(big2,big1) ;
    printf("big res #3 =") ; _th_big_print_hex(bigres) ;

    big1[0] = 2 ;
    big1[1] = 0x1 ;
    big1[2] = 0x1 ;
    big2[0] = 3 ;
    big2[1] = 1 ;
    big2[2] = 1 ;
    big2[3] = 1 ;
    bigres = _th_big_add(big1,big2) ;
    printf("big res #4 =") ; _th_big_print_hex(bigres) ;

    big1[0] = 2 ;
    big1[1] = 0xffffffff ;
    big1[2] = 0x1 ;
    big2[0] = 3 ;
    big2[1] = 1 ;
    big2[2] = 0xffffffff ;
    big2[3] = 1 ;
    bigres = _th_big_add(big1,big2) ;
    printf("big res #5 =") ; _th_big_print_hex(bigres) ;

    bigres = _th_big_add(big2,big1) ;
    printf("big res #6 =") ; _th_big_print_hex(bigres) ;

    big1[0] = 2 ;
    big1[1] = 0xffffffff ;
    big1[2] = 0x1 ;
    big2[0] = 3 ;
    big2[1] = 1 ;
    big2[2] = 0x2 ;
    big2[3] = 0 ;
    bigres = _th_big_add(big1,big2) ;
    printf("big res #7 =") ; _th_big_print_hex(bigres) ;

    big1[0] = 4 ;
    big1[1] = 0xffffffff ;
    big1[2] = 0x1 ;
    big1[3] = 0xffffffff ;
    big1[4] = 0xffffffff ;
    big2[0] = 4 ;
    big2[1] = 1 ;
    big2[2] = 0x2 ;
    big2[3] = 0 ;
    big2[4] = 0 ;
    bigres = _th_big_add(big1,big2) ;
    printf("big res #8 =") ; _th_big_print_hex(bigres) ;

    big1[0] = 2 ;
    big1[1] = 3 ;
    big1[2] = 1 ;
    big2[0] = 2 ;
    big2[1] = 1 ;
    big2[2] = 1 ;
    bigres = _th_big_sub(big1,big2) ;
    printf("big res #9 =") ; _th_big_print_hex(bigres) ;

    bigres = _th_big_sub(big2,big1) ;
    printf("big res #10 =") ; _th_big_print_hex(bigres) ;

    big1[0] = 4 ;
    big1[1] = 1 ;
    big1[2] = 1 ;
    big1[3] = 0 ;
    big1[4] = 1 ;
    big2[0] = 2 ;
    big2[1] = 3 ;
    big2[2] = 1 ;
    bigres = _th_big_sub(big1,big2) ;
    printf("big res #11 =") ; _th_big_print_hex(bigres) ;

    bigres = _th_big_sub(big2,big1) ;
    printf("big res #12 =") ; _th_big_print_hex(bigres) ;

    big1[0] = 2 ;
    big1[1] = 0x10001000 ;
    big1[2] = 0x1 ;
    big2[0] = 2 ;
    big2[1] = 1 ;
    big2[2] = 1 ;

    bigres = _th_big_multiply(big2,big1) ;
    printf("big res #13 =") ; _th_big_print_hex(bigres) ;

    big1[0] = 1 ;
    big1[1] = 6 ;
    big2[0] = 1 ;
    big2[1] = 3 ;

    bigres = _th_big_divide(big1,big2) ;
    printf("big res #14 =") ; _th_big_print_hex(bigres) ;

    big1[0] = 2 ;
    big1[1] = 6 ;
    big1[2] = 6 ;
    big2[0] = 1 ;
    big2[1] = 3 ;

    bigres = _th_big_divide(big1,big2) ;
    printf("big res #15 =") ; _th_big_print_hex(bigres) ;

    /* Type checking tests */
    exp1 = _ex_intern_appl(INTERN_BOOL,0,NULL) ;

    exp = _ex_intern_appl(INTERN_TRUE,0,NULL) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _ex_intern_small_integer(5) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(&& (True) x)") ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(&& 5 x)") ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(&& (== 3 5) x)") ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(&& (== 3 e) x)") ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(&& (== 3 x) x)") ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(&& (== 3 (True)) x)") ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    _th_add_type_definition(2,def,_th_parse(def,"(List x)"), _th_parse(def,"(| (Nil) (Cons x (List x)))")) ;

    exp = _th_parse(def,"(Cons 4 (Nil))") ;
    exp1 = _th_parse(def,"(List x)") ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(Cons 4 (Cons 5 (Nil)))") ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(Cons 4 (Cons (True) (Nil)))") ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(ALL (x: (nless x 3)) (nless x 2))") ;
    exp1 = _ex_intern_appl(INTERN_BOOL,0,NULL) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(ALL (x: (nless x 3)) (== x (True)))") ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(ALL (x: (== x (False))) (== x (True)))") ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(EXISTS (x) (== x (True)))") ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(SET (x: (nless x 3)) x)") ;
    exp1 = _th_parse(def,"(Set (Int))") ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(SET (x: (== x (True))) x)") ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(case (== x 3) (True) (nplus x 1) (False) (nplus x 2))") ;
    exp1 = _ex_intern_appl(INTERN_BOOL,0,NULL) ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(case (== x 3) (True) (True) (False) (nplus x 2))") ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(case x (Cons a b) b (Nil) (Nil))") ;
    exp1 = _th_parse(def,"(List x)") ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    exp = _th_parse(def,"(case x (Cons a b) b (Nil) 5)") ;
    exp1 = _th_parse(def,"(List x)") ;
    printf("exp = %s\n", _th_print_exp(exp)) ;
    printf("type = %x\n", _th_checkTyping(def, exp1, exp)) ;

    printf("START\n") ;
    do {
        printf("> ") ;
        fflush(stdout) ;
        gets(line) ;
    } while (!_th_process(line)) ;

    /* Shutdown */
    _th_print_shutdown() ;
    _ex_shutdown() ;
    _th_intern_shutdown () ;
    _th_alloc_shutdown() ;
}

#else

void break_handler(int x)
{
    _th_break_pressed = 1 ;
}

static int preprocess_flag = 0;
static int print_failures = 0;

main(argc, argv)
int argc ;
char *argv[] ;
{
    //char line[80] ;
    int change = 0;

    //signal(SIGINT,break_handler);

    fprintf(stderr, "Heuristic Theorem Prover (Version 2.1, Jan 1, 2008)\n\n");
    fprintf(stderr, "(C) 2008, Kenneth Roe and Formal Documentation Systems\n");
    fprintf(stderr, "All rights reserved\n\n");
    fprintf(stderr, "Prerelease version for research purposes only.\n");

    //if (time(NULL) > EXPIRATION) {
    //    fprintf(stderr, "This version is expired\n");
    //    exit(1);
    //}

    fflush(stderr);

    _th_init_rewrite("evidence") ;
    _tree_print0("log");
    _th_command_init() ;
    _th_init_term_cache() ;

#ifdef XX
    if (argc > 1 && isdigit(argv[1][0])) {
        _tree_start = atoi(argv[1]) ;
        ++argv ;
        --argc ;
        if (argc > 1 && isdigit(argv[1][0])) {
            _tree_end = atoi(argv[1]) ;
            ++argv ;
            --argc ;
        } else {
            _tree_end = _tree_start ;
        }
    }
#endif
    
    do {
        change = 0;
#ifdef XX
        if (argc > 2 && !strcmp(argv[1],"-s")) {
            ++argv ;
            --argc ;
#ifndef FAST
            _tree_sub = _tree_sub2 = atoi(argv[1]) ;
#endif
            ++argv ;
            --argc ;
            if (isdigit(argv[1][0])) {
#ifndef FAST
                _tree_sub2 = atoi(argv[1]) ;
#endif
                ++argv ;
                --argc ;
            }
            change = 1;
        }

        if (argc > 1 && !strcmp(argv[1],"-core")) {
            ++argv ;
            --argc ;
#ifndef FAST
            _tree_core = 1 ;
#endif
            change = 1;
        }
#endif

        if (argc > 2 && !strncmp(argv[1],"-t",2)) {
            _tree_set_time_limit(atoi(argv[2]));
            argv += 2;
            argc -= 2;
            change = 1;
        } else  if (argc > 2 && !strncmp(argv[1],"-l",2)) {
            _th_do_learn = atoi(argv[2]);
            argv += 2;
            argc -= 2;
            change = 1;
        } else

        //if (argc > 2 && !strncmp(argv[1],"-ec",3)) {
        //    _th_use_transitive = atoi(argv[2]);
        //    argv += 2;
        //    argc -= 2;
        //    change = 1;
        //}

        if (argc > 1 && !strncmp(argv[1],"-s",2)) {
            _th_do_symmetry = 1;
            argv += 1;
            argc -= 1;
            change = 1;
        } else if (argc > 1 && !strncmp(argv[1],"-h",2)) {
            printf("HTP options:\n");
            printf("    -h   - print this message.\n");
			printf("    -f   - print conditions in sat case\n");
            printf("    -t n - set execution time limit to n seconds.\n");
            printf("    -l n - if n is zero disables all learning, if n > 0 enables\n");
            printf("           learning and restarts after <number> seconds.\n");
            printf("    -s   - Enables symmetry detection in the preprocessor.\n");
            printf("    -p   - Preprocessor mode.  HTP rewrites its input file to an\n");
            printf("           output file with the same name plus \".out\" and possibly\n");
            printf("           a file with the same name plus \".cnf\" if the result is a boolean\n");
            printf("           expression.\n");
            printf("    -pr  - Preprocessor autorun mode.  HTP rewrites its input file to an\n");
            printf("           output file with the same name plus \".out\" and possibly\n");
            printf("           a file with the same name plus \".cnf\" if the result is a boolean\n");
            printf("           expression.  Then either Yices or MiniSat are run on the result.\n");
            printf("    -o   - Output the input file.  Useful for pretty printing.\n");
            printf("    -e   - only eliminate unates of the form \"v = e\" when running\n");
            printf("           HTP as a preprocessor.\n");
            printf("    -b   - Block big groups in the difference logic encoder\n");
            exit(0);
        } else if (argc > 1 && !strncmp(argv[1],"-e",2)) {
            _th_equality_only = 1;
            argv += 1;
            argc -= 1;
            change = 1;
		} else if (argc > 1 && !strncmp(argv[1],"-f",2)) {
			print_failures = 1;
			argv += 1;
			argc -= 1;
			change = 1;
        } else if (argc > 1 && !strncmp(argv[1],"-o",2)) {
            preprocess_flag = -1;
            argv += 1;
            argc -= 1;
            change = 1;
        } else if (argc > 1 && !strncmp(argv[1],"-pr",3)) {
            preprocess_flag = 2;
            argv += 1;
            argc -= 1;
            change = 1;
        } else if (argc > 1 && !strncmp(argv[1],"-p",2)) {
            preprocess_flag = 1;
            argv += 1;
            argc -= 1;
            change = 1;
        } else if (argc > 1 && !strncmp(argv[1],"-b",2)) {
            argv += 1;
            argc -= 1;
            _th_block_bigs = 1;
            change = 1;
        } else if (argc > 1 && argv[1][0]=='-') {
            printf("Unrecognized option.  Enter \"prove -h\" for options.\n");
            exit(1);
        }

    } while (change);

	//if (change) {
	//	return Minisat_main(argc, argv);
	//}

    //_tree_start = 1;
    //_tree_end = 19160;
    //_tree_sub = -1;
    //_tree_sub2 = -1;
    //_tree_core = 1;

    //if (argc==2 && !strcmp(argv[1],"-ui")) {
    //    printf("START\n") ;
    //    do {
    //        printf("> ") ;
    //        fflush(stdout) ;
    //        line[0]= 0 ;
    //        gets(line) ;
    //        printf("%s\n", line) ;
    //    } while (!_th_process(line) && !feof(stdin)) ;
    if (argc==2 && !strcmp(argv[1]+strlen(argv[1])-4,".svc")) {
        struct env *env = _th_default_env(ENVIRONMENT_SPACE);
        int res = _th_svcs(env,argv[1]);
        _th_command_shutdown() ;
        _th_shutdown_rewrite() ;
        exit(res);
    //} else if (argc==2 && !strcmp(argv[1],"-cmd")) {
    //    struct env *env = _th_default_env(ENVIRONMENT_SPACE) ;//
        //_tree_interactive = 1// ;
//#ifndef FAST
//        _tree_start = 0;
//        _tree_end = 2000000;
//        _tree_sub = -1;
//        _tree_sub2 = -1;
//#endif
        //_tree_print0("Interactive");
        //_th_process_file(env, "stdin", stdin) ;
    } else if (argc==2) {
        struct env *env = _th_default_env(ENVIRONMENT_SPACE);
        int res;
        if (preprocess_flag < 0) {
            res = _th_print_smt(env,argv[1]);
        } else if (preprocess_flag==1) {
            res = _th_preprocess_smt(env,argv[1]);
        } else if (preprocess_flag==2) {
            res = _th_smt_autorun(env,argv[1]);
        } else {
            res = _th_smt(env,argv[1],print_failures);
        }
        _th_command_shutdown() ;
        _th_shutdown_rewrite() ;
        exit(res);
    //} else if (argc==2 && !strcmp(argv[1],"-cmd")) {
        //struct env *env = _th_default_env(ENVIRONMENT_SPACE) ;
        //_tree_interactive = 1 ;
//#ifndef FAST
//        _tree_start = 0;
//        _tree_end = 2000000;
//        _tree_sub = -1;
//        _tree_sub2 = -1;
//#endif
        //_tree_print0("Interactive");
        //_th_process_file(env, "stdin", stdin) ;
#ifdef XX
    } else if (argc==2) {
        struct env *env = _th_default_env(ENVIRONMENT_SPACE) ;
        struct entry *e ;
        char name[1000] ;
        /*char *x = getenv("PROVEHOME") ;*/
        char *x = "C:\\c-engine" ;
        FILE *file ;
        struct _ex_intern *prog ;
#ifndef FAST
        _debug_print("Reading initialization files") ;
#endif
        _tree_indent() ;
        sprintf(name, "%s\\defs\\basic.ld", x) ;
        file = fopen(name, "r") ;
        if (file==NULL) {
            printf("File %s not found\n", name) ;
            exit(1) ;
        }
        env = _th_process_file(env, name, file) ;
        fclose(file) ;
        //sprintf(name, "%s\\defs\\c.ld", x) ;
        //file = fopen(name, "r") ;
        //if (file==NULL) {
        //    printf("File %s not found\n", name) ;
        //    exit(1) ;
        //}
        //env = _th_process_file(env, name, file) ;
        //fclose(file) ;
        sprintf(name, "cl /I \\c-engine\\include /E /C %s > tmp", argv[1]) ;
        system(name) ;
        file = fopen("tmp","r") ;
        if (file==NULL) {
            printf("File %s not found\n", argv[1]) ;
            exit(1) ;
        }
        _th_read_file(file) ;
        system("erase tmp") ;
        _tree_undent() ;
        prog = _th_pp_parse_mode(argv[1], env, _th_intern("decl"), _th_source_buffer) ;
#ifndef FAST
        _d_print1("Prog:\n%s\n", _th_print_exp(prog)) ;
#endif
        fflush(stdout) ;
        _th_do_context_rewrites = 0 ;
        prog = _th_rewrite(env, prog) ;
        _th_do_context_rewrites = 1 ;
        _d_print1("Prog:\n%s\n", _th_print_exp(prog)) ;

#ifdef MAKE_LOG
        rewrite_log = fopen("rewrite.log","w") ;
#endif

        e = _th_compile(DERIVATION_BASE,env,prog) ;
#ifdef _DEBUG
        //printf("expression %s\n", _th_pp_print(env, INTERN_DEFAULT, 80, e)) ;
        //fflush(stdout) ;
        _th_print_assembly(e) ;
#endif
        printf("Verifying\n") ;
        fflush(stdout) ;
        //_th_verify(DERIVATION_BASE,env,e) ;
        printf("Done verifying\n") ;
        fflush(stdout) ;
#ifdef MAKE_LOG
        fclose(rewrite_log) ;
#endif
#endif
    } else {
        struct env *env = _th_default_env(ENVIRONMENT_SPACE);
        int res;
        if (preprocess_flag < 0) {
            res = _th_print_smt(env,argv[1]);
        } else if (preprocess_flag) {
            res = _th_preprocess_smt(env,NULL);
        } else {
            res = _th_smt(env,NULL,print_failures);
        }
        _th_command_shutdown() ;
        _th_shutdown_rewrite() ;
        exit(res);
    }
    
    _th_command_shutdown() ;
    _th_shutdown_rewrite() ;
}

#endif
