/*
 * RewriteLog.h
 *
 * 7/12/3
 *
 * Macros for logging rewrite commands
 *
 * (C) 2003, Kenneth Roe
 *
 * Confidential and proprietary information.  May not be used or distributed
 * except as stated in an agreement controlling such use and distribution.
 */

/*#define MAKE_LOG*/

#ifdef MAKE_LOG
FILE *rewrite_log ;

struct _ex_intern *_th_log_rewrite(struct env *env, struct _ex_intern *exp) ;
struct _ex_intern *_th_log_int_rewrite(struct env *env, struct _ex_intern *exp, int flags) ;
char *_th_log_derive_push(struct env *env) ;
void _th_log_derive_pop(struct env *env) ;
void _th_log_derive_pop_release(struct env *env,unsigned char *mark) ;
void _th_log_derive_and_add(struct env *env, struct _ex_intern *exp) ;
char *_th_log_start_rewrite() ;
struct _ex_intern *_th_log_finish_rewrite(mark,env,exp) ;
void _th_log_add_attrib(int space, struct env *env, unsigned attrib, unsigned n, struct parameter *params) ;
void _th_log_derive_and_add_property(int space, struct env *env, struct _ex_intern *prop) ;
void _th_log_add_precedence(int space, struct env *env, unsigned a, unsigned b) ;
void _th_log_add_equal_precedence(int space, struct env *env, unsigned a, unsigned b) ;
void _th_log_add_max_precedence(int space,struct env *env, unsigned a) ;

#else

#define _th_log_rewrite(env,exp) _th_rewrite(env,exp)
#define _th_log_int_rewrite(env,exp,flags) _th_int_rewrite(env,exp,flags)
#define _th_log_derive_push(env) _th_derive_push(env)
#define _th_log_derive_pop(env)  _th_derive_pop(env)
#define _th_log_derive_pop_release(env,mark)  _th_derive_pop_release(env,mark)
#define _th_log_derive_and_add(env,exp) _th_derive_and_add(env,exp)
#define _th_log_start_rewrite() _th_start_rewrite()
#define _th_log_finish_rewrite(mark,env,exp) _th_finish_rewrite(mark,env,exp)
#define _th_log_add_attrib(space,env,attrib,n,params) _th_add_attrib(env,attrib,n,params)
#define _th_log_derive_and_add_property(space,env,prop) _th_derive_and_add_property(space,env,prop)
#define _th_log_add_precedence(space,env,a,b) _th_add_precedence(space,env,a,b)
#define _th_log_add_equal_precedence(space,env,a,b) _th_add_equal_precedence(space,env,a,b)
#define _th_log_add_max_precedence(space,env,a) _th_add_max_precedence(space,env,1)

#endif
