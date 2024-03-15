#//////////////////////////////////////////////////////////////////////////////
#/                                                                           //
#/  Copyright (C) 1995-2002 by the Board of Trustees of Leland Stanford      //
#/  Junior University.  See LICENSE for details.                             //
#/                                                                           //
#//////////////////////////////////////////////////////////////////////////////

# Makefile for c-engine

TARGET =			
LIBNAME =			rewlib.a
EXTRA_CXXFLAGS =		
EXTRA_LDFLAGS =			
LIBS =				
LOCALLIBDIRS =			
LOCALINCLDIRS =
LEX =				flex
LFLAGS =
YACC =				bison
YFLAGS =			-d
INST=				install-lib
CFLAGS=	-O4

HEADERS = 	globals.h intern.h rewrite_log.h

SRCS = rewlib/abstraction.c rewlib/Alloc.c rewlib/array.c rewlib/Balanced.c rewlib/Bignum.c rewlib/bitblast.c rewlib/boolean.c \
       rewlib/grouping.c rewlib/Builtin.c rewlib/Cache.c rewlib/calculus.c rewlib/case.c rewlib/case_split.c rewlib/crewrite.c rewlib/Derive.c \
       rewlib/Disc.c rewlib/env.c rewlib/equality.c rewlib/Exp_inte.c rewlib/Exp_util.c rewlib/fd.c rewlib/finite.c rewlib/heuristic.c \
       rewlib/Intern.c rewlib/lambda.c rewlib/learn.c rewlib/load.c rewlib/Match.c rewlib/memory.c rewlib/mymalloc.c \
       rewlib/Parse.c rewlib/parse_yices_ce.c rewlib/Pplex.c rewlib/Print.c rewlib/print_smt.c \
       rewlib/quant.c rewlib/Rewrite.c rewlib/RewriteLog.c rewlib/Rule_app.c rewlib/set.c rewlib/setsize.c \
       rewlib/solve.c rewlib/Subst.c rewlib/svc_parse.c rewlib/symmetry.c rewlib/term_cache.c \
       rewlib/Transiti.c rewlib/Tree.c rewlib/Type.c rewlib/unate.c rewlib/PPPARSE.c rewlib/PPDIR.c rewlib/simplex.c rewlib/decompose.c \
       rewlib/dimacs.c prove/Command.c prove/Compile.c prove/Derivati.c prove/Expand.c prove/Mainp.c prove/Normaliz.c prove/Search.c \
       prove/Search_n.c prove/Search_u.c prove/verilog.c

EXPORTS =	globals.h intern.h rewrite_log.h
YSRCS =		rewlib/smt_parser.y
LSRCS =		rewlib/smt_lexer.l
TMP_SRCS =	rewlib/smt_parser.c rewlib/smt_lexer.c
TMP_HEADERS =	rewlib/smt_parser.tab.h
OBJS =		$(SRCS:.c=.o) $(TMP_SRCS:.c=.o)

c-engine: $(OBJS)
	gcc -o c-engine $(OBJS)

all:		c-engine

rewlib/PPPARSE.o: rewlib/PPPARSE.c rewlib/globals.h rewlib/intern.h
		cc $(CFLAGS) -c -o rewlib/PPPARSE.o rewlib/PPPARSE.c

rewlib/smt_lexer.c:	rewlib/smt_lexer.l
		$(LEX) $(LFLAGS) rewlib/smt_lexer.l
		@mv lex.yy.c rewlib/smt_lexer.c

rewlib/smt_parser.h	\
rewlib/smt_parser.c:	rewlib/smt_parser.y
		$(YACC) $(YFLAGS) rewlib/smt_parser.y
		@mv smt_parser.tab.c rewlib/smt_parser.c
		@mv smt_parser.tab.h rewlib/smt_parser.tab.h
		@cp rewlib/smt_parser.tab.h rewlib/smt_parser.h
