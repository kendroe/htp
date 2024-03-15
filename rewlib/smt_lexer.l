%{
/*
 * smt_lexer.l
 *
 * This program is free software.  See LICENSE for more information *)
 */
#include <stdlib.h>
#include <string.h>
#include "smt_parser.h"

char yytoken[2000];
%}

%a 3000
%e 1700
%k 1000
%n 700
%o 4000
%p 5000

%%

"true"				 { return TRUE_TOK; }
"false"				 { return FALSE_TOK; }
"ite"				 { return ITE_TOK; }
"not"				 { return NOT_TOK; }
"implies"			 { return IMPLIES_TOK; }
"if_then_else"		 { return IF_THEN_ELSE_TOK; }
"and"				 { return AND_TOK; }
"or"				 { return OR_TOK; }
"xor"				 { return XOR_TOK; }
"iff"				 { return IFF_TOK; }
"exists"			 { return EXISTS_TOK; }
"forall"			 { return FORALL_TOK; }
"let"				 { return LET_TOK; }
"flet"				 { return FLET_TOK; }
\"[^"]*\"            { strcpy(yytoken,yytext+1); yytoken[strlen(yytoken)-1] = 0; return STRING_TOK; }
\{[^{}]*\}           { strcpy(yytoken,yytext+1); yytoken[strlen(yytoken)-1] = 0; return USER_VAL_TOK; }
"notes"              { return NOTES_TOK; }
"sorts"              { return SORTS_TOK; }
"funs"               { return FUNS_TOK; }
"preds"              { return PREDS_TOK; }
"extensions"         { return EXTENSIONS_TOK; }
"definition"         { return DEFINITION_TOK; }
"axioms"             { return AXIOMS_TOK; }
"logic"              { return LOGIC_TOK; }
\:                   { return COLON_TOK; }
\(                   { return LPAREN_TOK; }
\)                   { return RPAREN_TOK; }
"sat"                { return SAT_TOK; }
"unsat"              { return UNSAT_TOK; }
"unknown"            { return UNKNOWN_TOK ; }
"assumption"         { return ASSUMPTION_TOK; }
"formula"            { return FORMULA_TOK; }
"status"             { return STATUS_TOK; }
"benchmark"          { return BENCHMARK_TOK; }
"extrasorts"         { return EXTRASORTS_TOK; }
"extrafuns"          { return EXTRAFUNS_TOK; }
"extrapreds"         { return EXTRAPREDS_TOK; }
"language"           { return LANGUAGE_TOK; }
\=                   { return EQUALS_TOK; }
"distinct"           { return DISTINCT_TOK; }
\;[^\n]*\n           { continue; }
\$                   { return DOLLAR_TOK; }
[=<>&@#+\-*/%|~]+    { strcpy(yytoken, yytext); return AR_SYMB; }
[0-9]+               { strcpy(yytoken, yytext); return NUMERAL_TOK; }
\?[a-zA-Z][a-zA-Z._0-9]* { strcpy(yytoken, yytext); return VAR_TOK;}
[a-zA-Z\/][a-zA-Z.\-\+\/_\'0-9]* { strcpy(yytoken,yytext); return SYM_TOK; }
[\ \t\n\r]           { continue; }
\_                   { continue; }


%%

int yywrap()
{
    return 1;
}
