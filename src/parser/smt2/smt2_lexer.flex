/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SMT lexer
 */

%{
#include "parser/smt2/smt2_lexer.h"

// NOTE: alternatively we could lex simple_symbol as:
//  [a-zA-Z0-9~!@\$%\^&\*+=<>\.\?/_-]+
// ??
// Note that removing `%option full` allows us to support piping from stdin
// natively without relying on interactive mode (--stdin-input-per-line).
// Disabling --stdin-input-per-line may cause some use cases of cvc5 involving
// piping to hang (see issue #9257).
// Option `%option ecs` ensures we parse quoted symbols with special characters.
%}

%option full
%option ecs
%option noyywrap
%option nounput
%option c++
%option yyclass="cvc5::parser::Smt2Lexer"

%{
#define YY_USER_ACTION addColumns(yyleng);
%}

nl          [\n]+
ws          [ \t\r\f]+
string_literal \"(\"\"|[^"])*\"
unterminated_string_literal \"(\"\"|[^"])*
nat         [0-9]+
decimal     [0-9]+\.[0-9]+
bitstr      #b[01]+
hexstr      #x[0-9a-fA-F]+
ffstr     #f[0-9]+m[0-9]+
simple_symbol [a-zA-Z~!@\$%\^&\*+=<>\.\?/_-][a-zA-Z0-9~!@\$%\^&\*+=<>\.\?/_-]*
quoted_symbol \|[^\|\\]*\|
unterminated_quoted_symbol \|[^\|\\]*
comment ;[^\n]*\n
unterminated_comment ;[^\n]*

%%

%{
  bumpSpan();
%}

"assert"   return cvc5::parser::ASSERT_TOK;
"assume"   return d_sygus ? cvc5::parser::ASSUME_TOK : cvc5::parser::SYMBOL;
"as"   return cvc5::parser::AS_TOK;
"!"   return cvc5::parser::ATTRIBUTE_TOK;
"block-model"   return d_strict ? cvc5::parser::SYMBOL : cvc5::parser::BLOCK_MODEL_TOK;
"block-model-values"   return d_strict ? cvc5::parser::SYMBOL : cvc5::parser::BLOCK_MODEL_VALUES_TOK;
"check-sat-assuming"   return cvc5::parser::CHECK_SAT_ASSUMING_TOK;
"check-sat"   return cvc5::parser::CHECK_SAT_TOK;
"check-synth-next"   return d_sygus ? cvc5::parser::CHECK_SYNTH_NEXT_TOK : cvc5::parser::SYMBOL;
"check-synth"   return d_sygus ? cvc5::parser::CHECK_SYNTH_TOK : cvc5::parser::SYMBOL;
"constraint"   return d_sygus ? cvc5::parser::CONSTRAINT_TOK : cvc5::parser::SYMBOL;
"declare-codatatypes"   return cvc5::parser::DECLARE_CODATATYPES_TOK;
"declare-codatatype"   return cvc5::parser::DECLARE_CODATATYPE_TOK;
"declare-const"   return cvc5::parser::DECLARE_CONST_TOK;
"declare-datatypes"   return cvc5::parser::DECLARE_DATATYPES_TOK;
"declare-datatype"   return cvc5::parser::DECLARE_DATATYPE_TOK;
"declare-fun"   return cvc5::parser::DECLARE_FUN_TOK;
"declare-heap"   return d_strict ? cvc5::parser::SYMBOL : cvc5::parser::DECLARE_HEAP;
"declare-pool"   return d_strict ? cvc5::parser::SYMBOL : cvc5::parser::DECLARE_POOL;
"declare-sort"   return cvc5::parser::DECLARE_SORT_TOK;
"declare-var"   return d_sygus ? cvc5::parser::DECLARE_VAR_TOK : cvc5::parser::SYMBOL;
"define-const"   return cvc5::parser::DEFINE_CONST_TOK;
"define-funs-rec"   return cvc5::parser::DEFINE_FUNS_REC_TOK;
"define-fun-rec"   return cvc5::parser::DEFINE_FUN_REC_TOK;
"define-fun"   return cvc5::parser::DEFINE_FUN_TOK;
"define-sort"   return cvc5::parser::DEFINE_SORT_TOK;
"echo"   return cvc5::parser::ECHO_TOK;
"exit"   return cvc5::parser::EXIT_TOK;
"get-abduct-next"   return d_strict ? cvc5::parser::SYMBOL : cvc5::parser::GET_ABDUCT_NEXT_TOK;
"get-abduct"   return d_strict ? cvc5::parser::SYMBOL : cvc5::parser::GET_ABDUCT_TOK;
"get-assertions"   return cvc5::parser::GET_ASSERTIONS_TOK;
"get-assignment"   return cvc5::parser::GET_ASSIGNMENT_TOK;
"get-difficulty"   return d_strict ? cvc5::parser::SYMBOL : cvc5::parser::GET_DIFFICULTY_TOK;
"get-info"   return cvc5::parser::GET_INFO_TOK;
"get-interpolant-next"   return d_strict ? cvc5::parser::SYMBOL : cvc5::parser::GET_INTERPOL_NEXT_TOK;
"get-interpolant"   return d_strict ? cvc5::parser::SYMBOL : cvc5::parser::GET_INTERPOL_TOK;
"get-learned-literals"   return d_strict ? cvc5::parser::SYMBOL : cvc5::parser::GET_LEARNED_LITERALS_TOK;
"get-model"   return cvc5::parser::GET_MODEL_TOK;
"get-option"   return cvc5::parser::GET_OPTION_TOK;
"get-proof"   return cvc5::parser::GET_PROOF_TOK;
"get-qe-disjunct"   return d_strict ? cvc5::parser::SYMBOL : cvc5::parser::GET_QE_DISJUNCT_TOK;
"get-qe"   return d_strict ? cvc5::parser::SYMBOL : cvc5::parser::GET_QE_TOK;
"get-unsat-assumptions"   return cvc5::parser::GET_UNSAT_ASSUMPTIONS_TOK;
"get-unsat-core"   return cvc5::parser::GET_UNSAT_CORE_TOK;
"get-value"   return cvc5::parser::GET_VALUE_TOK;
"include"   return d_strict ? cvc5::parser::SYMBOL : cvc5::parser::INCLUDE_TOK;
"_"   return cvc5::parser::INDEX_TOK;
"inv-constraint"   return d_sygus ? cvc5::parser::INV_CONSTRAINT_TOK : cvc5::parser::SYMBOL;
"let"   return cvc5::parser::LET_TOK;
"("   return cvc5::parser::LPAREN_TOK;
"match"   return cvc5::parser::MATCH_TOK;
"par"   return cvc5::parser::PAR_TOK;
"pop"   return cvc5::parser::POP_TOK;
"push"   return cvc5::parser::PUSH_TOK;
"reset-assertions"   return cvc5::parser::RESET_ASSERTIONS_TOK;
"reset"   return cvc5::parser::RESET_TOK;
")"   return cvc5::parser::RPAREN_TOK;
"set-feature"   return d_sygus ? cvc5::parser::SET_FEATURE_TOK : cvc5::parser::SYMBOL;
"set-info"   return cvc5::parser::SET_INFO_TOK;
"set-logic"   return cvc5::parser::SET_LOGIC_TOK;
"set-option"   return cvc5::parser::SET_OPTION_TOK;
"simplify"   return d_strict ? cvc5::parser::SYMBOL : cvc5::parser::SIMPLIFY_TOK;
"Constant"   return cvc5::parser::SYGUS_CONSTANT_TOK;
"Variable"   return cvc5::parser::SYGUS_VARIABLE_TOK;
"synth-fun"   return d_sygus ? cvc5::parser::SYNTH_FUN_TOK : cvc5::parser::SYMBOL;
"synth-inv"   return d_sygus ? cvc5::parser::SYNTH_INV_TOK : cvc5::parser::SYMBOL;

{ws}   bumpSpan();
{nl}   addLines(yyleng); bumpSpan();
{string_literal}    {
                      // increment location for each line
                      for (const char * c=yytext; *c; ++c)
                      {
                        if (*c == '\n')
                        {
                          addLines(1);
                          bumpSpan();
                        }
                      }
                      return cvc5::parser::STRING_LITERAL;
                    }
{unterminated_string_literal}   return cvc5::parser::UNTERMINATED_STRING_LITERAL;
{nat}   return cvc5::parser::INTEGER_LITERAL;
{decimal}   return cvc5::parser::DECIMAL_LITERAL;
{hexstr}   return cvc5::parser::HEX_LITERAL;
{bitstr}   return cvc5::parser::BINARY_LITERAL;
{ffstr}   return cvc5::parser::FIELD_LITERAL;
\:{simple_symbol}  return cvc5::parser::KEYWORD;
{quoted_symbol} {
                  // increment location for each line
                  for (const char * c=yytext; *c; ++c)
                  {
                    if (*c == '\n')
                    {
                      addLines(1);
                      bumpSpan();
                    }
                  }
                  return cvc5::parser::QUOTED_SYMBOL;
                }
{unterminated_quoted_symbol} return cvc5::parser::UNTERMINATED_QUOTED_SYMBOL;
{simple_symbol} return cvc5::parser::SYMBOL;
{unterminated_comment} return cvc5::parser::EOF_TOK;
{comment} {
            addLines(1);
            bumpSpan();
            break;
          }
. parseError("Error finding token"); break;
%%

namespace cvc5 {
namespace parser {

Smt2Lexer::Smt2Lexer(bool isSygus, bool isStrict)
  : FlexLexer(),
    d_sygus(isSygus),
    d_strict(isStrict)
{
}

bool Smt2Lexer::isSygus() const { return d_sygus; }

bool Smt2Lexer::isStrict() const { return d_strict; }
  
}
}
