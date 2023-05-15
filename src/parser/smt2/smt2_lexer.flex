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

"as"   return cvc5::parser::AS_TOK;
"!"   return cvc5::parser::ATTRIBUTE_TOK;
"_"   return cvc5::parser::INDEX_TOK;
"let"   return cvc5::parser::LET_TOK;
"("   return cvc5::parser::LPAREN_TOK;
"match"   return cvc5::parser::MATCH_TOK;
"par"   return cvc5::parser::PAR_TOK;
")"   return cvc5::parser::RPAREN_TOK;

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
