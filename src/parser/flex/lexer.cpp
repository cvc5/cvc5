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
 * Base class lexer
 */

#include "parser/flex/lexer.h"

#include <cassert>
#include <iostream>
#include <sstream>
#include "base/check.h"

namespace cvc5 {
namespace parser {

std::ostream& operator<<(std::ostream& o, const Location& l)
{
  return o << l.d_line << ":" << l.d_column;
}
std::ostream& operator<<(std::ostream& o, const Span& l)
{
  return o << l.d_start << "-" << l.d_end;
}

Lexer::Lexer() : yyFlexLexer(), d_peeked(Token::NONE) {}

void Lexer::warning(const std::string& msg)
{
  if (d_inputName.length())
  {
    std::cerr << "Warning: " << d_inputName << " at " << d_span;
  }
  std::cerr << std::endl << msg << std::endl;
}

void Lexer::parseError(const std::string& msg)
{
  if (d_inputName.length())
  {
    std::cerr << "Error: " << d_inputName << " at " << d_span;
  }
  std::cerr << std::endl << msg << std::endl;
  exit(1);
}

void Lexer::init_d_span()
{
  d_span.d_start.d_line = 1;
  d_span.d_start.d_column = 1;
  d_span.d_end.d_line = 1;
  d_span.d_end.d_column = 1;
}
void Lexer::bump_span()
{
  d_span.d_start.d_line = d_span.d_end.d_line;
  d_span.d_start.d_column = d_span.d_end.d_column;
}
void Lexer::add_columns(uint32_t columns) { d_span.d_end.d_column += columns; }
void Lexer::add_lines(uint32_t lines)
{
  d_span.d_end.d_line += lines;
  d_span.d_end.d_column = 1;
}

void Lexer::initialize(std::istream& input, const std::string& inputName)
{
  d_inputName = inputName;
  yyrestart(input);
  init_d_span();
}

const char* Lexer::token_str() { return YYText(); }

Token Lexer::nextToken()
{
  if (d_peeked == Token::NONE)
  {
    // Call the derived yylex() and convert it to a token
    return Token(yylex());
  }
  Token t = d_peeked;
  d_peeked = Token::NONE;
  return t;
}

Token Lexer::peekToken()
{
  Assert(d_peeked == Token::NONE);
  Token t = Token(yylex());
  // reinsert it
  d_peeked = t;
  return t;
}

void Lexer::unexpectedTokenError(Token t, const std::string& info)
{
  std::ostringstream o{};
  o << info << ", got `" << YYText() << "` (" << t << ").";
  parseError(o.str());
}

std::string Lexer::prefix_id()
{
  nextToken();
  return YYText();
}

void Lexer::eatToken(Token t)
{
  Token tt = nextToken();
  if (t != tt)
  {
    std::ostringstream o{};
    o << "Expected a " << t;
    unexpectedTokenError(tt, o.str());
  }
}

bool Lexer::eatTokenChoice(Token t, Token f)
{
  Token tt = nextToken();
  if (tt == t)
  {
    return true;
  }
  else if (tt != f)
  {
    std::ostringstream o{};
    o << "Expected " << t << " or " << f;
    unexpectedTokenError(tt, o.str());
  }
  return false;
}

}  // namespace parser
}  // namespace cvc5
