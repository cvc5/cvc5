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

Lexer::Lexer() : yyFlexLexer() {}

void Lexer::report_error(const std::string& msg)
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

Token Lexer::nextToken() { return Token(yylex()); }

void Lexer::unexpected_token_error(Token t, const std::string& info)
{
  std::ostringstream o{};
  o << "Scanned token " << t << ", `" << YYText()
    << "`, which is invalid in this position";
  if (info.length())
  {
    o << std::endl << "Note: " << info;
  }
  report_error(o.str());
}

std::string Lexer::prefix_id()
{
  nextToken();
  return YYText();
}

void Lexer::eat_token(Token t)
{
  auto tt = nextToken();
  if (t != tt)
  {
    std::ostringstream o{};
    o << "Expected a " << t << ", but got a " << tt << ", `" << YYText() << "`";
    unexpected_token_error(tt, o.str());
  }
}

}  // namespace parser
}  // namespace cvc5
