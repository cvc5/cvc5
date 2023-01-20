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

#include "parser/flex_lexer.h"

#include <cassert>
#include <iostream>
#include <sstream>

#include "base/check.h"
#include "base/output.h"
#include "parser/parser_exception.h"

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

FlexLexer::FlexLexer() : yyFlexLexer() {}

void FlexLexer::warning(const std::string& msg)
{
  Warning() << d_inputName << ':' << d_span.d_start.d_line << '.'
            << d_span.d_start.d_column << ": " << msg << std::endl;
}

void FlexLexer::parseError(const std::string& msg, bool eofException)
{
  if (eofException)
  {
    throw ParserEndOfFileException(
        msg, d_inputName, d_span.d_start.d_line, d_span.d_start.d_column);
  }
  else
  {
    throw ParserException(
        msg, d_inputName, d_span.d_start.d_line, d_span.d_start.d_column);
  }
}

void FlexLexer::initSpan()
{
  d_span.d_start.d_line = 1;
  d_span.d_start.d_column = 1;
  d_span.d_end.d_line = 1;
  d_span.d_end.d_column = 1;
}
void FlexLexer::bumpSpan()
{
  d_span.d_start.d_line = d_span.d_end.d_line;
  d_span.d_start.d_column = d_span.d_end.d_column;
}
void FlexLexer::addColumns(uint32_t columns)
{
  d_span.d_end.d_column += columns;
}
void FlexLexer::addLines(uint32_t lines)
{
  d_span.d_end.d_line += lines;
  d_span.d_end.d_column = 1;
}

void FlexLexer::initialize(std::istream& input, const std::string& inputName)
{
  d_inputName = inputName;
  // use the std::istream* version which is supported in earlier Flex versions
  yyrestart(&input);
  initSpan();
  d_peeked.clear();
}

const char* FlexLexer::tokenStr()
{
  Assert(d_peeked.empty());
  return YYText();
}

Token FlexLexer::nextToken()
{
  if (d_peeked.empty())
  {
    // Call the derived yylex() and convert it to a token
    return Token(yylex());
  }
  Token t = d_peeked.back();
  d_peeked.pop_back();
  return t;
}

Token FlexLexer::peekToken()
{
  // parse next token
  Token t = Token(yylex());
  // reinsert it immediately
  reinsertToken(t);
  // return it
  return t;
}

void FlexLexer::reinsertToken(Token t) { d_peeked.push_back(t); }

void FlexLexer::unexpectedTokenError(Token t, const std::string& info)
{
  Assert(d_peeked.empty());
  std::ostringstream o{};
  o << info << ", got `" << tokenStr() << "` (" << t << ").";
  // Note that we treat this as an EOF exception if the token is EOF_TOK.
  // This is important for exception handling in interactive mode.
  parseError(o.str(), t == Token::EOF_TOK);
}

void FlexLexer::eatToken(Token t)
{
  Token tt = nextToken();
  if (t != tt)
  {
    std::ostringstream o{};
    o << "Expected a " << t;
    unexpectedTokenError(tt, o.str());
  }
}

bool FlexLexer::eatTokenChoice(Token t, Token f)
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
