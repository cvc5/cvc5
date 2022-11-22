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

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__SMT2_LEXER_H
#define CVC5__PARSER__SMT2_LEXER_H

// Super hack
// https://stackoverflow.com/a/40665154/4917890
#if !defined(yyFlexLexerOnce)
#include <FlexLexer.h>
#endif

#include <fstream>
#include <iosfwd>
#include <string>

#include "parser/flex/lexer.h"

namespace cvc5 {
namespace parser {

struct Location
{
  Location() : d_line(1), d_column(1) {}
  uint32_t d_line;
  uint32_t d_column;
};

struct Span
{
  Location d_start;
  Location d_end;
};

std::ostream& operator<<(std::ostream& o, const Location& l);
std::ostream& operator<<(std::ostream& o, const Span& l);

// Lexer explanation.
//
// This a lookahead-two lexer, backed by a length-two buffer.
//
// View it as a stack of tokens. The topmost is first.
//
// It is implemented with functions for pulling tokens out of the lexer,
// getting information about the token just pulled, and pushing a token back
// into the conceptual stream/concrete buffer.

// Private components
// Currrent lexer
class Smt2Lexer : public Lexer
{
 public:
  Smt2Lexer();
  /** Set the input for the given file.
   *
   * @param filename the input filename
   */
  void setFileInput(const std::string& filename);

  /** Set the input for the given stream.
   *
   * @param input the input stream
   * @param name the name of the stream, for use in error messages
   */
  void setStreamInput(std::istream& input, const std::string& name);

  /** Set the input for the given string
   *
   * @param input the input string
   * @param name the name of the stream, for use in error messages
   */
  void setStringInput(const std::string& input, const std::string& name);
  // Core functions
  // Advance to the next token (pop from stack)
  Token next_token();
  // String corresponding to the last token (old top of stack)
  const char* token_str();
  // Used to report errors, with the current source location attached.
  void report_error(const std::string&);

  // Derived functions
  // Expect a token `t` as the next one. Error o.w.
  void eat_token(Token t);
  // Interpret the next token as an identifier (even if it isn't) and return its
  // string
  std::string prefix_id();
  // Error. Got `t`, expected `info`.
  void unexpected_token_error(Token t, const std::string& info);
  /** lexer in scope */
  static Smt2Lexer* s_inScope;
  /** Allocated flex lexer */
  FlexLexer* d_lexer;
  /** Name of current file */
  std::string d_inputName;
};

}  // namespace parser
}  // namespace cvc5

#endif
