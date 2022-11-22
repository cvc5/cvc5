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

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__LEXER_H
#define CVC5__PARSER__LEXER_H

#include <fstream>
#include <iosfwd>
#include <string>

#include "parser/flex/tokens.h"

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

class Lexer
{
 public:
  Lexer();
  virtual ~Lexer() {}
  /** get next token */
  virtual Token nextToken() = 0;
  /** initialize */
  virtual void initialize(std::istream& input,
                          const std::string& inputName) = 0;
  // Used to report errors, with the current source location attached.
  void report_error(const std::string&);
  // Used to initialize d_span.
  void init_d_span();
  // Sets the spans start to its current end.
  void bump_span();
  // Add columns or lines to the end location of the span.
  void add_columns(uint32_t columns);
  void add_lines(uint32_t lines);
  // Span of last token pulled from underlying lexer (old top of stack)
  Span d_span;
  /** Name of current file */
  std::string d_inputName;
};

}  // namespace parser
}  // namespace cvc5

#endif
