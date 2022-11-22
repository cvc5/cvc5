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
 * Term parser for smt2
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__SMT2_TERM_PARSER_H
#define CVC5__PARSER__SMT2_TERM_PARSER_H

#include "parser/flex/smt2_lexer.h"

namespace cvc5 {
namespace parser {

/**
 */
class Smt2TermParser
{
 public:
  Smt2TermParser(Smt2Lexer& lex);
  virtual ~Smt2TermParser() {}

  /** Parse and return the next expression. */
  Term nextExpression();

 protected:
  /** The lexer */
  Smt2Lexer& d_lex;
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__SMT2_TERM_PARSER_H */
