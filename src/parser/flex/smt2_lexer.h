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

#include <fstream>
#include <iosfwd>
#include <string>

#include "parser/flex/lexer.h"

namespace cvc5 {
namespace parser {

/**
 */
class Smt2Lexer : public Lexer
{
 public:
  Smt2Lexer();
  virtual ~Smt2Lexer() {}
  /** Inherited from yyFlexLexer */
  int yylex() override;
};

}  // namespace parser
}  // namespace cvc5

#endif
