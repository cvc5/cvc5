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
 * SyGuS lexer
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__SYGUS_LEXER_H
#define CVC5__PARSER__SYGUS_LEXER_H

#include "parser/flex/smt2_lexer.h"

namespace cvc5 {
namespace parser {

/**
 */
class SygusLexer : public Smt2Lexer
{
 public:
  SygusLexer();
  virtual ~SygusLexer() {}
};

}  // namespace parser
}  // namespace cvc5

#endif
