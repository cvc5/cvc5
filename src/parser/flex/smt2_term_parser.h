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

#include "api/cpp/cvc5.h"
#include "parser/flex/smt2_lexer.h"
#include "parser/smt2/smt2_state.h"

namespace cvc5 {
namespace parser {

/**
 */
class Smt2TermParser
{
 public:
  Smt2TermParser(Smt2Lexer& lex, Smt2State& state);
  virtual ~Smt2TermParser() {}

  ///
  Term parseTerm();
  const std::string& parseSymbol(DeclarationCheck check = CHECK_NONE, SymbolType type = SYM_SORT);
  const std::string& parseKeyword();
 protected:
  /** The lexer */
  Smt2Lexer& d_lex;
  /** The state */
  Smt2State& d_state;
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__SMT2_TERM_PARSER_H */
