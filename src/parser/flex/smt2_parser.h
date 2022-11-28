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
 * Definitions of SMT2 tokens.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__SMT2_PARSER_H
#define CVC5__PARSER__SMT2_PARSER_H

#include "api/cpp/cvc5.h"
#include "parser/flex/flex_parser.h"
#include "parser/flex/smt2_cmd_parser.h"
#include "parser/flex/smt2_lexer.h"
#include "parser/flex/smt2_term_parser.h"
#include "parser/smt2/smt2_state.h"

namespace cvc5 {
namespace parser {

/**
 */
class Smt2Parser : public FlexParser
{
 public:
  Smt2Parser(Solver* solver,
             SymbolManager* sm,
             bool strictMode = false,
             bool isSygus = false);
  virtual ~Smt2Parser() {}
 protected:
  /**
   * Parse and return the next command.
   */
  Command* parseNextCommand() override;

  /** Parse and return the next expression. */
  Term parseNextExpression() override;
  /** Is sygus? */
  bool d_isSygus;
  /** The lexer */
  Smt2Lexer d_slex;
  /** The state */
  Smt2State d_state;
  /** Term parser */
  Smt2TermParser d_termParser;
  /** Command parser */
  Smt2CmdParser d_cmdParser;
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__SMT2_H */
