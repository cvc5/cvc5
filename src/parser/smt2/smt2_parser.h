/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The flex smt2 parser.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__SMT2__SMT2_PARSER_H
#define CVC5__PARSER__SMT2__SMT2_PARSER_H

#include <cvc5/cvc5.h>

#include "parser/parser.h"
#include "parser/smt2/smt2_state.h"
#include "parser/smt2/smt2_cmd_parser.h"
#include "parser/smt2/smt2_lexer.h"
#include "parser/smt2/smt2_term_parser.h"

namespace cvc5 {
namespace parser {

/**
 * -based smt2 parser. It maintains a lexer, a state, a term parser and a
 * command parser. The latter two are used for parsing terms and commands. The
 * command parser depends on the term parser.
 */
class Smt2Parser : public Parser
{
 public:
  Smt2Parser(Solver* solver,
             SymbolManager* sm,
             bool isStrict = false,
             bool isSygus = false);
  virtual ~Smt2Parser() {}
  /** Set the logic */
  void setLogic(const std::string& logic) override;

 protected:
  /**
   * Parse and return the next command. Will initialize the logic to "ALL"
   * or the forced logic if no logic is set prior to this point and a command
   * is read that requires initializing the logic.
   */
  std::unique_ptr<Command> parseNextCommand() override;

  /**
   * Parse and return the next expression. Requires setting the logic
   * beforehand.
   */
  Term parseNextExpression() override;
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
