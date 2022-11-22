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

#ifndef CVC5__PARSER__SMT2_CMD_PARSER_H
#define CVC5__PARSER__SMT2_CMD_PARSER_H

#include "parser/flex/smt2_lexer.h"
#include "parser/flex/smt2_term_parser.h"

namespace cvc5 {
namespace parser {

/**
 */
class Smt2CmdParser
{
 public:
  Smt2CmdParser(Smt2Lexer& lex, Smt2TermParser& tparser);
  virtual ~Smt2CmdParser() {}
  /**
   * Parse and return the next command.
   */
  Command* nextCommand() override;

 protected:
  /** The lexer */
  Smt2Lexer& d_lex;
  /** The term parser */
  Smt2TermParser& d_tparser
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__SMT2_H */
