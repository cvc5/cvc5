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
 * The smt2 command parser.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__SMT2_CMD_PARSER_H
#define CVC5__PARSER__SMT2_CMD_PARSER_H

#include "parser/smt2/smt2_state.h"
#include "parser/smt2/smt2_lexer.h"
#include "parser/smt2/smt2_term_parser.h"

namespace cvc5 {
namespace parser {

class Command;

/**
 * The smt2 command parser, which parses commands. It reads from the given
 * lexer, and relies on a term parser for parsing terms in the body of commands.
 */
class Smt2CmdParser
{
 public:
  Smt2CmdParser(Smt2Lexer& lex, Smt2State& state, Smt2TermParser& tparser);
  virtual ~Smt2CmdParser() {}
  /**
   * Parse and return the next command, or nullptr if we are at the end of file.
   */
  std::unique_ptr<Command> parseNextCommand();

 protected:
  /** Next command token */
  Token nextCommandToken();
  /** The lexer */
  Smt2Lexer& d_lex;
  /** The state */
  Smt2State& d_state;
  /** The term parser */
  Smt2TermParser& d_tparser;
  /** Map strings to tokens */
  std::map<std::string, Token> d_table;
  /** is strict */
  bool d_isStrict;
  /** is sygus */
  bool d_isSygus;
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__SMT2_H */
