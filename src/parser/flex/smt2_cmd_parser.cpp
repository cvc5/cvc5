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

#include "parser/flex/smt2_cmd_parser.h"

#include "parser/api/cpp/command.h"

namespace cvc5 {
namespace parser {

Smt2CmdParser::Smt2CmdParser(Smt2Lexer& lex, Smt2TermParser& tparser)
    : d_lex(lex), d_tparser(tparser)
{
}

Command* Smt2CmdParser::nextCommand() { 
  d_lex.eat_token(Token::LPAREN_TOK);
  Token t = d_lex.nextToken();
  switch (t)
  {

    default:
      // TODO: error
      break;
  }
  d_lex.eat_token(Token::RPAREN_TOK);
  return nullptr;
}

}  // namespace parser
}  // namespace cvc5
