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

#include "parser/flex/smt2_parser.h"

#include "base/output.h"

namespace cvc5 {
namespace parser {

Smt2Parser::Smt2Parser(Solver* solver, SymbolManager* sm, bool isSygus)
    : FlexParser(solver, sm),
      d_isSygus(isSygus),
      d_lex(),
      d_termParser(d_lex),
      d_cmdParser(d_lex, d_termParser)
{
}

void Smt2Parser::initializeInput(std::istream& s, const std::string& inputName)
{
  d_lex.initialize(s, inputName);

  Trace("ajr-temp") << "Get tokens" << std::endl;
  Token t;
  while ((t = d_lex.nextToken()) != Token::EOF_TOK)
  {
    Trace("ajr-temp") << "Token: " << t << std::endl;
  }
  Trace("ajr-temp") << "Finished" << std::endl;
  exit(1);
}

Command* Smt2Parser::nextCommand() { return d_cmdParser.nextCommand(); }

Term Smt2Parser::nextExpression() { return d_termParser.nextExpression(); }

}  // namespace parser
}  // namespace cvc5
