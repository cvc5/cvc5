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

namespace cvc5 {
namespace parser {

Smt2Parser::Smt2Parser(bool isSygus) : d_isSygus(isSygus)
{
  
}

void Smt2Parser::initializeInput(std::istream& s, const std::string& inputName)
{
  d_lex.initialize(s, inputName);
}

Command* Smt2Parser::nextCommand()
{
  // TODO
  return nullptr;
}

Term Smt2Parser::nextExpression()
{
  // TODO
  return t;
}

}  // namespace parser
}  // namespace cvc5
