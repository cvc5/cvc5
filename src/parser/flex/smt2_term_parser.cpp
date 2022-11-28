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

#include "parser/flex/smt2_term_parser.h"

namespace cvc5 {
namespace parser {

Smt2TermParser::Smt2TermParser(Smt2Lexer& lex, Smt2State& state)
    : d_lex(lex), d_state(state)
{
}

Term Smt2TermParser::parseTerm()
{
  Term t;
  return t;
}

const std::string& Smt2TermParser::parseSymbol(DeclarationCheck check, SymbolType type)
{
  
}

}  // namespace parser
}  // namespace cvc5
