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
std::vector<Term> Smt2TermParser::parseTermList()
{
  std::vector<Term> terms;

  return terms;
}

Term Smt2TermParser::parseSymbolicExpr()
{
  Term t;
  return t;
}

Sort Smt2TermParser::parseSort()
{
  Sort s;
  return s;
}

std::vector<Sort> Smt2TermParser::parseSortList()
{
  std::vector<Sort> sorts;
  return sorts;
}

const std::string& Smt2TermParser::parseSymbol(DeclarationCheck check,
                                               SymbolType type)
{
  return "";
}

const std::string& Smt2TermParser::parseKeyword() { return ""; }

Grammar* Smt2TermParser::parseGrammar() { return nullptr; }

}  // namespace parser
}  // namespace cvc5
