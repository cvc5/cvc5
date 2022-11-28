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

std::vector<std::pair<std::string, Sort> > Smt2TermParser::parseSortedVarList()
{
  std::vector<std::pair<std::string, Sort> > varList;
  return varList;
}

const std::string& Smt2TermParser::parseSymbol(DeclarationCheck check,
                                               SymbolType type)
{
  return "";
}

const std::string& Smt2TermParser::parseKeyword() { return ""; }

Grammar* Smt2TermParser::parseGrammar(const std::vector<Term>& sygusVars,
                                      const std::string& fun)
{
  return nullptr;
}

size_t Smt2TermParser::parseIntegerNumeral() { return 0; }

std::vector<DatatypeDecl> Smt2TermParser::parseDatatypeDef(
    bool isCo,
    const std::vector<std::string>& dnames,
    const std::vector<size_t>& arities)
{
  std::vector<DatatypeDecl> dts;
  return dts;
}

}  // namespace parser
}  // namespace cvc5
