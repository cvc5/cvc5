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

#include <string.h>
#include "base/check.h"

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

std::string Smt2TermParser::parseSymbol(DeclarationCheck check, SymbolType type)
{
  return "";
}

std::vector<std::string> Smt2TermParser::parseSymbolList(DeclarationCheck check,
                                                         SymbolType type)
{
  std::vector<std::string> symbols;
  return symbols;
}

std::string Smt2TermParser::parseKeyword() { return ""; }

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

std::string Smt2TermParser::parseStr(bool unescape) {
  d_lex.eatToken(Token::STRING_LITERAL);
  std::string s = d_lex.YYText();
    if (unescape)
    {
      /* strip off the quotes */
      s = s.substr(1, s.size() - 2);
      for (size_t i = 0, ssize = s.size(); i < ssize; i++)
      {
        if ((unsigned)s[i] > 127 && !isprint(s[i]))
        {
          d_state.parseError(
              "Extended/unprintable characters are not "
              "part of SMT-LIB, and they must be encoded "
              "as escape sequences");
        }
      }
      char* p_orig = strdup(s.c_str());
      char *p = p_orig, *q = p_orig;
      while (*q != '\0')
      {
        if (*q == '"')
        {
          // Handle SMT-LIB >=2.5 standard escape '""'.
          ++q;
          Assert(*q == '"');
        }
        *p++ = *q++;
      }
      *p = '\0';
      s = p_orig;
      free(p_orig);
    }
  return s; 
}

}  // namespace parser
}  // namespace cvc5
