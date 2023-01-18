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

#include "parser/smt2/smt2_term_parser.h"

#include <string.h>

#include "base/check.h"
#include "base/output.h"

namespace cvc5 {
namespace parser {

Smt2TermParser::Smt2TermParser(Smt2Lexer& lex, Smt2State& state)
    : d_lex(lex), d_state(state)
{
}

Term Smt2TermParser::parseTerm()
{
  Term ret;
  return ret;
}

Term Smt2TermParser::parseSymbolicExpr()
{
  Term ret;
  Token tok;
  std::vector<std::vector<Term>> sstack;
  Solver* slv = d_state.getSolver();
  do
  {
    tok = d_lex.nextToken();
    switch (tok)
    {
      // ------------------- open paren
      case Token::LPAREN_TOK:
      {
        sstack.emplace_back(std::vector<Term>());
      }
      break;
      // ------------------- close paren
      case Token::RPAREN_TOK:
      {
        if (sstack.empty())
        {
          d_lex.unexpectedTokenError(
              tok, "Mismatched parentheses in SMT-LIBv2 s-expression");
        }
        ret = slv->mkTerm(SEXPR, sstack.back());
        // pop the stack
        sstack.pop_back();
      }
      break;
      // ------------------- base case
      default:
      {
        // note that there are no tokens that are forbidden here
        std::string str = d_lex.tokenStr();
        ret = slv->mkString(d_state.processAdHocStringEsc(str));
      }
      break;
    }
    if (!ret.isNull())
    {
      // add it to the list and reset ret
      if (!sstack.empty())
      {
        sstack.back().push_back(ret);
        ret = Term();
      }
      // otherwise it will be returned
    }
  } while (!sstack.empty());
  Assert(!ret.isNull());
  return ret;
}

Sort Smt2TermParser::parseSort()
{
  Sort ret;
  Token tok;
  std::vector<std::pair<std::string, std::vector<Sort>>> sstack;
  do
  {
    tok = d_lex.nextToken();
    switch (tok)
    {
      // ------------------- open paren
      case Token::LPAREN_TOK:
      {
        tok = d_lex.nextToken();
        switch (tok)
        {
          case Token::INDEX_TOK:
          {
            // a standalone indexed symbol
            std::string name = parseSymbol(CHECK_NONE, SYM_SORT);
            std::vector<std::string> numerals = parseNumeralList();
            d_lex.eatToken(Token::RPAREN_TOK);
            ret = d_state.getIndexedSort(name, numerals);
          }
          break;
          case Token::SYMBOL:
          case Token::QUOTED_SYMBOL:
          {
            // sort constructor identifier
            std::string name = tokenStrToSymbol(tok);
            // open a new stack frame
            std::vector<Sort> emptyArgs;
            sstack.emplace_back(name, emptyArgs);
          }
          break;
          default:
            // NOTE: it is possible to have sorts e.g.
            // ((_ FixedSizeList 4) Real) where tok would be LPAREN_TOK here.
            // However, we have no such examples in cvc5 currently.
            d_lex.unexpectedTokenError(tok,
                                       "Expected SMT-LIBv2 sort constructor");
            break;
        }
      }
      break;
      // ------------------- close paren
      case Token::RPAREN_TOK:
      {
        if (sstack.empty())
        {
          d_lex.unexpectedTokenError(
              tok, "Mismatched parentheses in SMT-LIBv2 sort");
        }
        // Construct the (parametric) sort specified by sstack.back()
        ret = d_state.getParametricSort(sstack.back().first,
                                        sstack.back().second);
        // pop the stack
        sstack.pop_back();
      }
      break;
      // ------------------- a simple (defined or builtin) sort
      case Token::SYMBOL:
      case Token::QUOTED_SYMBOL:
      {
        std::string name = tokenStrToSymbol(tok);
        ret = d_state.getSort(name);
      }
      break;
      default:
        d_lex.unexpectedTokenError(tok, "Expected SMT-LIBv2 sort");
        break;
    }
    if (!ret.isNull())
    {
      // add it to the list and reset ret
      if (!sstack.empty())
      {
        sstack.back().second.push_back(ret);
        ret = Sort();
      }
      // otherwise it will be returned
    }
  } while (!sstack.empty());
  Assert(!ret.isNull());
  return ret;
}

std::vector<Sort> Smt2TermParser::parseSortList()
{
  d_lex.eatToken(Token::LPAREN_TOK);
  std::vector<Sort> sorts;
  Token tok = d_lex.nextToken();
  while (tok != Token::RPAREN_TOK)
  {
    d_lex.reinsertToken(tok);
    Sort s = parseSort();
    sorts.push_back(s);
    tok = d_lex.nextToken();
  }
  return sorts;
}

std::vector<std::pair<std::string, Sort>> Smt2TermParser::parseSortedVarList()
{
  std::vector<std::pair<std::string, Sort>> varList;
  d_lex.eatToken(Token::LPAREN_TOK);
  std::string name;
  Sort t;
  // while the next token is LPAREN, exit if RPAREN
  while (d_lex.eatTokenChoice(Token::LPAREN_TOK, Token::RPAREN_TOK))
  {
    name = parseSymbol(CHECK_NONE, SYM_VARIABLE);
    t = parseSort();
    varList.emplace_back(name, t);
    d_lex.eatToken(Token::RPAREN_TOK);
  }
  return varList;
}

std::string Smt2TermParser::parseSymbol(DeclarationCheck check, SymbolType type)
{
  Token tok = d_lex.nextToken();
  std::string id = tokenStrToSymbol(tok);
  // run the check
  if (!d_state.isAbstractValue(id))
  {
    // if an abstract value, SolverEngine handles declaration
    d_state.checkDeclaration(id, check, type);
  }
  return id;
}

std::vector<std::string> Smt2TermParser::parseSymbolList(DeclarationCheck check,
                                                         SymbolType type)
{
  d_lex.eatToken(Token::LPAREN_TOK);
  std::vector<std::string> symbols;
  Token tok = d_lex.nextToken();
  while (tok != Token::RPAREN_TOK)
  {
    d_lex.reinsertToken(tok);
    std::string sym = parseSymbol(check, type);
    symbols.push_back(sym);
    tok = d_lex.nextToken();
  }
  return symbols;
}

std::string Smt2TermParser::parseKeyword()
{
  d_lex.eatToken(Token::KEYWORD);
  std::string s = d_lex.tokenStr();
  // strip off the initial colon
  return s.erase(0, 1);
}

Grammar* Smt2TermParser::parseGrammar(const std::vector<Term>& sygusVars,
                                      const std::string& fun)
{
  // We read a sorted variable list ((<symbol> <sort>)^n+1)
  std::vector<std::pair<std::string, Sort>> sortedVarNames =
      parseSortedVarList();
  // non-terminal symbols in the pre-declaration are locally scoped
  d_state.pushScope();
  std::vector<Term> ntSyms;
  for (std::pair<std::string, Sort>& i : sortedVarNames)
  {
    d_state.checkDeclaration(i.first, CHECK_UNDECLARED, SYM_SORT);
    // make the non-terminal symbol, which will be parsed as an ordinary
    // free variable.
    Term nts = d_state.bindBoundVar(i.first, i.second);
    ntSyms.push_back(nts);
  }
  Grammar* ret = d_state.mkGrammar(sygusVars, ntSyms);
  // Parse (<GroupedRuleList>^n+1)
  d_lex.eatToken(Token::LPAREN_TOK);
  for (size_t i = 0, nnts = ntSyms.size(); i < nnts; i++)
  {
    // start the non-terminal definition
    d_lex.eatToken(Token::LPAREN_TOK);
    std::string name = parseSymbol(CHECK_DECLARED, SYM_VARIABLE);
    Sort t = parseSort();
    // check that it matches sortedVarNames
    if (sortedVarNames[i].first != name)
    {
      std::stringstream sse;
      sse << "Grouped rule listing " << name
          << " does not match the name (in order) from the predeclaration ("
          << sortedVarNames[i].first << ")." << std::endl;
      d_lex.parseError(sse.str().c_str());
    }
    if (sortedVarNames[i].second != t)
    {
      std::stringstream sse;
      sse << "Type for grouped rule listing " << name
          << " does not match the type (in order) from the predeclaration ("
          << sortedVarNames[i].second << ")." << std::endl;
      d_lex.parseError(sse.str().c_str());
    }
    // read the grouped rule listing (<GTerm>+)
    d_lex.eatToken(Token::LPAREN_TOK);
    Token tok = d_lex.nextToken();
    while (tok != Token::RPAREN_TOK)
    {
      // Lookahead for Constant/Variable.
      bool parsedGTerm = false;
      if (tok == Token::LPAREN_TOK)
      {
        Token tok2 = d_lex.nextToken();
        switch (tok2)
        {
          case Token::SYGUS_CONSTANT_TOK:
          {
            t = parseSort();
            ret->addAnyConstant(ntSyms[i]);
            d_lex.eatToken(Token::RPAREN_TOK);
            parsedGTerm = true;
          }
          break;
          case Token::SYGUS_VARIABLE_TOK:
          {
            t = parseSort();
            ret->addAnyVariable(ntSyms[i]);
            d_lex.eatToken(Token::RPAREN_TOK);
            parsedGTerm = true;
          }
          break;
          default:
            // Did not process tok2.
            d_lex.reinsertToken(tok2);
            break;
        }
      }
      if (!parsedGTerm)
      {
        // We did not process tok. Note that Lex::d_peeked may contain
        // {tok2, LPAREN_TOK} or {tok}.
        d_lex.reinsertToken(tok);
        // parse ordinary term
        Term e = parseTerm();
        ret->addRule(ntSyms[i], e);
      }
      tok = d_lex.nextToken();
    }
    // finish the non-terminal
    d_lex.eatToken(Token::RPAREN_TOK);
  }
  d_lex.eatToken(Token::RPAREN_TOK);
  // pop scope from the pre-declaration
  d_state.popScope();
  return ret;
}

Grammar* Smt2TermParser::parseGrammarOrNull(const std::vector<Term>& sygusVars,
                                            const std::string& fun)
{
  Token t = d_lex.peekToken();
  // note that we assume that the grammar is not present if the input continues
  // with anything other than left parenthesis.
  if (t != Token::LPAREN_TOK)
  {
    return nullptr;
  }
  return parseGrammar(sygusVars, fun);
}

uint32_t Smt2TermParser::parseIntegerNumeral()
{
  d_lex.eatToken(Token::INTEGER_LITERAL);
  return tokenStrToUnsigned();
}

uint32_t Smt2TermParser::tokenStrToUnsigned()
{
  // forbid leading zeroes if in strict mode
  if (d_lex.isStrict())
  {
    if (d_lex.tokenStr()[0] == '0')
    {
      d_lex.parseError("Numeral with leading zeroes are forbidden");
    }
  }
  uint32_t result;
  std::stringstream ss;
  ss << d_lex.tokenStr();
  ss >> result;
  return result;
}

std::string Smt2TermParser::tokenStrToSymbol(Token tok)
{
  std::string id;
  switch (tok)
  {
    case Token::SYMBOL: id = d_lex.tokenStr(); break;
    case Token::QUOTED_SYMBOL:
      id = d_lex.tokenStr();
      // strip off the quotes
      id = id.erase(0, 1);
      id = id.erase(id.size() - 1, 1);
      break;
    case Token::UNTERMINATED_QUOTED_SYMBOL:
      d_lex.parseError("Expected SMT-LIBv2 symbol", true);
      break;
    default:
      d_lex.unexpectedTokenError(tok, "Expected SMT-LIBv2 symbol");
      break;
  }
  return id;
}

std::vector<std::string> Smt2TermParser::parseNumeralList()
{
  std::vector<std::string> numerals;
  Token tok = d_lex.nextToken();
  while (tok == Token::INTEGER_LITERAL)
  {
    numerals.emplace_back(d_lex.tokenStr());
    tok = d_lex.nextToken();
  }
  d_lex.reinsertToken(tok);
  return numerals;
}

std::string Smt2TermParser::parseStr(bool unescape)
{
  d_lex.eatToken(Token::STRING_LITERAL);
  std::string s = d_lex.tokenStr();
  if (unescape)
  {
    unescapeString(s);
  }
  return s;
}

void Smt2TermParser::unescapeString(std::string& s)
{
  // strip off the quotes
  s = s.erase(0, 1);
  s = s.erase(s.size() - 1, 1);
  for (size_t i = 0, ssize = s.size(); i < ssize; i++)
  {
    if ((unsigned)s[i] > 127 && !isprint(s[i]))
    {
      d_lex.parseError(
          "Extended/unprintable characters are not "
          "part of SMT-LIB, and they must be encoded "
          "as escape sequences");
    }
  }
  size_t dst = 0;
  for (size_t src = 0; src<s.size(); ++src, ++dst)
  {
    s[dst] = s[src];
    if (s[src]=='"')
    {
      ++src;
    }
  }
  s.erase(dst);
}

}  // namespace parser
}  // namespace cvc5
