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
  Term ret;
  Token tok;
  std::vector<std::pair<ParseOp, std::vector<Term>>> tstack;
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
          case Token::AS_TOK:
          {
            // a standalone qualifier identifier
          }
          break;
          case Token::INDEX_TOK:
          {
            // a standalone qualified identifier
          }
          break;
          case Token::LPAREN_TOK:
          {
            // must be a qualified identifier
          }
          break;
          case Token::FORALL_TOK:
          case Token::EXISTS_TOK:
          {
          }
          break;
          case Token::LET_TOK:
          {
          }
          break;
          case Token::MATCH_TOK:
          {
          }
          break;
          case Token::ATTRIBUTE_TOK:
          {
          }
          break;
          case Token::SYMBOL:
          {
            // function identifier
          }
          break;
          default: break;
        }
      }
      break;
      // ------------------- close paren
      case Token::RPAREN_TOK:
      {
      }
      break;
      // ------------------- base cases
      case Token::SYMBOL:
      {
      }
      break;
      case Token::INTEGER_LITERAL:
      {
      }
      break;
      case Token::DECIMAL_LITERAL:
      {
      }
      break;
      case Token::HEX_LITERAL:
      {
      }
      break;
      case Token::BINARY_LITERAL:
      {
      }
      break;
      case Token::STRING_LITERAL:
      {
      }
      break;
      default: break;
    }
  } while (!tstack.empty());

  return ret;
}
std::vector<Term> Smt2TermParser::parseTermList()
{
  d_lex.eatToken(Token::LPAREN_TOK);
  std::vector<Term> terms;
  Token tok = d_lex.peekToken();
  while (tok != Token::RPAREN_TOK)
  {
    Term t = parseTerm();
    terms.push_back(t);
    tok = d_lex.peekToken();
  }
  return terms;
}

Term Smt2TermParser::parseSymbolicExpr()
{
  Term t;
  // TODO
  return t;
}

Sort Smt2TermParser::parseSort()
{
  Sort s;
  // TODO
  return s;
}

std::vector<Sort> Smt2TermParser::parseSortList()
{
  d_lex.eatToken(Token::LPAREN_TOK);
  std::vector<Sort> sorts;
  Token tok = d_lex.peekToken();
  while (tok != Token::RPAREN_TOK)
  {
    Sort s = parseSort();
    sorts.push_back(s);
    tok = d_lex.peekToken();
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
  std::string id;
  switch (tok)
  {
    case Token::SYMBOL:
    {
      id = d_lex.YYText();
    }
    break;
    case Token::QUOTED_SYMBOL:
    {
      id = d_lex.YYText();
      // strip off the quotes
      id = id.substr(1, id.size() - 2);
    }
    break;
    default:
      d_lex.unexpectedTokenError(tok, "Expected SMT-LIBv2 symbol");
      break;
  }
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
  Token tok = d_lex.peekToken();
  while (tok != Token::RPAREN_TOK)
  {
    std::string sym = parseSymbol(check, type);
    symbols.push_back(sym);
    tok = d_lex.peekToken();
  }
  return symbols;
}

std::string Smt2TermParser::parseKeyword()
{
  d_lex.eatToken(Token::KEYWORD);
  std::string s = d_lex.YYText();
  // strip off the initial colon
  return s.substr(1);
}

Grammar* Smt2TermParser::parseGrammar(const std::vector<Term>& sygusVars,
                                      const std::string& fun)
{
  // TODO
  return nullptr;
}

Grammar* Smt2TermParser::parseGrammarOrNull(const std::vector<Term>& sygusVars,
                                            const std::string& fun)
{
  Token t = d_lex.peekToken();
  if (t != Token::LPAREN_TOK)
  {
    return nullptr;
  }
  return parseGrammar(sygusVars, fun);
}

size_t Smt2TermParser::parseIntegerNumeral()
{
  d_lex.eatToken(Token::INTEGER_LITERAL);
  // TODO: leading zeroes in strict mode?
  size_t result;
  std::stringstream ss;
  ss << d_lex.YYText();
  ss >> result;
  return result;
}

std::vector<DatatypeDecl> Smt2TermParser::parseDatatypeDef(
    bool isCo,
    const std::vector<std::string>& dnames,
    const std::vector<size_t>& arities)
{
  std::vector<DatatypeDecl> dts;
  return dts;
}

std::string Smt2TermParser::parseStr(bool unescape)
{
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
