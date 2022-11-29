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
  Token tok = d_lex.nextToken();
  while (tok != Token::RPAREN_TOK)
  {
    d_lex.reinsertToken(tok);
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
  std::string s = d_lex.YYText();
  // strip off the initial colon
  return s.substr(1);
}

Grammar* Smt2TermParser::parseGrammar(const std::vector<Term>& sygusVars,
                                      const std::string& fun)
{
  // We read a sorted variable list.
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
    // read the grouped rule listing
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
          case SYGUS_CONSTANT_TOK:
          {
            t = parseSort();
            ret->addAnyConstant(ntSyms[i]);
            d_lex.eatToken(Token::RPAREN_TOK);
            parsedGTerm = true;
          }
          break;
          case SYGUS_VARIABLE_TOK:
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
  Assert(dnames.size() == arities.size()
         || (dnames.size() == 1 && arities.empty()));
  std::vector<DatatypeDecl> dts;
  d_state.pushScope();
  // Declare the datatypes that are currently being defined as unresolved
  // types. If we do not know the arity of the datatype yet, we wait to
  // define it until parsing the preamble of its body, which may optionally
  // involve `par`. This is limited to the case of single datatypes defined
  // via declare-datatype, and hence no datatype body is parsed without
  // having all types declared. This ensures we can parse datatypes with
  // nested recursion, e.g. datatypes D having a subfield type
  // (Array Int D).
  for (unsigned i = 0, dsize = dnames.size(); i < dsize; i++)
  {
    if (i >= arities.size())
    {
      // do not know the arity yet
      continue;
    }
    d_state.mkUnresolvedType(dnames[i], arities[i]);
  }
  d_lex.eatToken(Token::LPAREN_TOK);
  // while we get another datatype declaration, or close the list
  while (d_lex.eatTokenChoice(Token::LPAREN_TOK, Token::RPAREN_TOK))
  {
    std::vector<Sort> params;
    size_t i = dts.size();
    Trace("parser-dt") << "Processing datatype #" << i << std::endl;
    if (i >= dnames.size())
    {
      d_lex.parseError("Too many datatypes defined in this block.");
    }
    Token tok = d_lex.nextToken();
    bool pushedScope = false;
    if (tok == PAR_TOK)
    {
      pushedScope = true;
      d_state.pushScope();
      std::vector<std::string> symList =
          parseSymbolList(CHECK_UNDECLARED, SYM_SORT);
      for (const std::string& sym : symList)
      {
        params.push_back(d_state.mkSort(sym));
      }
      Trace("parser-dt") << params.size() << " parameters for " << dnames[i]
                         << std::endl;
      dts.push_back(
          d_state.getSolver()->mkDatatypeDecl(dnames[i], params, isCo));
    }
    else
    {
      d_lex.reinsertToken(tok);
      dts.push_back(
          d_state.getSolver()->mkDatatypeDecl(dnames[i], params, isCo));
    }
    if (i >= arities.size())
    {
      // if the arity is not yet fixed, declare it as an unresolved type
      d_state.mkUnresolvedType(dnames[i], params.size());
    }
    else if (arities[i] >= 0 && params.size() != arities[i])
    {
      // if the arity was fixed by prelude and is not equal to the number of
      // parameters
      d_lex.parseError("Wrong number of parameters for datatype.");
    }
    // read constructor definition list, populate into the current datatype
    parseConstructorDefinitionList(dts.back());
    if (pushedScope)
    {
      d_lex.eatToken(Token::RPAREN_TOK);
      d_state.popScope();
    }
    d_lex.eatToken(Token::RPAREN_TOK);
  }
  if (dts.size() != dnames.size())
  {
    d_lex.parseError("Wrong number of datatypes provided.");
  }
  d_state.popScope();
  return dts;
}

void Smt2TermParser::parseConstructorDefinitionList(DatatypeDecl& type)
{
  d_lex.eatToken(Token::LPAREN_TOK);
  // parse another constructor or close the list
  while (d_lex.eatTokenChoice(Token::LPAREN_TOK, Token::RPAREN_TOK))
  {
    std::string name = parseSymbol(CHECK_NONE, SYM_VARIABLE);
    DatatypeConstructorDecl* ctor = new DatatypeConstructorDecl(
        d_state.getSolver()->mkDatatypeConstructorDecl(name));
    // parse another selector or close the current constructor
    while (d_lex.eatTokenChoice(Token::LPAREN_TOK, Token::RPAREN_TOK))
    {
      std::string id = parseSymbol(CHECK_NONE, SYM_SORT);
      Sort t = parseSort();
      ctor->addSelector(id, t);
      Trace("parser-idt") << "selector: " << id << " of type " << t
                          << std::endl;
      d_lex.eatToken(Token::RPAREN_TOK);
    }
    // make the constructor
    type.addConstructor(*ctor);
    Trace("parser-idt") << "constructor: " << name << std::endl;
    delete ctor;
  }
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
        d_lex.parseError(
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
