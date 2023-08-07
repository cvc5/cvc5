/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

/**
 * Definition of state identifiers when parsing terms
 *
 * This is required for non-recursive parsing of terms. Note that in SMT-LIB,
 * terms generally are of the form (...anything not involving terms... <term>*)
 * However, let-terms, match-terms, and terms appearing within attributes
 * for term annotations (e.g. quantifier patterns) are exceptions to this.
 * Thus, in the main parsing loop in parseTerm below, we require tracking
 * the context we are in, which dictates how to setup parsing the term after
 * the current one.
 *
 * In each state, the stack contains a topmost ParseOp `op` and a list of
 * arguments `args`, which give a recipe for the term we are parsing. The data
 * in these depend on the context we are in, as documented below.
 */
enum class ParseCtx
{
  /**
   * NEXT_ARG: in context (<op> <term>* <term>
   * `op` specifies the operator we parsed.
   * `args` contain the accumulated list of arguments.
   */
  NEXT_ARG,
  /**
   * CLOSURE_NEXT_ARG: in context (<closure> <variable_list> <term>* <term>
   * `op` specifies the (closure) operator we parsed.
   * `args` contain the variable list and the accumulated list of arguments.
   */
  CLOSURE_NEXT_ARG,
  /**
   * Let bindings
   *
   * LET_NEXT_BIND: in context (let (<binding>* (<symbol> <term>
   * `op` contains:
   * - d_name: the name of last bound variable.
   *
   * LET_BODY: in context (let (<binding>*) <term>
   */
  LET_NEXT_BIND,
  LET_BODY,
  /**
   * Match terms
   *
   * MATCH_HEAD: in context (match <term>
   *
   * MATCH_NEXT_CASE: in context (match <term> (<case>* (<pattern> <term>
   * `op` contains:
   * - d_type: set to the type of the head.
   * `args` contain the head term and the accumulated list of case terms.
   */
  MATCH_HEAD,
  MATCH_NEXT_CASE,
  /**
   * Term annotations
   *
   * TERM_ANNOTATE_BODY: in context (! <term>
   *
   * TERM_ANNOTATE_NEXT_ATTR: in context (! <term> <attr>* <keyword> <term_spec>
   * where notice that <term_spec> may be a term or a list of terms.
   * `op` contains:
   * - d_expr: the body of the term annotation.
   * - d_kind: the kind to apply to the current <term_spec> (if any).
   * `args` contain the accumulated patterns or quantifier attributes.
   */
  TERM_ANNOTATE_BODY,
  TERM_ANNOTATE_NEXT_ATTR
};

Smt2TermParser::Smt2TermParser(Smt2Lexer& lex, Smt2State& state)
    : d_lex(lex), d_state(state)
{
}

Term Smt2TermParser::parseTerm()
{
  // the last parsed term
  Term ret;
  // a request was made to update the current parse context
  bool needsUpdateCtx = false;
  // the last token we read
  Token tok;
  // The stack(s) containing the parse context, and the recipe for the
  // current we are building.
  std::vector<ParseCtx> xstack;
  std::vector<std::pair<ParseOp, std::vector<Term>>> tstack;
  // Let bindings, dynamically allocated for each let in scope.
  std::vector<std::vector<std::pair<std::string, Term>>> letBinders;
  Solver* slv = d_state.getSolver();
  do
  {
    Assert(tstack.size() == xstack.size());
    // At this point, we are ready to parse the next term
    tok = d_lex.nextToken();
    Term currTerm;
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
            // a standalone qualified identifier
            ParseOp op = continueParseQualifiedIdentifier(false);
            ret = op.d_expr;
            if (ret.isNull() || op.d_kind == INTERNAL_KIND)
            {
              d_lex.parseError("Unexpected qualified identifier");
            }
          }
          break;
          case Token::INDEX_TOK:
          {
            // a standalone indexed symbol
            ParseOp op = continueParseIndexedIdentifier(false);
            ret = op.d_expr;
            if (ret.isNull())
            {
              d_lex.parseError("Unexpected indexed symbol");
            }
          }
          break;
          case Token::LPAREN_TOK:
          {
            tok = d_lex.nextToken();
            switch (tok)
            {
              case Token::AS_TOK:
              {
                // a qualified identifier operator
                ParseOp op = continueParseQualifiedIdentifier(true);
                xstack.emplace_back(ParseCtx::NEXT_ARG);
                tstack.emplace_back(op, std::vector<Term>());
              }
              break;
              case Token::INDEX_TOK:
              {
                // an indexed identifier operator
                ParseOp op = continueParseIndexedIdentifier(true);
                xstack.emplace_back(ParseCtx::NEXT_ARG);
                tstack.emplace_back(op, std::vector<Term>());
              }
              break;
              default:
                d_lex.unexpectedTokenError(
                    tok, "Expected SMT-LIBv2 qualified indentifier");
                break;
            }
          }
          break;
          case Token::LET_TOK:
          {
            xstack.emplace_back(ParseCtx::LET_NEXT_BIND);
            tstack.emplace_back(ParseOp(), std::vector<Term>());
            needsUpdateCtx = true;
            letBinders.emplace_back();
          }
          break;
          case Token::MATCH_TOK:
          {
            xstack.emplace_back(ParseCtx::MATCH_HEAD);
            tstack.emplace_back();
          }
          break;
          case Token::ATTRIBUTE_TOK:
          {
            xstack.emplace_back(ParseCtx::TERM_ANNOTATE_BODY);
            tstack.emplace_back();
          }
          break;
          case Token::SYMBOL:
          case Token::QUOTED_SYMBOL:
          {
            // function identifier
            ParseOp op;
            op.d_name = tokenStrToSymbol(tok);
            std::vector<Term> args;
            if (d_state.isClosure(op.d_name))
            {
              // if it is a closure, immediately read the bound variable list
              d_state.pushScope();
              std::vector<std::pair<std::string, Sort>> sortedVarNames =
                  parseSortedVarList();
              if (sortedVarNames.empty())
              {
                d_lex.parseError("Expected non-empty sorted variable list");
              }
              std::vector<Term> vs = d_state.bindBoundVars(sortedVarNames);
              Term vl = slv->mkTerm(VARIABLE_LIST, vs);
              args.push_back(vl);
              xstack.emplace_back(ParseCtx::CLOSURE_NEXT_ARG);
            }
            else
            {
              xstack.emplace_back(ParseCtx::NEXT_ARG);
            }
            tstack.emplace_back(op, args);
          }
          break;
          case Token::UNTERMINATED_QUOTED_SYMBOL:
            d_lex.parseError("Expected SMT-LIBv2 operator", true);
            break;
          default:
            d_lex.unexpectedTokenError(tok, "Expected SMT-LIBv2 operator");
            break;
        }
      }
      break;
      // ------------------- close paren
      case Token::RPAREN_TOK:
      {
        // should only be here if we are expecting arguments
        if (tstack.empty() || (xstack.back() != ParseCtx::NEXT_ARG
               && xstack.back() != ParseCtx::CLOSURE_NEXT_ARG))
        {
          d_lex.unexpectedTokenError(
              tok, "Mismatched parentheses in SMT-LIBv2 term");
        }
        // Construct the application term specified by tstack.back()
        ParseOp& op = tstack.back().first;
        ret = d_state.applyParseOp(op, tstack.back().second);
        // process the scope change if a closure
        if (xstack.back() == ParseCtx::CLOSURE_NEXT_ARG)
        {
          // if we were a closure, pop a scope
          d_state.popScope();
        }
        // pop the stack
        tstack.pop_back();
        xstack.pop_back();
      }
      break;
      // ------------------- base cases
      case Token::SYMBOL:
      case Token::QUOTED_SYMBOL:
      {
        std::string name = tokenStrToSymbol(tok);
        ret = d_state.getVariable(name);
      }
      break;
      case Token::UNTERMINATED_QUOTED_SYMBOL:
        d_lex.parseError("Expected SMT-LIBv2 term", true);
        break;
      case Token::INTEGER_LITERAL:
      {
        ret = d_state.mkRealOrIntFromNumeral(d_lex.tokenStr());
      }
      break;
      case Token::DECIMAL_LITERAL:
      {
        ret = d_state.getSolver()->mkReal(d_lex.tokenStr());
      }
      break;
      case Token::HEX_LITERAL:
      {
        std::string hexStr = d_lex.tokenStr();
        hexStr = hexStr.substr(2);
        ret = d_state.getSolver()->mkBitVector(hexStr.size() * 4, hexStr, 16);
      }
      break;
      case Token::BINARY_LITERAL:
      {
        std::string binStr = d_lex.tokenStr();
        binStr = binStr.substr(2);
        ret = d_state.getSolver()->mkBitVector(binStr.size(), binStr, 2);
      }
      break;
      case Token::FIELD_LITERAL:
      {
        std::string ffStr = d_lex.tokenStr();
        Assert(ffStr.find("#f") == 0);
        size_t mPos = ffStr.find("m");
        Assert(mPos > 2);
        std::string ffValStr = ffStr.substr(2, mPos - 2);
        std::string ffModStr = ffStr.substr(mPos + 1);
        Sort ffSort = d_state.getSolver()->mkFiniteFieldSort(ffModStr);
        ret = d_state.getSolver()->mkFiniteFieldElem(ffValStr, ffSort);
      }
      break;
      case Token::STRING_LITERAL:
      {
        std::string s = d_lex.tokenStr();
        unescapeString(s);
        ret = d_state.getSolver()->mkString(s, true);
      }
      break;
      default:
        d_lex.unexpectedTokenError(tok, "Expected SMT-LIBv2 term");
        break;
    }

    // Based on the current context, setup next parsed term.
    // We do this only if a context is allocated (!tstack.empty()) and we
    // either just finished parsing a term (!ret.isNull()), or otherwise have
    // indicated that we need to update the context (needsUpdateCtx).
    while (!tstack.empty() && (!ret.isNull() || needsUpdateCtx))
    {
      needsUpdateCtx = false;
      switch (xstack.back())
      {
        // ------------------------- argument lists
        case ParseCtx::NEXT_ARG:
        case ParseCtx::CLOSURE_NEXT_ARG:
        {
          Assert(!ret.isNull());
          // add it to the list of arguments and clear
          tstack.back().second.push_back(ret);
          ret = Term();
        }
        break;
        // ------------------------- let terms
        case ParseCtx::LET_NEXT_BIND:
        {
          // if we parsed a term, process it as a binding
          if (!ret.isNull())
          {
            Assert(!letBinders.empty());
            std::vector<std::pair<std::string, Term>>& bs = letBinders.back();
            // add binding from the symbol to ret
            bs.emplace_back(tstack.back().first.d_name, ret);
            ret = Term();
            // close the current binding
            d_lex.eatToken(Token::RPAREN_TOK);
          }
          else
          {
            // eat the opening left parenthesis of the binding list
            d_lex.eatToken(Token::LPAREN_TOK);
          }
          // see if there is another binding
          if (d_lex.eatTokenChoice(Token::LPAREN_TOK, Token::RPAREN_TOK))
          {
            // (, another binding: setup parsing the next term
            // get the symbol and store in the ParseOp
            tstack.back().first.d_name = parseSymbol(CHECK_NONE, SYM_VARIABLE);
          }
          else
          {
            // ), we are now looking for the body of the let
            xstack[xstack.size() - 1] = ParseCtx::LET_BODY;
            // push scope
            d_state.pushScope();
            // implement the bindings
            Assert(!letBinders.empty());
            const std::vector<std::pair<std::string, Term>>& bs =
                letBinders.back();
            for (const std::pair<std::string, Term>& b : bs)
            {
              d_state.defineVar(b.first, b.second);
            }
            // done with the binders
            letBinders.pop_back();
          }
        }
        break;
        case ParseCtx::LET_BODY:
        {
          // the let body is the returned term
          d_lex.eatToken(Token::RPAREN_TOK);
          xstack.pop_back();
          tstack.pop_back();
          // pop scope
          d_state.popScope();
        }
        break;
        // ------------------------- match terms
        case ParseCtx::MATCH_HEAD:
        {
          Assert(!ret.isNull());
          // add the head
          tstack.back().second.push_back(ret);
          Sort retSort = ret.getSort();
          // eagerly check if datatype
          if (!retSort.isDatatype())
          {
            d_lex.parseError("Cannot match on non-datatype term.");
          }
          // we use a placeholder to store the type (retSort), which is
          // used during MATCH_NEXT_CASE
          tstack.back().first.d_kind = INTERNAL_KIND;
          tstack.back().first.d_expr = slv->mkConst(retSort, "_placeholder_");
          ret = Term();
          xstack[xstack.size() - 1] = ParseCtx::MATCH_NEXT_CASE;
          needsUpdateCtx = true;
        }
        break;
        case ParseCtx::MATCH_NEXT_CASE:
        {
          if (!ret.isNull())
          {
            // add it to the list of arguments and clear
            tstack.back().second.push_back(ret);
            ret = Term();
            // pop the scope
            d_state.popScope();
          }
          else
          {
            // eat the opening left parenthesis of the case list
            d_lex.eatToken(Token::LPAREN_TOK);
          }
          // see if there is another case
          if (d_lex.eatTokenChoice(Token::LPAREN_TOK, Token::RPAREN_TOK))
          {
            // push the scope
            d_state.pushScope();
            // parse the pattern, which also does the binding
            Assert(!tstack.back().first.d_expr.isNull());
            std::vector<Term> boundVars;
            Term pattern = parseMatchCasePattern(
                tstack.back().first.d_expr.getSort(), boundVars);
            // If we bound variables when parsing the pattern, we will construct
            // a match bind case
            ParseOp op;
            std::vector<Term> args;
            if (!boundVars.empty())
            {
              op.d_kind = MATCH_BIND_CASE;
              Term vl = slv->mkTerm(VARIABLE_LIST, boundVars);
              args.push_back(slv->mkTerm(VARIABLE_LIST, boundVars));
            }
            else
            {
              op.d_kind = MATCH_CASE;
            }
            args.push_back(pattern);
            // we now look for the body of the case + closing right parenthesis
            xstack.emplace_back(ParseCtx::NEXT_ARG);
            tstack.emplace_back(op, args);
          }
          else
          {
            // Finished with match, now just wait for the closing right
            // parenthesis. Set the kind to construct as MATCH and clear the
            // head sort.
            ParseOp& op = tstack.back().first;
            op.d_kind = MATCH;
            op.d_expr = Term();
            xstack[xstack.size() - 1] = ParseCtx::NEXT_ARG;
          }
        }
        break;
        // ------------------------- annotated terms
        case ParseCtx::TERM_ANNOTATE_BODY:
        {
          // save ret as the expression and clear
          tstack.back().first.d_expr = ret;
          ret = Term();
          // now parse attribute list
          xstack[xstack.size() - 1] = ParseCtx::TERM_ANNOTATE_NEXT_ATTR;
          needsUpdateCtx = true;
          // ensure there is at least one attribute
          tok = d_lex.peekToken();
          if (tok == Token::RPAREN_TOK)
          {
            d_lex.parseError(
                "Expecting at least one attribute for term annotation.");
          }
        }
        break;
        case ParseCtx::TERM_ANNOTATE_NEXT_ATTR:
        {
          if (!ret.isNull())
          {
            // if we got here, we either:
            // (1) parsed a single term (the current ParseOp::d_kind was set)
            // (2) a list of terms in a nested context.
            if (tstack.back().first.d_kind != NULL_TERM)
            {
              // if (1), apply d_kind to the argument and reset d_kind
              ret = slv->mkTerm(tstack.back().first.d_kind, {ret});
              tstack.back().first.d_kind = NULL_TERM;
            }
            tstack.back().second.push_back(ret);
            ret = Term();
          }
          // see if there is another keyword
          if (d_lex.eatTokenChoice(Token::KEYWORD, Token::RPAREN_TOK))
          {
            std::string key = d_lex.tokenStr();
            // Based on the keyword, determine the context.
            // Set needsUpdateCtx to true if we are finished parsing the
            // current attribute.
            Kind attrKind = NULL_TERM;
            Term attrValue;
            if (key == ":inst-add-to-pool")
            {
              attrKind = INST_ADD_TO_POOL;
            }
            else if (key == ":quant-inst-max-level")
            {
              // a numeral
              d_lex.eatToken(Token::INTEGER_LITERAL);
              attrValue = slv->mkInteger(d_lex.tokenStr());
            }
            else if (key == ":named")
            {
              Assert(!tstack.back().first.d_expr.isNull());
              // expression is the body of the term annotation
              std::string sym = parseSymbol(CHECK_UNDECLARED, SYM_VARIABLE);
              d_state.notifyNamedExpression(tstack.back().first.d_expr, sym);
              needsUpdateCtx = true;
            }
            else if (key == ":no-pattern")
            {
              // a single term, set the current kind
              tstack.back().first.d_kind = INST_NO_PATTERN;
            }
            else if (key == ":pattern")
            {
              attrKind = INST_PATTERN;
            }
            else if (key == ":pool")
            {
              attrKind = INST_POOL;
            }
            else if (key == ":qid")
            {
              std::string sym = parseSymbol(CHECK_UNDECLARED, SYM_VARIABLE);
              // must create a variable whose name is the name of the quantified
              // formula, not a string.
              attrValue = slv->mkConst(slv->getBooleanSort(), sym);
            }
            else if (key == ":skolem-add-to-pool")
            {
              attrKind = SKOLEM_ADD_TO_POOL;
            }
            else
            {
              // warn that the attribute is not supported
              d_state.attributeNotSupported(d_lex.tokenStr());
              tok = d_lex.nextToken();
              // We don't know whether to expect an attribute value. Thus,
              // we will either see keyword (the next attribute), rparen
              // (the term annotation is finished), or else parse as generic
              // symbolic expression for the current attribute.
              switch (tok)
              {
                case Token::KEYWORD:
                case Token::RPAREN_TOK:
                  // finished with this attribute, go to the next one if it
                  // exists.
                  d_lex.reinsertToken(tok);
                  break;
                default:
                  // ignore the symbolic expression that follows
                  d_lex.reinsertToken(tok);
                  parseSymbolicExpr();
                  // will parse another attribute
                  break;
              }
              needsUpdateCtx = true;
            }
            if (attrKind != NULL_TERM)
            {
              // e.g. `:pattern (t1 ... tn)`, where we have parsed `:pattern (`
              d_lex.eatToken(Token::LPAREN_TOK);
              // Will parse list as arguments to the kind + closing parenthesis.
              ParseOp op;
              op.d_kind = attrKind;
              tstack.emplace_back(op, std::vector<Term>());
              xstack.emplace_back(ParseCtx::NEXT_ARG);
            }
            else if (!attrValue.isNull())
            {
              // if we constructed a term as the attribute value, make into
              // an INST_ATTRIBUTE and add it to args
              std::string keyName = key.substr(1);
              Term keyword = slv->mkString(keyName);
              Term iattr = slv->mkTerm(INST_ATTRIBUTE, {keyword, attrValue});
              tstack.back().second.push_back(iattr);
              needsUpdateCtx = true;
            }
          }
          // if we instead saw a RPAREN_TOK, we are finished
          else
          {
            Assert(!tstack.back().first.d_expr.isNull());
            // finished parsing attributes, we will return the original term
            ret = tstack.back().first.d_expr;
            Term ipl;
            // if args non-empty, construct an instantiation pattern list
            if (!tstack.back().second.empty())
            {
              ipl = slv->mkTerm(INST_PATTERN_LIST, tstack.back().second);
            }
            xstack.pop_back();
            tstack.pop_back();
            // If we constructed an instantiation pattern list, it should have
            // been a quantified formula body. Check the next scope up.
            if (!ipl.isNull())
            {
              if (tstack.empty() || xstack.back() != ParseCtx::CLOSURE_NEXT_ARG
                  || tstack.back().second.size() != 1)
              {
                d_lex.parseError(
                    "Patterns and quantifier attributes should be applied to "
                    "quantified formula bodies only.");
              }
              // Push ret and the instantiation pattern list and clear. We
              // wait for the closing parenthesis, which should follow.
              tstack.back().second.push_back(ret);
              tstack.back().second.push_back(ipl);
              ret = Term();
            }
          }
        }
        break;
        default: break;
      }
    }
    // otherwise ret will be returned
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
    tok = d_lex.nextToken();
  }
  return terms;
}

Term Smt2TermParser::parseSymbolicExpr()
{
  Term ret;
  Token tok;
  std::vector<std::vector<Term>> sstack;
  Solver* slv = d_state.getSolver();
  Sort dummyType = slv->getBooleanSort();
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
        ret = slv->mkVar(dummyType, str);
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
        if (tok2 == Token::SYMBOL)
        {
          std::string tokenStr(d_lex.tokenStr());
          if (tokenStr == "Constant")
          {
            t = parseSort();
            ret->addAnyConstant(ntSyms[i]);
            d_lex.eatToken(Token::RPAREN_TOK);
            parsedGTerm = true;
          }
          else if (tokenStr == "Variable")
          {
            t = parseSort();
            ret->addAnyVariable(ntSyms[i]);
            d_lex.eatToken(Token::RPAREN_TOK);
            parsedGTerm = true;
          }
          else
          {
            // Did not process tok2.
            d_lex.reinsertToken(tok2);
          }
        }
        else
        {
          // Did not process tok2.
          d_lex.reinsertToken(tok2);
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
    std::string token = d_lex.tokenStr();
    if (token.size() > 1 && token[0] == '0')
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

std::vector<DatatypeDecl> Smt2TermParser::parseDatatypesDef(
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
  // while we get another datatype declaration, or close the list
  Token tok = d_lex.nextToken();
  while (tok == Token::LPAREN_TOK)
  {
    std::vector<Sort> params;
    size_t i = dts.size();
    Trace("parser-dt") << "Processing datatype #" << i << std::endl;
    if (i >= dnames.size())
    {
      d_lex.parseError("Too many datatypes defined in this block.");
    }
    tok = d_lex.nextToken();
    bool pushedScope = false;
    if (tok == Token::PAR_TOK)
    {
      pushedScope = true;
      d_state.pushScope();
      std::vector<std::string> symList =
          parseSymbolList(CHECK_UNDECLARED, SYM_SORT);
      if (symList.empty())
      {
        d_lex.parseError("Expected non-empty parameter list");
      }
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
      // we will parse the parentheses-enclosed construct list below
      d_lex.reinsertToken(Token::LPAREN_TOK);
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
    tok = d_lex.nextToken();
  }
  if (dts.size() != dnames.size())
  {
    d_lex.unexpectedTokenError(tok, "Wrong number of datatypes provided.");
  }
  d_lex.reinsertToken(tok);
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
    DatatypeConstructorDecl ctor(
        d_state.getSolver()->mkDatatypeConstructorDecl(name));
    // parse another selector or close the current constructor
    while (d_lex.eatTokenChoice(Token::LPAREN_TOK, Token::RPAREN_TOK))
    {
      std::string id = parseSymbol(CHECK_NONE, SYM_SORT);
      Sort t = parseSort();
      ctor.addSelector(id, t);
      Trace("parser-idt") << "selector: " << id << " of type " << t
                          << std::endl;
      d_lex.eatToken(Token::RPAREN_TOK);
    }
    // make the constructor
    type.addConstructor(ctor);
    Trace("parser-idt") << "constructor: " << name << std::endl;
  }
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

ParseOp Smt2TermParser::continueParseIndexedIdentifier(bool isOperator)
{
  ParseOp p;
  std::string name = parseSymbol(CHECK_NONE, SYM_VARIABLE);
  // parse the list of numerals or symbols
  std::vector<std::string> symbols;
  std::vector<uint32_t> numerals;
  // we currently only have symbols that are indexed by only numerals, or
  // are indexed by a symbol, followed by combinations of symbols/numerals.
  Token tok = d_lex.nextToken();
  while (tok != Token::RPAREN_TOK)
  {
    switch (tok)
    {
      case Token::INTEGER_LITERAL:
        if (symbols.empty())
        {
          numerals.push_back(tokenStrToUnsigned());
        }
        else
        {
          // If we parsed a symbol, treat the remaining indices as symbols
          // This is required for parsing fmf.card.
          symbols.push_back(d_lex.tokenStr());
        }
        break;
      case Token::SYMBOL:
      case Token::HEX_LITERAL:
        // (_ char <hex_literal>) expects a hex literal
        symbols.push_back(d_lex.tokenStr());
        break;
      default:
        d_lex.unexpectedTokenError(
            tok, "Expected index while parsing indexed identifier");
        break;
    }
    tok = d_lex.nextToken();
  }
  if (numerals.empty() && symbols.empty())
  {
    d_lex.parseError(std::string("No indices provided for symbol " + name));
  }
  // if indexed by numerals
  if (!numerals.empty())
  {
    if (!isOperator)
    {
      // resolve the index constant
      p.d_expr = d_state.mkIndexedConstant(name, numerals);
    }
    else
    {
      // In some cases, we don't know which kind to use until we know the type
      // of the arguments, which is the case for:
      // - to_fp
      // - (_ tuple.select n) and (_ tuple.update n)
      // For consistency, we always construct the op lazily.
      p.d_name = name;
      p.d_indices = numerals;
      p.d_kind = UNDEFINED_KIND;
    }
  }
  // otherwise, indexed by symbols
  else if (!isOperator)
  {
    // handles:
    // - fmf.card indexed by Type symbol + numeral
    // - char indexed by HEX
    p.d_expr = d_state.mkIndexedConstant(name, symbols);
  }
  else
  {
    // handles:
    // - testers and updaters indexed by constructor names
    Kind k = d_state.getIndexedOpKind(name);
    if (k != APPLY_UPDATER && k != APPLY_TESTER)
    {
      d_lex.parseError(std::string("Unexpected indexed symbol " + name));
    }
    if (symbols.size() != 1)
    {
      d_lex.parseError(std::string("Unexpected number of indices for " + name));
    }
    p.d_kind = k;
    p.d_name = symbols[0];
  }
  return p;
}

ParseOp Smt2TermParser::continueParseQualifiedIdentifier(bool isOperator)
{
  ParseOp op;
  Token tok = d_lex.nextToken();
  switch (tok)
  {
    case Token::LPAREN_TOK:
      tok = d_lex.nextToken();
      switch (tok)
      {
        case Token::INDEX_TOK:
          op = continueParseIndexedIdentifier(isOperator);
          break;
        default:
          d_lex.unexpectedTokenError(tok,
                                     "Expected (indexed) identifier while "
                                     "parsing qualified identifier");
          break;
      }
      break;
    case Token::SYMBOL:
    case Token::QUOTED_SYMBOL: op.d_name = tokenStrToSymbol(tok); break;
    case Token::UNTERMINATED_QUOTED_SYMBOL:
      d_lex.parseError("Expected identifier while parsing qualified identifier",
                       true);
      break;
    default:
      d_lex.unexpectedTokenError(
          tok, "Expected identifier while parsing qualified identifier");
      break;
  }
  // parse a sort
  Sort type = parseSort();
  // close parentheses
  d_lex.eatToken(Token::RPAREN_TOK);
  // apply the type ascription to the parsed op
  d_state.parseOpApplyTypeAscription(op, type);
  return op;
}

Term Smt2TermParser::parseMatchCasePattern(Sort headSort,
                                           std::vector<Term>& boundVars)
{
  if (d_lex.eatTokenChoice(Token::SYMBOL, Token::LPAREN_TOK))
  {
    // a nullary constructor or variable, depending on if the symbol is declared
    std::string name = d_lex.tokenStr();
    if (d_state.isDeclared(name, SYM_VARIABLE))
    {
      Term pat = d_state.getVariable(name);
      Sort type = pat.getSort();
      if (!type.isDatatype())
      {
        d_lex.parseError(
            "Must apply constructors of arity greater than 0 to arguments in "
            "pattern.");
      }
      // make nullary constructor application
      return pat;
    }
    // it has the type of the head expr
    Term pat = d_state.bindBoundVar(name, headSort);
    boundVars.push_back(pat);
    return pat;
  }
  // a non-nullary constructor
  // We parse a constructor name
  const Datatype& dt = headSort.getDatatype();
  std::string cname = parseSymbol(CHECK_DECLARED, SYM_VARIABLE);
  const DatatypeConstructor& dc = dt.getConstructor(cname);
  // get the constructor, which could be instantiated based on the head type
  // if we are a parametric datatype
  Term f = dt.isParametric() ? dc.getInstantiatedTerm(headSort) : dc.getTerm();
  // f should be a constructor
  Sort type = f.getSort();
  Assert(type.isDatatypeConstructor());
  Trace("parser-dt") << "Pattern head : " << f << " " << type << std::endl;
  std::vector<Sort> argTypes = type.getDatatypeConstructorDomainSorts();
  // now, parse symbols that are interpreted as bindings for the argument
  // types
  while (d_lex.eatTokenChoice(Token::SYMBOL, Token::RPAREN_TOK))
  {
    if (boundVars.size() >= argTypes.size())
    {
      d_state.parseError("Too many arguments for pattern.");
    }
    // make of proper type
    Term arg =
        d_state.bindBoundVar(d_lex.tokenStr(), argTypes[boundVars.size()]);
    boundVars.push_back(arg);
  }
  std::vector<Term> cargs;
  cargs.push_back(f);
  cargs.insert(cargs.end(), boundVars.begin(), boundVars.end());
  // make the pattern term
  return d_state.getSolver()->mkTerm(APPLY_CONSTRUCTOR, cargs);
}

}  // namespace parser
}  // namespace cvc5
