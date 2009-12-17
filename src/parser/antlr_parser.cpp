/*********************                                           -*- C++ -*-  */
/** antlr_parser.cpp
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): cconway, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** [[ Add file-specific comments here ]]
 **/

/*
 * antlr_parser.cpp
 *
 *  Created on: Nov 30, 2009
 *      Author: dejan
 */

#include <iostream>

#include "antlr_parser.h"
#include "util/output.h"
#include "util/Assert.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;

namespace CVC4 {
namespace parser {

ostream& operator<<(ostream& out, AntlrParser::BenchmarkStatus status) {
  switch(status) {
  case AntlrParser::SMT_SATISFIABLE:
    out << "sat";
    break;
  case AntlrParser::SMT_UNSATISFIABLE:
    out << "unsat";
    break;
  case AntlrParser::SMT_UNKNOWN:
    out << "unknown";
    break;
  default:
    Unhandled("Unhandled ostream case for AntlrParser::BenchmarkStatus");
  }
  return out;
}

unsigned AntlrParser::getPrecedence(Kind kind) {
  switch(kind) {
  // Boolean operators
  case OR:
    return 5;
  case AND:
    return 4;
  case IFF:
    return 3;
  case IMPLIES:
    return 2;
  case XOR:
    return 1;
  default:
    Unhandled ("Undefined precedence - necessary for proper parsing of CVC files!");
  }
  return 0;
}

AntlrParser::AntlrParser(const antlr::ParserSharedInputState& state, int k) :
  antlr::LLkParser(state, k) {
}

AntlrParser::AntlrParser(antlr::TokenBuffer& tokenBuf, int k) :
  antlr::LLkParser(tokenBuf, k) {
}

AntlrParser::AntlrParser(antlr::TokenStream& lexer, int k) :
  antlr::LLkParser(lexer, k) {
}

Expr AntlrParser::getVariable(std::string var_name) {
  Expr e = d_var_symbol_table.getObject(var_name);
  Debug("parser") << "getvar " << var_name << " gives " << e << endl;
  return e;
}

Expr AntlrParser::getTrueExpr() const {
  return d_expr_manager->mkExpr(TRUE);
}

Expr AntlrParser::getFalseExpr() const {
  return d_expr_manager->mkExpr(FALSE);
}

Expr AntlrParser::newExpression(Kind kind, const Expr& child) {
  return d_expr_manager->mkExpr(kind, child);
}

Expr AntlrParser::newExpression(Kind kind, const Expr& child_1, const Expr& child_2) {
  return d_expr_manager->mkExpr(kind, child_1, child_2);
}

Expr AntlrParser::newExpression(Kind kind, const std::vector<Expr>& children) {
  return d_expr_manager->mkExpr(kind, children);
}

void AntlrParser::newPredicate(std::string p_name, const std::vector<
    std::string>& p_sorts) {
  if(p_sorts.size() == 0)
    d_var_symbol_table.bindName(p_name, d_expr_manager->mkVar());
  else
    Unhandled("Non unary predicate not supported yet!");
}

void AntlrParser::newPredicates(const std::vector<std::string>& p_names) {
  vector<string> sorts;
  for(unsigned i = 0; i < p_names.size(); ++i)
    newPredicate(p_names[i], sorts);
}

void AntlrParser::setBenchmarkStatus(BenchmarkStatus status) {
  d_benchmark_status = status;
}

void AntlrParser::addExtraSorts(const std::vector<std::string>& extra_sorts) {
}

void AntlrParser::setExpressionManager(ExprManager* em) {
  d_expr_manager = em;
}

bool AntlrParser::isDeclared(string name, SymbolType type) {
  switch(type) {
  case SYM_VARIABLE:
    return d_var_symbol_table.isBound(name);
  default:
    Unhandled("Unhandled symbol type!");
  }
}

void AntlrParser::rethrow(antlr::SemanticException& e, string new_message)
    throw (antlr::SemanticException) {
  throw antlr::SemanticException(new_message, getFilename(),
                                 LT(0).get()->getLine(),
                                 LT(0).get()->getColumn());
}

Expr AntlrParser::createPrecedenceExpr(const vector<Expr>& exprs,
                                       const vector<Kind>& kinds) {
  Assert( exprs.size() > 0, "Expected non-empty vector expr");
  Assert( kinds.size() + 1 == exprs.size(), "Expected kinds to match exprs");
  return createPrecedenceExpr(exprs, kinds, 0, exprs.size() - 1);
}

unsigned AntlrParser::findPivot(const std::vector<Kind>& kinds,
                                unsigned start_index, unsigned end_index) const {
  Assert( start_index >= 0, "Expected start_index >= 0. ");
  Assert( end_index < kinds.size(), "Expected end_index < kinds.size(). ");
  Assert( start_index <= end_index, "Expected start_index <= end_index. ");

  int pivot = start_index;
  unsigned pivot_precedence = getPrecedence(kinds[pivot]);

  for(unsigned i = start_index + 1; i <= end_index; ++i) {
    unsigned current_precedence = getPrecedence(kinds[i]);
    if(current_precedence > pivot_precedence) {
      pivot = i;
      pivot_precedence = current_precedence;
    }
  }

  return pivot;
}

Expr AntlrParser::createPrecedenceExpr(const std::vector<Expr>& exprs,
                                       const std::vector<Kind>& kinds,
                                       unsigned start_index, unsigned end_index) {
  Assert( exprs.size() > 0, "Expected non-empty vector expr");
  Assert( kinds.size() + 1 == exprs.size(), "Expected kinds to match exprs.");
  Assert( start_index >= 0, "Expected start_index >= 0. ");
  Assert( end_index < exprs.size(), "Expected end_index < exprs.size. ");
  Assert( start_index <= end_index, "Expected start_index <= end_index. ");

  if(start_index == end_index)
    return exprs[start_index];

  unsigned pivot = findPivot(kinds, start_index, end_index - 1);

  Expr child_1 = createPrecedenceExpr(exprs, kinds, start_index, pivot);
  Expr child_2 = createPrecedenceExpr(exprs, kinds, pivot + 1, end_index);
  return d_expr_manager->mkExpr(kinds[pivot], child_1, child_2);
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
