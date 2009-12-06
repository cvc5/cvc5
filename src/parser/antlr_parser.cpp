/*
 * antlr_parser.cpp
 *
 *  Created on: Nov 30, 2009
 *      Author: dejan
 */

#include <iostream>

#include "antlr_parser.h"
#include "expr/expr_manager.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;

ostream& operator <<(ostream& out, AntlrParser::BenchmarkStatus status) {
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
    CVC4::UnhandledImpl(
        "Unhandled ostream case for AntlrParser::BenchmarkStatus");
  }
  return out;
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
  return d_var_symbol_table.getObject(var_name);
}

Expr AntlrParser::getTrueExpr() const {
  return d_expr_manager->mkExpr(TRUE);
}

Expr AntlrParser::getFalseExpr() const {
  return d_expr_manager->mkExpr(FALSE);
}

Expr AntlrParser::newExpression(Kind kind, const std::vector<Expr>& children) {
  return d_expr_manager->mkExpr(kind, children);
}

void AntlrParser::newPredicate(std::string p_name,
    std::vector<std::string>& p_sorts) {
  if(p_sorts.size() == 0)
    d_var_symbol_table.bindName(p_name, d_expr_manager->mkExpr(VARIABLE));
  else
    Unhandled("Non unary predicate not supported yet!");
}

void AntlrParser::setBenchmarkStatus(BenchmarkStatus status) {
  d_benchmark_status = status;
}

void AntlrParser::addExtraSorts(std::vector<std::string>& extra_sorts) {
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

void AntlrParser::rethrow(antlr::SemanticException& e, string new_message) throw(antlr::SemanticException) {
  throw antlr::SemanticException(new_message, getFilename(), LT(0).get()->getLine(), LT(0).get()->getColumn());
}
