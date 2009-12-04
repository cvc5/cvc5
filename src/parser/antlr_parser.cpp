/*
 * antlr_parser.cpp
 *
 *  Created on: Nov 30, 2009
 *      Author: dejan
 */

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
    CVC4::UnhandledImpl("Unhandled ostream case for AntlrParser::BenchmarkStatus");
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
  cout << "getVariable(" << var_name << ")" << endl;
  return d_expr_manager->mkExpr(VARIABLE);
}

Expr AntlrParser::getTrueExpr() const {
  return d_expr_manager->mkExpr(TRUE);
}

Expr AntlrParser::getFalseExpr() const {
  return d_expr_manager->mkExpr(FALSE);
}

Expr AntlrParser::newExpression(Kind kind, const std::vector<Expr>& children) {
  cout << "newExpression(" << kind << ", " << children.size()
      << ")" << endl;
  return d_expr_manager->mkExpr(kind, children);
}

void AntlrParser::newPredicate(std::string p_name,
    std::vector<std::string>& p_sorts) {
  cout << "newPredicate(" << p_name << ", " << p_sorts.size() << ")" << endl;
}

void AntlrParser::setBenchmarkStatus(BenchmarkStatus status) {
  cout << "setBenchmarkStatus()" << endl;
  d_benchmark_status = status;
}

void AntlrParser::addExtraSorts(std::vector<std::string>& extra_sorts) {
  cout << "addExtraSorts()" << endl;
}
