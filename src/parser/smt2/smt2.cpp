/*********************                                                        */
/** smt2.h
 ** Original author: cconway
 ** Major contributors:
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Definitions of SMT2 constants.
 **/

#include <ext/hash_map>
namespace std {
using namespace __gnu_cxx;
}

#include "parser/parser.h"
#include "parser/smt2/smt2.h"

namespace CVC4 {
namespace parser {

std::hash_map<const std::string, Smt2::Logic, CVC4::StringHashFunction> Smt2::newLogicMap() {
  std::hash_map<const std::string, Smt2::Logic, CVC4::StringHashFunction> logicMap;
  logicMap["QF_AX"] = QF_AX;
  logicMap["QF_BV"] = QF_BV;
  logicMap["QF_LIA"] = QF_LIA;
  logicMap["QF_LRA"] = QF_LRA;
  logicMap["QF_UF"] = QF_UF;
  return logicMap;
}

Smt2::Logic Smt2::toLogic(const std::string& name) {
  static std::hash_map<const std::string, Smt2::Logic, CVC4::StringHashFunction> logicMap = newLogicMap();
  return logicMap[name];
}

void Smt2::addArithmeticOperators(Parser& parser) {
  parser.addOperator(kind::PLUS);
  parser.addOperator(kind::MINUS);
  parser.addOperator(kind::UMINUS);
  parser.addOperator(kind::MULT);
  parser.addOperator(kind::LT);
  parser.addOperator(kind::LEQ);
  parser.addOperator(kind::GT);
  parser.addOperator(kind::GEQ);
}

/**
 * Add theory symbols to the parser state.
 *
 * @param parser the CVC4 Parser object
 * @param theory the theory to open (e.g., Core, Ints)
 */
void Smt2::addTheory(Parser& parser, Theory theory) {
  switch(theory) {
  case THEORY_CORE:
    parser.defineType("Bool", parser.getExprManager()->booleanType());
    parser.defineVar("true", parser.getExprManager()->mkConst(true));
    parser.defineVar("false", parser.getExprManager()->mkConst(false));
    parser.addOperator(kind::AND);
    parser.addOperator(kind::EQUAL);
    parser.addOperator(kind::IFF);
    parser.addOperator(kind::IMPLIES);
    parser.addOperator(kind::ITE);
    parser.addOperator(kind::NOT);
    parser.addOperator(kind::OR);
    parser.addOperator(kind::XOR);
    break;

  case THEORY_REALS_INTS:
    parser.defineType("Real", parser.getExprManager()->realType());
    // falling-through on purpose, to add Ints part of RealsInts

  case THEORY_INTS:
    parser.defineType("Int", parser.getExprManager()->integerType());
    addArithmeticOperators(parser);
    break;

  case THEORY_REALS:
    parser.defineType("Real", parser.getExprManager()->realType());
    addArithmeticOperators(parser);
    break;

  default:
    Unhandled(theory);
  }
}

/**
 * Sets the logic for the current benchmark. Declares any logic and theory symbols.
 *
 * @param parser the CVC4 Parser object
 * @param name the name of the logic (e.g., QF_UF, AUFLIA)
 */
void Smt2::setLogic(Parser& parser, const std::string& name) {
  // Core theory belongs to every logic
  addTheory(parser, THEORY_CORE);

  switch(toLogic(name)) {
  case QF_UF:
    parser.addOperator(kind::APPLY_UF);
    break;

  case QF_LRA:
    addTheory(parser, THEORY_REALS);
    break;

  default:
    Unhandled(name);
  }
}

void Smt2::setInfo(Parser& parser, const std::string& flag, const SExpr& sexpr) {
  // TODO: ???
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
