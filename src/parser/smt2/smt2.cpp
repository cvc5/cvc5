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
  logicMap["QF_IDL"] = QF_IDL;
  logicMap["QF_LIA"] = QF_LIA;
  logicMap["QF_LRA"] = QF_LRA;
  logicMap["QF_NIA"] = QF_NIA;
  logicMap["QF_RDL"] = QF_RDL;
  logicMap["QF_UF"] = QF_UF;
  logicMap["QF_UFIDL"] = QF_UFIDL;
  return logicMap;
}

Smt2::Logic Smt2::toLogic(const std::string& name) {
  static std::hash_map<const std::string, Smt2::Logic, CVC4::StringHashFunction> logicMap = newLogicMap();
  return logicMap[name];
}

Smt2::Smt2(ExprManager* exprManager, Input* input, bool strictMode) :
  Parser(exprManager,input,strictMode),
  d_logicSet(false) {
  if( !strictModeEnabled() ) {
    addTheory(Smt2::THEORY_CORE);
  }
}

void Smt2::addArithmeticOperators() {
  addOperator(kind::PLUS);
  addOperator(kind::MINUS);
  addOperator(kind::UMINUS);
  addOperator(kind::MULT);
  addOperator(kind::LT);
  addOperator(kind::LEQ);
  addOperator(kind::GT);
  addOperator(kind::GEQ);
}

/**
 * Add theory symbols to the parser state.
 *
 * @param parser the CVC4 Parser object
 * @param theory the theory to open (e.g., Core, Ints)
 */
void Smt2::addTheory(Theory theory) {
  switch(theory) {
  case THEORY_CORE:
    defineType("Bool", getExprManager()->booleanType());
    defineVar("true", getExprManager()->mkConst(true));
    defineVar("false", getExprManager()->mkConst(false));
    addOperator(kind::AND);
    addOperator(kind::EQUAL);
    addOperator(kind::IFF);
    addOperator(kind::IMPLIES);
    addOperator(kind::ITE);
    addOperator(kind::NOT);
    addOperator(kind::OR);
    addOperator(kind::XOR);
    break;

  case THEORY_REALS_INTS:
    defineType("Real", getExprManager()->realType());
    // falling-through on purpose, to add Ints part of RealsInts

  case THEORY_INTS:
    defineType("Int", getExprManager()->integerType());
    addArithmeticOperators();
    break;

  case THEORY_REALS:
    defineType("Real", getExprManager()->realType());
    addArithmeticOperators();
    break;

  default:
    Unhandled(theory);
  }
}

bool Smt2::logicIsSet() {
  return d_logicSet;
}

/**
 * Sets the logic for the current benchmark. Declares any logic and theory symbols.
 *
 * @param parser the CVC4 Parser object
 * @param name the name of the logic (e.g., QF_UF, AUFLIA)
 */
void Smt2::setLogic(const std::string& name) {
  d_logicSet = true;
  d_logic = toLogic(name);

  // Core theory belongs to every logic
  addTheory(THEORY_CORE);

  switch(d_logic) {
  case QF_IDL:
  case QF_LIA:
  case QF_NIA:
    addTheory(THEORY_INTS);
    break;
    
  case QF_LRA:
  case QF_RDL:
    addTheory(THEORY_REALS);
    break;

  case QF_UFIDL:
    addTheory(THEORY_INTS);
    // falling-through on purpose, to add UF part of UFIDL

  case QF_UF:
    addOperator(kind::APPLY_UF);
    break;

  case AUFLIA:
  case AUFLIRA:
  case AUFNIRA:
  case QF_AUFBV:
  case QF_AUFLIA:
    Unhandled(name);
  }
}

void Smt2::setInfo(const std::string& flag, const SExpr& sexpr) {
  // TODO: ???
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
