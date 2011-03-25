/*********************                                                        */
/*! \file smt2.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Definitions of SMT2 constants.
 **
 ** Definitions of SMT2 constants.
 **/

#include "expr/type.h"
#include "parser/parser.h"
#include "parser/smt/smt.h"
#include "parser/smt2/smt2.h"

namespace CVC4 {
namespace parser {

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
  addOperator(kind::DIVISION);
  addOperator(kind::LT);
  addOperator(kind::LEQ);
  addOperator(kind::GT);
  addOperator(kind::GEQ);
}

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

  case THEORY_ARRAYS:
    // FIXME: should define a paramterized type 'Array' with 2 arguments
    mkSort("Array");

    addOperator(kind::SELECT);
    addOperator(kind::STORE);
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

  case THEORY_BITVECTORS:
    break;

  default:
    Unhandled(theory);
  }
}

bool Smt2::logicIsSet() {
  return d_logicSet;
}

void Smt2::setLogic(const std::string& name) {
  d_logicSet = true;
  d_logic = Smt::toLogic(name);

  // Core theory belongs to every logic
  addTheory(THEORY_CORE);

  switch(d_logic) {
  case Smt::QF_SAT:
    /* No extra symbols necessary */
    break;

  case Smt::QF_AX:
    addTheory(THEORY_ARRAYS);
    break;

  case Smt::QF_IDL:
  case Smt::QF_LIA:
  case Smt::QF_NIA:
    addTheory(THEORY_INTS);
    break;

  case Smt::QF_LRA:
  case Smt::QF_RDL:
    addTheory(THEORY_REALS);
    break;

  case Smt::QF_UF:
    addOperator(kind::APPLY_UF);
    break;

  case Smt::QF_UFIDL:
    addTheory(THEORY_INTS);
    addOperator(kind::APPLY_UF);
    break;

  case Smt::QF_UFLIA:
  case Smt::QF_UFLRA:
  case Smt::QF_UFNRA:
    addTheory(THEORY_REALS);
    addOperator(kind::APPLY_UF);
    break;

  case Smt::QF_BV:
    addTheory(THEORY_BITVECTORS);
    break;

  case Smt::AUFLIA:
  case Smt::AUFLIRA:
  case Smt::AUFNIRA:
  case Smt::LRA:
  case Smt::UFNIA:
  case Smt::QF_AUFBV:
  case Smt::QF_AUFLIA:
    Unhandled(name);
  }
}

void Smt2::setInfo(const std::string& flag, const SExpr& sexpr) {
  // TODO: ???
}

void Smt2::setOption(const std::string& flag, const SExpr& sexpr) {
  // TODO: ???
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
