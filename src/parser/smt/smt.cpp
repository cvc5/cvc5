/*********************                                                        */
/*! \file smt.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** Definitions of SMT constants.
 **/

#include <ext/hash_map>
namespace std {
  using namespace __gnu_cxx;
}

#include "expr/type.h"
#include "expr/command.h"
#include "parser/parser.h"
#include "parser/smt/smt.h"

namespace CVC4 {
namespace parser {

std::hash_map<const std::string, Smt::Logic, CVC4::StringHashFunction> Smt::newLogicMap() {
  std::hash_map<const std::string, Smt::Logic, CVC4::StringHashFunction> logicMap;
  logicMap["QF_AX"] = QF_AX;
  logicMap["QF_BV"] = QF_BV;
  logicMap["QF_IDL"] = QF_IDL;
  logicMap["QF_LIA"] = QF_LIA;
  logicMap["QF_LRA"] = QF_LRA;
  logicMap["QF_NIA"] = QF_NIA;
  logicMap["QF_NRA"] = QF_NRA;
  logicMap["QF_RDL"] = QF_RDL;
  logicMap["QF_SAT"] = QF_SAT;
  logicMap["QF_UF"] = QF_UF;
  logicMap["QF_UFIDL"] = QF_UFIDL;
  logicMap["QF_UFBV"] = QF_UFBV;
  logicMap["QF_UFLRA"] = QF_UFLRA;
  logicMap["QF_UFLIA"] = QF_UFLIA;
  logicMap["QF_UFLIRA"] = QF_UFLIRA;
  logicMap["QF_UFNIA"] = QF_UFNIA;
  logicMap["QF_UFNIRA"] = QF_UFNIRA;
  logicMap["QF_UFNRA"] = QF_UFNRA;
  logicMap["QF_ABV"] = QF_ABV;
  logicMap["QF_AUFBV"] = QF_AUFBV;
  logicMap["QF_AUFBVLIA"] = QF_AUFBVLIA;
  logicMap["QF_AUFBVLRA"] = QF_AUFBVLRA;
  logicMap["QF_UFNIRA"] = QF_UFNIRA;
  logicMap["QF_AUFLIA"] = QF_AUFLIA;
  logicMap["QF_AUFLIRA"] = QF_AUFLIRA;
  logicMap["QF_ALL_SUPPORTED"] = QF_ALL_SUPPORTED;
  logicMap["ALL_SUPPORTED"] = ALL_SUPPORTED;
  return logicMap;
}

Smt::Logic Smt::toLogic(const std::string& name) {
  static std::hash_map<const std::string, Smt::Logic, CVC4::StringHashFunction> logicMap = newLogicMap();
  return logicMap[name];
}

Smt::Smt(ExprManager* exprManager, Input* input, bool strictMode, bool parseOnly) :
  Parser(exprManager,input,strictMode,parseOnly),
  d_logicSet(false) {

  // Boolean symbols are always defined
  addOperator(kind::AND);
  addOperator(kind::EQUAL);
  addOperator(kind::IFF);
  addOperator(kind::IMPLIES);
  addOperator(kind::ITE);
  addOperator(kind::NOT);
  addOperator(kind::OR);
  addOperator(kind::XOR);

}

void Smt::addArithmeticOperators() {
  addOperator(kind::PLUS);
  addOperator(kind::MINUS);
  addOperator(kind::UMINUS);
  addOperator(kind::MULT);
  addOperator(kind::LT);
  addOperator(kind::LEQ);
  addOperator(kind::GT);
  addOperator(kind::GEQ);
}

void Smt::addTheory(Theory theory) {
  switch(theory) {
  case THEORY_ARRAYS:
  case THEORY_ARRAYS_EX: {
    Type indexType = mkSort("Index");
    Type elementType = mkSort("Element");
    DeclarationSequence* seq = new DeclarationSequence();
    seq->addCommand(new DeclareTypeCommand("Index", 0, indexType));
    seq->addCommand(new DeclareTypeCommand("Element", 0, elementType));
    preemptCommand(seq);

    defineType("Array", getExprManager()->mkArrayType(indexType, elementType));

    addOperator(kind::SELECT);
    addOperator(kind::STORE);
    break;
  }

  case THEORY_INT_ARRAYS_EX: {
    defineType("Array", getExprManager()->mkArrayType(getExprManager()->integerType(), getExprManager()->integerType()));

    addOperator(kind::SELECT);
    addOperator(kind::STORE);
    break;
  }

  case THEORY_EMPTY: {
    Type sort = mkSort("U");
    preemptCommand(new DeclareTypeCommand("U", 0, sort));
    break;
  }

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

bool Smt::logicIsSet() {
  return d_logicSet;
}

inline void Smt::addUf() {
  addTheory(Smt::THEORY_EMPTY);
  addOperator(kind::APPLY_UF);
}

void Smt::setLogic(const std::string& name) {
  d_logicSet = true;
  d_logic = toLogic(name);

  switch(d_logic) {
  case QF_AX:
    addTheory(THEORY_ARRAYS_EX);
    break;

  case QF_IDL:
  case QF_LIA:
  case QF_NIA:
    addTheory(THEORY_INTS);
    break;

  case QF_RDL:
  case QF_LRA:
  case QF_NRA:
    addTheory(THEORY_REALS);
    break;

  case QF_SAT:
    /* no extra symbols needed */
    break;

  case QF_UFIDL:
  case QF_UFLIA:
  case QF_UFNIA:// nonstandard logic
    addTheory(THEORY_INTS);
    addUf();
    break;

  case QF_UFLRA:
  case QF_UFNRA:
    addTheory(THEORY_REALS);
    addUf();
    break;

  case QF_UFLIRA:// nonstandard logic
  case QF_UFNIRA:// nonstandard logic
    addTheory(THEORY_INTS);
    addTheory(THEORY_REALS);
    addUf();
    break;

  case QF_UF:
    addUf();
    break;

  case QF_BV:
    addTheory(THEORY_BITVECTORS);
    break;

  case QF_ABV:
    addTheory(THEORY_ARRAYS_EX);
    addTheory(THEORY_BITVECTORS);
    break;

  case QF_UFBV:
    addUf();
    addTheory(THEORY_BITVECTORS);
    break;

  case QF_AUFBV:
    addUf();
    addTheory(THEORY_ARRAYS_EX);
    addTheory(THEORY_BITVECTORS);
    break;

  case QF_AUFBVLIA:
    addUf();
    addTheory(THEORY_ARRAYS_EX);
    addTheory(THEORY_BITVECTORS);
    addTheory(THEORY_INTS);
    break;

  case QF_AUFBVLRA:
    addUf();
    addTheory(THEORY_ARRAYS_EX);
    addTheory(THEORY_BITVECTORS);
    addTheory(THEORY_REALS);
    break;

  case QF_AUFLIA:
    addTheory(THEORY_INT_ARRAYS_EX);
    addUf();
    addTheory(THEORY_INTS);
    break;

  case QF_AUFLIRA:
    addTheory(THEORY_ARRAYS_EX);
    addUf();
    addTheory(THEORY_INTS);
    addTheory(THEORY_REALS);
    break;

  case ALL_SUPPORTED:
    /* fall through */
  case QF_ALL_SUPPORTED:
    addTheory(THEORY_ARRAYS_EX);
    addUf();
    addTheory(THEORY_INTS);
    addTheory(THEORY_REALS);
    addTheory(THEORY_BITVECTORS);
    break;

  case AUFLIA:
  case AUFLIRA:
  case AUFNIRA:
  case LRA:
  case UFLRA:
  case UFNIA:
    Unhandled(name);
  }
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
