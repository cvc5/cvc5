/*********************                                                        */
/*! \file smt1.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Christopher L. Conway, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** Definitions of SMT-LIB (v1) constants.
 **/

#include <ext/hash_map>
namespace std {
  using namespace __gnu_cxx;
}

#include "expr/type.h"
#include "smt/command.h"
#include "parser/parser.h"
#include "parser/smt1/smt1.h"

namespace CVC4 {
namespace parser {

std::hash_map<const std::string, Smt1::Logic, CVC4::StringHashFunction> Smt1::newLogicMap() {
  std::hash_map<const std::string, Smt1::Logic, CVC4::StringHashFunction> logicMap;
  logicMap["AUFLIA"] = AUFLIA;
  logicMap["AUFLIRA"] = AUFLIRA;
  logicMap["AUFNIRA"] = AUFNIRA;
  logicMap["LRA"] = LRA;
  logicMap["QF_AX"] = QF_AX;
  logicMap["QF_BV"] = QF_BV;
  logicMap["QF_IDL"] = QF_IDL;
  logicMap["QF_LIA"] = QF_LIA;
  logicMap["QF_LRA"] = QF_LRA;
  logicMap["QF_NIA"] = QF_NIA;
  logicMap["QF_NRA"] = QF_NRA;
  logicMap["QF_RDL"] = QF_RDL;
  logicMap["QF_S"] = QF_S;
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
  logicMap["UFNIA"] = UFNIA;
  logicMap["UFNIRA"] = UFNIRA;
  logicMap["UFLRA"] = UFLRA;
  logicMap["QF_ALL_SUPPORTED"] = QF_ALL_SUPPORTED;
  logicMap["ALL_SUPPORTED"] = ALL_SUPPORTED;
  logicMap["QF_ALL"] = QF_ALL_SUPPORTED;
  logicMap["ALL"] = ALL_SUPPORTED;
  return logicMap;
}

Smt1::Logic Smt1::toLogic(const std::string& name) {
  static std::hash_map<const std::string, Smt1::Logic, CVC4::StringHashFunction> logicMap = newLogicMap();
  return logicMap[name];
}

Smt1::Smt1(ExprManager* exprManager, Input* input, bool strictMode, bool parseOnly) :
  Parser(exprManager,input,strictMode,parseOnly),
  d_logicSet(false) {

  // Boolean symbols are always defined
  addOperator(kind::AND);
  addOperator(kind::EQUAL);
  addOperator(kind::IMPLIES);
  addOperator(kind::ITE);
  addOperator(kind::NOT);
  addOperator(kind::OR);
  addOperator(kind::XOR);

}

void Smt1::addArithmeticOperators() {
  addOperator(kind::PLUS);
  addOperator(kind::MINUS);
  addOperator(kind::UMINUS);
  addOperator(kind::MULT);
  addOperator(kind::LT);
  addOperator(kind::LEQ);
  addOperator(kind::GT);
  addOperator(kind::GEQ);
}

void Smt1::addTheory(Theory theory) {
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

  case THEORY_BITVECTOR_ARRAYS_EX: {
    // We don't define the "Array" symbol in this case;
    // the parser creates the Array[m:n] types on the fly.
    addOperator(kind::SELECT);
    addOperator(kind::STORE);
    break;
  }

  case THEORY_INT_INT_REAL_ARRAY_ARRAYS_EX: {
    defineType("Array1", getExprManager()->mkArrayType(getSort("Int"), getSort("Real")));
    defineType("Array2", getExprManager()->mkArrayType(getSort("Int"), getSort("Array1")));
    addOperator(kind::SELECT);
    addOperator(kind::STORE);
    break;
  }

  case THEORY_INT_ARRAYS:
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

  case THEORY_QUANTIFIERS:
    break;

  default:
    std::stringstream ss;
    ss << "internal error: unsupported theory " << theory;
    throw ParserException(ss.str());
  }
}

bool Smt1::logicIsSet() {
  return d_logicSet;
}

void Smt1::setLogic(const std::string& name) {
  d_logicSet = true;
  if(logicIsForced()) {
    d_logic = toLogic(getForcedLogic());
  } else {
    d_logic = toLogic(name);
  }

  switch(d_logic) {
  case QF_S:
    throw ParserException("Strings theory unsupported in SMT-LIBv1 front-end; try SMT-LIBv2.");
    break;

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
    addOperator(kind::APPLY_UF);
    break;

  case QF_UFLRA:
  case QF_UFNRA:
    addTheory(THEORY_REALS);
    addOperator(kind::APPLY_UF);
    break;

  case QF_UFLIRA:// nonstandard logic
  case QF_UFNIRA:// nonstandard logic
    addTheory(THEORY_INTS);
    addTheory(THEORY_REALS);
    addOperator(kind::APPLY_UF);
    break;

  case QF_UF:
    addTheory(THEORY_EMPTY);
    addOperator(kind::APPLY_UF);
    break;

  case QF_BV:
    addTheory(THEORY_BITVECTORS);
    break;

  case QF_ABV:// nonstandard logic
    addTheory(THEORY_BITVECTOR_ARRAYS_EX);
    addTheory(THEORY_BITVECTORS);
    break;

  case QF_UFBV:
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_BITVECTORS);
    break;

  case QF_AUFBV:
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_BITVECTOR_ARRAYS_EX);
    addTheory(THEORY_BITVECTORS);
    break;

  case QF_AUFBVLIA:// nonstandard logic
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_ARRAYS_EX);
    addTheory(THEORY_BITVECTORS);
    addTheory(THEORY_INTS);
    break;

  case QF_AUFBVLRA:// nonstandard logic
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_ARRAYS_EX);
    addTheory(THEORY_BITVECTORS);
    addTheory(THEORY_REALS);
    break;

  case QF_AUFLIA:
    addTheory(THEORY_INT_ARRAYS_EX);// nonstandard logic
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_INTS);
    break;

  case QF_AUFLIRA:// nonstandard logic
    addTheory(THEORY_INT_INT_REAL_ARRAY_ARRAYS_EX);
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_INTS);
    addTheory(THEORY_REALS);
    break;

  case ALL_SUPPORTED:// nonstandard logic
    addTheory(THEORY_QUANTIFIERS);
    /* fall through */
  case QF_ALL_SUPPORTED:// nonstandard logic
    addTheory(THEORY_ARRAYS_EX);
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_INTS);
    addTheory(THEORY_REALS);
    addTheory(THEORY_BITVECTORS);
    break;

  case AUFLIA:
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_INTS);
    addTheory(THEORY_INT_ARRAYS_EX);
    addTheory(THEORY_QUANTIFIERS);
    break;

  case AUFLIRA:
  case AUFNIRA:
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_INTS);
    addTheory(THEORY_REALS);
    addTheory(THEORY_INT_INT_REAL_ARRAY_ARRAYS_EX);
    addTheory(THEORY_QUANTIFIERS);
    break;

  case LRA:
    addTheory(THEORY_REALS);
    addTheory(THEORY_QUANTIFIERS);
    break;

  case UFNIA:
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_INTS);
    addTheory(THEORY_QUANTIFIERS);
    break;
  case UFNIRA:
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_INTS);
    addTheory(THEORY_REALS);
    addTheory(THEORY_QUANTIFIERS);
    break;

  case UFLRA:
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_REALS);
    addTheory(THEORY_QUANTIFIERS);
    break;
  }
}/* Smt1::setLogic() */

}/* CVC4::parser namespace */
}/* CVC4 namespace */
