/*********************                                                        */
/*! \file smt2.cpp
 ** \verbatim
 ** Original author: Christopher L. Conway
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Definitions of SMT2 constants.
 **
 ** Definitions of SMT2 constants.
 **/

#include "expr/type.h"
#include "expr/command.h"
#include "parser/parser.h"
#include "parser/smt1/smt1.h"
#include "parser/smt2/smt2.h"

namespace CVC4 {
namespace parser {

Smt2::Smt2(ExprManager* exprManager, Input* input, bool strictMode, bool parseOnly) :
  Parser(exprManager,input,strictMode,parseOnly),
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

void Smt2::addBitvectorOperators() {
  addOperator(kind::BITVECTOR_CONCAT);
  addOperator(kind::BITVECTOR_AND);
  addOperator(kind::BITVECTOR_OR);
  addOperator(kind::BITVECTOR_XOR);
  addOperator(kind::BITVECTOR_NOT);
  addOperator(kind::BITVECTOR_NAND);
  addOperator(kind::BITVECTOR_NOR);
  addOperator(kind::BITVECTOR_XNOR);
  addOperator(kind::BITVECTOR_COMP);
  addOperator(kind::BITVECTOR_MULT);
  addOperator(kind::BITVECTOR_PLUS);
  addOperator(kind::BITVECTOR_SUB);
  addOperator(kind::BITVECTOR_NEG);
  addOperator(kind::BITVECTOR_UDIV);
  addOperator(kind::BITVECTOR_UREM);
  addOperator(kind::BITVECTOR_SDIV);
  addOperator(kind::BITVECTOR_SREM);
  addOperator(kind::BITVECTOR_SMOD);
  addOperator(kind::BITVECTOR_SHL);
  addOperator(kind::BITVECTOR_LSHR);
  addOperator(kind::BITVECTOR_ASHR);
  addOperator(kind::BITVECTOR_ULT);
  addOperator(kind::BITVECTOR_ULE);
  addOperator(kind::BITVECTOR_UGT);
  addOperator(kind::BITVECTOR_UGE);
  addOperator(kind::BITVECTOR_SLT);
  addOperator(kind::BITVECTOR_SLE);
  addOperator(kind::BITVECTOR_SGT);
  addOperator(kind::BITVECTOR_SGE);
  addOperator(kind::BITVECTOR_BITOF);
  addOperator(kind::BITVECTOR_EXTRACT);
  addOperator(kind::BITVECTOR_REPEAT);
  addOperator(kind::BITVECTOR_ZERO_EXTEND);
  addOperator(kind::BITVECTOR_SIGN_EXTEND);
  addOperator(kind::BITVECTOR_ROTATE_LEFT);
  addOperator(kind::BITVECTOR_ROTATE_RIGHT);
}

void Smt2::addTheory(Theory theory) {
  switch(theory) {
  case THEORY_CORE:
    defineType("Bool", getExprManager()->booleanType());
    defineVar("true", getExprManager()->mkConst(true));
    defineVar("false", getExprManager()->mkConst(false));
    addOperator(kind::AND);
    addOperator(kind::DISTINCT);
    addOperator(kind::EQUAL);
    addOperator(kind::IFF);
    addOperator(kind::IMPLIES);
    addOperator(kind::ITE);
    addOperator(kind::NOT);
    addOperator(kind::OR);
    addOperator(kind::XOR);
    break;

  case THEORY_ARRAYS:
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
    addBitvectorOperators();
    break;

  case THEORY_QUANTIFIERS:
    break;

  default:
    std::stringstream ss;
    ss << "internal error: unsupported theory " << theory;
    throw ParserException(ss.str());
  }
}

bool Smt2::logicIsSet() {
  return d_logicSet;
}

void Smt2::setLogic(const std::string& name) {
  d_logicSet = true;
  d_logic = Smt1::toLogic(name);

  // Core theory belongs to every logic
  addTheory(THEORY_CORE);

  switch(d_logic) {
  case Smt1::QF_SAT:
    /* No extra symbols necessary */
    break;

  case Smt1::QF_AX:
    addTheory(THEORY_ARRAYS);
    break;

  case Smt1::QF_IDL:
  case Smt1::QF_LIA:
  case Smt1::QF_NIA:
    addTheory(THEORY_INTS);
    break;

  case Smt1::QF_RDL:
  case Smt1::QF_LRA:
  case Smt1::QF_NRA:
    addTheory(THEORY_REALS);
    break;

  case Smt1::QF_UF:
    addOperator(kind::APPLY_UF);
    break;

  case Smt1::QF_UFIDL:
  case Smt1::QF_UFLIA:
  case Smt1::QF_UFNIA:// nonstandard logic
    addTheory(THEORY_INTS);
    addOperator(kind::APPLY_UF);
    break;

  case Smt1::QF_UFLRA:
  case Smt1::QF_UFNRA:
    addTheory(THEORY_REALS);
    addOperator(kind::APPLY_UF);
    break;

  case Smt1::QF_UFLIRA:// nonstandard logic
  case Smt1::QF_UFNIRA:// nonstandard logic
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_INTS);
    addTheory(THEORY_REALS);
    break;

  case Smt1::QF_BV:
    addTheory(THEORY_BITVECTORS);
    break;

  case Smt1::QF_ABV:
    addTheory(THEORY_ARRAYS);
    addTheory(THEORY_BITVECTORS);
    break;

  case Smt1::QF_UFBV:
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_BITVECTORS);
    break;

  case Smt1::QF_AUFBV:
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_ARRAYS);
    addTheory(THEORY_BITVECTORS);
    break;

  case Smt1::QF_AUFBVLIA:
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_ARRAYS);
    addTheory(THEORY_BITVECTORS);
    addTheory(THEORY_INTS);
    break;

  case Smt1::QF_AUFBVLRA:
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_ARRAYS);
    addTheory(THEORY_BITVECTORS);
    addTheory(THEORY_REALS);
    break;

  case Smt1::QF_AUFLIA:
    addTheory(THEORY_ARRAYS);
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_INTS);
    break;

  case Smt1::QF_AUFLIRA:
    addTheory(THEORY_ARRAYS);
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_INTS);
    addTheory(THEORY_REALS);
    break;

  case Smt1::ALL_SUPPORTED:
    addTheory(THEORY_QUANTIFIERS);
    /* fall through */
  case Smt1::QF_ALL_SUPPORTED:
    addTheory(THEORY_ARRAYS);
    addOperator(kind::APPLY_UF);
    addTheory(THEORY_INTS);
    addTheory(THEORY_REALS);
    addTheory(THEORY_BITVECTORS);
    break;

  case Smt1::AUFLIA:
  case Smt1::AUFLIRA:
  case Smt1::AUFNIRA:
  case Smt1::LRA:
  case Smt1::UFNIA:
  case Smt1::UFNIRA:
  case Smt1::UFLRA:
    if(d_logic != Smt1::AUFLIA && d_logic != Smt1::UFNIA) {
      addTheory(THEORY_REALS);
    }
    if(d_logic != Smt1::LRA) {
      addOperator(kind::APPLY_UF);
      if(d_logic != Smt1::UFLRA) {
        addTheory(THEORY_INTS);
        if(d_logic != Smt1::UFNIA && d_logic != Smt1::UFNIRA) {
          addTheory(THEORY_ARRAYS);
        }
      }
    }
    addTheory(THEORY_QUANTIFIERS);
    break;
  }
}/* Smt2::setLogic() */

void Smt2::setInfo(const std::string& flag, const SExpr& sexpr) {
  // TODO: ???
}

void Smt2::setOption(const std::string& flag, const SExpr& sexpr) {
  // TODO: ???
}

void Smt2::checkThatLogicIsSet() {
  if( ! logicIsSet() ) {
    if( strictModeEnabled() ) {
      parseError("set-logic must appear before this point.");
    } else {
      warning("No set-logic command was given before this point.");
      warning("CVC4 will assume the non-standard ALL_SUPPORTED logic.");
      warning("Consider setting a stricter logic for (likely) better performance.");
      warning("To suppress this warning in the future use (set-logic ALL_SUPPORTED).");

      setLogic("ALL_SUPPORTED");

      Command* c = new SetBenchmarkLogicCommand("ALL_SUPPORTED");
      c->setMuted(true);
      preemptCommand(c);
    }
  }
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
