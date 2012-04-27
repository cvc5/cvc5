/*********************                                                        */
/*! \file smt.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** Definitions of SMT constants.
 **/

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__SMT_H
#define __CVC4__PARSER__SMT_H

#include <ext/hash_map>
namespace std { using namespace __gnu_cxx; }

#include "util/hash.h"
#include "parser/parser.h"

namespace CVC4 {

class SExpr;

namespace parser {

class Smt : public Parser {
  friend class ParserBuilder;

public:
  enum Logic {
    AUFLIA, // +p and -p?
    AUFLIRA,
    AUFNIRA,
    LRA,
    QF_ABV,
    QF_AUFBV,
    QF_AUFLIA,
    QF_AUFLIRA,
    QF_AX,
    QF_BV,
    QF_IDL,
    QF_LIA,
    QF_LRA,
    QF_NIA,
    QF_NRA,
    QF_RDL,
    QF_SAT,
    QF_UF,
    QF_UFIDL,
    QF_UFBV,
    QF_UFLIA,
    QF_UFNIA, // nonstandard
    QF_UFLRA,
    QF_UFLIRA, // nonstandard
    QF_UFNIRA, // nonstandard
    QF_UFNRA,
    UFLRA,
    UFNIA
  };

  enum Theory {
    THEORY_ARRAYS,
    THEORY_ARRAYS_EX,
    THEORY_BITVECTORS,
    THEORY_BITVECTORS_32,
    THEORY_BITVECTORS_ARRAYS_EX,
    THEORY_EMPTY,
    THEORY_INTS,
    THEORY_INT_ARRAYS,
    THEORY_INT_ARRAYS_EX,
    THEORY_INT_INT_REAL_ARRAY_ARRAYS_EX,
    THEORY_REALS,
    THEORY_REALS_INTS,
  };

private:
  bool d_logicSet;
  Logic d_logic;

protected:
  Smt(ExprManager* exprManager, Input* input, bool strictMode = false, bool parseOnly = false);

public:
  /**
   * Add theory symbols to the parser state.
   *
   * @param theory the theory to open (e.g., Core, Ints)
   */
  void addTheory(Theory theory);

  bool logicIsSet();

  /**
   * Sets the logic for the current benchmark. Declares any logic and theory symbols.
   *
   * @param name the name of the logic (e.g., QF_UF, AUFLIA)
   */
  void setLogic(const std::string& name);

  static Logic toLogic(const std::string& name);

private:

  void addArithmeticOperators();
  void addUf();
  static std::hash_map<const std::string, Logic, CVC4::StringHashFunction> newLogicMap();
};/* class Smt */

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__SMT_INPUT_H */
