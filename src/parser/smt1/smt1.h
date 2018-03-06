/*********************                                                        */
/*! \file smt1.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway, Morgan Deters, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** Definitions of SMT constants.
 **/

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__SMT1_H
#define __CVC4__PARSER__SMT1_H

#include <string>
#include <unordered_map>

#include "parser/parser.h"

namespace CVC4 {

class SExpr;

namespace parser {

class Smt1 : public Parser {
  friend class ParserBuilder;

public:
 enum Logic {
   UNSET = 0,  // This indicates that the logic has not been set.
   AUFLIA,     // +p and -p?
   AUFLIRA,
   AUFNIRA,
   LRA,
   QF_ABV,
   QF_AUFBV,
   QF_AUFBVLIA,
   QF_AUFBVLRA,
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
   QF_S,  // nonstandard (for string theory)
   QF_SAT,
   QF_UF,
   QF_UFIDL,
   QF_UFBV,
   QF_UFLIA,
   QF_UFNIA,  // nonstandard
   QF_UFLRA,
   QF_UFLIRA,  // nonstandard
   QF_UFNIRA,  // nonstandard
   QF_UFNRA,
   SAT,
   UFLRA,
   UFNIRA,  // nonstandard
   UFNIA,
   QF_ALL_SUPPORTED,  // nonstandard
   ALL_SUPPORTED      // nonstandard
 };

 enum Theory {
   THEORY_ARRAYS,
   THEORY_ARRAYS_EX,
   THEORY_BITVECTORS,
   THEORY_BITVECTORS_32,
   THEORY_BITVECTOR_ARRAYS_EX,
   THEORY_EMPTY,
   THEORY_INTS,
   THEORY_INT_ARRAYS,
   THEORY_INT_ARRAYS_EX,
   THEORY_INT_INT_REAL_ARRAY_ARRAYS_EX,
   THEORY_REALS,
   THEORY_REALS_INTS,
   THEORY_STRINGS,
   THEORY_QUANTIFIERS,
   THEORY_CARDINALITY_CONSTRAINT
 };

private:
  Logic d_logic;

protected:
  Smt1(ExprManager* exprManager, Input* input, bool strictMode = false, bool parseOnly = false);

public:
  /**
   * Add theory symbols to the parser state.
   *
   * @param theory the theory to open (e.g., Core, Ints)
   */
  void addTheory(Theory theory);

  bool logicIsSet() override;

  /**
   * Sets the logic for the current benchmark. Declares any logic and theory symbols.
   *
   * @param name the name of the logic (e.g., QF_UF, AUFLIA)
   */
  void setLogic(const std::string& name);

  static Logic toLogic(const std::string& name);

private:

  void addArithmeticOperators();
  static std::unordered_map<std::string, Logic> newLogicMap();
};/* class Smt1 */

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__SMT1_H */
