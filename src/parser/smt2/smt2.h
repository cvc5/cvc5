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

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__SMT2_H
#define __CVC4__PARSER__SMT2_H

#include <ext/hash_map>
namespace std { using namespace __gnu_cxx; }

#include "util/hash.h"

namespace CVC4 {

class SExpr;

namespace parser {

class Parser;

class Smt2 {

public:
  enum Logic {
    QF_AX,
    QF_BV,
    QF_LIA,
    QF_LRA,
    QF_UF,
  };

  enum Theory {
    THEORY_ARRAYS,
    THEORY_BITVECTORS,
    THEORY_CORE,
    THEORY_INTS,
    THEORY_REALS,
    THEORY_REALS_INTS,
  };

  /**
   * Add theory symbols to the parser state.
   *
   * @param parser the CVC4 Parser object
   * @param theory the theory to open (e.g., Core, Ints)
   */
  static void
  addTheory(Parser& parser, Theory theory);

  /**
   * Sets the logic for the current benchmark. Declares any logic and theory symbols.
   *
   * @param parser the CVC4 Parser object
   * @param name the name of the logic (e.g., QF_UF, AUFLIA)
   */
  static void
  setLogic(Parser& parser, const std::string& name);

  static void
  setInfo(Parser& parser, const std::string& flag, const SExpr& sexpr);

  static Logic toLogic(const std::string& name);

private:

  static void addArithmeticOperators(Parser& parser);
  static std::hash_map<const std::string, Logic, CVC4::StringHashFunction> newLogicMap();
};
}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__SMT2_INPUT_H */
