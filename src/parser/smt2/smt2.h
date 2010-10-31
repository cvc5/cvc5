/*********************                                                        */
/*! \file smt2.h
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

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__SMT2_H
#define __CVC4__PARSER__SMT2_H

#include "parser/parser.h"
#include "parser/smt/smt.h"

namespace CVC4 {

class SExpr;

namespace parser {

class Smt2 : public Parser {
  friend class ParserBuilder;

public:
  enum Theory {
    THEORY_ARRAYS,
    THEORY_BITVECTORS,
    THEORY_CORE,
    THEORY_INTS,
    THEORY_REALS,
    THEORY_REALS_INTS,
  };

private:
  bool d_logicSet;
  Smt::Logic d_logic;

protected:
  Smt2(ExprManager* exprManager, Input* input, bool strictMode = false);

public:
  /**
   * Add theory symbols to the parser state.
   *
   * @param theory the theory to open (e.g., Core, Ints)
   */
  void addTheory(Theory theory);

  bool logicIsSet();

  /**
   * Sets the logic for the current benchmark. Declares any logic and
   * theory symbols.
   *
   * @param name the name of the logic (e.g., QF_UF, AUFLIA)
   */
  void setLogic(const std::string& name);

  void setInfo(const std::string& flag, const SExpr& sexpr);

  void setOption(const std::string& flag, const SExpr& sexpr);

private:

  void addArithmeticOperators();
};/* class Smt2 */

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__SMT2_INPUT_H */
