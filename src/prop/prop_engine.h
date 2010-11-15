/*********************                                                        */
/*! \file prop_engine.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking, dejan
 ** Minor contributors (to current version): cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The PropEngine (proposiitonal engine); main interface point
 ** between CVC4's SMT infrastructure and the SAT solver.
 **
 ** The PropEngine (proposiitonal engine); main interface point
 ** between CVC4's SMT infrastructure and the SAT solver.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROP_ENGINE_H
#define __CVC4__PROP_ENGINE_H

#include "expr/node.h"
#include "util/options.h"
#include "util/result.h"

namespace CVC4 {

class TheoryEngine;

namespace prop {

class CnfStream;
class SatSolver;

/**
 * PropEngine is the abstraction of a Sat Solver, providing methods for
 * solving the SAT problem and conversion to CNF (via the CnfStream).
 */
class PropEngine {

  /**
   * Indicates that the sat solver is currently solving something and we should
   * not mess with it's internal state.
   */
  bool d_inCheckSat;

  /** The global options */
  //const Options d_options;

  /** The theory engine we will be using */
  TheoryEngine *d_theoryEngine;

  context::Context* d_context;

  /** The SAT solver proxy */
  SatSolver* d_satSolver;

  /** List of all of the assertions that need to be made */
  std::vector<Node> d_assertionList;

  /** The CNF converter in use */
  CnfStream* d_cnfStream;

  void printSatisfyingAssignment();

public:

  /**
   * Create a PropEngine with a particular decision and theory engine.
   */
  PropEngine(TheoryEngine*, context::Context*, const Options&);

  /**
   * Destructor.
   */
  CVC4_PUBLIC ~PropEngine();

  /**
   * This is called by SmtEngine, at shutdown time, just before
   * destruction.  It is important because there are destruction
   * ordering issues between some parts of the system (notably between
   * PropEngine and Theory).  For now, there's nothing to do here in
   * the PropEngine.
   */
  void shutdown() { }

  /**
   * Converts the given formula to CNF and assert the CNF to the sat solver.
   * The formula is asserted permanently for the current context.
   * @param node the formula to assert
   */
  void assertFormula(TNode node);

  /**
   * Converts the given formula to CNF and assert the CNF to the sat solver.
   * The formula can be removed by the sat solver after backtracking lower
   * than the (SAT and SMT) level at which it was asserted.
   *
   * @param node the formula to assert
   */
  void assertLemma(TNode node);

  /**
   * Checks the current context for satisfiability.
   */
  Result checkSat();

  /**
   * Get the value of a boolean variable.
   *
   * @return mkConst<true>, mkConst<false>, or Node::null() if
   * unassigned.
   */
  Node getValue(TNode node);

  /**
   * Push the context level.
   */
  void push();

  /**
   * Pop the context level.
   */
  void pop();

};/* class PropEngine */

}/* CVC4::prop namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PROP_ENGINE_H */
