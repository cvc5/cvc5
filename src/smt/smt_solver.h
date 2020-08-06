/*********************                                                        */
/*! \file smt_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The solver for SMT queries in an SmtEngine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__SMT_SOLVER_H
#define CVC4__SMT__SMT_SOLVER_H

#include <vector>

#include "expr/node.h"
#include "theory/theory_engine.h"
#include "prop/prop_engine.h"
#include "util/result.h"

namespace CVC4 {

class SmtEngine;

namespace smt {

/**
 * A solver for SMT queries.
 * 
 * This class manages the initialization of the theory engine and propositional
 * engines and implements the method for checking satisfiability of the current
 * set of assertions.
 */
class SmtSolver
{
 public:
  SmtSolver(SmtEngine& smt);
  ~SmtSolver();
  /** Create theory engine, prop engine. */
  void finishInit();
  /** Reset all assertions, global declarations, etc.  */
  void resetAssertions();
  /**
   * Interrupt a running query.  This can be called from another thread
   * or from a signal handler.  Throws a ModalException if the SmtSolver
   * isn't currently in a query.
   */
  void interrupt();
  /**
   * Cleanup memory allocated by modules in this class. This is required to be
   * done explicitly so that passes are deleted before the objects they refer
   * to in the SmtEngine destructor.
   */
  void cleanup();
  /**
   * This is called by the destructor of SmtEngine, just before destroying the
   * PropEngine, TheoryEngine, and DecisionEngine (in that order).  It
   * is important because there are destruction ordering issues
   * between PropEngine and Theory.
   */
  void shutdown();
  /** Push a user-level context. */
  void push();
  /** Pop a user-level context. */
  void pop();
  /**
   * Check satisfiability (used to check satisfiability and entailment).
   * Returns the result of 
   */
  Result checkSatisfiability(Assertions& as,
                             const Node& assumption,
                             bool inUnsatCore,
                             bool isEntailmentCheck);
  /** Same as above, for a vector of assumptions */
  Result checkSatisfiability(Assertions& as,
                             const std::vector<Node>& assumptions,
                             bool inUnsatCore,
                             bool isEntailmentCheck);
  //------------------------------------------ access methods
  /** Get a pointer to the TheoryEngine owned by this solver. */
  TheoryEngine* getTheoryEngine() { return d_theoryEngine.get(); }
  /** Get a pointer to the PropEngine owned by this solver. */
  prop::PropEngine* getPropEngine() { return d_propEngine.get(); }
  //------------------------------------------ end access methods
 private:
  /** Reference to The parent SMT engine */
  SmtEngine& d_smt;
  /** The theory engine */
  std::unique_ptr<TheoryEngine> d_theoryEngine;
  /** The propositional engine */
  std::unique_ptr<prop::PropEngine> d_propEngine;
};

}  // namespace smt
}  // namespace CVC4

#endif /* CVC4__SMT__SMT_SOLVER_H */
