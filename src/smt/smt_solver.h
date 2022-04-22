/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for SMT queries in an SolverEngine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__SMT_SOLVER_H
#define CVC5__SMT__SMT_SOLVER_H

#include <vector>

#include "expr/node.h"
#include "smt/assertions.h"
#include "smt/env_obj.h"
#include "smt/preprocessor.h"
#include "theory/logic_info.h"
#include "util/result.h"

namespace cvc5::internal {

class SolverEngine;
class Env;
class TheoryEngine;
class ResourceManager;
class ProofNodeManager;

namespace prop {
class PropEngine;
}

namespace theory {
class QuantifiersEngine;
}

namespace smt {

class SolverEngineState;
struct SolverEngineStatistics;

/**
 * A solver for SMT queries.
 *
 * This class manages the initialization of the theory engine and propositional
 * engines and implements the method for checking satisfiability of the current
 * set of assertions.
 *
 * Notice that this class is only conceptually responsible for running
 * check-sat commands and an interface for sending formulas to the underlying
 * classes. It does not implement any query techniques beyond getting the result
 * (unsat/sat/unknown) of check-sat calls. More detailed information (e.g.
 * models) can be queries using other classes that examine the state of the
 * TheoryEngine directly, which can be accessed via getTheoryEngine.
 */
class SmtSolver : protected EnvObj
{
 public:
  SmtSolver(Env& env,
            AbstractValues& abs,
            SolverEngineStatistics& stats);
  ~SmtSolver();
  /**
   * Create theory engine, prop engine based on the environment.
   */
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
   * Check satisfiability (used to check satisfiability and entailment)
   * in SolverEngine. This is done via adding assumptions (when necessary) to
   * assertions as, preprocessing and pushing assertions into the prop engine
   * of this class, and checking for satisfiability via the prop engine.
   *
   * @param as The object managing the assertions in SolverEngine. This class
   * maintains a current set of (unprocessed) assertions which are pushed
   * into the internal members of this class (TheoryEngine and PropEngine)
   * during this call.
   * @param assumptions The assumptions for this check-sat call, which are
   * temporary assertions.
   */
  Result checkSatisfiability(Assertions& as,
                             const std::vector<Node>& assumptions);
  /**
   * Process the assertions that have been asserted in as. This moves the set of
   * assertions that have been buffered into as, preprocesses them, pushes them
   * into the SMT solver, and clears the buffer.
   */
  void processAssertions(Assertions& as);
  /**
   * Perform a deep restart.
   *
   * This constructs a fresh copy of the theory engine and prop engine, and
   * populates the given assertions for the next call to checkSatisfiability.
   * In particular, we add the preprocessed assertions from the previous
   * call to checkSatisfiability, as well as those in zll.
   *
   * @param as The assertions to populate
   * @param zll The zero-level literals we learned on the previous call to
   * checkSatisfiability.
   */
  void deepRestart(Assertions& as, const std::vector<Node>& zll);
  //------------------------------------------ access methods
  /** Get a pointer to the TheoryEngine owned by this solver. */
  TheoryEngine* getTheoryEngine();
  /** Get a pointer to the PropEngine owned by this solver. */
  prop::PropEngine* getPropEngine();
  /** Get a pointer to the QuantifiersEngine owned by this solver. */
  theory::QuantifiersEngine* getQuantifiersEngine();
  /** Get a pointer to the preprocessor */
  Preprocessor* getPreprocessor();
  //------------------------------------------ end access methods

 private:
  /** Whether we track information necessary for deep restarts */
  bool canDeepRestart() const;
  /** The preprocessor of this SMT solver */
  Preprocessor d_pp;
  /** Reference to the statistics of SolverEngine */
  SolverEngineStatistics& d_stats;
  /** The theory engine */
  std::unique_ptr<TheoryEngine> d_theoryEngine;
  /** The propositional engine */
  std::unique_ptr<prop::PropEngine> d_propEngine;
  //------------------------------------------ Bookkeeping for deep restarts
  /** The exact list of preprocessed assertions we sent to the PropEngine */
  std::vector<Node> d_ppAssertions;
  /** The skolem map associated with d_ppAssertions */
  std::unordered_map<size_t, Node> d_ppSkolemMap;
  /** All learned literals, used for debugging */
  std::unordered_set<Node> d_allLearnedLits;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif /* CVC5__SMT__SMT_SOLVER_H */
