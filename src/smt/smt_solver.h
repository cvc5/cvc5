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
   * Refresh the assertions that have been asserted in as. This moves the set of
   * assertions that have been buffered into as, preprocesses them, pushes them
   * into the SMT solver, and clears the buffer. We ensure that assertions
   * are refreshed eagerly during user pushes to ensure that assertions are
   * only preprocessed in one context.
   */
  void refreshAssertions();
  /**
   * Get the list of preprocessed assertions. Only valid if
   * trackPreprocessedAssertions is true.
   */
  const std::vector<Node>& getPreprocessedAssertions() const;
  /**
   * Get the skolem map corresponding to the preprocessed assertions. Only valid
   * if trackPreprocessedAssertions is true.
   */
  const std::unordered_map<size_t, Node>& getPreprocessedSkolemMap() const;
  /** Performs a push on the underlying prop engine. */
  void pushPropContext();
  /** Performs a pop on the underlying prop engine. */
  void popPropContext();
  /**
   * Reset the prop engine trail and call the postsolve method of the
   * underlying TheoryEngine.
   */
  void postsolve();
  //------------------------------------------ access methods
  /** Get a pointer to the TheoryEngine owned by this solver. */
  TheoryEngine* getTheoryEngine();
  /** Get a pointer to the PropEngine owned by this solver. */
  prop::PropEngine* getPropEngine();
  /** Get a pointer to the QuantifiersEngine owned by this solver. */
  theory::QuantifiersEngine* getQuantifiersEngine();
  /** Get a pointer to the preprocessor */
  Preprocessor* getPreprocessor();
  /** Get the assertions maintained by this SMT solver */
  Assertions& getAssertions();
  //------------------------------------------ end access methods
  /**
   * Preprocess the assertions. This calls the preprocessor on the assertions
   * d_asserts and records d_ppAssertions / d_ppSkolemMap if necessary.
   */
  void preprocess(preprocessing::AssertionPipeline& ap);
  /**
   * Push the assertions to the prop engine. Assumes that the assertions
   * (d_asserts) have been preprocessed. This pushes the assertions
   * into the prop engine of this solver and subsequently clears d_asserts.
   */
  void assertToInternal(preprocessing::AssertionPipeline& ap);
  /**
   * Check satisfiability based on the current state of the prop engine.
   * This assumes we have pushed the necessary assertions to it. It post
   * processes the results based on the options.
   */
  Result checkSatInternal();

 private:
  /** Whether we track information necessary for deep restarts */
  bool trackPreprocessedAssertions() const;
  /** The preprocessor of this SMT solver */
  Preprocessor d_pp;
  /** Assertions manager */
  smt::Assertions d_asserts;
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
