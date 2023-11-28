/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A module for computing a timeout core from a set of assertions.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__TIMEOUT_CORE_MANAGER_H
#define CVC5__SMT__TIMEOUT_CORE_MANAGER_H

#include "expr/subs.h"
#include "smt/assertions.h"
#include "smt/env_obj.h"
#include "util/result.h"

namespace cvc5::internal {

class SolverEngine;

namespace smt {

class SmtSolver;
class ContextManager;

/**
 * A module for computing a timeout core.
 *
 * The algorithm it uses maintains a set of formulas C and a set of models M,
 * both initially empty.
 * In each iteration of the loop:
 *   If C is unsat, return <unsat, C>
 *   If C is timeout, return <unknown, C>
 *   If C is sat or unknown with model m:
 *     If m satisfies all input formulas, return <sat, {}>
 *     Otherwise, add m to M.
 *     Update C to C' such that C'^m' = false for all models m' in M and repeat.
 *
 * The selection of C' is done by adding to C a single new assertion from our
 * input that is falsified by m, and then removing from C any assertions that
 * are not falsified by another assertion already in C'. In detail, each model
 * in M is "owned" by an assertion in C. When a new assertion is added to C,
 * it takes ownership of all models that it is falsified by.
 *
 * In the worst case, this algorithm runs N check-sat calls, where N is the
 * number of assertions, since assertions are added one at a time and if
 * an assertion is ever removed from C, it is never readded.
 *
 * On average, it is expected that timeout cores are similar in size to unsat
 * cores, so the average number of check-sat calls is roughly 25% of N
 * typically, as a very rough estimate.
 *
 * However, it is important to note that all check-sat which do not lead to
 * termination are *not* timeouts. When we encounter the first timeout, our
 * set is already minimal covering of the models we have accumulated so far.
 * This is important for performance since there is at most one *timeout* call
 * to check-sat.
 */
class TimeoutCoreManager : protected EnvObj
{
 public:
  TimeoutCoreManager(Env& env);

  /**
   * Get timeout core for the current set of assertions stored in ppAsserts.
   *
   * Returns a pair containing a result and a list of formulas C. For details,
   * see Solver::getTimeoutCore.
   *
   * If assumptions is non-empty, the timeout core is a subset of formulas in
   * assumptions.
   *
   * Otherwise, the timeout core is a subset of formulas in ppAsserts.
   *
   * @param ppAsserts The preprocessed assertions
   * @param ppSkolemMap Mapping from indices in ppAsserts to skolem it defined,
   * if applicable.
   * @param assumptions The assumptions, if non-empty
   */
  std::pair<Result, std::vector<Node>> getTimeoutCore(
      const std::vector<Node>& ppAsserts,
      const std::map<size_t, Node>& ppSkolemMap,
      const std::vector<Node>& assumptions);
  /** Get the SMT solver */
  SolverEngine* getSubSolver();

 private:
  /** initialize assertions */
  void initializeAssertions(const std::vector<Node>& ppAsserts,
                            const std::map<size_t, Node>& ppSkolemMap,
                            const std::vector<Node>& assumptions);
  /**
   * Get next assertions
   *
   * @param nextInclude The indices of assertions to include. Note that
   * during this method, we may refine the current set of assertions we are
   * considering based on what is included.
   * @param nextAssertions The assertions for the next checkSat call, which
   * are populated during this call. Note this may include auxiliary definitions
   * not directly referenced in nextInclude.
   */
  void getNextAssertions(const std::vector<size_t>& nextInclude,
                         std::vector<Node>& nextAssertions);
  /**
   * Check sat next
   * @param nextAssertions The assertions to check on this call
   * @param nextInclude The indices of assertions to add for the next call,
   * which are populated during this call.
   * @return The result of the checkSatNext.
   */
  Result checkSatNext(const std::vector<Node>& nextAssertions,
                      std::vector<size_t>& nextInclude);
  /**
   * Record current model, return true if nextInclude is non-empty, which
   * contains the list of indices of new assertions that we would like to
   * add for the next check-sat call.
   *
   * @param allAssertsSat set to true if the current model satisfies all
   * assertions.
   */
  bool recordCurrentModel(bool& allAssertsSat,
                          std::vector<size_t>& nextInclude);
  /** Include the i^th assertion */
  void includeAssertion(size_t index, bool& removedAssertion);
  /**
   * Does the i^th assertion have a current shared symbol (a free symbol in
   * d_asymbols).
   */
  bool hasCurrentSharedSymbol(size_t i) const;
  /** Get active definitions */
  void getActiveDefinitions(std::vector<Node>& nextAssertions);
  /** Subsolver */
  std::unique_ptr<SolverEngine> d_subSolver;
  /** Common nodes */
  Node d_true;
  Node d_false;
  /**
   * The preprocessed assertions which are candidates for the timeout core
   * that we are working with.
   */
  std::vector<Node> d_ppAsserts;
  /**
   * A vector of the same size as above that we should report as the timeout
   * core.
   */
  std::vector<Node> d_ppAssertsOrig;

  /** Number of non-skolem definitions, a prefix of d_ppAsserts */
  size_t d_numAssertsNsk;
  /**
   * Mapping from skolem variables to their skolem definitions included in
   * the assertions.
   */
  std::map<Node, Node> d_skolemToAssert;
  /**
   * The cache of models, we store a model as the model value of each assertion
   * in d_ppAsserts.
   */
  std::vector<std::vector<Node>> d_modelValues;
  /**
   * Set of indices in d_modelValues that only had unknown (but no false)
   * values of assertions.
   */
  std::unordered_set<size_t> d_unkModels;
  /**
   * Mapping from indices in d_modelToAssert to index of the assertion that
   * covers them */
  std::unordered_map<size_t, size_t> d_modelToAssert;
  /** Information about an assertion. */
  class AssertInfo
  {
   public:
    AssertInfo() : d_coverModels(0) {}
    /** Number of models we cover */
    size_t d_coverModels;
  };
  /**
   * The current indices in d_ppAsserts we are considering. The assertions
   * whose indices are in the domain of this map are the current candidate
   * timeout core.
   */
  std::map<size_t, AssertInfo> d_ainfo;
  /** The current set of free variables of the current candidate core. */
  std::unordered_set<Node> d_asymbols;
  /** Free symbols of each assertion */
  std::map<size_t, std::unordered_set<Node>> d_syms;
  /** Globally included assertions */
  std::vector<Node> d_globalInclude;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
