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

  /** get timeout core for the current set of assertions stored in ppAsserts.
   *
   * Returns a pair containing a result and a list of formulas C. If the result
   * is unknown and the reason is timeout, then the list C corresponds to
   * a subset of the current assertions that cause a timeout in the specified
   * by timeout-core-timeout. If the result is unsat, then C is an unsat core
   * for the set of assertions. Otherwise, the list of formulas is empty and the
   * result has the same guarantees as a response to checkSat.
   */
  std::pair<Result, std::vector<Node>> getTimeoutCore(
      const std::vector<Node>& ppAsserts,
      const std::map<size_t, Node>& ppSkolemMap);

 private:
  /** initialize assertions */
  void initializePreprocessedAssertions(
      const std::vector<Node>& ppAsserts,
      const std::map<size_t, Node>& ppSkolemMap);
  /** get next assertions */
  void getNextAssertions(std::vector<Node>& nextAssertions);
  /** check sat next */
  Result checkSatNext(const std::vector<Node>& nextAssertions);
  /**
   * Record current model, return true if we set d_nextIndexToInclude,
   * indicating that we want to include a new assertion
   * (d_ppAsserts[d_nextIndexToInclude]).
   *
   * @param allAssertsSat set to true if the current model satisfies all
   * assertions.
   */
  bool recordCurrentModel(bool& allAssertsSat,
                          SolverEngine* subSolver = nullptr);
  /** Does the i^th assertion have a current shared symbol (a free symbol in
   * d_asymbols). */
  bool hasCurrentSharedSymbol(size_t i) const;
  /** Add skolem definitions */
  void getActiveSkolemDefinitions(std::vector<Node>& nextAssertions);

  /** Common nodes */
  Node d_true;
  Node d_false;
  /**
   * The preprocessed assertions, which we have run substitutions and
   * rewriting on
   */
  std::vector<Node> d_ppAsserts;
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
  /** The next index of an assertion to include */
  size_t d_nextIndexToInclude;
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
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
