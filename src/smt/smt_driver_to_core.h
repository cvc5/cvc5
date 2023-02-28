/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
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

#ifndef CVC5__SMT__SMT_DRIVER_TO_CORE_H
#define CVC5__SMT__SMT_DRIVER_TO_CORE_H

#include "smt/assertions.h"
#include "smt/env_obj.h"
#include "util/result.h"

namespace cvc5::internal {

class SolverEngine;

namespace smt {

class SmtSolver;
class ContextManager;

/**
 * An algorithm for computing a timeout core.
 *
 * The algorithm maintains a set of formulas C and a set of models M, both
 * initially empty.
 * In each iteration of the loop:
 *   If C is unsat, return <unsat, {}>
 *   If C is timeout, return <unknown, C>
 *   If C is sat or unknown with model m:
 *     If m satisfies all input formulas, return <sat, {}>
 *     Otherwise, add m to M.
 *     Update C to C' such that C'^m' = false for all models m' in M and repeat.
 *
 * The selection of C' is done by adding to C a single new assertion from our
 * input that is falsified by m, and then removing from C' any assertions that
 * are not falsified by another assertion already in C'.
 */
class SmtDriverToCore : protected EnvObj
{
 public:
  SmtDriverToCore(Env& env);

  /** get timeout core for the current set of assertions stored in as.
   *
   * Returns a pair containing a result and a list of formulas. If the result is
   * unknown and the reason is timeout, then the list of formulas correspond to
   * a subset of the current assertions that cause a timeout in the specified
   * by timeout-core-timeout. Otherwise, the list of formulas is empty and the
   * result has the same guarantees as a response to checkSat.
   */
  std::pair<Result, std::vector<Node>> getTimeoutCore(const Assertions& as);

 private:
  /** initialize assertions */
  void initializePreprocessedAssertions(const std::vector<Node>& ppAsserts);
  /** get next assertions */
  void getNextAssertions(std::vector<Node>& nextAssertions);
  /** check sat next */
  Result checkSatNext(const std::vector<Node>& nextAssertions);

  /**
   * Record current model, return true if we set d_nextIndexToInclude,
   * indicating that we want to include a new assertion.
   *
   * @param allAssertsSat set to true if the current model satisfies all
   * assertions.
   */
  bool recordCurrentModel(bool& allAssertsSat,
                          SolverEngine* subSolver = nullptr);
  /** has current shared symbol */
  bool hasCurrentSharedSymbol(size_t i) const;
  /** Common nodes */
  Node d_true;
  Node d_false;
  /** The original preprocessed assertions */
  std::vector<Node> d_ppAsserts;
  std::vector<Node> d_asserts;
  /** the model value map */
  std::vector<std::vector<Node>> d_modelValues;
  /** set of model indices that only had unknown points */
  std::unordered_set<size_t> d_unkModels;
  /** mapping from models to the assertions that cover them */
  std::unordered_map<size_t, size_t> d_modelToAssert;
  /** next index to include */
  size_t d_nextIndexToInclude;
  /**
   * All information about an assertion.
   */
  class AssertInfo
  {
   public:
    AssertInfo() : d_coverModels(0) {}
    /** Number of models we cover */
    size_t d_coverModels;
    /** the skolem */
    Node d_skolem;
  };
  /** The current indices in d_ppAsserts we are considering */
  std::map<size_t, AssertInfo> d_ainfo;
  /** Query count */
  size_t d_queryCount;
  /** Current free variables */
  std::unordered_set<Node> d_asymbols;
  /** Free symbols of each assertion */
  std::map<size_t, std::unordered_set<Node>> d_syms;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
