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

#include "smt/smt_driver.h"
#include "util/result.h"

namespace cvc5::internal {

class SolverEngine;

namespace smt {

class SmtSolver;
class ContextManager;

class SmtDriverToCore : public SmtDriver
{
 public:
  SmtDriverToCore(Env& env, SmtSolver& smt, ContextManager* ctx);

 protected:
  Result checkSatNext(preprocessing::AssertionPipeline& ap) override;
  void getNextAssertions(preprocessing::AssertionPipeline& ap) override;

 private:
  /** initialize assertions */
  void initializePreprocessedAssertions(const std::vector<Node>& ppAsserts);
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
  /** Initialized */
  bool d_initialized;
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
  /** Use subsolver */
  bool d_useSubsolver;
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
