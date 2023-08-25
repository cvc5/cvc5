/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for processing assertions for an SMT engine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__PROCESS_ASSERTIONS_H
#define CVC5__SMT__PROCESS_ASSERTIONS_H

#include <unordered_map>

#include "context/cdlist.h"
#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "smt/env_obj.h"
#include "util/resource_manager.h"

namespace cvc5::internal {

namespace preprocessing {
class AssertionPipeline;
}

namespace smt {

class Assertions;
struct SolverEngineStatistics;

/**
 * Module in charge of processing assertions for an SMT engine.
 *
 * Its main features are:
 * (1) apply(AssertionsPipeline&), which updates the assertions based on our
 * preprocessing steps,
 * (2) expandDefinitions(TNode, ...), which returns the expanded formula of a
 * term.
 * The method finishInit(...) must be called before these methods are called.
 *
 * It is designed to be agnostic to whether we are in incremental mode. That is,
 * it processes assertions in a way that assumes that apply(...) could be
 * applied multiple times to different sets of assertions.
 */
class ProcessAssertions : protected EnvObj
{
  /** The types for the recursive function definitions */
  typedef context::CDList<Node> NodeList;
  typedef std::unordered_map<Node, bool> NodeToBoolHashMap;

 public:
  ProcessAssertions(Env& env, SolverEngineStatistics& stats);
  ~ProcessAssertions();
  /** Finish initialize
   *
   * This initializes the preprocessing passes owned by this module.
   */
  void finishInit(preprocessing::PreprocessingPassContext* pc);
  /** Cleanup
   *
   * This deletes the processing passes owned by this module.
   */
  void cleanup();
  /**
   * Process the formulas in ap. Returns true if there was no conflict when
   * processing the assertions.
   *
   * @param ap The assertions to preprocess.
   */
  bool apply(preprocessing::AssertionPipeline& ap);

 private:
  /** Reference to the SMT stats */
  SolverEngineStatistics& d_slvStats;
  /** The preprocess context */
  preprocessing::PreprocessingPassContext* d_preprocessingPassContext;
  /** True node */
  Node d_true;
  /**
   * Map of preprocessing pass instances, mapping from names to preprocessing
   * pass instance
   */
  std::unordered_map<std::string,
                     std::unique_ptr<preprocessing::PreprocessingPass>>
      d_passes;
  /**
   * Number of calls of simplify assertions active.
   */
  unsigned d_simplifyAssertionsDepth;
  /** Spend resource r by the resource manager of this class. */
  void spendResource(Resource r);
  /**
   * Perform non-clausal simplification of a Node.  This involves
   * Theory implementations, but does NOT involve the SAT solver in
   * any way.
   *
   * Returns false if the formula simplifies to "false"
   */
  bool simplifyAssertions(preprocessing::AssertionPipeline& ap);
  /**
   * Dump assertions. Print the current assertion list to the dump
   * assertions:`key` if it is enabled.
   */
  void dumpAssertions(const std::string& key,
                      const preprocessing::AssertionPipeline& ap);
  /**
   * Dump assertions to stream os using the print benchmark utility.
   */
  void dumpAssertionsToStream(std::ostream& os,
                              const preprocessing::AssertionPipeline& ap);
  /** apply pass */
  preprocessing::PreprocessingPassResult applyPass(
      const std::string& pass, preprocessing::AssertionPipeline& ap);
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
