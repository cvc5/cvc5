/*********************                                                        */
/*! \file process_assertions.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for processing assertions for an SMT engine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__PROCESS_ASSERTIONS_H
#define CVC4__SMT__PROCESS_ASSERTIONS_H

#include <map>

#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "expr/node.h"
#include "expr/type_node.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/assertions.h"
#include "smt/expand_definitions.h"
#include "smt/smt_engine_stats.h"
#include "util/resource_manager.h"

namespace CVC4 {

class SmtEngine;

namespace smt {

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
class ProcessAssertions
{
  /** The types for the recursive function definitions */
  typedef context::CDList<Node> NodeList;
  typedef unordered_map<Node, bool, NodeHashFunction> NodeToBoolHashMap;

 public:
  ProcessAssertions(SmtEngine& smt,
                    ExpandDefs& exDefs,
                    ResourceManager& rm,
                    SmtEngineStatistics& stats);
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
   * Process the formulas in as. Returns true if there was no conflict when
   * processing the assertions.
   */
  bool apply(Assertions& as);

 private:
  /** Reference to the SMT engine */
  SmtEngine& d_smt;
  /** Reference to expand definitions module */
  ExpandDefs& d_exDefs;
  /** Reference to resource manager */
  ResourceManager& d_resourceManager;
  /** Reference to the SMT stats */
  SmtEngineStatistics& d_smtStats;
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
  void spendResource(ResourceManager::Resource r);
  /**
   * Perform non-clausal simplification of a Node.  This involves
   * Theory implementations, but does NOT involve the SAT solver in
   * any way.
   *
   * Returns false if the formula simplifies to "false"
   */
  bool simplifyAssertions(preprocessing::AssertionPipeline& assertions);
  /**
   * Dump assertions. Print the current assertion list to the dump
   * assertions:`key` if it is enabled.
   */
  void dumpAssertions(const char* key,
                      const preprocessing::AssertionPipeline& assertionList);
};

}  // namespace smt
}  // namespace CVC4

#endif
