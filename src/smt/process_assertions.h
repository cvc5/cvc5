/*********************                                                        */
/*! \file process_assertions.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for processing assertions for an SMT engine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__PROCESS_ASSERTIONS_H
#define CVC4__SMT__PROCESS_ASSERTIONS_H

#include <map>

#include "expr/node.h"
#include "expr/type_node.h"
#include "context/cdlist.h"
#include "context/cdhashmap.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "util/resource_manager.h"
#include "smt/smt_engine_stats.h"

namespace CVC4 {
  
class SmtEngine;

namespace smt {

/** 
 * Module in charge of processing assertions for an SMT engine.
 * 
 * It is designed to be agnostic to whether we are in incremental mode. That is,
 * it processes assertions in a way that assumes that apply(...) can be
 * applied multiple times to assertions.
 */
class ProcessAssertions {
  /** The types for the recursive function definitions */
  typedef context::CDList<Node> NodeList;
  typedef unordered_map<Node, Node, NodeHashFunction> NodeToNodeHashMap;
  typedef unordered_map<Node, bool, NodeHashFunction> NodeToBoolHashMap;
 public:
  ProcessAssertions(SmtEngine& smt, SmtEngineStatistics& stats, ResourceManager& rm);

  ~ProcessAssertions();
  /**
   * Process the assertions that have been asserted. Returns true if there
   * was no conflict when processing the assertions.
   */
  bool apply(preprocessing::AssertionPipeline& assertions);
  /** Finish init */
  void finishInit(preprocessing::PreprocessingPassContext* pc);
  /** Cleanup */
  void cleanup();
  /** 
   * Expand definitions in n. Return the expanded form of n.
   * If expandOnly is true, then the expandDefinitions function of TheoryEngine
   * is not called on subterms of n.
   */
  Node expandDefinitions(TNode n,
                         NodeToNodeHashMap& cache,
                         bool expandOnly = false);
private:
  /** Reference to the SMT engine */
  SmtEngine& d_smt;
  /** Reference to the statistics of SMT engine */
  SmtEngineStatistics& d_stats;
  /** Reference to resource manager */
  ResourceManager& d_resourceManager;
  /** The preprocess context */
  preprocessing::PreprocessingPassContext* d_preprocessingPassContext;
  /** True node */
  Node d_true;
  /**
   * Map of preprocessing pass instances, mapping from names to preprocessing
   * pass instance
   */
  std::unordered_map<std::string, std::unique_ptr<preprocessing::PreprocessingPass>> d_passes;
  /** 
   * Number of calls of simplify assertions active.
   */
  unsigned d_simplifyAssertionsDepth;
  /** recursive function definition abstractions for fmf-fun */
  std::map<Node, TypeNode> d_fmfRecFunctionsAbs;
  /** map to concrete definitions for fmf-fun */
  std::map<Node, std::vector<Node> > d_fmfRecFunctionsConcrete;
  /** List of defined recursive functions processed by fmf-fun */
  NodeList* d_fmfRecFunctionsDefined;
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
  /**
   * Helper function to fix up assertion list to restore invariants needed after
   * ite removal.
   */
  void collectSkolems(IteSkolemMap& iskMap, TNode n, set<TNode>& skolemSet, NodeToBoolHashMap& cache);
  /**
   * Helper function to fix up assertion list to restore invariants needed after
   * ite removal.
   */
  bool checkForBadSkolems(IteSkolemMap& iskMap, TNode n, TNode skolem, NodeToBoolHashMap& cache);
};

}
}

#endif
