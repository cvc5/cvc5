/*********************                                                        */
/*! \file expand_definitions.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for processing assertions for an SMT engine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__EXPAND_DEFINITIONS_H
#define CVC4__SMT__EXPAND_DEFINITIONS_H

#include <unordered_map>

#include "expr/node.h"
#include "expr/term_conversion_proof_generator.h"
#include "preprocessing/assertion_pipeline.h"
#include "smt/smt_engine_stats.h"
#include "util/resource_manager.h"

namespace CVC4 {

class SmtEngine;

namespace smt {

/**
 * Module in charge of expanding definitions for an SMT engine.
 *
 * Its main features is expandDefinitions(TNode, ...), which returns the
 * expanded formula of a term.
 */
class ExpandDefs
{
 public:
  ExpandDefs(SmtEngine& smt, ResourceManager& rm, SmtEngineStatistics& stats);
  ~ExpandDefs();
  /**
   * Expand definitions in term n. Return the expanded form of n.
   *
   * @param n The node to expand
   * @param cache Cache of previous results
   * @param expandOnly if true, then the expandDefinitions function of
   * TheoryEngine is not called on subterms of n.
   * @return The expanded term.
   */
  Node expandDefinitions(
      TNode n,
      std::unordered_map<Node, Node, NodeHashFunction>& cache,
      bool expandOnly = false);
  /**
   * Expand defintitions in assertions. This applies this above method to each
   * assertion in the given pipeline.
   */
  void expandAssertions(preprocessing::AssertionPipeline& assertions,
                        bool expandOnly = false);

  /**
   * Set proof node manager, which signals this class to enable proofs using the
   * given proof node manager.
   */
  void setProofNodeManager(ProofNodeManager* pnm);

 private:
  /**
   * Helper function for above, called to specify if we want proof production
   * based on the optional argument tpg.
   */
  theory::TrustNode expandDefinitions(
      TNode n,
      std::unordered_map<Node, Node, NodeHashFunction>& cache,
      bool expandOnly,
      TConvProofGenerator* tpg);
  /** Reference to the SMT engine */
  SmtEngine& d_smt;
  /** Reference to resource manager */
  ResourceManager& d_resourceManager;
  /** Reference to the SMT stats */
  SmtEngineStatistics& d_smtStats;
  /** A proof generator for the term conversion. */
  std::unique_ptr<TConvProofGenerator> d_tpg;
};

}  // namespace smt
}  // namespace CVC4

#endif
