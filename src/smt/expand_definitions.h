/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for processing assertions for an SMT engine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__EXPAND_DEFINITIONS_H
#define CVC5__SMT__EXPAND_DEFINITIONS_H

#include <unordered_map>

#include "expr/node.h"
#include "theory/trust_node.h"

namespace cvc5 {

class Env;
class ProofNodeManager;
class TConvProofGenerator;

namespace smt {

struct SmtEngineStatistics;

/**
 * Module in charge of expanding definitions for an SMT engine.
 *
 * Its main features is expandDefinitions(TNode, ...), which returns the
 * expanded formula of a term.
 */
class ExpandDefs
{
 public:
  ExpandDefs(Env& env, SmtEngineStatistics& stats);
  ~ExpandDefs();
  /**
   * Expand definitions in term n. Return the expanded form of n.
   *
   * @param n The node to expand
   * @param cache Cache of previous results
   * @return The expanded term.
   */
  Node expandDefinitions(
      TNode n, std::unordered_map<Node, Node, NodeHashFunction>& cache);

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
      TConvProofGenerator* tpg);
  /** Reference to the environment. */
  Env& d_env;
  /** Reference to the SMT stats */
  SmtEngineStatistics& d_smtStats;
  /** A proof generator for the term conversion. */
  std::unique_ptr<TConvProofGenerator> d_tpg;
};

}  // namespace smt
}  // namespace cvc5

#endif
