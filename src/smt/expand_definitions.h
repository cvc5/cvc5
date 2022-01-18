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
#include "proof/trust_node.h"
#include "smt/env_obj.h"

namespace cvc5 {

class ProofNodeManager;
class TConvProofGenerator;

namespace smt {

/**
 * Module in charge of expanding definitions for an SMT engine.
 *
 * Its main features is expandDefinitions(TNode, ...), which returns the
 * expanded formula of a term.
 */
class ExpandDefs : protected EnvObj
{
 public:
  ExpandDefs(Env& env);
  ~ExpandDefs();
  /**
   * Expand definitions in term n. Return the expanded form of n.
   *
   * @param n The node to expand
   * @param cache Cache of previous results
   * @return The expanded term.
   */
  Node expandDefinitions(TNode n, std::unordered_map<Node, Node>& cache);

  /** Enable proofs using the proof node manager of the env. */
  void enableProofs();

 private:
  /**
   * Helper function for above, called to specify if we want proof production
   * based on the optional argument tpg.
   */
  TrustNode expandDefinitions(TNode n,
                              std::unordered_map<Node, Node>& cache,
                              TConvProofGenerator* tpg);
  /** A proof generator for the term conversion. */
  std::unique_ptr<TConvProofGenerator> d_tpg;
};

}  // namespace smt
}  // namespace cvc5

#endif
