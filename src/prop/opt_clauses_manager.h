/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Manager of proofs for optimized clauses
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__OPT_CLAUSES_MANAGER_H
#define CVC5__PROP__OPT_CLAUSES_MANAGER_H

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "expr/node.h"
#include "proof/proof.h"

namespace cvc5::internal {
namespace prop {

/**
 * A manager for the proofs of clauses that are stored in the SAT solver in a
 * context level below the one in which its proof is generated.
 *
 * Due to the above, when popping the context in which the proof was generated
 * the respective clause, if ever needed in a subsequent (lower than generated)
 * context, would be proofless. To prevent the issue this manager allows, for a
 * given context, storing a proof in a given level and, when the the respective
 * context pops, proofs of level no greater than the new one are reinserted in
 * the proof marked to be notified.
 */
class OptimizedClausesManager : context::ContextNotifyObj
{
 public:
  /** Constructor for OptimizedClausesManager
   *
   * @param context The context generating notifications
   * @param parentProof The proof to be updated when context pops
   * @param optProofs A mapping from context levels (note it has to be `int`) to
   * proof nodes to be reinserted at these levels
   */
  OptimizedClausesManager(
      context::Context* context,
      CDProof* parentProof,
      std::map<int, std::vector<std::shared_ptr<ProofNode>>>& optProofs);

  /** Adds a hash set of nodes to be tracked and updated when popping
   *
   * This method can be used when it is necessary to track, in a
   * context-dependent manner, other information, in a node hash set, beyond the
   * proofs associated with given clauses. For example, the SAT proof manager
   * needs to bookeep the current assumptions of the SAT solver, which are
   * stored in a node hash set.
   *
   * @param nodeHashSet the node hash set to be updated when context pops
   * @param nodeLevels a mapping from context levels to nodes to be reinserted
   * at these levels
   */
  void trackNodeHashSet(context::CDHashSet<Node>* nodeHashSet,
                        std::map<int, std::vector<Node>>* nodeLevels);

 private:
  /** Event triggered by the tracked contexting popping
   *
   * When the context pops, every proof node associated with a level up to new
   * level is reinsented in `d_parentProof`. Proof nodes with levels above the
   * current one are discarded.
   */
  void contextNotifyPop() override;

  /** The context being tracked. */
  context::Context* d_context;
  /** Map from levels to proof nodes. */
  std::map<int, std::vector<std::shared_ptr<ProofNode>>>& d_optProofs;
  /** Proof to be updated when context pops. */
  CDProof* d_parentProof;
  /** Node hash set to be updated when context pops, if such a set is tracked */
  context::CDHashSet<Node>* d_nodeHashSet;
  /** Map from levels to proof nodes. */
  std::map<int, std::vector<Node>>* d_nodeLevels;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP__OPT_CLAUSES_MANAGER_H */
