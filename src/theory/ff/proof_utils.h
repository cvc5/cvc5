/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for finite field proofs.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__PROOF_UTILS_H
#define CVC5__THEORY__FF__PROOF_UTILS_H

// std includes
#include <unordered_map>
#include <utility>
#include <vector>

// internal includes
#include "expr/node.h"
#include "proof/proof.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/** Build the term stating that the variety of this ideal is empty. */
Node varietyIsEmpty(NodeManager* nm, Node ideal);

/**
 * Prove false from a conflict.
 *
 * @param fieldPolys the field polynomials that were used, if any
 * @param litToPolyEq map from each literal to the equality (p = 0) that
 * encodes it
 * @param litToMonic map from each literal to the (scale factor, monic
 * polynomial) pair that makes its encoding monic
 * @param conflict the conflicting literals
 */
void produceContradiction(
    NodeManager* nm,
    CDProof* cdp,
    const std::vector<Node>& fieldPolys,
    const std::unordered_map<Node, Node>& litToPolyEq,
    const std::unordered_map<Node, std::pair<Node, Node>>& litToMonic,
    const std::vector<Node>& conflict);

/**
 * Prove that the disequality orig is equivalent to (conv = 0), where sk is the
 * witness skolem for orig.
 */
void registerDisequalityProof(
    NodeManager* nm, Node orig, Node conv, Node sk, CDProof* cdp);

/** Prove that the equality orig is equivalent to (conv = 0). */
void registerEqualityProof(NodeManager* nm, Node orig, Node conv, CDProof* cdp);

/** A proof step that has not been added to a proof yet. */
class ProofInfo
{
 public:
  ProofInfo(ProofRule id, std::vector<Node> children, std::vector<Node> args);
  /** the rule of the step */
  ProofRule d_id;
  /** the premises of the step */
  std::vector<Node> d_children;
  /** the arguments of the step */
  std::vector<Node> d_args;
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__PROOF_UTILS_H */
