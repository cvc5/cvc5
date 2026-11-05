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
 * Prove false from a conflict L1 ... Ln, where each Li is encoded as
 * (= pi 0) and qi is the monic form of pi (qi = pi if pi is already monic).
 *
 * If pi is not monic, with scale factor c, the step for Li is
 *
 *                    ------------------------------------------ FF_POLY_NORM
 *                     (= (* c (+ pi (- 0))) (* 1 (+ qi (- 0))))
 *                    ------------------------------------------ FF_POLY_NORM_EQ
 *   (= Li (= pi 0))   (= (= pi 0) (= qi 0))
 *  ---------------------------------------- TRANS
 *   (= Li (= qi 0))
 *
 * where (= Li (= pi 0)) must already be justified in cdp. Then
 *
 *  (= L1 (= q1 0)) ... (= Ln (= qn 0))
 *  ----------------------------------- NARY_CONG
 *   (and L1 ... Ln)  (= (and L1 ... Ln) (and (= q1 0) ... (= qn 0)))
 *  ---------------------------------------------------------------- EQ_RESOLVE
 *   (and (= q1 0) ... (= qn 0))
 *  ---------------------------------------------- FF_POLY_CONVERSION
 *   (not (set.is_empty (ff.variety (ff.ideal q1 ... qn))))
 *  ---------------------------------------------- FF_FIELD_POLYS
 *   (not (set.is_empty (ff.variety (ff.ideal q1 ... qn f1 ... fm))))
 *  ---------------------------------------------- CONTRA
 *   false
 *
 * where the second premise of CONTRA, (set.is_empty (ff.variety ...)), must
 * be justified elsewhere, NARY_CONG is skipped when n = 1, and FF_FIELD_POLYS
 * is skipped when there are no field polynomials f1 ... fm.
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
 * Prove (= conv 0) from the disequality orig = (not (= a b)), where sk is the
 * witness skolem for orig. Letting w = (+ (* (+ a (- b)) sk) -1):
 *
 *  -------------------------------------------- FF_POLY_NORM
 *   (= (* 1 (+ w (- 0))) (* 1 (+ conv (- 0))))
 *  -------------------------------------------- FF_POLY_NORM_EQ
 *   (= (= w 0) (= conv 0))
 *
 *  ------------------ FF_DISEQ
 *   (= orig (= w 0))   (= (= w 0) (= conv 0))
 *  ------------------------------------------ TRANS
 *   orig   (= orig (= conv 0))
 *  ---------------------------- EQ_RESOLVE
 *   (= conv 0)
 */
void registerDisequalityProof(
    NodeManager* nm, Node orig, Node conv, Node sk, CDProof* cdp);

/**
 * Prove (= conv 0) from the equality orig = (= a b):
 *
 *  ----------------------------------------- FF_POLY_NORM
 *   (= (* 1 (+ a (- b))) (* 1 (+ conv (- 0))))
 *  ----------------------------------------- FF_POLY_NORM_EQ
 *   orig   (= orig (= conv 0))
 *  ---------------------------- EQ_RESOLVE
 *   (= conv 0)
 */
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
