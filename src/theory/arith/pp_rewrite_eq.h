/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Preprocess equality rewriter for arithmetic
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__PP_REWRITE_EQ__H
#define CVC5__THEORY__ARITH__PP_REWRITE_EQ__H

#include "context/context.h"
#include "expr/node.h"
#include "proof/eager_proof_generator.h"
#include "proof/proof_node_manager.h"

namespace cvc5 {
namespace theory {
namespace arith {

/**
 * This class is responsible for rewriting arithmetic equalities based on the
 * current options.
 *
 * In particular, we may rewrite (= x y) to (and (>= x y) (<= x y)).
 */
class PreprocessRewriteEq
{
 public:
  PreprocessRewriteEq(context::Context* c, ProofNodeManager* pnm);
  ~PreprocessRewriteEq() {}
  /**
   * Preprocess equality, applies ppRewrite for equalities. This method is
   * distinct from ppRewrite since it is not allowed to construct lemmas.
   */
  TrustNode ppRewriteEq(TNode eq);

 private:
  /** Are proofs enabled? */
  bool proofsEnabled() const;
  /** Used to prove pp-rewrites */
  EagerProofGenerator d_ppPfGen;
  /** Proof node manager */
  ProofNodeManager* d_pnm;
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif
