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
 * Branch and bound for arithmetic
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__BRANCH_AND_BOUND__H
#define CVC5__THEORY__ARITH__BRANCH_AND_BOUND__H

#include <map>

#include "expr/node.h"
#include "proof/proof_node_manager.h"
#include "proof/trust_node.h"
#include "theory/arith/arith_state.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/pp_rewrite_eq.h"
#include "util/rational.h"

namespace cvc5 {
namespace theory {
namespace arith {

/**
 * Class is responsible for constructing branch and bound lemmas. It is
 * agnostic to the state of solver; instead is simply given (variable, value)
 * pairs in branchIntegerVariable below and constructs the appropriate lemma.
 */
class BranchAndBound
{
 public:
  BranchAndBound(ArithState& s,
                 InferenceManager& im,
                 PreprocessRewriteEq& ppre,
                 ProofNodeManager* pnm);
  ~BranchAndBound() {}
  /**
   * Branch variable, called when integer var has given value
   * in the current model, returns a split to eliminate this model.
   */
  TrustNode branchIntegerVariable(TNode var, Rational value);

 private:
  /** Are proofs enabled? */
  bool proofsEnabled() const;
  /** Reference to the state */
  ArithState& d_astate;
  /** Reference to the inference manager */
  InferenceManager& d_im;
  /** Reference to the preprocess rewriter for equality */
  PreprocessRewriteEq& d_ppre;
  /** Proof generator. */
  std::unique_ptr<EagerProofGenerator> d_pfGen;
  /** Proof node manager */
  ProofNodeManager* d_pnm;
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif
