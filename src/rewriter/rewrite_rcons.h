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
 * The module for basic (non-DSL-dependent) automatic reconstructing proofs of
 * THEORY_REWRITE steps.
 */

#include "cvc5_private.h"

#ifndef CVC5__REWRITER__REWRITE_RCONS_H
#define CVC5__REWRITER__REWRITE_RCONS_H

#include <unordered_set>

#include "expr/node.h"
#include "proof/proof.h"
#include "proof/proof_node_manager.h"
#include "theory/builtin/proof_checker.h"

namespace cvc5 {
namespace rewriter {

/**
 */
class TheoryRewriteRCons
{
 public:
  TheoryRewriteRCons(ProofNodeManager* pnm);
  ~TheoryRewriteRCons() {}
  /**
   * Reconstruct
   */
  bool prove(CDProof* cdp, Node a, Node b, theory::TheoryId tid, MethodId mid);

 private:
  /** Try rule */
  bool tryRule(CDProof* cdp, Node eq, PfRule r, const std::vector<Node>& args);
  /** Proof node manager */
  ProofNodeManager* d_pnm;
};

}  // namespace rewriter
}  // namespace cvc5

#endif
