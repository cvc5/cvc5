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

#include "theory/arith/pp_rewrite_eq.h"

#include "options/arith_options.h"
#include "theory/builtin/proof_checker.h"
#include "theory/rewriter.h"

namespace cvc5 {
namespace theory {
namespace arith {

PreprocessRewriteEq::PreprocessRewriteEq(context::Context* c,
                                         ProofNodeManager* pnm)
    : d_ppPfGen(pnm, c, "Arith::ppRewrite"), d_pnm(pnm)
{
}

TrustNode PreprocessRewriteEq::ppRewriteEq(TNode atom)
{
  Assert(atom.getKind() == kind::EQUAL);
  if (!options::arithRewriteEq())
  {
    return TrustNode::null();
  }
  Assert(atom[0].getType().isReal());
  Node leq = NodeBuilder(kind::LEQ) << atom[0] << atom[1];
  Node geq = NodeBuilder(kind::GEQ) << atom[0] << atom[1];
  Node rewritten = Rewriter::rewrite(leq.andNode(geq));
  Debug("arith::preprocess")
      << "arith::preprocess() : returning " << rewritten << std::endl;
  // don't need to rewrite terms since rewritten is not a non-standard op
  if (proofsEnabled())
  {
    Node t = builtin::BuiltinProofRuleChecker::mkTheoryIdNode(THEORY_ARITH);
    return d_ppPfGen.mkTrustedRewrite(
        atom,
        rewritten,
        d_pnm->mkNode(
            PfRule::THEORY_INFERENCE, {}, {atom.eqNode(rewritten), t}));
  }
  return TrustNode::mkTrustRewrite(atom, rewritten, nullptr);
}

bool PreprocessRewriteEq::proofsEnabled() const { return d_pnm != nullptr; }

}  // namespace arith
}  // namespace theory
}  // namespace cvc5
