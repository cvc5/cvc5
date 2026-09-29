/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Preprocess equality rewriter for arithmetic
 */

#include "theory/arith/pp_rewrite_eq.h"

#include "options/arith_options.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "theory/arith/arith_proof_utilities.h"
#include "theory/builtin/proof_checker.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

PreprocessRewriteEq::PreprocessRewriteEq(Env& env)
    : EnvObj(env), d_ppPfGen(env, context(), "Arith::ppRewrite")
{
}

TrustNode PreprocessRewriteEq::ppRewriteEq(TNode atom)
{
  Assert(atom.getKind() == Kind::EQUAL);
  Assert(atom[0].getType().isRealOrInt());
  if (!options().arith.arithRewriteEq)
  {
    // We are not splitting the equality into inequalities below, in which case
    // we normalize it. Note this is applied here and not by Rewriter::rewrite,
    // since normalizing an equality does not preserve its terms, which is
    // incompatible with theory combination for equalities that are generated
    // as literals in lemmas. It is instead an extended equality rewrite, see
    // ArithRewriter::rewriteEqualityExt.
    Node atomn = rewriteEqualityExt(atom);
    if (atomn == atom)
    {
      return TrustNode::null();
    }
    return ppNormalizeEq(atom, atomn);
  }
  Node leq = NodeBuilder(nodeManager(), Kind::LEQ) << atom[0] << atom[1];
  Node geq = NodeBuilder(nodeManager(), Kind::GEQ) << atom[0] << atom[1];
  Node rewritten = leq.andNode(geq);
  Trace("arith::preprocess")
      << "arith::preprocess() : returning " << rewritten << std::endl;
  // don't need to rewrite terms since rewritten is not a non-standard op
  if (d_env.isTheoryProofProducing())
  {
    Node t = builtin::BuiltinProofRuleChecker::mkTheoryIdNode(nodeManager(),
                                                              THEORY_ARITH);
    Node eq = atom.eqNode(rewritten);
    return d_ppPfGen.mkTrustedRewrite(
        atom,
        rewritten,
        d_env.getProofNodeManager()->mkTrustedNode(
            TrustId::THEORY_INFERENCE_ARITH, {}, {}, eq));
  }
  return TrustNode::mkTrustRewrite(atom, rewritten, nullptr);
}

TrustNode PreprocessRewriteEq::ppNormalizeEq(TNode eq, TNode eqn)
{
  Assert(eq.getKind() == Kind::EQUAL);
  if (d_env.isTheoryProofProducing())
  {
    ProofNodeManager* pnm = d_env.getProofNodeManager();
    // The two are equivalent up to polynomial normalization, unless the
    // normalized form is a Boolean constant.
    if (std::shared_ptr<ProofNode> pf = mkArithPolyNormRel(pnm, eq, eqn);
        pf != nullptr)
    {
      return d_ppPfGen.mkTrustedRewrite(eq, eqn, pf);
    }
    Node equiv = eq.eqNode(eqn);
    return d_ppPfGen.mkTrustedRewrite(
        eq,
        eqn,
        pnm->mkTrustedNode(TrustId::THEORY_INFERENCE_ARITH, {}, {}, equiv));
  }
  return TrustNode::mkTrustRewrite(eq, eqn, nullptr);
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
