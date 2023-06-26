/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Branch and bound for arithmetic
 */

#include "theory/arith/branch_and_bound.h"

#include "expr/skolem_manager.h"
#include "options/arith_options.h"
#include "proof/eager_proof_generator.h"
#include "proof/proof_node.h"
#include "theory/arith/arith_utilities.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {

BranchAndBound::BranchAndBound(Env& env,
                               TheoryState& s,
                               InferenceManager& im,
                               PreprocessRewriteEq& ppre)
    : EnvObj(env),
      d_astate(s),
      d_im(im),
      d_ppre(ppre),
      d_pfGen(new EagerProofGenerator(env, userContext()))
{
}

std::vector<TrustNode> BranchAndBound::branchIntegerVariable(TNode var,
                                                             Rational value)
{
  std::vector<TrustNode> lems;
  NodeManager* nm = NodeManager::currentNM();
  Integer floor = value.floor();
  if (options().arith.brabTest)
  {
    Trace("integers") << "branch-round-and-bound enabled" << std::endl;
    Integer ceil = value.ceiling();
    Rational f = value - floor;
    // Multiply by -1 to get abs value.
    Rational c = (value - ceil) * (-1);
    Integer nearest = (c > f) ? floor : ceil;

    // Prioritize trying a simple rounding of the real solution first,
    // it that fails, fall back on original branch and bound strategy.
    Node ub = rewrite(nm->mkNode(LEQ, var, nm->mkConstInt(nearest - 1)));
    // The rewritten form should be a GEQ literal, otherwise the split returned
    // by this method will not have its intended effect
    Assert(ub.getKind() == GEQ
           || (ub.getKind() == NOT && ub[0].getKind() == GEQ));
    Node ubatom = ub.getKind() == NOT ? ub[0] : ub;
    Node lb = rewrite(nm->mkNode(GEQ, var, nm->mkConstInt(nearest + 1)));
    Node right = nm->mkNode(OR, ub, lb);
    Node rawEq = nm->mkNode(EQUAL, var, nm->mkConstInt(nearest));
    Node eq = rewrite(rawEq);
    // Also preprocess it before we send it out. This is important since
    // arithmetic may prefer eliminating equalities.
    TrustNode teq;
    if (d_env.theoryOf(eq) == THEORY_ARITH)
    {
      teq = d_ppre.ppRewriteEq(eq);
      eq = teq.isNull() ? eq : teq.getNode();
    }
    Node literal = d_astate.getValuation().ensureLiteral(eq);
    Trace("integers") << "eq: " << eq << "\nto: " << literal << std::endl;
    d_im.requirePhase(literal, true);
    Node l = nm->mkNode(OR, literal, right);
    Trace("integers") << "l: " << l << std::endl;
    if (proofsEnabled())
    {
      ProofNodeManager* pnm = d_env.getProofNodeManager();
      Node less = nm->mkNode(LT, var, nm->mkConstInt(nearest));
      Node greater = nm->mkNode(GT, var, nm->mkConstInt(nearest));
      // TODO (project #37): justify. Thread proofs through *ensureLiteral*.
      Trace("integers::pf") << "less: " << less << std::endl;
      Trace("integers::pf") << "greater: " << greater << std::endl;
      Trace("integers::pf") << "literal: " << literal << std::endl;
      Trace("integers::pf") << "eq: " << eq << std::endl;
      Trace("integers::pf") << "rawEq: " << rawEq << std::endl;
      Pf pfNotLit = pnm->mkAssume(literal.negate());
      // rewrite notLiteral to notRawEq, using teq.
      Pf pfNotRawEq =
          literal == rawEq
              ? pfNotLit
              : pnm->mkNode(
                  PfRule::MACRO_SR_PRED_TRANSFORM,
                  {pfNotLit, teq.getGenerator()->getProofFor(teq.getProven())},
                  {rawEq.negate()});
      Pf pfBot =
          pnm->mkNode(PfRule::CONTRA,
                      {pnm->mkNode(PfRule::ARITH_TRICHOTOMY,
                                   {pnm->mkAssume(less.negate()), pfNotRawEq},
                                   {greater}),
                       pnm->mkAssume(greater.negate())},
                      {});
      std::vector<Node> assumptions = {
          literal.negate(), less.negate(), greater.negate()};
      // Proof of (not (and (not (= v i)) (not (< v i)) (not (> v i))))
      Pf pfNotAnd = pnm->mkScope(pfBot, assumptions);
      Pf pfL = pnm->mkNode(PfRule::MACRO_SR_PRED_TRANSFORM,
                           {pnm->mkNode(PfRule::NOT_AND, {pfNotAnd}, {})},
                           {l});
      lems.push_back(d_pfGen->mkTrustNode(l, pfL));
    }
    else
    {
      lems.push_back(TrustNode::mkTrustLemma(l, nullptr));
    }
  }
  else
  {
    Node ub = rewrite(nm->mkNode(LEQ, var, nm->mkConstInt(floor)));
    // Similar to above, the rewritten form should be a GEQ literal, otherwise
    // the split returned by this method will not have its intended effect
    Assert(ub.getKind() == GEQ
           || (ub.getKind() == NOT && ub[0].getKind() == GEQ));
    Node lb = ub.notNode();
    if (proofsEnabled())
    {
      lems.push_back(d_pfGen->mkTrustNode(
          nm->mkNode(OR, ub, lb), PfRule::SPLIT, {}, {ub}));
    }
    else
    {
      lems.push_back(TrustNode::mkTrustLemma(nm->mkNode(OR, ub, lb), nullptr));
    }
  }
  if (TraceIsOn("integers"))
  {
    Trace("integers") << "integers: branch & bound:";
    for (const TrustNode& tn : lems)
    {
      Trace("integers") << " " << tn;
    }
    Trace("integers") << std::endl;
  }
  return lems;
}

bool BranchAndBound::proofsEnabled() const
{
  return d_env.isTheoryProofProducing();
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
