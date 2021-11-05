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

#include "theory/arith/branch_and_bound.h"

#include "options/arith_options.h"
#include "proof/eager_proof_generator.h"
#include "proof/proof_node.h"
#include "theory/arith/arith_utilities.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace arith {

BranchAndBound::BranchAndBound(Env& env,
                               ArithState& s,
                               InferenceManager& im,
                               PreprocessRewriteEq& ppre,
                               ProofNodeManager* pnm)
    : EnvObj(env),
      d_astate(s),
      d_im(im),
      d_ppre(ppre),
      d_pfGen(new EagerProofGenerator(pnm, userContext())),
      d_pnm(pnm)
{
}

TrustNode BranchAndBound::branchIntegerVariable(TNode var, Rational value)
{
  TrustNode lem = TrustNode::null();
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
    Node ub = rewrite(nm->mkNode(LEQ, var, mkRationalNode(nearest - 1)));
    Node lb = rewrite(nm->mkNode(GEQ, var, mkRationalNode(nearest + 1)));
    Node right = nm->mkNode(OR, ub, lb);
    Node rawEq = nm->mkNode(EQUAL, var, mkRationalNode(nearest));
    Node eq = rewrite(rawEq);
    // Also preprocess it before we send it out. This is important since
    // arithmetic may prefer eliminating equalities.
    TrustNode teq;
    if (Theory::theoryOf(eq) == THEORY_ARITH)
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
      Node less = nm->mkNode(LT, var, mkRationalNode(nearest));
      Node greater = nm->mkNode(GT, var, mkRationalNode(nearest));
      // TODO (project #37): justify. Thread proofs through *ensureLiteral*.
      Debug("integers::pf") << "less: " << less << std::endl;
      Debug("integers::pf") << "greater: " << greater << std::endl;
      Debug("integers::pf") << "literal: " << literal << std::endl;
      Debug("integers::pf") << "eq: " << eq << std::endl;
      Debug("integers::pf") << "rawEq: " << rawEq << std::endl;
      Pf pfNotLit = d_pnm->mkAssume(literal.negate());
      // rewrite notLiteral to notRawEq, using teq.
      Pf pfNotRawEq =
          literal == rawEq
              ? pfNotLit
              : d_pnm->mkNode(
                    PfRule::MACRO_SR_PRED_TRANSFORM,
                    {pfNotLit,
                     teq.getGenerator()->getProofFor(teq.getProven())},
                    {rawEq.negate()});
      Pf pfBot = d_pnm->mkNode(
          PfRule::CONTRA,
          {d_pnm->mkNode(PfRule::ARITH_TRICHOTOMY,
                         {d_pnm->mkAssume(less.negate()), pfNotRawEq},
                         {greater}),
           d_pnm->mkAssume(greater.negate())},
          {});
      std::vector<Node> assumptions = {
          literal.negate(), less.negate(), greater.negate()};
      // Proof of (not (and (not (= v i)) (not (< v i)) (not (> v i))))
      Pf pfNotAnd = d_pnm->mkScope(pfBot, assumptions);
      Pf pfL = d_pnm->mkNode(PfRule::MACRO_SR_PRED_TRANSFORM,
                             {d_pnm->mkNode(PfRule::NOT_AND, {pfNotAnd}, {})},
                             {l});
      lem = d_pfGen->mkTrustNode(l, pfL);
    }
    else
    {
      lem = TrustNode::mkTrustLemma(l, nullptr);
    }
  }
  else
  {
    Node ub = rewrite(nm->mkNode(LEQ, var, mkRationalNode(floor)));
    Node lb = ub.notNode();
    if (proofsEnabled())
    {
      lem =
          d_pfGen->mkTrustNode(nm->mkNode(OR, ub, lb), PfRule::SPLIT, {}, {ub});
    }
    else
    {
      lem = TrustNode::mkTrustLemma(nm->mkNode(OR, ub, lb), nullptr);
    }
  }

  Trace("integers") << "integers: branch & bound: " << lem << std::endl;
  return lem;
}

bool BranchAndBound::proofsEnabled() const { return d_pnm != nullptr; }

}  // namespace arith
}  // namespace theory
}  // namespace cvc5
