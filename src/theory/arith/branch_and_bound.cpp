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

namespace cvc5 {
namespace theory {
namespace arith {


BranchAndBound::BranchAndBound(ProofNodeManager * pnm) : d_pnm(pnm)
{
}

TrustNode BranchAndBound::branchVariable(TNode var, Rational value)
{
  TrustNode lem = TrustNode::null();
  NodeManager* nm = NodeManager::currentNM();
  Rational floor = value.floor();
  if (options::brabTest())
  {
    Trace("integers") << "branch-round-and-bound enabled" << endl;
    Integer ceil = value.ceiling();
    Rational f = r - floor;
    // Multiply by -1 to get abs value.
    Rational c = (r - ceil) * (-1);
    Integer nearest = (c > f) ? floor : ceil;

    // Prioritize trying a simple rounding of the real solution first,
    // it that fails, fall back on original branch and bound strategy.
    Node ub = Rewriter::rewrite(
        nm->mkNode(kind::LEQ, var, mkRationalNode(nearest - 1)));
    Node lb = Rewriter::rewrite(
        nm->mkNode(kind::GEQ, var, mkRationalNode(nearest + 1)));
    Node right = nm->mkNode(kind::OR, ub, lb);
    Node rawEq = nm->mkNode(kind::EQUAL, var, mkRationalNode(nearest));
    Node eq = Rewriter::rewrite(rawEq);
    // Also preprocess it before we send it out. This is important since
    // arithmetic may prefer eliminating equalities.
    TrustNode teq;
    if (Theory::theoryOf(eq) == THEORY_ARITH)
    {
      teq = d_containing.ppRewriteEq(eq);
      eq = teq.isNull() ? eq : teq.getNode();
    }
    Node literal = d_containing.getValuation().ensureLiteral(eq);
    Trace("integers") << "eq: " << eq << "\nto: " << literal << endl;
    d_containing.getOutputChannel().requirePhase(literal, true);
    Node l = nm->mkNode(kind::OR, literal, right);
    Trace("integers") << "l: " << l << endl;
    if (proofsEnabled())
    {
      Node less = nm->mkNode(kind::LT, var, mkRationalNode(nearest));
      Node greater = nm->mkNode(kind::GT, var, mkRationalNode(nearest));
      // TODO (project #37): justify. Thread proofs through *ensureLiteral*.
      Debug("integers::pf") << "less: " << less << endl;
      Debug("integers::pf") << "greater: " << greater << endl;
      Debug("integers::pf") << "literal: " << literal << endl;
      Debug("integers::pf") << "eq: " << eq << endl;
      Debug("integers::pf") << "rawEq: " << rawEq << endl;
      Pf pfNotLit = d_pnm->mkAssume(literal.negate());
      // rewrite notLiteral to notRawEq, using teq.
      Pf pfNotRawEq =
          literal == rawEq
              ? pfNotLit
              : d_pnm->mkNode(
                  PfRule::MACRO_SR_PRED_TRANSFORM,
                  {pfNotLit, teq.getGenerator()->getProofFor(teq.getProven())},
                  {rawEq.negate()});
      Pf pfBot =
          d_pnm->mkNode(PfRule::CONTRA,
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
    Node ub =
        Rewriter::rewrite(nm->mkNode(kind::LEQ, var, mkRationalNode(floor)));
    Node lb = ub.notNode();
    if (proofsEnabled())
    {
      lem = d_pfGen->mkTrustNode(
          nm->mkNode(kind::OR, ub, lb), PfRule::SPLIT, {}, {ub});
    }
    else
    {
      lem = TrustNode::mkTrustLemma(nm->mkNode(kind::OR, ub, lb), nullptr);
    }
  }

  Trace("integers") << "integers: branch & bound: " << lem << endl;
  if (Debug.isOn("integers"))
  {
    Node l = lem.getNode();
    if (isSatLiteral(l[0]))
    {
      Debug("integers") << "    " << l[0] << " == " << getSatValue(l[0])
                        << endl;
    }
    else
    {
      Debug("integers") << "    " << l[0] << " is not assigned a SAT literal"
                        << endl;
    }
    if (isSatLiteral(l[1]))
    {
      Debug("integers") << "    " << l[1] << " == " << getSatValue(l[1])
                        << endl;
    }
    else
    {
      Debug("integers") << "    " << l[1] << " is not assigned a SAT literal"
                        << endl;
    }
  }
  return lem;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5
