/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common functions for dealing with proof nodes.
 */

#include "theory/arith/arith_proof_utilities.h"

#include "proof/proof_node_manager.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

std::vector<Node> getMacroSumUbCoeff(const std::vector<Pf>& pfs,
                                     const std::vector<Node>& coeffs)
{
  Assert(pfs.size() == coeffs.size());
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> ret;
  TypeNode itype = nm->integerType();
  TypeNode rtype = nm->realType();
  // For each coefficient, we must use a real if the lhs or rhs of the relation
  // is a real, or if the coefficient is not integral.
  for (size_t i = 0, ncoeff = coeffs.size(); i < ncoeff; i++)
  {
    Assert(coeffs[i].isConst());
    Node res = pfs[i]->getResult();
    Assert(res.getType().isBoolean() && res.getNumChildren() == 2);
    const Rational& r = coeffs[i].getConst<Rational>();
    bool isReal = !r.isIntegral() || res[0].getType().isReal()
                  || res[1].getType().isReal();
    ret.push_back(nm->mkConstRealOrInt(isReal ? rtype : itype, r));
  }
  return ret;
}

Node expandMacroSumUb(const std::vector<Node>& children,
                      const std::vector<Node>& args,
                      CDProof* cdp)
{
  if (TraceIsOn("macro::arith"))
  {
    Trace("macro::arith") << "Expand MACRO_ARITH_SCALE_SUM_UB" << std::endl;
    for (const auto& child : children)
    {
      Trace("macro::arith") << "  child: " << child << std::endl;
    }
    Trace("macro::arith") << "   args: " << args << std::endl;
  }
  Assert(args.size() == children.size());
  NodeManager* nm = NodeManager::currentNM();
  ProofStepBuffer steps{cdp->getManager()->getChecker()};

  // Scale all children, accumulating
  std::vector<Node> scaledRels;
  Node one = nm->mkConstInt(Rational(1));
  for (size_t i = 0; i < children.size(); ++i)
  {
    TNode child = children[i];
    TNode scalar = args[i];
    if (scalar.getConst<Rational>() == 1)
    {
      // if scaled by one, just take original
      scaledRels.push_back(child);
      continue;
    }
    bool isPos = scalar.getConst<Rational>() > 0;
    Node scalarCmp =
        nm->mkNode(isPos ? Kind::GT : Kind::LT,
                   scalar,
                   nm->mkConstRealOrInt(scalar.getType(), Rational(0)));
    // (= scalarCmp true)
    Node scalarCmpOrTrue = steps.tryStep(ProofRule::EVALUATE, {}, {scalarCmp});
    Assert(!scalarCmpOrTrue.isNull());
    // scalarCmp
    steps.addStep(ProofRule::TRUE_ELIM, {scalarCmpOrTrue}, {}, scalarCmp);
    // (and scalarCmp relation)
    Node scalarCmpAndRel =
        steps.tryStep(ProofRule::AND_INTRO, {scalarCmp, child}, {});
    Assert(!scalarCmpAndRel.isNull());
    // (=> (and scalarCmp relation) scaled)
    Node impl = steps.tryStep(
        isPos ? ProofRule::ARITH_MULT_POS : ProofRule::ARITH_MULT_NEG,
        {},
        {scalar, child});
    Assert(!impl.isNull());
    // scaled
    Node scaled =
        steps.tryStep(ProofRule::MODUS_PONENS, {scalarCmpAndRel, impl}, {});
    Assert(!scaled.isNull());
    scaledRels.emplace_back(scaled);
  }

  Node sumBounds = steps.tryStep(ProofRule::ARITH_SUM_UB, scaledRels, {});
  cdp->addSteps(steps);
  Trace("macro::arith") << "Expansion done. Proved: " << sumBounds << std::endl;
  return sumBounds;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
