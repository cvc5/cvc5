/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common functions for dealing with proof nodes.
 */

#include "theory/arith/arith_proof_utilities.h"

#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "theory/arith/arith_poly_norm.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

std::vector<Node> getMacroSumUbCoeff(NodeManager* nm,
                                     const std::vector<Pf>& pfs,
                                     const std::vector<Node>& coeffs)
{
  Assert(pfs.size() == coeffs.size());

  std::vector<Node> premises;
  for (const Pf& p : pfs)
  {
    premises.push_back(p->getResult());
  }
  return getMacroSumUbCoeff(nm, premises, coeffs);
}
std::vector<Node> getMacroSumUbCoeff(NodeManager* nm,
                                     const std::vector<Node>& premises,
                                     const std::vector<Node>& coeffs)
{
  Assert(premises.size() == coeffs.size());

  std::vector<Node> ret;
  TypeNode itype = nm->integerType();
  TypeNode rtype = nm->realType();
  // For each coefficient, we must use a real if the lhs or rhs of the relation
  // is a real, or if the coefficient is not integral.
  for (size_t i = 0, ncoeff = coeffs.size(); i < ncoeff; i++)
  {
    Assert(coeffs[i].isConst());
    Node res = premises[i];
    Assert(res.getType().isBoolean() && res.getNumChildren() == 2);
    const Rational& r = coeffs[i].getConst<Rational>();
    bool isReal = !r.isIntegral() || res[0].getType().isReal()
                  || res[1].getType().isReal();
    ret.push_back(nm->mkConstRealOrInt(isReal ? rtype : itype, r));
  }
  return ret;
}

Node expandMacroSumUb(NodeManager* nm,
                      const std::vector<Node>& children,
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

/**
 * Is n a (possibly negated) arithmetic relation, i.e. one that can be related
 * to another arithmetic relation via polynomial normalization?
 */
bool isArithRel(const Node& n)
{
  Node atom = n.getKind() == Kind::NOT ? n[0] : n;
  Kind k = atom.getKind();
  if (k != Kind::EQUAL && k != Kind::GEQ && k != Kind::LEQ && k != Kind::GT
      && k != Kind::LT)
  {
    return false;
  }
  return atom[0].getType().isRealOrInt();
}

std::shared_ptr<ProofNode> ensurePredTransform(ProofNodeManager* pnm,
                                               std::shared_ptr<ProofNode>& pf,
                                               const Node& pred)
{
  Node res = pf->getResult();
  if (res == pred)
  {
    return pf;
  }
  // Two arithmetic relations may be equivalent while having distinct rewritten
  // forms, e.g. (= (+ x 1) 2) and (= x 1), or (= (to_real x) 0.0) and (= x 0),
  // in which case they cannot be related by MACRO_SR_PRED_TRANSFORM. We relate
  // such predicates by polynomial normalization instead, whenever possible.
  if (Pf epf = mkArithPolyNormRel(pnm, res, pred); epf != nullptr)
  {
    return pnm->mkNode(ProofRule::EQ_RESOLVE, {pf, epf}, {}, pred);
  }
  // give the predicate as the expected result, which is important for
  // performance (does not require proof checking).
  return pnm->mkNode(ProofRule::MACRO_SR_PRED_TRANSFORM, {pf}, {pred}, pred);
}

std::shared_ptr<ProofNode> mkArithPolyNormRel(ProofNodeManager* pnm,
                                              const Node& a,
                                              const Node& b)
{
  bool negated = (a.getKind() == Kind::NOT);
  if (!isArithRel(a) || !isArithRel(b) || negated != (b.getKind() == Kind::NOT))
  {
    return nullptr;
  }
  Node aatom = negated ? a[0] : a;
  Node batom = negated ? b[0] : b;
  Rational ca, cb;
  if (!PolyNorm::isArithPolyNormRel(aatom, batom, ca, cb))
  {
    return nullptr;
  }
  Node premise = PolyNorm::getArithPolyNormRelPremise(aatom, batom, ca, cb);
  Pf ppf = pnm->mkNode(ProofRule::ARITH_POLY_NORM, {}, {premise}, premise);
  Node equiv = aatom.eqNode(batom);
  Pf epf = pnm->mkNode(ProofRule::ARITH_POLY_NORM_REL, {ppf}, {equiv}, equiv);
  if (negated)
  {
    // lift the equivalence of the atoms to the negated relations
    Node nequiv = a.eqNode(b);
    std::vector<Node> cargs;
    ProofRule cr = expr::getCongRule(a, cargs);
    epf = pnm->mkNode(cr, {epf}, cargs, nequiv);
  }
  return epf;
}

bool addArithPolyNormRel(CDProof& cdp, const Node& a, const Node& b)
{
  Pf pf = mkArithPolyNormRel(cdp.getManager(), a, b);
  if (pf == nullptr)
  {
    return false;
  }
  cdp.addProof(pf);
  return true;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
