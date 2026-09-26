/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for finite field proofs.
 */

#include "theory/ff/proof_utils.h"

#include "util/finite_field_value.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

namespace {

/** Build c * (l + -r), the canonical form used by FF_POLY_NORM. */
Node mkScaledDiff(NodeManager* nm, Node l, Node r, Node c)
{
  return nm->mkNode(
      Kind::FINITE_FIELD_MULT,
      c,
      nm->mkNode(
          Kind::FINITE_FIELD_ADD, l, nm->mkNode(Kind::FINITE_FIELD_NEG, r)));
}

}  // namespace

Node varietyIsEmpty(NodeManager* nm, Node ideal)
{
  Node variety = nm->mkNode(Kind::FINITE_FIELD_VARIETY, ideal);
  return nm->mkNode(Kind::SET_IS_EMPTY, variety);
}

void produceContradiction(
    NodeManager* nm,
    CDProof* cdp,
    const std::vector<Node>& fieldPolys,
    const std::unordered_map<Node, Node>& litToPolyEq,
    const std::unordered_map<Node, std::pair<Node, Node>>& litToMonic,
    const std::vector<Node>& conflict)
{
  const Node unsatCore = nm->mkAnd(conflict);
  std::vector<Node> monicPolys{};
  std::vector<Node> litEquivs{};
  for (const Node& lit : conflict)
  {
    Node litPolyEq = litToPolyEq.at(lit);
    Node litPoly = litPolyEq[0];
    const Integer size = litPoly.getType().getFfSize();
    Node zero = nm->mkConst(FiniteFieldValue(0, size));
    Node one = nm->mkConst(FiniteFieldValue(1, size));
    const auto res = litToMonic.find(lit);
    Assert(res != litToMonic.end());
    auto [scaleFactor, monicPoly] = res->second;
    if (scaleFactor.getConst<FiniteFieldValue>().getValue() != 1)
    {
      // the encoding was scaled to make it monic; lift the proof of the
      // equivalence with the unscaled encoding to the monic one
      Node scaledLitPoly = mkScaledDiff(nm, litPoly, zero, scaleFactor);
      Node monicNorm = mkScaledDiff(nm, monicPoly, zero, one);
      Node monicEqZ = nm->mkNode(Kind::EQUAL, monicPoly, zero);
      Node polyToMonicEq = nm->mkNode(Kind::EQUAL, litPolyEq, monicEqZ);
      Node normEq = nm->mkNode(Kind::EQUAL, scaledLitPoly, monicNorm);
      cdp->addStep(normEq, ProofRule::FF_POLY_NORM, {}, {normEq});
      cdp->addStep(
          polyToMonicEq, ProofRule::FF_POLY_NORM_EQ, {normEq}, {polyToMonicEq});
      cdp->addStep(
          monicEqZ, ProofRule::EQ_RESOLVE, {litPolyEq, polyToMonicEq}, {});
      Node litConvEq = nm->mkNode(Kind::EQUAL, lit, litPolyEq);
      Node litMonicEq = nm->mkNode(Kind::EQUAL, lit, monicEqZ);
      cdp->addStep(
          litMonicEq, ProofRule::TRANS, {litConvEq, polyToMonicEq}, {});
      litEquivs.push_back(litMonicEq);
      monicPolys.push_back(monicPoly);
    }
    else
    {
      // the encoding is already monic, so we already have a proof of the
      // equivalence
      litEquivs.push_back(nm->mkNode(Kind::EQUAL, lit, litPolyEq));
      monicPolys.push_back(litPoly);
    }
  }
  std::vector<Node> polyEqs;
  for (const Node& litEquiv : litEquivs)
  {
    Assert(litEquiv[1].getKind() == Kind::EQUAL);
    polyEqs.push_back(litEquiv[1]);
  }
  Node core = nm->mkAnd(polyEqs);
  Node coreEquiv = nm->mkNode(Kind::EQUAL, unsatCore, core);
  Node idealGens = nm->mkNode(Kind::FINITE_FIELD_IDEAL, monicPolys);
  if (core.getKind() == Kind::AND)
  {
    cdp->addStep(coreEquiv, ProofRule::NARY_CONG, litEquivs, {unsatCore});
  }
  cdp->addStep(core, ProofRule::EQ_RESOLVE, {unsatCore, coreEquiv}, {});
  Trace("ff::proof") << "Assumption: " << unsatCore << std::endl;
  Trace("ff::proof") << "Converting from " << core << std::endl;
  Node hasCommonRoot = varietyIsEmpty(nm, idealGens).negate();
  cdp->addStep(hasCommonRoot,
               ProofRule::FF_POLY_CONVERSION,
               {core},
               {core, hasCommonRoot});
  if (!fieldPolys.empty())
  {
    monicPolys.insert(monicPolys.end(), fieldPolys.begin(), fieldPolys.end());
    idealGens = nm->mkNode(Kind::FINITE_FIELD_IDEAL, monicPolys);
    Node extendedHasCommonRoot = varietyIsEmpty(nm, idealGens).negate();
    cdp->addStep(extendedHasCommonRoot,
                 ProofRule::FF_FIELD_POLYS,
                 {hasCommonRoot},
                 {fieldPolys});
    hasCommonRoot = extendedHasCommonRoot;
  }
  Node falseNode = nm->mkConst<bool>(false);
  Node noCommonRoot = varietyIsEmpty(nm, idealGens);
  cdp->addStep(falseNode, ProofRule::CONTRA, {noCommonRoot, hasCommonRoot}, {});
}

void registerDisequalityProof(
    NodeManager* nm, Node orig, Node conv, Node sk, CDProof* cdp)
{
  Node l = orig[0][0];
  Node r = orig[0][1];
  const Integer size = l.getType().getFfSize();
  Node sub = nm->mkNode(
      Kind::FINITE_FIELD_ADD, l, nm->mkNode(Kind::FINITE_FIELD_NEG, r));
  Node one = nm->mkConst(FiniteFieldValue(1, size));
  Node minusOne = nm->mkConst(FiniteFieldValue(-1, size));
  Node zero = nm->mkConst(FiniteFieldValue(0, size));
  Node diseqWitness = nm->mkNode(Kind::FINITE_FIELD_ADD,
                                 nm->mkNode(Kind::FINITE_FIELD_MULT, sub, sk),
                                 minusOne);
  Node diseqWitnessEqZ = nm->mkNode(Kind::EQUAL, diseqWitness, zero);
  Node convEq = nm->mkNode(Kind::EQUAL, conv, zero);
  Node equiv = nm->mkNode(Kind::EQUAL, diseqWitnessEqZ, convEq);
  Node normEq = nm->mkNode(Kind::EQUAL,
                           mkScaledDiff(nm, diseqWitness, zero, one),
                           mkScaledDiff(nm, conv, zero, one));
  Node origNEquiv = nm->mkNode(Kind::EQUAL, orig, diseqWitnessEqZ);
  Node origConvEquiv = nm->mkNode(Kind::EQUAL, orig, convEq);
  cdp->addStep(origNEquiv, ProofRule::FF_DISEQ, {}, {l, r, sk});
  cdp->addStep(normEq, ProofRule::FF_POLY_NORM, {}, {normEq});
  cdp->addStep(equiv, ProofRule::FF_POLY_NORM_EQ, {normEq}, {equiv});
  cdp->addStep(origConvEquiv, ProofRule::TRANS, {origNEquiv, equiv}, {});
  cdp->addStep(convEq, ProofRule::EQ_RESOLVE, {orig, origConvEquiv}, {});
}

void registerEqualityProof(NodeManager* nm, Node orig, Node conv, CDProof* cdp)
{
  Node l = orig[0];
  Node r = orig[1];
  const Integer size = l.getType().getFfSize();
  Node zero = nm->mkConst(FiniteFieldValue(0, size));
  Node one = nm->mkConst(FiniteFieldValue(1, size));
  Node diffNorm = mkScaledDiff(nm, l, r, one);
  Node convEq = nm->mkNode(Kind::EQUAL, conv, zero);
  Node normEq =
      nm->mkNode(Kind::EQUAL, diffNorm, mkScaledDiff(nm, conv, zero, one));
  Node litConvEq = nm->mkNode(Kind::EQUAL, orig, convEq);
  cdp->addStep(normEq, ProofRule::FF_POLY_NORM, {}, {normEq});
  cdp->addStep(litConvEq, ProofRule::FF_POLY_NORM_EQ, {normEq}, {litConvEq});
  cdp->addStep(convEq, ProofRule::EQ_RESOLVE, {orig, litConvEq}, {});
}

ProofInfo::ProofInfo(ProofRule id,
                     std::vector<Node> children,
                     std::vector<Node> args)
    : d_id(id), d_children(std::move(children)), d_args(std::move(args))
{
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
