/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Ideal membership proofs.
 */

#ifdef CVC5_USE_COCOA

#include "theory/ff/membership_proof_manager.h"

// external includes
#include <CoCoA/SparsePolyOps-RingElem.H>
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/SparsePolyRing.H>
#include <CoCoA/TmpGPoly.H>

// std includes
#include <utility>

// internal includes
#include "proof/proof.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

MembershipProofManager::MembershipProofManager(Env& env,
                                               const std::vector<Node>& polys,
                                               Node ideal,
                                               CoCoA::ring ring,
                                               CocoaEncoder& enc,
                                               CDProof* proof)
    : EnvObj(env),
      d_ideal(ideal),
      d_cocoaRing(ring),
      d_factToProof(),
      d_enc(enc),
      d_proof(proof)
{
  Trace("ff::proof") << "Inputs:" << std::endl;
  for (const Node& polyRepr : polys)
  {
    Trace("ff::proof") << "\t" << polyRepr << std::endl;
    storeProof(polyRepr, ProofRule::FF_IDEAL_GENERATOR, {}, {polyRepr});
  }
}

void MembershipProofManager::updateIdeal(Node ideal) { d_ideal = ideal; }

Node MembershipProofManager::produceMembershipNode(Node poly)
{
  return nodeManager()->mkNode(Kind::SET_MEMBER, poly, d_ideal);
}

void MembershipProofManager::setFunctionPointers()
{
  MembershipProofManager* t = this;
  d_sPoly =
      std::function([=](CoCoA::ConstRefRingElem p,
                        CoCoA::ConstRefRingElem q,
                        CoCoA::ConstRefRingElem s) { t->sPoly(p, q, s); });
  d_reductionStart =
      std::function([=](CoCoA::ConstRefRingElem p) { t->reductionStart(p); });
  d_reductionStep =
      std::function([=](CoCoA::ConstRefRingElem p) { t->reductionStep(p); });
  d_reductionEnd =
      std::function([=](CoCoA::ConstRefRingElem p) { t->reductionEnd(p); });
  d_monicProof = std::function(
      [=](CoCoA::ConstRefRingElem poly, CoCoA::ConstRefRingElem monic) {
        t->monicProof(poly, monic);
      });
  d_membershipStart =
      std::function([=](CoCoA::ConstRefRingElem p) { t->membershipStart(p); });
  d_membershipStep =
      std::function([=](CoCoA::ConstRefRingElem p) { t->membershipStep(p); });
  d_membershipEnd = std::function([=]() { t->membershipEnd(); });
  d_storeMultiplier = std::function(
      [=](CoCoA::ConstRefRingElem mul) { t->storeMultiplier(mul); });
  d_storeMultiplierRaw = std::function(
      [=](CoCoA::DistrMPolyInlPP& mul) { t->storeMultiplierRaw(mul); });
  d_storeMultiplierRawFp = std::function(
      [=](CoCoA::DistrMPolyInlFpPP& mul) { t->storeMultiplierRaw(mul); });

  CoCoA::sPolyProof = d_sPoly;
  CoCoA::reductionStartProof = d_reductionStart;
  CoCoA::reductionStepProof = d_reductionStep;
  CoCoA::reductionEndProof = d_reductionEnd;
  CoCoA::membershipStart = d_membershipStart;
  CoCoA::membershipStep = d_membershipStep;
  CoCoA::membershipEnd = d_membershipEnd;
  CoCoA::monicProof = d_monicProof;
  CoCoA::storeMultiplier = d_storeMultiplier;
  CoCoA::storeMultiplierRaw = d_storeMultiplierRaw;
  CoCoA::storeMultiplierRawFp = d_storeMultiplierRawFp;
}

void MembershipProofManager::storeProof(Node poly,
                                        ProofRule id,
                                        std::vector<Node> children,
                                        std::vector<Node> args)
{
  d_factToProof.emplace(poly,
                        ProofInfo(id, std::move(children), std::move(args)));
}

Node MembershipProofManager::getMembershipFact(CoCoA::ConstRefRingElem poly)
{
  return produceMembershipNode(d_enc.decode(poly));
}

Node MembershipProofManager::proveIdealMembership(CoCoA::RingElem poly,
                                                  CoCoA::ideal ideal)
{
  Node polyRepr = d_enc.decode(poly);
  Node membershipRepr = produceMembershipNode(polyRepr);
  if (d_factToProof.count(polyRepr))
  {
    return membershipRepr;
  }
  Assert(CoCoA::HasGBasis(ideal));
  AlwaysAssert(CoCoA::IsElem(poly, ideal));
  Trace("ff::proof") << "Ideal has element " << poly
                     << " with membership representation " << membershipRepr
                     << std::endl;
  return membershipRepr;
}

void MembershipProofManager::registerProofs()
{
  for (const auto& it : d_factToProof)
  {
    Node conclusion = produceMembershipNode(it.first);
    ProofRule id = it.second.d_id;
    std::vector<Node> children = it.second.d_children;
    std::vector<Node> args = it.second.d_args;
    if (id == ProofRule::FF_IDEAL_GENERATOR)
    {
      args.push_back(d_ideal);
    }
    else
    {
      for (Node& child : children)
      {
        child = produceMembershipNode(child);
      }
    }
    d_proof->addStep(conclusion, id, children, args);
  }
}

void MembershipProofManager::storeMultiplier(CoCoA::ConstRefRingElem p)
{
  Trace("ff::proof") << "Reduction multiplier: " << d_enc.decode(p)
                     << std::endl;
  d_multiplierSeq.push_back(p);
}

template <typename T>
void MembershipProofManager::storeMultiplierRaw(T& p)
{
  // CoCoALib hands us its internal polynomial representation, so we rebuild a
  // ring element from the monomials
  CoCoA::RingElem poly = CoCoA::zero(d_cocoaRing);
  typename T::iter iter(p);
  for (; !CoCoA::IsEnded(iter); ++iter)
  {
    poly += CoCoA::monomial(d_cocoaRing, CoCoA::coeff(iter), CoCoA::PP(iter));
  }
  storeMultiplier(poly);
}
template void MembershipProofManager::storeMultiplierRaw<
    CoCoA::DistrMPolyInlPP>(CoCoA::DistrMPolyInlPP&);
template void MembershipProofManager::storeMultiplierRaw<
    CoCoA::DistrMPolyInlFpPP>(CoCoA::DistrMPolyInlFpPP&);

void MembershipProofManager::sPoly(CoCoA::ConstRefRingElem p,
                                   CoCoA::ConstRefRingElem q,
                                   CoCoA::ConstRefRingElem s)
{
  Node sNode = d_enc.decode(s);
  Trace("ff::proof") << "s: " << p << ", " << q << " -> " << s << std::endl;
  if (d_factToProof.count(sNode) == 0)
  {
    Trace("ff::proof") << " keep" << std::endl;
    Assert(d_multiplierSeq.size() == 2) << d_multiplierSeq.size();
    Node pNode = d_enc.decode(p);
    Node qNode = d_enc.decode(q);
    Node rs = nodeManager()->mkNode(Kind::SEXPR, {pNode, qNode});
    Node ms = nodeManager()->mkNode(
        Kind::SEXPR,
        {d_enc.decode(d_multiplierSeq[0]), d_enc.decode(d_multiplierSeq[1])});
    storeProof(sNode,
               ProofRule::MACRO_FF_POLY_COMBINATION,
               {pNode, qNode},
               {rs, ms, sNode});
  }
  else
  {
    Trace("ff::proof") << " drop" << std::endl;
  }
  d_multiplierSeq.clear();
}

void MembershipProofManager::reductionStart(CoCoA::ConstRefRingElem p)
{
  Assert(d_reductionSeq.empty());
  Trace("ff::proof") << "GB reduction proof start: " << d_enc.decode(p)
                     << std::endl;
  d_reductionSeq.push_back(p);
}

void MembershipProofManager::reductionStep(CoCoA::ConstRefRingElem q)
{
  // q is the reducer, which already has a membership proof
  Assert(!d_reductionSeq.empty());
  Trace("ff::proof") << "GB reduction proof step: " << d_enc.decode(q)
                     << std::endl;
  d_reductionSeq.push_back(q);
}

void MembershipProofManager::reductionEnd(CoCoA::ConstRefRingElem r)
{
  Assert(!d_reductionSeq.empty());
  Node rTerm = d_enc.decode(r);
  Trace("ff::proof") << "GB reduction proof end: " << rTerm << std::endl;
  if (d_factToProof.count(rTerm) == 0)
  {
    Trace("ff::proof") << " keep" << std::endl;
    std::vector<Node> reductors{};
    for (const CoCoA::RingElem& reductor : d_reductionSeq)
    {
      reductors.push_back(d_enc.decode(reductor));
    }
    // the polynomial being reduced is used with multiplier one
    std::vector<Node> multipliers{d_enc.one()};
    for (const CoCoA::RingElem& mul : d_multiplierSeq)
    {
      multipliers.push_back(d_enc.decode(mul));
    }
    Node rs = nodeManager()->mkNode(Kind::SEXPR, reductors);
    Node ms = nodeManager()->mkNode(Kind::SEXPR, multipliers);
    storeProof(rTerm,
               ProofRule::MACRO_FF_POLY_COMBINATION,
               reductors,
               {rs, ms, rTerm});
  }
  d_multiplierSeq.clear();
  d_reductionSeq.clear();
}

void MembershipProofManager::monicProof(CoCoA::ConstRefRingElem poly,
                                        CoCoA::ConstRefRingElem monic)
{
  Node polyTerm = d_enc.decode(poly);
  Node monicTerm = d_enc.decode(monic);
  CoCoA::RingElem lcInv = CoCoA::one(d_cocoaRing) / CoCoA::LC(poly);
  Node rs = nodeManager()->mkNode(Kind::SEXPR, polyTerm);
  Node ms = nodeManager()->mkNode(Kind::SEXPR, d_enc.decode(lcInv));
  Trace("ff::proof") << "monic: " << poly << " -> " << monic << std::endl;
  Assert(d_factToProof.count(polyTerm));
  storeProof(monicTerm,
             ProofRule::MACRO_FF_POLY_COMBINATION,
             {polyTerm},
             {rs, ms, monicTerm});
}

void MembershipProofManager::membershipStart(CoCoA::ConstRefRingElem p)
{
  Assert(d_membershipSeq.empty());
  d_reducingPoly = p;
  CoCoA::membershipTest = true;
  Trace("ff::proof") << "Starting membership proof with: " << p << std::endl;
}

void MembershipProofManager::membershipStep(CoCoA::RingElem red)
{
  Trace("ff::proof") << "Membership step done" << std::endl;
  d_membershipSeq.push_back(red);
}

void MembershipProofManager::membershipEnd()
{
  CoCoA::membershipTest = false;
  Assert(!d_membershipSeq.empty());
  std::vector<Node> reductors{};
  for (const CoCoA::RingElem& reductor : d_membershipSeq)
  {
    reductors.push_back(d_enc.decode(reductor));
  }
  std::vector<Node> multipliers{};
  for (const CoCoA::RingElem& mul : d_multiplierSeq)
  {
    multipliers.push_back(d_enc.decode(mul));
  }
  Node rs = nodeManager()->mkNode(Kind::SEXPR, reductors);
  Node ms = nodeManager()->mkNode(Kind::SEXPR, multipliers);
  Node reducingPolyNode = d_enc.decode(d_reducingPoly);
  storeProof(reducingPolyNode,
             ProofRule::MACRO_FF_POLY_COMBINATION,
             reductors,
             {rs, ms, reducingPolyNode});
  d_multiplierSeq.clear();
  d_membershipSeq.clear();
  Trace("ff::proof") << "Finished membership proof for " << d_reducingPoly
                     << std::endl;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
