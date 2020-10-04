/*********************                                                        */
/*! \file trust_substitutions.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Trust substitutions
 **/

#include "theory/trust_substitutions.h"

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {

TrustSubstitutionMap::TrustSubstitutionMap(context::Context* c,
                                           ProofNodeManager* pnm)
    : d_subs(c),
      d_tsubs(c),
      d_tspb(pnm ? new TheoryProofStepBuffer(pnm->getChecker()) : nullptr),
      d_subsPg(
          pnm ? new LazyCDProof(pnm, nullptr, c, "TrustSubstitutionMap::subsPg")
              : nullptr),
      d_applyPg(pnm ? new EagerProofGenerator(pnm, c) : nullptr),
      d_currentSubs(c)
{
}

void TrustSubstitutionMap::addSubstitution(TNode x, TNode t, ProofGenerator* pg)
{
  Trace("trust-subs") << "TrustSubstitutionMap::addSubstitution: add " << x << " -> " << t << std::endl;
  d_subs.addSubstitution(x, t);
  if (isProofEnabled())
  {
    TrustNode tnl = TrustNode::mkTrustRewrite(x, t, pg);
    d_tsubs.push_back(tnl);
    // current substitution node is no longer valid.
    d_currentSubs = Node::null();
    // add to lazy proof
    d_subsPg->addLazyStep(tnl.getProven(), pg, false, "TrustSubstitutionMap::addSubstitution", false, PfRule::TRUST);
  }
}

void TrustSubstitutionMap::addSubstitutions(TrustSubstitutionMap& t)
{
  if (!isProofEnabled())
  {
    d_subs.addSubstitutions(t.get());
    return;
  }
  // append trust node list
  for (const TrustNode& tns : t.d_tsubs)
  {
    Node proven = tns.getProven();
    addSubstitution(proven[0], proven[1],
  }
}

TrustNode TrustSubstitutionMap::apply(Node n, bool doRewrite)
{
  Trace("trust-subs") << "TrustSubstitutionMap::addSubstitution: apply " << n << std::endl;
  Node ns = d_subs.apply(n);
  Trace("trust-subs") << "...subs " << ns << std::endl;
  if (doRewrite)
  {
    ns = Rewriter::rewrite(ns);
    Trace("trust-subs") << "...rewrite " << ns << std::endl;
  }
  if (!isProofEnabled())
  {
    return TrustNode::mkTrustRewrite(n, ns, nullptr);
  }
  // proof is a single application of MACRO_SR_PRED_TRANSFORM
  Node cs = getCurrentSubstitution();
  Trace("trust-subs") << "TrustSubstitutionMap::addSubstitution: current substitution is " << cs << std::endl;
  std::vector<Node> pfChildren;
  if (!cs.isConst())
  {
    pfChildren.push_back(cs);
  }
  if (!d_tspb->applyEqIntro(n, ns, pfChildren))
  {
    Assert(false) << "TrustSubstitutionMap::addSubstitution: failed to apply substitution";
    return TrustNode::mkTrustRewrite(n, ns, nullptr);
  }
  return TrustNode::mkTrustRewrite(n, ns, nullptr);
}

SubstitutionMap& TrustSubstitutionMap::get() { return d_subs; }

bool TrustSubstitutionMap::isProofEnabled() const
{
  return d_subsPg != nullptr;
}

Node TrustSubstitutionMap::getCurrentSubstitution()
{
  Assert (isProofEnabled());
  if (!d_currentSubs.get().isNull())
  {
    return d_currentSubs;
  }
  std::vector<Node> csubsChildren;
  for (const TrustNode& tns : d_tsubs)
  {
    csubsChildren.push_back(tns.getProven());
  }
  d_currentSubs = NodeManager::currentNM()->mkAnd(csubsChildren);
  return d_currentSubs;
}

}  // namespace theory
}  // namespace CVC4
