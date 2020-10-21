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
                                           ProofNodeManager* pnm,
                                           std::string name,
                                           PfRule trustId,
                                           MethodId ids)
    : d_subs(c),
      d_pnm(pnm),
      d_tsubs(c),
      d_tspb(pnm ? new TheoryProofStepBuffer(pnm->getChecker()) : nullptr),
      d_subsPg(
          pnm ? new LazyCDProof(pnm, nullptr, c, "TrustSubstitutionMap::subsPg")
              : nullptr),
      d_applyPg(pnm ? new LazyCDProof(
                          pnm, nullptr, c, "TrustSubstitutionMap::applyPg")
                    : nullptr),
      d_helperPf(pnm, c),
      d_currentSubs(c),
      d_name(name),
      d_trustId(trustId),
      d_ids(ids)
{
}

void TrustSubstitutionMap::addSubstitution(TNode x, TNode t, ProofGenerator* pg)
{
  Trace("trust-subs") << "TrustSubstitutionMap::addSubstitution: add " << x
                      << " -> " << t << std::endl;
  d_subs.addSubstitution(x, t);
  if (isProofEnabled())
  {
    TrustNode tnl = TrustNode::mkTrustRewrite(x, t, pg);
    d_tsubs.push_back(tnl);
    // current substitution node is no longer valid.
    d_currentSubs = Node::null();
    // add to lazy proof
    d_subsPg->addLazyStep(tnl.getProven(), pg, d_trustId);
  }
}

void TrustSubstitutionMap::addSubstitution(TNode x,
                                           TNode t,
                                           PfRule id,
                                           const std::vector<Node>& args)
{
  if (!isProofEnabled())
  {
    addSubstitution(x, t, nullptr);
    return;
  }
  LazyCDProof* stepPg = d_helperPf.allocateProof();
  Node eq = x.eqNode(t);
  stepPg->addStep(eq, id, {}, args);
  addSubstitution(x, t, stepPg);
}

ProofGenerator* TrustSubstitutionMap::addSubstitutionSolved(TNode x,
                                                            TNode t,
                                                            TrustNode tn)
{
  Trace("trust-subs") << "TrustSubstitutionMap::addSubstitutionSolved: add "
                      << x << " -> " << t << " from " << tn.getProven()
                      << std::endl;
  if (!isProofEnabled() || tn.getGenerator() == nullptr)
  {
    // no generator or not proof enabled, nothing to do
    addSubstitution(x, t, nullptr);
    Trace("trust-subs") << "...no proof" << std::endl;
    return nullptr;
  }
  Node eq = x.eqNode(t);
  Node proven = tn.getProven();
  // notice that this checks syntactic equality, not CDProof::isSame since
  // tn.getGenerator() is not necessarily robust to symmetry.
  if (eq == proven)
  {
    // no rewrite required, just use the generator
    addSubstitution(x, t, tn.getGenerator());
    Trace("trust-subs") << "...use generator directly" << std::endl;
    return tn.getGenerator();
  }
  LazyCDProof* solvePg = d_helperPf.allocateProof();
  // Try to transform tn.getProven() to (= x t) here, if necessary
  if (!d_tspb->applyPredTransform(proven, eq, {}))
  {
    // failed to rewrite
    addSubstitution(x, t, nullptr);
    Trace("trust-subs") << "...failed to rewrite" << std::endl;
    return nullptr;
  }
  Trace("trust-subs") << "...successful rewrite" << std::endl;
  solvePg->addSteps(*d_tspb.get());
  d_tspb->clear();
  // link the given generator
  solvePg->addLazyStep(proven, tn.getGenerator());
  addSubstitution(x, t, solvePg);
  return solvePg;
}

void TrustSubstitutionMap::addSubstitutions(TrustSubstitutionMap& t)
{
  if (!isProofEnabled())
  {
    // just use the basic utility
    d_subs.addSubstitutions(t.get());
    return;
  }
  // call addSubstitution above in sequence
  for (const TrustNode& tns : t.d_tsubs)
  {
    Node proven = tns.getProven();
    addSubstitution(proven[0], proven[1], tns.getGenerator());
  }
}

TrustNode TrustSubstitutionMap::apply(Node n, bool doRewrite)
{
  Trace("trust-subs") << "TrustSubstitutionMap::addSubstitution: apply " << n
                      << std::endl;
  Node ns = d_subs.apply(n);
  Trace("trust-subs") << "...subs " << ns << std::endl;
  // rewrite if indicated
  if (doRewrite)
  {
    ns = Rewriter::rewrite(ns);
    Trace("trust-subs") << "...rewrite " << ns << std::endl;
  }
  if (n == ns)
  {
    // no change
    return TrustNode::null();
  }
  if (!isProofEnabled())
  {
    // no proofs, use null generator
    return TrustNode::mkTrustRewrite(n, ns, nullptr);
  }
  Node cs = getCurrentSubstitution();
  Trace("trust-subs")
      << "TrustSubstitutionMap::addSubstitution: current substitution is " << cs
      << std::endl;
  // Easy case: if n is in the domain of the substitution, maybe it is already
  // a proof in the substitution proof generator. This is moreover required
  // to avoid cyclic proofs below. For example, if { x -> 5 } is a substitution,
  // and we are asked to transform x, resulting in 5, we hence must provide
  // a proof of (= x 5) based on the substitution. However, it must be the
  // case that (= x 5) is a proven fact of the substitution generator. Hence
  // we avoid a proof that looks like:
  // ---------- from d_subsPg
  // (= x 5)
  // ---------- MACRO_SR_EQ_INTRO{x}
  // (= x 5)
  // by taking the premise proof directly.
  Node eq = n.eqNode(ns);
  if (d_subsPg->hasStep(eq) || d_subsPg->hasGenerator(eq))
  {
    return TrustNode::mkTrustRewrite(n, ns, d_subsPg.get());
  }
  Assert(eq != cs);
  std::vector<Node> pfChildren;
  if (!cs.isConst())
  {
    // note we will get more proof reuse if we do not special case AND here.
    if (cs.getKind() == kind::AND)
    {
      for (const Node& csc : cs)
      {
        pfChildren.push_back(csc);
        // connect substitution generator into apply generator
        d_applyPg->addLazyStep(csc, d_subsPg.get());
      }
    }
    else
    {
      pfChildren.push_back(cs);
      // connect substitution generator into apply generator
      d_applyPg->addLazyStep(cs, d_subsPg.get());
    }
  }
  if (!d_tspb->applyEqIntro(n, ns, pfChildren, d_ids))
  {
    return TrustNode::mkTrustRewrite(n, ns, nullptr);
  }
  // -------        ------- from external proof generators
  // x1 = t1 ...    xn = tn
  // ----------------------- AND_INTRO
  //   ...
  // --------- MACRO_SR_EQ_INTRO
  // n == ns
  // add it to the apply proof generator.
  //
  // Notice that we use a single child to MACRO_SR_EQ_INTRO here. This is an
  // optimization motivated by the fact that n may be large and reused many
  // time. For instance, if this class is being used to track substitutions
  // derived during non-clausal simplification during preprocessing, it is
  // a fixed (possibly) large substitution applied to many terms. Having
  // a single child saves us from creating many proofs with n children, where
  // notice this proof is reused.
  d_applyPg->addSteps(*d_tspb.get());
  d_tspb->clear();
  return TrustNode::mkTrustRewrite(n, ns, d_applyPg.get());
}

SubstitutionMap& TrustSubstitutionMap::get() { return d_subs; }

bool TrustSubstitutionMap::isProofEnabled() const
{
  return d_subsPg != nullptr;
}

Node TrustSubstitutionMap::getCurrentSubstitution()
{
  Assert(isProofEnabled());
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
  if (d_currentSubs.get().getKind() == kind::AND)
  {
    d_subsPg->addStep(d_currentSubs, PfRule::AND_INTRO, csubsChildren, {});
  }
  return d_currentSubs;
}

}  // namespace theory
}  // namespace CVC4
