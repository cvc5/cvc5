/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Trust substitutions.
 */

#include "theory/trust_substitutions.h"

#include "smt/env.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace theory {

TrustSubstitutionMap::TrustSubstitutionMap(Env& env,
                                           context::Context* c,
                                           std::string name,
                                           PfRule trustId,
                                           MethodId ids)
    : EnvObj(env),
      d_ctx(c),
      d_subs(c),
      d_tsubs(c),
      d_tspb(nullptr),
      d_subsPg(nullptr),
      d_applyPg(nullptr),
      d_helperPf(nullptr),
      d_name(name),
      d_trustId(trustId),
      d_ids(ids),
      d_eqtIndex(c)
{
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  if (pnm != nullptr)
  {
    d_tspb.reset(new TheoryProofStepBuffer(pnm->getChecker()));
    d_subsPg.reset(
        new LazyCDProof(env, nullptr, d_ctx, "TrustSubstitutionMap::subsPg"));
    d_applyPg.reset(
        new LazyCDProof(env, nullptr, d_ctx, "TrustSubstitutionMap::applyPg"));
    d_helperPf.reset(new CDProofSet<LazyCDProof>(env, d_ctx));
  }
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
    // add to lazy proof
    d_subsPg->addLazyStep(tnl.getProven(), pg, d_trustId);
  }
}

void TrustSubstitutionMap::addSubstitution(TNode x,
                                           TNode t,
                                           PfRule id,
                                           const std::vector<Node>& children,
                                           const std::vector<Node>& args)
{
  if (!isProofEnabled())
  {
    addSubstitution(x, t, nullptr);
    return;
  }
  LazyCDProof* stepPg = d_helperPf->allocateProof(nullptr, d_ctx);
  Node eq = x.eqNode(t);
  stepPg->addStep(eq, id, children, args);
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
  LazyCDProof* solvePg = d_helperPf->allocateProof(nullptr, d_ctx);
  // Try to transform tn.getProven() to (= x t) here, if necessary
  if (!d_tspb->applyPredTransform(proven, eq, {}))
  {
    // failed to rewrite, we add a trust step which assumes eq is provable
    // from proven, and proceed as normal.
    Trace("trust-subs") << "...failed to rewrite " << proven << std::endl;
    d_tspb->addStep(PfRule::TRUST_SUBS_EQ, {proven}, {eq}, eq);
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

TrustNode TrustSubstitutionMap::applyTrusted(Node n, Rewriter* r)
{
  Trace("trust-subs") << "TrustSubstitutionMap::addSubstitution: apply " << n
                      << std::endl;
  Node ns = d_subs.apply(n, r);
  Trace("trust-subs") << "...subs " << ns << std::endl;
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
  Node eq = n.eqNode(ns);
  // If we haven't already stored an index, remember the index. Otherwise, a
  // (possibly shorter) prefix of the substitution already suffices to show eq
  if (d_eqtIndex.find(eq) == d_eqtIndex.end())
  {
    d_eqtIndex[eq] = d_tsubs.size();
  }
  // this class will provide a proof if asked
  return TrustNode::mkTrustRewrite(n, ns, this);
}

Node TrustSubstitutionMap::apply(Node n, Rewriter* r)
{
  return d_subs.apply(n, r);
}

std::shared_ptr<ProofNode> TrustSubstitutionMap::getProofFor(Node eq)
{
  Assert(eq.getKind() == kind::EQUAL);
  Node n = eq[0];
  Node ns = eq[1];
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
  if (d_subsPg->hasStep(eq) || d_subsPg->hasGenerator(eq))
  {
    return d_subsPg->getProofFor(eq);
  }
  Trace("trust-subs-pf") << "getProofFor " << eq << std::endl;
  AlwaysAssert(d_proving.find(eq) == d_proving.end())
      << "Repeat getProofFor in TrustSubstitutionMap " << eq;
  d_proving.insert(eq);
  NodeUIntMap::iterator it = d_eqtIndex.find(eq);
  Assert(it != d_eqtIndex.end());
  Trace("trust-subs-pf") << "TrustSubstitutionMap::getProofFor, # assumptions= "
                         << it->second << std::endl;
  Node cs = getSubstitution(it->second);
  Trace("trust-subs-pf") << "getProofFor substitution is " << cs << std::endl;
  Assert(eq != cs);
  std::vector<Node> pfChildren;
  if (!cs.isConst())
  {
    // note that cs may be an AND node, in which case it specifies multiple
    // substitutions
    pfChildren.push_back(cs);
    // connect substitution generator into apply generator
    d_applyPg->addLazyStep(cs, d_subsPg.get());
  }
  Trace("trust-subs-pf") << "...apply eq intro" << std::endl;
  // We use fixpoint as the substitution-apply identifier. Notice that it
  // suffices to use SBA_SEQUENTIAL here, but SBA_FIXPOINT is typically
  // more efficient. This is because for substitution of size n, sequential
  // substitution can either be implemented as n traversals of the term to
  // apply the substitution to, or a single traversal of the term, but n^2/2
  // traversals of the range of the substitution to prepare a simultaneous
  // substitution. Both of these options are inefficient. Note that we
  // expect this rule to succeed, so useExpected is set to true.
  if (!d_tspb->applyEqIntro(n,
                            ns,
                            pfChildren,
                            d_ids,
                            MethodId::SBA_FIXPOINT,
                            MethodId::RW_REWRITE,
                            true))
  {
    // if we fail for any reason, we must use a trusted step instead
    d_tspb->addStep(PfRule::TRUST_SUBS_MAP, pfChildren, {eq}, eq);
  }
  Trace("trust-subs-pf") << "...made steps" << std::endl;
  // -------        ------- from external proof generators
  // x1 = t1 ...    xn = tn
  // ----------------------- AND_INTRO
  //   ...
  // --------- MACRO_SR_EQ_INTRO (or TRUST_SUBS_MAP if we failed above)
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
  Trace("trust-subs-pf") << "...finish, make proof" << std::endl;
  std::shared_ptr<ProofNode> ret = d_applyPg->getProofFor(eq);
  d_proving.erase(eq);
  return ret;
}

std::string TrustSubstitutionMap::identify() const { return d_name; }

SubstitutionMap& TrustSubstitutionMap::get() { return d_subs; }

bool TrustSubstitutionMap::isProofEnabled() const
{
  return d_subsPg != nullptr;
}

Node TrustSubstitutionMap::getSubstitution(size_t index)
{
  Assert(index <= d_tsubs.size());
  std::vector<Node> csubsChildren;
  for (size_t i = 0; i < index; i++)
  {
    csubsChildren.push_back(d_tsubs[i].getProven());
  }
  std::reverse(csubsChildren.begin(), csubsChildren.end());
  Node cs = NodeManager::currentNM()->mkAnd(csubsChildren);
  if (cs.getKind() == kind::AND)
  {
    d_subsPg->addStep(cs, PfRule::AND_INTRO, csubsChildren, {});
  }
  return cs;
}

}  // namespace theory
}  // namespace cvc5::internal
