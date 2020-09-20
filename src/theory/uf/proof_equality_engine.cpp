/*********************                                                        */
/*! \file proof_equality_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the proof-producing equality engine
 **/

#include "theory/uf/proof_equality_engine.h"

#include "theory/rewriter.h"
#include "theory/uf/proof_checker.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace eq {

ProofEqEngine::ProofEqEngine(context::Context* c,
                             context::UserContext* u,
                             EqualityEngine& ee,
                             ProofNodeManager* pnm)
    : EagerProofGenerator(pnm, u, "pfee::" + ee.identify()),
      d_ee(ee),
      d_factPg(c, pnm),
      d_pnm(pnm),
      d_proof(pnm, nullptr, c, "pfee::LazyCDProof::" + ee.identify()),
      d_keep(c)
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
  AlwaysAssert(pnm != nullptr)
      << "Should not construct ProofEqEngine without proof node manager";
}

bool ProofEqEngine::assertFact(Node lit,
                               PfRule id,
                               const std::vector<Node>& exp,
                               const std::vector<Node>& args)
{
  Trace("pfee") << "pfee::assertFact " << lit << " " << id << ", exp = " << exp
                << ", args = " << args << std::endl;

  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;
  // register the step in the proof
  if (holds(atom, polarity))
  {
    // we do not process this fact if it already holds
    return false;
  }
  // Buffer the step in the fact proof generator. We do this instead of
  // adding explict steps to the lazy proof d_proof since CDProof has
  // (at most) one proof for each formula. Thus, we "claim" only the
  // formula that is proved by this fact. Otherwise, aliasing may occur,
  // which leads to cyclic or bogus proofs.
  ProofStep ps;
  ps.d_rule = id;
  ps.d_children = exp;
  ps.d_args = args;
  d_factPg.addStep(lit, ps);
  // add lazy step to proof
  d_proof.addLazyStep(lit, &d_factPg, false);
  // second, assert it to the equality engine
  Node reason = NodeManager::currentNM()->mkAnd(exp);
  return assertFactInternal(atom, polarity, reason);
}

bool ProofEqEngine::assertFact(Node lit,
                               PfRule id,
                               Node exp,
                               const std::vector<Node>& args)
{
  Trace("pfee") << "pfee::assertFact " << lit << " " << id << ", exp = " << exp
                << ", args = " << args << std::endl;
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;
  // register the step in the proof
  if (holds(atom, polarity))
  {
    // we do not process this fact if it already holds
    return false;
  }
  // must extract the explanation as a vector
  std::vector<Node> expv;
  // Flatten (single occurrences) of AND. We do not allow nested AND, it is
  // the responsibilty of the caller to ensure these do not occur.
  if (exp != d_true)
  {
    if (exp.getKind() == AND)
    {
      for (const Node& expc : exp)
      {
        // should not have doubly nested AND
        Assert(expc.getKind() != AND);
        expv.push_back(expc);
      }
    }
    else
    {
      expv.push_back(exp);
    }
  }
  // buffer the step in the fact proof generator
  ProofStep ps;
  ps.d_rule = id;
  ps.d_children = expv;
  ps.d_args = args;
  d_factPg.addStep(lit, ps);
  // add lazy step to proof
  d_proof.addLazyStep(lit, &d_factPg, false);
  // second, assert it to the equality engine
  return assertFactInternal(atom, polarity, exp);
}

bool ProofEqEngine::assertFact(Node lit, Node exp, ProofStepBuffer& psb)
{
  Trace("pfee") << "pfee::assertFact " << lit << ", exp = " << exp
                << " via buffer with " << psb.getNumSteps() << " steps"
                << std::endl;
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;
  if (holds(atom, polarity))
  {
    // we do not process this fact if it already holds
    return false;
  }
  // buffer the steps in the fact proof generator
  const std::vector<std::pair<Node, ProofStep>>& steps = psb.getSteps();
  for (const std::pair<Node, ProofStep>& step : steps)
  {
    d_factPg.addStep(step.first, step.second);
  }
  // add lazy step to proof
  d_proof.addLazyStep(lit, &d_factPg, false);
  // second, assert it to the equality engine
  return assertFactInternal(atom, polarity, exp);
}

bool ProofEqEngine::assertFact(Node lit, Node exp, ProofGenerator* pg)
{
  Trace("pfee") << "pfee::assertFact " << lit << ", exp = " << exp
                << " via generator" << std::endl;
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;
  if (holds(atom, polarity))
  {
    // we do not process this fact if it already holds
    return false;
  }
  // note the proof generator is responsible for remembering the explanation
  d_proof.addLazyStep(lit, pg, false);
  // second, assert it to the equality engine
  return assertFactInternal(atom, polarity, exp);
}

TrustNode ProofEqEngine::assertConflict(Node lit)
{
  Trace("pfee") << "pfee::assertConflict " << lit << std::endl;
  std::vector<TNode> assumps;
  explainWithProof(lit, assumps, &d_proof);
  // lit may not be equivalent to false, but should rewrite to false
  if (lit != d_false)
  {
    Assert(Rewriter::rewrite(lit) == d_false)
        << "pfee::assertConflict: conflict literal is not rewritable to "
           "false";
    std::vector<Node> exp;
    exp.push_back(lit);
    std::vector<Node> args;
    if (!d_proof.addStep(d_false, PfRule::MACRO_SR_PRED_ELIM, exp, args))
    {
      Assert(false) << "pfee::assertConflict: failed conflict step";
      return TrustNode::null();
    }
  }
  return ensureProofForFact(
      d_false, assumps, TrustNodeKind::CONFLICT, &d_proof);
}

TrustNode ProofEqEngine::assertConflict(PfRule id,
                                        const std::vector<Node>& exp,
                                        const std::vector<Node>& args)
{
  Trace("pfee") << "pfee::assertConflict " << id << ", exp = " << exp
                << ", args = " << args << std::endl;
  // conflict is same as lemma concluding false
  return assertLemma(d_false, id, exp, {}, args);
}

TrustNode ProofEqEngine::assertConflict(const std::vector<Node>& exp,
                                        ProofStepBuffer& psb)
{
  Trace("pfee") << "pfee::assertConflict " << exp << " via buffer with "
                << psb.getNumSteps() << " steps" << std::endl;
  return assertLemma(d_false, exp, {}, psb);
}

TrustNode ProofEqEngine::assertConflict(const std::vector<Node>& exp,
                                        ProofGenerator* pg)
{
  Assert(pg != nullptr);
  Trace("pfee") << "pfee::assertConflict " << exp << " via generator"
                << std::endl;
  return assertLemma(d_false, exp, {}, pg);
}

TrustNode ProofEqEngine::assertLemma(Node conc,
                                     PfRule id,
                                     const std::vector<Node>& exp,
                                     const std::vector<Node>& noExplain,
                                     const std::vector<Node>& args)
{
  Trace("pfee") << "pfee::assertLemma " << conc << " " << id
                << ", exp = " << exp << ", noExplain = " << noExplain
                << ", args = " << args << std::endl;
  Assert(conc != d_true);
  LazyCDProof tmpProof(d_pnm, &d_proof);
  LazyCDProof* curr;
  if (conc == d_false)
  {
    // optimization: we can use the main lazy proof directly, because we
    // know we will backtrack immediately after this call.
    curr = &d_proof;
  }
  else
  {
    // use a lazy proof that always links to d_proof
    curr = &tmpProof;
  }
  // Register the proof step.
  if (!curr->addStep(conc, id, exp, args))
  {
    // a step went wrong, e.g. during checking
    Assert(false) << "pfee::assertConflict: register proof step";
    return TrustNode::null();
  }
  // We've now decided which lazy proof to use (curr), now get the proof
  // for conc.
  return assertLemmaInternal(conc, exp, noExplain, curr);
}

TrustNode ProofEqEngine::assertLemma(Node conc,
                                     const std::vector<Node>& exp,
                                     const std::vector<Node>& noExplain,
                                     ProofStepBuffer& psb)
{
  Trace("pfee") << "pfee::assertLemma " << conc << ", exp = " << exp
                << ", noExplain = " << noExplain << " via buffer with "
                << psb.getNumSteps() << " steps" << std::endl;
  LazyCDProof tmpProof(d_pnm, &d_proof);
  LazyCDProof* curr;
  // same policy as above: for conflicts, use existing lazy proof
  if (conc == d_false)
  {
    curr = &d_proof;
  }
  else
  {
    curr = &tmpProof;
  }
  // add all steps to the proof
  const std::vector<std::pair<Node, ProofStep>>& steps = psb.getSteps();
  for (const std::pair<Node, ProofStep>& ps : steps)
  {
    if (!curr->addStep(ps.first, ps.second))
    {
      return TrustNode::null();
    }
  }
  return assertLemmaInternal(conc, exp, noExplain, curr);
}

TrustNode ProofEqEngine::assertLemma(Node conc,
                                     const std::vector<Node>& exp,
                                     const std::vector<Node>& noExplain,
                                     ProofGenerator* pg)
{
  Assert(pg != nullptr);
  Trace("pfee") << "pfee::assertLemma " << conc << ", exp = " << exp
                << ", noExplain = " << noExplain << " via generator"
                << std::endl;
  LazyCDProof tmpProof(d_pnm, &d_proof);
  LazyCDProof* curr;
  // same policy as above: for conflicts, use existing lazy proof
  if (conc == d_false)
  {
    curr = &d_proof;
  }
  else
  {
    curr = &tmpProof;
  }
  // Register the proof. Notice we do a deep copy here because the CDProof
  // curr should take ownership of the proof steps that pg provided for conc.
  // In other words, this sets up the "skeleton" of proof that is the base
  // of the proof we are constructing. The call to assertLemmaInternal below
  // will expand the leaves of this proof. If we used a shallow copy, then
  // the connection to these leaves would be lost since they would not be
  // owned by curr.
  if (!pg->addProofTo(conc, curr, CDPOverwrite::ASSUME_ONLY, true))
  {
    // a step went wrong, e.g. during checking
    Assert(false) << "pfee::assertConflict: register proof step";
    return TrustNode::null();
  }
  return assertLemmaInternal(conc, exp, noExplain, curr);
}

TrustNode ProofEqEngine::explain(Node conc)
{
  Trace("pfee") << "pfee::explain " << conc << std::endl;
  LazyCDProof tmpProof(d_pnm, &d_proof);
  std::vector<TNode> assumps;
  explainWithProof(conc, assumps, &tmpProof);
  return ensureProofForFact(conc, assumps, TrustNodeKind::PROP_EXP, &tmpProof);
}

TrustNode ProofEqEngine::assertLemmaInternal(Node conc,
                                             const std::vector<Node>& exp,
                                             const std::vector<Node>& noExplain,
                                             LazyCDProof* curr)
{
  // We are a conflict if the conclusion is false and all literals are
  // explained.
  TrustNodeKind tnk =
      conc == d_false ? TrustNodeKind::CONFLICT : TrustNodeKind::LEMMA;

  // get the explanation, with proofs
  std::vector<TNode> assumps;
  std::vector<Node> expn;
  for (const Node& e : exp)
  {
    if (std::find(noExplain.begin(), noExplain.end(), e) == noExplain.end())
    {
      explainWithProof(e, assumps, curr);
    }
    else
    {
      // it did not have a proof; it was an assumption of the previous rule
      assumps.push_back(e);
      // it is not a conflict, since it may involve new literals
      tnk = TrustNodeKind::LEMMA;
    }
  }
  return ensureProofForFact(conc, assumps, tnk, curr);
}

TrustNode ProofEqEngine::ensureProofForFact(Node conc,
                                            const std::vector<TNode>& assumps,
                                            TrustNodeKind tnk,
                                            LazyCDProof* curr)
{
  Trace("pfee-proof") << std::endl;
  Trace("pfee-proof") << "pfee::ensureProofForFact: input " << conc << " via "
                      << assumps << ", TrustNodeKind=" << tnk << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  // The proof
  std::shared_ptr<ProofNode> pf;
  ProofGenerator* pfg = nullptr;
  // the explanation is the conjunction of assumptions
  Node exp;
  // If proofs are enabled, generate the proof and possibly modify the
  // assumptions to match SCOPE.
  Assert(curr != nullptr);
  Trace("pfee-proof") << "pfee::ensureProofForFact: make proof for fact"
                      << std::endl;
  // get the proof for conc
  std::shared_ptr<ProofNode> pfBody = curr->getProofFor(conc);
  if (pfBody == nullptr)
  {
    Trace("pfee-proof")
        << "pfee::ensureProofForFact: failed to make proof for fact"
        << std::endl
        << std::endl;
    // should have existed
    Assert(false) << "pfee::assertConflict: failed to get proof for " << conc;
    return TrustNode::null();
  }
  // clone it so that we have a fresh copy
  pfBody = pfBody->clone();
  Trace("pfee-proof") << "pfee::ensureProofForFact: add scope" << std::endl;
  // The free assumptions must be closed by assumps, which should be passed
  // as arguments of SCOPE. However, some of the free assumptions may not
  // literally be equal to assumps, for instance, due to symmetry. In other
  // words, the SCOPE could be closing (= x y) in a proof with free
  // assumption (= y x). We modify the proof leaves to account for this
  // below.

  std::vector<Node> scopeAssumps;
  // we first ensure the assumptions are flattened
  for (const TNode& a : assumps)
  {
    if (a.getKind() == AND)
    {
      scopeAssumps.insert(scopeAssumps.end(), a.begin(), a.end());
    }
    else
    {
      scopeAssumps.push_back(a);
    }
  }
  // scope the proof constructed above, and connect the formula with the proof
  // minimize the assumptions
  pf = d_pnm->mkScope(pfBody, scopeAssumps, true, true);
  exp = nm->mkAnd(scopeAssumps);
  // Make the lemma or conflict node. This must exactly match the conclusion
  // of SCOPE below.
  Node formula;
  if (tnk == TrustNodeKind::CONFLICT)
  {
    // conflict is negated
    Assert(conc == d_false);
    formula = exp;
  }
  else
  {
    formula =
        exp == d_true
            ? conc
            : (conc == d_false ? exp.negate() : nm->mkNode(IMPLIES, exp, conc));
  }
  Trace("pfee-proof") << "pfee::ensureProofForFact: formula is " << formula
                      << std::endl;
  // should always be non-null
  Assert(pf != nullptr);
  if (Trace.isOn("pfee-proof") || Trace.isOn("pfee-proof-final"))
  {
    Trace("pfee-proof") << "pfee::ensureProofForFact: printing proof"
                        << std::endl;
    std::stringstream ss;
    pf->printDebug(ss);
    Trace("pfee-proof") << "pfee::ensureProofForFact: Proof is " << ss.str()
                        << std::endl;
  }
  // Should be a closed proof now. If it is not, then the overall proof
  // is malformed.
  Assert(pf->isClosed());
  pfg = this;
  // set the proof for the conflict or lemma, which can be queried later
  switch (tnk)
  {
    case TrustNodeKind::CONFLICT: setProofForConflict(formula, pf); break;
    case TrustNodeKind::LEMMA: setProofForLemma(formula, pf); break;
    case TrustNodeKind::PROP_EXP: setProofForPropExp(conc, exp, pf); break;
    default:
      pfg = nullptr;
      Unhandled() << "Unhandled trust node kind " << tnk;
      break;
  }
  Trace("pfee-proof") << "pfee::ensureProofForFact: finish" << std::endl
                      << std::endl;
  // we can provide a proof for conflict, lemma or explained propagation
  switch (tnk)
  {
    case TrustNodeKind::CONFLICT:
      return TrustNode::mkTrustConflict(formula, pfg);
    case TrustNodeKind::LEMMA: return TrustNode::mkTrustLemma(formula, pfg);
    case TrustNodeKind::PROP_EXP:
      return TrustNode::mkTrustPropExp(conc, exp, pfg);
    default: Unhandled() << "Unhandled trust node kind " << tnk; break;
  }
  return TrustNode::null();
}

bool ProofEqEngine::assertFactInternal(TNode atom, bool polarity, TNode reason)
{
  Trace("pfee-debug") << "pfee::assertFactInternal: " << atom << " " << polarity
                      << " " << reason << std::endl;
  bool ret;
  if (atom.getKind() == EQUAL)
  {
    ret = d_ee.assertEquality(atom, polarity, reason);
  }
  else
  {
    ret = d_ee.assertPredicate(atom, polarity, reason);
  }
  if (ret)
  {
    // must reference count the new atom and explanation
    d_keep.insert(atom);
    d_keep.insert(reason);
  }
  return ret;
}

bool ProofEqEngine::holds(TNode atom, bool polarity)
{
  if (atom.getKind() == EQUAL)
  {
    if (!d_ee.hasTerm(atom[0]) || !d_ee.hasTerm(atom[1]))
    {
      return false;
    }
    return polarity ? d_ee.areEqual(atom[0], atom[1])
                    : d_ee.areDisequal(atom[0], atom[1], false);
  }
  if (!d_ee.hasTerm(atom))
  {
    return false;
  }
  TNode b = polarity ? d_true : d_false;
  return d_ee.areEqual(atom, b);
}

void ProofEqEngine::explainWithProof(Node lit,
                                     std::vector<TNode>& assumps,
                                     LazyCDProof* curr)
{
  if (std::find(assumps.begin(), assumps.end(), lit) != assumps.end())
  {
    return;
  }
  std::shared_ptr<eq::EqProof> pf = std::make_shared<eq::EqProof>();
  Trace("pfee-proof") << "pfee::explainWithProof: " << lit << std::endl;
  bool polarity = lit.getKind() != NOT;
  TNode atom = polarity ? lit : lit[0];
  Assert(atom.getKind() != AND);
  std::vector<TNode> tassumps;
  if (atom.getKind() == EQUAL)
  {
    if (atom[0] == atom[1])
    {
      return;
    }
    Assert(d_ee.hasTerm(atom[0]));
    Assert(d_ee.hasTerm(atom[1]));
    if (!polarity)
    {
      // ensure the explanation exists
      AlwaysAssert(d_ee.areDisequal(atom[0], atom[1], true));
    }
    d_ee.explainEquality(atom[0], atom[1], polarity, tassumps, pf.get());
  }
  else
  {
    Assert(d_ee.hasTerm(atom));
    d_ee.explainPredicate(atom, polarity, tassumps, pf.get());
  }
  Trace("pfee-proof") << "...got " << tassumps << std::endl;
  // avoid duplicates
  for (const TNode a : tassumps)
  {
    if (a == lit)
    {
      assumps.push_back(a);
    }
    else if (std::find(assumps.begin(), assumps.end(), a) == assumps.end())
    {
      assumps.push_back(a);
    }
  }
  if (Trace.isOn("pfee-proof"))
  {
    Trace("pfee-proof") << "pfee::explainWithProof: add to proof ---"
                        << std::endl;
    std::stringstream sse;
    pf->debug_print(sse);
    Trace("pfee-proof") << sse.str() << std::endl;
    Trace("pfee-proof") << "---" << std::endl;
  }
  // add the steps in the equality engine proof to the Proof
  pf->addToProof(curr);
  Trace("pfee-proof") << "pfee::explainWithProof: finished" << std::endl;
}

}  // namespace eq
}  // namespace theory
}  // namespace CVC4
