/*********************                                                        */
/*! \file proof_equality_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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
                             ProofNodeManager* pnm,
                             bool pfEnabled,
                             bool recExplain
                            )
    : EagerProofGenerator(u, pnm),
      d_ee(ee),
      d_pnm(pnm),
      d_proof(pnm, c),
      d_keep(c),
      d_pfEnabled(pfEnabled),
      d_recExplain(recExplain)
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

bool ProofEqEngine::assertAssume(TNode lit)
{
  Trace("pfee") << "pfee::assertAssume " << lit << std::endl;
  // don't need to explicitly assume
/*
  if (d_pfEnabled)
  {
    // first, add the step in the proof
    std::vector<Node> exp;
    std::vector<Node> args;
    args.push_back(lit);
    if (!d_proof.addStep(lit, PfRule::ASSUME, exp, args))
    {
      // failed to add step
      return false;
    }
  }
*/
  TNode atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;

  // Second, assert it directly to the equality engine, where it is its own
  // explanation. Notice we do not reference count atom/lit.
  if (atom.getKind() == EQUAL)
  {
    d_ee.assertEquality(atom, polarity, lit);
  }
  else
  {
    d_ee.assertPredicate(atom, polarity, lit);
  }
  return true;
}

bool ProofEqEngine::assertFact(Node lit,
                               PfRule id,
                               const std::vector<Node>& exp,
                               const std::vector<Node>& args)
{
  Trace("pfee") << "pfee::assertFact " << lit << " " << id << ", exp = " << exp
                << ", args = " << args << std::endl;
  // first, register the step in the proof
  if (d_pfEnabled)// && d_recExplain)
  {
    if (!addProofStep(lit, id, exp, args))
    {
      return false;
    }
  }

  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;

  // second, assert it to the equality engine
  Node reason = mkAnd(exp);
  assertFactInternal(atom, polarity, reason);
  return true;
}

bool ProofEqEngine::assertFact(Node lit,
                               PfRule id,
                               Node exp,
                               const std::vector<Node>& args)
{
  Trace("pfee") << "pfee::assertFact " << lit << " " << id << ", exp = " << exp
                << ", args = " << args << std::endl;
  // first, register the step in the proof
  if (d_pfEnabled)// && d_recExplain)
  {
    // must extract the explanation as a vector
    std::vector<Node> expv;
    flattenAnd(exp, expv);
    if (!addProofStep(lit, id, expv, args))
    {
      // failed to register step
      return false;
    }
  }
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;

  // second, assert it to the equality engine
  assertFactInternal(atom, polarity, exp);
  return true;
}

bool ProofEqEngine::assertFact(Node lit, Node exp, ProofStepBuffer& psb)
{
  Trace("pfee") << "pfee::assertFact " << lit << ", exp = " << exp
                << " via buffer with " << psb.getNumSteps() << " steps"
                << std::endl;
  if (d_pfEnabled)// && d_recExplain)
  {
    if (!d_proof.addSteps(psb))
    {
      return false;
    }
  }
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;

  // second, assert it to the equality engine
  assertFactInternal(atom, polarity, exp);
  return true;
}

bool ProofEqEngine::assertFact(Node lit, Node exp, ProofGenerator* pg)
{
  Trace("pfee") << "pfee::assertFact " << lit << ", exp = " << exp
                << " via generator" << std::endl;
  if (d_pfEnabled)// && d_recExplain)
  {
    // note the proof generator is responsible for remembering the explanation
    d_proof.addLazyStep(lit, pg);
  }
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;
  // second, assert it to the equality engine
  assertFactInternal(atom, polarity, exp);
  return true;
}

TrustNode ProofEqEngine::assertConflict(Node lit)
{
  Trace("pfee") << "pfee::assertConflict " << lit << std::endl;
  std::vector<TNode> assumps;
  explainWithProof(lit, assumps);
  if (d_pfEnabled)
  {
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
  }
  return ensureProofForFact(d_false, assumps, true);
}

TrustNode ProofEqEngine::assertConflict(PfRule id, const std::vector<Node>& exp)
{
  Trace("pfee") << "pfee::assertConflict " << id << ", exp = " << exp
                << std::endl;
  std::vector<Node> args;
  return assertConflict(id, exp, args);
}

TrustNode ProofEqEngine::assertConflict(PfRule id,
                                        const std::vector<Node>& exp,
                                        const std::vector<Node>& args)
{
  Trace("pfee") << "pfee::assertConflict " << id << ", exp = " << exp
                << ", args = " << args << std::endl;
  // conflict is same as proof of false
  return assertLemma(d_false, id, exp, exp, args);
}

TrustNode ProofEqEngine::assertConflict(const std::vector<Node>& exp,
                                        ProofStepBuffer& psb)
{
  Trace("pfee") << "pfee::assertConflict " << exp << " via buffer with "
                << psb.getNumSteps() << " steps" << std::endl;
  if (d_pfEnabled)
  {
    if (!d_proof.addSteps(psb))
    {
      return TrustNode::null();
    }
  }
  return assertLemmaInternal(d_false, exp, exp);
}

TrustNode ProofEqEngine::assertLemma(Node conc,
                                     PfRule id,
                                     const std::vector<Node>& exp,
                                     const std::vector<Node>& toExplain,
                                     const std::vector<Node>& args)
{
  Trace("pfee") << "pfee::assertLemma " << conc << " " << id
                << ", exp = " << exp << ", toExplain = " << toExplain
                << ", args = " << args << std::endl;
  Assert(conc != d_true);
  if (d_pfEnabled)
  {
    // Register the proof step.
    if (!d_proof.addStep(conc, id, exp, args))
    {
      // a step went wrong, e.g. during checking
      Assert(false) << "pfee::assertConflict: register proof step";
      return TrustNode::null();
    }
  }
  return assertLemmaInternal(conc, exp, toExplain);
}

TrustNode ProofEqEngine::assertLemma(Node conc,
                                     const std::vector<Node>& exp,
                                     const std::vector<Node>& toExplain,
                                     ProofStepBuffer& psb)
{
  Trace("pfee") << "pfee::assertLemma " << conc << ", exp = " << exp
                << ", toExplain = " << toExplain << " via buffer with "
                << psb.getNumSteps() << " steps" << std::endl;
  if (d_pfEnabled)
  {
    // add all steps to the proof
    const std::vector<std::pair<Node, ProofStep>>& steps = psb.getSteps();
    for (const std::pair<Node, ProofStep>& ps : steps)
    {
      if (!d_proof.addStep(ps.first, ps.second))
      {
        return TrustNode::null();
      }
    }
  }
  return assertLemmaInternal(conc, exp, toExplain);
}

TrustNode ProofEqEngine::assertLemmaInternal(Node conc,
                                             const std::vector<Node>& exp,
                                             const std::vector<Node>& toExplain)
{
  // We are a conflict if the conclusion is false and all literals are
  // explained.
  bool isConflict = conc == d_false;

  // get the explanation, with proofs
  std::vector<TNode> assumps;
  std::vector<Node> expn;
  for (const Node& e : exp)
  {
    if (std::find(toExplain.begin(), toExplain.end(), e) != toExplain.end())
    {
      explainWithProof(e, assumps);
    }
    else
    {
      // it did not have a proof; it was an assumption of the previous rule
      assumps.push_back(e);
      // it is not a conflict, since it may involve new literals
      isConflict = false;
    }
  }
  return ensureProofForFact(conc, assumps, isConflict);
}

TrustNode ProofEqEngine::ensureProofForFact(Node conc,
                                            const std::vector<TNode>& assumps,
                                            bool isConflict)
{
  Trace("pfee-proof") << std::endl;
  Trace("pfee-proof") << "pfee::ensureProofForFact: input " << conc << " via "
                      << assumps << ", isConflict=" << isConflict << std::endl;
  // make the conflict or lemma
  NodeManager* nm = NodeManager::currentNM();

  // The arguments to pass to SCOPE
  std::vector<Node> scopeAssumps;
  // The proof
  std::shared_ptr<ProofNode> pfConc;
  ProofGenerator* pfg = nullptr;
  // if proofs are enabled, generate the proof and clean the assumptions
  if (d_pfEnabled)
  {
    Trace("pfee-proof") << "pfee::ensureProofForFact: make proof for fact"
                        << std::endl;
    // get the proof for conc
    pfConc = mkProofForFact(conc);
    if (pfConc == nullptr)
    {
      Trace("pfee-proof")
          << "pfee::ensureProofForFact: failed to make proof for fact"
          << std::endl
          << std::endl;
      // should have existed
      Assert(false) << "pfee::assertConflict: failed to get proof for " << conc;
      return TrustNode::null();
    }
    Trace("pfee-proof") << "pfee::ensureProofForFact: add scope" << std::endl;
    // The free assumptions must be closed by assumps, which should be passed
    // as arguments of SCOPE. However, some of the free assumptions may not
    // literally be equal to assumps, for instance, due to symmetry. In other
    // words, the SCOPE could be closing (= x y) in a proof with free
    // assumption (= y x). Instead of modifying the proof, we modify the
    // assumption vector to pass to SCOPE so that all assumptions are matched.

    // The free assumptions of the proof
    std::vector<Node> freeAssumps;
    pfConc->getFreeAssumptions(freeAssumps);
    // Whether we have ensured freeAssumps is a subset of scopeAssumps
    for (const TNode& a : assumps)
    {
      if (std::find(freeAssumps.begin(), freeAssumps.end(), a)
          != freeAssumps.end())
      {
        scopeAssumps.push_back(a);
        continue;
      }
      // otherwise it may be due to symmetry?
      bool polarity = a.getKind() != NOT;
      Node aeq = polarity ? a : a[0];
      if (aeq.getKind() == EQUAL)
      {
        Node aeqSym = aeq[1].eqNode(aeq[0]);
        aeqSym = polarity ? aeqSym : aeqSym.notNode();
        if (std::find(freeAssumps.begin(), freeAssumps.end(), aeqSym)
            != freeAssumps.end())
        {
          scopeAssumps.push_back(aeqSym);
          continue;
        }
      }
      scopeAssumps.push_back(a);
      // The assumption should match a free assumption; if it does not, then
      // the explanation could have been smaller. This assertion should be
      // ensured by the fact that the core mechanism for generating proofs
      // from the equality engine is syncronized with its getExplanation
      // method.
      Trace("pfee-proof") << "Could not find free assumption for " << a
                          << " in " << freeAssumps << std::endl;
      Assert(false) << "pfee::ensureProofForFact: explained assumption " << a
                    << " does not match a free assumption from " << freeAssumps
                    << " in the corresponding proof";
    }
  }
  else
  {
    scopeAssumps.insert(scopeAssumps.end(), assumps.begin(), assumps.end());
  }
  // Make the lemma or conflict node. This must exactly match the conclusion
  // of SCOPE below.
  Node formula = mkAnd(scopeAssumps);
  if (isConflict)
  {
    Assert(conc == d_false);
  }
  else
  {
    formula = formula == d_true
                  ? conc
                  : (conc == d_false ? formula.negate()
                                     : nm->mkNode(IMPLIES, formula, conc));
  }
  Trace("pfee-proof") << "pfee::ensureProofForFact: formula is " << formula
                      << std::endl;
  // if proofs are enabled, scope the proof constructed above, and connect the
  // formula with the proof
  if (d_pfEnabled)
  {
    // Notice that we have an expected conclusion (formula) which we pass to
    // mkNode, which can check it if it wants. This is negated for conflicts.
    Node concFormula = isConflict ? formula.negate() : formula;
    std::shared_ptr<ProofNode> pf =
        d_pnm->mkNode(PfRule::SCOPE, pfConc, scopeAssumps, concFormula);
    if (Trace.isOn("pfee-proof") || Trace.isOn("pfee-proof-final"))
    {
      Trace("pfee-proof") << "pfee::ensureProofForFact: printing proof"
                          << std::endl;
      std::stringstream ss;
      pf->printDebug(ss);
      Trace("pfee-proof") << "pfee::ensureProofForFact: Proof is " << ss.str()
                          << std::endl;
      Trace("pfee-proof-final")
          << "pfee::ensureProofForFact: Proof is " << ss.str() << std::endl;
    }
    // should always succeed, since assumptions should be closed
    Assert(pf != nullptr);
    // Should be a closed proof now. If it is not, then the overall proof
    // is malformed.
    if (!pf->isClosed())
    {
      std::stringstream ss;
      pf->printDebug(ss);
      Trace("pfee-proof-final")
          << "pfee::ensureProofForFact: Proof is " << ss.str() << std::endl;
      AlwaysAssert(false) << "Generated a non-closed proof: " << ss.str()
                          << std::endl;
    }
    // set the proof for the conflict or lemma, which can be queried later
    if (isConflict)
    {
      setProofForConflict(formula, pf);
    }
    else
    {
      setProofForLemma(formula, pf);
    }
    pfg = this;
  }
  Trace("pfee-proof") << "pfee::ensureProofForFact: finish" << std::endl
                      << std::endl;
  // we can provide a proof for conflict or lemma
  if (isConflict)
  {
    return TrustNode::mkTrustConflict(formula, pfg);
  }
  return TrustNode::mkTrustLemma(formula, pfg);
}

std::shared_ptr<ProofNode> ProofEqEngine::mkProofForFact(Node lit)
{
  // use the lazy proof version
  std::shared_ptr<ProofNode> p = d_proof.getLazyProof(lit);
  if (p == nullptr)
  {
    return nullptr;
  }
  // clone it so that we have a fresh copy
  return p->clone();
}

void ProofEqEngine::assertFactInternal(TNode atom, bool polarity, TNode reason)
{
  Trace("pfee-debug") << "pfee::assertFactInternal: " << atom << " " << polarity
                      << " " << reason << std::endl;
  if (atom.getKind() == EQUAL)
  {
    d_ee.assertEquality(atom, polarity, reason);
  }
  else
  {
    d_ee.assertPredicate(atom, polarity, reason);
  }
  // must reference count the new atom and explanation
  d_keep.insert(atom);
  d_keep.insert(reason);
}

bool ProofEqEngine::addProofStep(Node lit,
                                 PfRule id,
                                 const std::vector<Node>& exp,
                                 const std::vector<Node>& args)
{
  if (id == PfRule::UNKNOWN)
  {
    // should only provide unknown step if already set up the proof step
    Assert(d_proof.hasStep(lit));
  }
  else if (!d_proof.addStep(lit, id, exp, args))
  {
    // failed to register step
    return false;
  }
  return true;
}

void ProofEqEngine::explainWithProof(Node lit, std::vector<TNode>& assumps)
{
  if (std::find(assumps.begin(), assumps.end(), lit)
      != assumps.end())
  {
    return;
  }
  std::shared_ptr<eq::EqProof> pf =
      d_pfEnabled ? std::make_shared<eq::EqProof>() : nullptr;
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
      if (d_recExplain)
      {
        if(!d_ee.areDisequal(atom[0],atom[1],true))
        {
          // TODO: it appears that this is necessary for assumptions that caused
          // a conflict
          assumps.push_back(lit);
          return;
        }
      }
      else
      {
        // ensure the explanation exists
        AlwaysAssert(d_ee.areDisequal(atom[0], atom[1], true));
      }
    }
    else
    {
      // Assert(d_ee.areEqual(atom[0], atom[1]));
    }
    d_ee.explainEquality(atom[0], atom[1], polarity, tassumps, pf.get());
  }
  else
  {
    if (d_recExplain)
    {
      if (!d_ee.hasTerm(atom))
      {
        // TODO: it appears that this is necessary for assumptions that caused
        // a conflict
        assumps.push_back(lit);
        return;
      }
    }
    else
    {
      Assert(d_ee.hasTerm(atom));
    }
    d_ee.explainPredicate(atom, polarity, tassumps, pf.get());
  }
  Trace("pfee-proof") << "...got " << tassumps << std::endl;
  // avoid duplicates
  for (const TNode a : tassumps)
  {
    if (a==lit)
    {
      assumps.push_back(a);
    }
    else if (d_recExplain)
    {
      if (a.getKind()==AND)
      {
        for (const Node& ac : a)
        {
          // recurse
          explainWithProof(ac, assumps);
        }
      }
      else
      {
        // recurse
        explainWithProof(a, assumps);
      }
    }
    else if (std::find(assumps.begin(), assumps.end(), a) == assumps.end())
    {
      assumps.push_back(a);
    }
  }
  if (d_pfEnabled)
  {
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
    pf->addToProof(&d_proof);
  }
  Trace("pfee-proof") << "pfee::explainWithProof: finished" << std::endl;
}

Node ProofEqEngine::mkAnd(const std::vector<Node>& a)
{
  if (a.empty())
  {
    return d_true;
  }
  else if (a.size() == 1)
  {
    return a[0];
  }
  return NodeManager::currentNM()->mkNode(AND, a);
}

Node ProofEqEngine::mkAnd(const std::vector<TNode>& a)
{
  if (a.empty())
  {
    return d_true;
  }
  else if (a.size() == 1)
  {
    return a[0];
  }
  return NodeManager::currentNM()->mkNode(AND, a);
}

void ProofEqEngine::flattenAnd(TNode an, std::vector<Node>& a)
{
  if (an == d_true)
  {
    return;
  }
  if (an.getKind() != AND)
  {
    a.push_back(an);
    return;
  }
  for (const Node& anc : an)
  {
    // should not have doubly nested AND
    Assert(anc.getKind() != AND);
    a.push_back(anc);
  }
}

std::ostream& operator<<(std::ostream& out, const ProofInferInfo& pii)
{
  out << "(proof-infer " << pii.d_rule << " " << pii.d_conc;
  if (!pii.d_children.empty())
  {
    out << " :children (" << pii.d_children << ")";
  }
  if (!pii.d_args.empty())
  {
    out << " :args (" << pii.d_args << ")";
  }
  if (!pii.d_childrenToExplain.empty())
  {
    out << " :childrenExp (" << pii.d_childrenToExplain << ")";
  }
  out << ")";
  return out;
}

}  // namespace eq
}  // namespace theory
}  // namespace CVC4
