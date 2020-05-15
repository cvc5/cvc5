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
                             bool recExplain)
    : EagerProofGenerator(u, pnm),
      d_ee(ee),
      d_pnm(pnm),
      d_proof(pnm, nullptr, c),
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
  // don't need to explicitly add anything to the proof here, since ASSUME
  // nodes are constructed lazily
  TNode atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;

  // Second, assert it directly to the equality engine, where it is its own
  // explanation. Notice we do not reference count atom/lit.
  if (atom.getKind() == EQUAL)
  {
    return d_ee.assertEquality(atom, polarity, lit);
  }
  return d_ee.assertPredicate(atom, polarity, lit);
}

bool ProofEqEngine::assertFact(Node lit,
                               PfRule id,
                               const std::vector<Node>& exp,
                               const std::vector<Node>& args)
{
  Trace("pfee") << "pfee::assertFact " << lit << " " << id << ", exp = " << exp
                << ", args = " << args << std::endl;
  // first, register the step in the proof
  if (d_pfEnabled)
  {
    AlwaysAssert(false);
    // FIXME this should buffer the Step
  }

  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;

  // second, assert it to the equality engine
  Node reason = mkAnd(exp);
  return assertFactInternal(atom, polarity, reason);
}

bool ProofEqEngine::assertFact(Node lit,
                               PfRule id,
                               Node exp,
                               const std::vector<Node>& args)
{
  Trace("pfee") << "pfee::assertFact " << lit << " " << id << ", exp = " << exp
                << ", args = " << args << std::endl;
  // first, register the step in the proof
  if (d_pfEnabled)
  {
    // must extract the explanation as a vector
    std::vector<Node> expv;
    flattenAnd(exp, expv);

    AlwaysAssert(false);
    // FIXME this should buffer the Step
  }
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;

  // second, assert it to the equality engine
  return assertFactInternal(atom, polarity, exp);
}

bool ProofEqEngine::assertFact(Node lit, Node exp, ProofStepBuffer& psb)
{
  Trace("pfee") << "pfee::assertFact " << lit << ", exp = " << exp
                << " via buffer with " << psb.getNumSteps() << " steps"
                << std::endl;
  if (d_pfEnabled)
  {
    AlwaysAssert(false);
    // FIXME this should buffer the Steps
  }
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;

  // second, assert it to the equality engine
  return assertFactInternal(atom, polarity, exp);
}

bool ProofEqEngine::assertFact(Node lit, Node exp, ProofGenerator* pg)
{
  Trace("pfee") << "pfee::assertFact " << lit << ", exp = " << exp
                << " via generator" << std::endl;
  if (d_pfEnabled)
  {
    // note the proof generator is responsible for remembering the explanation
    d_proof.addLazyStep(lit, pg);
  }
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;
  // second, assert it to the equality engine
  return assertFactInternal(atom, polarity, exp);
}

TrustNode ProofEqEngine::assertConflict(Node lit)
{
  Trace("pfee") << "pfee::assertConflict " << lit << std::endl;
  std::vector<TNode> assumps;
  explainWithProof(lit, assumps, &d_proof);
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
  return ensureProofForFact(
      d_false, assumps, TrustNodeKind::CONFLICT, &d_proof);
}

TrustNode ProofEqEngine::assertConflict(PfRule id,
                                        const std::vector<Node>& exp,
                                        const std::vector<Node>& args)
{
  Trace("pfee") << "pfee::assertConflict " << id << ", exp = " << exp
                << ", args = " << args << std::endl;
  // conflict is same as proof of false
  std::vector<Node> empVec;
  return assertLemma(d_false, id, exp, empVec, args);
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
  std::vector<Node> empVec;
  return assertLemmaInternal(d_false, exp, empVec, &d_proof);
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
  if (d_pfEnabled)
  {
    PRefProofGenerator prg(&d_proof);
    LazyCDProof tmpProof(d_pnm, &prg);
    LazyCDProof* curr;
    if (conc == d_false)
    {
      curr = &d_proof;
    }
    else
    {
      curr = &tmpProof;
    }
    // Register the proof step.
    if (!curr->addStep(conc, id, exp, args))
    {
      // a step went wrong, e.g. during checking
      Assert(false) << "pfee::assertConflict: register proof step";
      return TrustNode::null();
    }
    return assertLemmaInternal(conc, exp, noExplain, curr);
  }
  return assertLemmaInternal(conc, exp, noExplain, nullptr);
}

TrustNode ProofEqEngine::assertLemma(Node conc,
                                     const std::vector<Node>& exp,
                                     const std::vector<Node>& noExplain,
                                     ProofStepBuffer& psb)
{
  Trace("pfee") << "pfee::assertLemma " << conc << ", exp = " << exp
                << ", noExplain = " << noExplain << " via buffer with "
                << psb.getNumSteps() << " steps" << std::endl;
  if (d_pfEnabled)
  {
    PRefProofGenerator prg(&d_proof);
    LazyCDProof tmpProof(d_pnm, &prg);
    LazyCDProof* curr;
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
  return assertLemmaInternal(conc, exp, noExplain, nullptr);
}

TrustNode ProofEqEngine::assertLemma(Node conc,
                                     const std::vector<Node>& exp,
                                     const std::vector<Node>& noExplain,
                                     ProofGenerator* pg)
{
  Trace("pfee") << "pfee::assertLemma " << conc << ", exp = " << exp
                << ", noExplain = " << noExplain << " via buffer with generator"
                << std::endl;
  if (d_pfEnabled)
  {
    PRefProofGenerator prg(&d_proof);
    LazyCDProof tmpProof(d_pnm, &prg);
    LazyCDProof* curr;
    if (conc == d_false)
    {
      curr = &d_proof;
    }
    else
    {
      curr = &tmpProof;
    }
    // Register the proof step.
    if (!pg->addProofTo(conc, curr))
    {
      // a step went wrong, e.g. during checking
      Assert(false) << "pfee::assertConflict: register proof step";
      return TrustNode::null();
    }
    return assertLemmaInternal(conc, exp, noExplain, curr);
  }
  return assertLemmaInternal(conc, exp, noExplain, nullptr);
}

TrustNode ProofEqEngine::explain(Node conc)
{
  if (d_pfEnabled)
  {
    PRefProofGenerator prg(&d_proof);
    LazyCDProof tmpProof(d_pnm, &prg);
    std::vector<TNode> assumps;
    explainWithProof(conc, assumps, &tmpProof);
    return ensureProofForFact(
        conc, assumps, TrustNodeKind::PROP_EXP, &tmpProof);
  }
  std::vector<TNode> assumps;
  explainWithProof(conc, assumps, nullptr);
  return ensureProofForFact(conc, assumps, TrustNodeKind::PROP_EXP, nullptr);
}

std::string ProofEqEngine::identify() const
{
  std::stringstream ss;
  ss << "pf::" << d_ee.identify();
  return ss.str();
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
  // make the conflict or lemma
  NodeManager* nm = NodeManager::currentNM();

  // The arguments to pass to SCOPE
  std::vector<Node> scopeAssumps;
  // The proof
  std::shared_ptr<ProofNode> pfConc;
  ProofGenerator* pfg = nullptr;
  // the explanation is the conjunction of assumptions
  Node exp;
  ;
  // If proofs are enabled, generate the proof and possibly modify the
  // assumptions to match SCOPE.
  if (d_pfEnabled)
  {
    Assert(curr != nullptr);
    Trace("pfee-proof") << "pfee::ensureProofForFact: make proof for fact"
                        << std::endl;
    // get the proof for conc
    pfConc = curr->mkProof(conc);
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
    // clone it so that we have a fresh copy
    pfConc = pfConc->clone();
    Trace("pfee-proof") << "pfee::ensureProofForFact: add scope" << std::endl;
    // The free assumptions must be closed by assumps, which should be passed
    // as arguments of SCOPE. However, some of the free assumptions may not
    // literally be equal to assumps, for instance, due to symmetry. In other
    // words, the SCOPE could be closing (= x y) in a proof with free
    // assumption (= y x). We modify the proof leaves to account for this
    // below.

    // The free assumptions of the proof
    std::map<Node, std::vector<ProofNode*>> famap;
    pfConc->getFreeAssumptionsMap(famap);
    // we first ensure the assumptions are flattened
    std::unordered_set<Node, NodeHashFunction> ac;
    for (const TNode& a : assumps)
    {
      if (a.getKind() == AND)
      {
        ac.insert(a.begin(), a.end());
      }
      else
      {
        ac.insert(a);
      }
    }
    std::unordered_set<Node, NodeHashFunction> acu;
    std::unordered_set<Node, NodeHashFunction>::iterator itf;
    for (const std::pair<const Node, std::vector<ProofNode*>>& fa : famap)
    {
      Node a = fa.first;
      if (ac.find(a) != ac.end())
      {
        // already covered by an assumption
        acu.insert(a);
        continue;
      }
      // otherwise it may be due to symmetry?
      bool polarity = a.getKind() != NOT;
      Node aeq = polarity ? a : a[0];
      if (aeq.getKind() == EQUAL)
      {
        Node aeqSym = aeq[1].eqNode(aeq[0]);
        aeqSym = polarity ? aeqSym : aeqSym.notNode();
        itf = ac.find(aeqSym);
        if (itf != ac.end())
        {
          Trace("pfee-proof")
              << "- reorient assumption " << aeqSym << " via " << a << " for "
              << fa.second.size() << " proof nodes" << std::endl;
          std::shared_ptr<ProofNode> pfaa = d_pnm->mkAssume(aeqSym);
          for (ProofNode* pfs : fa.second)
          {
            Assert(pfs->getResult() == a);
            // must correct the orientation on this leaf
            std::vector<std::shared_ptr<ProofNode>> children;
            children.push_back(pfaa);
            std::vector<Node> args;
            args.push_back(a);
            d_pnm->updateNode(
                pfs, PfRule::MACRO_SR_PRED_TRANSFORM, children, args);
          }
          Trace("pfee-proof") << "...finished" << std::endl;
          acu.insert(aeqSym);
          continue;
        }
      }
      // All free assumptions should be arguments to SCOPE. If not, then this is
      // not a proof of the lemma/conflict/exp-prop we are sending out.
      std::stringstream ss;
      pfConc->printDebug(ss);
      ss << std::endl << "Free assumption: " << a << std::endl;
      for (const Node& aprint : ac)
      {
        ss << "- assumption: " << aprint << std::endl;
      }
      AlwaysAssert(false)
          << "Generated a proof that is not closed by the scope: " << ss.str()
          << std::endl;
    }
    if (acu.size() < ac.size())
    {
      // All assumptions should match a free assumption; if one does not, then
      // the explanation could have been smaller. This assertion should be
      // ensured by the fact that the core mechanism for generating proofs
      // from the equality engine is syncronized with its getExplanation
      // method.
      for (const Node& a : ac)
      {
        if (acu.find(a) == acu.end())
        {
          Notice() << "pfee::ensureProofForFact: assumption " << a
                   << " does not match a free assumption in proof" << std::endl;
        }
      }
    }
    scopeAssumps.insert(scopeAssumps.end(), acu.begin(), acu.end());
    exp = mkAnd(scopeAssumps);
  }
  else
  {
    exp = mkAnd(assumps);
  }
  // Make the lemma or conflict node. This must exactly match the conclusion
  // of SCOPE below.
  Node formula;
  Node concFormula;
  if (tnk == TrustNodeKind::CONFLICT)
  {
    // conflict is negated
    Assert(conc == d_false);
    formula = exp;
    concFormula = formula.negate();
  }
  else
  {
    formula =
        exp == d_true
            ? conc
            : (conc == d_false ? exp.negate() : nm->mkNode(IMPLIES, exp, conc));
    concFormula = formula;
  }
  Trace("pfee-proof") << "pfee::ensureProofForFact: formula is " << formula
                      << std::endl;
  // if proofs are enabled, scope the proof constructed above, and connect the
  // formula with the proof
  if (d_pfEnabled)
  {
    // Notice that we have an expected conclusion (formula) which we pass to
    // mkNode, which can check it if it wants. This is negated for conflicts.
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

void ProofEqEngine::explainWithProof(Node lit,
                                     std::vector<TNode>& assumps,
                                     LazyCDProof* curr)
{
  if (std::find(assumps.begin(), assumps.end(), lit) != assumps.end())
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
        if (!d_ee.areDisequal(atom[0], atom[1], true))
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
    if (a == lit)
    {
      assumps.push_back(a);
    }
    else if (d_recExplain)
    {
      if (a.getKind() == AND)
      {
        for (const Node& ac : a)
        {
          // recurse
          explainWithProof(ac, assumps, curr);
        }
      }
      else
      {
        // recurse
        explainWithProof(a, assumps, curr);
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
    pf->addToProof(curr);
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

}  // namespace eq
}  // namespace theory
}  // namespace CVC4
