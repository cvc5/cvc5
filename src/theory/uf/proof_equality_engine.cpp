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
      d_keep(c),
      d_pfEnabled(pnm != nullptr)
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
    if (d_pfEnabled)
    {
      // If proofs are enabled, we check if lit is an assertion of the form
      //   (= P true), (= P false), (= false P) or (= true P).
      // Such literals must be handled as a special case here, since equality
      // with Boolean constants have a special status internally within equality
      // engine. In particular, the proofs constructed by EqProof conversion
      // always produce proofs involving equalities with Boolean constants, and
      // whose assumptions are only of the form P or (not P). However, in the
      // case that (= P true) (resp (= P false)) is itself an input to the
      // equality engine, we will explain in terms of P (resp. (not P)), which
      // leads to a bogus proof, typically encountered in
      // ProofNodeManager::mkScope.
      //
      // To correct this, we add an explicit *fact* that P holds by (= P true)
      // here. This means that EqProof conversion may generate a proof where
      // the internal equality (= P true) is justified by assumption P, and that
      // afterwards, P is explained in terms of the original (external) equality
      // (= P true) by the step provided here. This means that the proof may end
      // up using (= P true) in a roundabout way (through two redundant steps),
      // but regardless this allows the core proof utilities (EqProof
      // conversion, proof equality engine, lazy proof, etc.) to be unconcerned
      // with this case. Multiple users of the proof equality engine
      // (SharedTermDatabase and TheoryArrays) require this special case.
      if (atom[0].getKind() == kind::CONST_BOOLEAN
          || atom[1].getKind() == kind::CONST_BOOLEAN)
      {
        Node nlit = Rewriter::rewrite(lit);
        if (!CDProof::isSame(lit, nlit))
        {
          // use a rewrite step as a fact
          std::vector<Node> pfChildren;
          pfChildren.push_back(lit);
          return assertFact(nlit, PfRule::MACRO_SR_PRED_ELIM, pfChildren, {});
        }
      }
    }
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

  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;
  // register the step in the proof
  if (d_pfEnabled)
  {
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
  }
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
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;
  // register the step in the proof
  if (d_pfEnabled)
  {
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
  }
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
  if (d_pfEnabled)
  {
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
  }
  // second, assert it to the equality engine
  return assertFactInternal(atom, polarity, exp);
}

bool ProofEqEngine::assertFact(Node lit, Node exp, ProofGenerator* pg)
{
  Trace("pfee") << "pfee::assertFact " << lit << ", exp = " << exp
                << " via generator" << std::endl;
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;
  if (d_pfEnabled)
  {
    if (holds(atom, polarity))
    {
      // we do not process this fact if it already holds
      return false;
    }
    // note the proof generator is responsible for remembering the explanation
    d_proof.addLazyStep(lit, pg, false);
  }
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
  // not using a proof
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
  Trace("pfee") << "pfee::explain " << conc << std::endl;
  if (d_pfEnabled)
  {
    LazyCDProof tmpProof(d_pnm, &d_proof);
    std::vector<TNode> assumps;
    explainWithProof(conc, assumps, &tmpProof);
    return ensureProofForFact(
        conc, assumps, TrustNodeKind::PROP_EXP, &tmpProof);
  }
  std::vector<TNode> assumps;
  explainWithProof(conc, assumps, nullptr);
  return ensureProofForFact(conc, assumps, TrustNodeKind::PROP_EXP, nullptr);
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
  if (d_pfEnabled)
  {
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
    exp = mkAnd(scopeAssumps);
  }
  else
  {
    exp = mkAnd(assumps);
  }
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
  if (d_pfEnabled)
  {
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

ProofEqEngine::FactProofGenerator::FactProofGenerator(context::Context* c,
                                                      ProofNodeManager* pnm)
    : ProofGenerator(), d_facts(c), d_pnm(pnm)
{
}

bool ProofEqEngine::FactProofGenerator::addStep(Node fact, ProofStep ps)
{
  if (d_facts.find(fact) != d_facts.end())
  {
    // duplicate
    return false;
  }
  Node symFact = CDProof::getSymmFact(fact);
  if (!symFact.isNull())
  {
    if (d_facts.find(symFact) != d_facts.end())
    {
      // duplicate due to symmetry
      return false;
    }
  }
  d_facts.insert(fact, std::make_shared<ProofStep>(ps));
  return true;
}

std::shared_ptr<ProofNode> ProofEqEngine::FactProofGenerator::getProofFor(
    Node fact)
{
  Trace("pfee-fact-gen") << "FactProofGenerator::getProofFor: " << fact
                         << std::endl;
  NodeProofStepMap::iterator it = d_facts.find(fact);
  if (it == d_facts.end())
  {
    Node symFact = CDProof::getSymmFact(fact);
    if (symFact.isNull())
    {
      Trace("pfee-fact-gen") << "...cannot find step" << std::endl;
      Assert(false);
      return nullptr;
    }
    it = d_facts.find(symFact);
    if (it == d_facts.end())
    {
      Assert(false);
      Trace("pfee-fact-gen") << "...cannot find step (no sym)" << std::endl;
      return nullptr;
    }
  }
  Trace("pfee-fact-gen") << "...return via step " << *(*it).second << std::endl;
  CDProof cdp(d_pnm);
  cdp.addStep(fact, *(*it).second);
  return cdp.getProofFor(fact);
}

}  // namespace eq
}  // namespace theory
}  // namespace CVC4
