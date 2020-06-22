/*********************                                                        */
/*! \file inference_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the inference manager for the theory of strings.
 **/

#include "theory/strings/inference_manager.h"

#include "options/strings_options.h"
#include "theory/ext_theory.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

InferenceManager::InferenceManager(SolverState& s,
                                   TermRegistry& tr,
                                   ExtTheory& e,
                                   OutputChannel& out,
                                   SequencesStatistics& statistics,
                                   ProofNodeManager* pnm)
    : d_state(s),
      d_termReg(tr),
      d_extt(e),
      d_out(out),
      d_statistics(statistics),
      d_pfee(new eq::ProofEqEngine(d_state.getSatContext(),
                                   d_state.getUserContext(),
                                   *d_state.getEqualityEngine(),
                                   pnm)),
      d_ipc(new InferProofCons(
          d_state.getSatContext(), pnm, d_statistics, options::proofNew()))
{
  NodeManager* nm = NodeManager::currentNM();
  d_zero = nm->mkConst(Rational(0));
  d_one = nm->mkConst(Rational(1));
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

void InferenceManager::sendAssumption(TNode lit)
{
  preProcessFact(lit);
  // assert it to the equality engine as an assumption
  d_pfee->assertAssume(lit);
  // process the fact
  postProcessFact(lit);
}

bool InferenceManager::sendInternalInference(std::vector<Node>& exp,
                                             Node conc,
                                             Inference infer)
{
  if (conc.getKind() == AND
      || (conc.getKind() == NOT && conc[0].getKind() == OR))
  {
    Node conj = conc.getKind() == AND ? conc : conc[0];
    bool pol = conc.getKind() == AND;
    bool ret = true;
    for (const Node& cc : conj)
    {
      bool retc = sendInternalInference(exp, pol ? cc : cc.negate(), infer);
      ret = ret && retc;
    }
    return ret;
  }
  bool pol = conc.getKind() != NOT;
  Node lit = pol ? conc : conc[0];
  if (lit.getKind() == EQUAL)
  {
    for (unsigned i = 0; i < 2; i++)
    {
      if (!lit[i].isConst() && !d_state.hasTerm(lit[i]))
      {
        // introduces a new non-constant term, do not infer
        return false;
      }
    }
    // does it already hold?
    if (pol ? d_state.areEqual(lit[0], lit[1])
            : d_state.areDisequal(lit[0], lit[1]))
    {
      return true;
    }
  }
  else if (lit.isConst())
  {
    if (lit.getConst<bool>())
    {
      Assert(pol);
      // trivially holds
      return true;
    }
  }
  else if (!d_state.hasTerm(lit))
  {
    // introduces a new non-constant term, do not infer
    return false;
  }
  else if (d_state.areEqual(lit, pol ? d_true : d_false))
  {
    // already holds
    return true;
  }
  sendInference(exp, conc, infer);
  return true;
}

void InferenceManager::sendInference(const std::vector<Node>& exp,
                                     const std::vector<Node>& noExplain,
                                     Node eq,
                                     Inference infer,
                                     bool isRev,
                                     bool asLemma)
{
  if (eq.isNull())
  {
    eq = d_false;
  }
  else if (Rewriter::rewrite(eq) == d_true)
  {
    // if trivial, return
    return;
  }
  // wrap in infer info and send below
  InferInfo ii;
  ii.d_id = infer;
  ii.d_idRev = isRev;
  ii.d_conc = eq;
  ii.d_ant = exp;
  ii.d_noExplain = noExplain;
  sendInference(ii, asLemma);
}

void InferenceManager::sendInference(const std::vector<Node>& exp,
                                     Node eq,
                                     Inference infer,
                                     bool isRev,
                                     bool asLemma)
{
  std::vector<Node> noExplain;
  sendInference(exp, noExplain, eq, infer, isRev, asLemma);
}

void InferenceManager::sendInference(const InferInfo& ii, bool asLemma)
{
  Assert(!ii.isTrivial());
  Trace("strings-infer-debug")
      << "sendInference: " << ii << ", asLemma = " << asLemma << std::endl;
  // check if we should send a conflict, lemma or a fact
  if (asLemma || options::stringInferAsLemmas() || !ii.isFact())
  {
    if (ii.isConflict())
    {
      Trace("strings-infer-debug") << "...as conflict" << std::endl;
      Trace("strings-lemma") << "Strings::Conflict: " << ii.d_ant << " by "
                             << ii.d_id << std::endl;
      Trace("strings-conflict") << "CONFLICT: inference conflict " << ii.d_ant
                                << " by " << ii.d_id << std::endl;
      ++(d_statistics.d_conflictsInfer);
      // process the conflict
      processConflict(ii);
      return;
    }
    Trace("strings-infer-debug") << "...as lemma" << std::endl;
    d_pendingLem.push_back(ii);
    return;
  }
  if (options::stringInferSym())
  {
    std::vector<Node> vars;
    std::vector<Node> subs;
    std::vector<Node> unproc;
    for (const Node& ac : ii.d_ant)
    {
      d_termReg.inferSubstitutionProxyVars(ac, vars, subs, unproc);
    }
    if (unproc.empty())
    {
      Node eqs = ii.d_conc.substitute(
          vars.begin(), vars.end(), subs.begin(), subs.end());
      InferInfo iiSubsLem;
      // keep the same id for now, since we are transforming the form of the
      // inference, not the root reason.
      iiSubsLem.d_id = ii.d_id;
      iiSubsLem.d_conc = eqs;
      if (Trace.isOn("strings-lemma-debug"))
      {
        Trace("strings-lemma-debug")
            << "Strings::Infer " << iiSubsLem << std::endl;
        Trace("strings-lemma-debug")
            << "Strings::Infer Alternate : " << eqs << std::endl;
        for (unsigned i = 0, nvars = vars.size(); i < nvars; i++)
        {
          Trace("strings-lemma-debug")
              << "  " << vars[i] << " -> " << subs[i] << std::endl;
        }
      }
      Trace("strings-infer-debug") << "...as symbolic lemma" << std::endl;
      d_pendingLem.push_back(iiSubsLem);
      return;
    }
    if (Trace.isOn("strings-lemma-debug"))
    {
      for (const Node& u : unproc)
      {
        Trace("strings-lemma-debug")
            << "  non-trivial explanation : " << u << std::endl;
      }
    }
  }
  Trace("strings-infer-debug") << "...as fact" << std::endl;
  // add to pending to be processed as a fact
  d_pending.push_back(ii);
}

void InferenceManager::processConflict(const InferInfo& ii)
{
  // we must fully explain it
  bool useBuffer = false;
  ProofStep ps;
  d_ipc->convert(ii, ps, useBuffer);
  TrustNode tconf;
  if (useBuffer)
  {
    tconf = d_pfee->assertConflict(ps.d_children, *d_ipc->getBuffer());
  }
  else
  {
    tconf = d_pfee->assertConflict(ps.d_rule, ps.d_children, ps.d_args);
  }
  Assert(tconf.getKind() == TrustNodeKind::CONFLICT);
  Trace("strings-assert") << "(assert (not " << tconf.getNode()
                          << ")) ; conflict " << ii.d_id << std::endl;
  d_out.trustedConflict(tconf);
  d_state.setConflict();
}

bool InferenceManager::sendSplit(Node a, Node b, Inference infer, bool preq)
{
  Node eq = a.eqNode(b);
  eq = Rewriter::rewrite(eq);
  if (eq.isConst())
  {
    return false;
  }
  NodeManager* nm = NodeManager::currentNM();
  InferInfo iiSplit;
  iiSplit.d_id = infer;
  iiSplit.d_conc = nm->mkNode(OR, eq, nm->mkNode(NOT, eq));
  sendPhaseRequirement(eq, preq);
  d_pendingLem.push_back(iiSplit);
  return true;
}

void InferenceManager::sendPhaseRequirement(Node lit, bool pol)
{
  lit = Rewriter::rewrite(lit);
  d_pendingReqPhase[lit] = pol;
}

void InferenceManager::setIncomplete() { d_out.setIncomplete(); }

void InferenceManager::addToExplanation(Node a,
                                        Node b,
                                        std::vector<Node>& exp) const
{
  if (a != b)
  {
    Debug("strings-explain")
        << "Add to explanation : " << a << " == " << b << std::endl;
    Assert(d_state.areEqual(a, b));
    exp.push_back(a.eqNode(b));
  }
}

void InferenceManager::addToExplanation(Node lit, std::vector<Node>& exp) const
{
  if (!lit.isNull())
  {
    Assert(!lit.isConst());
    exp.push_back(lit);
  }
}

void InferenceManager::doPendingFacts()
{
  size_t i = 0;
  while (!d_state.isInConflict() && i < d_pending.size())
  {
    InferInfo& ii = d_pending[i];
    // get the facts
    std::vector<Node> facts;
    if (ii.d_conc.getKind() == AND)
    {
      for (const Node& cc : ii.d_conc)
      {
        facts.push_back(cc);
      }
    }
    else
    {
      facts.push_back(ii.d_conc);
    }
    Trace("strings-assert")
        << "(assert (=> " << ii.getAntecedant() << " " << ii.d_conc
        << ")) ; fact " << ii.d_id << std::endl;
    Trace("strings-lemma") << "Strings::Fact: " << ii.d_conc << " from "
                           << ii.getAntecedant() << " by " << ii.d_id
                           << std::endl;
    std::vector<Node> exp;
    for (const Node& ec : ii.d_ant)
    {
      utils::flattenOp(AND, ec, exp);
    }
    Node cexp = utils::mkAnd(exp);
    // convert for each fact
    for (const Node& fact : facts)
    {
      ii.d_conc = fact;
      preProcessFact(fact);
      // notify fact
      d_ipc->notifyFact(ii);
      // assert to equality engine using proof generator interface for
      // assertFact.
      d_pfee->assertFact(fact, cexp, d_ipc.get());
      // may be in conflict
      if (d_state.isInConflict())
      {
        break;
      }
      // otherwise, post-process
      postProcessFact(fact);
    }
    i++;
  }
  d_pending.clear();
}

void InferenceManager::doPendingLemmas()
{
  if (d_state.isInConflict())
  {
    // just clear the pending vectors, nothing else to do
    d_pendingLem.clear();
    d_pendingReqPhase.clear();
    return;
  }
  // we probably don't need to add lazily since temporary proofs are setup
  bool lazyAdd = false;
  for (unsigned i = 0, psize = d_pendingLem.size(); i < psize; i++)
  {
    InferInfo& ii = d_pendingLem[i];
    Assert(!ii.isTrivial());
    Assert(!ii.isConflict());
    // set up proof step based on inference
    // pfExp is the children of the proof step below. This should be an
    // ordered list of expConj + expn.

    // set up the explanation and no-explanation
    TrustNode tlem;
    std::vector<Node> exp;
    for (const Node& ec : ii.d_ant)
    {
      utils::flattenOp(AND, ec, exp);
    }
    std::vector<Node> noExplain;
    if (!options::stringRExplainLemmas())
    {
      // if we aren't regressing the explanation, we add all literals to
      // noExplain and ignore ii.d_antn.
      noExplain.insert(noExplain.end(), exp.begin(), exp.end());
    }
    else
    {
      // otherwise, the no-explain literals are those provided
      for (const Node& ecn : ii.d_noExplain)
      {
        utils::flattenOp(AND, ecn, noExplain);
      }
    }
    if (lazyAdd)
    {
      // notify fact and assert lemma via generator
      d_ipc->notifyFact(ii);
      tlem = d_pfee->assertLemma(ii.d_conc, exp, noExplain, d_ipc.get());
    }
    else
    {
      // make the trusted lemma object
      bool useBuffer = false;
      ProofStep ps;
      Node conc = d_ipc->convert(ii, ps, useBuffer);
      if (useBuffer)
      {
        tlem = d_pfee->assertLemma(conc, exp, noExplain, *d_ipc->getBuffer());
      }
      else
      {
        tlem = d_pfee->assertLemma(conc, ps.d_rule, exp, noExplain, ps.d_args);
      }
    }
    Node lem = tlem.getNode();
    Trace("strings-pending") << "Process pending lemma : " << lem << std::endl;

    // Process the side effects of the inference info.
    // Register the new skolems from this inference. We register them here
    // (lazily), since this is the moment when we have decided to process the
    // inference.
    for (const std::pair<const LengthStatus, std::vector<Node> >& sks :
         ii.d_new_skolem)
    {
      for (const Node& n : sks.second)
      {
        d_termReg.registerTermAtomic(n, sks.first);
      }
    }

    Trace("strings-assert")
        << "(assert " << lem << ") ; lemma " << ii.d_id << std::endl;
    Trace("strings-lemma") << "Strings::Lemma: " << lem << " by " << ii.d_id
                           << std::endl;
    ++(d_statistics.d_lemmasInfer);
    d_out.trustedLemma(tlem);
  }
  // process the pending require phase calls
  for (const std::pair<const Node, bool>& prp : d_pendingReqPhase)
  {
    Trace("strings-pending") << "Require phase : " << prp.first
                             << ", polarity = " << prp.second << std::endl;
    d_out.requirePhase(prp.first, prp.second);
  }
  d_pendingLem.clear();
  d_pendingReqPhase.clear();
}

void InferenceManager::preProcessFact(TNode fact)
{
  bool polarity = fact.getKind() != NOT;
  TNode atom = polarity ? fact : fact[0];
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  Assert(atom.getKind() != OR) << "Infer error: a split.";
  if (atom.getKind() == EQUAL)
  {
    // we must ensure these terms are registered
    for (const Node& t : atom)
    {
      // terms in the equality engine are already registered, hence skip
      // currently done for only string-like terms, but this could potentially
      // be avoided.
      if (!ee->hasTerm(t) && t.getType().isStringLike())
      {
        d_termReg.registerTerm(t, 0);
      }
    }
  }
}
void InferenceManager::postProcessFact(TNode fact)
{
  bool polarity = fact.getKind() != NOT;
  TNode atom = polarity ? fact : fact[0];
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  if (atom.getKind() == STRING_IN_REGEXP && polarity
      && atom[1].getKind() == REGEXP_CONCAT)
  {
    Node eqc = ee->getRepresentative(atom[0]);
    d_state.addEndpointsToEqcInfo(atom, atom[1], eqc);
  }
  // process the conflict
  if (!d_state.isInConflict())
  {
    Node pc = d_state.getPendingConflict();
    if (!pc.isNull())
    {
      Trace("strings-pending")
          << "Process pending conflict " << pc << std::endl;
      InferInfo iiPrefixConf;
      iiPrefixConf.d_id = Inference::PREFIX_CONFLICT;
      iiPrefixConf.d_conc = d_false;
      utils::flattenOp(AND, pc, iiPrefixConf.d_ant);
      Trace("strings-conflict")
          << "CONFLICT: Eager prefix : " << pc << std::endl;
      ++(d_statistics.d_conflictsEagerPrefix);
      processConflict(iiPrefixConf);
    }
  }
  Trace("strings-pending-debug") << "  Now collect terms" << std::endl;
  // Collect extended function terms in the atom. Notice that we must register
  // all extended functions occurring in assertions and shared terms. We
  // make a similar call to registerTermRec in TheoryStrings::addSharedTerm.
  d_extt.registerTermRec(atom);
  Trace("strings-pending-debug") << "  Finished collect terms" << std::endl;
}

bool InferenceManager::hasProcessed() const
{
  return d_state.isInConflict() || !d_pendingLem.empty() || !d_pending.empty();
}

TrustNode InferenceManager::explain(TNode literal) const
{
  // use the explain method of proof equality engine
  TrustNode trn = d_pfee->explain(literal);
  return trn;
}

void InferenceManager::markCongruent(Node a, Node b)
{
  Assert(a.getKind() == b.getKind());
  if (d_extt.hasFunctionKind(a.getKind()))
  {
    d_extt.markCongruent(a, b);
  }
}

void InferenceManager::markReduced(Node n, bool contextDepend)
{
  d_extt.markReduced(n, contextDepend);
}
eq::ProofEqEngine* InferenceManager::getProofEqEngine() { return d_pfee.get(); }

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
