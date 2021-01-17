/*********************                                                        */
/*! \file inference_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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

InferenceManager::InferenceManager(Theory& t,
                                   SolverState& s,
                                   TermRegistry& tr,
                                   ExtTheory& e,
                                   SequencesStatistics& statistics,
                                   ProofNodeManager* pnm)
    : InferenceManagerBuffered(t, s, pnm),
      d_state(s),
      d_termReg(tr),
      d_extt(e),
      d_statistics(statistics),
      d_ipc(pnm ? new InferProofCons(d_state.getSatContext(), pnm, d_statistics)
                : nullptr)
{
  NodeManager* nm = NodeManager::currentNM();
  d_zero = nm->mkConst(Rational(0));
  d_one = nm->mkConst(Rational(1));
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

void InferenceManager::doPending()
{
  doPendingFacts();
  if (d_state.isInConflict())
  {
    // just clear the pending vectors, nothing else to do
    clearPendingLemmas();
    clearPendingPhaseRequirements();
    return;
  }
  doPendingLemmas();
  doPendingPhaseRequirements();
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

bool InferenceManager::sendInference(const std::vector<Node>& exp,
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
    return false;
  }
  // wrap in infer info and send below
  InferInfo ii;
  ii.d_id = infer;
  ii.d_idRev = isRev;
  ii.d_conc = eq;
  ii.d_premises = exp;
  ii.d_noExplain = noExplain;
  sendInference(ii, asLemma);
  return true;
}

bool InferenceManager::sendInference(const std::vector<Node>& exp,
                                     Node eq,
                                     Inference infer,
                                     bool isRev,
                                     bool asLemma)
{
  std::vector<Node> noExplain;
  return sendInference(exp, noExplain, eq, infer, isRev, asLemma);
}

void InferenceManager::sendInference(InferInfo& ii, bool asLemma)
{
  Assert(!ii.isTrivial());
  // set that this inference manager will be processing this inference
  ii.d_sim = this;
  Trace("strings-infer-debug")
      << "sendInference: " << ii << ", asLemma = " << asLemma << std::endl;
  // check if we should send a conflict, lemma or a fact
  if (ii.isConflict())
  {
    Trace("strings-infer-debug") << "...as conflict" << std::endl;
    Trace("strings-lemma") << "Strings::Conflict: " << ii.d_premises << " by "
                           << ii.d_id << std::endl;
    Trace("strings-conflict") << "CONFLICT: inference conflict " << ii.d_premises << " by " << ii.d_id << std::endl;
    ++(d_statistics.d_conflictsInfer);
    // process the conflict immediately
    processConflict(ii);
    return;
  }
  else if (asLemma || options::stringInferAsLemmas() || !ii.isFact())
  {
    Trace("strings-infer-debug") << "...as lemma" << std::endl;
    addPendingLemma(std::unique_ptr<InferInfo>(new InferInfo(ii)));
    return;
  }
  if (options::stringInferSym())
  {
    std::vector<Node> vars;
    std::vector<Node> subs;
    std::vector<Node> unproc;
    for (const Node& ac : ii.d_premises)
    {
      d_termReg.inferSubstitutionProxyVars(ac, vars, subs, unproc);
    }
    if (unproc.empty())
    {
      Node eqs = ii.d_conc.substitute(
          vars.begin(), vars.end(), subs.begin(), subs.end());
      InferInfo iiSubsLem;
      iiSubsLem.d_sim = this;
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
      addPendingLemma(std::unique_ptr<InferInfo>(new InferInfo(iiSubsLem)));
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
  addPendingFact(std::unique_ptr<InferInfo>(new InferInfo(ii)));
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
  iiSplit.d_sim = this;
  iiSplit.d_id = infer;
  iiSplit.d_conc = nm->mkNode(OR, eq, nm->mkNode(NOT, eq));
  eq = Rewriter::rewrite(eq);
  addPendingPhaseRequirement(eq, preq);
  addPendingLemma(std::unique_ptr<InferInfo>(new InferInfo(iiSplit)));
  return true;
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

bool InferenceManager::hasProcessed() const
{
  return d_state.isInConflict() || hasPending();
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

void InferenceManager::processConflict(const InferInfo& ii)
{
  Assert(!d_state.isInConflict());
  // setup the fact to reproduce the proof in the call below
  d_statistics.d_inferences << ii.d_id;
  if (d_ipc != nullptr)
  {
    d_ipc->notifyFact(ii);
  }
  // make the trust node
  TrustNode tconf = mkConflictExp(ii.d_premises, d_ipc.get());
  Assert(tconf.getKind() == TrustNodeKind::CONFLICT);
  Trace("strings-assert") << "(assert (not " << tconf.getNode()
                          << ")) ; conflict " << ii.d_id << std::endl;
  // send the trusted conflict
  trustedConflict(tconf);
}

bool InferenceManager::processFact(InferInfo& ii)
{
  // Get the fact(s). There are multiple facts if the conclusion is an AND
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
  Trace("strings-assert") << "(assert (=> " << ii.getPremises() << " "
                          << ii.d_conc << ")) ; fact " << ii.d_id << std::endl;
  Trace("strings-lemma") << "Strings::Fact: " << ii.d_conc << " from "
                         << ii.getPremises() << " by " << ii.d_id
                         << std::endl;
  std::vector<Node> exp;
  for (const Node& ec : ii.d_premises)
  {
    utils::flattenOp(AND, ec, exp);
  }
  bool ret = false;
  // convert for each fact
  for (const Node& fact : facts)
  {
    ii.d_conc = fact;
    d_statistics.d_inferences << ii.d_id;
    bool polarity = fact.getKind() != NOT;
    TNode atom = polarity ? fact : fact[0];
    bool curRet = false;
    if (d_ipc != nullptr)
    {
      // ensure the proof generator is ready to explain this fact in the
      // current SAT context
      d_ipc->notifyFact(ii);
      // now, assert the internal fact with d_ipc as proof generator
      curRet = assertInternalFact(atom, polarity, exp, d_ipc.get());
    }
    else
    {
      Node cexp = utils::mkAnd(exp);
      // without proof generator
      curRet = assertInternalFact(atom, polarity, cexp);
    }
    ret = ret || curRet;
    // may be in conflict
    if (d_state.isInConflict())
    {
      break;
    }
  }
  return ret;
}

bool InferenceManager::processLemma(InferInfo& ii)
{
  Assert(!ii.isTrivial());
  Assert(!ii.isConflict());
  // set up the explanation and no-explanation
  std::vector<Node> exp;
  for (const Node& ec : ii.d_premises)
  {
    utils::flattenOp(AND, ec, exp);
  }
  std::vector<Node> noExplain;
  if (!options::stringRExplainLemmas())
  {
    // if we aren't regressing the explanation, we add all literals to
    // noExplain and ignore ii.d_ant.
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
  // ensure that the proof generator is ready to explain the final conclusion
  // of the lemma (ii.d_conc).
  d_statistics.d_inferences << ii.d_id;
  if (d_ipc != nullptr)
  {
    d_ipc->notifyFact(ii);
  }
  TrustNode tlem = mkLemmaExp(ii.d_conc, exp, noExplain, d_ipc.get());
  Trace("strings-pending") << "Process pending lemma : " << tlem.getNode()
                           << std::endl;

  // Process the side effects of the inference info.
  // Register the new skolems from this inference. We register them here
  // (lazily), since this is the moment when we have decided to process the
  // inference.
  for (const std::pair<const LengthStatus, std::vector<Node> >& sks :
       ii.d_newSkolem)
  {
    for (const Node& n : sks.second)
    {
      d_termReg.registerTermAtomic(n, sks.first);
    }
  }
  LemmaProperty p = LemmaProperty::NONE;
  if (ii.d_id == Inference::REDUCTION)
  {
    p |= LemmaProperty::NEEDS_JUSTIFY;
  }
  Trace("strings-assert") << "(assert " << tlem.getNode() << ") ; lemma "
                          << ii.d_id << std::endl;
  Trace("strings-lemma") << "Strings::Lemma: " << tlem.getNode() << " by "
                         << ii.d_id << std::endl;
  ++(d_statistics.d_lemmasInfer);

  // call the trusted lemma, without caching
  return trustedLemma(tlem, p, false);
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
