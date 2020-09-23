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
    : TheoryInferenceManager(t, s, pnm),
      d_state(s),
      d_termReg(tr),
      d_extt(e),
      d_statistics(statistics)
{
  NodeManager* nm = NodeManager::currentNM();
  d_zero = nm->mkConst(Rational(0));
  d_one = nm->mkConst(Rational(1));
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
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
  eq = eq.isNull() ? d_false : Rewriter::rewrite(eq);
  if (eq == d_true)
  {
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
      // we must fully explain it
      Node conf = mkExplain(ii.d_ant);
      Trace("strings-assert") << "(assert (not " << conf << ")) ; conflict "
                              << ii.d_id << std::endl;
      ++(d_statistics.d_conflictsInfer);
      // only keep stats if we process it here
      d_statistics.d_inferences << ii.d_id;
      d_out.conflict(conf);
      d_state.notifyInConflict();
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
            << "  non-trivial exp : " << u << std::endl;
      }
    }
  }
  Trace("strings-infer-debug") << "...as fact" << std::endl;
  // add to pending, to be processed as a fact
  d_pending.push_back(ii);
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
    exp.push_back(lit);
  }
}

void InferenceManager::doPendingFacts()
{
  size_t i = 0;
  while (!d_state.isInConflict() && i < d_pending.size())
  {
    InferInfo& ii = d_pending[i];
    // At this point, ii should be a "fact", i.e. something whose conclusion
    // should be added as a normal equality or predicate to the equality engine
    // with no new external assumptions (ii.d_noExplain).
    Assert(ii.isFact());
    Node facts = ii.d_conc;
    Node exp = utils::mkAnd(ii.d_ant);
    Trace("strings-assert") << "(assert (=> " << exp << " " << facts
                            << ")) ; fact " << ii.d_id << std::endl;
    // only keep stats if we process it here
    Trace("strings-lemma") << "Strings::Fact: " << facts << " from " << exp
                           << " by " << ii.d_id << std::endl;
    d_statistics.d_inferences << ii.d_id;
    // assert it as a pending fact
    if (facts.getKind() == AND)
    {
      for (const Node& fact : facts)
      {
        bool polarity = fact.getKind() != NOT;
        TNode atom = polarity ? fact : fact[0];
        // no double negation or double (conjunctive) conclusions
        Assert(atom.getKind() != NOT && atom.getKind() != AND);
        assertInternalFact(atom, polarity, exp);
      }
    }
    else
    {
      bool polarity = facts.getKind() != NOT;
      TNode atom = polarity ? facts : facts[0];
      // no double negation or double (conjunctive) conclusions
      Assert(atom.getKind() != NOT && atom.getKind() != AND);
      assertInternalFact(atom, polarity, exp);
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
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0, psize = d_pendingLem.size(); i < psize; i++)
  {
    InferInfo& ii = d_pendingLem[i];
    Assert(!ii.isTrivial());
    Assert(!ii.isConflict());
    // get the explanation
    Node eqExp;
    if (options::stringRExplainLemmas())
    {
      eqExp = mkExplain(ii.d_ant, ii.d_noExplain);
    }
    else
    {
      std::vector<Node> ev;
      ev.insert(ev.end(), ii.d_ant.begin(), ii.d_ant.end());
      eqExp = utils::mkAnd(ev);
    }
    // make the lemma node
    Node lem = ii.d_conc;
    if (eqExp != d_true)
    {
      lem = nm->mkNode(IMPLIES, eqExp, lem);
    }
    Trace("strings-pending") << "Process pending lemma : " << lem << std::endl;
    Trace("strings-assert")
        << "(assert " << lem << ") ; lemma " << ii.d_id << std::endl;
    Trace("strings-lemma") << "Strings::Lemma: " << lem << " by " << ii.d_id
                           << std::endl;
    // only keep stats if we process it here
    d_statistics.d_inferences << ii.d_id;
    ++(d_statistics.d_lemmasInfer);

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
    LemmaProperty p = LemmaProperty::NONE;
    if (ii.d_id == Inference::REDUCTION)
    {
      p |= LemmaProperty::NEEDS_JUSTIFY;
    }
    d_out.lemma(lem, p);
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

bool InferenceManager::hasProcessed() const
{
  return d_state.isInConflict() || !d_pendingLem.empty() || !d_pending.empty();
}

Node InferenceManager::mkExplain(const std::vector<Node>& a) const
{
  std::vector<Node> noExplain;
  return mkExplain(a, noExplain);
}

Node InferenceManager::mkExplain(const std::vector<Node>& a,
                                 const std::vector<Node>& noExplain) const
{
  std::vector<TNode> antec_exp;
  // copy to processing vector
  std::vector<Node> aconj;
  for (const Node& ac : a)
  {
    utils::flattenOp(AND, ac, aconj);
  }
  for (const Node& apc : aconj)
  {
    if (std::find(noExplain.begin(), noExplain.end(), apc) != noExplain.end())
    {
      if (std::find(antec_exp.begin(), antec_exp.end(), apc) == antec_exp.end())
      {
        Debug("strings-explain")
            << "Add to explanation (new literal) " << apc << std::endl;
        antec_exp.push_back(apc);
      }
      continue;
    }
    Assert(apc.getKind() != AND);
    Debug("strings-explain") << "Add to explanation " << apc << std::endl;
    if (apc.getKind() == NOT && apc[0].getKind() == EQUAL)
    {
      Assert(d_ee->hasTerm(apc[0][0]));
      Assert(d_ee->hasTerm(apc[0][1]));
      // ensure that we are ready to explain the disequality
      AlwaysAssert(d_ee->areDisequal(apc[0][0], apc[0][1], true));
    }
    Assert(apc.getKind() != EQUAL || d_ee->areEqual(apc[0], apc[1]));
    // now, explain
    explain(apc, antec_exp);
  }
  Node ant;
  if (antec_exp.empty())
  {
    ant = d_true;
  }
  else if (antec_exp.size() == 1)
  {
    ant = antec_exp[0];
  }
  else
  {
    ant = NodeManager::currentNM()->mkNode(AND, antec_exp);
  }
  return ant;
}

void InferenceManager::explain(TNode literal,
                               std::vector<TNode>& assumptions) const
{
  Debug("strings-explain") << "Explain " << literal << " "
                           << d_state.isInConflict() << std::endl;
  bool polarity = literal.getKind() != NOT;
  TNode atom = polarity ? literal : literal[0];
  std::vector<TNode> tassumptions;
  if (atom.getKind() == EQUAL)
  {
    if (atom[0] != atom[1])
    {
      Assert(d_ee->hasTerm(atom[0]));
      Assert(d_ee->hasTerm(atom[1]));
      d_ee->explainEquality(atom[0], atom[1], polarity, tassumptions);
    }
  }
  else
  {
    d_ee->explainPredicate(atom, polarity, tassumptions);
  }
  for (const TNode a : tassumptions)
  {
    if (std::find(assumptions.begin(), assumptions.end(), a)
        == assumptions.end())
    {
      assumptions.push_back(a);
    }
  }
  if (Debug.isOn("strings-explain-debug"))
  {
    Debug("strings-explain-debug")
        << "Explanation for " << literal << " was " << std::endl;
    for (const TNode a : tassumptions)
    {
      Debug("strings-explain-debug") << "   " << a << std::endl;
    }
  }
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

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
