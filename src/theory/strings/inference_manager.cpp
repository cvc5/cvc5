/*********************                                                        */
/*! \file inference_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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

InferenceManager::InferenceManager(context::Context* c,
                                   context::UserContext* u,
                                   SolverState& s,
                                   TermRegistry& tr,
                                   ExtTheory& e,
                                   OutputChannel& out,
                                   SequencesStatistics& statistics)
    : d_state(s),
      d_termReg(tr),
      d_extt(e),
      d_out(out),
      d_statistics(statistics),
      d_keep(c)
{
  NodeManager* nm = NodeManager::currentNM();
  d_zero = nm->mkConst(Rational(0));
  d_one = nm->mkConst(Rational(1));
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

void InferenceManager::sendAssumption(TNode lit)
{
  bool polarity = lit.getKind() != kind::NOT;
  TNode atom = polarity ? lit : lit[0];
  // assert pending fact
  assertPendingFact(atom, polarity, lit);
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
                                     const std::vector<Node>& exp_n,
                                     Node eq,
                                     Inference infer,
                                     bool asLemma)
{
  eq = eq.isNull() ? d_false : Rewriter::rewrite(eq);
  if (Trace.isOn("strings-infer-debug"))
  {
    Trace("strings-infer-debug")
        << "By " << infer << ", infer : " << eq << " from: " << std::endl;
    for (unsigned i = 0; i < exp.size(); i++)
    {
      Trace("strings-infer-debug") << "  " << exp[i] << std::endl;
    }
    for (unsigned i = 0; i < exp_n.size(); i++)
    {
      Trace("strings-infer-debug") << "  N:" << exp_n[i] << std::endl;
    }
  }
  if (eq == d_true)
  {
    return;
  }
  // only keep stats if not trivial conclusion
  d_statistics.d_inferences << infer;
  Node atom = eq.getKind() == NOT ? eq[0] : eq;
  // check if we should send a lemma or an inference
  if (asLemma || atom == d_false || atom.getKind() == OR || !exp_n.empty()
      || options::stringInferAsLemmas())
  {
    Node eq_exp;
    if (options::stringRExplainLemmas())
    {
      eq_exp = mkExplain(exp, exp_n);
    }
    else
    {
      if (exp.empty())
      {
        eq_exp = utils::mkAnd(exp_n);
      }
      else if (exp_n.empty())
      {
        eq_exp = utils::mkAnd(exp);
      }
      else
      {
        std::vector<Node> ev;
        ev.insert(ev.end(), exp.begin(), exp.end());
        ev.insert(ev.end(), exp_n.begin(), exp_n.end());
        eq_exp = NodeManager::currentNM()->mkNode(AND, ev);
      }
    }
    // if we have unexplained literals, this lemma is not a conflict
    if (eq == d_false && !exp_n.empty())
    {
      eq = eq_exp.negate();
      eq_exp = d_true;
    }
    sendLemma(eq_exp, eq, infer);
  }
  else
  {
    sendInfer(utils::mkAnd(exp), eq, infer);
  }
}

void InferenceManager::sendInference(const std::vector<Node>& exp,
                                     Node eq,
                                     Inference infer,
                                     bool asLemma)
{
  std::vector<Node> exp_n;
  sendInference(exp, exp_n, eq, infer, asLemma);
}

void InferenceManager::sendInference(const InferInfo& i)
{
  sendInference(i.d_ant, i.d_antn, i.d_conc, i.d_id, true);
}

void InferenceManager::sendLemma(Node ant, Node conc, Inference infer)
{
  if (conc.isNull() || conc == d_false)
  {
    Trace("strings-conflict")
        << "Strings::Conflict : " << infer << " : " << ant << std::endl;
    Trace("strings-lemma") << "Strings::Conflict : " << infer << " : " << ant
                           << std::endl;
    Trace("strings-assert")
        << "(assert (not " << ant << ")) ; conflict " << infer << std::endl;
    ++(d_statistics.d_conflictsInfer);
    d_out.conflict(ant);
    d_state.setConflict();
    return;
  }
  Node lem;
  if (ant == d_true)
  {
    lem = conc;
  }
  else
  {
    lem = NodeManager::currentNM()->mkNode(IMPLIES, ant, conc);
  }
  Trace("strings-lemma") << "Strings::Lemma " << infer << " : " << lem
                         << std::endl;
  Trace("strings-assert") << "(assert " << lem << ") ; lemma " << infer
                          << std::endl;
  d_pendingLem.push_back(lem);
}

void InferenceManager::sendInfer(Node eq_exp, Node eq, Inference infer)
{
  if (options::stringInferSym())
  {
    std::vector<Node> vars;
    std::vector<Node> subs;
    std::vector<Node> unproc;
    d_termReg.inferSubstitutionProxyVars(eq_exp, vars, subs, unproc);
    if (unproc.empty())
    {
      Node eqs =
          eq.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
      if (Trace.isOn("strings-lemma-debug"))
      {
        Trace("strings-lemma-debug") << "Strings::Infer " << eq << " from "
                                     << eq_exp << " by " << infer << std::endl;
        Trace("strings-lemma-debug")
            << "Strings::Infer Alternate : " << eqs << std::endl;
        for (unsigned i = 0, nvars = vars.size(); i < nvars; i++)
        {
          Trace("strings-lemma-debug")
              << "  " << vars[i] << " -> " << subs[i] << std::endl;
        }
      }
      sendLemma(d_true, eqs, infer);
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
  Trace("strings-lemma") << "Strings::Infer " << eq << " from " << eq_exp
                         << " by " << infer << std::endl;
  Trace("strings-assert") << "(assert (=> " << eq_exp << " " << eq
                          << ")) ; infer " << infer << std::endl;
  d_pending.push_back(eq);
  d_pendingExp[eq] = eq_exp;
  d_keep.insert(eq);
  d_keep.insert(eq_exp);
}

bool InferenceManager::sendSplit(Node a, Node b, Inference infer, bool preq)
{
  Node eq = a.eqNode(b);
  eq = Rewriter::rewrite(eq);
  if (eq.isConst())
  {
    return false;
  }
  // update statistics
  d_statistics.d_inferences << infer;
  NodeManager* nm = NodeManager::currentNM();
  Node lemma_or = nm->mkNode(OR, eq, nm->mkNode(NOT, eq));
  Trace("strings-lemma") << "Strings::Lemma " << infer
                         << " SPLIT : " << lemma_or << std::endl;
  d_pendingLem.push_back(lemma_or);
  sendPhaseRequirement(eq, preq);
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
    Node fact = d_pending[i];
    Node exp = d_pendingExp[fact];
    if (fact.getKind() == AND)
    {
      for (const Node& lit : fact)
      {
        bool polarity = lit.getKind() != NOT;
        TNode atom = polarity ? lit : lit[0];
        assertPendingFact(atom, polarity, exp);
      }
    }
    else
    {
      bool polarity = fact.getKind() != NOT;
      TNode atom = polarity ? fact : fact[0];
      assertPendingFact(atom, polarity, exp);
    }
    i++;
  }
  d_pending.clear();
  d_pendingExp.clear();
}

void InferenceManager::doPendingLemmas()
{
  if (!d_state.isInConflict())
  {
    for (const Node& lc : d_pendingLem)
    {
      Trace("strings-pending") << "Process pending lemma : " << lc << std::endl;
      ++(d_statistics.d_lemmasInfer);
      d_out.lemma(lc);
    }
    for (const std::pair<const Node, bool>& prp : d_pendingReqPhase)
    {
      Trace("strings-pending") << "Require phase : " << prp.first
                               << ", polarity = " << prp.second << std::endl;
      d_out.requirePhase(prp.first, prp.second);
    }
  }
  d_pendingLem.clear();
  d_pendingReqPhase.clear();
}

void InferenceManager::assertPendingFact(Node atom, bool polarity, Node exp)
{
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  Trace("strings-pending") << "Assert pending fact : " << atom << " "
                           << polarity << " from " << exp << std::endl;
  Assert(atom.getKind() != OR) << "Infer error: a split.";
  if (atom.getKind() == EQUAL)
  {
    // we must ensure these terms are registered
    Trace("strings-pending-debug") << "  Register term" << std::endl;
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
    Trace("strings-pending-debug") << "  Now assert equality" << std::endl;
    ee->assertEquality(atom, polarity, exp);
    Trace("strings-pending-debug") << "  Finished assert equality" << std::endl;
  }
  else
  {
    ee->assertPredicate(atom, polarity, exp);
    if (atom.getKind() == STRING_IN_REGEXP)
    {
      if (polarity && atom[1].getKind() == REGEXP_CONCAT)
      {
        Node eqc = ee->getRepresentative(atom[0]);
        d_state.addEndpointsToEqcInfo(atom, atom[1], eqc);
      }
    }
  }
  // process the conflict
  if (!d_state.isInConflict())
  {
    Node pc = d_state.getPendingConflict();
    if (!pc.isNull())
    {
      std::vector<Node> a;
      a.push_back(pc);
      Trace("strings-pending")
          << "Process pending conflict " << pc << std::endl;
      Node conflictNode = mkExplain(a);
      d_state.setConflict();
      Trace("strings-conflict")
          << "CONFLICT: Eager prefix : " << conflictNode << std::endl;
      ++(d_statistics.d_conflictsEagerPrefix);
      d_out.conflict(conflictNode);
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

Node InferenceManager::mkExplain(const std::vector<Node>& a) const
{
  std::vector<Node> an;
  return mkExplain(a, an);
}

Node InferenceManager::mkExplain(const std::vector<Node>& a,
                                 const std::vector<Node>& an) const
{
  std::vector<TNode> antec_exp;
  // copy to processing vector
  std::vector<Node> aconj;
  for (const Node& ac : a)
  {
    utils::flattenOp(AND, ac, aconj);
  }
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  for (const Node& apc : aconj)
  {
    Assert(apc.getKind() != AND);
    Debug("strings-explain") << "Add to explanation " << apc << std::endl;
    if (apc.getKind() == NOT && apc[0].getKind() == EQUAL)
    {
      Assert(ee->hasTerm(apc[0][0]));
      Assert(ee->hasTerm(apc[0][1]));
      // ensure that we are ready to explain the disequality
      AlwaysAssert(ee->areDisequal(apc[0][0], apc[0][1], true));
    }
    Assert(apc.getKind() != EQUAL || ee->areEqual(apc[0], apc[1]));
    // now, explain
    explain(apc, antec_exp);
  }
  for (const Node& anc : an)
  {
    if (std::find(antec_exp.begin(), antec_exp.end(), anc) == antec_exp.end())
    {
      Debug("strings-explain")
          << "Add to explanation (new literal) " << anc << std::endl;
      antec_exp.push_back(anc);
    }
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
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  bool polarity = literal.getKind() != NOT;
  TNode atom = polarity ? literal : literal[0];
  std::vector<TNode> tassumptions;
  if (atom.getKind() == EQUAL)
  {
    if (atom[0] != atom[1])
    {
      Assert(ee->hasTerm(atom[0]));
      Assert(ee->hasTerm(atom[1]));
      ee->explainEquality(atom[0], atom[1], polarity, tassumptions);
    }
  }
  else
  {
    ee->explainPredicate(atom, polarity, tassumptions);
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
