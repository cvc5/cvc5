/*********************                                                        */
/*! \file output_channel.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the output channel for the theory of strings.
 **/

#include "theory/strings/output_channel.h"

#include "expr/kind.h"
#include "options/strings_options.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings.h"
#include "theory/strings/theory_strings_rewriter.h"
#include "theory/strings/theory_strings_utils.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

OutputChannelStrings::OutputChannelStrings(TheoryStrings& p,
                                           context::Context* c,
                                           context::UserContext* u,
                                           eq::EqualityEngine& ee,
                                           OutputChannel& out)
    : d_parent(p), d_ee(ee), d_out(out), d_keep(c)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

bool OutputChannelStrings::sendInternalInference(std::vector<Node>& exp,
                                                 Node conc,
                                                 const char* c)
{
  if (conc.getKind() == AND
      || (conc.getKind() == NOT && conc[0].getKind() == OR))
  {
    Node conj = conc.getKind() == AND ? conc : conc[0];
    bool pol = conc.getKind() == AND;
    bool ret = true;
    for (const Node& cc : conj)
    {
      bool retc = sendInternalInference(exp, pol ? cc : cc.negate(), c);
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
      if (!lit[i].isConst() && !hasTerm(lit[i]))
      {
        // introduces a new non-constant term, do not infer
        return false;
      }
    }
    // does it already hold?
    if (pol ? areEqual(lit[0], lit[1]) : areDisequal(lit[0], lit[1]))
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
  else if (!hasTerm(lit))
  {
    // introduces a new non-constant term, do not infer
    return false;
  }
  else if (areEqual(lit, pol ? d_true : d_false))
  {
    // already holds
    return true;
  }
  sendInference(exp, conc, c);
  return true;
}

void OutputChannelStrings::sendInference(std::vector<Node>& exp,
                                         std::vector<Node>& exp_n,
                                         Node eq,
                                         const char* c,
                                         bool asLemma)
{
  eq = eq.isNull() ? d_false : Rewriter::rewrite(eq);
  if (eq == d_true)
  {
    return;
  }
  if (Trace.isOn("strings-infer-debug"))
  {
    Trace("strings-infer-debug")
        << "By " << c << ", infer : " << eq << " from: " << std::endl;
    for (unsigned i = 0; i < exp.size(); i++)
    {
      Trace("strings-infer-debug") << "  " << exp[i] << std::endl;
    }
    for (unsigned i = 0; i < exp_n.size(); i++)
    {
      Trace("strings-infer-debug") << "  N:" << exp_n[i] << std::endl;
    }
  }
  // check if we should send a lemma or an inference
  if (asLemma || eq == d_false || eq.getKind() == OR || !exp_n.empty()
      || options::stringInferAsLemmas())
  {
    Node eq_exp;
    if (options::stringRExplainLemmas())
    {
      eq_exp = d_parent.mkExplain(exp, exp_n);
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
    sendLemma(eq_exp, eq, c);
  }
  else
  {
    sendInfer(utils::mkAnd(exp), eq, c);
  }
}

void OutputChannelStrings::sendInference(std::vector<Node>& exp,
                                         Node eq,
                                         const char* c,
                                         bool asLemma)
{
  std::vector<Node> exp_n;
  sendInference(exp, exp_n, eq, c, asLemma);
}

void OutputChannelStrings::sendLemma(Node ant, Node conc, const char* c)
{
  if (conc.isNull() || conc == d_false)
  {
    Trace("strings-conflict")
        << "Strings::Conflict : " << c << " : " << ant << std::endl;
    Trace("strings-lemma") << "Strings::Conflict : " << c << " : " << ant
                           << std::endl;
    Trace("strings-assert")
        << "(assert (not " << ant << ")) ; conflict " << c << std::endl;
    d_out.conflict(ant);
    d_parent.d_conflict = true;
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
  Trace("strings-lemma") << "Strings::Lemma " << c << " : " << lem << std::endl;
  Trace("strings-assert") << "(assert " << lem << ") ; lemma " << c
                          << std::endl;
  d_pending_lem.push_back(lem);
}

void OutputChannelStrings::sendInfer(Node eq_exp, Node eq, const char* c)
{
  if (options::stringInferSym())
  {
    std::vector<Node> vars;
    std::vector<Node> subs;
    std::vector<Node> unproc;
    inferSubstitutionProxyVars(eq_exp, vars, subs, unproc);
    if (unproc.empty())
    {
      Node eqs =
          eq.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
      if (Trace.isOn("strings-lemma-debug"))
      {
        Trace("strings-lemma-debug") << "Strings::Infer " << eq << " from "
                                     << eq_exp << " by " << c << std::endl;
        Trace("strings-lemma-debug")
            << "Strings::Infer Alternate : " << eqs << std::endl;
        for (unsigned i = 0; i < vars.size(); i++)
        {
          Trace("strings-lemma-debug")
              << "  " << vars[i] << " -> " << subs[i] << std::endl;
        }
      }
      sendLemma(d_true, eqs, c);
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
                         << " by " << c << std::endl;
  Trace("strings-assert") << "(assert (=> " << eq_exp << " " << eq
                          << ")) ; infer " << c << std::endl;
  d_pending.push_back(eq);
  d_pending_exp[eq] = eq_exp;
  d_keep.insert(eq);
  d_keep.insert(eq_exp);
}

bool OutputChannelStrings::sendSplit(Node a, Node b, const char* c, bool preq)
{
  Node eq = a.eqNode(b);
  eq = Rewriter::rewrite(eq);
  if (eq.isConst())
  {
    return false;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node lemma_or = nm->mkNode(OR, eq, nm->mkNode(NOT, eq));
  Trace("strings-lemma") << "Strings::Lemma " << c << " SPLIT : " << lemma_or
                         << std::endl;
  d_pending_lem.push_back(lemma_or);
  sendPhaseRequirement(eq, preq);
  return true;
}

void OutputChannelStrings::sendPhaseRequirement(Node lit, bool pol)
{
  d_pending_req_phase[lit] = pol;
}

Node OutputChannelStrings::getRepresentative(Node t)
{
  if (d_ee.hasTerm(t))
  {
    return d_ee.getRepresentative(t);
  }
  return t;
}

bool OutputChannelStrings::hasTerm(Node a) { return d_ee.hasTerm(a); }

bool OutputChannelStrings::areEqual(Node a, Node b)
{
  if (a == b)
  {
    return true;
  }
  else if (hasTerm(a) && hasTerm(b))
  {
    return d_ee.areEqual(a, b);
  }
  return false;
}

bool OutputChannelStrings::areDisequal(Node a, Node b)
{
  if (a == b)
  {
    return false;
  }
  if (hasTerm(a) && hasTerm(b))
  {
    Node ar = d_ee.getRepresentative(a);
    Node br = d_ee.getRepresentative(b);
    return (ar != br && ar.isConst() && br.isConst())
           || d_ee.areDisequal(ar, br, false);
  }
  Node ar = getRepresentative(a);
  Node br = getRepresentative(b);
  return ar != br && ar.isConst() && br.isConst();
}

void OutputChannelStrings::doPendingFacts()
{
  size_t i = 0;
  while (!hasConflict() && i < d_pending.size())
  {
    Node fact = d_pending[i];
    Node exp = d_pending_exp[fact];
    if (fact.getKind() == AND)
    {
      for (const Node& lit : fact)
      {
        bool polarity = lit.getKind() != NOT;
        TNode atom = polarity ? lit : lit[0];
        d_parent.assertPendingFact(atom, polarity, exp);
      }
    }
    else
    {
      bool polarity = fact.getKind() != NOT;
      TNode atom = polarity ? fact : fact[0];
      d_parent.assertPendingFact(atom, polarity, exp);
    }
    i++;
  }
  d_pending.clear();
  d_pending_exp.clear();
}

void OutputChannelStrings::doPendingLemmas()
{
  if (!hasConflict())
  {
    for (const Node& lc : d_pending_lem)
    {
      Trace("strings-pending") << "Process pending lemma : " << lc << std::endl;
      d_out.lemma(lc);
    }
    for (const std::pair<const Node, bool>& prp : d_pending_req_phase)
    {
      Trace("strings-pending") << "Require phase : " << prp.first
                               << ", polarity = " << prp.second << std::endl;
      d_out.requirePhase(prp.first, prp.second);
    }
  }
  d_pending_lem.clear();
  d_pending_req_phase.clear();
}

bool OutputChannelStrings::hasConflict() const { return d_parent.d_conflict; }

void OutputChannelStrings::inferSubstitutionProxyVars(
    Node n,
    std::vector<Node>& vars,
    std::vector<Node>& subs,
    std::vector<Node>& unproc) const
{
  if (n.getKind() == AND)
  {
    for (const Node& nc : n)
    {
      inferSubstitutionProxyVars(nc, vars, subs, unproc);
    }
    return;
  }
  if (n.getKind() == EQUAL)
  {
    Node ns = n.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
    ns = Rewriter::rewrite(ns);
    if (ns.getKind() == EQUAL)
    {
      Node s;
      Node v;
      for (unsigned i = 0; i < 2; i++)
      {
        Node ss;
        if (ns[i].getAttribute(StringsProxyVarAttribute()))
        {
          // it is a proxy variable
          ss = ns[i];
        }
        else if (ns[i].isConst())
        {
          ss = d_parent.getProxyVariableFor(ns[i]);
        }
        if (!ss.isNull())
        {
          v = ns[1 - i];
          if (v.getNumChildren() == 0)
          {
            if (s.isNull())
            {
              s = ss;
            }
            else
            {
              // both sides involved in proxy var
              if (ss == s)
              {
                // it is a trivial equality, e.g. between a proxy variable
                // and its definition
                return;
              }
              else
              {
                s = Node::null();
              }
            }
          }
        }
      }
      if (!s.isNull())
      {
        subs.push_back(s);
        vars.push_back(v);
        return;
      }
    }
    else
    {
      n = ns;
    }
  }
  if (n != d_true)
  {
    unproc.push_back(n);
  }
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
