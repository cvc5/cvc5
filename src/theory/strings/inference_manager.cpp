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

InferenceManager::InferenceManager(TheoryStrings& p,
                                   context::Context* c,
                                   context::UserContext* u,
                                   eq::EqualityEngine& ee,
                                   OutputChannel& out)
    : d_parent(p), d_ee(ee), d_out(out), d_keep(c)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

bool InferenceManager::sendInternalInference(std::vector<Node>& exp,
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
      if (!lit[i].isConst() && !d_parent.hasTerm(lit[i]))
      {
        // introduces a new non-constant term, do not infer
        return false;
      }
    }
    // does it already hold?
    if (pol ? d_parent.areEqual(lit[0], lit[1])
            : d_parent.areDisequal(lit[0], lit[1]))
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
  else if (!d_parent.hasTerm(lit))
  {
    // introduces a new non-constant term, do not infer
    return false;
  }
  else if (d_parent.areEqual(lit, pol ? d_true : d_false))
  {
    // already holds
    return true;
  }
  sendInference(exp, conc, c);
  return true;
}

void InferenceManager::sendInference(const std::vector<Node>& exp,
                                     const std::vector<Node>& exp_n,
                                     Node eq,
                                     const char* c,
                                     bool asLemma)
{
  eq = eq.isNull() ? d_false : Rewriter::rewrite(eq);
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
  if (eq == d_true)
  {
    return;
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

void InferenceManager::sendInference(const std::vector<Node>& exp,
                                     Node eq,
                                     const char* c,
                                     bool asLemma)
{
  std::vector<Node> exp_n;
  sendInference(exp, exp_n, eq, c, asLemma);
}

void InferenceManager::sendInference(const InferInfo& i)
{
  std::stringstream ssi;
  ssi << i.d_id;
  sendInference(i.d_ant, i.d_antn, i.d_conc, ssi.str().c_str(), true);
}

void InferenceManager::sendLemma(Node ant, Node conc, const char* c)
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
  d_pendingLem.push_back(lem);
}

void InferenceManager::sendInfer(Node eq_exp, Node eq, const char* c)
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
        for (unsigned i = 0, nvars = vars.size(); i < nvars; i++)
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
  d_pendingExp[eq] = eq_exp;
  d_keep.insert(eq);
  d_keep.insert(eq_exp);
}

bool InferenceManager::sendSplit(Node a, Node b, const char* c, bool preq)
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
  d_pendingLem.push_back(lemma_or);
  sendPhaseRequirement(eq, preq);
  return true;
}

void InferenceManager::sendPhaseRequirement(Node lit, bool pol)
{
  lit = Rewriter::rewrite(lit);
  d_pendingReqPhase[lit] = pol;
}

void InferenceManager::doPendingFacts()
{
  size_t i = 0;
  while (!hasConflict() && i < d_pending.size())
  {
    Node fact = d_pending[i];
    Node exp = d_pendingExp[fact];
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
  d_pendingExp.clear();
}

void InferenceManager::doPendingLemmas()
{
  if (!hasConflict())
  {
    for (const Node& lc : d_pendingLem)
    {
      Trace("strings-pending") << "Process pending lemma : " << lc << std::endl;
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

bool InferenceManager::hasConflict() const { return d_parent.d_conflict; }

void InferenceManager::inferSubstitutionProxyVars(
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
        // determine whether this side has a proxy variable
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
          // if the other side is a constant or variable
          if (v.getNumChildren() == 0)
          {
            if (s.isNull())
            {
              s = ss;
            }
            else
            {
              // both sides of the equality correspond to a proxy variable
              if (ss == s)
              {
                // it is a trivial equality, e.g. between a proxy variable
                // and its definition
                return;
              }
              else
              {
                // equality between proxy variables, non-trivial
                s = Node::null();
              }
            }
          }
        }
      }
      if (!s.isNull())
      {
        // the equality can be turned into a substitution
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
