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
#include "theory/ext_theory.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

InferenceManager::InferenceManager(TheoryStrings& p,
                                   context::Context* c,
                                   context::UserContext* u,
                                   SolverState& s,
                                   SkolemCache& skc,
                                   OutputChannel& out,
                                   SequencesStatistics& statistics)
    : d_parent(p),
      d_state(s),
      d_skCache(skc),
      d_out(out),
      d_statistics(statistics),
      d_keep(c),
      d_proxyVar(u),
      d_proxyVarToLength(u),
      d_lengthLemmaTermsCache(u)
{
  NodeManager* nm = NodeManager::currentNM();
  d_zero = nm->mkConst(Rational(0));
  d_one = nm->mkConst(Rational(1));
  d_emptyString = nm->mkConst(::CVC4::String(""));
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
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

void InferenceManager::sendInference(const std::vector<Node>& exp,
                                     const std::vector<Node>& exp_n,
                                     Node eq,
                                     Inference infer,
                                     bool asLemma)
{
  d_statistics.d_inferences << infer;
  std::stringstream ss;
  ss << infer;
  sendInference(exp, exp_n, eq, ss.str().c_str(), asLemma);
}

void InferenceManager::sendInference(const std::vector<Node>& exp,
                                     Node eq,
                                     Inference infer,
                                     bool asLemma)
{
  d_statistics.d_inferences << infer;
  std::stringstream ss;
  ss << infer;
  sendInference(exp, eq, ss.str().c_str(), asLemma);
}

void InferenceManager::sendInference(const InferInfo& i)
{
  sendInference(i.d_ant, i.d_antn, i.d_conc, i.d_id, true);
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

Node InferenceManager::getProxyVariableFor(Node n) const
{
  NodeNodeMap::const_iterator it = d_proxyVar.find(n);
  if (it != d_proxyVar.end())
  {
    return (*it).second;
  }
  return Node::null();
}

Node InferenceManager::getSymbolicDefinition(Node n,
                                             std::vector<Node>& exp) const
{
  if (n.getNumChildren() == 0)
  {
    Node pn = getProxyVariableFor(n);
    if (pn.isNull())
    {
      return Node::null();
    }
    Node eq = n.eqNode(pn);
    eq = Rewriter::rewrite(eq);
    if (std::find(exp.begin(), exp.end(), eq) == exp.end())
    {
      exp.push_back(eq);
    }
    return pn;
  }
  std::vector<Node> children;
  if (n.getMetaKind() == metakind::PARAMETERIZED)
  {
    children.push_back(n.getOperator());
  }
  for (const Node& nc : n)
  {
    if (n.getType().isRegExp())
    {
      children.push_back(nc);
    }
    else
    {
      Node ns = getSymbolicDefinition(nc, exp);
      if (ns.isNull())
      {
        return Node::null();
      }
      else
      {
        children.push_back(ns);
      }
    }
  }
  return NodeManager::currentNM()->mkNode(n.getKind(), children);
}

Node InferenceManager::registerTerm(Node n)
{
  Assert(n.getType().isStringLike());
  NodeManager* nm = NodeManager::currentNM();
  // register length information:
  //  for variables, split on empty vs positive length
  //  for concat/const/replace, introduce proxy var and state length relation
  Node lsum;
  if (n.getKind() != STRING_CONCAT && !n.isConst())
  {
    Node lsumb = nm->mkNode(STRING_LENGTH, n);
    lsum = Rewriter::rewrite(lsumb);
    // can register length term if it does not rewrite
    if (lsum == lsumb)
    {
      registerTermAtomic(n, LENGTH_SPLIT);
      return Node::null();
    }
  }
  Node sk = d_skCache.mkSkolemCached(n, SkolemCache::SK_PURIFY, "lsym");
  StringsProxyVarAttribute spva;
  sk.setAttribute(spva, true);
  Node eq = Rewriter::rewrite(sk.eqNode(n));
  d_proxyVar[n] = sk;
  // If we are introducing a proxy for a constant or concat term, we do not
  // need to send lemmas about its length, since its length is already
  // implied.
  if (n.isConst() || n.getKind() == STRING_CONCAT)
  {
    // do not send length lemma for sk.
    registerTermAtomic(sk, LENGTH_IGNORE);
  }
  Node skl = nm->mkNode(STRING_LENGTH, sk);
  if (n.getKind() == STRING_CONCAT)
  {
    std::vector<Node> nodeVec;
    for (const Node& nc : n)
    {
      if (nc.getAttribute(StringsProxyVarAttribute()))
      {
        Assert(d_proxyVarToLength.find(nc) != d_proxyVarToLength.end());
        nodeVec.push_back(d_proxyVarToLength[nc]);
      }
      else
      {
        Node lni = nm->mkNode(STRING_LENGTH, nc);
        nodeVec.push_back(lni);
      }
    }
    lsum = nm->mkNode(PLUS, nodeVec);
    lsum = Rewriter::rewrite(lsum);
  }
  else if (n.isConst())
  {
    lsum = nm->mkConst(Rational(Word::getLength(n)));
  }
  Assert(!lsum.isNull());
  d_proxyVarToLength[sk] = lsum;
  Node ceq = Rewriter::rewrite(skl.eqNode(lsum));

  return nm->mkNode(AND, eq, ceq);
}

void InferenceManager::registerTermAtomic(Node n, LengthStatus s)
{
  if (d_lengthLemmaTermsCache.find(n) != d_lengthLemmaTermsCache.end())
  {
    return;
  }
  d_lengthLemmaTermsCache.insert(n);

  if (s == LENGTH_IGNORE)
  {
    // ignore it
    return;
  }
  std::map<Node, bool> reqPhase;
  Node lenLem = getRegisterTermAtomicLemma(n, s, reqPhase);
  if (!lenLem.isNull())
  {
    Trace("strings-lemma") << "Strings::Lemma REGISTER-TERM-ATOMIC : " << lenLem
                           << std::endl;
    Trace("strings-assert") << "(assert " << lenLem << ")" << std::endl;
    ++(d_statistics.d_lemmasRegisterTermAtomic);
    d_out.lemma(lenLem);
  }
  for (const std::pair<const Node, bool>& rp : reqPhase)
  {
    d_out.requirePhase(rp.first, rp.second);
  }
}

Node InferenceManager::getRegisterTermAtomicLemma(
    Node n, LengthStatus s, std::map<Node, bool>& reqPhase)
{
  NodeManager* nm = NodeManager::currentNM();
  Node n_len = nm->mkNode(kind::STRING_LENGTH, n);

  if (s == LENGTH_GEQ_ONE)
  {
    Node neq_empty = n.eqNode(d_emptyString).negate();
    Node len_n_gt_z = nm->mkNode(GT, n_len, d_zero);
    Node len_geq_one = nm->mkNode(AND, neq_empty, len_n_gt_z);
    Trace("strings-lemma") << "Strings::Lemma SK-GEQ-ONE : " << len_geq_one
                           << std::endl;
    Trace("strings-assert") << "(assert " << len_geq_one << ")" << std::endl;
    return len_geq_one;
  }

  if (s == LENGTH_ONE)
  {
    Node len_one = n_len.eqNode(d_one);
    Trace("strings-lemma") << "Strings::Lemma SK-ONE : " << len_one
                           << std::endl;
    Trace("strings-assert") << "(assert " << len_one << ")" << std::endl;
    return len_one;
  }
  Assert(s == LENGTH_SPLIT);

  std::vector<Node> lems;
  if (options::stringSplitEmp() || !options::stringLenGeqZ())
  {
    Node n_len_eq_z = n_len.eqNode(d_zero);
    Node n_len_eq_z_2 = n.eqNode(d_emptyString);
    Node case_empty = nm->mkNode(AND, n_len_eq_z, n_len_eq_z_2);
    case_empty = Rewriter::rewrite(case_empty);
    Node case_nempty = nm->mkNode(GT, n_len, d_zero);
    if (!case_empty.isConst())
    {
      Node lem = nm->mkNode(OR, case_empty, case_nempty);
      lems.push_back(lem);
      Trace("strings-lemma")
          << "Strings::Lemma LENGTH >= 0 : " << lem << std::endl;
      // prefer trying the empty case first
      // notice that requirePhase must only be called on rewritten literals that
      // occur in the CNF stream.
      n_len_eq_z = Rewriter::rewrite(n_len_eq_z);
      Assert(!n_len_eq_z.isConst());
      reqPhase[n_len_eq_z] = true;
      n_len_eq_z_2 = Rewriter::rewrite(n_len_eq_z_2);
      Assert(!n_len_eq_z_2.isConst());
      reqPhase[n_len_eq_z_2] = true;
    }
    else if (!case_empty.getConst<bool>())
    {
      // the rewriter knows that n is non-empty
      Trace("strings-lemma")
          << "Strings::Lemma LENGTH > 0 (non-empty): " << case_nempty
          << std::endl;
      lems.push_back(case_nempty);
    }
    else
    {
      // If n = "" ---> true or len( n ) = 0 ----> true, then we expect that
      // n ---> "". Since this method is only called on non-constants n, it must
      // be that n = "" ^ len( n ) = 0 does not rewrite to true.
      Assert(false);
    }
  }

  // additionally add len( x ) >= 0 ?
  if (options::stringLenGeqZ())
  {
    Node n_len_geq = nm->mkNode(kind::GEQ, n_len, d_zero);
    n_len_geq = Rewriter::rewrite(n_len_geq);
    lems.push_back(n_len_geq);
  }

  if (lems.empty())
  {
    return Node::null();
  }
  return lems.size() == 1 ? lems[0] : nm->mkNode(AND, lems);
}

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
  if (!d_state.isInConflict())
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

bool InferenceManager::hasProcessed() const
{
  return d_state.isInConflict() || !d_pendingLem.empty() || !d_pending.empty();
}

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
          ss = getProxyVariableFor(ns[i]);
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
    ant = NodeManager::currentNM()->mkNode(kind::AND, antec_exp);
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
void InferenceManager::setIncomplete() { d_out.setIncomplete(); }

void InferenceManager::markCongruent(Node a, Node b)
{
  Assert(a.getKind() == b.getKind());
  ExtTheory* eth = d_parent.getExtTheory();
  if (eth->hasFunctionKind(a.getKind()))
  {
    eth->markCongruent(a, b);
  }
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
