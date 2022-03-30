/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Kshitij Bansal
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sets theory implementation.
 */

#include "theory/sets/theory_sets_private.h"

#include <algorithm>
#include <climits>

#include "expr/emptyset.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/sets_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/sets/normal_form.h"
#include "theory/sets/theory_sets.h"
#include "theory/theory_model.h"
#include "util/rational.h"
#include "util/result.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace sets {

TheorySetsPrivate::TheorySetsPrivate(Env& env,
                                     TheorySets& external,
                                     SolverState& state,
                                     InferenceManager& im,
                                     SkolemCache& skc,
                                     ProofNodeManager* pnm,
                                     CarePairArgumentCallback& cpacb)
    : EnvObj(env),
      d_deq(context()),
      d_termProcessed(userContext()),
      d_fullCheckIncomplete(false),
      d_fullCheckIncompleteId(IncompleteId::UNKNOWN),
      d_external(external),
      d_state(state),
      d_im(im),
      d_skCache(skc),
      d_treg(d_env, state, im, skc, pnm),
      d_rels(new TheorySetsRels(d_env, state, im, skc, d_treg)),
      d_cardSolver(new CardinalityExtension(d_env, state, im, d_treg)),
      d_rels_enabled(false),
      d_card_enabled(false),
      d_cpacb(cpacb)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_zero = NodeManager::currentNM()->mkConstInt(Rational(0));
}

TheorySetsPrivate::~TheorySetsPrivate()
{
  for (std::pair<const Node, EqcInfo*>& current_pair : d_eqc_info)
  {
    delete current_pair.second;
  }
}

void TheorySetsPrivate::finishInit()
{
  d_equalityEngine = d_external.getEqualityEngine();
  Assert(d_equalityEngine != nullptr);
}

void TheorySetsPrivate::eqNotifyNewClass(TNode t)
{
  if (t.getKind() == kind::SET_SINGLETON || t.getKind() == kind::SET_EMPTY)
  {
    EqcInfo* e = getOrMakeEqcInfo(t, true);
    e->d_singleton = t;
  }
}

void TheorySetsPrivate::eqNotifyMerge(TNode t1, TNode t2)
{
  if (!d_state.isInConflict() && t1.getType().isSet())
  {
    Trace("sets-prop-debug")
        << "Merge " << t1 << " and " << t2 << "..." << std::endl;
    Node s1, s2;
    EqcInfo* e2 = getOrMakeEqcInfo(t2);
    if (e2)
    {
      s2 = e2->d_singleton;
      EqcInfo* e1 = getOrMakeEqcInfo(t1);
      Trace("sets-prop-debug") << "Merging singletons..." << std::endl;
      if (e1)
      {
        s1 = e1->d_singleton;
        if (!s1.isNull() && !s2.isNull())
        {
          if (s1.getKind() == s2.getKind())
          {
            Trace("sets-prop") << "Propagate eq inference : " << s1
                               << " == " << s2 << std::endl;
            // infer equality between elements of singleton
            Node exp = s1.eqNode(s2);
            Node eq = s1[0].eqNode(s2[0]);
            d_im.assertSetsFact(eq, true, InferenceId::SETS_SINGLETON_EQ, exp);
          }
          else
          {
            // singleton equal to emptyset, conflict
            Trace("sets-prop")
                << "Propagate conflict : " << s1 << " == " << s2 << std::endl;
            Node eqs = s1.eqNode(s2);
            d_im.conflict(eqs, InferenceId::SETS_EQ_CONFLICT);
            return;
          }
        }
      }
      else
      {
        // copy information
        e1 = getOrMakeEqcInfo(t1, true);
        e1->d_singleton.set(e2->d_singleton);
      }
    }
    // merge membership list
    Trace("sets-prop-debug") << "Copying membership list..." << std::endl;
    // if s1 has a singleton or empty set and s2 does not, we may have new
    // inferences to process.
    Node checkSingleton = s2.isNull() ? s1 : Node::null();
    std::vector<Node> facts;
    // merge the membership list in the state, which may produce facts or
    // conflicts to propagate
    if (!d_state.merge(t1, t2, facts, checkSingleton))
    {
      // conflict case
      Assert(facts.size() == 1);
      Trace("sets-prop") << "Propagate eq-mem conflict : " << facts[0]
                         << std::endl;
      d_im.conflict(facts[0], InferenceId::SETS_EQ_MEM_CONFLICT);
      return;
    }
    for (const Node& f : facts)
    {
      Assert(f.getKind() == kind::IMPLIES);
      Trace("sets-prop") << "Propagate eq-mem eq inference : " << f[0] << " => "
                         << f[1] << std::endl;
      d_im.assertSetsFact(f[1], true, InferenceId::SETS_EQ_MEM, f[0]);
    }
  }
}

void TheorySetsPrivate::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  if (t1.getType().isSet())
  {
    Node eq = t1.eqNode(t2);
    if (d_deq.find(eq) == d_deq.end())
    {
      d_deq[eq] = true;
    }
  }
}

TheorySetsPrivate::EqcInfo::EqcInfo(context::Context* c) : d_singleton(c) {}

TheorySetsPrivate::EqcInfo* TheorySetsPrivate::getOrMakeEqcInfo(TNode n,
                                                                bool doMake)
{
  std::map<Node, EqcInfo*>::iterator eqc_i = d_eqc_info.find(n);
  if (eqc_i == d_eqc_info.end())
  {
    EqcInfo* ei = NULL;
    if (doMake)
    {
      ei = new EqcInfo(context());
      d_eqc_info[n] = ei;
    }
    return ei;
  }
  else
  {
    return eqc_i->second;
  }
}

void TheorySetsPrivate::fullEffortReset()
{
  Assert(d_equalityEngine->consistent());
  d_fullCheckIncomplete = false;
  d_fullCheckIncompleteId = IncompleteId::UNKNOWN;
  d_most_common_type.clear();
  d_most_common_type_term.clear();
  d_card_enabled = false;
  d_rels_enabled = false;
  // reset the state object
  d_state.reset();
  // reset the inference manager
  d_im.reset();
  d_im.clearPendingLemmas();
  // reset the cardinality solver
  d_cardSolver->reset();
}

void TheorySetsPrivate::fullEffortCheck()
{
  Trace("sets") << "----- Full effort check ------" << std::endl;
  do
  {
    Assert(!d_im.hasPendingLemma() || d_im.hasSent());

    Trace("sets") << "...iterate full effort check..." << std::endl;
    fullEffortReset();

    Trace("sets-eqc") << "Equality Engine:" << std::endl;
    std::map<TypeNode, unsigned> eqcTypeCount;
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(d_equalityEngine);
    while (!eqcs_i.isFinished())
    {
      Node eqc = (*eqcs_i);
      bool isSet = false;
      TypeNode tn = eqc.getType();
      d_state.registerEqc(tn, eqc);
      eqcTypeCount[tn]++;
      // common type node and term
      TypeNode tnc;
      Node tnct;
      if (tn.isSet())
      {
        isSet = true;
        tnc = tn.getSetElementType();
        tnct = eqc;
      }
      Trace("sets-eqc") << "[" << eqc << "] : ";
      eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, d_equalityEngine);
      while (!eqc_i.isFinished())
      {
        Node n = (*eqc_i);
        if (n != eqc)
        {
          if (TraceIsOn("sets-eqc"))
          {
            Trace("sets-eqc") << n;
            if (n.isConst())
            {
              Trace("sets-eqc") << " (const) ";
            }
          }
        }
        TypeNode tnn = n.getType();
        if (isSet)
        {
          Assert(tnn.isSet());
          TypeNode tnnel = tnn.getSetElementType();
          tnc = TypeNode::mostCommonTypeNode(tnc, tnnel);
          Assert(!tnc.isNull());
          // update the common type term
          if (tnc == tnnel)
          {
            tnct = n;
          }
        }
        // register it with the state
        d_state.registerTerm(eqc, tnn, n);
        Kind nk = n.getKind();
        if (nk == kind::SET_SINGLETON)
        {
          // ensure the proxy has been introduced
          d_treg.getProxy(n);
        }
        else if (nk == kind::SET_CARD)
        {
          d_card_enabled = true;
          // register it with the cardinality solver
          d_cardSolver->registerTerm(n);
          if (d_im.hasSent())
          {
            break;
          }
          // if we do not handle the kind, set incomplete
          Kind nk0 = n[0].getKind();
          // some kinds of cardinality we cannot handle
          if (d_rels->isRelationKind(nk0))
          {
            d_fullCheckIncomplete = true;
            d_fullCheckIncompleteId = IncompleteId::SETS_RELS_CARD;
            Trace("sets-incomplete")
                << "Sets : incomplete because of " << n << "." << std::endl;
            // TODO (#1124):  The issue can be divided into 4 parts
            // 1- Supporting the universe cardinality for finite types with
            // finite cardinality (done)
            // 2- Supporting the universe cardinality for uninterpreted sorts
            // with finite-model-find (pending) See the implementation of
            //    CardinalityExtension::checkCardinalityExtended
            // 3- Supporting the universe cardinality for non-finite types
            // (done)
            // 4- Supporting cardinality for relations (hard)
          }
        }
        else if (d_rels->isRelationKind(nk))
        {
          d_rels_enabled = true;
        }
        ++eqc_i;
      }
      if (isSet)
      {
        Assert(tnct.getType().getSetElementType() == tnc);
        d_most_common_type[eqc] = tnc;
        d_most_common_type_term[eqc] = tnct;
      }
      Trace("sets-eqc") << std::endl;
      ++eqcs_i;
    }

    Trace("sets-eqc") << "...finished equality engine." << std::endl;

    if (TraceIsOn("sets-state"))
    {
      Trace("sets-state") << "Equivalence class counters:" << std::endl;
      for (std::pair<const TypeNode, unsigned>& ec : eqcTypeCount)
      {
        Trace("sets-state")
            << "  " << ec.first << " -> " << ec.second << std::endl;
      }
    }

    // We may have sent lemmas while registering the terms in the loop above,
    // e.g. the cardinality solver.
    if (d_im.hasSent())
    {
      continue;
    }
    if (TraceIsOn("sets-mem"))
    {
      const std::vector<Node>& sec = d_state.getSetsEqClasses();
      for (const Node& s : sec)
      {
        Trace("sets-mem") << "Eqc " << s << " : ";
        const std::map<Node, Node>& smem = d_state.getMembers(s);
        if (!smem.empty())
        {
          Trace("sets-mem") << "Memberships : ";
          for (const std::pair<const Node, Node>& it2 : smem)
          {
            Trace("sets-mem") << it2.first << " ";
          }
        }
        Node ss = d_state.getSingletonEqClass(s);
        if (!ss.isNull())
        {
          Trace("sets-mem") << " : Singleton : " << ss;
        }
        Trace("sets-mem") << std::endl;
      }
    }
    d_im.doPendingLemmas();
    if (d_im.hasSent())
    {
      continue;
    }
    // check downwards closure
    checkDownwardsClosure();
    d_im.doPendingLemmas();
    if (d_im.hasSent())
    {
      continue;
    }
    // check upwards closure
    checkUpwardsClosure();
    d_im.doPendingLemmas();
    if (d_im.hasSent())
    {
      continue;
    }
    // check disequalities
    checkDisequalities();
    d_im.doPendingLemmas();
    if (d_im.hasSent())
    {
      continue;
    }
    // check reduce comprehensions
    checkReduceComprehensions();

    d_im.doPendingLemmas();
    if (d_im.hasSent())
    {
      continue;
    }
    if (d_card_enabled)
    {
      // call the check method of the cardinality solver
      d_cardSolver->check();
      if (d_im.hasSent())
      {
        continue;
      }
    }
    if (d_rels_enabled)
    {
      // call the check method of the relations solver
      d_rels->check(Theory::EFFORT_FULL);
    }
  } while (!d_im.hasSentLemma() && !d_state.isInConflict()
           && d_im.hasSentFact());
  Assert(!d_im.hasPendingLemma() || d_im.hasSent());
  Trace("sets") << "----- End full effort check, conflict="
                << d_state.isInConflict() << ", lemma=" << d_im.hasSentLemma()
                << std::endl;
}

void TheorySetsPrivate::checkDownwardsClosure()
{
  Trace("sets") << "TheorySetsPrivate: check downwards closure..." << std::endl;
  // downwards closure
  const std::vector<Node>& sec = d_state.getSetsEqClasses();
  for (const Node& s : sec)
  {
    const std::vector<Node>& nvsets = d_state.getNonVariableSets(s);
    if (!nvsets.empty())
    {
      const std::map<Node, Node>& smem = d_state.getMembers(s);
      for (const Node& nv : nvsets)
      {
        if (!d_state.isCongruent(nv))
        {
          for (const std::pair<const Node, Node>& it2 : smem)
          {
            Node mem = it2.second;
            Node eq_set = nv;
            Assert(d_equalityEngine->areEqual(mem[1], eq_set));
            if (mem[1] != eq_set)
            {
              Trace("sets-debug") << "Downwards closure based on " << mem
                                  << ", eq_set = " << eq_set << std::endl;
              if (!options().sets.setsProxyLemmas)
              {
                Node nmem = NodeManager::currentNM()->mkNode(
                    kind::SET_MEMBER, mem[0], eq_set);
                nmem = rewrite(nmem);
                std::vector<Node> exp;
                exp.push_back(mem);
                exp.push_back(mem[1].eqNode(eq_set));
                d_im.assertInference(nmem, InferenceId::SETS_DOWN_CLOSURE, exp);
                if (d_state.isInConflict())
                {
                  return;
                }
              }
              else
              {
                // use proxy set
                Node k = d_treg.getProxy(eq_set);
                Node pmem = NodeManager::currentNM()->mkNode(
                    kind::SET_MEMBER, mem[0], k);
                Node nmem = NodeManager::currentNM()->mkNode(
                    kind::SET_MEMBER, mem[0], eq_set);
                nmem = rewrite(nmem);
                std::vector<Node> exp;
                if (d_state.areEqual(mem, pmem))
                {
                  exp.push_back(pmem);
                }
                else
                {
                  nmem = NodeManager::currentNM()->mkNode(
                      kind::OR, pmem.negate(), nmem);
                }
                d_im.assertInference(nmem, InferenceId::SETS_DOWN_CLOSURE, exp);
              }
            }
          }
        }
      }
    }
  }
}

void TheorySetsPrivate::checkUpwardsClosure()
{
  // upwards closure
  NodeManager* nm = NodeManager::currentNM();
  const std::map<Kind, std::map<Node, std::map<Node, Node> > >& boi =
      d_state.getBinaryOpIndex();
  for (const std::pair<const Kind, std::map<Node, std::map<Node, Node> > >&
           itb : boi)
  {
    Kind k = itb.first;
    Trace("sets") << "TheorySetsPrivate: check upwards closure " << k << "..."
                  << std::endl;
    for (const std::pair<const Node, std::map<Node, Node> >& it : itb.second)
    {
      Node r1 = it.first;
      // see if there are members in first argument r1
      const std::map<Node, Node>& r1mem = d_state.getMembers(r1);
      if (!r1mem.empty() || k == kind::SET_UNION)
      {
        for (const std::pair<const Node, Node>& it2 : it.second)
        {
          Node r2 = it2.first;
          Node term = it2.second;
          // see if there are members in second argument
          const std::map<Node, Node>& r2mem = d_state.getMembers(r2);
          const std::map<Node, Node>& r2nmem = d_state.getNegativeMembers(r2);
          if (!r2mem.empty() || k != kind::SET_INTER)
          {
            Trace("sets-debug")
                << "Checking " << term << ", members = " << (!r1mem.empty())
                << ", " << (!r2mem.empty()) << std::endl;
            // for all members of r1
            if (!r1mem.empty())
            {
              for (const std::pair<const Node, Node>& itm1m : r1mem)
              {
                Node xr = itm1m.first;
                Node x = itm1m.second[0];
                Trace("sets-debug") << "checking membership " << xr << " "
                                    << itm1m.second << std::endl;
                std::vector<Node> exp;
                exp.push_back(itm1m.second);
                d_state.addEqualityToExp(term[0], itm1m.second[1], exp);
                bool valid = false;
                int inferType = 0;
                if (k == kind::SET_UNION)
                {
                  valid = true;
                }
                else if (k == kind::SET_INTER)
                {
                  // conclude x is in term
                  // if also existing in members of r2
                  std::map<Node, Node>::const_iterator itm = r2mem.find(xr);
                  if (itm != r2mem.end())
                  {
                    exp.push_back(itm->second);
                    d_state.addEqualityToExp(term[1], itm->second[1], exp);
                    d_state.addEqualityToExp(x, itm->second[0], exp);
                    valid = true;
                  }
                  else
                  {
                    // if not, check whether it is definitely not a member, if
                    // unknown, split
                    if (r2nmem.find(xr) == r2nmem.end())
                    {
                      exp.push_back(nm->mkNode(kind::SET_MEMBER, x, term[1]));
                      valid = true;
                      inferType = 1;
                    }
                  }
                }
                else
                {
                  Assert(k == kind::SET_MINUS);
                  std::map<Node, Node>::const_iterator itm = r2mem.find(xr);
                  if (itm == r2mem.end())
                  {
                    // must add lemma for set minus since non-membership in this
                    // case is not explained
                    exp.push_back(
                        nm->mkNode(kind::SET_MEMBER, x, term[1]).negate());
                    valid = true;
                    inferType = 1;
                  }
                }
                if (valid)
                {
                  Node rr = d_equalityEngine->getRepresentative(term);
                  if (!d_state.isMember(x, rr))
                  {
                    Node kk = d_treg.getProxy(term);
                    Node fact = nm->mkNode(kind::SET_MEMBER, x, kk);
                    d_im.assertInference(
                        fact, InferenceId::SETS_UP_CLOSURE, exp, inferType);
                    if (d_state.isInConflict())
                    {
                      return;
                    }
                  }
                }
                Trace("sets-debug") << "done checking membership " << xr << " "
                                    << itm1m.second << std::endl;
              }
            }
            if (k == kind::SET_UNION)
            {
              if (!r2mem.empty())
              {
                // for all members of r2
                for (const std::pair<const Node, Node>& itm2m : r2mem)
                {
                  Node x = itm2m.second[0];
                  Node rr = d_equalityEngine->getRepresentative(term);
                  if (!d_state.isMember(x, rr))
                  {
                    std::vector<Node> exp;
                    exp.push_back(itm2m.second);
                    d_state.addEqualityToExp(term[1], itm2m.second[1], exp);
                    Node r = d_treg.getProxy(term);
                    Node fact = nm->mkNode(kind::SET_MEMBER, x, r);
                    d_im.assertInference(fact, InferenceId::SETS_UP_CLOSURE_2, exp);
                    if (d_state.isInConflict())
                    {
                      return;
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  if (!d_im.hasSent())
  {
    if (options().sets.setsExt)
    {
      // universal sets
      Trace("sets-debug") << "Check universe sets..." << std::endl;
      // all elements must be in universal set
      const std::vector<Node>& sec = d_state.getSetsEqClasses();
      for (const Node& s : sec)
      {
        // if equivalence class contains a variable
        Node v = d_state.getVariableSet(s);
        if (!v.isNull())
        {
          // the variable in the equivalence class
          std::map<TypeNode, Node> univ_set;
          const std::map<Node, Node>& smems = d_state.getMembers(s);
          for (const std::pair<const Node, Node>& it2 : smems)
          {
            Node e = it2.second[0];
            TypeNode tn = NodeManager::currentNM()->mkSetType(e.getType());
            Node u;
            std::map<TypeNode, Node>::iterator itu = univ_set.find(tn);
            if (itu == univ_set.end())
            {
              Node ueqc = d_state.getUnivSetEqClass(tn);
              // if the universe does not yet exist, or is not in this
              // equivalence class
              if (s != ueqc)
              {
                u = d_treg.getUnivSet(tn);
              }
              univ_set[tn] = u;
            }
            else
            {
              u = itu->second;
            }
            if (!u.isNull())
            {
              Assert(it2.second.getKind() == kind::SET_MEMBER);
              std::vector<Node> exp;
              exp.push_back(it2.second);
              if (v != it2.second[1])
              {
                exp.push_back(v.eqNode(it2.second[1]));
              }
              Node fact = nm->mkNode(kind::SET_MEMBER, it2.second[0], u);
              d_im.assertInference(fact, InferenceId::SETS_UP_UNIV, exp);
              if (d_state.isInConflict())
              {
                return;
              }
            }
          }
        }
      }
    }
  }
}

void TheorySetsPrivate::checkDisequalities()
{
  // disequalities
  Trace("sets") << "TheorySetsPrivate: check disequalities..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  for (NodeBoolMap::const_iterator it = d_deq.begin(); it != d_deq.end(); ++it)
  {
    if (!(*it).second)
    {
      // not active
      continue;
    }
    Node deq = (*it).first;
    // check if it is already satisfied
    Assert(d_equalityEngine->hasTerm(deq[0])
           && d_equalityEngine->hasTerm(deq[1]));
    Node r1 = d_equalityEngine->getRepresentative(deq[0]);
    Node r2 = d_equalityEngine->getRepresentative(deq[1]);
    bool is_sat = d_state.isSetDisequalityEntailed(r1, r2);
    Trace("sets-debug") << "Check disequality " << deq
                        << ", is_sat = " << is_sat << std::endl;
    // will process regardless of sat/processed/unprocessed
    d_deq[deq] = false;

    if (is_sat)
    {
      // already satisfied
      continue;
    }
    if (d_termProcessed.find(deq) != d_termProcessed.end())
    {
      // already added lemma
      continue;
    }
    d_termProcessed.insert(deq);
    d_termProcessed.insert(deq[1].eqNode(deq[0]));
    Trace("sets") << "Process Disequality : " << deq.negate() << std::endl;
    TypeNode elementType = deq[0].getType().getSetElementType();
    Node x = sm->mkSkolemFunction(
        SkolemFunId::SETS_DEQ_DIFF, elementType, {deq[0], deq[1]});
    Node mem1 = nm->mkNode(SET_MEMBER, x, deq[0]);
    Node mem2 = nm->mkNode(SET_MEMBER, x, deq[1]);
    Node lem = nm->mkNode(OR, deq, nm->mkNode(EQUAL, mem1, mem2).negate());
    lem = rewrite(lem);
    d_im.assertInference(lem, InferenceId::SETS_DEQ, d_true, 1);
    d_im.doPendingLemmas();
    if (d_im.hasSent())
    {
      return;
    }
  }
}

void TheorySetsPrivate::checkReduceComprehensions()
{
  NodeManager* nm = NodeManager::currentNM();
  const std::vector<Node>& comps = d_state.getComprehensionSets();
  for (const Node& n : comps)
  {
    if (d_termProcessed.find(n) != d_termProcessed.end())
    {
      // already reduced it
      continue;
    }
    d_termProcessed.insert(n);
    Node v = nm->mkBoundVar(n[2].getType());
    Node body = nm->mkNode(AND, n[1], v.eqNode(n[2]));
    // must do substitution
    std::vector<Node> vars;
    std::vector<Node> subs;
    for (const Node& cv : n[0])
    {
      vars.push_back(cv);
      Node cvs = nm->mkBoundVar(cv.getType());
      subs.push_back(cvs);
    }
    body = body.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
    Node bvl = nm->mkNode(BOUND_VAR_LIST, subs);
    body = nm->mkNode(EXISTS, bvl, body);
    Node mem = nm->mkNode(SET_MEMBER, v, n);
    Node lem =
        nm->mkNode(FORALL, nm->mkNode(BOUND_VAR_LIST, v), body.eqNode(mem));
    Trace("sets-comprehension")
        << "Comprehension reduction: " << lem << std::endl;
    d_im.lemma(lem, InferenceId::SETS_COMPREHENSION);
  }
}

//--------------------------------- standard check

void TheorySetsPrivate::postCheck(Theory::Effort level)
{
  Trace("sets-check") << "Sets finished assertions effort " << level
                      << std::endl;
  // invoke full effort check, relations check
  if (!d_state.isInConflict())
  {
    if (level == Theory::EFFORT_FULL)
    {
      if (!d_external.d_valuation.needCheck())
      {
        fullEffortCheck();
        if (!d_state.isInConflict() && !d_im.hasSentLemma()
            && d_fullCheckIncomplete)
        {
          d_im.setIncomplete(d_fullCheckIncompleteId);
        }
      }
    }
  }
  Trace("sets-check") << "Sets finish Check effort " << level << std::endl;
}

void TheorySetsPrivate::notifyFact(TNode atom, bool polarity, TNode fact)
{
  if (d_state.isInConflict())
  {
    return;
  }
  if (atom.getKind() == kind::SET_MEMBER && polarity)
  {
    // check if set has a value, if so, we can propagate
    Node r = d_equalityEngine->getRepresentative(atom[1]);
    EqcInfo* e = getOrMakeEqcInfo(r, true);
    if (e)
    {
      Node s = e->d_singleton;
      if (!s.isNull())
      {
        Node pexp = NodeManager::currentNM()->mkNode(
            kind::AND, atom, atom[1].eqNode(s));
        if (s.getKind() == kind::SET_SINGLETON)
        {
          if (s[0] != atom[0])
          {
            Trace("sets-prop") << "Propagate mem-eq : " << pexp << std::endl;
            Node eq = s[0].eqNode(atom[0]);
            // triggers an internal inference
            d_im.assertSetsFact(eq, true, InferenceId::SETS_MEM_EQ, pexp);
          }
        }
        else
        {
          Trace("sets-prop")
              << "Propagate mem-eq conflict : " << pexp << std::endl;
          d_im.conflict(pexp, InferenceId::SETS_MEM_EQ_CONFLICT);
        }
      }
    }
    // add to membership list
    d_state.addMember(r, atom);
  }
}
//--------------------------------- end standard check

void TheorySetsPrivate::computeCareGraph()
{
  const std::map<Kind, std::vector<Node> >& ol = d_state.getOperatorList();
  for (const std::pair<const Kind, std::vector<Node> >& it : ol)
  {
    Kind k = it.first;
    if (k == kind::SET_SINGLETON || k == kind::SET_MEMBER)
    {
      unsigned n_pairs = 0;
      Trace("sets-cg-summary") << "Compute graph for sets, op=" << k << "..."
                               << it.second.size() << std::endl;
      Trace("sets-cg") << "Build index for " << k << "..." << std::endl;
      std::map<TypeNode, TNodeTrie> index;
      unsigned arity = 0;
      // populate indices
      for (TNode f1 : it.second)
      {
        Trace("sets-cg-debug") << "...build for " << f1 << std::endl;
        Assert(d_equalityEngine->hasTerm(f1));
        // break into index based on operator, and the type of the element
        // type of the proper set, which notice must be safe wrt subtyping.
        TypeNode tn;
        if (k == kind::SET_SINGLETON)
        {
          // get the type of the singleton set (not the type of its element)
          tn = f1.getType().getSetElementType();
        }
        else
        {
          Assert(k == kind::SET_MEMBER);
          // get the element type of the set (not the type of the element)
          tn = f1[1].getType().getSetElementType();
        }
        std::vector<TNode> reps;
        bool hasCareArg = false;
        for (unsigned j = 0; j < f1.getNumChildren(); j++)
        {
          reps.push_back(d_equalityEngine->getRepresentative(f1[j]));
          if (isCareArg(f1, j))
          {
            hasCareArg = true;
          }
        }
        if (hasCareArg)
        {
          Trace("sets-cg-debug") << "......adding." << std::endl;
          index[tn].addTerm(f1, reps);
          arity = reps.size();
        }
        else
        {
          Trace("sets-cg-debug") << "......skip." << std::endl;
        }
      }
      if (arity > 0)
      {
        // for each index
        for (std::pair<const TypeNode, TNodeTrie>& tt : index)
        {
          Trace("sets-cg") << "Process index " << tt.first << "..."
                           << std::endl;
          nodeTriePathPairProcess(&tt.second, arity, d_cpacb);
        }
      }
      Trace("sets-cg-summary") << "...done, # pairs = " << n_pairs << std::endl;
    }
  }
}

bool TheorySetsPrivate::isCareArg(Node n, unsigned a)
{
  if (d_equalityEngine->isTriggerTerm(n[a], THEORY_SETS))
  {
    return true;
  }
  else if ((n.getKind() == kind::SET_MEMBER
            || n.getKind() == kind::SET_SINGLETON)
           && a == 0 && n[0].getType().isSet())
  {
    return true;
  }
  return false;
}

/******************** Model generation ********************/
/******************** Model generation ********************/
/******************** Model generation ********************/

namespace {
/**
 * This function is a helper function to print sets as
 * Set A = { a0, a1, a2, }
 * instead of
 * (union (singleton a0) (union (singleton a1) (singleton a2)))
 */
void traceSetElementsRecursively(stringstream& stream, const Node& set)
{
  Assert(set.getType().isSet());
  if (set.getKind() == SET_SINGLETON)
  {
    stream << set[0] << ", ";
  }
  if (set.getKind() == SET_UNION)
  {
    traceSetElementsRecursively(stream, set[0]);
    traceSetElementsRecursively(stream, set[1]);
  }
}

std::string traceElements(const Node& set)
{
  std::stringstream stream;
  traceSetElementsRecursively(stream, set);
  return stream.str();
}

}  // namespace

bool TheorySetsPrivate::collectModelValues(TheoryModel* m,
                                           const std::set<Node>& termSet)
{
  Trace("sets-model") << "Set collect model values" << std::endl;

  NodeManager* nm = NodeManager::currentNM();
  std::map<Node, Node> mvals;
  // If cardinality is enabled, we need to use the ordered equivalence class
  // list computed by the cardinality solver, where sets equivalence classes
  // are assigned model values based on their position in the cardinality
  // graph.
  const std::vector<Node>& sec = d_card_enabled
                                     ? d_cardSolver->getOrderedSetsEqClasses()
                                     : d_state.getSetsEqClasses();
  Valuation& val = getValuation();
  for (int i = (int)(sec.size() - 1); i >= 0; i--)
  {
    Node eqc = sec[i];
    if (termSet.find(eqc) == termSet.end())
    {
      Trace("sets-model") << "* Do not assign value for " << eqc
                          << " since is not relevant." << std::endl;
    }
    else
    {
      std::vector<Node> els;
      bool is_base = !d_card_enabled || d_cardSolver->isModelValueBasic(eqc);
      if (is_base)
      {
        Trace("sets-model")
            << "Collect elements of base eqc " << eqc << std::endl;
        // members that must be in eqc
        const std::map<Node, Node>& emems = d_state.getMembers(eqc);
        if (!emems.empty())
        {
          TypeNode elementType = eqc.getType().getSetElementType();
          for (const std::pair<const Node, Node>& itmm : emems)
          {
            // when we have y -> (set.member x S) where rep(x)=y, we use x
            // in the model here. Using y may not be legal with respect to
            // subtyping, since y may be real where x is an int.
            Node t = nm->mkSingleton(elementType, itmm.second[0]);
            els.push_back(t);
          }
        }
      }
      if (d_card_enabled)
      {
        // make the slack elements for the equivalence class based on set
        // cardinality
        d_cardSolver->mkModelValueElementsFor(val, eqc, els, mvals, m);
      }

      Node rep = NormalForm::mkBop(kind::SET_UNION, els, eqc.getType());
      rep = rewrite(rep);
      Trace("sets-model") << "* Assign representative of " << eqc << " to "
                          << rep << std::endl;
      mvals[eqc] = rep;
      if (!m->assertEquality(eqc, rep, true))
      {
        return false;
      }
      m->assertSkeleton(rep);

      // we add the element terms (singletons) as representatives to tell the
      // model builder to evaluate them along with their union (rep).
      // This is needed to account for cases when members and rep are not enough
      // for the model builder to evaluate set terms.
      // e.g.
      // eqc(rep) = [(union (singleton skolem) (singleton 0))]
      // eqc(skolem) = [0]
      // The model builder would fail to evaluate rep as (singleton 0)
      // if (singleton skolem) is not registered as a representative in the
      // model
      for (const Node& el : els)
      {
        m->assertSkeleton(el);
      }

      Trace("sets-model") << "Set " << eqc << " = { " << traceElements(rep)
                          << " }" << std::endl;
    }
  }

  // handle slack elements constraints for finite types
  if (d_card_enabled)
  {
    const std::map<TypeNode, std::vector<TNode> >& slackElements =
        d_cardSolver->getFiniteTypeSlackElements();
    for (const auto& pair : slackElements)
    {
      const std::vector<Node>& members =
          d_cardSolver->getFiniteTypeMembers(pair.first);
      m->setAssignmentExclusionSetGroup(pair.second, members);
      Trace("sets-model") << "ExclusionSet: Group " << pair.second
                          << " is excluded from set" << members << std::endl;
    }
  }
  return true;
}

/********************** Helper functions ***************************/
/********************** Helper functions ***************************/
/********************** Helper functions ***************************/

Valuation& TheorySetsPrivate::getValuation() { return d_external.d_valuation; }

bool TheorySetsPrivate::isEntailed(Node n, bool pol)
{
  return d_state.isEntailed(n, pol);
}

void TheorySetsPrivate::processCarePairArgs(TNode a, TNode b)
{
  for (size_t k = 0, nchild = a.getNumChildren(); k < nchild; ++k)
  {
    TNode x = a[k];
    TNode y = b[k];
    if (!d_equalityEngine->areEqual(x, y))
    {
      if (isCareArg(a, k) && isCareArg(b, k))
      {
        // splitting on sets (necessary for handling set of sets properly)
        if (x.getType().isSet())
        {
          Assert(y.getType().isSet());
          Trace("sets-cg-lemma")
              << "Should split on : " << x << "==" << y << std::endl;
          d_im.split(x.eqNode(y), InferenceId::SETS_CG_SPLIT);
        }
      }
    }
  }
}

Node TheorySetsPrivate::explain(TNode literal)
{
  Trace("sets") << "TheorySetsPrivate::explain(" << literal << ")" << std::endl;

  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  std::vector<TNode> assumptions;

  if (atom.getKind() == kind::EQUAL)
  {
    d_equalityEngine->explainEquality(atom[0], atom[1], polarity, assumptions);
  }
  else if (atom.getKind() == kind::SET_MEMBER)
  {
    d_equalityEngine->explainPredicate(atom, polarity, assumptions);
  }
  else
  {
    Trace("sets") << "unhandled: " << literal << "; (" << atom << ", "
                  << polarity << "); kind" << atom.getKind() << std::endl;
    Unhandled();
  }
  return NodeManager::currentNM()->mkAnd(assumptions);
}

void TheorySetsPrivate::preRegisterTerm(TNode node)
{
  Trace("sets") << "TheorySetsPrivate::preRegisterTerm(" << node << ")"
                << std::endl;
  TypeNode tn = node.getType();
  if (tn.isSet())
  {
    ensureFirstClassSetType(tn);
  }
  switch (node.getKind())
  {
    case kind::EQUAL:
    case kind::SET_MEMBER:
    {
      // add trigger predicate for equality and membership
      d_equalityEngine->addTriggerPredicate(node);
    }
    break;
    case kind::RELATION_JOIN_IMAGE:
    {
      // these are logic exceptions, not type checking exceptions
      if (!node[1].isConst())
      {
        throw LogicException(
            "JoinImage cardinality constraint must be a constant");
      }
      cvc5::internal::Rational r(INT_MAX);
      if (node[1].getConst<Rational>() > r)
      {
        throw LogicException(
            "JoinImage Exceeded INT_MAX in cardinality constraint");
      }
      if (node[1].getConst<Rational>().getNumerator().getSignedInt() < 0)
      {
        throw LogicException(
            "JoinImage cardinality constraint must be non-negative");
      }
    }
    break;
    case kind::SET_MAP:
    {
        throw LogicException(
            "set.map not currently supported by the sets theory solver");
    }
      break;
    default: d_equalityEngine->addTerm(node); break;
  }
}

TrustNode TheorySetsPrivate::ppRewrite(Node node,
                                       std::vector<SkolemLemma>& lems)
{
  Trace("sets-proc") << "ppRewrite : " << node << std::endl;

  switch (node.getKind())
  {
    case kind::SET_CHOOSE: return expandChooseOperator(node, lems);
    case kind::SET_IS_SINGLETON: return expandIsSingletonOperator(node);
    case kind::SET_MINUS:
    {
      if (node[0].getKind() == kind::SET_UNIVERSE)
      {
        // Due to complications involving the cardinality graph, we must purify
        // universe from argument of set minus, so that
        //   (set.minus set.universe x)
        // is replaced by
        //   (set.minus univ x)
        // along with the lemma (= univ set.universe), where univ is the
        // purification skolem for set.universe. We require this purification
        // since the cardinality graph incorrectly thinks that
        // rewrite( (set.inter set.universe x) ), which evaluates to x, is
        // a sibling of (set.minus set.universe x).
        NodeManager* nm = NodeManager::currentNM();
        SkolemManager* sm = nm->getSkolemManager();
        Node sk = sm->mkPurifySkolem(node[0], "univ");
        Trace("ajr-temp") << "PURIFY " << node[0] << " returns " << sk
                          << std::endl;
        Node eq = sk.eqNode(node[0]);
        lems.push_back(SkolemLemma(TrustNode::mkTrustLemma(eq), sk));
        Node ret = nm->mkNode(kind::SET_MINUS, sk, node[1]);
        return TrustNode::mkTrustRewrite(node, ret, nullptr);
      }
    }
    break;
    default: break;
  }
  return TrustNode::null();
}

TrustNode TheorySetsPrivate::expandChooseOperator(
    const Node& node, std::vector<SkolemLemma>& lems)
{
  Assert(node.getKind() == SET_CHOOSE);

  // (choose A) is eliminated to k, with lemma
  //   (and (= k (uf A)) (or (= A (as set.empty (Set E))) (set.member k A)))
  // where uf: (Set E) -> E is a skolem function, and E is the type of elements
  // of A

  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  // the skolem will occur in a term context, thus we give it Boolean
  // term variable kind immediately.
  SkolemManager::SkolemFlags flags = node.getType().isBoolean()
                                         ? SkolemManager::SKOLEM_BOOL_TERM_VAR
                                         : SkolemManager::SKOLEM_DEFAULT;
  Node x = sm->mkPurifySkolem(
      node, "setChoose", "a variable used to eliminate set choose", flags);
  Node A = node[0];
  TypeNode setType = A.getType();
  ensureFirstClassSetType(setType);
  TypeNode ufType = nm->mkFunctionType(setType, setType.getSetElementType());
  // a Null node is used here to get a unique skolem function per set type
  Node uf = sm->mkSkolemFunction(SkolemFunId::SETS_CHOOSE, ufType, Node());
  Node ufA = NodeManager::currentNM()->mkNode(APPLY_UF, uf, A);

  Node equal = x.eqNode(ufA);
  Node emptySet = nm->mkConst(EmptySet(setType));
  Node isEmpty = A.eqNode(emptySet);
  Node member = nm->mkNode(SET_MEMBER, x, A);
  Node lem = nm->mkNode(AND, equal, nm->mkNode(OR, isEmpty, member));
  TrustNode tlem = TrustNode::mkTrustLemma(lem, nullptr);
  lems.push_back(SkolemLemma(tlem, x));
  return TrustNode::mkTrustRewrite(node, x, nullptr);
}

TrustNode TheorySetsPrivate::expandIsSingletonOperator(const Node& node)
{
  Assert(node.getKind() == SET_IS_SINGLETON);

  // we call the rewriter here to handle the pattern
  // (is_singleton (singleton x)) because the rewriter is called after expansion
  Node rewritten = rewrite(node);
  if (rewritten.getKind() != SET_IS_SINGLETON)
  {
    return TrustNode::mkTrustRewrite(node, rewritten, nullptr);
  }

  // (is_singleton A) is expanded as
  // (exists ((x: T)) (= A (singleton x)))
  // where T is the sort of elements of A

  NodeManager* nm = NodeManager::currentNM();
  Node set = rewritten[0];

  std::map<Node, Node>::iterator it = d_isSingletonNodes.find(rewritten);

  if (it != d_isSingletonNodes.end())
  {
    return TrustNode::mkTrustRewrite(rewritten, it->second, nullptr);
  }

  TypeNode setType = set.getType();
  ensureFirstClassSetType(setType);
  Node boundVar = nm->mkBoundVar(setType.getSetElementType());
  Node singleton = nm->mkSingleton(setType.getSetElementType(), boundVar);
  Node equal = set.eqNode(singleton);
  std::vector<Node> variables = {boundVar};
  Node boundVars = nm->mkNode(BOUND_VAR_LIST, variables);
  Node exists = nm->mkNode(kind::EXISTS, boundVars, equal);
  d_isSingletonNodes[rewritten] = exists;

  return TrustNode::mkTrustRewrite(node, exists, nullptr);
}

void TheorySetsPrivate::ensureFirstClassSetType(TypeNode tn) const
{
  Assert(tn.isSet());
  if (!tn.getSetElementType().isFirstClass())
  {
    std::stringstream ss;
    ss << "Cannot handle sets of non-first class types, offending set type is "
       << tn;
    throw LogicException(ss.str());
  }
}

void TheorySetsPrivate::presolve() { d_state.reset(); }

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal
