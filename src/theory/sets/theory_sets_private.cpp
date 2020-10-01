/*********************                                                        */
/*! \file theory_sets_private.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mudathir Mohamed, Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets theory implementation.
 **
 ** Sets theory implementation.
 **/

#include "theory/sets/theory_sets_private.h"

#include <algorithm>

#include "expr/emptyset.h"
#include "expr/node_algorithm.h"
#include "options/sets_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/sets/normal_form.h"
#include "theory/sets/theory_sets.h"
#include "theory/theory_model.h"
#include "util/result.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace sets {

TheorySetsPrivate::TheorySetsPrivate(TheorySets& external,
                                     SolverState& state,
                                     InferenceManager& im,
                                     SkolemCache& skc)
    : d_deq(state.getSatContext()),
      d_termProcessed(state.getUserContext()),
      d_full_check_incomplete(false),
      d_external(external),
      d_state(state),
      d_im(im),
      d_skCache(skc),
      d_treg(state, im, skc),
      d_rels(new TheorySetsRels(state, im, skc, d_treg)),
      d_cardSolver(new CardinalityExtension(state, im, d_treg)),
      d_rels_enabled(false),
      d_card_enabled(false)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
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
  if (t.getKind() == kind::SINGLETON || t.getKind() == kind::EMPTYSET)
  {
    EqcInfo* e = getOrMakeEqcInfo(t, true);
    e->d_singleton = t;
  }
}

void TheorySetsPrivate::eqNotifyMerge(TNode t1, TNode t2)
{
  if (!d_state.isInConflict())
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
            d_im.assertInternalFact(eq, true, exp);
          }
          else
          {
            // singleton equal to emptyset, conflict
            Trace("sets-prop")
                << "Propagate conflict : " << s1 << " == " << s2 << std::endl;
            d_im.conflictEqConstantMerge(s1, s2);
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
      d_im.conflict(facts[0]);
      return;
    }
    for (const Node& f : facts)
    {
      Assert(f.getKind() == kind::IMPLIES);
      Trace("sets-prop") << "Propagate eq-mem eq inference : " << f[0] << " => "
                         << f[1] << std::endl;
      d_im.assertInternalFact(f[1], true, f[0]);
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
      ei = new EqcInfo(d_external.getSatContext());
      d_eqc_info[n] = ei;
    }
    return ei;
  }
  else
  {
    return eqc_i->second;
  }
}

bool TheorySetsPrivate::areCareDisequal(Node a, Node b)
{
  if (d_equalityEngine->isTriggerTerm(a, THEORY_SETS)
      && d_equalityEngine->isTriggerTerm(b, THEORY_SETS))
  {
    TNode a_shared =
        d_equalityEngine->getTriggerTermRepresentative(a, THEORY_SETS);
    TNode b_shared =
        d_equalityEngine->getTriggerTermRepresentative(b, THEORY_SETS);
    EqualityStatus eqStatus =
        d_external.d_valuation.getEqualityStatus(a_shared, b_shared);
    if (eqStatus == EQUALITY_FALSE_AND_PROPAGATED || eqStatus == EQUALITY_FALSE
        || eqStatus == EQUALITY_FALSE_IN_MODEL)
    {
      return true;
    }
  }
  return false;
}

void TheorySetsPrivate::fullEffortReset()
{
  Assert(d_equalityEngine->consistent());
  d_full_check_incomplete = false;
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
          Trace("sets-eqc") << n << " (" << n.isConst() << ") ";
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
        if (nk == kind::SINGLETON)
        {
          // ensure the proxy has been introduced
          d_treg.getProxy(n);
        }
        else if (nk == kind::CARD)
        {
          d_card_enabled = true;
          // register it with the cardinality solver
          d_cardSolver->registerTerm(n);
          // if we do not handle the kind, set incomplete
          Kind nk0 = n[0].getKind();
          // some kinds of cardinality we cannot handle
          if (d_rels->isRelationKind(nk0))
          {
            d_full_check_incomplete = true;
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

    if (Trace.isOn("sets-state"))
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
    if (Trace.isOn("sets-mem"))
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
    // check subtypes
    checkSubtypes();
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

void TheorySetsPrivate::checkSubtypes()
{
  Trace("sets") << "TheorySetsPrivate: check Subtypes..." << std::endl;
  const std::vector<Node>& sec = d_state.getSetsEqClasses();
  for (const Node& s : sec)
  {
    TypeNode mct = d_most_common_type[s];
    Assert(!mct.isNull());
    const std::map<Node, Node>& smems = d_state.getMembers(s);
    if (!smems.empty())
    {
      for (const std::pair<const Node, Node>& it2 : smems)
      {
        Trace("sets") << "  check subtype " << it2.first << " " << it2.second
                      << std::endl;
        Trace("sets") << "    types : " << it2.first.getType() << " " << mct
                      << std::endl;
        if (!it2.first.getType().isSubtypeOf(mct))
        {
          Node mctt = d_most_common_type_term[s];
          Assert(!mctt.isNull());
          Trace("sets") << "    most common type term is " << mctt << std::endl;
          std::vector<Node> exp;
          exp.push_back(it2.second);
          Assert(d_state.areEqual(mctt, it2.second[1]));
          exp.push_back(mctt.eqNode(it2.second[1]));
          Node tc_k = d_treg.getTypeConstraintSkolem(it2.first, mct);
          if (!tc_k.isNull())
          {
            Node etc = tc_k.eqNode(it2.first);
            d_im.assertInference(etc, exp, "subtype-clash");
            if (d_state.isInConflict())
            {
              return;
            }
          }
        }
      }
    }
  }
  Trace("sets") << "TheorySetsPrivate: finished." << std::endl;
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
              if (!options::setsProxyLemmas())
              {
                Node nmem = NodeManager::currentNM()->mkNode(
                    kind::MEMBER, mem[0], eq_set);
                nmem = Rewriter::rewrite(nmem);
                std::vector<Node> exp;
                exp.push_back(mem);
                exp.push_back(mem[1].eqNode(eq_set));
                d_im.assertInference(nmem, exp, "downc");
                if (d_state.isInConflict())
                {
                  return;
                }
              }
              else
              {
                // use proxy set
                Node k = d_treg.getProxy(eq_set);
                Node pmem =
                    NodeManager::currentNM()->mkNode(kind::MEMBER, mem[0], k);
                Node nmem = NodeManager::currentNM()->mkNode(
                    kind::MEMBER, mem[0], eq_set);
                nmem = Rewriter::rewrite(nmem);
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
                d_im.assertInference(nmem, exp, "downc");
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
      if (!r1mem.empty() || k == kind::UNION)
      {
        for (const std::pair<const Node, Node>& it2 : it.second)
        {
          Node r2 = it2.first;
          Node term = it2.second;
          // see if there are members in second argument
          const std::map<Node, Node>& r2mem = d_state.getMembers(r2);
          const std::map<Node, Node>& r2nmem = d_state.getNegativeMembers(r2);
          if (!r2mem.empty() || k != kind::INTERSECTION)
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
                if (k == kind::UNION)
                {
                  valid = true;
                }
                else if (k == kind::INTERSECTION)
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
                      exp.push_back(nm->mkNode(kind::MEMBER, x, term[1]));
                      valid = true;
                      inferType = 1;
                    }
                  }
                }
                else
                {
                  Assert(k == kind::SETMINUS);
                  std::map<Node, Node>::const_iterator itm = r2mem.find(xr);
                  if (itm == r2mem.end())
                  {
                    // must add lemma for set minus since non-membership in this
                    // case is not explained
                    exp.push_back(
                        nm->mkNode(kind::MEMBER, x, term[1]).negate());
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
                    Node fact = nm->mkNode(kind::MEMBER, x, kk);
                    d_im.assertInference(fact, exp, "upc", inferType);
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
            if (k == kind::UNION)
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
                    Node fact = nm->mkNode(kind::MEMBER, x, r);
                    d_im.assertInference(fact, exp, "upc2");
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
    if (options::setsExt())
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
              Assert(it2.second.getKind() == kind::MEMBER);
              std::vector<Node> exp;
              exp.push_back(it2.second);
              if (v != it2.second[1])
              {
                exp.push_back(v.eqNode(it2.second[1]));
              }
              Node fact = nm->mkNode(kind::MEMBER, it2.second[0], u);
              d_im.assertInference(fact, exp, "upuniv");
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
    Node x = d_skCache.mkTypedSkolemCached(
        elementType, deq[0], deq[1], SkolemCache::SK_DISEQUAL, "sde");
    Node mem1 = nm->mkNode(MEMBER, x, deq[0]);
    Node mem2 = nm->mkNode(MEMBER, x, deq[1]);
    Node lem = nm->mkNode(OR, deq, nm->mkNode(EQUAL, mem1, mem2).negate());
    lem = Rewriter::rewrite(lem);
    d_im.assertInference(lem, d_true, "diseq", 1);
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
    Node mem = nm->mkNode(MEMBER, v, n);
    Node lem =
        nm->mkNode(FORALL, nm->mkNode(BOUND_VAR_LIST, v), body.eqNode(mem));
    Trace("sets-comprehension")
        << "Comprehension reduction: " << lem << std::endl;
    d_im.lemma(lem);
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
            && d_full_check_incomplete)
        {
          d_im.setIncomplete();
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
  if (atom.getKind() == kind::MEMBER && polarity)
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
        if (s.getKind() == kind::SINGLETON)
        {
          if (s[0] != atom[0])
          {
            Trace("sets-prop") << "Propagate mem-eq : " << pexp << std::endl;
            Node eq = s[0].eqNode(atom[0]);
            // triggers an internal inference
            d_im.assertInternalFact(eq, true, pexp);
          }
        }
        else
        {
          Trace("sets-prop")
              << "Propagate mem-eq conflict : " << pexp << std::endl;
          d_im.conflict(pexp);
        }
      }
    }
    // add to membership list
    d_state.addMember(r, atom);
  }
}
//--------------------------------- end standard check

/************************ Sharing ************************/
/************************ Sharing ************************/
/************************ Sharing ************************/

void TheorySetsPrivate::addCarePairs(TNodeTrie* t1,
                                     TNodeTrie* t2,
                                     unsigned arity,
                                     unsigned depth,
                                     unsigned& n_pairs)
{
  if (depth == arity)
  {
    if (t2 != NULL)
    {
      Node f1 = t1->getData();
      Node f2 = t2->getData();
      if (!d_state.areEqual(f1, f2))
      {
        Trace("sets-cg") << "Check " << f1 << " and " << f2 << std::endl;
        vector<pair<TNode, TNode> > currentPairs;
        for (unsigned k = 0; k < f1.getNumChildren(); ++k)
        {
          TNode x = f1[k];
          TNode y = f2[k];
          Assert(d_equalityEngine->hasTerm(x));
          Assert(d_equalityEngine->hasTerm(y));
          Assert(!d_state.areDisequal(x, y));
          Assert(!areCareDisequal(x, y));
          if (!d_equalityEngine->areEqual(x, y))
          {
            Trace("sets-cg")
                << "Arg #" << k << " is " << x << " " << y << std::endl;
            if (d_equalityEngine->isTriggerTerm(x, THEORY_SETS)
                && d_equalityEngine->isTriggerTerm(y, THEORY_SETS))
            {
              TNode x_shared = d_equalityEngine->getTriggerTermRepresentative(
                  x, THEORY_SETS);
              TNode y_shared = d_equalityEngine->getTriggerTermRepresentative(
                  y, THEORY_SETS);
              currentPairs.push_back(make_pair(x_shared, y_shared));
            }
            else if (isCareArg(f1, k) && isCareArg(f2, k))
            {
              // splitting on sets (necessary for handling set of sets properly)
              if (x.getType().isSet())
              {
                Assert(y.getType().isSet());
                if (!d_state.areDisequal(x, y))
                {
                  Trace("sets-cg-lemma")
                      << "Should split on : " << x << "==" << y << std::endl;
                  d_im.split(x.eqNode(y));
                }
              }
            }
          }
        }
        for (unsigned c = 0; c < currentPairs.size(); ++c)
        {
          Trace("sets-cg-pair") << "Pair : " << currentPairs[c].first << " "
                                << currentPairs[c].second << std::endl;
          d_external.addCarePair(currentPairs[c].first, currentPairs[c].second);
          n_pairs++;
        }
      }
    }
  }
  else
  {
    if (t2 == NULL)
    {
      if (depth < (arity - 1))
      {
        // add care pairs internal to each child
        for (std::pair<const TNode, TNodeTrie>& t : t1->d_data)
        {
          addCarePairs(&t.second, NULL, arity, depth + 1, n_pairs);
        }
      }
      // add care pairs based on each pair of non-disequal arguments
      for (std::map<TNode, TNodeTrie>::iterator it = t1->d_data.begin();
           it != t1->d_data.end();
           ++it)
      {
        std::map<TNode, TNodeTrie>::iterator it2 = it;
        ++it2;
        for (; it2 != t1->d_data.end(); ++it2)
        {
          if (!d_equalityEngine->areDisequal(it->first, it2->first, false))
          {
            if (!areCareDisequal(it->first, it2->first))
            {
              addCarePairs(
                  &it->second, &it2->second, arity, depth + 1, n_pairs);
            }
          }
        }
      }
    }
    else
    {
      // add care pairs based on product of indices, non-disequal arguments
      for (std::pair<const TNode, TNodeTrie>& tt1 : t1->d_data)
      {
        for (std::pair<const TNode, TNodeTrie>& tt2 : t2->d_data)
        {
          if (!d_equalityEngine->areDisequal(tt1.first, tt2.first, false))
          {
            if (!areCareDisequal(tt1.first, tt2.first))
            {
              addCarePairs(&tt1.second, &tt2.second, arity, depth + 1, n_pairs);
            }
          }
        }
      }
    }
  }
}

void TheorySetsPrivate::computeCareGraph()
{
  const std::map<Kind, std::vector<Node> >& ol = d_state.getOperatorList();
  for (const std::pair<const Kind, std::vector<Node> >& it : ol)
  {
    Kind k = it.first;
    if (k == kind::SINGLETON || k == kind::MEMBER)
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
        Assert(d_equalityEngine->hasTerm(f1));
        Trace("sets-cg-debug") << "...build for " << f1 << std::endl;
        Assert(d_equalityEngine->hasTerm(f1));
        // break into index based on operator, and type of first argument (since
        // some operators are parametric)
        TypeNode tn = f1[0].getType();
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
          addCarePairs(&tt.second, nullptr, arity, 0, n_pairs);
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
  else if ((n.getKind() == kind::MEMBER || n.getKind() == kind::SINGLETON)
           && a == 0 && n[0].getType().isSet())
  {
    return true;
  }
  else
  {
    return false;
  }
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
  if (set.getKind() == SINGLETON)
  {
    stream << set[0] << ", ";
  }
  if (set.getKind() == UNION)
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
          for (const std::pair<const Node, Node>& itmm : emems)
          {
            Node t = nm->mkNode(kind::SINGLETON, itmm.first);
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
      Node rep = NormalForm::mkBop(kind::UNION, els, eqc.getType());
      rep = Rewriter::rewrite(rep);
      Trace("sets-model") << "* Assign representative of " << eqc << " to "
                          << rep << std::endl;
      mvals[eqc] = rep;
      if (!m->assertEquality(eqc, rep, true))
      {
        return false;
      }
      m->assertSkeleton(rep);

      Trace("sets-model") << "Set " << eqc << " = { " << traceElements(rep)
                          << " }" << std::endl;
    }
  }

  // handle slack elements constraints for finite types
  if (d_card_enabled)
  {
    const std::map<TypeNode, std::vector<TNode> >& slackElements =
        d_cardSolver->getFiniteTypeSlackElements();
    for (const std::pair<TypeNode, std::vector<TNode> >& pair : slackElements)
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

Node mkAnd(const std::vector<TNode>& conjunctions)
{
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;
  for (unsigned i = 0; i < conjunctions.size(); ++i)
  {
    TNode t = conjunctions[i];
    if (t.getKind() == kind::AND)
    {
      for (TNode::iterator child_it = t.begin(); child_it != t.end();
           ++child_it)
      {
        Assert((*child_it).getKind() != kind::AND);
        all.insert(*child_it);
      }
    }
    else
    {
      all.insert(t);
    }
  }

  Assert(all.size() > 0);
  if (all.size() == 1)
  {
    // All the same, or just one
    return conjunctions[0];
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end)
  {
    conjunction << *it;
    ++it;
  }
  return conjunction;
} /* mkAnd() */

Valuation& TheorySetsPrivate::getValuation() { return d_external.d_valuation; }

Node TheorySetsPrivate::explain(TNode literal)
{
  Debug("sets") << "TheorySetsPrivate::explain(" << literal << ")" << std::endl;

  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  std::vector<TNode> assumptions;

  if (atom.getKind() == kind::EQUAL)
  {
    d_equalityEngine->explainEquality(atom[0], atom[1], polarity, assumptions);
  }
  else if (atom.getKind() == kind::MEMBER)
  {
    d_equalityEngine->explainPredicate(atom, polarity, assumptions);
  }
  else
  {
    Debug("sets") << "unhandled: " << literal << "; (" << atom << ", "
                  << polarity << "); kind" << atom.getKind() << std::endl;
    Unhandled();
  }

  return mkAnd(assumptions);
}

void TheorySetsPrivate::preRegisterTerm(TNode node)
{
  Debug("sets") << "TheorySetsPrivate::preRegisterTerm(" << node << ")"
                << std::endl;
  switch (node.getKind())
  {
    case kind::EQUAL:
    case kind::MEMBER:
    {
      // add trigger predicate for equality and membership
      d_equalityEngine->addTriggerPredicate(node);
    }
    break;
    case kind::CARD: d_equalityEngine->addTriggerTerm(node, THEORY_SETS); break;
    default: d_equalityEngine->addTerm(node); break;
  }
}

TrustNode TheorySetsPrivate::expandDefinition(Node node)
{
  Debug("sets-proc") << "expandDefinition : " << node << std::endl;

  switch (node.getKind())
  {
    case kind::CHOOSE: return expandChooseOperator(node);
    case kind::IS_SINGLETON: return expandIsSingletonOperator(node);
    default: return TrustNode::null();
  }
}

TrustNode TheorySetsPrivate::expandChooseOperator(const Node& node)
{
  Assert(node.getKind() == CHOOSE);

  // we call the rewriter here to handle the pattern (choose (singleton x))
  // because the rewriter is called after expansion
  Node rewritten = Rewriter::rewrite(node);
  if (rewritten.getKind() != CHOOSE)
  {
    return TrustNode::mkTrustRewrite(node, rewritten, nullptr);
  }

  // (choose A) is expanded as
  // (witness ((x elementType))
  //    (ite
  //      (= A (as emptyset setType))
  //      (= x chooseUf(A))
  //      (and (member x A) (= x chooseUf(A)))

  NodeManager* nm = NodeManager::currentNM();
  Node set = rewritten[0];
  TypeNode setType = set.getType();
  Node chooseSkolem = getChooseFunction(setType);
  Node apply = NodeManager::currentNM()->mkNode(APPLY_UF, chooseSkolem, set);

  Node witnessVariable = nm->mkBoundVar(setType.getSetElementType());

  Node equal = witnessVariable.eqNode(apply);
  Node emptySet = nm->mkConst(EmptySet(setType));
  Node isEmpty = set.eqNode(emptySet);
  Node member = nm->mkNode(MEMBER, witnessVariable, set);
  Node memberAndEqual = member.andNode(equal);
  Node ite = nm->mkNode(ITE, isEmpty, equal, memberAndEqual);
  Node witnessVariables = nm->mkNode(BOUND_VAR_LIST, witnessVariable);
  Node witness = nm->mkNode(WITNESS, witnessVariables, ite);
  return TrustNode::mkTrustRewrite(node, witness, nullptr);
}

TrustNode TheorySetsPrivate::expandIsSingletonOperator(const Node& node)
{
  Assert(node.getKind() == IS_SINGLETON);

  // we call the rewriter here to handle the pattern
  // (is_singleton (singleton x)) because the rewriter is called after expansion
  Node rewritten = Rewriter::rewrite(node);
  if (rewritten.getKind() != IS_SINGLETON)
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
  Node boundVar = nm->mkBoundVar(setType.getSetElementType());
  Node singleton = nm->mkNode(kind::SINGLETON, boundVar);
  Node equal = set.eqNode(singleton);
  std::vector<Node> variables = {boundVar};
  Node boundVars = nm->mkNode(BOUND_VAR_LIST, variables);
  Node exists = nm->mkNode(kind::EXISTS, boundVars, equal);
  d_isSingletonNodes[rewritten] = exists;

  return TrustNode::mkTrustRewrite(node, exists, nullptr);
}

Node TheorySetsPrivate::getChooseFunction(const TypeNode& setType)
{
  std::map<TypeNode, Node>::iterator it = d_chooseFunctions.find(setType);
  if (it != d_chooseFunctions.end())
  {
    return it->second;
  }

  NodeManager* nm = NodeManager::currentNM();
  TypeNode chooseUf = nm->mkFunctionType(setType, setType.getSetElementType());
  stringstream stream;
  stream << "chooseUf" << setType.getId();
  string name = stream.str();
  Node chooseSkolem = nm->mkSkolem(
      name, chooseUf, "choose function", NodeManager::SKOLEM_EXACT_NAME);
  d_chooseFunctions[setType] = chooseSkolem;
  return chooseSkolem;
}

void TheorySetsPrivate::presolve() { d_state.reset(); }

}  // namespace sets
}  // namespace theory
}  // namespace CVC4
