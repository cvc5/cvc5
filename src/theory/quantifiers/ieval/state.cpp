/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * State for congruence closure with free variables
 */

#include "theory/quantifiers/ieval/state.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "theory/quantifiers/quantifiers_state.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

State::State(Env& env, context::Context* c, QuantifiersState& qs, TermDb* tdb)
    : EnvObj(env),
      d_ctx(c),
      d_qstate(qs),
      d_tdb(tdb),
      d_registeredTerms(c),
      d_numActiveQuant(c, 0)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  d_none = sm->mkDummySkolem("none", nm->booleanType());
  d_some = sm->mkDummySkolem("some", nm->booleanType());
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

void State::watch(Node q, const std::vector<Node>& vars, Node body)
{
  std::map<Node, QuantInfo>::iterator it = d_quantInfo.find(q);
  if (it != d_quantInfo.end())
  {
    // already initialized
    return;
  }
  d_quantInfo.emplace(q, d_ctx);
  it = d_quantInfo.find(q);
  // initialize the quantifier info, which stores basic constraint information
  it->second.initialize(q, body, d_tdb);
  // add to free variable lists
  for (const Node& v : vars)
  {
    FreeVarInfo& finfo = getOrMkFreeVarInfo(v);
    finfo.d_quantList.push_back(q);
  }
  // initialize pattern terms
  NodeSet::const_iterator itr;
  std::vector<TNode> visit;
  // we traverse its constraint terms to set up the parent notification lists
  const std::vector<TNode>& cterms = it->second.getConstraintTerms();
  for (TNode c : cterms)
  {
    // we will notify the quantified formula when the pattern becomes set
    PatTermInfo& pi = getOrMkPatTermInfo(c);
    // (2) when the constraint term is assigned, we notify q
    pi.d_parentNotify.push_back(q);
    // we visit the constraint term below
    visit.push_back(c);
  }

  TNode cur;
  do
  {
    cur = visit.back();
    visit.pop_back();
    itr = d_registeredTerms.find(cur);
    if (itr == d_registeredTerms.end())
    {
      if (!expr::hasBoundVar(cur) || !QuantInfo::isTraverseTerm(cur))
      {
        continue;
      }
      Kind k = cur.getKind();
      if (k == BOUND_VARIABLE)
      {
        // should be one of the free variables of the quantified formula
        Assert(std::find(vars.begin(), vars.end(), cur) != vars.end());
        continue;
      }
      PatTermInfo& pi = getOrMkPatTermInfo(cur);
      // also get the number of unique children
      std::set<TNode> children;
      children.insert(cur.begin(), cur.end());
      pi.d_numChildren = children.size();
      for (TNode cc : children)
      {
        PatTermInfo& pic = getOrMkPatTermInfo(cc);
        // require notifications to parent
        pic.d_parentNotify.push_back(cur);
        visit.push_back(cc);
      }
    }
  } while (!visit.empty());
}

bool State::assignVar(TNode v, TNode s, std::vector<Node>& assignedQuants)
{
  // notify that the variable is equal to the ground term
  Node r = d_qstate.getRepresentative(s);
  notifyPatternEqGround(v, r);
  // might the inactive now
  if (isFinished())
  {
    return false;
  }
  // decrement the unassigned variable counts for all quantified formulas
  // containing this variable
  FreeVarInfo& finfo = getFreeVarInfo(v);
  for (const Node& q : finfo.d_quantList)
  {
    QuantInfo& qinfo = getQuantInfo(q);
    if (!qinfo.isActive())
    {
      // marked inactive, skip
      continue;
    }
    if (qinfo.getNumUnassignedVars()==1)
    {
      // now fully assigned
      assignedQuants.push_back(q);
      // set inactive
      setQuantInactive(qinfo);
    }
    else
    {
      // decrement the variable
      qinfo.decrementUnassignedVar();
    }
  }
  return true;
}

bool State::isFinished() const { return d_numActiveQuant == 0; }

QuantInfo& State::getQuantInfo(TNode q)
{
  std::map<Node, QuantInfo>::iterator it = d_quantInfo.find(q);
  Assert(it != d_quantInfo.end());
  return it->second;
}

FreeVarInfo& State::getOrMkFreeVarInfo(TNode v)
{
  std::map<Node, FreeVarInfo>::iterator it = d_fvInfo.find(v);
  if (it == d_fvInfo.end())
  {
    d_fvInfo.emplace(v, d_ctx);
    it = d_fvInfo.find(v);
  }
  return it->second;
}

FreeVarInfo& State::getFreeVarInfo(TNode v)
{
  std::map<Node, FreeVarInfo>::iterator it = d_fvInfo.find(v);
  Assert(it != d_fvInfo.end());
  return it->second;
}

PatTermInfo& State::getOrMkPatTermInfo(TNode p)
{
  std::map<Node, PatTermInfo>::iterator it = d_pInfo.find(p);
  if (it == d_pInfo.end())
  {
    it = d_pInfo.emplace(p, d_ctx).first;
    // initialize the pattern
    it->second.initialize(p, d_tdb);
  }
  return it->second;
}

PatTermInfo& State::getPatTermInfo(TNode p)
{
  std::map<Node, PatTermInfo>::iterator it = d_pInfo.find(p);
  Assert(it != d_pInfo.end());
  return it->second;
}

void State::notifyPatternNone(TNode p) { notifyPatternEqGround(p, d_none); }

void State::notifyPatternEqGround(TNode p, TNode g)
{
  Assert(!g.isNull());
  Assert(isGroundEqc(g) || isNone(g));
  std::map<Node, PatTermInfo>::iterator it = d_pInfo.find(p);
  Assert(it != d_pInfo.end());
  if (!it->second.isActive())
  {
    // already assigned
    return;
  }
  Trace("ieval-state-debug")
      << "Notify pattern eq ground: " << p << " == " << g << std::endl;
  it->second.d_eq = g;
  // run notifications until fixed point
  size_t tnIndex = 0;
  std::vector<std::map<Node, PatTermInfo>::iterator> toNotify;
  toNotify.push_back(it);
  while (tnIndex < toNotify.size())
  {
    it = toNotify[tnIndex];
    ++tnIndex;
    Assert(it != d_pInfo.end());
    p = it->second.d_pattern;
    g = it->second.d_eq;
    Assert(!g.isNull());
    context::CDList<Node>& notifyList = it->second.d_parentNotify;
    for (TNode pp : notifyList)
    {
      if (pp.getKind() == FORALL)
      {
        // quantified formulas are ordinary parents
        Assert(i == 0);
        // if we have a quantified formula as a parent, notify is a special
        // method, which will test the constraints
        notifyQuant(pp, p, g);
        // could be finished now
        if (isFinished())
        {
          break;
        }
        continue;
      }
      // otherwise, notify the parent pattern
      it = d_pInfo.find(pp);
      Assert(it != d_pInfo.end());
      if (it->second.notifyChild(*this, p, g))
      {
        toNotify.push_back(it);
      }
    }
  }
}

void State::notifyQuant(TNode q, TNode p, TNode val)
{
  Assert(q.getKind() == FORALL);
  QuantInfo& qi = getQuantInfo(q);
  if (!qi.isActive())
  {
    // quantified formula is already inactive
    return;
  }
  Trace("ieval-state-debug") << "Notify quant constraint " << q.getId() << " "
                             << p << " == " << val << std::endl;
  Assert(d_numActiveQuant.get() > 0);
  // check whether we should set inactive
  bool setInactive = false;
  if (isNone(val))
  {
    setInactive = true;
    Trace("ieval-state-debug") << "...inactive due to none" << std::endl;
  }
  else
  {
    // Are we the "some" val? This is true for predicates whose value is
    // a predicate e.g. equality applied to existing terms.
    bool valSome = isSome(val);
    const std::map<TNode, std::vector<Node>>& cs = qi.getConstraints();
    std::map<TNode, std::vector<Node>>::const_iterator itm = cs.find(p);
    if (itm != cs.end())
    {
      for (TNode c : itm->second)
      {
        if (c.isNull())
        {
          // the constraint said you must be disequal to none, i.e. we must be
          // equal to something. we are ok
          continue;
        }
        else if (valSome)
        {
          // it has the "some" value, and we have any constraint, we remain
          // active but are not strictly a conflict
          qi.setNoConflict();
          Trace("ieval-state-debug") << "...no conflict" << std::endl;
          break;
        }
        // if a disequality constraint
        bool isEq = true;
        TNode dval;
        if (QuantInfo::isDeqConstraint(c, p, dval))
        {
          Assert(c[0].getKind() == EQUAL);
          isEq = false;
          c = dval;
        }
        // otherwise check the constraint
        TNode r = d_qstate.getRepresentative(c);
        if (isEq != (val == r))
        {
          Trace("ieval-state-debug")
              << "...inactive due to constraint " << c << std::endl;
          setInactive = true;
          break;
        }
        else
        {
          Trace("ieval-state-debug")
              << "...satisfied constraint " << c << std::endl;
        }
      }
    }
    else
    {
      Trace("ieval-state-debug") << "...no constraints" << std::endl;
    }
  }
  // if we should set inactive, update qi and decrement d_numActiveQuant
  if (setInactive)
  {
    setQuantInactive(qi);
  }
  else
  {
    Trace("ieval-state-debug") << "...still active" << std::endl;
  }
  // otherwise, we could have an instantiation, but we do not check for this
  // here; instead this is handled based on watching the number of free
  // variables assigned.
}

void State::setQuantInactive(QuantInfo& qi)
{
  if (qi.isActive())
  {
    qi.setActive(false);
    d_numActiveQuant = d_numActiveQuant - 1;
  }
}

Node State::getNone() const { return d_none; }

bool State::isNone(TNode n) const { return n == d_none; }

Node State::getSome() const { return d_some; }

bool State::isSome(TNode n) const { return n == d_some; }

bool State::areDisequal(TNode a, TNode b) const
{
  return d_qstate.areDisequal(a, b);
}

Node State::doRewrite(Node n) { return rewrite(n); }

bool State::isQuantActive(TNode q) const
{
  std::map<Node, QuantInfo>::const_iterator it = d_quantInfo.find(q);
  Assert(it != d_quantInfo.end());
  return it->second.isActive();
}

TNode State::getValue(TNode p) const
{
  std::map<Node, PatTermInfo>::const_iterator it = d_pInfo.find(p);
  if (it != d_pInfo.end())
  {
    return it->second.d_eq;
  }
  // all pattern terms should have been assigned pattern term info
  Assert(!expr::hasBoundVar(p));
  return d_qstate.getRepresentative(p);
}

std::string State::toString() const
{
  std::stringstream ss;
  ss << "#patterns = " << d_pInfo.size() << std::endl;
  ss << "#freeVars = " << d_fvInfo.size() << std::endl;
  ss << "#quants = " << d_numActiveQuant.get() << " / " << d_quantInfo.size()
     << std::endl;
  return ss.str();
}

std::string State::toStringSearch() const
{
  std::stringstream ss;
  ss << "activeQuants = " << d_numActiveQuant.get();
  return ss.str();
}

std::string State::toStringDebugSearch() const
{
  std::stringstream ss;
  ss << "activeQuants = " << d_numActiveQuant.get() << "[";
  size_t nqc = 0;
  for (const std::pair<const Node, QuantInfo>& q : d_quantInfo)
  {
    if (q.second.isActive())
    {
      ss << " " << q.first.getId();
      nqc++;
    }
  }
  ss << " ]";
  Assert(nqc == d_numActiveQuant.get()) << "Active quant mismatch " << ss.str();
  return ss.str();
}

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
