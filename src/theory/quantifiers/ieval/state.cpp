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
 * State for instantiation evaluator
 */

#include "theory/quantifiers/ieval/state.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "theory/quantifiers/ieval/term_evaluator.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_registry.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

State::State(Env& env,
             context::Context* c,
             QuantifiersState& qs,
             TermRegistry& tr)
    : EnvObj(env),
      d_ctx(c),
      d_qstate(qs),
      d_treg(tr),
      d_tevMode(ieval::TermEvaluatorMode::NONE),
      d_registeredTerms(c),
      d_registeredBaseTerms(c),
      d_initialized(c, false),
      d_numActiveQuant(c, 0)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  d_none = sm->mkDummySkolem("none", nm->booleanType());
  d_some = sm->mkDummySkolem("some", nm->booleanType());
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

void State::setEvaluatorMode(TermEvaluatorMode tev)
{
  d_tevMode = tev;
  // TODO: could preserve the term evaluator?
  // initialize the term evaluator
  if (tev == TermEvaluatorMode::CONFLICT || tev == TermEvaluatorMode::PROP
      || tev == TermEvaluatorMode::NO_ENTAIL)
  {
    d_tec.reset(
        new TermEvaluatorEntailed(d_env, d_qstate, d_treg.getTermDatabase()));
  }
  else if (tev == TermEvaluatorMode::MODEL)
  {
    // d_tec.reset(new TermEvaluatorModel(
  }
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
  it->second.initialize(q, body);
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
      d_registeredTerms.insert(cur);
      if (cur.getKind() == BOUND_VARIABLE)
      {
        // should be one of the free variables of the quantified formula
        Assert(std::find(vars.begin(), vars.end(), cur) != vars.end());
        continue;
      }
      size_t nchild = 0;
      if (QuantInfo::isTraverseTerm(cur))
      {
        // get the unique children
        std::set<TNode> children;
        children.insert(cur.begin(), cur.end());
        for (TNode cc : children)
        {
          // skip constants
          if (cc.isConst())
          {
            continue;
          }
          // require notifications to parent
          PatTermInfo& pic = getOrMkPatTermInfo(cc);
          pic.d_parentNotify.push_back(cur);
          visit.push_back(cc);
        }
        nchild = children.size();
      }
      if (nchild > 0)
      {
        // set the number of watched children
        PatTermInfo& pi = getPatTermInfo(cur);
        pi.d_numUnassigned = nchild;
      }
      else
      {
        Assert(d_pInfo.find(cur) != d_pInfo.end());
        // no notifying children, this term will be initialized immediately
        d_registeredBaseTerms.insert(cur);
      }
    }
  } while (!visit.empty());
  // increment the count of quantified formulas
  d_numActiveQuant = d_numActiveQuant + 1;
}

bool State::initialize()
{
  if (d_initialized.get())
  {
    // already intialized
    return !isFinished();
  }
  Trace("ieval") << "INITIALIZE" << std::endl;
  // should have set a valid evaluator mode
  Assert(d_tec != nullptr);
  d_initialized = true;
  for (const Node& b : d_registeredBaseTerms)
  {
    Node bev = d_tec->evaluateBase(*this, b);
    Assert(!bev.isNull());
    Trace("ieval") << "  " << b << " := " << bev << " (initialize)"
                   << std::endl;
    notifyPatternEqGround(b, bev);
    if (isFinished())
    {
      return false;
    }
  }
  return true;
}

bool State::assignVar(TNode v,
                      TNode s,
                      std::vector<Node>& assignedQuants,
                      bool trackAssignedQuant)
{
  Assert(d_initialized.get());
  // notify that the variable is equal to the ground term
  Node r = d_tec->evaluateBase(*this, s);
  Trace("ieval") << "ASSIGN: " << v << " := " << r << std::endl;
  notifyPatternEqGround(v, r);
  // might the inactive now
  if (isFinished())
  {
    return false;
  }
  if (trackAssignedQuant)
  {
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
      if (qinfo.getNumUnassignedVars() == 1)
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
    it->second.initialize(p);
  }
  return it->second;
}

PatTermInfo& State::getPatTermInfo(TNode p)
{
  std::map<Node, PatTermInfo>::iterator it = d_pInfo.find(p);
  Assert(it != d_pInfo.end());
  return it->second;
}

void State::notifyPatternEqGround(TNode p, TNode g)
{
  Assert(!g.isNull());
  Assert(!expr::hasBoundVar(g));
  Assert(d_tec->evaluateBase(*this, g) == g);
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
      // returns true if we have evaluated
      if (it->second.notifyChild(*this, p, g, d_tec.get()))
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
  std::stringstream inactiveReason;
  if (isNone(val))
  {
    // a top-level constraint is "none", i.e. this instantiation will generate
    // a predicate over new terms.
    if (d_tevMode == TermEvaluatorMode::CONFLICT
        || d_tevMode == TermEvaluatorMode::PROP)
    {
      // if we are looking for conflicts and propagations only, we are now
      // inactive
      inactiveReason << "none, req conflict/prop";
      setInactive = true;
      Trace("ieval-state-debug") << "...inactive due to none" << std::endl;
    }
    else
    {
      qi.setNoConflict();
    }
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
          if (d_tevMode == TermEvaluatorMode::CONFLICT)
          {
            // if we require conflicts, we are inactive now
            inactiveReason << "some, req conflict";
            setInactive = true;
            break;
          }
          else
          {
            qi.setNoConflict();
          }
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
        TNode r = getValue(c);
        if (isEq != (val == r))
        {
          Trace("ieval-state-debug")
              << "...inactive due to constraint " << c << std::endl;
          setInactive = true;
          inactiveReason << "constraint-true";
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
    Trace("ieval") << "  -> " << q << " inactive due to "
                   << inactiveReason.str() << std::endl;
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
    Assert(d_numActiveQuant.get() > 0);
    d_numActiveQuant = d_numActiveQuant - 1;
  }
}

Node State::getNone() const { return d_none; }

bool State::isNone(TNode n) const { return n == d_none; }

Node State::getSome() const { return d_some; }

bool State::isSome(TNode n) const { return n == d_some; }

Node State::doRewrite(Node n) const { return rewrite(n); }

bool State::isQuantActive(TNode q) const
{
  std::map<Node, QuantInfo>::const_iterator it = d_quantInfo.find(q);
  Assert(it != d_quantInfo.end());
  return it->second.isActive();
}

TNode State::getValue(TNode p) const
{
  if (p.isConst())
  {
    return p;
  }
  std::map<Node, PatTermInfo>::const_iterator it = d_pInfo.find(p);
  if (it != d_pInfo.end())
  {
    return it->second.d_eq;
  }
  // all pattern terms should have been assigned pattern term info
  Assert(!expr::hasBoundVar(p));
  return d_tec->evaluateBase(*this, p);
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
