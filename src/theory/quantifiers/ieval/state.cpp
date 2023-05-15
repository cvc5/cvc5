/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

State::State(Env& env, context::Context* c, QuantifiersState& qs, TermDb& tdb)
    : EnvObj(env),
      d_ctx(c),
      d_qstate(qs),
      d_tdb(tdb),
      d_tevMode(ieval::TermEvaluatorMode::NONE),
      d_registeredTerms(c),
      d_registeredBaseTerms(c),
      d_initialized(c, false),
      d_numActiveQuant(c, 0)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  TypeNode btype = nm->booleanType();
  d_none = sm->mkSkolemFunction(SkolemFunId::IEVAL_NONE, btype);
  d_some = sm->mkSkolemFunction(SkolemFunId::IEVAL_SOME, btype);
}

bool State::hasInitialized() const { return d_initialized.get(); }

bool State::initialize()
{
  Assert(!d_initialized.get());
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

void State::setEvaluatorMode(TermEvaluatorMode tev)
{
  d_tevMode = tev;
  // initialize the term evaluator, which is freshly allocated
  if (tev == TermEvaluatorMode::CONFLICT || tev == TermEvaluatorMode::PROP
      || tev == TermEvaluatorMode::NO_ENTAIL)
  {
    // finding conflict, propagating, or non-entailed instances all
    // involve the entailment term evaluator
    d_tec.reset(new TermEvaluatorEntailed(d_env, tev, d_qstate, d_tdb));
  }
}

void State::watch(Node q, const std::vector<Node>& vars, Node body)
{
  // Note this method does not rely on d_tec, since evaluation may be
  // context dependent.
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
  const std::map<TNode, bool>& cterms = it->second.getConstraints();
  for (const std::pair<const TNode, bool>& c : cterms)
  {
    // we will notify the quantified formula when the pattern becomes set
    PatTermInfo& pi = getOrMkPatTermInfo(c.first);
    // when the constraint term is assigned, we notify q
    pi.d_parentNotify.push_back(q);
    // we visit the constraint term below
    visit.push_back(c.first);
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
        // we don't traverse into operators here
        children.insert(cur.begin(), cur.end());
        for (TNode cc : children)
        {
          // skip constants
          if (cc.isConst())
          {
            continue;
          }
          nchild++;
          // require notifications to parent
          PatTermInfo& pic = getOrMkPatTermInfo(cc);
          pic.d_parentNotify.push_back(cur);
          visit.push_back(cc);
        }
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

bool State::assignVar(TNode v,
                      TNode r,
                      std::vector<Node>& assignedQuants,
                      bool trackAssignedQuant)
{
  // notify that the variable is equal to the ground term
  Trace("ieval") << "ASSIGN: " << v << " := " << r << std::endl;
  Assert(d_initialized.get());
  // note that we allow setting patterns to terms that evaluate to "none",
  // e.g. for conflict-based instantiation where a variable is entailed
  // equal to a term in the body of the quantified formula that is not
  // registered to the term database.
  Assert(isNone(getValue(r)) || getValue(r) == r)
      << "Unexpected value " << getValue(r) << " for " << r;
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

void State::getFailureExp(Node q, std::unordered_set<Node>& processed) const
{
  const QuantInfo& qi = getQuantInfo(q);
  TNode failConstraint = qi.getFailureConstraint();
  Assert(!failConstraint.isNull());
  std::vector<TNode> visit;
  visit.push_back(failConstraint);
  do
  {
    TNode cur = visit.back();
    visit.pop_back();
    if (processed.find(cur) == processed.end())
    {
      processed.insert(cur);
      // as an optimization, only visit children of terms that have bound
      // variables
      if (!expr::hasBoundVar(cur) || !QuantInfo::isTraverseTerm(cur))
      {
        continue;
      }
      Assert(d_pInfo.find(cur) != d_pInfo.end())
          << "Missing pattern info for " << cur;
      const PatTermInfo& pi = getPatTermInfo(cur);
      TNode pcexp = pi.d_evalExpChild.get();
      if (!pcexp.isNull())
      {
        // partial evaluation was forced by single child
        visit.push_back(pcexp);
      }
      else
      {
        // used all children to evaluate, add all to visit list
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  } while (!visit.empty());
}

bool State::isFinished() const { return d_numActiveQuant == 0; }

QuantInfo& State::getQuantInfo(TNode q)
{
  std::map<Node, QuantInfo>::iterator it = d_quantInfo.find(q);
  Assert(it != d_quantInfo.end());
  return it->second;
}

const QuantInfo& State::getQuantInfo(TNode q) const
{
  std::map<Node, QuantInfo>::const_iterator it = d_quantInfo.find(q);
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

const PatTermInfo& State::getPatTermInfo(TNode p) const
{
  std::map<Node, PatTermInfo>::const_iterator it = d_pInfo.find(p);
  Assert(it != d_pInfo.end());
  return it->second;
}

void State::notifyPatternEqGround(TNode p, TNode g)
{
  Trace("ieval-state-debug")
      << "Notify pattern eq ground: " << p << " == " << g << std::endl;
  Assert(!g.isNull());
  Assert(!expr::hasFreeVar(g));
  // note that we allow setting patterns to terms that evaluate to "none",
  // e.g. for conflict-based instantiation where a variable is entailed
  // equal to a term in the body of the quantified formula that is not
  // registered to the term database.
  Assert(isNone(d_tec->evaluateBase(*this, g))
         || d_tec->evaluateBase(*this, g) == g)
      << "Bad eval: " << d_tec->evaluateBase(*this, g) << " " << g;
  std::map<Node, PatTermInfo>::iterator it = d_pInfo.find(p);
  if (it == d_pInfo.end())
  {
    // in rare cases, we may be considering a quantified formula not containing
    // one of its bound variables, e.g. if the variable is in an annotation
    // (pattern) only, or if only in nested quantification.
    return;
  }
  if (!it->second.isActive())
  {
    // already assigned
    return;
  }
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
    Trace("ieval-state-debug")
        << "process notifications (" << p << ", " << g << ")" << std::endl;
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
  Assert(!val.isNull());
  Assert(val.getType().isBoolean());
  if (!val.isConst() && val != d_none)
  {
    // in the rare case that we evaluate to non-constant, we treat this as
    // "some" here instead. This can happen if a term is congruent to an
    // (unassigned) Boolean term.
    val = d_some;
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
      if (TraceIsOn("ieval"))
      {
        inactiveReason << "none, req conflict/prop";
      }
      setInactive = true;
    }
    else
    {
      qi.setNoConflict();
    }
  }
  else if (isSome(val))
  {
    // it has the "some" value, and we have any constraint, we remain
    // active but are not strictly a conflict
    if (d_tevMode == TermEvaluatorMode::CONFLICT)
    {
      // if we require conflicts, we are inactive now
      if (TraceIsOn("ieval"))
      {
        inactiveReason << "some, req conflict";
      }
      setInactive = true;
    }
    else
    {
      qi.setNoConflict();
    }
  }
  else
  {
    Assert(val.isConst());
    const std::map<TNode, bool>& cs = qi.getConstraints();
    std::map<TNode, bool>::const_iterator itm = cs.find(p);
    Assert(itm != cs.end());
    if (val.getConst<bool>() != itm->second)
    {
      setInactive = true;
      if (TraceIsOn("ieval"))
      {
        inactiveReason << "constraint-true";
      }
    }
    else
    {
      Trace("ieval-state-debug")
          << "...satisfied constraint " << p << std::endl;
    }
  }
  // if we should set inactive, update qi and decrement d_numActiveQuant
  if (setInactive)
  {
    qi.setFailureConstraint(p);
    setQuantInactive(qi);
    Trace("ieval") << "  -> " << q << " inactive due to "
                   << inactiveReason.str() << ", from " << p << std::endl;
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

TNode State::getNone() const { return d_none; }

bool State::isNone(TNode n) const { return n == d_none; }

TNode State::getSome() const { return d_some; }

bool State::isSome(TNode n) const { return n == d_some; }

Node State::doRewrite(Node n) const { return rewrite(n); }

bool State::isQuantActive(TNode q) const
{
  std::map<Node, QuantInfo>::const_iterator it = d_quantInfo.find(q);
  Assert(it != d_quantInfo.end());
  return it->second.isActive();
}

TNode State::evaluate(TNode n) const
{
  if (n.isConst())
  {
    return n;
  }
  // all pattern terms should have been assigned pattern term info
  Assert(!expr::hasFreeVar(n));
  return d_tec->evaluateBase(*this, n);
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
  Assert(!expr::hasFreeVar(p));
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
