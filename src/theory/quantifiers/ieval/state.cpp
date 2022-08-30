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
      d_tevMode(ieval::TermEvaluatorMode::NONE)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  TypeNode btype = nm->booleanType();
  d_none = sm->mkSkolemFunction(SkolemFunId::IEVAL_NONE, btype);
  d_some = sm->mkSkolemFunction(SkolemFunId::IEVAL_SOME, btype);
}


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

Node State::getNone() const { return d_none; }

bool State::isNone(TNode n) const { return n == d_none; }

Node State::getSome() const { return d_some; }

bool State::isSome(TNode n) const { return n == d_some; }

Node State::doRewrite(Node n) const { return rewrite(n); }

TNode State::evaluate(TNode n) const
{
  if (n.isConst())
  {
    return n;
  }
  // all pattern terms should have been assigned pattern term info
  Assert(!expr::hasBoundVar(n));
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
  Assert(!expr::hasBoundVar(p));
  return d_tec->evaluateBase(*this, p);
}

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
