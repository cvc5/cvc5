/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inst evaluator class.
 */

#include "theory/quantifiers/ieval/inst_evaluator.h"

#include "theory/quantifiers/term_registry.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

InstEvaluator::InstEvaluator(Env& env,
                             QuantifiersState& qs,
                             TermRegistry& tr,
                             TermEvaluator* tec,
                             bool doCanonize,
                             bool trackAssignedQuant)
    : EnvObj(env),
      d_context(),
      d_qs(qs),
      d_treg(tr),
      d_doCanonize(doCanonize),
      d_trackAssignedQuant(trackAssignedQuant),
      d_state(env, &d_context, qs, tr.getTermDatabase(), tec),
      d_varMap(&d_context)
{
}

void InstEvaluator::watch(Node q)
{
  Assert(q.getKind() == kind::FORALL);
  watch(q, q[1]);
}

void InstEvaluator::watch(Node q, Node body)
{
  Assert(q.getKind() == kind::FORALL);
  std::vector<Node> vars;
  if (d_doCanonize)
  {
    std::map<TNode, Node> visited;
    body = d_tcanon.getCanonicalTerm(body, visited);
    std::map<TNode, Node>::iterator it;
    for (const Node& v : q[0])
    {
      it = visited.find(v);
      vars.push_back(it->second);
      d_varMap[v] = it->second;
    }
  }
  else
  {
    vars.insert(vars.end(), q[0].begin(), q[0].end());
  }
  d_state.watch(q, vars, body);
}

void InstEvaluator::push() { d_context.push(); }

bool InstEvaluator::push(TNode v, TNode s)
{
  std::vector<Node> assignedQuants;
  return pushInternal(v, s, assignedQuants);
}

bool InstEvaluator::push(TNode v, TNode s, std::vector<Node>& assignedQuants)
{
  Assert(d_trackAssignedQuant);
  return pushInternal(v, s, assignedQuants);
}

bool InstEvaluator::pushInternal(TNode v,
                                 TNode s,
                                 std::vector<Node>& assignedQuants)
{
  d_context.push();
  TNode canonVar = v;
  if (d_doCanonize)
  {
    canonVar = d_varMap[v];
  }
  d_varMap[v] = s;
  if (!d_state.assignVar(canonVar, s, assignedQuants, d_trackAssignedQuant))
  {
    d_context.pop();
    return false;
  }
  return true;
}

void InstEvaluator::pop() { d_context.pop(); }

std::vector<Node> InstEvaluator::getInstantiationFor(Node q) const
{
  NodeNodeMap::const_iterator it;
  std::vector<Node> vars;
  for (const Node& v : q[0])
  {
    it = d_varMap.find(v);
    if (it != d_varMap.end())
    {
      vars.push_back(it->second);
    }
  }
  return vars;
}

bool InstEvaluator::isFeasible() const { return !d_state.isFinished(); }

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
