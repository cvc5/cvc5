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
                             bool genLearning,
                             bool canonize,
                             bool trackAssignedQuant)
    : EnvObj(env),
      d_context(),
      d_genLearning(genLearning),
      d_canonize(canonize),
      d_trackAssignedQuant(trackAssignedQuant),
      d_state(env, &d_context, qs, tr),
      d_varMap(&d_context),
      d_quantList(&d_context),
      d_varList(&d_context)
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
  d_quantList.push_back(q);
  // must provide all quantified formulas before initializing the state
  Assert(d_context.getLevel() == 0);
  std::vector<Node> vars;
  if (d_canonize)
  {
    std::map<TNode, Node> visited;
    body = d_tcanon.getCanonicalTerm(body, visited);
    std::map<TNode, Node>::iterator it;
    for (const Node& v : q[0])
    {
      it = visited.find(v);
      vars.push_back(it->second);
      // initially map the variable to its canonical form
      if (d_varMap.find(v) == d_varMap.end())
      {
        d_varMap[v] = it->second;
        // remember the varisable
        d_varList.push_back(v);
      }
    }
  }
  else
  {
    vars.insert(vars.end(), q[0].begin(), q[0].end());
  }
  d_state.watch(q, vars, body);
}

void InstEvaluator::push()
{
  // TODO: interface may be useful for popping quantified formulas?
  d_context.push();
}

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
  // We ensure initialized before we push, since it is context independent.
  // This does the initial evaluations of (ground) subterms in quantified
  // formulas.
  if (!d_state.hasInitialized())
  {
    // Always push an outermost context here. This is because the initialization
    // of ground terms depends on the (SAT) context.
    d_context.push();
    if (!d_state.initialize())
    {
      learnFailure();
      return false;
    }
    Assert(d_state.hasInitialized());
  }
  // push the context
  d_context.push();
  TNode canonVar = v;
  if (d_canonize)
  {
    Assert(d_varMap.find(v) != d_varMap.end());
    // use the canonical variable for the state, which should be stored in the
    // variable map
    canonVar = d_varMap[v];
  }
  // note that the first assigned variable will force an initialization of the
  // state
  if (!d_state.assignVar(canonVar, s, assignedQuants, d_trackAssignedQuant))
  {
    learnFailure();
    d_context.pop();
    return false;
  }
  d_varMap[v] = s;
  return true;
}

void InstEvaluator::pop() { d_context.pop(); }

void InstEvaluator::resetAll()
{
  // pop to level zero.
  // TODO: we undo the state's initialization here. We could save this
  // by popping to level 1?
  d_context.popto(0);
}

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

void InstEvaluator::setEvaluatorMode(TermEvaluatorMode tev)
{
  Assert(d_context.getLevel() == 0);
  d_state.setEvaluatorMode(tev);
}

void InstEvaluator::learnFailure()
{
  if (!d_genLearning)
  {
    return;
  }
  std::unordered_set<Node> processed;
  for (const Node& q : d_quantList)
  {
    d_state.getFailureExp(q, processed);
  }
  /*
  for (const Node& v : d_varList)
  {

  }
  */
}

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
