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
                             TermDb& tdb,
                             TermEvaluatorMode tev,
                             bool genLearning,
                             bool canonize,
                             bool trackAssignedQuant)
    : EnvObj(env),
      d_context(),
      d_genLearning(genLearning),
      d_canonize(canonize),
      d_trackAssignedQuant(trackAssignedQuant),
      d_state(env, &d_context, qs, tdb),
      d_varMap(&d_context),
      d_quantList(&d_context),
      d_varList(&d_context)
{
  setEvaluatorMode(tev);
}

void InstEvaluator::watch(Node q)
{
  Assert(q.getKind() == kind::FORALL);
  watch(q, q[1]);
}

void InstEvaluator::watch(Node q, Node body)
{
  Assert(q.getKind() == kind::FORALL);
  // must provide all quantified formulas before initializing the state
  Assert(d_context.getLevel() == 0);
  std::vector<Node> vars;
  if (d_canonize)
  {
    body = d_tcanon.getCanonicalTerm(body, d_canonVisited);
    for (const Node& v : q[0])
    {
      vars.push_back(lookupCanonicalTerm(v));
    }
  }
  else
  {
    // if we aren't canonizing, we should never add more than one quantified
    // formula
    Assert(d_quantList.empty());
    Assert(d_varList.empty());
    vars.insert(vars.end(), q[0].begin(), q[0].end());
  }
  d_quantList.push_back(q);
  for (const Node& v : vars)
  {
    d_varList.push_back(v);
  }
  d_state.watch(q, vars, body);
}

bool InstEvaluator::initialize()
{
  // We ensure initialized before we push, since it is context independent.
  // This does the initial evaluations of (ground) subterms in quantified
  // formulas.
  if (d_state.hasInitialized())
  {
    return !d_state.isFinished();
  }
  // Always push an outermost context here. This is because the initialization
  // of ground terms depends on the (SAT) context.
  d_context.push();
  // clear what we have learned
  if (d_genLearning)
  {
    d_itrie.reset(new IndexTrie);
  }
  if (!d_state.initialize())
  {
    learnFailure();
    return false;
  }
  Assert(d_state.hasInitialized());
  return true;
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
  // initialize if not done so already
  if (!initialize())
  {
    return false;
  }
  // push the context
  d_context.push();
  // use the canonical variable for the state
  TNode vc = lookupCanonicalTerm(v);
  // evaluate the term
  Node r = d_state.evaluate(s);
  // store the variable mapping
  d_varMap[vc] = r;
  // if we are generalizing failures, check if there is a learned failure
  if (checkLearnedFailure())
  {
    d_context.pop();
    return false;
  }
  // note that the first assigned variable will force an initialization of the
  // state
  if (!d_state.assignVar(vc, r, assignedQuants, d_trackAssignedQuant))
  {
    learnFailure();
    d_context.pop();
    return false;
  }
  return true;
}

void InstEvaluator::pop() { d_context.pop(); }

void InstEvaluator::resetAll(bool isSoft)
{
  if (!d_state.hasInitialized())
  {
    // not necessary to reset if we have not initialized
    return;
  }
  // pop to level one if soft, zero if not soft
  Assert(d_context.getLevel() >= 1);
  d_context.popto(isSoft ? 1 : 0);
}

std::vector<Node> InstEvaluator::getInstantiationFor(Node q) const
{
  NodeNodeMap::const_iterator it;
  std::vector<Node> inst;
  for (const Node& v : q[0])
  {
    // must get the canonized variable
    Node vc = lookupCanonicalTerm(v);
    it = d_varMap.find(v);
    if (it != d_varMap.end())
    {
      inst.push_back(it->second);
    }
    else
    {
      inst.push_back(v);
    }
  }
  return inst;
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
  std::vector<bool> mask;
  std::vector<Node> cterms = getCurrentTerms();
  for (const Node& v : d_varList)
  {
    mask.push_back(processed.find(v) != processed.end());
  }
  Assert(d_itrie != nullptr);
  d_itrie->add(mask, cterms);
}

bool InstEvaluator::checkLearnedFailure() const
{
  if (!d_genLearning)
  {
    return false;
  }
  // see if the current terms exist
  std::vector<Node> cterms = getCurrentTerms();
  Assert(d_itrie != nullptr);
  size_t nonBlankLength;
  return d_itrie->find(cterms, nonBlankLength);
}

std::vector<Node> InstEvaluator::getCurrentTerms() const
{
  std::vector<Node> terms;
  NodeNodeMap::const_iterator it;
  for (const Node& v : d_varList)
  {
    it = d_varMap.find(v);
    if (it != d_varMap.end())
    {
      terms.push_back(it->second);
    }
    else
    {
      // unassigned
      terms.push_back(Node::null());
    }
  }
  return terms;
}

Node InstEvaluator::lookupCanonicalTerm(TNode n) const
{
  if (d_canonize)
  {
    std::map<TNode, Node>::const_iterator itc = d_canonVisited.find(n);
    Assert(itc != d_canonVisited.end());
    return itc->second;
  }
  return n;
}

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
