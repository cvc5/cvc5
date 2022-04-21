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

InstEvaluator::InstEvaluator(Env& env, QuantifiersState& qs, TermRegistry& tr, bool doCanonize)
    : EnvObj(env), d_context(), d_qs(qs), d_treg(tr), d_doCanonize(doCanonize), d_state(env, &d_context, qs, tr.getTermDatabase())
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
  d_state.watch(q, body);
}

void InstEvaluator::push()
{
  d_context.push();
}

bool InstEvaluator::push(TNode v, TNode s, std::vector<Node>& assignedQuants)
{
  d_context.push();
  if (!d_state.assignVar(v, s, assignedQuants))
  {
    d_context.pop();
  }
}

void InstEvaluator::pop() { d_context.pop(); }

std::vector<Node> InstEvaluator::getInstantiationFor(Node q) 
{
  std::vector<Node> vars;
  for (const Node& v : q[0])
  {
    vars.push_back(d_state.getValue(v));
  }
  return vars;
}

}
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
