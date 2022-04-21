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

#include "theory/quantifiers/inst_evaluator.h"

#include "expr/node_algorithm.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

InstEvaluator::InstEvaluator(Node q) : d_quant(q), d_currFeasible(true)
{
  Assert (q.getKind()==kind::FORALL);
}

bool InstEvaluator::initialize()
{
  Assert (d_evalBody.empty());
  Assert (d_currFeasible);
  d_currVar = TNode::null();
  d_currSubs = TNode::null();
  // convert and push the body
  return convertAndPush(d_quant[1]);
}

bool InstEvaluator::push(TNode v, TNode s)
{
  Assert (!d_evalBody.empty());
  Assert (d_evalBody.size()<=d_quant[0].getNumChildren());
  Node curr = d_evalBody.back();
  d_currVar = v;
  d_currSubs = s;
  return convertAndPush(curr);
}

bool InstEvaluator::convertAndPush(Node body)
{
  Node cbody = convert(body);
  if (!d_currFeasible || !isFeasibleBody(cbody))
  {
    // do not push, and reset the flag
    d_currFeasible = true;
    return false;
  }
  d_evalBody.push_back(cbody);
  return true;
}

void InstEvaluator::pop()
{
  Assert (!d_evalBody.empty());
  d_evalBody.pop_back();
}

bool InstEvaluator::shouldTraverse(Node n)
{
  if (!d_currFeasible)
  {
    // don't traverse further if already infeasible
    return false;
  }
  // optimization: never traverse ground terms, unless we are initializing
  if (!d_currVar.isNull() && !expr::hasBoundVar(n))
  {
    return false;
  }
  // TODO: could cache the subterms that contain d_currVar?
  return true;
}

Node InstEvaluator::postReconstruct(Node cur, const std::vector<Node>& children, bool childChanged)
{
  if (cur==d_currVar)
  {
  // apply the substitution
    return d_currSubs;
  }
  if (d_currFeasible)
  {
    if (d_currVar.isNull() || childChanged)
    {
      // evaluate
      Node neval = evaluateInternal(cur, children, d_currFeasible);
      return neval;
    }
  }
  // otherwise, just use the default  (TODO: or return null?)
  return NodeConverter::postReconstruct(cur, children, childChanged);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

