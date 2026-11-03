/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Preprocessing pass that lifts if-then-else terms out of theory predicates.
 */

#include "preprocessing/passes/ite_lift.h"

#include "preprocessing/assertion_pipeline.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

IteLift::IteLift(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ite-lift")
{
}

PreprocessingPassResult IteLift::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node a = (*assertionsToPreprocess)[i];
    Node an = convert(a);
    if (an != a)
    {
      assertionsToPreprocess->replace(
          i, an, nullptr, TrustId::PREPROCESS_ITE_LIFT);
      if (assertionsToPreprocess->isInConflict())
      {
        return PreprocessingPassResult::CONFLICT;
      }
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

Node IteLift::convert(TNode n)
{
  std::unordered_map<Node, Node>::iterator it = d_cache.find(n);
  if (it != d_cache.end())
  {
    return it->second;
  }
  Node ret = n;
  // we do not lift if-then-else terms in quantified formulas
  if (n.getNumChildren() > 0 && !n.isClosure())
  {
    std::vector<Node> children;
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.push_back(n.getOperator());
    }
    bool childChanged = false;
    for (const Node& nc : n)
    {
      Node ncc = convert(nc);
      childChanged = childChanged || ncc != nc;
      children.push_back(ncc);
    }
    if (childChanged)
    {
      ret = nodeManager()->mkNode(n.getKind(), children);
    }
    ret = liftAtom(ret);
  }
  d_cache[n] = ret;
  return ret;
}

Node IteLift::liftAtom(const Node& n) const
{
  // Note that Boolean connectives are excluded by the requirement below that
  // the other argument is not Boolean.
  if (n.getNumChildren() != 2 || !n.getType().isBoolean()
      || n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    return n;
  }
  for (size_t i = 0; i < 2; i++)
  {
    const Node& other = n[1 - i];
    if (n[i].getKind() == Kind::ITE && (other.isVar() || other.isConst())
        && !other.getType().isBoolean())
    {
      // P(x, ite(c, t, s)) ---> ite(c, P(x, t), P(x, s)), where P(x, t) and
      // P(x, s) are lifted recursively
      NodeManager* nm = nodeManager();
      std::vector<Node> children(n.begin(), n.end());
      std::vector<Node> branches;
      for (size_t j = 1; j <= 2; j++)
      {
        children[i] = n[i][j];
        branches.push_back(liftAtom(nm->mkNode(n.getKind(), children)));
      }
      return nm->mkNode(Kind::ITE, n[i][0], branches[0], branches[1]);
    }
  }
  return n;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
