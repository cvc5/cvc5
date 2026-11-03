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

#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

IteLift::IteLift(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ite-lift")
{
  if (options().smt.produceProofs)
  {
    d_tpg = std::make_unique<TConvProofGenerator>(d_env,
                                                  nullptr,
                                                  TConvPolicy::FIXPOINT,
                                                  TConvCachePolicy::NEVER,
                                                  "IteLift::tpg");
  }
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
      assertionsToPreprocess->replace(i, an, d_tpg.get());
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

Node IteLift::liftAtom(const Node& n)
{
  // We only consider equalities and arithmetic comparisons, for which the
  // lifting steps can be reconstructed by RARE rewrite rules in proofs.
  Kind k = n.getKind();
  if (k != Kind::EQUAL && k != Kind::GEQ && k != Kind::GT && k != Kind::LEQ
      && k != Kind::LT)
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
      std::vector<Node> liftedBranches;
      for (size_t j = 1; j <= 2; j++)
      {
        children[i] = n[i][j];
        branches.push_back(nm->mkNode(n.getKind(), children));
        liftedBranches.push_back(liftAtom(branches.back()));
      }
      if (d_tpg != nullptr)
      {
        // justify the single lifting step, which is expected to be
        // reconstructed by the RARE rewrite rules for lifting if-then-else
        Node lifted = nm->mkNode(Kind::ITE, n[i][0], branches[0], branches[1]);
        d_tpg->addRewriteStep(
            n, lifted, nullptr, false, TrustId::PREPROCESS_ITE_LIFT);
      }
      return nm->mkNode(
          Kind::ITE, n[i][0], liftedBranches[0], liftedBranches[1]);
    }
  }
  return n;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
