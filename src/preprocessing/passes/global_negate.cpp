/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Yoni Zohar, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of global_negate.
 */

#include "preprocessing/passes/global_negate.h"

#include <vector>

#include "expr/node.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/rewriter.h"

using namespace std;
using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

Node GlobalNegate::simplify(const std::vector<Node>& assertions,
                            NodeManager* nm)
{
  Assert(!assertions.empty());
  Trace("cegqi-gn") << "Global negate : " << std::endl;
  // collect free variables in all assertions
  std::vector<Node> free_vars;
  std::vector<TNode> visit;
  std::unordered_set<TNode> visited;
  for (const Node& as : assertions)
  {
    Trace("cegqi-gn") << "  " << as << std::endl;
    TNode cur = as;
    // compute free variables
    visit.push_back(cur);
    do
    {
      cur = visit.back();
      visit.pop_back();
      if (visited.find(cur) == visited.end())
      {
        visited.insert(cur);
        if (cur.isVar() && cur.getKind() != BOUND_VARIABLE)
        {
          free_vars.push_back(cur);
        }
        for (const TNode& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    } while (!visit.empty());
  }

  Node body;
  if (assertions.size() == 1)
  {
    body = assertions[0];
  }
  else
  {
    body = nm->mkNode(AND, assertions);
  }

  // do the negation
  body = body.negate();

  if (!free_vars.empty())
  {
    std::vector<Node> bvs;
    for (const Node& v : free_vars)
    {
      Node bv = nm->mkBoundVar(v.getType());
      bvs.push_back(bv);
    }

    body = body.substitute(
        free_vars.begin(), free_vars.end(), bvs.begin(), bvs.end());

    Node bvl = nm->mkNode(BOUND_VAR_LIST, bvs);

    body = nm->mkNode(FORALL, bvl, body);
  }

  Trace("cegqi-gn-debug") << "...got (pre-rewrite) : " << body << std::endl;
  body = rewrite(body);
  Trace("cegqi-gn") << "...got (post-rewrite) : " << body << std::endl;
  return body;
}

GlobalNegate::GlobalNegate(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "global-negate"){};

PreprocessingPassResult GlobalNegate::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager* nm = NodeManager::currentNM();
  Node simplifiedNode = simplify(assertionsToPreprocess->ref(), nm);
  Node trueNode = nm->mkConst(true);
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    if (i == 0)
    {
      assertionsToPreprocess->replace(i, simplifiedNode);
    }
    else
    {
      assertionsToPreprocess->replace(i, trueNode);
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
