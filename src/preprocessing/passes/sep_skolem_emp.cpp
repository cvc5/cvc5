/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The sep-pre-skolem-emp preprocessing pass.
 */

#include "preprocessing/passes/sep_skolem_emp.h"

#include <string>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/skolem_manager.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

namespace cvc5 {
namespace preprocessing {
namespace passes {

using namespace std;
using namespace cvc5::theory;

namespace {

Node preSkolemEmp(Node n,
                         bool pol,
                         std::map<bool, std::map<Node, Node>>& visited)
{
  std::map<Node, Node>::iterator it = visited[pol].find(n);
  if (it == visited[pol].end())
  {
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* sm = nm->getSkolemManager();
    Trace("sep-preprocess") << "Pre-skolem emp " << n << " with pol " << pol
                            << std::endl;
    Node ret = n;
    if (n.getKind() == kind::SEP_EMP)
    {
      if (!pol)
      {
        TypeNode tnx = n[0].getType();
        TypeNode tny = n[1].getType();
        Node x =
            sm->mkDummySkolem("ex", tnx, "skolem location for negated emp");
        Node y = sm->mkDummySkolem("ey", tny, "skolem data for negated emp");
        return nm
            ->mkNode(kind::SEP_STAR,
                     nm->mkNode(kind::SEP_PTO, x, y),
                     nm->mkConst(true))
            .negate();
      }
    }
    else if (n.getKind() != kind::FORALL && n.getNumChildren() > 0)
    {
      std::vector<Node> children;
      bool childChanged = false;
      if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(n.getOperator());
      }
      for (unsigned i = 0; i < n.getNumChildren(); i++)
      {
        bool newPol, newHasPol;
        QuantPhaseReq::getPolarity(n, i, true, pol, newHasPol, newPol);
        Node nc = n[i];
        if (newHasPol)
        {
          nc = preSkolemEmp(n[i], newPol, visited);
          childChanged = childChanged || nc != n[i];
        }
        children.push_back(nc);
      }
      if (childChanged)
      {
        return nm->mkNode(n.getKind(), children);
      }
    }
    visited[pol][n] = ret;
    return n;
  }
  else
  {
    return it->second;
  }
}

}  // namespace

SepSkolemEmp::SepSkolemEmp(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "sep-skolem-emp"){};

PreprocessingPassResult SepSkolemEmp::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::map<bool, std::map<Node, Node>> visited;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    Node prev = (*assertionsToPreprocess)[i];
    bool pol = true;
    Node next = preSkolemEmp(prev, pol, visited);
    if (next != prev)
    {
      assertionsToPreprocess->replace(i, Rewriter::rewrite(next));
      Trace("sep-preprocess") << "*** Preprocess sep " << prev << endl;
      Trace("sep-preprocess") << "   ...got " << (*assertionsToPreprocess)[i]
                              << endl;
    }
    visited.clear();
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
