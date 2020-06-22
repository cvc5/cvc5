/*********************                                                        */
/*! \file sort_infer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sort inference preprocessing pass
 **/

#include "preprocessing/passes/sort_infer.h"

#include "options/smt_options.h"
#include "options/uf_options.h"
#include "theory/rewriter.h"
#include "theory/sort_inference.h"

using namespace std;

namespace CVC4 {
namespace preprocessing {
namespace passes {

SortInferencePass::SortInferencePass(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "sort-inference")
{
}

PreprocessingPassResult SortInferencePass::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  SortInference* si = d_preprocContext->getTheoryEngine()->getSortInference();

  if (options::sortInference())
  {
    si->initialize(assertionsToPreprocess->ref());
    std::map<Node, Node> model_replace_f;
    std::map<Node, std::map<TypeNode, Node> > visited;
    for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; i++)
    {
      Node prev = (*assertionsToPreprocess)[i];
      Node next = si->simplify(prev, model_replace_f, visited);
      if (next != prev)
      {
        next = theory::Rewriter::rewrite(next);
        assertionsToPreprocess->replace(i, next);
        Trace("sort-infer-preprocess")
            << "*** Preprocess SortInferencePass " << prev << endl;
        Trace("sort-infer-preprocess")
            << "   ...got " << (*assertionsToPreprocess)[i] << endl;
      }
    }
    std::vector<Node> newAsserts;
    si->getNewAssertions(newAsserts);
    for (const Node& na : newAsserts)
    {
      Node nar = theory::Rewriter::rewrite(na);
      Trace("sort-infer-preprocess")
          << "*** Preprocess SortInferencePass : new constraint " << nar
          << endl;
      assertionsToPreprocess->push_back(nar);
    }
    // indicate correspondence between the functions
    // TODO (#2308): move this to a better place
    SmtEngine* smt = smt::currentSmtEngine();
    for (const std::pair<const Node, Node>& mrf : model_replace_f)
    {
      smt->setPrintFuncInModel(mrf.first.toExpr(), false);
      smt->setPrintFuncInModel(mrf.second.toExpr(), true);
    }
  }
  // only need to compute monotonicity on the resulting formula if we are
  // using this option
  if (options::ufssFairnessMonotone())
  {
    si->computeMonotonicity(assertionsToPreprocess->ref());
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
