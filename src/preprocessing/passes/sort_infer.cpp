/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sort inference preprocessing pass.
 */

#include "preprocessing/passes/sort_infer.h"

#include "options/smt_options.h"
#include "options/uf_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/dump_manager.h"
#include "theory/rewriter.h"
#include "theory/sort_inference.h"
#include "theory/theory_engine.h"

using namespace std;

namespace cvc5 {
namespace preprocessing {
namespace passes {

SortInferencePass::SortInferencePass(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "sort-inference")
{
}

PreprocessingPassResult SortInferencePass::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  theory::SortInference* si =
      d_preprocContext->getTheoryEngine()->getSortInference();

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
    SmtEngine* smt = d_preprocContext->getSmt();
    smt::DumpManager* dm = smt->getDumpManager();
    for (const std::pair<const Node, Node>& mrf : model_replace_f)
    {
      dm->setPrintFuncInModel(mrf.first, false);
      dm->setPrintFuncInModel(mrf.second, true);
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
}  // namespace cvc5
