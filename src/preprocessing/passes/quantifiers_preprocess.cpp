/*********************                                                        */
/*! \file quantifiers_preprocess.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Caleb Donovick
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Remove rewrite rules, apply pre-skolemization to existential
 *quantifiers
 **
 **
 ** Calls the quantifier rewriter, removing rewrite rules and applying
 ** pre-skolemization to existential quantifiers
 **/

#include "preprocessing/passes/quantifiers_preprocess.h"

#include "base/output.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;

QuantifiersPreprocess::QuantifiersPreprocess(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "quantifiers-preprocess"){};

PreprocessingPassResult QuantifiersPreprocess::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  size_t size = assertionsToPreprocess->size();
  for (size_t i = 0; i < size; ++i)
  {
    Node prev = (*assertionsToPreprocess)[i];
    Node next = quantifiers::QuantifiersRewriter::preprocess(prev);
    if (next != prev)
    {
      assertionsToPreprocess->replace(i, Rewriter::rewrite(next));
      Trace("quantifiers-preprocess") << "*** Pre-skolemize " << prev << endl;
      Trace("quantifiers-preprocess")
          << "   ...got " << (*assertionsToPreprocess)[i] << endl;
    }
  }

  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
