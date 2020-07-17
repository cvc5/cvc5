/*********************                                                        */
/*! \file static_learning.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The static learning preprocessing pass
 **
 **/

#include "preprocessing/passes/static_learning.h"

#include <string>

#include "expr/node.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

StaticLearning::StaticLearning(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "static-learning"){};

PreprocessingPassResult StaticLearning::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  d_preprocContext->spendResource(ResourceManager::Resource::PreprocessStep);

  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    NodeBuilder<> learned(kind::AND);
    learned << (*assertionsToPreprocess)[i];
    d_preprocContext->getTheoryEngine()->ppStaticLearn(
        (*assertionsToPreprocess)[i], learned);
    if (learned.getNumChildren() == 1)
    {
      learned.clear();
    }
    else
    {
      assertionsToPreprocess->replace(i, learned);
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
