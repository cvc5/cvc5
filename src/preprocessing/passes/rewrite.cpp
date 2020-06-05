/*********************                                                        */
/*! \file rewrite.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Caleb Donovick
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The rewrite preprocessing pass
 **
 ** Calls the rewriter on every assertion
 **/

#include "preprocessing/passes/rewrite.h"

#include "theory/rewriter.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;


Rewrite::Rewrite(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "rewrite"){};

PreprocessingPassResult Rewrite::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    TNode a = (*assertionsToPreprocess)[i];
    assertionsToPreprocess->replace(
        i, Rewriter::rewrite((*assertionsToPreprocess)[i]));
    if (CVC4::options::proofNew())
    {
      // assertion changed and it was not just reordering a symmetry. The latter
      // test is necessary to prevent a cyclic proof
      if (a != (*assertionsToPreprocess)[i]
          && (a.getKind() != kind::EQUAL
              || (*assertionsToPreprocess)[i].getKind() != kind::EQUAL
              || a[0] != (*assertionsToPreprocess)[i][1]
              || a[1] != (*assertionsToPreprocess)[i][0]))
      {
        // giving the conclusion as an argument as a workaround for checking
        NewProofManager::currentPM()->addStep(
            (*assertionsToPreprocess)[i], PfRule::REWRITE_PREPROCESS, {a}, {});
      }
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
