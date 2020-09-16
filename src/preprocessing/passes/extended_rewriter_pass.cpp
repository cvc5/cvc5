/*********************                                                        */
/*! \file extended_rewriter_pass.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The ExtRewPre preprocessing pass
 **
 ** Applies the extended rewriter to assertions
 **/

#include "preprocessing/passes/extended_rewriter_pass.h"

#include "theory/quantifiers/extended_rewrite.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

ExtRewPre::ExtRewPre(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ext-rew-pre"){};

PreprocessingPassResult ExtRewPre::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  theory::quantifiers::ExtendedRewriter extr(options::extRewPrepAgg());
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    assertionsToPreprocess->replace(
        i, extr.extendedRewrite((*assertionsToPreprocess)[i]));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
