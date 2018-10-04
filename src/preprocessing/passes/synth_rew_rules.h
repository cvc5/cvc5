/*********************                                                        */
/*! \file synth_rew_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A technique for synthesizing candidate rewrites of the form t1 = t2,
 ** where t1 and t2 are subterms of the input.
 **/

#ifndef __CVC4__PREPROCESSING__PASSES__SYNTH_REW_RULES_H
#define __CVC4__PREPROCESSING__PASSES__SYNTH_REW_RULES_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

/**
 * This class computes candidate rewrite rules of the form t1 = t2, where
 * t1 and t2 are subterms of assertionsToPreprocess. It prints
 * "candidate-rewrite" messages on the output stream of options.
 *
 * In contrast to other preprocessing passes, this pass does not modify
 * the set of assertions.
 */
class SynthRewRulesPass : public PreprocessingPass
{
 public:
  SynthRewRulesPass(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__SYNTH_REW_RULES_H */
