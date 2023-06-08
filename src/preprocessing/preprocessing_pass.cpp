/******************************************************************************
 * Top contributors (to current version):
 *   Justin Xu, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The preprocessing pass super class.
 */

#include "preprocessing/preprocessing_pass.h"

#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "printer/printer.h"
#include "smt/env.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace preprocessing {

PreprocessingPassResult PreprocessingPass::apply(
    AssertionPipeline* assertionsToPreprocess) {
  TimerStat::CodeTimer codeTimer(d_timer);
  Trace("preprocessing") << "PRE " << d_name << std::endl;
  verbose(2) << d_name << "..." << std::endl;
  PreprocessingPassResult result = applyInternal(assertionsToPreprocess);
  Trace("preprocessing") << "POST " << d_name << std::endl;
  return result;
}

PreprocessingPass::PreprocessingPass(PreprocessingPassContext* preprocContext,
                                     const std::string& name)
    : EnvObj(preprocContext->getEnv()),
      d_preprocContext(preprocContext),
      d_name(name),
      d_timer(statisticsRegistry().registerTimer("preprocessing::" + name))
{
}

PreprocessingPass::~PreprocessingPass() {}

}  // namespace preprocessing
}  // namespace cvc5::internal
