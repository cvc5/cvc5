/******************************************************************************
 * Top contributors (to current version):
 *   Justin Xu, Abdalrhman Mohamed, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "smt/dump.h"
#include "smt/output_manager.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "util/statistics_stats.h"

namespace cvc5 {
namespace preprocessing {

PreprocessingPassResult PreprocessingPass::apply(
    AssertionPipeline* assertionsToPreprocess) {
  TimerStat::CodeTimer codeTimer(d_timer);
  Trace("preprocessing") << "PRE " << d_name << std::endl;
  Chat() << d_name << "..." << std::endl;
  dumpAssertions(("pre-" + d_name).c_str(), *assertionsToPreprocess);
  PreprocessingPassResult result = applyInternal(assertionsToPreprocess);
  dumpAssertions(("post-" + d_name).c_str(), *assertionsToPreprocess);
  Trace("preprocessing") << "POST " << d_name << std::endl;
  return result;
}

void PreprocessingPass::dumpAssertions(const char* key,
                                       const AssertionPipeline& assertionList) {
  if (Dump.isOn("assertions") && Dump.isOn(std::string("assertions:") + key))
  {
    // Push the simplified assertions to the dump output stream
    OutputManager& outMgr = d_preprocContext->getSmt()->getOutputManager();
    const Printer& printer = outMgr.getPrinter();
    std::ostream& out = outMgr.getDumpOut();

    for (const auto& n : assertionList)
    {
      printer.toStreamCmdAssert(out, n);
    }
  }
}

PreprocessingPass::PreprocessingPass(PreprocessingPassContext* preprocContext,
                                     const std::string& name)
    : d_name(name),
      d_timer(smtStatisticsRegistry().registerTimer("preprocessing::" + name))
{
  d_preprocContext = preprocContext;
}

PreprocessingPass::~PreprocessingPass() {
  Assert(smt::smtEngineInScope());
}

}  // namespace preprocessing
}  // namespace cvc5
