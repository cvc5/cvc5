/*********************                                                        */
/*! \file preprocessing_pass.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Justin Xu, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessing pass super class
 **
 ** Preprocessing pass super class.
 **/

#include "preprocessing/preprocessing_pass.h"

#include "smt/dump.h"
#include "smt/smt_statistics_registry.h"

namespace CVC4 {
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
    for (const auto& n : assertionList) {
      Dump("assertions") << AssertCommand(Expr(n.toExpr()));
    }
  }
}

PreprocessingPass::PreprocessingPass(PreprocessingPassContext* preprocContext,
                                     const std::string& name)
    : d_name(name), d_timer("preprocessing::" + name) {
  d_preprocContext = preprocContext;
  smtStatisticsRegistry()->registerStat(&d_timer);
}

PreprocessingPass::~PreprocessingPass() {
  Assert(smt::smtEngineInScope());
  if (smtStatisticsRegistry() != nullptr) {
    smtStatisticsRegistry()->unregisterStat(&d_timer);
  }
}

}  // namespace preprocessing
}  // namespace CVC4
