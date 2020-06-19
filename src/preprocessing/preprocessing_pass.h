/*********************                                                        */
/*! \file preprocessing_pass.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Justin Xu, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessing pass super class
 **
 ** Implementation of the preprocessing pass super class. Preprocessing passes
 ** that inherit from this class, need to pass their name to the constructor to
 ** register the pass appropriately. The core of a preprocessing pass lives
 ** in applyInternal(), which operates on a list of assertions and is called
 ** from apply() in the super class. The apply() method automatically takes
 ** care of the following:
 **
 ** - Dumping assertions before and after the pass
 ** - Initializing the timer
 ** - Tracing and chatting
 **
 ** Optionally, preprocessing passes can overwrite the initInteral() method to
 ** do work that only needs to be done once.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PREPROCESSING_PASS_H
#define CVC4__PREPROCESSING__PREPROCESSING_PASS_H

#include <string>

#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/smt_engine_scope.h"
#include "theory/logic_info.h"

namespace CVC4 {
namespace preprocessing {

/**
 * Preprocessing passes return a result which indicates whether a conflict has
 * been detected during preprocessing.
 */
enum PreprocessingPassResult { CONFLICT, NO_CONFLICT };

class PreprocessingPass {
 public:
  /* Preprocesses a list of assertions assertionsToPreprocess */
  PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);

  PreprocessingPass(PreprocessingPassContext* preprocContext,
                    const std::string& name);
  virtual ~PreprocessingPass();

 protected:
  /*
   * Method for dumping assertions within a pass. Also called before and after
   * applying the pass.
   */
  void dumpAssertions(const char* key, const AssertionPipeline& assertionList);

  /*
   * Abstract method that each pass implements to do the actual preprocessing.
   */
  virtual PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) = 0;

  /* Context for Preprocessing Passes that initializes necessary variables */
  PreprocessingPassContext* d_preprocContext;

 private:
  /* Name of pass */
  std::string d_name;
  /* Timer for registering the preprocessing time of this pass */
  TimerStat d_timer;
};

}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PREPROCESSING_PASS_H */
