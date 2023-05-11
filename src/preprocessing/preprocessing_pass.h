/******************************************************************************
 * Top contributors (to current version):
 *   Justin Xu, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The preprocessing pass super class
 *
 * Implementation of the preprocessing pass super class. Preprocessing passes
 * that inherit from this class, need to pass their name to the constructor to
 * register the pass appropriately. The core of a preprocessing pass lives
 * in applyInternal(), which operates on a list of assertions and is called
 * from apply() in the super class. The apply() method automatically takes
 * care of the following:
 *
 * - Dumping assertions before and after the pass
 * - Initializing the timer
 * - Tracing and chatting
 *
 * Optionally, preprocessing passes can overwrite the initInteral() method to
 * do work that only needs to be done once.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PREPROCESSING_PASS_H
#define CVC5__PREPROCESSING__PREPROCESSING_PASS_H

#include <string>

#include "smt/env_obj.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace preprocessing {

class AssertionPipeline;
class PreprocessingPassContext;

/**
 * Preprocessing passes return a result which indicates whether a conflict has
 * been detected during preprocessing.
 */
enum PreprocessingPassResult { CONFLICT, NO_CONFLICT };

class PreprocessingPass : protected EnvObj
{
 public:
  /* Preprocesses a list of assertions assertionsToPreprocess */
  PreprocessingPassResult apply(AssertionPipeline* assertionsToPreprocess);

  PreprocessingPass(PreprocessingPassContext* preprocContext,
                    const std::string& name);
  virtual ~PreprocessingPass();

 protected:

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
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PREPROCESSING_PASS_H */
