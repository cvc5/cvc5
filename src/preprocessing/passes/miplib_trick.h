/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The MIPLIB trick preprocessing pass.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__MIPLIB_TRICK_H
#define CVC5__PREPROCESSING__PASSES__MIPLIB_TRICK_H

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class MipLibTrick : public PreprocessingPass
{
 public:
  MipLibTrick(PreprocessingPassContext* preprocContext);
  ~MipLibTrick();

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  struct Statistics
  {
    /** number of assertions removed by miplib pass */
    IntStat d_numMiplibAssertionsRemoved;
    Statistics(StatisticsRegistry& reg);
  };

  size_t removeFromConjunction(
      Node& n, const std::unordered_set<unsigned long>& toRemove);
  /**
   * Collect Boolean variables in the given pipeline, store them in d_boolVars.
   */
  void collectBooleanVariables(AssertionPipeline* assertionsToPreprocess);

  Statistics d_statistics;

  std::vector<Node> d_boolVars;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__MIPLIB_TRICK_H */
