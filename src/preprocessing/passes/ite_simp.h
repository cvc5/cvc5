/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * ITE simplification preprocessing pass.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__ITE_SIMP_H
#define CVC5__PREPROCESSING__PASSES__ITE_SIMP_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/util/ite_utilities.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class ITESimp : public PreprocessingPass
{
 public:
   ITESimp(PreprocessingPassContext* preprocContext);

 protected:
   PreprocessingPassResult applyInternal(
       AssertionPipeline* assertionsToPreprocess) override;

 private:
  struct Statistics
  {
    IntStat d_arithSubstitutionsAdded;
    Statistics(StatisticsRegistry& reg);
  };

  Node simpITE(util::ITEUtilities* ite_utils, TNode assertion);
  bool doneSimpITE(AssertionPipeline *assertionsToPreprocesss);

  /** A collection of ite preprocessing passes. */
  util::ITEUtilities d_iteUtilities;

  Statistics d_statistics;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif
