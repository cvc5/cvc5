/*********************                                                        */
/*! \file ite_simp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief ITE simplification preprocessing pass.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PASSES__ITE_SIMP_H
#define CVC4__PREPROCESSING__PASSES__ITE_SIMP_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
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
    Statistics();
    ~Statistics();
  };

  bool doneSimpITE(AssertionPipeline *assertionsToPreprocesss);

  /** A collection of ite preprocessing passes. */
  util::ITEUtilities d_iteUtilities;

  Statistics d_statistics;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif
