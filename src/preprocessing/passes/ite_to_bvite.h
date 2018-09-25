/*********************                                                        */
/*! \file ite_to_bvite.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the CVC4 project.
** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file COPYING in the top-level source
** directory for licensing information.\endverbatim
**
** \brief The IteToBvite preprocessing pass. Converts ITEs to BITVECTOR_ITEs
**         when it's convenient to do so, as implemented by easyToLower
**
**/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__ITE_TO_BVITE_H
#define __CVC4__PREPROCESSING__PASSES__ITE_TO_BVITE_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

class IteToBvite : public PreprocessingPass
{
 public:
  IteToBvite(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  struct Statistics
  {
    IntStat d_numIteToBvite;
    Statistics();
    ~Statistics();
  };

  Node lowerIte(TNode term);
  Node lowerBool(TNode boolTerm);
  bool easyToLower(TNode boolTerm);
  Statistics d_statistics;
};  // class IteToBvite

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__ITE_TO_BVITE_H */
