/*********************                                                        */
/*! \file fp_ic_pass.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The FpIcPre preprocessing pass
 *
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__FP_IC_PASS_H
#define __CVC4__PREPROCESSING__PASSES__FP_IC_PASS_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

class FpIcPre : public PreprocessingPass
{
 public:
  FpIcPre(PreprocessingPassContext* preprocContext);

 protected:
  int getCtnIndex( Node x, Node n);
  Node solve( Node x, Node p, std::vector< Node >& ics, int ctnIndex=-1, bool useIc=true );
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__FP_IC_PASS_H */
