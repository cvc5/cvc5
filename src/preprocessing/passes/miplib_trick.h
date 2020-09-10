/*********************                                                        */
/*! \file miplib_trick.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The MIPLIB trick preprocessing pass
 **
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PASSES__MIPLIB_TRICK_H
#define CVC4__PREPROCESSING__PASSES__MIPLIB_TRICK_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

class MipLibTrick : public PreprocessingPass, public NodeManagerListener
{
 public:
  MipLibTrick(PreprocessingPassContext* preprocContext);
  ~MipLibTrick();

  // NodeManagerListener callbacks to collect d_boolVars.
  void nmNotifyNewVar(TNode n, uint32_t flags) override;
  void nmNotifyNewSkolem(TNode n,
                         const std::string& comment,
                         uint32_t flags) override;

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  struct Statistics
  {
    /** number of assertions removed by miplib pass */
    IntStat d_numMiplibAssertionsRemoved;
    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;

  std::vector<Node> d_boolVars;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PASSES__MIPLIB_TRICK_H */
