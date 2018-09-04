/*********************                                                        */
/*! \file bool_to_bv.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The BoolToBv preprocessing pass
 **
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__BOOL_TO_BV_H
#define __CVC4__PREPROCESSING__PASSES__BOOL_TO_BV_H

#include "preprocessing/passes/bv_to_bool.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

class BoolToBV : public PreprocessingPass
{
 public:
  BoolToBV(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  struct Statistics
  {
    IntStat d_numTermsLowered;
    IntStat d_numAtomsLowered;
    IntStat d_numTermsForcedLowered;
    Statistics();
    ~Statistics();
  };

  void lowerBoolToBv(const std::vector<Node>& assertions,
                     std::vector<Node>& new_assertions);
  void addToLowerCache(TNode term, Node new_term);
  Node getLowerCache(TNode term) const;
  bool hasLowerCache(TNode term) const;
  Node lowerNode(TNode current, bool topLevel = false);
  NodeNodeMap d_lowerCache;
  Node d_one;
  Node d_zero;
  Statistics d_statistics;
};  // class
}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__BOOL_TO_BV_H */
