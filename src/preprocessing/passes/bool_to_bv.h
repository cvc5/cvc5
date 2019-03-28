/*********************                                                        */
/*! \file bool_to_bv.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar, Makai Mann, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The BoolToBV preprocessing pass
 **
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__BOOL_TO_BV_H
#define __CVC4__PREPROCESSING__PASSES__BOOL_TO_BV_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/bv/theory_bv_utils.h"
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
    IntStat d_numIteToBvite;
    IntStat d_numTermsLowered;
    IntStat d_numTermsForcedLowered;
    Statistics();
    ~Statistics();
  };

  /* Takes an assertion and tries to create more bit-vector structure */
  Node lowerAssertion(const TNode& a);

  /* Tries to lower one node to a width-one bit-vector */
  void lowerNode(const TNode& n);

  /* Returns cached node if it exists, otherwise returns the node */
  Node fromCache(TNode n) const;

  /** Checks if any of the nodes children were rebuilt,
   *  in which case n needs to be rebuilt as well
   */
  bool needToRebuild(TNode n) const;

  Statistics d_statistics;

  /* Keeps track of lowered nodes */
  std::unordered_map<Node, Node, NodeHashFunction> d_lowerCache;
};  // class BoolToBV

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__BOOL_TO_BV_H */
