/*********************                                                        */
/*! \file bv_to_int.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The BVToInt preprocessing pass
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__BV_TO_INT_H
#define __CVC4__PREPROCESSING__PASSES__BV_TO_INT_H

#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "context/context.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/bv/int_blaster.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using CDNodeMap = context::CDHashMap<Node, Node, NodeHashFunction>;

class BVToInt : public PreprocessingPass
{
 public:
  BVToInt(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

  void addFinalizeAssertions(AssertionPipeline* assertionsToPreprocess,
                             std::vector<Node> additionalConstraints);
  void addSkolemDefinitions(std::map<Node, Node> skolems);
  void defineBVUFAsIntUF(Node bvUF, Node intUF);

  IntBlaster d_intBlaster;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__BV_TO_INT_H */
