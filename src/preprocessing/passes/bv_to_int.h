/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The bv-to-int preprocessing pass.
 */

#ifndef __CVC5__PREPROCESSING__PASSES__BV_TO_INT_H
#define __CVC5__PREPROCESSING__PASSES__BV_TO_INT_H

#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "context/context.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/bv/int_blaster.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using CDNodeMap = context::CDHashMap<Node, Node>;

class BVToInt : public PreprocessingPass
{
 public:
  BVToInt(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

  // Add the lemmas in `additionalConstraints` to the assertions pipeline.
  void addFinalizeAssertions(AssertionPipeline* assertionsToPreprocess,
                             const std::vector<Node>& additionalConstraints);

  // include the skolem map as substitutions
  void addSkolemDefinitions(const std::map<Node, Node>& skolems);

  IntBlaster d_intBlaster;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* __CVC5__PREPROCESSING__PASSES__BV_TO_INT_H */
