/*********************                                                        */
/*! \file sygus_abduct.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SygusAbduct
 **/

#ifndef __CVC4__PREPROCESSING__PASSES__SYGUS_ABDUCT_H_
#define __CVC4__PREPROCESSING__PASSES__SYGUS_ABDUCT_H_

#include <map>
#include <string>
#include <vector>
#include "expr/node.h"

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

/** SygusAbduct
 *
 * A preprocessing utility that turns a set of (quantified) assertions into a
 * single SyGuS conjecture. If this is possible, we solve for this single Sygus
 * conjecture using a separate copy of the SMT engine. If sygus successfully
 * solves the conjecture, we plug the synthesis solutions back into the original
 * problem, thus obtaining a set of model substitutions under which the
 * assertions should simplify to true.
 */
class SygusAbduct : public PreprocessingPass
{
 public:
  SygusAbduct(PreprocessingPassContext* preprocContext);

 protected:
  /**
   * Either replaces all uninterpreted functions in assertions by their
   * interpretation in a sygus solution, or leaves the assertions unmodified.
   */
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__SYGUS_ABDUCT_H_ */
