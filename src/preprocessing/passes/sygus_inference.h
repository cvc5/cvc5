/*********************                                                        */
/*! \file sygus_inference.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SygusInference
 **/

#ifndef CVC4__PREPROCESSING__PASSES__SYGUS_INFERENCE_H_
#define CVC4__PREPROCESSING__PASSES__SYGUS_INFERENCE_H_

#include <map>
#include <string>
#include <vector>
#include "expr/node.h"

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

/** SygusInference
 *
 * A preprocessing utility that turns a set of (quantified) assertions into a
 * single SyGuS conjecture. If this is possible, we solve for this single Sygus
 * conjecture using a separate copy of the SMT engine. If sygus successfully
 * solves the conjecture, we plug the synthesis solutions back into the original
 * problem, thus obtaining a set of model substitutions under which the
 * assertions should simplify to true.
 */
class SygusInference : public PreprocessingPass
{
 public:
  SygusInference(PreprocessingPassContext* preprocContext);

 protected:
  /**
   * Either replaces all uninterpreted functions in assertions by their
   * interpretation in a sygus solution, or leaves the assertions unmodified.
   */
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /** solve sygus
   *
   * Returns true if we can recast the input problem assertions as a sygus
   * problem and successfully solve it using a separate call to an SMT engine.
   *
   * We fail if either a sygus conjecture that corresponds to assertions cannot
   * be inferred, or the sygus conjecture we infer is infeasible.
   *
   * If this function returns true, then we add all uninterpreted symbols s in
   * assertions to funs and their corresponding solution to sols.
   */
  bool solveSygus(std::vector<Node>& assertions,
                  std::vector<Node>& funs,
                  std::vector<Node>& sols);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PASSES__SYGUS_INFERENCE_H_ */
