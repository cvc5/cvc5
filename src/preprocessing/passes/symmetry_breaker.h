/*********************                                                        */
/*! \file symmetry_breaker.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Paul Meng, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Symmetry breaker for theories
 **/

#ifndef __CVC4__PREPROCESSING__PASSES__SYMMETRY_BREAKER_H_
#define __CVC4__PREPROCESSING__PASSES__SYMMETRY_BREAKER_H_

#include <map>
#include <string>
#include <vector>
#include "expr/node.h"

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

/**
 * Given a vector of partitions {{v_{11}, ... , v_{1n}}, {v_{m1}, ... , v_{mk}}},
 * the symmetry breaker will generate symmetry breaking constraints for each
 * partition {v_{i1}, ... , v_{ij}} depending on the type of variables
 * in each partition.
 *
 * For a partition of integer, real and bit-vectors variables {v1, ..., vn},
 * we generate ordered constraints: {v1 <= v2, ..., v{n-1} <= vn}.
 * For a partition of variables of other types {v1, ..., vn}, we generate
 * the following two kinds of constraints.
 *
 * 1. Consecutive constraints ensure that equivalence classes over v_1...v_n are
 *    in consecutive segments
 *    v_i = v_j => v_i = v_{j-1} for all 0 <= i < j-1 < j < n
 * 2. Length order constraints ensure that the length of segments occur in
 *    descending order
 *    v_i = v_j => (v_{i} = v_{i-1} OR v_{i-1} = x_{(i-1)-(j-i)})
 *    for all 1 <= i < j < part.size() and (i-1)-(j-i) >= 0
 * */

class SymmetryBreaker
{
 public:
  /**
   * Constructor
   * */
  SymmetryBreaker()
  {
    d_trueNode = NodeManager::currentNM()->mkConst<bool>(true);
    d_falseNode = NodeManager::currentNM()->mkConst<bool>(false);
  }

  /**
   * Destructor
   * */
  ~SymmetryBreaker() {}

  /**
   * This is to generate symmetry breaking constraints for partitions in parts.
   * Since parts are symmetries of the original assertions C,
   * the symmetry breaking constraints SB for parts returned by this function
   * conjuncted with the original assertions SB ^ C is equisatisfiable to C.
   * */
  Node generateSymBkConstraints(const std::vector<std::vector<Node> >& parts);

 private:

  /** True and false constant nodes */
  Node d_trueNode;
  Node d_falseNode;

  /**
   * Get the order kind depending on the type of node.
   * For example, if node is a integer or real, this function would return
   * the operator less than or equal to (<=) so that we can use it to build
   * ordered constraints.
   * */
  Kind getOrderKind(Node node);
};

/**
 * This class detects symmetries in the input assertions in the form of a
 * partition (see symmetry_detect.h), and subsequently adds symmetry breaking
 * constraints that correspond to this partition, using the above class.
 */
class SymBreakerPass : public PreprocessingPass
{
 public:
  SymBreakerPass(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__SYMMETRY_BREAKER_H_ */
