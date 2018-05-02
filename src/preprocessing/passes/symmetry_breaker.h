/*********************                                                        */
/*! \file symmetry_breaker.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Paul Meng, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Symmetry breaker for theories
 **/

#ifndef __CVC4__PREPROCESSING_PASSES_SYMMETRY_BREAKER_H_
#define __CVC4__PREPROCESSING_PASSES_SYMMETRY_BREAKER_H_

#include <map>
#include <string>
#include <vector>
#include "expr/node.h"

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
 * 1. Triplet constraints
 *    v_i = v_j => v_i = v_{j-1} for all 0 <= i < j-1 < j < n
 * 2. Segment constraints
 *    v_i = v_j => (v_0 = v_1 OR \ldots OR v_{i-1} = v_{i}) for all 1 <= i < j < n
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
   * The symmetry breaking constraints SB returned by this function conjuncted
   * with the original assertions SB ^ C is equisatisfiable to the C.
   * */
  Node generateSymBkConstraints(std::vector<std::vector<Node> >& parts);

 private:

  /** True and false constant nodes */
  Node d_trueNode;
  Node d_falseNode;

  /**
   * Get the order kind depending on the type of node.
   * For example, if node is a integer or real, we would return
   * the operator less than or equal to (<=) and use it to build
   * ordered constraints.
   * */
  Kind getOrderKind(Node node);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4_PREPROCESSING_PASSES_SYMMETRY_BREAKER_H_ */
