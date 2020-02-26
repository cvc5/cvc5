/*********************                                                        */
/*! \file nl_lemma_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for processing lemmas from the non-linear solver
 **/

#ifndef CVC4__THEORY__ARITH__NL_LEMMA_UTILS_H
#define CVC4__THEORY__ARITH__NL_LEMMA_UTILS_H

#include <tuple>
#include <vector>
#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * A side effect of adding a lemma in the non-linear solver. This is used
 * to specify how the state of the non-linear solver should update. This
 * includes:
 * - A set of secant points to record (for transcendental secant plane
 * inferences).
 */
struct NlLemmaSideEffect
{
  NlLemmaSideEffect() {}
  ~NlLemmaSideEffect() {}
  /** secant points to add
   *
   * A member (tf, d, c) in this vector indicates that point c should be added
   * to the list of secant points for an application of a transcendental
   * function tf for Taylor degree d. This is used for incremental linearization
   * for underapproximation (resp. overapproximations) of convex (resp.
   * concave) regions of transcendental functions. For details, see
   * Cimatti et al., CADE 2017.
   */
  std::vector<std::tuple<Node, unsigned, Node> > d_secantPoint;
};

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__NL_LEMMA_UTILS_H */
