/*********************                                                        */
/*! \file factoring_check.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Check for factoring lemma
 **/

#ifndef CVC4__THEORY__ARITH__NL__EXT__FACTORING_CHECK_H
#define CVC4__THEORY__ARITH__NL__EXT__FACTORING_CHECK_H

#include <vector>

#include "expr/node.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

class FactoringCheck
{
 public:
  FactoringCheck(InferenceManager& im, NlModel& model);

  /** check factoring
   *
   * Returns a set of valid theory lemmas, based on a
   * lemma schema that states a relationship betwen monomials
   * with common factors that occur in the same constraint.
   *
   * Examples:
   *
   * x*z+y*z > t => ( k = x + y ^ k*z > t )
   *   ...where k is fresh and x*z + y*z > t is a
   *      constraint that occurs in the current context.
   */
  void check(const std::vector<Node>& asserts,
             const std::vector<Node>& false_asserts);

 private:
  /** The inference manager that we push conflicts and lemmas to. */
  InferenceManager& d_im;
  /** Reference to the non-linear model object */
  NlModel& d_model;
  /** maps nodes to their factor skolems */
  std::map<Node, Node> d_factor_skolem;

  Node d_zero;
  Node d_one;

  Node getFactorSkolem(Node n);
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
