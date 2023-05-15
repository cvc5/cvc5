/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Check for factoring lemma.
 */

#ifndef CVC5__THEORY__ARITH__NL__EXT__FACTORING_CHECK_H
#define CVC5__THEORY__ARITH__NL__EXT__FACTORING_CHECK_H

#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class CDProof;

namespace theory {
namespace arith {
namespace nl {

class ExtState;

class FactoringCheck : protected EnvObj
{
 public:
  FactoringCheck(Env& env, ExtState* data);

  /** check factoring
   *
   * Returns a set of valid theory lemmas, based on a
   * lemma schema that states a relationship between monomials
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
  /** Basic data that is shared with other checks */
  ExtState* d_data;

  /** maps nodes to their factor skolems */
  std::map<Node, Node> d_factor_skolem;

  Node d_zero;
  Node d_one;

  /**
   * Introduces a new purification skolem k for n and adds k=n as lemma.
   * If proof is not nullptr, it proves this lemma via MACRO_SR_PRED_INTRO.
   */
  Node getFactorSkolem(Node n, CDProof* proof);
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
