/*********************                                                        */
/*! \file bv_gauss.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Mathias Preiner, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Gaussian Elimination preprocessing pass.
 **
 ** Simplify a given equation system modulo a (prime) number via Gaussian
 ** Elimination if possible.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PASSES__BV_GAUSS_ELIM_H
#define CVC4__PREPROCESSING__PASSES__BV_GAUSS_ELIM_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

class BVGauss : public PreprocessingPass
{
 public:
  BVGauss(PreprocessingPassContext* preprocContext,
          const std::string& name = "bv-gauss");

 protected:
  /**
   * Apply Gaussian Elimination on (possibly multiple) set(s) of equations
   * modulo some (prime) number given as bit-vector equations.
   *
   * Note that these sets of equations do not have to be modulo some prime
   * but can be modulo any arbitrary number. However, GE is guaranteed to
   * succeed modulo a prime number, which is not necessarily the case if a
   * given set of equations is modulo a non-prime number.
   */
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /* Note: The following functionality is only exposed for unit testing in
   * pass_bv_gauss_white.h. */

  /**
   *  Represents the result of Gaussian Elimination where the solution
   *  of the given equation system is
   *
   *   INVALID ... i.e., NOT of the form c1*x1 + c2*x2 + ... % p = b,
   *               where ci, b and p are
   *                 - bit-vector constants
   *                 - extracts or zero extensions on bit-vector constants
   *                 - of arbitrary nesting level
   *               and p is co-prime to all bit-vector constants for which
   *               a multiplicative inverse has to be computed.
   *
   *   UNIQUE  ... determined for all unknowns, e.g., x = 4
   *
   *   PARTIAL ... e.g., x = 4 - 2z
   *
   *   NONE    ... no solution
   *
   *   Given a matrix A representing an equation system, the resulting
   *   matrix B after applying GE represents, e.g.:
   *
   *   B = 1 0 0 2 <-    UNIQUE
   *       0 1 0 3 <-
   *       0 0 1 1 <-
   *
   *   B = 1 0 2 4 <-    PARTIAL
   *       0 1 3 2 <-
   *       0 0 1 1
   *
   *   B = 1 0 0 1       NONE
   *       0 1 1 2
   *       0 0 0 2 <-
   */
  enum class Result
  {
    INVALID,
    UNIQUE,
    PARTIAL,
    NONE
  };

  static Result gaussElim(Integer prime,
                          std::vector<Integer>& rhs,
                          std::vector<std::vector<Integer>>& lhs);

  static Result gaussElimRewriteForUrem(
      const std::vector<Node>& equations,
      std::unordered_map<Node, Node, NodeHashFunction>& res);

  static unsigned getMinBwExpr(Node expr);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif
