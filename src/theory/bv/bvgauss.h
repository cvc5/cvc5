/*********************                                                        */
/*! \file bvgauss.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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

#ifndef __CVC4__THEORY__BV__BV_GAUSS_ELIM_H
#define __CVC4__THEORY__BV__BV_GAUSS_ELIM_H

#include "expr/node.h"
#include "util/bitvector.h"

#include <unordered_map>
#include <vector>

namespace CVC4 {
namespace theory {
namespace bv {

class BVGaussElim
{
 public:
  /**
   * Apply Gaussian Elimination on (possibly multiple) set(s) of equations
   * modulo some (prime) number given as bit-vector equations.
   *
   * Note that these sets of equations do not have to be modulo some prime
   * but can be modulo any arbitrary number. However, GE is guaranteed to
   * succeed modulo a prime number, which is not necessarily the case if a
   * given set of equations is modulo a non-prime number.
   */
  static void gaussElimRewrite(std::vector<Node>& assertionsToPreprocess);

 private:
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

  /**
   * Determines if an overflow may occur in given 'expr'.
   *
   * Returns 0 if an overflow may occur, and the minimum required
   * bit-width such that no overflow occurs, otherwise.
   *
   * Note that it would suffice for this function to be Boolean.
   * However, it is handy to determine the minimum required bit-width for
   * debugging purposes.
   */
  static unsigned getMinBwExpr(Node expr);

  /**
   * Apply Gaussian Elimination on a set of equations modulo some (prime)
   * number given as bit-vector equations.
   *
   * IMPORTANT: Applying GE modulo some number (rather than modulo 2^bw)
   * on a set of bit-vector equations is only sound if this set of equations
   * has a solution that does not produce overflows. Consequently, we only
   * apply GE if the given bit-width guarantees that no overflows can occur
   * in the given set of equations.
   *
   * Note that the given set of equations does not have to be modulo a prime
   * but can be modulo any arbitrary number. However, if it is indeed modulo
   * prime, GE is guaranteed to succeed, which is not the case, otherwise.
   *
   * Returns INVALID if GE can not be applied, UNIQUE and PARTIAL if GE was
   * successful, and NONE, otherwise.
   *
   * The resulting constraints are stored in 'res' as a mapping of unknown
   * to result (modulo prime). These mapped results are added as constraints
   * of the form 'unknown = mapped result' in gaussElimRewrite.
   */
  static Result gaussElimRewriteForUrem(
      const std::vector<Node>& equations,
      std::unordered_map<Node, Node, NodeHashFunction>& res);

  /**
   * Apply Gaussian Elimination modulo a (prime) number.
   * The given equation system is represented as a matrix of Integers.
   *
   * Note that given 'prime' does not have to be prime but can be any
   * arbitrary number. However, if 'prime' is indeed prime, GE is guaranteed
   * to succeed, which is not the case, otherwise.
   *
   * Returns INVALID if GE can not be applied, UNIQUE and PARTIAL if GE was
   * successful, and NONE, otherwise.
   *
   * Vectors 'rhs' and 'lhs' represent the right hand side and left hand side
   * of the given matrix, respectively. The resulting matrix (in row echelon
   * form) is stored in 'rhs' and 'lhs', i.e., the given matrix is overwritten
   * with the resulting matrix.
   */
  static Result gaussElim(Integer prime,
                          std::vector<Integer>& rhs,
                          std::vector<std::vector<Integer>>& lhs);
};

}  // namespace bv
}  // namespace theory
}  // namespace CVC4

#endif
