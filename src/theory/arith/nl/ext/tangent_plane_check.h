/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Check for tangent_plane lemma.
 */

#ifndef CVC5__THEORY__ARITH__NL__EXT__TANGENT_PLANE_CHECK_H
#define CVC5__THEORY__ARITH__NL__EXT__TANGENT_PLANE_CHECK_H

#include <map>

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

class ExtState;

class TangentPlaneCheck : protected EnvObj
{
 public:
  TangentPlaneCheck(Env& env, ExtState* data);

  /** check tangent planes
   *
   * Returns a set of valid theory lemmas, based on an
   * "incremental linearization" of non-linear monomials.
   * This linearization is accomplished by adding constraints
   * corresponding to "tangent planes" at the current
   * model value of each non-linear monomial. In particular
   * consider the definition for constants a,b :
   *   T_{a,b}( x*y ) = b*x + a*y - a*b.
   * The lemmas added by this function are of the form :
   *  ( ( x>a ^ y<b) ^ (x<a ^ y>b) ) => x*y < T_{a,b}( x*y )
   *  ( ( x>a ^ y>b) ^ (x<a ^ y<b) ) => x*y > T_{a,b}( x*y )
   * It is inspired by "Invariant Checking of NRA Transition
   * Systems via Incremental Reduction to LRA with EUF" by
   * Cimatti et al., TACAS 2017.
   * This schema is not terminating in general.
   * It is not enabled by default, and can
   * be enabled by --nl-ext-tplanes.
   *
   * Examples:
   *
   * ( ( x>2 ^ y>5) ^ (x<2 ^ y<5) ) => x*y > 5*x + 2*y - 10
   * ( ( x>2 ^ y<5) ^ (x<2 ^ y>5) ) => x*y < 5*x + 2*y - 10
   */
  void check(bool asWaitingLemmas);

 private:
  /** Basic data that is shared with other checks */
  ExtState* d_data;
  /** tangent plane bounds */
  std::map<Node, std::map<Node, Node> > d_tangent_val_bound[4];
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
