/*********************                                                        */
/*! \file taylor_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Generate taylor approximations transcendental lemmas.
 **/

#ifndef CVC4__THEORY__ARITH__NL__TRANSCENDENTAL__TAYLOR_GENERATOR_H
#define CVC4__THEORY__ARITH__NL__TRANSCENDENTAL__TAYLOR_GENERATOR_H

#include "expr/node.h"
#include "theory/arith/nl/nl_model.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

class TaylorGenerator
{
 public:
  TaylorGenerator();

  /**
   * Return the variable used as x in getTaylor().
   */
  TNode getTaylorVariable();

  /**
   * Get Taylor series of degree n for function fa centered around point fa[0].
   *
   * Return value is ( P_{n,f(a)}( x ), R_{n+1,f(a)}( x ) ) where
   * the first part of the pair is the Taylor series expansion :
   *    P_{n,f(a)}( x ) = sum_{i=0}^n (f^i( a )/i!)*(x-a)^i
   * and the second part of the pair is the Taylor series remainder :
   *    R_{n+1,f(a),b}( x ) = (f^{n+1}( b )/(n+1)!)*(x-a)^{n+1}
   *
   * The above values are cached for each (f,n) for a fixed variable "a".
   * To compute the Taylor series for fa, we compute the Taylor series
   *   for ( fa.getKind(), n ) then substitute { a -> fa[0] } if fa[0]!=0.
   * We compute P_{n,f(0)}( x )/R_{n+1,f(0),b}( x ) for ( fa.getKind(), n )
   *   if fa[0]=0.
   * In the latter case, note we compute the exponential x^{n+1}
   * instead of (x-a)^{n+1}, which can be done faster.
   */
  std::pair<Node, Node> getTaylor(TNode fa, std::uint64_t n);

  /**
   * polynomial approximation bounds
   *
   * This adds P_l+[x], P_l-[x], P_u+[x], P_u-[x] to pbounds, where x is
   * d_taylor_real_fv. These are polynomial approximations of the Taylor series
   * of <k>( 0 ) for degree 2*d where k is SINE or EXPONENTIAL.
   * These correspond to P_l and P_u from Figure 3 of Cimatti et al., CADE 2017,
   * for positive/negative (+/-) values of the argument of <k>( 0 ).
   *
   * Notice that for certain bounds (e.g. upper bounds for exponential), the
   * Taylor approximation for a fixed degree is only sound up to a given
   * upper bound on the argument. To obtain sound lower/upper bounds for a
   * given <k>( c ), use the function below.
   */
  void getPolynomialApproximationBounds(Kind k,
                                        unsigned d,
                                        std::vector<Node>& pbounds);

  /**
   * polynomial approximation bounds
   *
   * This computes polynomial approximations P_l+[x], P_l-[x], P_u+[x], P_u-[x]
   * that are sound (lower, upper) bounds for <k>( c ). Notice that these
   * polynomials may depend on c. In particular, for P_u+[x] for <k>( c ) where
   * c>0, we return the P_u+[x] from the function above for the minimum degree
   * d' >= d such that (1-c^{2*d'+1}/(2*d'+1)!) is positive.
   * @return the actual degree of the polynomial approximations (which may be
   * larger than d).
   */
  unsigned getPolynomialApproximationBoundForArg(Kind k,
                                                 Node c,
                                                 unsigned d,
                                                 std::vector<Node>& pbounds);

  /** get transcendental function model bounds
   *
   * This returns the current lower and upper bounds of transcendental
   * function application tf based on Taylor of degree 2*d, which is dependent
   * on the model value of its argument.
   */
  std::pair<Node, Node> getTfModelBounds(Node tf, unsigned d, NlModel& model);

 private:
  NodeManager* d_nm;
  const Node d_taylor_real_fv;
  const Node d_taylor_real_fv_base;
  const Node d_taylor_real_fv_base_rem;
  std::unordered_map<Node,
                     std::unordered_map<std::uint64_t, Node>,
                     NodeHashFunction>
      s_taylor_sum;
  std::unordered_map<Node,
                     std::unordered_map<std::uint64_t, Node>,
                     NodeHashFunction>
      d_taylor_rem;
  std::map<Kind, std::map<unsigned, std::vector<Node>>> d_poly_bounds;
};

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__TRANSCENDENTAL_SOLVER_H */
