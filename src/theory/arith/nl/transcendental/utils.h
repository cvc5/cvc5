/*********************                                                        */
/*! \file utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for transcendental lemmas.
 **/

#ifndef CVC4__THEORY__ARITH__NL__TRANSCENDENTAL__UTILS_H
#define CVC4__THEORY__ARITH__NL__TRANSCENDENTAL__UTILS_H

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

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

}
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__TRANSCENDENTAL_SOLVER_H */
