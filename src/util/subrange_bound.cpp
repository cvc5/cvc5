/*********************                                                        */
/*! \file subrange_bound.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Representation of subrange bounds
 **
 ** Simple class to represent a subrange bound, either infinite
 ** (no bound) or finite (an arbitrary precision integer).
 **/

#include "util/subrange_bound.h"

#include <limits>

#include "base/cvc4_assert.h"
#include "base/exception.h"
#include "util/integer.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const SubrangeBounds& bounds) {
  out << bounds.lower << ".." << bounds.upper;

  return out;
}

/** Get the finite SubrangeBound, failing an assertion if infinite. */
const Integer& SubrangeBound::getBound() const {
  PrettyCheckArgument(!d_nobound, this, "SubrangeBound is infinite");
  return d_bound;
}

SubrangeBounds::SubrangeBounds(const SubrangeBound& l, const SubrangeBound& u)
    : lower(l), upper(u) {
  PrettyCheckArgument(
      !l.hasBound() || !u.hasBound() || l.getBound() <= u.getBound(), l,
      "Bad subrange bounds specified");
}

bool SubrangeBounds::joinIsBounded(const SubrangeBounds& a,
                                   const SubrangeBounds& b) {
  return (a.lower.hasBound() && b.lower.hasBound()) ||
         (a.upper.hasBound() && b.upper.hasBound());
}

SubrangeBounds SubrangeBounds::join(const SubrangeBounds& a,
                                    const SubrangeBounds& b) {
  DebugCheckArgument(joinIsBounded(a, b), a);
  SubrangeBound newLower = SubrangeBound::min(a.lower, b.lower);
  SubrangeBound newUpper = SubrangeBound::max(a.upper, b.upper);
  return SubrangeBounds(newLower, newUpper);
}

} /* namespace CVC4 */
