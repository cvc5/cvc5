/*********************                                                        */
/*! \file interval.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **/

#ifndef CVC4__THEORY__ARITH__ICP__INTERVAL_H
#define CVC4__THEORY__ARITH__ICP__INTERVAL_H

#include "util/real_algebraic_number.h"

#ifdef CVC4_POLY_IMP
#include <poly/polyxx.h>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace icp {

/**
 * Represents an interval with poly::Value bounds and origins for these bounds.
 */
struct Interval
{
  /** The lower bound */
  poly::Value lower = poly::Value::minus_infty();
  /** Whether the lower bound is strict or weak */
  bool lower_strict = true;
  /** The origin of the lower bound */
  Node lower_origin;
  /** The upper bound */
  poly::Value upper = poly::Value::plus_infty();
  /** Whether the upper bound is strict or weak */
  bool upper_strict = true;
  /** The origin of the upper bound */
  Node upper_origin;
};

/** Print an interval */
inline std::ostream& operator<<(std::ostream& os, const Interval& i)
{
  return os << (i.lower_strict ? '(' : '[') << i.lower << " .. " << i.upper
            << (i.upper_strict ? ')' : ']');
}

}  // namespace icp
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif

#endif
