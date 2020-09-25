/*********************                                                        */
/*! \file variable_bounds.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Extract bounds on variable from theory atoms.
 **/

#ifndef CVC4__THEORY__ARITH__ICP__VARIABLE_BOUNDS_H
#define CVC4__THEORY__ARITH__ICP__VARIABLE_BOUNDS_H

#include "util/real_algebraic_number.h"

#ifdef CVC4_POLY_IMP
#include <poly/polyxx.h>

#include <map>
#include <vector>

#include "expr/node.h"
#include "theory/arith/nl/icp/interval.h"
#include "theory/arith/nl/poly_conversion.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace icp {

/**
 * A utility class that extracts direct bounds on single variables from theory
 * atoms.
 */
class VariableBounds
{
  /** A reference to a mapper from cvc nodes to poly variables. */
  VariableMapper& d_mapper;
  /** The currently strictest bounds for every variable. */
  std::map<Node, Interval> d_intervals;

  /** Updates the lower bound for the given variable */
  void update_lower_bound(const Node& origin,
                          const Node& variable,
                          const poly::Value& value,
                          bool strict);
  /** Updates the upper bound for the given variable */
  void update_upper_bound(const Node& origin,
                          const Node& variable,
                          const poly::Value& value,
                          bool strict);

 public:
  VariableBounds(VariableMapper& mapper) : d_mapper(mapper) {}
  const VariableMapper& getMapper() const { return d_mapper; }
  /** Reset the bounds */
  void reset();

  /**
   * Get the current interval for v. Creates a new (full) interval if
   * necessary.
   */
  Interval& get(const Node& v);
  /**
   * Get the current interval for v. Returns a full interval if no interval was
   * derived yet.
   */
  Interval get(const Node& v) const;

  /** Return the current variable bounds as an interval assignment. */
  poly::IntervalAssignment get() const;

  /**
   * Add a new theory atom. Return true if the theory atom induces a new
   * variable bound.
   */
  bool add(const Node& n);
};

/** Print the current variable bounds. */
std::ostream& operator<<(std::ostream& os, const VariableBounds& vb);

}  // namespace icp
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif

#endif