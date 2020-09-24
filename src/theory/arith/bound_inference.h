/*********************                                                        */
/*! \file bound_inference.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Extract bounds on variables from theory atoms.
 **/

#ifndef CVC4__THEORY__ARITH__BOUND_INFERENCE_H
#define CVC4__THEORY__ARITH__BOUND_INFERENCE_H

#include <map>
#include <utility>
#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace arith {

  struct Bounds
  {
    /** The lower bound */
    Node lower;
    /** Whether the lower bound is strict or weak */
    bool lower_strict = true;
    /** The origin of the lower bound */
    Node lower_origin;
    /** The upper bound */
    Node upper;
    /** Whether the upper bound is strict or weak */
    bool upper_strict = true;
    /** The origin of the upper bound */
    Node upper_origin;
  };

/** Print the current variable bounds. */
std::ostream& operator<<(std::ostream& os, const Bounds& b);

/**
 * A utility class that extracts direct bounds on single variables from theory
 * atoms.
 */
class BoundInference
{
  /** The currently strictest bounds for every variable. */
  std::map<Node, Bounds> d_bounds;

  /** Updates the lower bound for the given variable */
  void update_lower_bound(const Node& origin,
                          const Node& variable,
                          const Node& value,
                          bool strict);
  /** Updates the upper bound for the given variable */
  void update_upper_bound(const Node& origin,
                          const Node& variable,
                          const Node& value,
                          bool strict);

 public:
  void reset();

  /**
   * Get the current interval for v. Creates a new (full) interval if
   * necessary.
   */
  Bounds& get_or_add(const Node& v);
  /**
   * Get the current interval for v. Returns a full interval if no interval was
   * derived yet.
   */
  Bounds get(const Node& v) const;

  /** Return the current variable bounds as an interval assignment. */
  const std::map<Node, Bounds>& get() const;

  /**
   * Add a new theory atom. Return true if the theory atom induces a new
   * variable bound.
   */
  bool add(const Node& n);
};

/** Print the current variable bounds. */
std::ostream& operator<<(std::ostream& os, const BoundInference& bi);

std::map<Node, std::pair<Node,Node>> getBounds(const std::vector<Node>& assertions);

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif