/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Extract bounds on variables from theory atoms.
 */

#ifndef CVC5__THEORY__ARITH__BOUND_INFERENCE_H
#define CVC5__THEORY__ARITH__BOUND_INFERENCE_H

#include <map>
#include <utility>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

  struct Bounds
  {
    /** The lower bound value */
    Node lower_value;
    /** Whether the lower bound is strict or weak */
    bool lower_strict = true;
    /** The lower bound as constraint */
    Node lower_bound;
    /** The origin of the lower bound */
    Node lower_origin;
    /** The upper bound value */
    Node upper_value;
    /** Whether the upper bound is strict or weak */
    bool upper_strict = true;
    /** The upper bound as constraint */
    Node upper_bound;
    /** The origin of the upper bound */
    Node upper_origin;
  };

  /** Print the current bounds. */
  std::ostream& operator<<(std::ostream& os, const Bounds& b);

  /**
   * A utility class that extracts direct bounds on arithmetic terms from theory
   * atoms.
   */
  class BoundInference : protected EnvObj
  {
   public:
    BoundInference(Env& env);
    void reset();

    /**
     * Get the current interval for lhs. Creates a new (full) interval if
     * necessary.
     */
    Bounds& get_or_add(const Node& lhs);
    /**
     * Get the current interval for lhs. Returns a full interval if no interval
     * was derived yet.
     */
    Bounds get(const Node& lhs) const;

    /** Return the current term bounds as an interval assignment. */
    const std::map<Node, Bounds>& get() const;

    /**
     * Add a new theory atom. Return true if the theory atom induces a new
     * term bound.
     * If onlyVariables is true, the left hand side needs to be a single
     * variable to induce a bound.
     */
    bool add(const Node& n, bool onlyVariables = true);

    /**
     * Post-processes a set of nodes and replaces bounds by their origins.
     * This utility sometimes creates new bounds, either due to tightening of
     * integer terms or because an equality was derived from two weak
     * inequalities. While the origins of these new bounds are recorded in
     * lower_origin and upper_origin, this method can be used to conveniently
     * replace these new nodes by their origins.
     * This can be used, for example, when constructing conflicts.
     */
    void replaceByOrigins(std::vector<Node>& nodes) const;

   private:
    /** The currently strictest bounds for every lhs. */
    std::map<Node, Bounds> d_bounds;

    /** Updates the lower bound for the given lhs */
    void update_lower_bound(const Node& origin,
                            const Node& lhs,
                            const Node& value,
                            bool strict);
    /** Updates the upper bound for the given lhs */
    void update_upper_bound(const Node& origin,
                            const Node& lhs,
                            const Node& value,
                            bool strict);
  };

/** Print the current variable bounds. */
std::ostream& operator<<(std::ostream& os, const BoundInference& bi);

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
