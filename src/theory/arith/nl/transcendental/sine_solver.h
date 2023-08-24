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
 * Solving for handling exponential function.
 */

#ifndef CVC5__THEORY__ARITH__NL__TRANSCENDENTAL__SINE_SOLVER_H
#define CVC5__THEORY__ARITH__NL__TRANSCENDENTAL__SINE_SOLVER_H

#include <map>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/arith/nl/transcendental/transcendental_state.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

/** Transcendental solver class
 *
 * This class implements model-based refinement schemes
 * for transcendental functions, described in:
 *
 * - "Satisfiability Modulo Transcendental
 * Functions via Incremental Linearization" by Cimatti
 * et al., CADE 2017.
 *
 * It's main functionality are methods that implement lemma schemas below,
 * which return a set of lemmas that should be sent on the output channel.
 */
class SineSolver : protected EnvObj
{
 public:
  SineSolver(Env& env, TranscendentalState* tstate);
  ~SineSolver();

  /** do reductions
   *
   * This method determines any applications of sin(x) that can be reasoned
   * about "precisely", either via symmetry:
   *   x = -y => sin(x) = -sin(y)
   * or via boundary points, e.g.:
   *   x = pi/2 => sin(x) = 1
   * Each application of sin(x) for which a reduction of the latter form exists
   * is removed from the range of d_funcMap in the transcendental state, and
   * thus will not be considered for other lemma schemas.
   */
  void doReductions();
  /**
   * Introduces new_a as purified version of a which is also shifted to the main
   * phase (from -pi to pi). new_a[0] is the new skolem used for purification.
   */
  void doPhaseShift(TNode a, TNode new_a);

  /**
   * check initial refine
   *
   * Constructs a set of valid theory lemmas, based on
   * simple facts about the sine function.
   * This mostly follows the initial axioms described in
   * Section 4 of "Satisfiability
   * Modulo Transcendental Functions via Incremental
   * Linearization" by Cimatti et al., CADE 2017.
   *
   * Examples:
   *
   * sin( x ) = -sin( -x )
   * ( PI > x > 0 ) => 0 < sin( x ) < 1
   */
  void checkInitialRefine();

  /**
   * check monotonicity
   *
   * Constructs a set of valid theory lemmas, based on a
   * lemma scheme that ensures that applications
   * of the sine function respect monotonicity.
   *
   * Examples:
   *
   * PI/2 > x > y > 0 => sin( x ) > sin( y )
   * PI > x > y > PI/2 => sin( x ) < sin( y )
   */
  void checkMonotonic();

  /** Sent tangent lemma around c for e */
  void doTangentLemma(
      TNode e, TNode c, TNode poly_approx, int region, std::uint64_t d);

  /** Sent secant lemmas around c for e */
  void doSecantLemmas(TNode e,
                      TNode poly_approx,
                      TNode c,
                      TNode poly_approx_c,
                      unsigned d,
                      unsigned actual_d,
                      int region);

  /**
   * Does n of the form sin(x) have an exact model value? This is true if
   * the model value of x is in the domain of d_mpointsSine.
   */
  bool hasExactModelValue(TNode n) const;

  /**
   * Make the lemma for the phase shift of arguments to SINE x and y, where
   * s is the (integral) shift. The lemma conceptually says that y is
   * in the bounds [-pi, pi] and y is offset from x by an integral factor of
   * 2*pi.
   */
  static Node getPhaseShiftLemma(const Node& x, const Node& y, const Node& s);

 private:
  std::pair<Node, Node> getSecantBounds(TNode e,
                                        TNode c,
                                        unsigned d,
                                        int region);

  /** region to lower bound
   *
   * Returns the term corresponding to the lower
   * bound of the region of transcendental function
   * with kind k. Returns Node::null if the region
   * is invalid, or there is no lower bound for the
   * region.
   */
  Node regionToLowerBound(int region) const
  {
    if (region >= 1 && region <= 4)
    {
      size_t index = static_cast<size_t>(region);
      return d_mpoints[index];
    }
    return Node();
  }

  /** region to upper bound
   *
   * Returns the term corresponding to the upper
   * bound of the region of transcendental function
   * with kind k. Returns Node::null if the region
   * is invalid, or there is no upper bound for the
   * region.
   */
  Node regionToUpperBound(int region) const
  {
    if (region >= 1 && region <= 4)
    {
      size_t index = static_cast<size_t>(region - 1);
      return d_mpoints[index];
    }
    return Node();
  }

  int regionToMonotonicityDir(int region) const
  {
    switch (region)
    {
      case 1:
      case 4: return -1;
      case 2:
      case 3: return 1;
      default: return 0;
    }
  }
  Convexity regionToConvexity(int region) const
  {
    switch (region)
    {
      case 1:
      case 2: return Convexity::CONCAVE;
      case 3:
      case 4: return Convexity::CONVEX;
      default: return Convexity::UNKNOWN;
    }
  }

  /** Holds common state for transcendental solvers */
  TranscendentalState* d_data;

  /** The transcendental functions we have done initial refinements on */
  std::map<Node, bool> d_tf_initial_refine;

  /** PI, -PI */
  Node d_pi;
  Node d_neg_pi;
  /** the boundary points */
  std::vector<Node> d_mpoints;
  /** mapping from values c to known points for sin(c) */
  std::map<Node, Node> d_mpointsSine;
}; /* class SineSolver */

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__TRANSCENDENTAL_SOLVER_H */
