/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Aina Niemetz
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

#ifndef CVC5__THEORY__ARITH__NL__TRANSCENDENTAL__EXPONENTIAL_SOLVER_H
#define CVC5__THEORY__ARITH__NL__TRANSCENDENTAL__EXPONENTIAL_SOLVER_H

#include <cstdint>
#include <map>

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

class TranscendentalState;

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
class ExponentialSolver : protected EnvObj
{
 public:
  ExponentialSolver(Env& env, TranscendentalState* tstate);
  ~ExponentialSolver();

  /**
   * Ensures that new_a is properly registered as a term where new_a is the
   * purified version of a, new_a[0] being the new skolem used for purification.
   */
  void doPurification(TNode a, TNode new_a);

  /**
   * check initial refine
   *
   * Constructs a set of valid theory lemmas, based on
   * simple facts about the exponential function.
   * This mostly follows the initial axioms described in
   * Section 4 of "Satisfiability
   * Modulo Transcendental Functions via Incremental
   * Linearization" by Cimatti et al., CADE 2017.
   *
   * Examples:
   *
   * exp( x )>0
   * x<0 => exp( x )<1
   */
  void checkInitialRefine();

  /**
   * check monotonicity
   *
   * Constructs a set of valid theory lemmas, based on a
   * lemma scheme that ensures that applications
   * of the exponential function respect monotonicity.
   *
   * Examples:
   *
   * x > y => exp( x ) > exp( y )
   */
  void checkMonotonic();

  /** Send tangent lemma around c for e */
  void doTangentLemma(TNode e, TNode c, TNode poly_approx, std::uint64_t d);

  /** Send secant lemmas around c for e */
  void doSecantLemmas(TNode e,
                      TNode poly_approx,
                      TNode center,
                      TNode cval,
                      unsigned d,
                      unsigned actual_d);

 private:
  /** Generate bounds for secant lemmas */
  std::pair<Node, Node> getSecantBounds(TNode e, TNode center, unsigned d);

  /** Holds common state for transcendental solvers */
  TranscendentalState* d_data;

  /** The transcendental functions we have done initial refinements on */
  std::map<Node, bool> d_tf_initial_refine;

}; /* class ExponentialSolver */

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__TRANSCENDENTAL_SOLVER_H */
