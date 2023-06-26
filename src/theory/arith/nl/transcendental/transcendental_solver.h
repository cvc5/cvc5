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
 * Solving for handling transcendental functions.
 */

#ifndef CVC5__THEORY__ARITH__NL__TRANSCENDENTAL__TRANSCENDENTAL_SOLVER_H
#define CVC5__THEORY__ARITH__NL__TRANSCENDENTAL__TRANSCENDENTAL_SOLVER_H

#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/arith/nl/transcendental/exponential_solver.h"
#include "theory/arith/nl/transcendental/sine_solver.h"
#include "theory/arith/nl/transcendental/transcendental_state.h"
#include "theory/theory_state.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

class InferenceManager;

namespace nl {

class NlModel;

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
class TranscendentalSolver : protected EnvObj
{
 public:
  TranscendentalSolver(Env& env,
                       TheoryState& state,
                       InferenceManager& im,
                       NlModel& m);
  ~TranscendentalSolver();

  /** init last call
   *
   * This is called at the beginning of last call effort check, where
   * assertions are the set of assertions belonging to arithmetic,
   * false_asserts is the subset of assertions that are false in the current
   * model, and xts is the set of extended function terms that are active in
   * the current context.
   *
   * This call may add lemmas to lems based on registering term
   * information (for example, purification of sine terms).
   */
  void initLastCall(const std::vector<Node>& xts);
  /** increment taylor degree */
  void incrementTaylorDegree();
  /** get taylor degree */
  unsigned getTaylorDegree() const;
  /** preprocess assertions check model
   *
   * This modifies the given assertions in preparation for running a call
   * to check model.
   *
   * This method returns false if a bound for a transcendental function
   * was conflicting.
   */
  bool preprocessAssertionsCheckModel(std::vector<Node>& assertions);
  /** Process side effects in lemma se */
  void processSideEffect(const NlLemma& se);
  //-------------------------------------------- lemma schemas
  // Relays to exp and sine solvers.
  void checkTranscendentalInitialRefine();

  // Relays to exp and sine solvers.
  void checkTranscendentalMonotonic();

  /** check transcendental tangent planes
   *
   * Constructs a set of valid theory lemmas, based on
   * computing an "incremental linearization" of
   * transcendental functions based on the model values
   * of transcendental functions and their arguments.
   * It is based on Figure 3 of "Satisfiability
   * Modulo Transcendental Functions via Incremental
   * Linearization" by Cimatti et al., CADE 2017.
   * This schema is not terminating in general.
   * It is not enabled by default, and can
   * be enabled by --nl-ext-tf-tplanes.
   *
   * Example:
   *
   * Assume we have a term sin(y) where M( y ) = 1 where M is the current model.
   * Note that:
   *   sin(1) ~= .841471
   *
   * The Taylor series and remainder of sin(y) of degree 7 is
   *   P_{7,sin(0)}( x ) = x + (-1/6)*x^3 + (1/20)*x^5
   *   R_{7,sin(0),b}( x ) = (-1/5040)*x^7
   *
   * This gives us lower and upper bounds :
   *   P_u( x ) = P_{7,sin(0)}( x ) + R_{7,sin(0),b}( x )
   *     ...where note P_u( 1 ) = 4243/5040 ~= .841865
   *   P_l( x ) = P_{7,sin(0)}( x ) - R_{7,sin(0),b}( x )
   *     ...where note P_l( 1 ) = 4241/5040 ~= .841468
   *
   * Assume that M( sin(y) ) > P_u( 1 ).
   * Since the concavity of sine in the region 0 < x < PI/2 is -1,
   * we add a tangent plane refinement.
   * The tangent plane at the point 1 in P_u is
   * given by the formula:
   *   T( x ) = P_u( 1 ) + ((d/dx)(P_u(x)))( 1 )*( x - 1 )
   * We add the lemma:
   *   ( 0 < y < PI/2 ) => sin( y ) <= T( y )
   * which is:
   *   ( 0 < y < PI/2 ) => sin( y ) <= (391/720)*(y - 2737/1506)
   *
   * Assume that M( sin(y) ) < P_u( 1 ).
   * Since the concavity of sine in the region 0 < x < PI/2 is -1,
   * we add a secant plane refinement for some constants ( l, u )
   * such that 0 <= l < M( y ) < u <= PI/2. Assume we choose
   * l = 0 and u = M( PI/2 ) = 150517/47912.
   * The secant planes at point 1 for P_l
   * are given by the formulas:
   *   S_l( x ) = (x-l)*(P_l( l )-P_l(c))/(l-1) + P_l( l )
   *   S_u( x ) = (x-u)*(P_l( u )-P_l(c))/(u-1) + P_l( u )
   * We add the lemmas:
   *   ( 0 < y < 1 ) => sin( y ) >= S_l( y )
   *   ( 1 < y < PI/2 ) => sin( y ) >= S_u( y )
   * which are:
   *   ( 0 < y < 1 ) => (sin y) >= 4251/5040*y
   *   ( 1 < y < PI/2 ) => (sin y) >= c1*(y+c2)
   *     where c1, c2 are rationals (for brevity, omitted here)
   *     such that c1 ~= .277 and c2 ~= 2.032.
   */
  void checkTranscendentalTangentPlanes();

  /**
   * Post-process model. This ensures that for all terms t in the domain of
   * arithModel, if t is in the same equivalence class as a transcendental
   * function application, then arithModel[t] maps to one such application.
   *
   * This is to ensure that the linear model is ignored for such terms,
   * as their values cannot be properly represented in the model.
   *
   * It is important to map such terms t to a transcendental function
   * application, or otherwise they would be unconstrained, leading to
   * spurious models.
   */
  void postProcessModel(std::map<Node, Node>& arithModel,
                        const std::set<Node>& termSet);

 private:
  /** check transcendental function refinement for tf
   *
   * This method is called by the above method for each "master"
   * transcendental function application that occurs in an assertion in the
   * current context. For example, an application like sin(t) is not a master
   * if we have introduced the constraints:
   *   t=y+2*pi*n ^ -pi <= y <= pi ^ sin(t) = sin(y).
   * See d_trMaster/d_trSlaves for more detail.
   *
   * This runs Figure 3 of Cimatti et al., CADE 2017 for transcendental
   * function application tf for Taylor degree d. It may add a secant or
   * tangent plane lemma to lems, which includes the side effect of the lemma
   * (if one exists).
   *
   * It returns false if the bounds are not precise enough to add a
   * secant or tangent plane lemma.
   */
  bool checkTfTangentPlanesFun(Node tf, unsigned d);
  //-------------------------------------------- end lemma schemas

  /** get concavity
   *
   * Returns whether we are concave (+1) or convex (-1)
   * in region of transcendental function with kind k,
   * where region is defined above.
   * Returns 0 if region is invalid.
   */
  int regionToConcavity(Kind k, int region);

  /** A reference to the arithmetic state object */
  TheoryState& d_astate;
  /** taylor degree
   *
   * Indicates that the degree of the polynomials in the Taylor approximation of
   * all transcendental functions is 2*d_taylor_degree. This value is set
   * initially to the nlExtTfTaylorDegree option and may be incremented
   * if the option nlExtTfIncPrecision is enabled.
   */
  uint64_t d_taylor_degree;

  /** Common state for transcendental solver */
  transcendental::TranscendentalState d_tstate;
  /** The solver responsible for the exponential function */
  transcendental::ExponentialSolver d_expSlv;
  /** The solver responsible for the sine function */
  transcendental::SineSolver d_sineSlv;
}; /* class TranscendentalSolver */

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__TRANSCENDENTAL_SOLVER_H */
