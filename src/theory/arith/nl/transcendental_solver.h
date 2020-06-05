/*********************                                                        */
/*! \file transcendental_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Solving for handling transcendental functions.
 **/

#ifndef CVC4__THEORY__ARITH__NL__TRANSCENDENTAL_SOLVER_H
#define CVC4__THEORY__ARITH__NL__TRANSCENDENTAL_SOLVER_H

#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/arith/nl/nl_model.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

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
class TranscendentalSolver
{
 public:
  TranscendentalSolver(NlModel& m);
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
  void initLastCall(const std::vector<Node>& assertions,
                    const std::vector<Node>& false_asserts,
                    const std::vector<Node>& xts,
                    std::vector<NlLemma>& lems);
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
  /** check transcendental initial refine
   *
   * Returns a set of valid theory lemmas, based on
   * simple facts about transcendental functions.
   * This mostly follows the initial axioms described in
   * Section 4 of "Satisfiability
   * Modulo Transcendental Functions via Incremental
   * Linearization" by Cimatti et al., CADE 2017.
   *
   * Examples:
   *
   * sin( x ) = -sin( -x )
   * ( PI > x > 0 ) => 0 < sin( x ) < 1
   * exp( x )>0
   * x<0 => exp( x )<1
   */
  std::vector<NlLemma> checkTranscendentalInitialRefine();

  /** check transcendental monotonic
   *
   * Returns a set of valid theory lemmas, based on a
   * lemma scheme that ensures that applications
   * of transcendental functions respect monotonicity.
   *
   * Examples:
   *
   * x > y => exp( x ) > exp( y )
   * PI/2 > x > y > 0 => sin( x ) > sin( y )
   * PI > x > y > PI/2 => sin( x ) < sin( y )
   */
  std::vector<NlLemma> checkTranscendentalMonotonic();

  /** check transcendental tangent planes
   *
   * Returns a set of valid theory lemmas, based on
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
  std::vector<NlLemma> checkTranscendentalTangentPlanes();
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
  bool checkTfTangentPlanesFun(Node tf, unsigned d, std::vector<NlLemma>& lems);
  //-------------------------------------------- end lemma schemas
 private:
  /** polynomial approximation bounds
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
  /** polynomial approximation bounds
   *
   * This computes polynomial approximations P_l+[x], P_l-[x], P_u+[x], P_u-[x]
   * that are sound (lower, upper) bounds for <k>( c ). Notice that these
   * polynomials may depend on c. In particular, for P_u+[x] for <k>( c ) where
   * c>0, we return the P_u+[x] from the function above for the minimum degree
   * d' >= d such that (1-c^{2*d'+1}/(2*d'+1)!) is positive.
   */
  void getPolynomialApproximationBoundForArg(Kind k,
                                             Node c,
                                             unsigned d,
                                             std::vector<Node>& pbounds);
  /** get transcendental function model bounds
   *
   * This returns the current lower and upper bounds of transcendental
   * function application tf based on Taylor of degree 2*d, which is dependent
   * on the model value of its argument.
   */
  std::pair<Node, Node> getTfModelBounds(Node tf, unsigned d);
  /** get monotonicity direction
   *
   * Returns whether the slope is positive (+1) or negative(-1)
   * in region of transcendental function with kind k.
   * Returns 0 if region is invalid.
   */
  int regionToMonotonicityDir(Kind k, int region);
  /** get concavity
   *
   * Returns whether we are concave (+1) or convex (-1)
   * in region of transcendental function with kind k,
   * where region is defined above.
   * Returns 0 if region is invalid.
   */
  int regionToConcavity(Kind k, int region);
  /** region to lower bound
   *
   * Returns the term corresponding to the lower
   * bound of the region of transcendental function
   * with kind k. Returns Node::null if the region
   * is invalid, or there is no lower bound for the
   * region.
   */
  Node regionToLowerBound(Kind k, int region);
  /** region to upper bound
   *
   * Returns the term corresponding to the upper
   * bound of the region of transcendental function
   * with kind k. Returns Node::null if the region
   * is invalid, or there is no upper bound for the
   * region.
   */
  Node regionToUpperBound(Kind k, int region);
  /** get derivative
   *
   * Returns d/dx n. Supports cases of n
   * for transcendental functions applied to x,
   * multiplication, addition, constants and variables.
   * Returns Node::null() if derivative is an
   * unhandled case.
   */
  Node getDerivative(Node n, Node x);

  void mkPi();
  void getCurrentPiBounds(std::vector<NlLemma>& lemmas);
  /** Make the node -pi <= a <= pi */
  static Node mkValidPhase(Node a, Node pi);

  /** Reference to the non-linear model object */
  NlModel& d_model;
  /** commonly used terms */
  Node d_zero;
  Node d_one;
  Node d_neg_one;
  Node d_true;
  Node d_false;
  /**
   * Some transcendental functions f(t) are "purified", e.g. we add
   * t = y ^ f(t) = f(y) where y is a fresh variable. Those that are not
   * purified we call "master terms".
   *
   * The maps below maintain a master/slave relationship over
   * transcendental functions (SINE, EXPONENTIAL, PI), where above
   * f(y) is the master of itself and of f(t).
   *
   * This is used for ensuring that the argument y of SINE we process is on the
   * interval [-pi .. pi], and that exponentials are not applied to arguments
   * that contain transcendental functions.
   */
  std::map<Node, Node> d_trMaster;
  std::map<Node, std::unordered_set<Node, NodeHashFunction>> d_trSlaves;
  /** The transcendental functions we have done initial refinements on */
  std::map<Node, bool> d_tf_initial_refine;

  /** concavity region for transcendental functions
   *
   * This stores an integer that identifies an interval in
   * which the current model value for an argument of an
   * application of a transcendental function resides.
   *
   * For exp( x ):
   *   region #1 is -infty < x < infty
   * For sin( x ):
   *   region #0 is pi < x < infty (this is an invalid region)
   *   region #1 is pi/2 < x <= pi
   *   region #2 is 0 < x <= pi/2
   *   region #3 is -pi/2 < x <= 0
   *   region #4 is -pi < x <= -pi/2
   *   region #5 is -infty < x <= -pi (this is an invalid region)
   * All regions not listed above, as well as regions 0 and 5
   * for SINE are "invalid". We only process applications
   * of transcendental functions whose arguments have model
   * values that reside in valid regions.
   */
  std::unordered_map<Node, int, NodeHashFunction> d_tf_region;
  /** cache of the above function */
  std::map<Kind, std::map<unsigned, std::vector<Node>>> d_poly_bounds;

  /**
   * Maps representives of a congruence class to the members of that class.
   *
   * In detail, a congruence class is a set of terms of the form
   *   { f(t1), ..., f(tn) }
   * such that t1 = ... = tn in the current context. We choose an arbitrary
   * term among these to be the repesentative of this congruence class.
   *
   * Moreover, notice we compute congruence classes only over terms that
   * are transcendental function applications that are "master terms",
   * see d_trMaster/d_trSlave.
   */
  std::map<Node, std::vector<Node>> d_funcCongClass;
  /**
   * A list of all functions for each kind in { EXPONENTIAL, SINE, POW, PI }
   * that are representives of their congruence class.
   */
  std::map<Kind, std::vector<Node>> d_funcMap;

  // tangent plane bounds
  std::map<Node, std::map<Node, Node>> d_tangent_val_bound[4];

  /** secant points (sorted list) for transcendental functions
   *
   * This is used for tangent plane refinements for
   * transcendental functions. This is the set
   * "get-previous-secant-points" in "Satisfiability
   * Modulo Transcendental Functions via Incremental
   * Linearization" by Cimatti et al., CADE 2017, for
   * each transcendental function application. We store this set for each
   * Taylor degree.
   */
  std::unordered_map<Node,
                     std::map<unsigned, std::vector<Node>>,
                     NodeHashFunction>
      d_secant_points;

  /** get Taylor series of degree n for function fa centered around point fa[0].
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
  std::pair<Node, Node> getTaylor(Node fa, unsigned n);

  /** internal variables used for constructing (cached) versions of the Taylor
   * series above.
   */
  Node d_taylor_real_fv;           // x above
  Node d_taylor_real_fv_base;      // a above
  Node d_taylor_real_fv_base_rem;  // b above

  /** cache of sum and remainder terms for getTaylor */
  std::unordered_map<Node, std::unordered_map<unsigned, Node>, NodeHashFunction>
      d_taylor_sum;
  std::unordered_map<Node, std::unordered_map<unsigned, Node>, NodeHashFunction>
      d_taylor_rem;
  /** taylor degree
   *
   * Indicates that the degree of the polynomials in the Taylor approximation of
   * all transcendental functions is 2*d_taylor_degree. This value is set
   * initially to options::nlExtTfTaylorDegree() and may be incremented
   * if the option options::nlExtTfIncPrecision() is enabled.
   */
  unsigned d_taylor_degree;
  /** PI
   *
   * Note that PI is a (symbolic, non-constant) nullary operator. This is
   * because its value cannot be computed exactly. We constraint PI to concrete
   * lower and upper bounds stored in d_pi_bound below.
   */
  Node d_pi;
  /** PI/2 */
  Node d_pi_2;
  /** -PI/2 */
  Node d_pi_neg_2;
  /** -PI */
  Node d_pi_neg;
  /** the concrete lower and upper bounds for PI */
  Node d_pi_bound[2];
}; /* class TranscendentalSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__TRANSCENDENTAL_SOLVER_H */
