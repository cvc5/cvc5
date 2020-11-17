/*********************                                                        */
/*! \file transcendental_state.h
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

#ifndef CVC4__THEORY__ARITH__NL__TRANSCENDENTAL__TRANSCENDENTAL_STATE_H
#define CVC4__THEORY__ARITH__NL__TRANSCENDENTAL__TRANSCENDENTAL_STATE_H

#include "expr/node.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/arith/nl/transcendental/utils.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

struct TranscendentalState
{
  TranscendentalState(InferenceManager& im, NlModel& model);

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
  void init(const std::vector<Node>& assertions,
            const std::vector<Node>& false_asserts,
            const std::vector<Node>& xts);

  void mkPi();
  void getCurrentPiBounds();

  std::pair<Node, Node> getClosestSecantPoints(TNode e, TNode c, unsigned d)
  {
    // bounds are the minimum and maximum previous secant points
    // should not repeat secant points: secant lemmas should suffice to
    // rule out previous assignment
    Assert(
        std::find(d_secant_points[e][d].begin(), d_secant_points[e][d].end(), c)
        == d_secant_points[e][d].end());
    // Insert into the (temporary) vector. We do not update this vector
    // until we are sure this secant plane lemma has been processed. We do
    // this by mapping the lemma to a side effect below.
    std::vector<Node> spoints = d_secant_points[e][d];
    spoints.push_back(c);

    // sort
    sortByNlModel(spoints.begin(), spoints.end(), &d_model);
    // get the resulting index of c
    unsigned index =
        std::find(spoints.begin(), spoints.end(), c) - spoints.begin();

    // bounds are the next closest upper/lower bound values
    return {index > 0 ? spoints[index - 1] : Node(),
            index < spoints.size() - 1 ? spoints[index + 1] : Node()};
  }

  Node mkSecantPlane(TNode arg, TNode b, TNode c, TNode approx, TNode approx_c)
  {
    NodeManager* nm = NodeManager::currentNM();
    // Figure 3 : P(l), P(u), for s = 0,1
    Node approx_b =
        Rewriter::rewrite(approx.substitute(d_taylor.getTaylorVariable(), b));
    // Figure 3: S_l( x ), S_u( x ) for s = 0,1
    Node rcoeff_n = Rewriter::rewrite(nm->mkNode(Kind::MINUS, b, c));
    Assert(rcoeff_n.isConst());
    Rational rcoeff = rcoeff_n.getConst<Rational>();
    Assert(rcoeff.sgn() != 0);
    return nm->mkNode(Kind::PLUS,
                      approx_b,
                      nm->mkNode(Kind::MULT,
                                 nm->mkNode(Kind::MINUS, approx_b, approx_c),
                                 nm->mkConst(rcoeff.inverse()),
                                 nm->mkNode(Kind::MINUS, arg, b)));
  }

  NlLemma mkSecantLemma(
      TNode lower, TNode upper, int concavity, TNode tf, TNode splane)
  {
    NodeManager* nm = NodeManager::currentNM();
    // With respect to Figure 3, this is slightly different.
    // In particular, we chose b to be the model value of bounds[s],
    // which is a constant although bounds[s] may not be (e.g. if it
    // contains PI).
    // To ensure that c...b does not cross an inflection point,
    // we guard with the symbolic version of bounds[s].
    // This leads to lemmas e.g. of this form:
    //   ( c <= x <= PI/2 ) => ( sin(x) < ( P( b ) - P( c ) )*( x -
    //   b ) + P( b ) )
    // where b = (PI/2)^M, the current value of PI/2 in the model.
    // This is sound since we are guarded by the symbolic
    // representation of PI/2.
    Node antec_n = nm->mkNode(Kind::AND,
                              nm->mkNode(Kind::GEQ, tf[0], lower),
                              nm->mkNode(Kind::LEQ, tf[0], upper));
    Node lem = nm->mkNode(
        Kind::IMPLIES,
        antec_n,
        nm->mkNode(concavity == 1 ? Kind::LEQ : Kind::GEQ, tf, splane));
    Trace("nl-ext-tftp-debug2")
        << "*** Secant plane lemma (pre-rewrite) : " << lem << std::endl;
    lem = Rewriter::rewrite(lem);
    Trace("nl-ext-tftp-lemma")
        << "*** Secant plane lemma : " << lem << std::endl;
    Assert(d_model.computeAbstractModelValue(lem) == d_false);
    return NlLemma(lem, LemmaProperty::NONE, nullptr, InferenceId::NL_T_SECANT);
  }

  void mkSecant(TNode lower,
                TNode approx_lower,
                TNode upper,
                TNode approx_upper,
                TNode tf,
                TNode c,
                unsigned d,
                int concavity)
  {
    if (lower == upper) return;
    Node splane =
        mkSecantPlane(tf[0], lower, upper, approx_lower, approx_upper);

    NlLemma nlem = mkSecantLemma(lower, upper, concavity, tf, splane);
    // The side effect says that if lem is added, then we should add the
    // secant point c for (tf,d).
    nlem.d_secantPoint.push_back(std::make_tuple(tf, d, c));
    d_im.addPendingArithLemma(nlem, true);
  }

  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
  Node d_neg_one;

  /** The inference manager that we push conflicts and lemmas to. */
  InferenceManager& d_im;
  /** Reference to the non-linear model object */
  NlModel& d_model;

  TaylorGenerator d_taylor;

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
};

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__NL__TRANSCENDENTAL__TRANSCENDENTAL_STATE_H */
