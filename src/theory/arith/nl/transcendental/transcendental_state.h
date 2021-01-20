/*********************                                                        */
/*! \file transcendental_state.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer, Andrew Reynolds
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
#include "expr/proof_set.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/arith/nl/transcendental/proof_checker.h"
#include "theory/arith/nl/transcendental/taylor_generator.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

/**
 * This enum indicates whether some function is convex, concave or unknown at
 * some point.
 */
enum class Convexity
{
  CONVEX,
  CONCAVE,
  UNKNOWN
};
inline std::ostream& operator<<(std::ostream& os, Convexity c) {
  switch (c) {
    case Convexity::CONVEX: return os << "CONVEX";
    case Convexity::CONCAVE: return os << "CONCAVE";
    default: return os << "UNKNOWN";
  }
}

/**
 * Holds common state and utilities for transcendental solvers.
 *
 * This includes common lookups and caches as well as generic utilities for
 * secant plane lemmas and taylor approximations.
 */
struct TranscendentalState
{
  TranscendentalState(InferenceManager& im,
                      NlModel& model,
                      ProofNodeManager* pnm,
                      context::UserContext* c);

  /**
   * Checks whether proofs are enabled.
   */
  bool isProofEnabled() const;
  /**
   * Creates and returns a new LazyCDProof that can be used to prove some lemma.
   */
  CDProof* getProof();

  /** init last call
   *
   * This is called at the beginning of last call effort check xts is the set of
   * extended function terms that are active in the current context.
   *
   * This call may add lemmas to lems based on registering term
   * information (for example to ensure congruence of terms).
   * It puts terms that need to be treated further as a master term on their own
   * (for example purification of sine terms) into needsMaster.
   */
  void init(const std::vector<Node>& xts, std::vector<Node>& needsMaster);

  /**
   * Checks for terms that are congruent but disequal to a.
   * If any are found, appropriate lemmas are sent.
   * @param a Some node
   * @param argTrie Lookup for equivalence classes
   */
  void ensureCongruence(TNode a, std::map<Kind, ArgTrie>& argTrie);

  /** Initialize members for pi-related values */
  void mkPi();
  /** Get current bounds for pi as a lemma */
  void getCurrentPiBounds();

  /**
   * Get the two closest secant points from the once stored already.
   * "closest" is determined according to the current model.
   * @param e The transcendental term (like (exp t))
   * @param center The point currently under consideration (probably the model
   * of t)
   * @param d The taylor degree.
   */
  std::pair<Node, Node> getClosestSecantPoints(TNode e,
                                               TNode center,
                                               unsigned d);

  /**
   * Construct a secant plane as function in arg between lower and upper
   * @param arg The argument of the transcendental term
   * @param lower Left secant point
   * @param upper Right secant point
   * @param lval Evaluation at lower
   * @param uval Evaluation at upper
   */
  Node mkSecantPlane(
      TNode arg, TNode lower, TNode upper, TNode lval, TNode uval);

  /**
   * Construct a secant lemma between lower and upper for tf.
   * @param lower Left secant point
   * @param upper Right secant point
   * @param concavity Concavity of the current regions
   * @param tf Current transcendental term
   * @param splane Secant plane as computed by mkSecantPlane()
   */
  NlLemma mkSecantLemma(TNode lower,
                        TNode upper,
                        TNode lapprox,
                        TNode uapprox,
                        int csign,
                        Convexity convexity,
                        TNode tf,
                        TNode splane,
                        unsigned actual_d);

  /**
   * Construct and send secant lemmas (if appropriate)
   * @param bounds Secant bounds
   * @param poly_approx Polynomial approximation
   * @param center Current point
   * @param cval Evaluation at c
   * @param tf Current transcendental term
   * @param d Current taylor degree
   * @param concavity Concavity in region of c
   */
  void doSecantLemmas(const std::pair<Node, Node>& bounds,
                      TNode poly_approx,
                      TNode center,
                      TNode cval,
                      TNode tf,
                      Convexity convexity,
                      unsigned d,
                      unsigned actual_d);

  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
  Node d_neg_one;

  /** The inference manager that we push conflicts and lemmas to. */
  InferenceManager& d_im;
  /** Reference to the non-linear model object */
  NlModel& d_model;
  /** Utility to compute taylor approximations */
  TaylorGenerator d_taylor;
  /**
   * Pointer to the current proof node manager. nullptr, if proofs are
   * disabled.
   */
  ProofNodeManager* d_pnm;
  /** The user context. */
  context::UserContext* d_ctx;
  /**
   * A CDProofSet that hands out CDProof objects for lemmas.
   */
  std::unique_ptr<CDProofSet<CDProof>> d_proof;

  /** The proof checker for transcendental proofs */
  std::unique_ptr<TranscendentalProofRuleChecker> d_proofChecker;

  /**
   * Some transcendental functions f(t) are "purified", e.g. we add
   * t = y ^ f(t) = f(y) where y is a fresh variable. Those that are not
   * purified we call "master terms".
   *
   * The maps below maintain a master/slave relationship over
   * transcendental functions (SINE, EXPONENTIAL, PI), where above
   * f(y) is the master of itself and of f(t).
   *
   * This is used for ensuring that the argument y of SINE we process is on
   * the interval [-pi .. pi], and that exponentials are not applied to
   * arguments that contain transcendental functions.
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
   * because its value cannot be computed exactly. We constraint PI to
   * concrete lower and upper bounds stored in d_pi_bound below.
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
