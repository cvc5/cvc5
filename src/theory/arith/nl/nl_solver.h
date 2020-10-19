/*********************                                                        */
/*! \file nl_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Solver for standard non-linear constraints
 **/

#ifndef CVC4__THEORY__ARITH__NL_SOLVER_H
#define CVC4__THEORY__ARITH__NL_SOLVER_H

#include <map>
#include <unordered_map>
#include <utility>
#include <vector>

#include "context/cdhashset.h"
#include "context/cdinsert_hashmap.h"
#include "context/cdlist.h"
#include "context/cdqueue.h"
#include "context/context.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_constraint.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/arith/nl/nl_monomial.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

typedef std::map<Node, unsigned> NodeMultiset;

/** Non-linear solver class
 *
 * This class implements model-based refinement schemes
 * for non-linear arithmetic, described in:
 *
 * - "Invariant Checking of NRA Transition Systems
 * via Incremental Reduction to LRA with EUF" by
 * Cimatti et al., TACAS 2017.
 *
 * - Section 5 of "Desiging Theory Solvers with
 * Extensions" by Reynolds et al., FroCoS 2017.
 */
class NlSolver
{
  typedef std::map<Node, NodeMultiset> MonomialExponentMap;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  NlSolver(InferenceManager& im, ArithState& astate, NlModel& model);
  ~NlSolver();

  /** init last call
   *
   * This is called at the beginning of last call effort check, where
   * assertions are the set of assertions belonging to arithmetic,
   * false_asserts is the subset of assertions that are false in the current
   * model, and xts is the set of extended function terms that are active in
   * the current context.
   */
  void initLastCall(const std::vector<Node>& assertions,
                    const std::vector<Node>& false_asserts,
                    const std::vector<Node>& xts);
  //-------------------------------------------- lemma schemas


  /** check monomial inferred bounds
   *
   * Returns a set of valid theory lemmas, based on a
   * lemma schema that infers new constraints about existing
   * terms based on mulitplying both sides of an existing
   * constraint by a term.
   * For more details, see Section 5 of "Design Theory
   * Solvers with Extensions" by Reynolds et al., FroCoS 2017,
   * Figure 5, this is the schema "Multiply".
   *
   * Examples:
   *
   * x > 0 ^ (y > z + w) => x*y > x*(z+w)
   * x < 0 ^ (y > z + w) => x*y < x*(z+w)
   *   ...where (y > z + w) and x*y are a constraint and term
   *      that occur in the current context.
   */
  void checkMonomialInferBounds(
      const std::vector<Node>& asserts,
      const std::vector<Node>& false_asserts);

  /** check monomial infer resolution bounds
   *
   * Returns a set of valid theory lemmas, based on a
   * lemma schema which "resolves" upper bounds
   * of one inequality with lower bounds for another.
   * This schema is not enabled by default, and can
   * be enabled by --nl-ext-rbound.
   *
   * Examples:
   *
   *  ( y>=0 ^ s <= x*z ^ x*y <= t ) => y*s <= z*t
   *  ...where s <= x*z and x*y <= t are constraints
   *     that occur in the current context.
   */
  void checkMonomialInferResBounds();

  /** check tangent planes
   *
   * Returns a set of valid theory lemmas, based on an
   * "incremental linearization" of non-linear monomials.
   * This linearization is accomplished by adding constraints
   * corresponding to "tangent planes" at the current
   * model value of each non-linear monomial. In particular
   * consider the definition for constants a,b :
   *   T_{a,b}( x*y ) = b*x + a*y - a*b.
   * The lemmas added by this function are of the form :
   *  ( ( x>a ^ y<b) ^ (x<a ^ y>b) ) => x*y < T_{a,b}( x*y )
   *  ( ( x>a ^ y>b) ^ (x<a ^ y<b) ) => x*y > T_{a,b}( x*y )
   * It is inspired by "Invariant Checking of NRA Transition
   * Systems via Incremental Reduction to LRA with EUF" by
   * Cimatti et al., TACAS 2017.
   * This schema is not terminating in general.
   * It is not enabled by default, and can
   * be enabled by --nl-ext-tplanes.
   *
   * Examples:
   *
   * ( ( x>2 ^ y>5) ^ (x<2 ^ y<5) ) => x*y > 5*x + 2*y - 10
   * ( ( x>2 ^ y<5) ^ (x<2 ^ y>5) ) => x*y < 5*x + 2*y - 10
   */
  void checkTangentPlanes(bool asWaitingLemmas);

  //-------------------------------------------- end lemma schemas
 private:
  /** The inference manager that we push conflicts and lemmas to. */
  InferenceManager& d_im;
  /** Reference to the state. */
  ArithState& d_astate;
  /** Reference to the non-linear model object */
  NlModel& d_model;
  /** commonly used terms */
  Node d_zero;
  Node d_one;
  Node d_neg_one;
  Node d_two;
  Node d_true;
  Node d_false;
  /** Context-independent database of monomial information */
  MonomialDb d_mdb;
  /** Context-independent database of constraint information */
  ConstraintDb d_cdb;

  // ( x*y, x*z, y ) for each pair of monomials ( x*y, x*z ) with common factors
  std::map<Node, std::map<Node, Node> > d_mono_diff;

  /** cache of terms t for which we have added the lemma ( t = 0 V t != 0 ). */
  NodeSet d_zero_split;

  // information about monomials
  std::vector<Node> d_ms;
  std::vector<Node> d_ms_vars;
  std::vector<Node> d_mterms;

  /** the set of monomials we should apply tangent planes to */
  std::unordered_set<Node, NodeHashFunction> d_tplane_refine;
  /** maps nodes to their factor skolems */
  std::map<Node, Node> d_factor_skolem;
  /** tangent plane bounds */
  std::map<Node, std::map<Node, Node> > d_tangent_val_bound[4];
  // term -> coeff -> rhs -> ( status, exp, b ),
  //   where we have that : exp =>  ( coeff * term <status> rhs )
  //   b is true if degree( term ) >= degree( rhs )
  std::map<Node, std::map<Node, std::map<Node, Kind> > > d_ci;
  std::map<Node, std::map<Node, std::map<Node, Node> > > d_ci_exp;
  std::map<Node, std::map<Node, std::map<Node, bool> > > d_ci_max;

}; /* class NlSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__NL_SOLVER_H */
