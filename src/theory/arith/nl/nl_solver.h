/*********************                                                        */
/*! \file nl_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
#include "theory/arith/nl/nl_constraint.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/arith/nl/nl_monomial.h"
#include "theory/arith/theory_arith.h"

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
  NlSolver(TheoryArith& containing, NlModel& model);
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
  /** check split zero
   *
   * Returns a set of theory lemmas of the form
   *   t = 0 V t != 0
   * where t is a term that exists in the current context.
   */
  std::vector<NlLemma> checkSplitZero();

  /** check monomial sign
   *
   * Returns a set of valid theory lemmas, based on a
   * lemma schema which ensures that non-linear monomials
   * respect sign information based on their facts.
   * For more details, see Section 5 of "Design Theory
   * Solvers with Extensions" by Reynolds et al., FroCoS 2017,
   * Figure 5, this is the schema "Sign".
   *
   * Examples:
   *
   * x > 0 ^ y > 0 => x*y > 0
   * x < 0 => x*y*y < 0
   * x = 0 => x*y*z = 0
   */
  std::vector<NlLemma> checkMonomialSign();

  /** check monomial magnitude
   *
   * Returns a set of valid theory lemmas, based on a
   * lemma schema which ensures that comparisons between
   * non-linear monomials respect the magnitude of their
   * factors.
   * For more details, see Section 5 of "Design Theory
   * Solvers with Extensions" by Reynolds et al., FroCoS 2017,
   * Figure 5, this is the schema "Magnitude".
   *
   * Examples:
   *
   * |x|>|y| => |x*z|>|y*z|
   * |x|>|y| ^ |z|>|w| ^ |x|>=1 => |x*x*z*u|>|y*w|
   *
   * Argument c indicates the class of inferences to perform for the
   * (non-linear) monomials in the vector d_ms. 0 : compare non-linear monomials
   * against 1, 1 : compare non-linear monomials against variables, 2 : compare
   * non-linear monomials against other non-linear monomials.
   */
  std::vector<NlLemma> checkMonomialMagnitude(unsigned c);

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
  std::vector<NlLemma> checkMonomialInferBounds(
      std::vector<NlLemma>& nt_lemmas,
      const std::vector<Node>& asserts,
      const std::vector<Node>& false_asserts);

  /** check factoring
   *
   * Returns a set of valid theory lemmas, based on a
   * lemma schema that states a relationship betwen monomials
   * with common factors that occur in the same constraint.
   *
   * Examples:
   *
   * x*z+y*z > t => ( k = x + y ^ k*z > t )
   *   ...where k is fresh and x*z + y*z > t is a
   *      constraint that occurs in the current context.
   */
  std::vector<NlLemma> checkFactoring(const std::vector<Node>& asserts,
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
  std::vector<NlLemma> checkMonomialInferResBounds();

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
  std::vector<NlLemma> checkTangentPlanes();

  //-------------------------------------------- end lemma schemas
 private:
  // The theory of arithmetic containing this extension.
  TheoryArith& d_containing;
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

  // ordering, stores variables and 0,1,-1
  std::map<Node, unsigned> d_order_vars;
  std::vector<Node> d_order_points;

  // information about monomials
  std::vector<Node> d_ms;
  std::vector<Node> d_ms_vars;
  std::map<Node, bool> d_ms_proc;
  std::vector<Node> d_mterms;

  // list of monomials with factors whose model value is non-constant in model
  //  e.g. y*cos( x )
  std::map<Node, bool> d_m_nconst_factor;
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

  /** Make literal */
  static Node mkLit(Node a, Node b, int status, bool isAbsolute = false);
  /** register monomial */
  void setMonomialFactor(Node a, Node b, const NodeMultiset& common);
  /** assign order ids */
  void assignOrderIds(std::vector<Node>& vars,
                      NodeMultiset& d_order,
                      bool isConcrete,
                      bool isAbsolute);

  /** Check whether we have already inferred a relationship between monomials
   * x and y based on the information in cmp_infers. This computes the
   * transitive closure of the relation stored in cmp_infers.
   */
  bool cmp_holds(Node x,
                 Node y,
                 std::map<Node, std::map<Node, Node> >& cmp_infers,
                 std::vector<Node>& exp,
                 std::map<Node, bool>& visited);
  /** In the following functions, status states a relationship
   * between two arithmetic terms, where:
   * 0 : equal
   * 1 : greater than or equal
   * 2 : greater than
   * -X : (greater -> less)
   * TODO (#1287) make this an enum?
   */
  /** compute the sign of a.
   *
   * Calls to this function are such that :
   *    exp => ( oa = a ^ a <status> 0 )
   *
   * This function iterates over the factors of a,
   * where a_index is the index of the factor in a
   * we are currently looking at.
   *
   * This function returns a status, which indicates
   * a's relationship to 0.
   * We add lemmas to lem of the form given by the
   * lemma schema checkSign(...).
   */
  int compareSign(Node oa,
                  Node a,
                  unsigned a_index,
                  int status,
                  std::vector<Node>& exp,
                  std::vector<NlLemma>& lem);
  /** compare monomials a and b
   *
   * Initially, a call to this function is such that :
   *    exp => ( oa = a ^ ob = b )
   *
   * This function returns true if we can infer a valid
   * arithmetic lemma of the form :
   *    P => abs( a ) >= abs( b )
   * where P is true and abs( a ) >= abs( b ) is false in the
   * current model.
   *
   * This function is implemented by "processing" factors
   * of monomials a and b until an inference of the above
   * form can be made. For example, if :
   *   a = x*x*y and b = z*w
   * Assuming we are trying to show abs( a ) >= abs( c ),
   * then if abs( M( x ) ) >= abs( M( z ) ) where M is the current model,
   * then we can add abs( x ) >= abs( z ) to our explanation, and
   * mark one factor of x as processed in a, and
   * one factor of z as processed in b. The number of processed factors of a
   * and b are stored in a_exp_proc and b_exp_proc respectively.
   *
   * cmp_infers stores information that is helpful
   * in discarding redundant inferences.  For example,
   * we do not want to infer abs( x ) >= abs( z ) if
   * we have already inferred abs( x ) >= abs( y ) and
   * abs( y ) >= abs( z ).
   * It stores entries of the form (status,t1,t2)->F,
   * which indicates that we constructed a lemma F that
   * showed t1 <status> t2.
   *
   * We add lemmas to lem of the form given by the
   * lemma schema checkMagnitude(...).
   */
  bool compareMonomial(
      Node oa,
      Node a,
      NodeMultiset& a_exp_proc,
      Node ob,
      Node b,
      NodeMultiset& b_exp_proc,
      std::vector<Node>& exp,
      std::vector<NlLemma>& lem,
      std::map<int, std::map<Node, std::map<Node, Node> > >& cmp_infers);
  /** helper function for above
   *
   * The difference is the inputs a_index and b_index, which are the indices of
   * children (factors) in monomials a and b which we are currently looking at.
   */
  bool compareMonomial(
      Node oa,
      Node a,
      unsigned a_index,
      NodeMultiset& a_exp_proc,
      Node ob,
      Node b,
      unsigned b_index,
      NodeMultiset& b_exp_proc,
      int status,
      std::vector<Node>& exp,
      std::vector<NlLemma>& lem,
      std::map<int, std::map<Node, std::map<Node, Node> > >& cmp_infers);
  /** Get factor skolem for n, add resulting lemmas to lemmas */
  Node getFactorSkolem(Node n, std::vector<NlLemma>& lemmas);
}; /* class NlSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__NL_SOLVER_H */
