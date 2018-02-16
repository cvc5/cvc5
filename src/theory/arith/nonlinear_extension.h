/*********************                                                        */
/*! \file nonlinear_extension.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Extensions for incomplete handling of nonlinear multiplication.
 **
 ** Extensions to the theory of arithmetic incomplete handling of nonlinear
 ** multiplication via axiom instantiations.
 **/

#ifndef __CVC4__THEORY__ARITH__NONLINEAR_EXTENSION_H
#define __CVC4__THEORY__ARITH__NONLINEAR_EXTENSION_H

#include <stdint.h>

#include <map>
#include <queue>
#include <set>
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
#include "theory/arith/theory_arith.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace arith {

typedef std::map<Node, unsigned> NodeMultiset;

// TODO : refactor/document this class (#1287)
/** Non-linear extension class
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
 *
 * - "Satisfiability Modulo Transcendental
 * Functions via Incremental Linearization" by Cimatti
 * et al., CADE 2017.
 *
 * It's main functionality is a check(...) method,
 * which is called by TheoryArithPrivate either:
 * (1) at full effort with no conflicts or lemmas emitted,
 * or
 * (2) at last call effort.
 * In this method, this class calls d_out->lemma(...)
 * for valid arithmetic theory lemmas, based on the current set of assertions,
 * where d_out is the output channel of TheoryArith.
 */
class NonlinearExtension {
 public:
  NonlinearExtension(TheoryArith& containing, eq::EqualityEngine* ee);
  ~NonlinearExtension();
  /** Get current substitution
   *
   * This function and the one below are
   * used for context-dependent
   * simplification, see Section 3.1 of
   * "Designing Theory Solvers with Extensions"
   * by Reynolds et al. FroCoS 2017.
   *
   * effort : an identifier indicating the stage where
   *          we are performing context-dependent simplification,
   * vars : a set of arithmetic variables.
   *
   * This function populates subs and exp, such that for 0 <= i < vars.size():
   *   ( exp[vars[i]] ) => vars[i] = subs[i]
   * where exp[vars[i]] is a set of assertions
   * that hold in the current context. We call { vars -> subs } a "derivable
   * substituion" (see Reynolds et al. FroCoS 2017).
   */
  bool getCurrentSubstitution(int effort, const std::vector<Node>& vars,
                              std::vector<Node>& subs,
                              std::map<Node, std::vector<Node> >& exp);
  /** Is the term n in reduced form?
   *
   * Used for context-dependent simplification.
   *
   * effort : an identifier indicating the stage where
   *          we are performing context-dependent simplification,
   * on : the original term that we reduced to n,
   * exp : an explanation such that ( exp => on = n ).
   *
   * We return a pair ( b, exp' ) such that
   *   if b is true, then:
   *     n is in reduced form
   *     if exp' is non-null, then ( exp' => on = n )
   * The second part of the pair is used for constructing
   * minimal explanations for context-dependent simplifications.
   */
  std::pair<bool, Node> isExtfReduced(int effort, Node n, Node on,
                                      const std::vector<Node>& exp) const;
  /** Check at effort level e.
   *
   * This call may result in (possibly multiple)
   * calls to d_out->lemma(...) where d_out
   * is the output channel of TheoryArith.
   */
  void check(Theory::Effort e);
  /** Does this class need a call to check(...) at last call effort? */
  bool needsCheckLastEffort() const { return d_needsLastCall; }
  /** add definition
   *
   * This function notifies this class that lem is a formula that defines or
   * constrains an auxiliary variable. For example, during
   * TheoryArith::expandDefinitions, we replace a term like arcsin( x ) with an
   * auxiliary variable k. The lemmas 0 <= k < pi and sin( x ) = k are added as
   * definitions to this class.
   */
  void addDefinition(Node lem);
  /** presolve
   *
   * This function is called during TheoryArith's presolve command.
   * In this function, we send lemmas we accumulated during preprocessing,
   * for instance, definitional lemmas from expandDefinitions are sent out
   * on the output channel of TheoryArith in this function.
   */
  void presolve();
  /** Compare arithmetic terms i and j based an ordering.
   *
   * orderType = 0 : compare concrete model values
   * orderType = 1 : compare abstract model values
   * orderType = 2 : compare abs of concrete model values
   * orderType = 3 : compare abs of abstract model values
   * TODO (#1287) make this an enum?
   *
   * For definitions of concrete vs abstract model values,
   * see computeModelValue below.
   */
  int compare(Node i, Node j, unsigned orderType) const;
  /** Compare constant rationals i and j based an ordering.
   * orderType is the same as above.
   */
  int compare_value(Node i, Node j, unsigned orderType) const;

 private:
  /** returns true if the multiset containing the
   * factors of monomial a is a subset of the multiset
   * containing the factors of monomial b.
   */
  bool isMonomialSubset(Node a, Node b) const;
  void registerMonomialSubset(Node a, Node b);

  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

  // monomial information (context-independent)
  class MonomialIndex {
   public:
    // status 0 : n equal, -1 : n superset, 1 : n subset
    void addTerm(Node n, const std::vector<Node>& reps, NonlinearExtension* nla,
                 int status = 0, unsigned argIndex = 0);

   private:
    std::map<Node, MonomialIndex> d_data;
    std::vector<Node> d_monos;
  }; /* class MonomialIndex */

  // constraint information (context-independent)
  struct ConstraintInfo {
   public:
    Node d_rhs;
    Node d_coeff;
    Kind d_type;
  }; /* struct ConstraintInfo */

  /** check last call
   *
   * Check assertions for consistency in the effort LAST_CALL with a subset of
   * the assertions, false_asserts, that evaluate to false in the current model.
   *
   * xts : the list of (non-reduced) extended terms in the current context.
   *
   * This method returns the number of lemmas added on the output channel of
   * TheoryArith.
   */
  int checkLastCall(const std::vector<Node>& assertions,
                    const std::vector<Node>& false_asserts,
                    const std::vector<Node>& xts);
  //---------------------------------------term utilities
  static bool isArithKind(Kind k);
  static Node mkLit(Node a, Node b, int status, int orderType = 0);
  static Node mkAbs(Node a);
  static Node mkValidPhase(Node a, Node pi);
  static Node mkBounded( Node l, Node a, Node u );
  static Kind joinKinds(Kind k1, Kind k2);
  static Kind transKinds(Kind k1, Kind k2);
  static bool isTranscendentalKind(Kind k);
  Node mkMonomialRemFactor(Node n, const NodeMultiset& n_exp_rem) const;
  //---------------------------------------end term utilities

  /** register monomial */
  void registerMonomial(Node n);
  void setMonomialFactor(Node a, Node b, const NodeMultiset& common);

  void registerConstraint(Node atom);
  /** compute model value
   *
   * This computes model values for terms based on two semantics, a "concrete"
   * semantics and an "abstract" semantics.
   *
   * index = 0 means compute the value of n based on its children recursively.
   *          (we call this its "concrete" value)
   * index = 1 means lookup the value of n in the model.
   *          (we call this its "abstract" value)
   * In other words, index = 1 treats multiplication terms and transcendental
   * function applications as variables, whereas index = 0 computes their
   * actual values. This is a key distinction used in the model-based
   * refinement scheme in Cimatti et al. TACAS 2017.
   *
   * For example, if M( a ) = 2, M( b ) = 3, M( a * b ) = 5, then :
   *
   *   computeModelValue( a*b, 0 ) =
   *   computeModelValue( a, 0 )*computeModelValue( b, 0 ) = 2*3 = 6
   * whereas:
   *   computeModelValue( a*b, 1 ) = 5
   */
  Node computeModelValue(Node n, unsigned index = 0);
  /** returns the Node corresponding to the value of i in the
   * type of order orderType, which is one of values
   * described above ::compare(...).
   */
  Node get_compare_value(Node i, unsigned orderType) const;
  void assignOrderIds(std::vector<Node>& vars, NodeMultiset& d_order,
                      unsigned orderType);

  /** check model
   *
   * Returns the subset of assertions whose concrete values we cannot show are
   * true in the current model. Notice that we typically cannot compute concrete
   * values for assertions involving transcendental functions. Any assertion
   * whose model value cannot be computed is included in the return value of
   * this function.
   */
  std::vector<Node> checkModel(const std::vector<Node>& assertions);

  /** check model for transcendental functions
   *
   * Checks the current model using error bounds on the Taylor approximation.
   *
   * If this function returns true, then all assertions in the input argument
   * "assertions" are satisfied for all interpretations of transcendental
   * functions within their error bounds (as stored in d_tf_check_model_bounds).
   *
   * For details, see Section 3 of Cimatti et al CADE 2017 under the heading
   * "Detecting Satisfiable Formulas".
   */
  bool checkModelTf(const std::vector<Node>& assertions);

  /** simple check model for transcendental functions for literal
   *
   * This method returns true if literal is true for all interpretations of
   * transcendental functions within their error bounds (as stored
   * in d_tf_check_model_bounds). This is determined by a simple under/over
   * approximation of the value of sum of (linear) monomials. For example,
   * if we determine that .8 < sin( 1 ) < .9, this function will return
   * true for literals like:
   *   2.0*sin( 1 ) > 1.5
   *   -1.0*sin( 1 ) < -0.79
   *   -1.0*sin( 1 ) > -0.91
   * It will return false for literals like:
   *   sin( 1 ) > 0.85
   * It will also return false for literals like:
   *   -0.3*sin( 1 )*sin( 2 ) + sin( 2 ) > .7
   *   sin( sin( 1 ) ) > .5
   * since the bounds on these terms cannot quickly be determined.
   */
  bool simpleCheckModelTfLit(Node lit);

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
  int compareSign(Node oa, Node a, unsigned a_index, int status,
                  std::vector<Node>& exp, std::vector<Node>& lem);
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
      Node oa, Node a, NodeMultiset& a_exp_proc, Node ob, Node b,
      NodeMultiset& b_exp_proc, std::vector<Node>& exp, std::vector<Node>& lem,
      std::map<int, std::map<Node, std::map<Node, Node> > >& cmp_infers);
  /** helper function for above
   *
   * The difference is the inputs a_index and b_index, which are the indices of
   * children (factors) in monomials a and b which we are currently looking at.
   */
  bool compareMonomial(
      Node oa, Node a, unsigned a_index, NodeMultiset& a_exp_proc, Node ob,
      Node b, unsigned b_index, NodeMultiset& b_exp_proc, int status,
      std::vector<Node>& exp, std::vector<Node>& lem,
      std::map<int, std::map<Node, std::map<Node, Node> > >& cmp_infers);
  /** Check whether we have already inferred a relationship between monomials
   * x and y based on the information in cmp_infers. This computes the
   * transitive closure of the relation stored in cmp_infers.
   */
  bool cmp_holds(Node x, Node y,
                 std::map<Node, std::map<Node, Node> >& cmp_infers,
                 std::vector<Node>& exp, std::map<Node, bool>& visited);
  /** Is n entailed with polarity pol in the current context? */
  bool isEntailed(Node n, bool pol);

  /** flush lemmas
   *
   * Potentially sends lem on the output channel if lem has not been sent on the
   * output channel in this context. Returns the number of lemmas sent on the
   * output channel of TheoryArith.
   */
  int flushLemma(Node lem);

  /** Potentially sends lemmas to the output channel and clears lemmas. Returns
   * the number of lemmas sent to the output channel.
   */
  int flushLemmas(std::vector<Node>& lemmas);

  // Returns the NodeMultiset for an existing monomial.
  const NodeMultiset& getMonomialExponentMap(Node monomial) const;

  // Map from monomials to var^index.
  typedef std::map<Node, NodeMultiset> MonomialExponentMap;
  MonomialExponentMap d_m_exp;

  /**
   * Mapping from monomials to the list of variables that occur in it. For
   * example, x*x*y*z -> { x, y, z }.
   */
  std::map<Node, std::vector<Node> > d_m_vlist;
  NodeMultiset d_m_degree;
  // monomial index, by sorted variables
  MonomialIndex d_m_index;
  // list of all monomials
  std::vector<Node> d_monomials;
  // containment ordering
  std::map<Node, std::vector<Node> > d_m_contain_children;
  std::map<Node, std::vector<Node> > d_m_contain_parent;
  std::map<Node, std::map<Node, Node> > d_m_contain_mult;
  std::map<Node, std::map<Node, Node> > d_m_contain_umult;
  // ( x*y, x*z, y ) for each pair of monomials ( x*y, x*z ) with common factors
  std::map<Node, std::map<Node, Node> > d_mono_diff;

  /** cache of definition lemmas (user-context-dependent) */
  NodeSet d_def_lemmas;
  /** cache of all lemmas sent on the output channel (user-context-dependent) */
  NodeSet d_lemmas;
  /** cache of terms t for which we have added the lemma ( t = 0 V t != 0 ). */
  NodeSet d_zero_split;
  
  // literals with Skolems (need not be satisfied by model)
  NodeSet d_skolem_atoms;

  /** commonly used terms */
  Node d_zero;
  Node d_one;
  Node d_neg_one;
  Node d_true;
  Node d_false;
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

  // The theory of arithmetic containing this extension.
  TheoryArith& d_containing;

  // pointer to used equality engine
  eq::EqualityEngine* d_ee;
  // needs last call effort
  bool d_needsLastCall;

  // if d_c_info[lit][x] = ( r, coeff, k ), then ( lit <=>  (coeff * x) <k> r )
  std::map<Node, std::map<Node, ConstraintInfo> > d_c_info;
  std::map<Node, std::map<Node, bool> > d_c_info_maxm;
  std::vector<Node> d_constraints;

  // model values/orderings
  /** cache of model values
   *
   * Stores the the concrete/abstract model values
   * at indices 0 and 1 respectively.
   */
  std::map<Node, Node> d_mv[2];

  // ordering, stores variables and 0,1,-1
  std::map<Node, unsigned> d_order_vars;
  std::vector<Node> d_order_points;
  
  //transcendental functions
  std::map<Node, Node> d_trig_base;
  std::map<Node, bool> d_trig_is_base;
  std::map< Node, bool > d_tf_initial_refine;
  
  void mkPi();
  void getCurrentPiBounds( std::vector< Node >& lemmas );
private:
  //per last-call effort check
  
  //information about monomials
  std::vector< Node > d_ms;
  std::vector< Node > d_ms_vars;
  std::map<Node, bool> d_ms_proc;
  std::vector<Node> d_mterms;

  //list of monomials with factors whose model value is non-constant in model 
  //  e.g. y*cos( x )
  std::map<Node, bool> d_m_nconst_factor;
  // If ( m, p1, true ), then it would help satisfiability if m were ( >
  // if p1=true, < if p1=false )
  std::map<Node, std::map<bool, bool> > d_tplane_refine_dir;
  // term -> coeff -> rhs -> ( status, exp, b ),
  //   where we have that : exp =>  ( coeff * term <status> rhs )
  //   b is true if degree( term ) >= degree( rhs )
  std::map<Node, std::map<Node, std::map<Node, Kind> > > d_ci;
  std::map<Node, std::map<Node, std::map<Node, Node> > > d_ci_exp;
  std::map<Node, std::map<Node, std::map<Node, bool> > > d_ci_max;

  /** transcendental function representative map
   *
   * For each transcendental function n = tf( x ),
   * this stores ( n.getKind(), r ) -> n
   * where r is the current representative of x
   * in the equality engine assoiated with this class.
   */
  std::map<Kind, std::map<Node, Node> > d_tf_rep_map;

  /** bounds for transcendental functions
   *
   * For each transcendental function application t, if this stores the pair
   * (c_l, c_u) then the model M is such that c_l <= M( t ) <= c_u.
   */
  std::map<Node, std::pair<Node, Node> > d_tf_check_model_bounds;

  // factor skolems
  std::map< Node, Node > d_factor_skolem;
  Node getFactorSkolem( Node n, std::vector< Node >& lemmas );
  
  // tangent plane bounds
  std::map< Node, std::map< Node, Node > > d_tangent_val_bound[4];

  /** secant points (sorted list) for transcendental functions
   *
   * This is used for tangent plane refinements for
   * transcendental functions. This is the set
   * "get-previous-secant-points" in "Satisfiability
   * Modulo Transcendental Functions via Incremental
   * Linearization" by Cimatti et al., CADE 2017, for
   * each transcendental function application.
   */
  std::unordered_map<Node, std::vector<Node>, NodeHashFunction> d_secant_points;

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
  std::pair<Node, Node> getTaylor(TNode fa, unsigned n);

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

 private:
  //-------------------------------------------- lemma schemas
  /** check split zero
  *
  * Returns a set of theory lemmas of the form
  *   t = 0 V t != 0
  * where t is a term that exists in the current context.
  */
  std::vector<Node> checkSplitZero();

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
  std::vector<Node> checkMonomialSign();

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
  * Argument c indicates the class of inferences to perform for the (non-linear)
  * monomials in the vector d_ms.
  *   0 : compare non-linear monomials against 1,
  *   1 : compare non-linear monomials against variables,
  *   2 : compare non-linear monomials against other non-linear monomials.
  */
  std::vector<Node> checkMonomialMagnitude( unsigned c );

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
  std::vector<Node> checkMonomialInferBounds(
      std::vector<Node>& nt_lemmas, const std::vector<Node>& false_asserts);

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
  std::vector<Node> checkFactoring(const std::vector<Node>& false_asserts);

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
  std::vector<Node> checkMonomialInferResBounds();

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
  std::vector<Node> checkTangentPlanes();

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
  std::vector<Node> checkTranscendentalInitialRefine();

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
  std::vector<Node> checkTranscendentalMonotonic();

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
  std::vector<Node> checkTranscendentalTangentPlanes();
  //-------------------------------------------- end lemma schemas
}; /* class NonlinearExtension */

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__ARITH__NONLINEAR_EXTENSION_H */
