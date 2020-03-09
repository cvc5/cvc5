/*********************                                                        */
/*! \file nonlinear_extension.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Extensions for incomplete handling of nonlinear multiplication.
 **
 ** Extensions to the theory of arithmetic incomplete handling of nonlinear
 ** multiplication via axiom instantiations.
 **/

#ifndef CVC4__THEORY__ARITH__NONLINEAR_EXTENSION_H
#define CVC4__THEORY__ARITH__NONLINEAR_EXTENSION_H

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
#include "theory/arith/nl_lemma_utils.h"
#include "theory/arith/nl_model.h"
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
 * (1) at full effort with no conflicts or lemmas emitted, or
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
   * This call may result in (possibly multiple) calls to d_out->lemma(...)
   * where d_out is the output channel of TheoryArith.
   *
   * If e is FULL, then we add lemmas based on context-depedent
   * simplification (see Reynolds et al FroCoS 2017).
   *
   * If e is LAST_CALL, we add lemmas based on model-based refinement
   * (see additionally Cimatti et al., TACAS 2017). The lemmas added at this
   * effort may be computed during a call to interceptModel as described below.
   */
  void check(Theory::Effort e);
  /** intercept model
   *
   * This method is called during TheoryArith::collectModelInfo, which is
   * invoked after the linear arithmetic solver passes a full effort check
   * with no lemmas.
   *
   * The argument arithModel is a map of the form { v1 -> c1, ..., vn -> cn }
   * which represents the linear arithmetic theory solver's contribution to the
   * current candidate model. That is, its collectModelInfo method is requesting
   * that equalities v1 = c1, ..., vn = cn be added to the current model, where
   * v1, ..., vn are arithmetic variables and c1, ..., cn are constants. Notice
   * arithmetic variables may be real-valued terms belonging to other theories,
   * or abstractions of applications of multiplication (kind NONLINEAR_MULT).
   *
   * This method requests that the non-linear solver inspect this model and
   * do any number of the following:
   * (1) Construct lemmas based on a model-based refinement procedure inspired
   * by Cimatti et al., TACAS 2017.,
   * (2) In the case that the nonlinear solver finds that the current
   * constraints are satisfiable, it may "repair" the values in the argument
   * arithModel so that it satisfies certain nonlinear constraints. This may
   * involve e.g. solving for variables in nonlinear equations.
   *
   * Notice that in the former case, the lemmas it constructs are not sent out
   * immediately. Instead, they are put in temporary vectors d_cmiLemmas
   * and d_cmiLemmasPp, which are then sent out (if necessary) when a last call
   * effort check is issued to this class.
   */
  void interceptModel(std::map<Node, Node>& arithModel);
  /** Does this class need a call to check(...) at last call effort? */
  bool needsCheckLastEffort() const { return d_needsLastCall; }
  /** presolve
   *
   * This function is called during TheoryArith's presolve command.
   * In this function, we send lemmas we accumulated during preprocessing,
   * for instance, definitional lemmas from expandDefinitions are sent out
   * on the output channel of TheoryArith in this function.
   */
  void presolve();
 private:
  /** Model-based refinement
   *
   * This is the main entry point of this class for generating lemmas on the
   * output channel of the theory of arithmetic.
   *
   * It is currently run at last call effort. It applies lemma schemas
   * described in Reynolds et al. FroCoS 2017 that are based on ruling out
   * the current candidate model.
   *
   * This function returns true if a lemma was added to the vector lems/lemsPp.
   * Otherwise, it returns false. In the latter case, the model object d_model
   * may have information regarding how to construct a model, in the case that
   * we determined the problem is satisfiable.
   *
   * The argument lemSE is the "side effect" of the lemmas in mlems and mlemsPp
   * (for details, see checkLastCall).
   */
  bool modelBasedRefinement(std::vector<Node>& mlems,
                            std::vector<Node>& mlemsPp,
                            std::map<Node, NlLemmaSideEffect>& lemSE);
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
   * This method adds lemmas to arguments lems, lemsPp, and wlems, each of
   * which are intended to be sent out on the output channel of TheoryArith
   * under certain conditions.
   *
   * If the set lems or lemsPp is non-empty, then no further processing is
   * necessary. The last call effort check should terminate and these
   * lemmas should be sent. The set lemsPp is distinguished from lems since
   * the preprocess flag on the lemma(...) call should be set to true.
   *
   * The "waiting" lemmas wlems contain lemmas that should be sent on the
   * output channel as a last resort. In other words, only if we are not
   * able to establish SAT via a call to checkModel(...) should wlems be
   * considered. This set typically contains tangent plane lemmas.
   *
   * The argument lemSE is the "side effect" of the lemmas from the previous
   * three calls. If a lemma is mapping to a side effect, it should be
   * processed via a call to processSideEffect(...) immediately after the
   * lemma is sent (if it is indeed sent on this call to check).
   */
  int checkLastCall(const std::vector<Node>& assertions,
                    const std::vector<Node>& false_asserts,
                    const std::vector<Node>& xts,
                    std::vector<Node>& lems,
                    std::vector<Node>& lemsPp,
                    std::vector<Node>& wlems,
                    std::map<Node, NlLemmaSideEffect>& lemSE);
  //---------------------------------------term utilities
  static bool isArithKind(Kind k);
  static Node mkLit(Node a, Node b, int status, bool isAbsolute = false);
  static Node mkAbs(Node a);
  static Node mkValidPhase(Node a, Node pi);
  static Node mkBounded( Node l, Node a, Node u );
  Node mkMonomialRemFactor(Node n, const NodeMultiset& n_exp_rem) const;
  //---------------------------------------end term utilities

  /** register monomial */
  void registerMonomial(Node n);
  void setMonomialFactor(Node a, Node b, const NodeMultiset& common);

  void registerConstraint(Node atom);
  /** assign order ids */
  void assignOrderIds(std::vector<Node>& vars,
                      NodeMultiset& d_order,
                      bool isConcrete,
                      bool isAbsolute);

  /** get assertions
   *
   * Let M be the set of assertions known by THEORY_ARITH. This function adds a
   * set of literals M' to assertions such that M' and M are equivalent.
   *
   * Examples of how M' differs with M:
   * (1) M' may not include t < c (in M) if t < c' is in M' for c' < c, where
   * c and c' are constants,
   * (2) M' may contain t = c if both t >= c and t <= c are in M.
   */
  void getAssertions(std::vector<Node>& assertions);
  /** check model
   *
   * Returns the subset of assertions whose concrete values we cannot show are
   * true in the current model. Notice that we typically cannot compute concrete
   * values for assertions involving transcendental functions. Any assertion
   * whose model value cannot be computed is included in the return value of
   * this function.
   */
  std::vector<Node> checkModelEval(const std::vector<Node>& assertions);

  //---------------------------check model
  /** Check model
   *
   * Checks the current model based on solving for equalities, and using error
   * bounds on the Taylor approximation.
   *
   * If this function returns true, then all assertions in the input argument
   * "assertions" are satisfied for all interpretations of variables within
   * their computed bounds (as stored in d_check_model_bounds).
   *
   * For details, see Section 3 of Cimatti et al CADE 2017 under the heading
   * "Detecting Satisfiable Formulas".
   *
   * The arguments lemmas and gs store the lemmas and guard literals to be sent
   * out on the output channel of TheoryArith as lemmas and calls to
   * ensureLiteral respectively.
   */
  bool checkModel(const std::vector<Node>& assertions,
                  const std::vector<Node>& false_asserts,
                  std::vector<Node>& lemmas,
                  std::vector<Node>& gs);
  //---------------------------end check model

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

  /**
   * Potentially adds lemmas to the set out and clears lemmas. Returns
   * the number of lemmas added to out. We do not add lemmas that have already
   * been sent on the output channel of TheoryArith.
   */
  unsigned filterLemmas(std::vector<Node>& lemmas, std::vector<Node>& out);
  /** singleton version of above */
  unsigned filterLemma(Node lem, std::vector<Node>& out);

  /**
   * Send lemmas in out on the output channel of theory of arithmetic.
   */
  void sendLemmas(const std::vector<Node>& out,
                  bool preprocess,
                  std::map<Node, NlLemmaSideEffect>& lemSE);
  /** Process side effect se */
  void processSideEffect(const NlLemmaSideEffect& se);

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

  /** cache of all lemmas sent on the output channel (user-context-dependent) */
  NodeSet d_lemmas;
  /** cache of terms t for which we have added the lemma ( t = 0 V t != 0 ). */
  NodeSet d_zero_split;

  /** commonly used terms */
  Node d_zero;
  Node d_one;
  Node d_neg_one;
  Node d_two;
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

  // per last-call effort

  // model values/orderings

  /** The non-linear model object
   *
   * This class is responsible for computing model values for arithmetic terms
   * and for establishing when we are able to answer "SAT".
   */
  NlModel d_model;
  /**
   * The lemmas we computed during collectModelInfo. We store two vectors of
   * lemmas to be sent out on the output channel of TheoryArith. The first
   * is not preprocessed, the second is.
   */
  std::vector<Node> d_cmiLemmas;
  std::vector<Node> d_cmiLemmasPp;
  /** the side effects of the above lemmas */
  std::map<Node, NlLemmaSideEffect> d_cmiLemmasSE;
  /**
   * The approximations computed during collectModelInfo. For details, see
   * NlModel::getModelValueRepair.
   */
  std::map<Node, std::pair<Node, Node>> d_approximations;
  /** have we successfully built the model in this SAT context? */
  context::CDO<bool> d_builtModel;

  // ordering, stores variables and 0,1,-1
  std::map<Node, unsigned> d_order_vars;
  std::vector<Node> d_order_points;
  
  //transcendental functions
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
  std::map<Node, std::vector<Node> > d_trSlaves;
  /** The transcendental functions we have done initial refinements on */
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
  /** the set of monomials we should apply tangent planes to */
  std::unordered_set<Node, NodeHashFunction> d_tplane_refine;
  // term -> coeff -> rhs -> ( status, exp, b ),
  //   where we have that : exp =>  ( coeff * term <status> rhs )
  //   b is true if degree( term ) >= degree( rhs )
  std::map<Node, std::map<Node, std::map<Node, Kind> > > d_ci;
  std::map<Node, std::map<Node, std::map<Node, Node> > > d_ci_exp;
  std::map<Node, std::map<Node, std::map<Node, bool> > > d_ci_max;

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
  std::map<Node, std::vector<Node> > d_funcCongClass;
  /**
   * A list of all functions for each kind in { EXPONENTIAL, SINE, POW, PI }
   * that are representives of their congruence class.
   */
  std::map<Kind, std::vector<Node> > d_funcMap;

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
   * each transcendental function application. We store this set for each
   * Taylor degree.
   */
  std::unordered_map<Node,
                     std::map<unsigned, std::vector<Node> >,
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
  /** cache of the above function */
  std::map<Kind, std::map<unsigned, std::vector<Node> > > d_poly_bounds;
  /** get transcendental function model bounds
   *
   * This returns the current lower and upper bounds of transcendental
   * function application tf based on Taylor of degree 2*d, which is dependent
   * on the model value of its argument.
   */
  std::pair<Node, Node> getTfModelBounds(Node tf, unsigned d);
  /** get approximate sqrt
   *
   * This approximates the square root of positive constant c. If this method
   * returns true, then l and u are updated to constants such that
   *   l <= sqrt( c ) <= u
   * The argument iter is the number of iterations in the binary search to
   * perform. By default, this is set to 15, which is usually enough to be
   * precise in the majority of simple cases, whereas not prohibitively
   * expensive to compute.
   */
  bool getApproximateSqrt(Node c, Node& l, Node& u, unsigned iter = 15) const;

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
      std::vector<Node>& nt_lemmas,
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
  std::vector<Node> checkFactoring(const std::vector<Node>& asserts,
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
   *
   * The argument lemSE is the "side effect" of the lemmas in the return
   * value of this function (for details, see checkLastCall).
   */
  std::vector<Node> checkTranscendentalTangentPlanes(
      std::map<Node, NlLemmaSideEffect>& lemSE);
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
   * tangent plane lemma to lems and its side effect (if one exists)
   * to lemSE.
   *
   * It returns false if the bounds are not precise enough to add a
   * secant or tangent plane lemma.
   */
  bool checkTfTangentPlanesFun(Node tf,
                               unsigned d,
                               std::vector<Node>& lems,
                               std::map<Node, NlLemmaSideEffect>& lemSE);
  //-------------------------------------------- end lemma schemas
}; /* class NonlinearExtension */

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__NONLINEAR_EXTENSION_H */
