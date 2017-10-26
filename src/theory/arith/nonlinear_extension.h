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

class NonlinearExtension {
 public:
  NonlinearExtension(TheoryArith& containing, eq::EqualityEngine* ee);
  ~NonlinearExtension();
  bool getCurrentSubstitution(int effort, const std::vector<Node>& vars,
                              std::vector<Node>& subs,
                              std::map<Node, std::vector<Node> >& exp);

  std::pair<bool, Node> isExtfReduced(int effort, Node n, Node on,
                                      const std::vector<Node>& exp) const;
  void check(Theory::Effort e);
  bool needsCheckLastEffort() const { return d_needsLastCall; }
  /** compare 
  * orderType = 0 : compare concrete model values
  * orderType = 1 : compare abstract model values
  * orderType = 2 : compare abs of concrete model values
  * orderType = 3 : compare abs of abstract model values
  * (for concrete vs abstract, see computeModelValue)
  */
  int compare(Node i, Node j, unsigned orderType) const;
  int compare_value(Node i, Node j, unsigned orderType) const;

  bool isMonomialSubset(Node a, Node b) const;
  void registerMonomialSubset(Node a, Node b);

 private:
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

  // Check assertions for consistency in the effort LAST_CALL with a subset of
  // the assertions, false_asserts, evaluate to false in the current model.
  // Returns the number of lemmas added on the output channel.
  int checkLastCall(const std::vector<Node>& assertions,
                    const std::set<Node>& false_asserts,
                    const std::vector<Node>& xts);

  static bool isArithKind(Kind k);
  static Node mkLit(Node a, Node b, int status, int orderType = 0);
  static Node mkAbs(Node a);
  static Node mkValidPhase(Node a, Node pi);
  static Node mkBounded( Node l, Node a, Node u );
  static Kind joinKinds(Kind k1, Kind k2);
  static Kind transKinds(Kind k1, Kind k2);
  static bool isTranscendentalKind(Kind k);
  Node mkMonomialRemFactor(Node n, const NodeMultiset& n_exp_rem) const;

  // register monomial
  void registerMonomial(Node n);
  void setMonomialFactor(Node a, Node b, const NodeMultiset& common);

  void registerConstraint(Node atom);
  // index = 0 means compute the value of n based on its children, recursively (its "concrete" value)
  // index = 1 means lookup the value of n in the model (its "abstract" value)
  // For example, if M( a ) = 2, M( b ) = 3, M( a * b ) = 5, then :
  //   computeModelValue( a*b, 0 ) = computeModelValue( a, 0 )*computeModelValue( b, 0 ) = 2*3 = 6
  //   computeModelValue( a*b, 1 ) = 5
  // In other words, index = 1 treats multiplication terms and transcendental function applications
  // as variables.
  Node computeModelValue(Node n, unsigned index = 0);

  Node get_compare_value(Node i, unsigned orderType) const;
  void assignOrderIds(std::vector<Node>& vars, NodeMultiset& d_order,
                      unsigned orderType);

  // Returns the subset of assertions that evaluate to false in the model.
  std::set<Node> getFalseInModel(const std::vector<Node>& assertions);

  // status
  // 0 : equal
  // 1 : greater than or equal
  // 2 : greater than
  // -X : (less)
  // in these functions we are iterating over variables of monomials
  // initially : exp => ( oa = a ^ ob = b )
  int compareSign(Node oa, Node a, unsigned a_index, int status,
                  std::vector<Node>& exp, std::vector<Node>& lem);
  bool compareMonomial(
      Node oa, Node a, NodeMultiset& a_exp_proc, Node ob, Node b,
      NodeMultiset& b_exp_proc, std::vector<Node>& exp, std::vector<Node>& lem,
      std::map<int, std::map<Node, std::map<Node, Node> > >& cmp_infers);
  bool compareMonomial(
      Node oa, Node a, unsigned a_index, NodeMultiset& a_exp_proc, Node ob,
      Node b, unsigned b_index, NodeMultiset& b_exp_proc, int status,
      std::vector<Node>& exp, std::vector<Node>& lem,
      std::map<int, std::map<Node, std::map<Node, Node> > >& cmp_infers);
  bool cmp_holds(Node x, Node y,
                 std::map<Node, std::map<Node, Node> >& cmp_infers,
                 std::vector<Node>& exp, std::map<Node, bool>& visited);

  bool isEntailed(Node n, bool pol);

  // Potentially sends lem on the output channel if lem has not been sent on the
  // output channel in this context. Returns the number of lemmas sent on the
  // output channel.
  int flushLemma(Node lem);

  // Potentially sends lemmas to the output channel and clears lemmas. Returns
  // the number of lemmas sent to the output channel.
  int flushLemmas(std::vector<Node>& lemmas);

  // Returns the NodeMultiset for an existing monomial.
  const NodeMultiset& getMonomialExponentMap(Node monomial) const;

  // Map from monomials to var^index.
  typedef std::map<Node, NodeMultiset> MonomialExponentMap;
  MonomialExponentMap d_m_exp;

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

  // cache of all lemmas sent
  NodeSet d_lemmas;
  NodeSet d_zero_split;
  
  // literals with Skolems (need not be satisfied by model)
  NodeSet d_skolem_atoms;

  // utilities
  Node d_zero;
  Node d_one;
  Node d_neg_one;
  Node d_true;
  Node d_false;

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
  // model values
  std::map<Node, Node> d_mv[2];

  // ordering, stores variables and 0,1,-1
  std::map<Node, unsigned> d_order_vars;
  std::vector<Node> d_order_points;
  
  //transcendental functions
  std::map<Node, Node> d_trig_base;
  std::map<Node, bool> d_trig_is_base;
  std::map< Node, bool > d_tf_initial_refine;
  // PI
  Node d_pi;
  // PI/2
  Node d_pi_2;
  // -PI/2
  Node d_pi_neg_2;
  // -PI
  Node d_pi_neg;
  Node d_pi_bound[2];
  
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
  
  //information about transcendental functions
  std::map< Kind, std::map< Node, Node > > d_tf_rep_map;  
  
  // factor skolems
  std::map< Node, Node > d_factor_skolem;
  Node getFactorSkolem( Node n, std::vector< Node >& lemmas );
  
  // tangent plane bounds
  std::map< Node, std::map< Node, Node > > d_tangent_val_bound[4];
  
  /** secant points (sorted list) for transcendental functions */
  std::map< Node, std::vector< Node > > d_secant_points;
  
  /** get Taylor series of degree n for function fa centered around point fa[0].
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
  std::pair< Node, Node > getTaylor( TNode fa, unsigned n );
  
  /** internal variables used for constructing (cached) versions
  * the Taylor series above
  */
  Node d_taylor_real_fv;          // x above
  Node d_taylor_real_fv_base;     // a above
  Node d_taylor_real_fv_base_rem; // b above
  
  /** internal cache of values for getTaylor */
  std::map< Node, std::map< unsigned, Node > > d_taylor_sum;
  std::map< Node, std::map< unsigned, Node > > d_taylor_rem;
  
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
  std::map< Node, int > d_tf_region;
  /** get monotonicity direction 
  * Returns whether the slope is positive (+1) or negative(-1) 
  * in region of transcendental function with kind k.
  * Returns 0 if region is invalid.
  */
  int regionToMonotonicityDir( Kind k, int region );
  /** get concavity
  * Returns whether we are concave (+1) or convex (-1) 
  * in region of transcendental function with kind k.
  * Returns 0 if region is invalid.
  */
  int regionToConcavity( Kind k, int region );
  /** region to lower bound */
  Node regionToLowerBound( Kind k, int region );
  /** region to upper bound */
  Node regionToUpperBound( Kind k, int region );
  /** Get derivative.
  * Returns d/dx n. Supports cases
  * for transcendental functions, multiplication,
  * addition, constants and variables.
  */
  Node getDerivative( Node n, Node x );
private:
  //-------------------------------------------- lemma schemas
  /** check split zero
  *
  * Returns a set of theory lemmas of the form
  *   t = 0 V t != 0
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
  */
  std::vector<Node> checkMonomialMagnitude( unsigned c );
  
  /** check monomial inferred bounds
  *
  * Returns a set of valid theory lemmas, based on a
  * lemma schema 
  * For more details, see Section 5 of "Design Theory
  * Solvers with Extensions" by Reynolds et al., FroCoS 2017,
  * Figure 5, this is the schema "Multiply".  
  * 
  * Examples:
  *
  * x > 0 ^ (y > z + w) => x*y > x*(z+w)
  * x < 0 ^ (y > z + w) => x*y < x*(z+w)
  *   ...where (y > z + w) and x*y exist in the current context.
  */
  std::vector<Node> checkMonomialInferBounds( std::vector<Node>& nt_lemmas,
                                              const std::set<Node>& false_asserts );
                                              
  /** check factoring
  *
  * Returns a set of valid theory lemmas, based on a
  * lemma schema that states a relationship betwen monomials
  * with common factors that occur in the same constraint.
  * 
  * Examples:
  *
  * x*z+y*z > t => ( k = x + y ^ k*z > t )
  *   ...where k is fresh x*z and y*z exist in the current context.
  */
  std::vector<Node> checkFactoring( const std::set<Node>& false_asserts );
  
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
  *  ...where s <= x*z and x*y <= t exist in the current
  *     context.
  */
  std::vector<Node> checkMonomialInferResBounds();
  
  /** check tangent planes
  *
  * Returns a set of valid theory lemmas, based on a
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
  
  //-------------------------------------------- end lemma schemas
}; /* class NonlinearExtension */

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__ARITH__NONLINEAR_EXTENSION_H */
