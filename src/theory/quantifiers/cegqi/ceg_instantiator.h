/*********************                                                        */
/*! \file ceg_instantiator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief counterexample-guided quantifier instantiation
 **/


#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__CEG_INSTANTIATOR_H
#define CVC4__THEORY__QUANTIFIERS__CEG_INSTANTIATOR_H

#include <vector>

#include "expr/node.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

class Instantiator;
class InstantiatorPreprocess;
class InstStrategyCegqi;

/**
 * Descriptions of the types of constraints that a term was solved for in.
 */
enum CegTermType
{
  // invalid
  CEG_TT_INVALID,
  // term was the result of solving an equality
  CEG_TT_EQUAL,
  // term was the result of solving a non-strict lower bound x >= t
  CEG_TT_LOWER,
  // term was the result of solving a strict lower bound x > t
  CEG_TT_LOWER_STRICT,
  // term was the result of solving a non-strict upper bound x <= t
  CEG_TT_UPPER,
  // term was the result of solving a strict upper bound x < t
  CEG_TT_UPPER_STRICT,
};
/** make (non-strict term type) c a strict term type */
CegTermType mkStrictCTT(CegTermType c);
/** negate c (lower/upper bounds are swapped) */
CegTermType mkNegateCTT(CegTermType c);
/** is c a strict term type? */
bool isStrictCTT(CegTermType c);
/** is c a lower bound? */
bool isLowerBoundCTT(CegTermType c);
/** is c an upper bound? */
bool isUpperBoundCTT(CegTermType c);

/** Term Properties
 *
 * Stores properties for a variable to solve for in counterexample-guided
 * instantiation.
 *
 * For LIA, this includes the coefficient of the variable, and the bound type
 * for the variable.
 */
class TermProperties {
 public:
  TermProperties() : d_type(CEG_TT_EQUAL) {}
  virtual ~TermProperties() {}

  /**
   * Type for the solution term. For arithmetic this corresponds to bound type
   * of the constraint that the constraint the term was solved for in.
   */
  CegTermType d_type;
  // for arithmetic
  Node d_coeff;
  // get cache node
  // we consider terms + TermProperties that are unique up to their cache node
  // (see constructInstantiationInc)
  virtual Node getCacheNode() const { return d_coeff; }
  // is non-basic 
  virtual bool isBasic() const { return d_coeff.isNull(); }
  // get modified term 
  virtual Node getModifiedTerm( Node pv ) const {
    if( !d_coeff.isNull() ){
      return NodeManager::currentNM()->mkNode( kind::MULT, d_coeff, pv );
    }else{
      return pv;
    }
  }
  // compose property, should be such that: 
  //   p.getModifiedTerm( this.getModifiedTerm( x ) ) = this_updated.getModifiedTerm( x )
  virtual void composeProperty(TermProperties& p);
};

/** Solved form
 *  This specifies a substitution:
 *  { d_props[i].getModifiedTerm(d_vars[i]) -> d_subs[i] | i = 0...|d_vars| }
 */
class SolvedForm {
public:
  // list of variables
  std::vector< Node > d_vars;
  // list of terms that they are substituted to
  std::vector< Node > d_subs;
  // properties for each variable
  std::vector< TermProperties > d_props;
  // the variables that have non-basic information regarding how they are substituted
  //   an example is for linear arithmetic, we store "substitution with coefficients".
  std::vector<Node> d_non_basic;
  // push the substitution pv_prop.getModifiedTerm(pv) -> n
  void push_back(Node pv, Node n, TermProperties& pv_prop);
  // pop the substitution pv_prop.getModifiedTerm(pv) -> n
  void pop_back(Node pv, Node n, TermProperties& pv_prop);
  // is this solved form empty?
  bool empty() { return d_vars.empty(); }
public:
  // theta values (for LIA, see Section 4 of Reynolds/King/Kuncak FMSD 2017)
  std::vector< Node > d_theta;
  // get the current value for theta (for LIA, see Section 4 of Reynolds/King/Kuncak FMSD 2017)
  Node getTheta() {
    if( d_theta.empty() ){
      return Node::null();
    }else{
      return d_theta[d_theta.size()-1];
    }
  }
};

/** instantiation effort levels
 *
 * This effort is used to stratify the construction of
 * instantiations for some theories that may result to
 * using model value instantiations.
 */
enum CegInstEffort
{
  // uninitialized
  CEG_INST_EFFORT_NONE,
  // standard effort level
  CEG_INST_EFFORT_STANDARD,
  // standard effort level, but we have used model values
  CEG_INST_EFFORT_STANDARD_MV,
  // full effort level
  CEG_INST_EFFORT_FULL
};

std::ostream& operator<<(std::ostream& os, CegInstEffort e);

/** instantiation phase for variables
 *
 * This indicates the phase in which we constructed
 * a substitution for individual variables.
 */
enum CegInstPhase
{
  // uninitialized
  CEG_INST_PHASE_NONE,
  // instantiation constructed during traversal of equivalence classes
  CEG_INST_PHASE_EQC,
  // instantiation constructed during solving equalities
  CEG_INST_PHASE_EQUAL,
  // instantiation constructed by looking at theory assertions
  CEG_INST_PHASE_ASSERTION,
  // instantiation constructed by querying model value
  CEG_INST_PHASE_MVALUE,
};

std::ostream& operator<<(std::ostream& os, CegInstPhase phase);

/**
 * The handled status of a sort/term/quantified formula, indicating whether
 * counterexample-guided instantiation handles it.
 */
enum CegHandledStatus
{
  // the sort/term/quantified formula is unhandled by cegqi
  CEG_UNHANDLED,
  // the sort/term/quantified formula is partially handled by cegqi
  CEG_PARTIALLY_HANDLED,
  // the sort/term/quantified formula is handled by cegqi
  CEG_HANDLED,
  // the sort/term/quantified formula is handled by cegqi, regardless of
  // additional factors
  CEG_HANDLED_UNCONDITIONAL,
};
std::ostream& operator<<(std::ostream& os, CegHandledStatus status);

/** Ceg instantiator
 *
 * This class manages counterexample-guided quantifier instantiation
 * for a single quantified formula.
 *
 * For details on counterexample-guided quantifier instantiation
 * (for linear arithmetic), see Reynolds/King/Kuncak FMSD 2017.
 */
class CegInstantiator {
 public:
  /**
   * The instantiator will be constructing instantiations for quantified formula
   * q, parent is the owner of this object.
   */
  CegInstantiator(Node q, InstStrategyCegqi* parent);
  virtual ~CegInstantiator();
  /** check
   * This adds instantiations based on the state of d_vars in current context
   * on the output channel d_out of this class.
   */
  bool check();
  /** presolve for quantified formula
   *
   * This initializes formulas that help static learning of the quantifier-free
   * solver. It is only called if the option --cbqi-prereg-inst is used.
   */
  void presolve(Node q);
  /** Register the counterexample lemma
   *
   * @param lem contains the counterexample lemma of the quantified formula we
   * are processing. The counterexample lemma is the formula { ~phi[e/x] } in
   * Figure 1 of Reynolds et al. FMSD 2017.
   * @param ce_vars contains the variables e. Notice these are variables of
   * INST_CONSTANT kind, since we do not permit bound variables in assertions.
   * This method may add additional variables to this vector if it decides there
   * are additional auxiliary variables to solve for.
   * @param auxLems : if this method decides that additional lemmas should be
   * sent on the output channel, they are added to this vector, and sent out by
   * the caller of this method.
   */
  void registerCounterexampleLemma(Node lem,
                                   std::vector<Node>& ce_vars,
                                   std::vector<Node>& auxLems);
  //------------------------------interface for instantiators
  /** get quantifiers engine */
  QuantifiersEngine* getQuantifiersEngine() { return d_qe; }
  /** push stack variable
   * This adds a new variable to solve for in the stack
   * of variables we are processing. This stack is only
   * used for datatypes, where e.g. the DtInstantiator
   * solving for a list x may push the stack "variables"
   * head(x) and tail(x).
   */
  void pushStackVariable(Node v);
  /** pop stack variable */
  void popStackVariable();
  /** construct instantiation increment
   *
   * Adds the substitution { pv_prop.getModifiedTerm(pv) -> n } to the current
   * instantiation, specified by sf.
   *
   * This function returns true if a call to
   * QuantifiersEngine::addInstantiation(...)
   * was successfully made in a recursive call.
   *
   * The solved form sf is reverted to its original state if
   *   this function returns false, or
   *   revertOnSuccess is true and this function returns true.
   */
  bool constructInstantiationInc(Node pv,
                                 Node n,
                                 TermProperties& pv_prop,
                                 SolvedForm& sf,
                                 bool revertOnSuccess = false);
  /** get the current model value of term n */
  Node getModelValue(Node n);
  /** get bound variable for type
   *
   * This gets the next (canonical) bound variable of
   * type tn. This can be used for instance when
   * constructing instantiations that involve witness expressions.
   */
  Node getBoundVariable(TypeNode tn);
  /** has this assertion been marked as solved? */
  bool isSolvedAssertion(Node n) const;
  /** marked solved */
  void markSolved(Node n, bool solved = true);
  //------------------------------end interface for instantiators

  /**
   * Get the number of atoms in the counterexample lemma of the quantified
   * formula we are processing with this class.
   */
  unsigned getNumCEAtoms() { return d_ce_atoms.size(); }
  /**
   * Get the i^th atom of the counterexample lemma of the quantified
   * formula we are processing with this class.
   */
  Node getCEAtom(unsigned i) { return d_ce_atoms[i]; }
  /** is n a term that is eligible for instantiation? */
  bool isEligible(Node n);
  /** does n have variable pv? */
  bool hasVariable(Node n, Node pv);
  /** are we processing a nested quantified formula? */
  bool hasNestedQuantification() const { return d_is_nested_quant; }
  /**
   * Are we allowed to instantiate the current quantified formula with n? This
   * includes restrictions such as if n is a variable, it must occur free in
   * the current quantified formula.
   */
  bool isEligibleForInstantiation(Node n) const;
  //------------------------------------ static queries
  /** Is k a kind for which counterexample-guided instantiation is possible?
   *
   * If this method returns CEG_UNHANDLED, then we prohibit cegqi for terms
   * involving this kind. If this method returns CEG_HANDLED, our approaches
   * for cegqi fully handle the kind.
   *
   * This typically corresponds to kinds that correspond to operators that
   * have total interpretations and are a part of the signature of
   * satisfaction complete theories (see Reynolds et al., CAV 2015).
   */
  static CegHandledStatus isCbqiKind(Kind k);
  /** is cbqi term?
   *
   * This method returns whether the term is handled by cegqi techniques, i.e.
   * whether all subterms of n have kinds that can be handled by cegqi.
   */
  static CegHandledStatus isCbqiTerm(Node n);
  /** is cbqi sort?
   *
   * This method returns whether the type tn is handled by cegqi techniques.
   * If the result is CEG_HANDLED_UNCONDITIONAL, then this indicates that a
   * variable of this type is handled regardless of the formula it appears in.
   *
   * The argument qe is used if handling sort tn is conditional on the
   * strategies initialized in qe. For example, uninterpreted sorts are
   * handled if dedicated support for EPR is enabled.
   */
  static CegHandledStatus isCbqiSort(TypeNode tn,
                                     QuantifiersEngine* qe = nullptr);
  /** is cbqi quantifier prefix
   *
   * This returns the minimum value of the above method for a bound variable
   * in the prefix of quantified formula q.
   */
  static CegHandledStatus isCbqiQuantPrefix(Node q,
                                            QuantifiersEngine* qe = nullptr);
  /** is cbqi quantified formula
   *
   * This returns whether quantified formula q can and should be handled by
   * counterexample-guided instantiation. If this function returns
   * a status CEG_HANDLED or above, then q is fully handled by counterexample
   * guided quantifier instantiation and need not be processed by any other
   * strategy for quantifiers (e.g. E-matching). Otherwise, if this function
   * returns CEG_PARTIALLY_HANDLED, then it may be worthwhile to handle the
   * quantified formula using cegqi, however other strategies should also be
   * tried.
   */
  static CegHandledStatus isCbqiQuant(Node q, QuantifiersEngine* qe = nullptr);
  //------------------------------------ end static queries
 private:
  /** The quantified formula of this instantiator */
  Node d_quant;
  /** The parent of this instantiator */
  InstStrategyCegqi* d_parent;
  /** quantified formula associated with this instantiator */
  QuantifiersEngine* d_qe;

  //-------------------------------globally cached
  /** cache from nodes to the set of variables it contains
    * (from the quantified formula we are instantiating).
    */
  std::unordered_map<Node,
                     std::unordered_set<Node, NodeHashFunction>,
                     NodeHashFunction>
      d_prog_var;
  /** cache of the set of terms that we have established are
   * ineligible for instantiation.
    */
  std::unordered_set<Node, NodeHashFunction> d_inelig;
  /** ensures n is in d_prog_var and d_inelig. */
  void computeProgVars(Node n);
  //-------------------------------end globally cached

  //-------------------------------cached per round
  /** current assertions per theory */
  std::map<TheoryId, std::vector<Node> > d_curr_asserts;
  /** map from representatives to the terms in their equivalence class */
  std::map<Node, std::vector<Node> > d_curr_eqc;
  /** map from types to representatives of that type */
  std::map<TypeNode, std::vector<Node> > d_curr_type_eqc;
  /** solved asserts */
  std::unordered_set<Node, NodeHashFunction> d_solved_asserts;
  /** process assertions
   * This is called once at the beginning of check to
   * set up all necessary information for constructing instantiations,
   * such as the above data structures.
   */
  void processAssertions();
  /** cache bound variables for type returned
   * by getBoundVariable(...).
   */
  std::unordered_map<TypeNode, std::vector<Node>, TypeNodeHashFunction>
      d_bound_var;
  /** current index of bound variables for type.
   * The next call to getBoundVariable(...) for
   * type tn returns the d_bound_var_index[tn]^th
   * element of d_bound_var[tn], or a fresh variable
   * if not in bounds.
   */
  std::unordered_map<TypeNode, unsigned, TypeNodeHashFunction>
      d_bound_var_index;
  //-------------------------------end cached per round

  //-------------------------------data per theory
  /** relevant theory ids
   * A list of theory ids that contain at least one
   * constraint in the body of the quantified formula we
   * are processing.
   */
  std::vector<TheoryId> d_tids;
  /** map from theory ids to instantiator preprocessors */
  std::map<TheoryId, InstantiatorPreprocess*> d_tipp;
  /** registers all theory ids associated with type tn
   *
   * This recursively calls registerTheoryId for typeOf(tn') for
   * all parameters and datatype subfields of type tn.
   * visited stores the types we have already visited.
   */
  void registerTheoryIds(TypeNode tn, std::map<TypeNode, bool>& visited);
  /** register theory id tid
   *
   * This is called when the quantified formula we are processing
   * with this class involves theory tid. In this case, we will
   * construct instantiations based on the assertion list of this theory.
   */
  void registerTheoryId(TheoryId tid);
  //-------------------------------end data per theory

  //-------------------------------the variables
  /** the variables we are instantiating
   *
   * This is a superset of the variables for the instantiations we are
   * generating and sending on the output channel of this class.
   */
  std::vector<Node> d_vars;
  /** set form of d_vars */
  std::unordered_set<Node, NodeHashFunction> d_vars_set;
  /** index of variables reported in instantiation */
  std::vector<unsigned> d_var_order_index;
  /** number of input variables
   *
   * These are the variables, in order, for the instantiations we are generating
   * and sending on the output channel of this class.
   */
  std::vector<Node> d_input_vars;
  /** register variable */
  void registerVariable(Node v);
  //-------------------------------the variables

  //-------------------------------quantified formula info
  /** are we processing a nested quantified formula? */
  bool d_is_nested_quant;
  /** the atoms of the CE lemma */
  std::vector<Node> d_ce_atoms;
  /** collect atoms */
  void collectCeAtoms(Node n, std::map<Node, bool>& visited);
  //-------------------------------end quantified formula info

  //-------------------------------current state
  /** the current effort level of the instantiator
   * This indicates the effort Instantiator objects
   * will put into the terms they return.
   */
  CegInstEffort d_effort;
  /** for each variable, the instantiator used for that variable */
  std::map<Node, Instantiator*> d_active_instantiators;
  /** map from variables to the index in the prefix of the quantified
   * formula we are processing.
   */
  std::map<Node, unsigned> d_curr_index;
  /** map from variables to the phase in which we instantiated them */
  std::map<Node, CegInstPhase> d_curr_iphase;
  /** cache of current substitutions tried between activate/deactivate */
  std::map<Node, std::map<Node, std::map<Node, bool> > > d_curr_subs_proc;
  /** stack of temporary variables we are solving for,
   * e.g. subfields of datatypes.
   */
  std::vector<Node> d_stack_vars;
  /** activate instantiation variable v at index
   *
   * This is called when variable (inst constant) v is activated
   * for the quantified formula we are processing.
   * This method initializes the instantiator class for
   * that variable if necessary, where this class is
   * determined by the type of v. It also initializes
   * the cache of values we have tried substituting for v
   * (in d_curr_subs_proc), and stores its index.
   */
  void activateInstantiationVariable(Node v, unsigned index);
  /** deactivate instantiation variable
   *
   * This is called when variable (inst constant) v is deactivated
   * for the quantified formula we are processing.
   */
  void deactivateInstantiationVariable(Node v);
  /**
   * Have we tried an instantiation for v after the last call to
   * activateInstantiationVariable.
   */
  bool hasTriedInstantiation(Node v);
  //-------------------------------end current state

  //---------------------------------for applying substitutions
  /** can use basic substitution */
  bool canApplyBasicSubstitution( Node n, std::vector< Node >& non_basic );
  /** apply substitution
  * We wish to process the substitution: 
  *   ( pv = n * sf )
  * where pv is a variable with type tn, and * denotes application of substitution.
  * The return value "ret" and pv_prop is such that the above equality is equivalent to
  *   ( pv_prop.getModifiedTerm(pv) = ret )
  */
  Node applySubstitution( TypeNode tn, Node n, SolvedForm& sf, TermProperties& pv_prop, bool try_coeff = true ) {
    return applySubstitution( tn, n, sf.d_vars, sf.d_subs, sf.d_props, sf.d_non_basic, pv_prop, try_coeff );
  }
  /** apply substitution, with solved form expanded to subs/prop/non_basic/vars */
  Node applySubstitution( TypeNode tn, Node n, std::vector< Node >& vars, std::vector< Node >& subs, std::vector< TermProperties >& prop, 
                          std::vector< Node >& non_basic, TermProperties& pv_prop, bool try_coeff = true );
  /** apply substitution to literal lit 
  * The return value is equivalent to ( lit * sf )
  * where * denotes application of substitution.
  */
  Node applySubstitutionToLiteral( Node lit, SolvedForm& sf ) {
    return applySubstitutionToLiteral( lit, sf.d_vars, sf.d_subs, sf.d_props, sf.d_non_basic );
  }
  /** apply substitution to literal lit, with solved form expanded to subs/prop/non_basic/vars */
  Node applySubstitutionToLiteral( Node lit, std::vector< Node >& vars, std::vector< Node >& subs, std::vector< TermProperties >& prop, 
                                   std::vector< Node >& non_basic );
  //---------------------------------end for applying substitutions

  /** map from variables to their instantiators */
  std::map<Node, Instantiator*> d_instantiator;

  /** construct instantiation
   *
   * This method attempts to find a term for the i^th variable in d_vars to
   * include in the current instantiation, given by sf.
   *
   * It returns true if a successful call to the output channel's
   * doAddInstantiation was made.
   */
  bool constructInstantiation(SolvedForm& sf, unsigned i);
  /** construct instantiation
   *
   * Helper method for the above method. This method attempts to find a term for
   * variable pv to include in the current instantiation, given by sf based
   * on equality and theory-specific instantiation techniques. The latter is
   * managed by the instantiator object vinst. Prior to calling this method,
   * the variable pv has been activated by a call to
   * activateInstantiationVariable.
   */
  bool constructInstantiation(SolvedForm& sf, Instantiator* vinst, Node pv);
  /** do add instantiation
   * This method is called by the above function after we finalize the
   * variables/substitution and auxiliary lemmas.
   * It returns true if a successful call to the output channel's
   * doAddInstantiation was made.
   */
  bool doAddInstantiation(std::vector<Node>& vars,
                          std::vector<Node>& subs,
                          std::vector<Node>& lemmas);

  //------------------------------------ static queries
  /** is cbqi sort
   *
   * Helper function for isCbqiSort. This function recurses over the structure
   * of the type tn, where visited stores the types we have visited.
   */
  static CegHandledStatus isCbqiSort(
      TypeNode tn,
      std::map<TypeNode, CegHandledStatus>& visited,
      QuantifiersEngine* qe);
  //------------------------------------ end  static queries
};

/** Instantiator class
 *
 * This is a virtual class that is used for methods for constructing
 * substitutions for individual variables in counterexample-guided
 * instantiation techniques.
 *
 * This class contains a set of interface functions below, which are called
 * based on a fixed instantiation method implemented by CegInstantiator.
 * In these calls, the Instantiator in turn makes calls to methods in
 * CegInstanatior (primarily constructInstantiationInc).
 */
class Instantiator {
public:
 Instantiator(TypeNode tn);
 virtual ~Instantiator() {}
 /** reset
  * This is called once, prior to any of the below methods are called.
  * This function sets up any initial information necessary for constructing
  * instantiations for pv based on the current context.
  */
 virtual void reset(CegInstantiator* ci,
                    SolvedForm& sf,
                    Node pv,
                    CegInstEffort effort)
 {
 }

  /** has process equal term
   *
   * Whether this instantiator implements processEqualTerm and
   * processEqualTerms.
   */
  virtual bool hasProcessEqualTerm(CegInstantiator* ci,
                                   SolvedForm& sf,
                                   Node pv,
                                   CegInstEffort effort)
  {
    return false;
  }
  /** process equal term
   *
   * This method is called when the entailment:
   *   E |= pv_prop.getModifiedTerm(pv) = n
   * holds in the current context E, and n is eligible for instantiation.
   *
   * Returns true if an instantiation was successfully added via a call to
   * CegInstantiator::constructInstantiationInc.
   */
  virtual bool processEqualTerm(CegInstantiator* ci,
                                SolvedForm& sf,
                                Node pv,
                                TermProperties& pv_prop,
                                Node n,
                                CegInstEffort effort);
  /** process equal terms
   *
   * This method is called after process equal term, where eqc is the list of
   * eligible terms in the equivalence class of pv.
   *
   * Returns true if an instantiation was successfully added via a call to
   * CegInstantiator::constructInstantiationInc.
   */
  virtual bool processEqualTerms(CegInstantiator* ci,
                                 SolvedForm& sf,
                                 Node pv,
                                 std::vector<Node>& eqc,
                                 CegInstEffort effort)
  {
    return false;
  }

  /** whether the instantiator implements processEquality */
  virtual bool hasProcessEquality(CegInstantiator* ci,
                                  SolvedForm& sf,
                                  Node pv,
                                  CegInstEffort effort)
  {
    return false;
  }
  /** process equality
   *  The input is such that term_props.size() = terms.size() = 2
   *  This method is called when the entailment:
   *    E ^ term_props[0].getModifiedTerm(x0) =
   *    terms[0] ^ term_props[1].getModifiedTerm(x1) = terms[1] |= x0 = x1
   *  holds in current context E for fresh variables xi, terms[i] are eligible,
   *  and at least one terms[i] contains pv for i = 0,1.
   *  Notice in the basic case, E |= terms[0] = terms[1].
   *
   *  Returns true if an instantiation was successfully added via a call to
   *  CegInstantiator::constructInstantiationInc.
   */
  virtual bool processEquality(CegInstantiator* ci,
                               SolvedForm& sf,
                               Node pv,
                               std::vector<TermProperties>& term_props,
                               std::vector<Node>& terms,
                               CegInstEffort effort)
  {
    return false;
  }

  /** whether the instantiator implements processAssertion for any literal */
  virtual bool hasProcessAssertion(CegInstantiator* ci,
                                   SolvedForm& sf,
                                   Node pv,
                                   CegInstEffort effort)
  {
    return false;
  }
  /** has process assertion
  *
  * This method is called when the entailment:
  *   E |= lit
  * holds in current context E. Typically, lit belongs to the list of current
  * assertions.
  *
  * This method is used to determine whether the instantiator implements
  * processAssertion for literal lit.
  *   If this method returns null, then this intantiator does not handle the
  *   literal lit. Otherwise, this method returns a literal lit' such that:
  *   (1) lit' is true in the current model,
  *   (2) lit' implies lit.
  *   where typically lit' = lit.
  */
  virtual Node hasProcessAssertion(CegInstantiator* ci,
                                   SolvedForm& sf,
                                   Node pv,
                                   Node lit,
                                   CegInstEffort effort)
  {
    return Node::null();
  }
  /** process assertion
   * This method processes the assertion slit for variable pv.
   * lit : the substituted form (under sf) of a literal returned by
   *       hasProcessAssertion
   * alit : the asserted literal, given as input to hasProcessAssertion
   *
   *  Returns true if an instantiation was successfully added via a call to
   *  CegInstantiator::constructInstantiationInc.
   */
  virtual bool processAssertion(CegInstantiator* ci,
                                SolvedForm& sf,
                                Node pv,
                                Node lit,
                                Node alit,
                                CegInstEffort effort)
  {
    return false;
  }
  /** process assertions
   *
   * Called after processAssertion is called for each literal asserted to the
   * instantiator.
   *
   * Returns true if an instantiation was successfully added via a call to
   * CegInstantiator::constructInstantiationInc.
   */
  virtual bool processAssertions(CegInstantiator* ci,
                                 SolvedForm& sf,
                                 Node pv,
                                 CegInstEffort effort)
  {
    return false;
  }

  /** do we use the model value as instantiation for pv?
   * This method returns true if we use model value instantiations
   * at the same effort level as those determined by this instantiator.
   */
  virtual bool useModelValue(CegInstantiator* ci,
                             SolvedForm& sf,
                             Node pv,
                             CegInstEffort effort)
  {
    return effort > CEG_INST_EFFORT_STANDARD;
  }
  /** do we allow the model value as instantiation for pv? */
  virtual bool allowModelValue(CegInstantiator* ci,
                               SolvedForm& sf,
                               Node pv,
                               CegInstEffort effort)
  {
    return d_closed_enum_type;
  }

  /** do we need to postprocess the solved form for pv? */
  virtual bool needsPostProcessInstantiationForVariable(CegInstantiator* ci,
                                                        SolvedForm& sf,
                                                        Node pv,
                                                        CegInstEffort effort)
  {
    return false;
  }
  /** postprocess the solved form for pv
   *
   * This method returns true if we successfully postprocessed the solved form.
   * lemmas is a set of lemmas we wish to return along with the instantiation.
   */
  virtual bool postProcessInstantiationForVariable(CegInstantiator* ci,
                                                   SolvedForm& sf,
                                                   Node pv,
                                                   CegInstEffort effort,
                                                   std::vector<Node>& lemmas)
  {
    return true;
  }

  /** Identify this module (for debugging) */
  virtual std::string identify() const { return "Default"; }
 protected:
  /** the type of the variable we are instantiating */
  TypeNode d_type;
  /** whether d_type is a closed enumerable type */
  bool d_closed_enum_type;
};

class ModelValueInstantiator : public Instantiator {
public:
 ModelValueInstantiator(TypeNode tn) : Instantiator(tn) {}
 virtual ~ModelValueInstantiator() {}
 bool useModelValue(CegInstantiator* ci,
                    SolvedForm& sf,
                    Node pv,
                    CegInstEffort effort) override
 {
   return true;
 }
  std::string identify() const override { return "ModelValue"; }
};

/** instantiator preprocess
 *
 * This class implements techniques for preprocessing the counterexample lemma
 * generated for counterexample-guided quantifier instantiation.
 */
class InstantiatorPreprocess
{
 public:
  InstantiatorPreprocess() {}
  virtual ~InstantiatorPreprocess() {}
  /** register counterexample lemma
   * This implements theory-specific preprocessing and registration
   * of counterexample lemmas, with the same contract as
   * CegInstantiation::registerCounterexampleLemma.
   */
  virtual void registerCounterexampleLemma(Node lem,
                                           std::vector<Node>& ceVars,
                                           std::vector<Node>& auxLems)
  {
  }
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif
