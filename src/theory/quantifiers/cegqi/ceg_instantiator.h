/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Counterexample-guided quantifier instantiation.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CEG_INSTANTIATOR_H
#define CVC5__THEORY__QUANTIFIERS__CEG_INSTANTIATOR_H

#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/inference_id.h"
#include "util/statistics_stats.h"
#include "theory/quantifiers/cegqi/ceg_utils.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class Instantiator;
class InstantiatorPreprocess;
class InstStrategyCegqi;
class QuantifiersState;
class QuantifiersInferenceManager;
class QuantifiersRegistry;
class TermRegistry;

/** Ceg instantiator
 *
 * This class manages counterexample-guided quantifier instantiation
 * for a single quantified formula.
 *
 * For details on counterexample-guided quantifier instantiation
 * (for linear arithmetic), see Reynolds/King/Kuncak FMSD 2017.
 */
class CegInstantiator : protected EnvObj
{
 public:
  /**
   * The instantiator will be constructing instantiations for quantified formula
   * q, parent is the owner of this object.
   */
  CegInstantiator(Env& env,
                  Node q,
                  QuantifiersState& qs,
                  QuantifiersInferenceManager& qim,
                  QuantifiersRegistry& qr,
                  TermRegistry& tr);
  virtual ~CegInstantiator();
  /** check
   * This adds instantiations based on the state of d_vars in current context
   * on the output channel d_out of this class.
   */
  bool check();
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
   * Instantiate::addInstantiation(...)
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
   */
  static CegHandledStatus isCbqiSort(TypeNode tn);
  /** is cbqi quantifier prefix
   *
   * This returns the minimum value of the above method for a bound variable
   * in the prefix of quantified formula q.
   */
  static CegHandledStatus isCbqiQuantPrefix(Node q);
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
   *
   * @param cegqiAll Whether we apply CEQGI to all quantifiers (option
   * options::cegqiAll).
   */
  static CegHandledStatus isCbqiQuant(Node q, bool cegqiAll);
  //------------------------------------ end static queries
 private:
  /** The quantified formula of this instantiator */
  Node d_quant;
  /** Reference to the quantifiers state */
  QuantifiersState& d_qstate;
  /** Reference to the quantifiers inference manager */
  QuantifiersInferenceManager& d_qim;
  /** Reference to the quantifiers registry */
  QuantifiersRegistry& d_qreg;
  /** Reference to the term registry */
  TermRegistry& d_treg;
  /** The parent of this instantiator */
  InstStrategyCegqi* d_parent;

  //-------------------------------globally cached
  /** cache from nodes to the set of variables it contains
    * (from the quantified formula we are instantiating).
    */
  std::unordered_map<Node, std::unordered_set<Node>> d_prog_var;
  /** cache of the set of terms that we have established are
   * ineligible for instantiation.
    */
  std::unordered_set<Node> d_inelig;
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
  std::unordered_set<Node> d_solved_asserts;
  /** process assertions
   * This is called once at the beginning of check to
   * set up all necessary information for constructing instantiations,
   * such as the above data structures.
   */
  void processAssertions();
  /** cache bound variables for type returned
   * by getBoundVariable(...).
   */
  std::unordered_map<TypeNode, std::vector<Node>> d_bound_var;
  /** current index of bound variables for type.
   * The next call to getBoundVariable(...) for
   * type tn returns the d_bound_var_index[tn]^th
   * element of d_bound_var[tn], or a fresh variable
   * if not in bounds.
   */
  std::unordered_map<TypeNode, unsigned> d_bound_var_index;
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
  std::unordered_set<Node> d_vars_set;
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
  /** collect atoms in n, store in d_ce_atoms */
  void collectCeAtoms(Node n);
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
  bool doAddInstantiation(std::vector<Node>& vars, std::vector<Node>& subs);

  //------------------------------------ static queries
  /** is cbqi sort
   *
   * Helper function for isCbqiSort. This function recurses over the structure
   * of the type tn, where visited stores the types we have visited.
   */
  static CegHandledStatus isCbqiSort(
      TypeNode tn, std::map<TypeNode, CegHandledStatus>& visited);
  //------------------------------------ end  static queries
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
