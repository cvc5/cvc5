/*********************                                                        */
/*! \file ceg_instantiator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief counterexample-guided quantifier instantiation
 **/


#include "cvc4_private.h"

#ifndef __CVC4__CEG_INSTANTIATOR_H
#define __CVC4__CEG_INSTANTIATOR_H

#include "theory/quantifiers_engine.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {

namespace arith {
  class TheoryArith;
}

namespace quantifiers {

class CegqiOutput {
public:
  virtual ~CegqiOutput() {}
  virtual bool doAddInstantiation( std::vector< Node >& subs ) = 0;
  virtual bool isEligibleForInstantiation( Node n ) = 0;
  virtual bool addLemma( Node lem ) = 0;
};

class Instantiator;

//stores properties for a variable to solve for in CEGQI
//  For LIA, this includes the coefficient of the variable, and the bound type for the variable
class TermProperties {
public:
  TermProperties() : d_type(0) {}
  // type of property for a term
  //  for arithmetic this corresponds to bound type (0:equal, 1:upper bound, -1:lower bound)
  int d_type;
  // for arithmetic
  Node d_coeff;
  // get cache node 
  // we consider terms + TermProperties that are unique up to their cache node (see doAddInstantiationInc)
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
  virtual void composeProperty( TermProperties& p ){
    if( !p.d_coeff.isNull() ){
      if( d_coeff.isNull() ){
        d_coeff = p.d_coeff;
      }else{
        d_coeff = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::MULT, d_coeff, p.d_coeff ) );
      }
    }
  }
};

//Solved form
//  This specifies a substitution:
//  { d_props[i].getModifiedTerm(d_vars[i]) -> d_subs[i] | i = 0...|d_vars| }
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
  std::vector< Node > d_non_basic;
  // push the substitution pv_prop.getModifiedTerm(pv) -> n
  void push_back( Node pv, Node n, TermProperties& pv_prop ){
    d_vars.push_back( pv );
    d_subs.push_back( n );
    d_props.push_back( pv_prop );
    if( !pv_prop.isBasic() ){
      d_non_basic.push_back( pv );
      // update theta value
      Node new_theta = getTheta();
      if( new_theta.isNull() ){
        new_theta = pv_prop.d_coeff;
      }else{
        new_theta = NodeManager::currentNM()->mkNode( kind::MULT, new_theta, pv_prop.d_coeff );
        new_theta = Rewriter::rewrite( new_theta );
      }
      d_theta.push_back( new_theta );
    }
  }
  // pop the substitution pv_prop.getModifiedTerm(pv) -> n
  void pop_back( Node pv, Node n, TermProperties& pv_prop ){
    d_vars.pop_back();
    d_subs.pop_back();
    d_props.pop_back();
    if( !pv_prop.isBasic() ){
      d_non_basic.pop_back();
      // update theta value
      d_theta.pop_back();
    }
  }
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

class CegInstantiator {
private:
  QuantifiersEngine * d_qe;
  CegqiOutput * d_out;
  bool d_use_vts_delta;
  bool d_use_vts_inf;
  //program variable contains cache
  std::map< Node, std::map< Node, bool > > d_prog_var;
  std::map< Node, bool > d_inelig;
  //current assertions
  std::map< TheoryId, std::vector< Node > > d_curr_asserts;
  std::map< Node, std::vector< Node > > d_curr_eqc;
  std::map< TypeNode, std::vector< Node > > d_curr_type_eqc;
  //auxiliary variables
  std::vector< Node > d_aux_vars;
  // relevant theory ids
  std::vector< TheoryId > d_tids;
  //literals to equalities for aux vars
  std::map< Node, std::map< Node, Node > > d_aux_eq;
  //the CE variables
  std::vector< Node > d_vars;
  //index of variables reported in instantiation
  std::vector< unsigned > d_var_order_index;
  //atoms of the CE lemma
  bool d_is_nested_quant;
  std::vector< Node > d_ce_atoms;
  //collect atoms
  void collectCeAtoms( Node n, std::map< Node, bool >& visited );
private:
  //map from variables to their instantiators
  std::map< Node, Instantiator * > d_instantiator;
  //cache of current substitutions tried between register/unregister
  std::map< Node, std::map< Node, std::map< Node, bool > > > d_curr_subs_proc;
  std::map< Node, unsigned > d_curr_index;
  //stack of temporary variables we are solving (e.g. subfields of datatypes)
  std::vector< Node > d_stack_vars;
  //used instantiators
  std::map< Node, Instantiator * > d_active_instantiators;
  //register variable
  void registerInstantiationVariable( Node v, unsigned index );
  void unregisterInstantiationVariable( Node v );
private:
  //for adding instantiations during check
  void computeProgVars( Node n );
  // effort=0 : do not use model value, 1: use model value, 2: one must use model value
  bool doAddInstantiation( SolvedForm& sf, unsigned i, unsigned effort );
  // called by the above function after we finalize the variables/substitution and auxiliary lemmas
  bool doAddInstantiation( std::vector< Node >& vars, std::vector< Node >& subs, std::vector< Node >& lemmas );
  //process
  void processAssertions();
  void addToAuxVarSubstitution( std::vector< Node >& subs_lhs, std::vector< Node >& subs_rhs, Node l, Node r );
private:
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
public:
  CegInstantiator( QuantifiersEngine * qe, CegqiOutput * out, bool use_vts_delta = true, bool use_vts_inf = true );
  virtual ~CegInstantiator();
  //check : add instantiations based on valuation of d_vars
  bool check();
  //presolve for quantified formula
  void presolve( Node q );
  //register the counterexample lemma (stored in lems), modify vector
  void registerCounterexampleLemma( std::vector< Node >& lems, std::vector< Node >& ce_vars );
  //output
  CegqiOutput * getOutput() { return d_out; }
  //get quantifiers engine
  QuantifiersEngine* getQuantifiersEngine() { return d_qe; }

//interface for instantiators
public:
  void pushStackVariable( Node v );
  void popStackVariable();
  /** do add instantiation increment
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
  bool doAddInstantiationInc(Node pv,
                             Node n,
                             TermProperties& pv_prop,
                             SolvedForm& sf,
                             unsigned effort,
                             bool revertOnSuccess = false);
  Node getModelValue( Node n );
public:
  unsigned getNumCEAtoms() { return d_ce_atoms.size(); }
  Node getCEAtom( unsigned i ) { return d_ce_atoms[i]; }
  // is eligible
  bool isEligible( Node n );
  // has variable
  bool hasVariable( Node n, Node pv );
  bool useVtsDelta() { return d_use_vts_delta; }
  bool useVtsInfinity() { return d_use_vts_inf; }
  bool hasNestedQuantification() { return d_is_nested_quant; }
};


// an instantiator for individual variables
//   will make calls into CegInstantiator::doAddInstantiationInc
class Instantiator {
protected:
  TypeNode d_type;
  bool d_closed_enum_type;
public:
  Instantiator( QuantifiersEngine * qe, TypeNode tn );
  virtual ~Instantiator(){}
  virtual void reset( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) {}

  //  Called when the entailment:
  //    E |= pv_prop.getModifiedTerm(pv) = n
  //  holds in the current context E, and n is eligible for instantiation.
  virtual bool processEqualTerm( CegInstantiator * ci, SolvedForm& sf, Node pv, TermProperties& pv_prop, Node n, unsigned effort );
  //  Called about process equal term, where eqc is the list of eligible terms in the equivalence class of pv
  virtual bool processEqualTerms( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& eqc, unsigned effort ) { return false; }

  // whether the instantiator implements processEquality
  virtual bool hasProcessEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return false; }
  //  term_props.size() = terms.size() = 2
  //  Called when the entailment:
  //    E ^ term_props[0].getModifiedTerm(x0) = terms[0] ^ term_props[1].getModifiedTerm(x1) = terms[1] |= x0 = x1
  //  holds in current context E for fresh variables xi, terms[i] are eligible, and at least one terms[i] contains pv for i = 0,1.
  //  Notice in the basic case, E |= terms[0] = terms[1].
  //  Returns true if an instantiation was successfully added via a recursive call
  virtual bool processEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< TermProperties >& term_props, std::vector< Node >& terms, unsigned effort ) { return false; }

  // whether the instantiator implements processAssertion for any literal
  virtual bool hasProcessAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return false; }
  /** has process assertion
  *
  * Called when the entailment:
  *   E |= lit
  * holds in current context E. Typically, lit belongs to the list of current
  * assertions.
  *
  * This function is used to determine whether the instantiator implements
  * processAssertion for literal lit.
  *   If this function returns null, then this intantiator does not handle the
  * literal lit
  *   Otherwise, this function returns a literal lit' with the properties:
  *   (1) lit' is true in the current model,
  *   (2) lit' implies lit.
  *   where typically lit' = lit.
  */
  virtual Node hasProcessAssertion(CegInstantiator* ci, SolvedForm& sf, Node pv,
                                   Node lit, unsigned effort) {
    return Node::null();
  }
  /** process assertion
  * Processes the assertion slit for variable pv
  *
  * lit is the substituted form (under sf) of a literal returned by
  * hasProcessAssertion
  * alit is the asserted literal, given as input to hasProcessAssertion
  *
  * Returns true if an instantiation was successfully added via a recursive call
  */
  virtual bool processAssertion(CegInstantiator* ci, SolvedForm& sf, Node pv,
                                Node lit, Node alit, unsigned effort) {
    return false;
  }
  /** process assertions
  * Called after processAssertion is called for each literal asserted to the
  * instantiator.
  */
  virtual bool processAssertions(CegInstantiator* ci, SolvedForm& sf, Node pv,
                                 unsigned effort) {
    return false;
  }

  //do we use the model value as instantiation for pv
  virtual bool useModelValue( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return false; }
  //do we allow the model value as instantiation for pv
  virtual bool allowModelValue( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return d_closed_enum_type; }

  //do we need to postprocess the solved form for pv?
  virtual bool needsPostProcessInstantiationForVariable( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return false; }
  //postprocess the solved form for pv, returns true if we successfully postprocessed, lemmas is a set of lemmas we wish to return along with the instantiation
  virtual bool postProcessInstantiationForVariable( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort, std::vector< Node >& lemmas ) { return true; }

  /** Identify this module (for debugging) */
  virtual std::string identify() const { return "Default"; }
};

class ModelValueInstantiator : public Instantiator {
public:
  ModelValueInstantiator( QuantifiersEngine * qe, TypeNode tn ) : Instantiator( qe, tn ){}
  virtual ~ModelValueInstantiator(){}
  bool useModelValue( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return true; }
  std::string identify() const { return "ModelValue"; }
};

}
}
}

#endif
