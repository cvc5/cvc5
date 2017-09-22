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
  Node getCacheNode() const { return d_coeff; }
  // is non-basic 
  bool isBasic() const { return d_coeff.isNull(); }
  // get modified term 
  Node getModifiedTerm( Node pv ) const {
    if( !d_coeff.isNull() ){
      return NodeManager::currentNM()->mkNode( kind::MULT, d_coeff, pv );
    }else{
      return pv;
    }
  }
  // combine property 
  void combineProperty( TermProperties& p ){
    if( !p.d_coeff.isNull() ){
      if( d_coeff.isNull() ){
        d_coeff = p.d_coeff;
      }else{
        d_coeff = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::MULT, d_coeff, p.d_coeff ) );
      }
    }
  }
};

//solved form, involves substitution with coefficients
class SolvedForm {
public:
  // list of variables
  std::vector< Node > d_vars;
  // list of terms that they are substituted to
  std::vector< Node > d_subs;
  // properties for each variable
  std::vector< TermProperties > d_props;
  // the variables that have non-basic information regarding how they are substituted
  //   an example is for linear arithmetic, we store "substitution with coefficients" such that 
  //   ( c * v ) -> s, where c is a positive integer constant.
  std::vector< Node > d_non_basic;
  // the current theta value (for LIA, see Section 4 of Reynolds/King/Kuncak FMSD 2017)
  Node d_theta;
  void copy( SolvedForm& sf ){
    d_vars.insert( d_vars.end(), sf.d_vars.begin(), sf.d_vars.end() );
    d_subs.insert( d_subs.end(), sf.d_subs.begin(), sf.d_subs.end() );
    d_props.insert( d_props.end(), sf.d_props.begin(), sf.d_props.end() );
    d_non_basic.insert( d_non_basic.end(), sf.d_non_basic.begin(), sf.d_non_basic.end() );
    d_theta = sf.d_theta;
  }
  void push_back( Node pv, Node n, TermProperties& pv_prop ){
    d_vars.push_back( pv );
    d_subs.push_back( n );
    d_props.push_back( pv_prop );
    if( !pv_prop.isBasic() ){
      d_non_basic.push_back( pv );
    }
  }
  void pop_back( Node pv, Node n, TermProperties& pv_prop ){
    d_vars.pop_back();
    d_subs.pop_back();
    d_props.pop_back();
    if( !pv_prop.isBasic() ){
      d_non_basic.pop_back();
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
  bool doAddInstantiation( std::vector< Node >& subs, std::vector< Node >& vars );
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
  bool doAddInstantiationInc( Node pv, Node n, TermProperties& pv_prop, SolvedForm& sf, unsigned effort );
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
  // whether the instantiator implements processAssertion for literal lit
  virtual bool hasProcessAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, Node lit, unsigned effort ) { return false; }
  // Called when the entailment:
  //   E |= lit 
  // holds in current context E. Typically, lit belongs to the list of current assertions.
  // Returns true if an instantiation was successfully added via a recursive call
  virtual bool processAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, Node lit, unsigned effort ) { return false; }
  // Called after processAssertion is called for each literal asserted to the instantiator.
  virtual bool processAssertions( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& lits, unsigned effort ) { return false; }

  //do we use the model value as instantiation for pv
  virtual bool useModelValue( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return false; }
  //do we allow the model value as instantiation for pv
  virtual bool allowModelValue( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return d_closed_enum_type; }

  //do we need to postprocess the solved form? did we successfully postprocess
  virtual bool needsPostProcessInstantiation( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return false; }
  virtual bool postProcessInstantiation( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return true; }

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
