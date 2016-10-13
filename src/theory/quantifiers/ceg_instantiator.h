/*********************                                                        */
/*! \file ceg_instantiator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
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


//solved form, involves substitution with coefficients
class SolvedForm {
public:
  std::vector< Node > d_vars;
  std::vector< Node > d_subs;
  std::vector< Node > d_coeff;
  std::vector< int > d_btyp;
  std::vector< Node > d_has_coeff;
  Node d_theta;
  void copy( SolvedForm& sf ){
    d_vars.insert( d_vars.end(), sf.d_vars.begin(), sf.d_vars.end() );
    d_subs.insert( d_subs.end(), sf.d_subs.begin(), sf.d_subs.end() );
    d_coeff.insert( d_coeff.end(), sf.d_coeff.begin(), sf.d_coeff.end() );
    d_btyp.insert( d_btyp.end(), sf.d_btyp.begin(), sf.d_btyp.end() );
    d_has_coeff.insert( d_has_coeff.end(), sf.d_has_coeff.begin(), sf.d_has_coeff.end() );
    d_theta = sf.d_theta;
  }
  void push_back( Node pv, Node n, Node pv_coeff, int bt ){
    d_vars.push_back( pv );
    d_subs.push_back( n );
    d_coeff.push_back( pv_coeff );
    d_btyp.push_back( bt );
    if( !pv_coeff.isNull() ){
      d_has_coeff.push_back( pv );
    }
  }
  void pop_back( Node pv, Node n, Node pv_coeff, int bt ){
    d_vars.pop_back();
    d_subs.pop_back();
    d_coeff.pop_back();
    d_btyp.pop_back();
    if( !pv_coeff.isNull() ){
      d_has_coeff.pop_back();
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
  bool doAddInstantiationInc( Node pv, Node n, Node pv_coeff, int bt, SolvedForm& sf, unsigned effort );
  Node getModelValue( Node n );
  // TODO: move to solved form?
  Node applySubstitution( TypeNode tn, Node n, SolvedForm& sf, Node& pv_coeff, bool try_coeff = true ) {
    return applySubstitution( tn, n, sf.d_subs, sf.d_coeff, sf.d_has_coeff, sf.d_vars, pv_coeff, try_coeff );
  }
  Node applySubstitution( TypeNode tn, Node n, std::vector< Node >& subs, std::vector< Node >& coeff, std::vector< Node >& has_coeff,
                          std::vector< Node >& vars, Node& pv_coeff, bool try_coeff = true );
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
  
  //called when pv_coeff * pv = n, and n is eligible for instantiation
  virtual bool processEqualTerm( CegInstantiator * ci, SolvedForm& sf, Node pv, Node pv_coeff, Node n, unsigned effort );
  //eqc is the equivalence class of pv
  virtual bool processEqualTerms( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& eqc, unsigned effort ) { return false; }
  
  //term_coeffs.size() = terms.size() = 2, called when term_coeff[0] * terms[0] = term_coeff[1] * terms[1], terms are eligible, and at least one of these terms contains pv
  virtual bool hasProcessEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return false; }
  virtual bool processEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& term_coeffs, std::vector< Node >& terms, unsigned effort ) { return false; }
  
  //called when assertion lit holds.  note that lit is unsubstituted, first must substitute/solve/check eligible
  virtual bool hasProcessAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return false; }
  virtual bool processAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, Node lit, unsigned effort ) { return false; }
  virtual bool processAssertions( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& lits, unsigned effort ) { return false; }
  
  //do we allow instantiation for the model value of pv
  virtual bool useModelValue( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return false; }
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
