/*********************                                                        */
/*! \file inst_strategy_cbqi.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief counterexample-guided quantifier instantiation
 **/


#include "cvc4_private.h"

#ifndef __CVC4__INST_STRATEGY_CBQI_H
#define __CVC4__INST_STRATEGY_CBQI_H

#include "theory/quantifiers/instantiation_engine.h"
#include "theory/arith/arithvar.h"

#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {

namespace arith {
  class TheoryArith;
}

namespace quantifiers {

class CegqiOutput
{
public:
  virtual ~CegqiOutput() {}
  virtual bool addInstantiation( std::vector< Node >& subs ) = 0;
  virtual bool isEligibleForInstantiation( Node n ) = 0;
  virtual bool addLemma( Node lem ) = 0;
};

class CegInstantiator
{
private:
  QuantifiersEngine * d_qe;
  CegqiOutput * d_out;
  //constants
  Node d_zero;
  Node d_one;
  Node d_true;
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
  //atoms of the CE lemma
  bool d_is_nested_quant;
  std::vector< Node > d_ce_atoms;
private:
  //collect atoms
  void collectCeAtoms( Node n, std::map< Node, bool >& visited );
  //for adding instantiations during check
  void computeProgVars( Node n );
  //solved form, involves substitution with coefficients
  class SolvedForm {
  public:
    std::vector< Node > d_subs;
    std::vector< Node > d_coeff;
    std::vector< Node > d_has_coeff;
    void copy( SolvedForm& sf ){
      d_subs.insert( d_subs.end(), sf.d_subs.begin(), sf.d_subs.end() );
      d_coeff.insert( d_coeff.end(), sf.d_coeff.begin(), sf.d_coeff.end() );
      d_has_coeff.insert( d_has_coeff.end(), sf.d_has_coeff.begin(), sf.d_has_coeff.end() );
    }
    void push_back( Node pv, Node n, Node pv_coeff ){
      d_subs.push_back( n );
      d_coeff.push_back( pv_coeff );
      if( !pv_coeff.isNull() ){
        d_has_coeff.push_back( pv );
      }
    }
    void pop_back( Node pv, Node n, Node pv_coeff ){
      d_subs.pop_back();
      d_coeff.pop_back();
      if( !pv_coeff.isNull() ){
        d_has_coeff.pop_back();
      }
    }
  };
  // effort=0 : do not use model value, 1: use model value, 2: one must use model value
  bool addInstantiation( SolvedForm& sf, SolvedForm& ssf, std::vector< Node >& vars,
                         std::vector< int >& btyp, Node theta, unsigned i, unsigned effort,
                         std::map< Node, Node >& cons, std::vector< Node >& curr_var );
  bool addInstantiationInc( Node n, Node pv, Node pv_coeff, int bt, SolvedForm& sf, SolvedForm& ssf, std::vector< Node >& vars,
                            std::vector< int >& btyp, Node theta, unsigned i, unsigned effort,
                            std::map< Node, Node >& cons, std::vector< Node >& curr_var );
  bool addInstantiationCoeff( SolvedForm& sf,
                              std::vector< Node >& vars, std::vector< int >& btyp,
                              unsigned j, std::map< Node, Node >& cons );
  bool addInstantiation( std::vector< Node >& subs, std::vector< Node >& vars, std::map< Node, Node >& cons );
  Node constructInstantiation( Node n, std::map< Node, Node >& subs_map, std::map< Node, Node >& cons );
  Node applySubstitution( Node n, SolvedForm& sf, std::vector< Node >& vars, Node& pv_coeff, bool try_coeff = true ) {
    return applySubstitution( n, sf.d_subs, sf.d_coeff, sf.d_has_coeff, vars, pv_coeff, try_coeff );
  }
  Node applySubstitution( Node n, std::vector< Node >& subs, std::vector< Node >& coeff, std::vector< Node >& has_coeff,
                          std::vector< Node >& vars, Node& pv_coeff, bool try_coeff = true );
  Node getModelBasedProjectionValue( Node t, bool isLower, Node c, Node me, Node mt, Node theta,
                                     Node inf_coeff, Node vts_inf, Node delta_coeff, Node vts_delta );
  void processAssertions();
  void addToAuxVarSubstitution( std::vector< Node >& subs_lhs, std::vector< Node >& subs_rhs, Node l, Node r );
public:
  CegInstantiator( QuantifiersEngine * qe, CegqiOutput * out, bool use_vts_delta = true, bool use_vts_inf = true );
  //check : add instantiations based on valuation of d_vars
  bool check();
  //presolve for quantified formula
  void presolve( Node q );
  //register the counterexample lemma (stored in lems), modify vector
  void registerCounterexampleLemma( std::vector< Node >& lems, std::vector< Node >& ce_vars );
};

class InstStrategySimplex : public InstStrategy{
private:
  /** reference to theory arithmetic */
  arith::TheoryArith* d_th;
  /** quantifiers we should process */
  std::map< Node, bool > d_quantActive;
  /** delta */
  std::map< TypeNode, Node > d_deltas;
  /** for each quantifier, simplex rows */
  std::map< Node, std::vector< arith::ArithVar > > d_instRows;
  /** tableaux */
  std::map< Node, std::map< arith::ArithVar, Node > > d_tableaux_term;
  std::map< Node, std::map< arith::ArithVar, std::map< Node, Node > > > d_tableaux_ce_term;
  std::map< Node, std::map< arith::ArithVar, std::map< Node, Node > > > d_tableaux;
  /** ce tableaux */
  std::map< Node, std::map< arith::ArithVar, std::map< Node, Node > > > d_ceTableaux;
  /** get value */
  //Node getTableauxValue( Node n, bool minus_delta = false );
  Node getTableauxValue( arith::ArithVar v, bool minus_delta = false );
  /** do instantiation */
  bool doInstantiation( Node f, Node ic, Node term, arith::ArithVar x, InstMatch& m, Node var );
  bool doInstantiation2( Node f, Node ic, Node term, arith::ArithVar x, InstMatch& m, Node var, bool minus_delta = false );
  /** add term to row */
  void addTermToRow( Node ic, arith::ArithVar x, Node n, NodeBuilder<>& t );
  /** print debug */
  void debugPrint( const char* c );
private:
  /** */
  int d_counter;
  /** constants */
  Node d_zero;
  Node d_negOne;
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e );
public:
  InstStrategySimplex( arith::TheoryArith* th, QuantifiersEngine* ie );
  ~InstStrategySimplex() throw() {}
  /** identify */
  std::string identify() const { return std::string("Simplex"); }
};


//generalized counterexample guided quantifier instantiation

class InstStrategyCegqi;

class CegqiOutputInstStrategy : public CegqiOutput
{
public:
  CegqiOutputInstStrategy( InstStrategyCegqi * out ) : d_out( out ){}
  InstStrategyCegqi * d_out;
  bool addInstantiation( std::vector< Node >& subs );
  bool isEligibleForInstantiation( Node n );
  bool addLemma( Node lem );
};

class InstStrategyCegqi : public InstStrategy {
private:
  CegqiOutputInstStrategy * d_out;
  std::map< Node, CegInstantiator * > d_cinst;
  Node d_small_const;
  Node d_curr_quant;
  bool d_check_vts_lemma_lc;
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e );
public:
  InstStrategyCegqi( QuantifiersEngine * qe );
  ~InstStrategyCegqi() throw() {}

  bool addInstantiation( std::vector< Node >& subs );
  bool isEligibleForInstantiation( Node n );
  bool addLemma( Node lem );
  /** identify */
  std::string identify() const { return std::string("Cegqi"); }

  //get instantiator for quantifier
  CegInstantiator * getInstantiator( Node q );
  //register quantifier
  void registerQuantifier( Node q );
  //presolve
  void presolve();
};

}
}
}

#endif
