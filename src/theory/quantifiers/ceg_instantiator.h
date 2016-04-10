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

class CegInstantiator {
private:
  QuantifiersEngine * d_qe;
  CegqiOutput * d_out;
  //constants
  Node d_zero;
  Node d_one;
  Node d_true;
  bool d_use_vts_delta;
  bool d_use_vts_inf;
  Node d_vts_sym[2];
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
  /*
  class MbpBound {
  public:
    Node d_bound;
    Node d_coeff;
    Node d_vts_coeff[2];
    Node d_lit;
  };
  */
  // effort=0 : do not use model value, 1: use model value, 2: one must use model value
  bool doAddInstantiation( SolvedForm& sf, SolvedForm& ssf, std::vector< Node >& vars,
                         std::vector< int >& btyp, Node theta, unsigned i, unsigned effort,
                         std::map< Node, Node >& cons, std::vector< Node >& curr_var );
  bool doAddInstantiationInc( Node n, Node pv, Node pv_coeff, int bt, SolvedForm& sf, SolvedForm& ssf, std::vector< Node >& vars,
                            std::vector< int >& btyp, Node theta, unsigned i, unsigned effort,
                            std::map< Node, Node >& cons, std::vector< Node >& curr_var );
  bool doAddInstantiationCoeff( SolvedForm& sf,
                              std::vector< Node >& vars, std::vector< int >& btyp,
                              unsigned j, std::map< Node, Node >& cons );
  bool doAddInstantiation( std::vector< Node >& subs, std::vector< Node >& vars, std::map< Node, Node >& cons );
  Node constructInstantiation( Node n, std::map< Node, Node >& subs_map, std::map< Node, Node >& cons );
  Node applySubstitution( TypeNode tn, Node n, SolvedForm& sf, std::vector< Node >& vars, Node& pv_coeff, bool try_coeff = true ) {
    return applySubstitution( tn, n, sf.d_subs, sf.d_coeff, sf.d_has_coeff, vars, pv_coeff, try_coeff );
  }
  Node applySubstitution( TypeNode tn, Node n, std::vector< Node >& subs, std::vector< Node >& coeff, std::vector< Node >& has_coeff,
                          std::vector< Node >& vars, Node& pv_coeff, bool try_coeff = true );
  Node getModelBasedProjectionValue( Node e, Node t, bool isLower, Node c, Node me, Node mt, Node theta, Node inf_coeff, Node delta_coeff );
  void processAssertions();
  void addToAuxVarSubstitution( std::vector< Node >& subs_lhs, std::vector< Node >& subs_rhs, Node l, Node r );
  //get model value
  Node getModelValue( Node n );
private:
  int solve_arith( Node v, Node atom, Node & veq_c, Node & val, Node& vts_coeff_inf, Node& vts_coeff_delta );
  Node solve_dt( Node v, Node a, Node b, Node sa, Node sb );
public:
  CegInstantiator( QuantifiersEngine * qe, CegqiOutput * out, bool use_vts_delta = true, bool use_vts_inf = true );
  //check : add instantiations based on valuation of d_vars
  bool check();
  //presolve for quantified formula
  void presolve( Node q );
  //register the counterexample lemma (stored in lems), modify vector
  void registerCounterexampleLemma( std::vector< Node >& lems, std::vector< Node >& ce_vars );
};

}
}
}

#endif
