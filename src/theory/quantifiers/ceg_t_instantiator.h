/*********************                                                        */
/*! \file ceg_t_instantiator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief theory-specific counterexample-guided quantifier instantiation
 **/


#include "cvc4_private.h"

#ifndef __CVC4__CEG_T_INSTANTIATOR_H
#define __CVC4__CEG_T_INSTANTIATOR_H

#include "theory/quantifiers/ceg_instantiator.h"

#include <unordered_set>

namespace CVC4 {
namespace theory {
namespace quantifiers {

class ArithInstantiator : public Instantiator {
private:
  Node d_vts_sym[2];
  std::vector< Node > d_mbp_bounds[2];
  std::vector< Node > d_mbp_coeff[2];
  std::vector< Node > d_mbp_vts_coeff[2][2];
  std::vector< Node > d_mbp_lit[2];
  int solve_arith( CegInstantiator * ci, Node v, Node atom, Node & veq_c, Node & val, Node& vts_coeff_inf, Node& vts_coeff_delta );
  Node getModelBasedProjectionValue( CegInstantiator * ci, Node e, Node t, bool isLower, Node c, Node me, Node mt, Node theta, Node inf_coeff, Node delta_coeff );
public:
  ArithInstantiator( QuantifiersEngine * qe, TypeNode tn ) : Instantiator( qe, tn ){}
  virtual ~ArithInstantiator(){}
  void reset( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort );
  bool hasProcessEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return true; }
  bool processEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< TermProperties >& term_props, std::vector< Node >& terms, unsigned effort );
  bool hasProcessAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return true; }
  bool hasProcessAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, Node lit, unsigned effort );
  bool processAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, Node lit, unsigned effort );
  bool processAssertions( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& lits, unsigned effort );
  bool needsPostProcessInstantiation( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort );
  bool postProcessInstantiation( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort );
  std::string identify() const { return "Arith"; }
};

class DtInstantiator : public Instantiator {
private:
  Node solve_dt( Node v, Node a, Node b, Node sa, Node sb );
public:
  DtInstantiator( QuantifiersEngine * qe, TypeNode tn ) : Instantiator( qe, tn ){}
  virtual ~DtInstantiator(){}
  void reset( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort );
  bool processEqualTerms( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& eqc, unsigned effort );
  bool hasProcessEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return true; }
  bool processEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< TermProperties >& term_props, std::vector< Node >& terms, unsigned effort );
  std::string identify() const { return "Dt"; }
};

class TermArgTrie;

class EprInstantiator : public Instantiator {
private:
  std::vector< Node > d_equal_terms;
  void computeMatchScore( CegInstantiator * ci, Node pv, Node catom, std::vector< Node >& arg_reps, TermArgTrie * tat, unsigned index, std::map< Node, int >& match_score );
  void computeMatchScore( CegInstantiator * ci, Node pv, Node catom, Node eqc, std::map< Node, int >& match_score );
public:
  EprInstantiator( QuantifiersEngine * qe, TypeNode tn ) : Instantiator( qe, tn ){}
  virtual ~EprInstantiator(){}
  void reset( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort );
  bool processEqualTerm( CegInstantiator * ci, SolvedForm& sf, Node pv, TermProperties& pv_prop, Node n, unsigned effort );
  bool processEqualTerms( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& eqc, unsigned effort );
  std::string identify() const { return "Epr"; }
};


// virtual class for model queries
class BvInverterModelQuery {
public:
  BvInverterModelQuery(){}
  virtual Node getModelValue( Node n ) = 0;
};

// class for storing information about the solved status
class BvInverterStatus {
public:
  BvInverterStatus() : d_status(0) {}
  int d_status;
  std::vector< Node > d_conds;
};

// inverter class
// TODO : move to theory/bv/ if generally useful?
class BvInverter {
private:
  std::map< TypeNode, Node > d_solve_var;
  Node getPathToPv( Node lit, Node pv, Node sv, std::vector< unsigned >& path, std::unordered_set< TNode, TNodeHashFunction >& visited );
public:
  // get dummy fresh variable of type tn, used as argument for sv 
  Node getSolveVariable( TypeNode tn );
  // Get path to pv in lit, replace that occurrence by sv and all others by pvs.
  // e.g. if return value R is non-null, then:
  //   lit.path = pv
  //   R.path = sv
  //   R.path' = pvs for all lit.path' = pv, where path' != path
  Node getPathToPv( Node lit, Node pv, Node sv, Node pvs, std::vector< unsigned >& path );
public:
  // solve for sv in constraint ( (pol ? _ : not) sv_t <rk> t ), where sv_t.path = sv
  // status accumulates side conditions
  Node solve_bv_constraint( Node sv, Node sv_t, Node t, Kind rk, bool pol, std::vector< unsigned >& path,
                            BvInverterModelQuery * m, BvInverterStatus& status );
  // solve for sv in lit, where lit.path = sv
  // status accumulates side conditions
  Node solve_bv_lit( Node sv, Node lit, bool pol, std::vector< unsigned >& path,
                     BvInverterModelQuery * m, BvInverterStatus& status );
};

class BvInstantiator : public Instantiator {
private:
  BvInverter d_inverter;
  unsigned d_inst_id_counter;
  std::map< Node, std::vector< unsigned > > d_var_to_inst_id;
  std::map< unsigned, Node > d_inst_id_to_term;
  std::map< unsigned, BvInverterStatus > d_inst_id_to_status;
private:
  void processLiteral( CegInstantiator * ci, SolvedForm& sf, Node pv, Node lit, unsigned effort );
public:
  BvInstantiator( QuantifiersEngine * qe, TypeNode tn ) : Instantiator( qe, tn ){}
  virtual ~BvInstantiator(){}
  void reset( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort );
  bool hasProcessEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return true; }
  bool processEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< TermProperties >& term_props, std::vector< Node >& terms, unsigned effort );
  bool hasProcessAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return true; }
  bool hasProcessAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, Node lit, unsigned effort );
  bool processAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, Node lit, unsigned effort );
  bool processAssertions( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& lits, unsigned effort );
  bool useModelValue( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return true; }
  std::string identify() const { return "Bv"; }
};


}
}
}

#endif
