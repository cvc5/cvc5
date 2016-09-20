/*********************                                                        */
/*! \file ceg_t_instantiator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
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
  bool processEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& term_coeffs, std::vector< Node >& terms, unsigned effort );
  bool hasProcessAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return true; }
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
  bool processEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& term_coeffs, std::vector< Node >& terms, unsigned effort );
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
  bool processEqualTerm( CegInstantiator * ci, SolvedForm& sf, Node pv, Node pv_coeff, Node n, unsigned effort );
  bool processEqualTerms( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& eqc, unsigned effort );
  std::string identify() const { return "Epr"; }
};

class BvInstantiator : public Instantiator {
public:
  BvInstantiator( QuantifiersEngine * qe, TypeNode tn ) : Instantiator( qe, tn ){}
  virtual ~BvInstantiator(){}
  bool processAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, Node lit, unsigned effort );
  bool useModelValue( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) { return true; }
  std::string identify() const { return "Bv"; }
};


}
}
}

#endif
