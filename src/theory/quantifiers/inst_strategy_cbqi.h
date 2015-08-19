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
 ** \brief instantiator_arith_instantiator
 **/


#include "cvc4_private.h"

#ifndef __CVC4__INST_STRATEGT_CBQI_H
#define __CVC4__INST_STRATEGT_CBQI_H

#include "theory/quantifiers/instantiation_engine.h"
#include "theory/arith/arithvar.h"

#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {

namespace arith {
  class TheoryArith;
}

namespace datatypes {
  class TheoryDatatypes;
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
  std::map< Node, Node > d_curr_rep;
  std::vector< Node > d_curr_arith_eqc;
private:
  //for adding instantiations during check
  void computeProgVars( Node n );
  // effort=0 : do not use model value, 1: use model value, 2: one must use model value
  bool addInstantiation( std::vector< Node >& subs, std::vector< Node >& vars,
                         std::vector< Node >& coeff, std::vector< Node >& has_coeff, Node theta,
                         unsigned i, unsigned effort );
  bool addInstantiationInc( Node n, Node pv, Node pv_coeff, std::vector< Node >& subs, std::vector< Node >& vars,
                            std::vector< Node >& coeff, std::vector< Node >& has_coeff, Node theta, unsigned i, unsigned effort );
  bool addInstantiationCoeff( std::vector< Node >& subs, std::vector< Node >& vars,
                              std::vector< Node >& coeff, std::vector< Node >& has_coeff,
                              unsigned j );
  bool addInstantiation( std::vector< Node >& subs, std::vector< Node >& vars );
  Node applySubstitution( Node n, std::vector< Node >& subs, std::vector< Node >& vars,
                          std::vector< Node >& coeff, std::vector< Node >& has_coeff, Node& pv_coeff, bool try_coeff = true );
  Node getModelBasedProjectionValue( Node t, bool strict, bool isLower, Node c, Node me, Node mt, Node theta );
  void processAssertions();
  void addToAuxVarSubstitution( std::vector< Node >& subs_lhs, std::vector< Node >& subs_rhs, Node l, Node r );
public:
  CegInstantiator( QuantifiersEngine * qe, CegqiOutput * out, bool use_vts_delta = true, bool use_vts_inf = true );
  //the CE variables
  std::vector< Node > d_vars;
  //auxiliary variables
  std::vector< Node > d_aux_vars;
  //check : add instantiations based on valuation of d_vars
  bool check();
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
  std::map< Node, std::vector< Node > > d_aux_variables;
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
  
  //set auxiliary variables
  void setAuxiliaryVariables( Node q, std::vector< Node >& vars );
};

}
}
}

#endif
