/*********************                                                        */
/*! \file inst_strategy_cbqi.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief counterexample-guided quantifier instantiation
 **/


#include "cvc4_private.h"

#ifndef __CVC4__INST_STRATEGY_CBQI_H
#define __CVC4__INST_STRATEGY_CBQI_H

#include "theory/arith/arithvar.h"
#include "theory/quantifiers/ceg_instantiator.h"
#include "theory/quantifiers/instantiation_engine.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {

namespace arith {
  class TheoryArith;
}

namespace quantifiers {

class InstStrategyCbqi : public QuantifiersModule {
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
protected:
  bool d_cbqi_set_quant_inactive;
  bool d_incomplete_check;
  /** whether we have added cbqi lemma */
  NodeSet d_added_cbqi_lemma;
  /** whether we have instantiated quantified formulas */
  //NodeSet d_added_inst;
  /** whether to do cbqi for this quantified formula */
  std::map< Node, bool > d_do_cbqi;
  /** register ce lemma */
  virtual void registerCounterexampleLemma( Node q, Node lem );
  /** has added cbqi lemma */
  bool hasAddedCbqiLemma( Node q ) { return d_added_cbqi_lemma.find( q )!=d_added_cbqi_lemma.end(); }
  /** helper functions */
  bool hasNonCbqiVariable( Node q );
  bool hasNonCbqiOperator( Node n, std::map< Node, bool >& visited );
  /** process functions */
  virtual void processResetInstantiationRound( Theory::Effort effort ) = 0;
  virtual void process( Node q, Theory::Effort effort, int e ) = 0;
public:
  InstStrategyCbqi( QuantifiersEngine * qe );
  ~InstStrategyCbqi() throw();
  /** whether to do CBQI for quantifier q */
  bool doCbqi( Node q );
  /** process functions */
  bool needsCheck( Theory::Effort e );
  unsigned needsModel( Theory::Effort e );
  void reset_round( Theory::Effort e );
  void check( Theory::Effort e, unsigned quant_e );
  bool checkComplete();
  void preRegisterQuantifier( Node q );
  void registerQuantifier( Node q );
  /** get next decision request */
  Node getNextDecisionRequest();
};


class InstStrategySimplex : public InstStrategyCbqi {
protected:
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
  void process( Node f, Theory::Effort effort, int e );
public:
  InstStrategySimplex( arith::TheoryArith* th, QuantifiersEngine* ie );
  ~InstStrategySimplex() throw() {}
  /** identify */
  std::string identify() const { return std::string("Simplex"); }
};


//generalized counterexample guided quantifier instantiation

class InstStrategyCegqi;

class CegqiOutputInstStrategy : public CegqiOutput {
public:
  CegqiOutputInstStrategy( InstStrategyCegqi * out ) : d_out( out ){}
  InstStrategyCegqi * d_out;
  bool doAddInstantiation( std::vector< Node >& subs );
  bool isEligibleForInstantiation( Node n );
  bool addLemma( Node lem );
};

class InstStrategyCegqi : public InstStrategyCbqi {
protected:
  CegqiOutputInstStrategy * d_out;
  std::map< Node, CegInstantiator * > d_cinst;
  Node d_small_const;
  Node d_curr_quant;
  bool d_check_vts_lemma_lc;
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  void process( Node f, Theory::Effort effort, int e );
  /** register ce lemma */
  void registerCounterexampleLemma( Node q, Node lem );
public:
  InstStrategyCegqi( QuantifiersEngine * qe );
  ~InstStrategyCegqi() throw();

  bool doAddInstantiation( std::vector< Node >& subs );
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
