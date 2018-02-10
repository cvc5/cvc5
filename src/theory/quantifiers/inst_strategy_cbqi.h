/*********************                                                        */
/*! \file inst_strategy_cbqi.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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
  typedef context::CDHashMap< Node, int, NodeHashFunction> NodeIntMap;

 protected:
  bool d_cbqi_set_quant_inactive;
  bool d_incomplete_check;
  /** whether we have added cbqi lemma */
  NodeSet d_added_cbqi_lemma;
  /** whether we have added cbqi lemma */
  NodeSet d_elim_quants;
  /** parent guards */
  std::map< Node, std::vector< Node > > d_parent_quant;
  std::map< Node, std::vector< Node > > d_children_quant;
  std::map< Node, bool > d_active_quant;
  /** whether we have instantiated quantified formulas */
  //NodeSet d_added_inst;
  /** whether to do cbqi for this quantified formula 0 : no, 2 : yes, 1 : yes but not exclusively, -1 : heuristically */
  std::map< Node, int > d_do_cbqi;
  /** register ce lemma */
  bool registerCbqiLemma( Node q );
  virtual void registerCounterexampleLemma( Node q, Node lem );
  /** has added cbqi lemma */
  bool hasAddedCbqiLemma( Node q ) { return d_added_cbqi_lemma.find( q )!=d_added_cbqi_lemma.end(); }
  /** helper functions */
  int hasNonCbqiVariable( Node q );
  bool hasNonCbqiOperator( Node n, std::map< Node, bool >& visited );
  int isCbqiSort( TypeNode tn, std::map< TypeNode, int >& visited );
  /** get next decision request with dependency checking */
  Node getNextDecisionRequestProc( Node q, std::map< Node, bool >& proc );  
  /** process functions */
  virtual void processResetInstantiationRound( Theory::Effort effort ) = 0;
  virtual void process( Node q, Theory::Effort effort, int e ) = 0;

 protected:
  //for identification
  uint64_t d_qid_count;
  //nested qe map
  std::map< Node, Node > d_nested_qe;
  //mark ids on quantifiers 
  Node getIdMarkedQuantNode( Node n, std::map< Node, Node >& visited );
  // id to ce quant
  std::map< Node, Node > d_id_to_ce_quant;
  std::map< Node, Node > d_ce_quant_to_id;
  //do nested quantifier elimination recursive
  Node doNestedQENode( Node q, Node ceq, Node n, std::vector< Node >& inst_terms, bool doVts );
  Node doNestedQERec( Node q, Node n, std::map< Node, Node >& visited, std::vector< Node >& inst_terms, bool doVts );
  //elimination information (for delayed elimination)
  class NestedQEInfo {
  public:
    NestedQEInfo() : d_doVts(false){}
    ~NestedQEInfo(){}
    Node d_q;
    std::vector< Node > d_inst_terms;
    bool d_doVts;
  };
  std::map< Node, NestedQEInfo > d_nested_qe_info;
  NodeIntMap d_nested_qe_waitlist_size;
  NodeIntMap d_nested_qe_waitlist_proc;
  std::map< Node, std::vector< Node > > d_nested_qe_waitlist;

 public:
  //do nested quantifier elimination
  Node doNestedQE( Node q, std::vector< Node >& inst_terms, Node lem, bool doVts );

 public:
  InstStrategyCbqi( QuantifiersEngine * qe );

  /** whether to do CBQI for quantifier q */
  bool doCbqi( Node q );
  /** process functions */
  bool needsCheck( Theory::Effort e );
  QEffort needsModel(Theory::Effort e);
  void reset_round( Theory::Effort e );
  void check(Theory::Effort e, QEffort quant_e);
  bool checkComplete();
  bool checkCompleteFor( Node q );
  void preRegisterQuantifier( Node q );
  void registerQuantifier( Node q );
  /** get next decision request */
  Node getNextDecisionRequest( unsigned& priority );
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
  void processResetInstantiationRound(Theory::Effort effort) override;
  void process(Node f, Theory::Effort effort, int e) override;
  /** register ce lemma */
  void registerCounterexampleLemma(Node q, Node lem) override;

 public:
  InstStrategyCegqi( QuantifiersEngine * qe );
  ~InstStrategyCegqi() override;

  bool doAddInstantiation( std::vector< Node >& subs );
  bool isEligibleForInstantiation( Node n );
  bool addLemma( Node lem );
  /** identify */
  std::string identify() const override { return std::string("Cegqi"); }

  //get instantiator for quantifier
  CegInstantiator * getInstantiator( Node q );
  //register quantifier
  void registerQuantifier(Node q) override;
  //presolve
  void presolve() override;
};

}
}
}

#endif
