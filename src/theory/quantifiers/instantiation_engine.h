/*********************                                                        */
/*! \file instantiation_engine.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Instantiation Engine classes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__INSTANTIATION_ENGINE_H
#define __CVC4__THEORY__QUANTIFIERS__INSTANTIATION_ENGINE_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/theory_quantifiers.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class InstStrategyUserPatterns;
class InstStrategyAutoGenTriggers;

/** instantiation strategy class */
class InstStrategy {
public:
  enum Status {
    STATUS_UNFINISHED,
    STATUS_UNKNOWN,
    STATUS_SAT,
  };/* enum Status */
protected:
  /** reference to the instantiation engine */
  QuantifiersEngine* d_quantEngine;
  /** should process a quantifier */
  std::map< Node, bool > d_quantActive;
  /** calculate should process */
  virtual bool calculateShouldProcess( Node f ) { return true; }
public:
  InstStrategy( QuantifiersEngine* qe ) : d_quantEngine( qe ){}
  virtual ~InstStrategy(){}

  /** should process quantified formula f? */
  bool shouldProcess( Node f ) {
    if( d_quantActive.find( f )==d_quantActive.end() ){
      d_quantActive[f] = calculateShouldProcess( f );
    }
    return d_quantActive[f];
  }
  /** reset instantiation */
  virtual void processResetInstantiationRound( Theory::Effort effort ) = 0;
  /** process method, returns a status */
  virtual int process( Node f, Theory::Effort effort, int e ) = 0;
  /** update status */
  static void updateStatus( int& currStatus, int addStatus ){
    if( addStatus==STATUS_UNFINISHED ){
      currStatus = STATUS_UNFINISHED;
    }else if( addStatus==STATUS_UNKNOWN ){
      if( currStatus==STATUS_SAT ){
        currStatus = STATUS_UNKNOWN;
      }
    }
  }
  /** identify */
  virtual std::string identify() const { return std::string("Unknown"); }
};/* class InstStrategy */

class InstantiationEngine : public QuantifiersModule
{
private:
  /** instantiation strategies */
  std::vector< InstStrategy* > d_instStrategies;
  /** instantiation strategies active */
  std::map< InstStrategy*, bool > d_instStrategyActive;
  /** user-pattern instantiation strategy */
  InstStrategyUserPatterns* d_isup;
  /** auto gen triggers; only kept for destructor cleanup */
  InstStrategyAutoGenTriggers* d_i_ag;
  /** is instantiation strategy active */
  bool isActiveStrategy( InstStrategy* is ) {
    return d_instStrategyActive.find( is )!=d_instStrategyActive.end() && d_instStrategyActive[is];
  }
  /** add inst strategy */
  void addInstStrategy( InstStrategy* is ){
    d_instStrategies.push_back( is );
    d_instStrategyActive[is] = true;
  }
private:
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  /** status of instantiation round (one of InstStrategy::STATUS_*) */
  int d_inst_round_status;
  /** whether the instantiation engine should set incomplete if it cannot answer SAT */
  bool d_setIncomplete;
  /** inst round counter */
  int d_ierCounter;
  bool d_performCheck;
  /** whether each quantifier is active */
  std::map< Node, bool > d_quant_active;
  /** whether we have added cbqi lemma */
  std::map< Node, bool > d_added_cbqi_lemma;
private:
  /** has added cbqi lemma */
  bool hasAddedCbqiLemma( Node f ) { return d_added_cbqi_lemma.find( f )!=d_added_cbqi_lemma.end(); }
  /** helper functions */
  bool hasNonArithmeticVariable( Node f );
  bool hasApplyUf( Node f );
  /** whether to do CBQI for quantifier f */
  bool doCbqi( Node f );
private:
  /** do instantiation round */
  bool doInstantiationRound( Theory::Effort effort );
  /** register literals of n, f is the quantifier it belongs to */
  //void registerLiterals( Node n, Node f );
private:
  enum{
    SAT_CBQI,
    SAT_INST_STRATEGY,
  };
  /** debug sat */
  void debugSat( int reason );
public:
  InstantiationEngine( QuantifiersEngine* qe, bool setIncomplete = true );
  ~InstantiationEngine();
  /** initialize */
  void finishInit();

  bool needsCheck( Theory::Effort e );
  void check( Theory::Effort e );
  void registerQuantifier( Node f );
  void assertNode( Node f );
  Node explain(TNode n){ return Node::null(); }
  Node getNextDecisionRequest();
  /** add user pattern */
  void addUserPattern( Node f, Node pat );
public:
  /** statistics class */
  class Statistics {
  public:
    IntStat d_instantiations_user_patterns;
    IntStat d_instantiations_auto_gen;
    IntStat d_instantiations_auto_gen_min;
    IntStat d_instantiations_guess;
    IntStat d_instantiations_cbqi_arith;
    IntStat d_instantiations_cbqi_arith_minus;
    IntStat d_instantiations_cbqi_datatypes;
    IntStat d_instantiation_rounds;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
  /** Identify this module */
  std::string identify() const { return "InstEngine"; }
};/* class InstantiationEngine */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__INSTANTIATION_ENGINE_H */
