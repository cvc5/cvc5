/*********************                                                        */
/*! \file instantiation_engine.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
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

class InstantiationEngine : public QuantifiersModule
{
private:
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  /** status of instantiation round (one of InstStrategy::STATUS_*) */
  int d_inst_round_status;
  /** whether the instantiation engine should set incomplete if it cannot answer SAT */
  bool d_setIncomplete;
  /** inst round counter */
  int d_ierCounter;
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
  ~InstantiationEngine(){}

  void check( Theory::Effort e );
  void registerQuantifier( Node f );
  void assertNode( Node f );
  Node explain(TNode n){ return Node::null(); }
  Node getNextDecisionRequest();
};/* class InstantiationEngine */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__INSTANTIATION_ENGINE_H */
