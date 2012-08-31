/*********************                                                        */
/*! \file instantiation_engine.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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
  /** map from universal quantifiers to their counterexample literals */
  std::map< Node, Node > d_ce_lit;
  /** whether the instantiation engine should set incomplete if it cannot answer SAT */
  bool d_setIncomplete;
private:
  bool hasAddedCbqiLemma( Node f );
  void addCbqiLemma( Node f );
private:
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
  void propagate( Theory::Effort level );
  Node getNextDecisionRequest();
public:
  /** get the corresponding counterexample literal for quantified formula node n */
  Node getCounterexampleLiteralFor( Node f ) { return d_ce_lit.find( f )==d_ce_lit.end() ? Node::null() : d_ce_lit[ f ]; }
};/* class InstantiationEngine */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__INSTANTIATION_ENGINE_H */
