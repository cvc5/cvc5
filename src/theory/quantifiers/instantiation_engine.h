/*********************                                                        */
/*! \file instantiation_engine.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
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
class InstStrategyFreeVariable;

/** instantiation strategy class */
class InstStrategy {
public:
  enum Status {
    STATUS_UNFINISHED,
    STATUS_UNKNOWN,
  };/* enum Status */
protected:
  /** reference to the instantiation engine */
  QuantifiersEngine* d_quantEngine;
public:
  InstStrategy( QuantifiersEngine* qe ) : d_quantEngine( qe ){}
  virtual ~InstStrategy(){}
  /** presolve */
  virtual void presolve() {}
  /** reset instantiation */
  virtual void processResetInstantiationRound( Theory::Effort effort ) = 0;
  /** process method, returns a status */
  virtual int process( Node f, Theory::Effort effort, int e ) = 0;
  /** identify */
  virtual std::string identify() const { return std::string("Unknown"); }
  /** register quantifier */
  //virtual void registerQuantifier( Node q ) {}
};/* class InstStrategy */

class InstantiationEngine : public QuantifiersModule
{
private:
  /** instantiation strategies */
  std::vector< InstStrategy* > d_instStrategies;
  /** user-pattern instantiation strategy */
  InstStrategyUserPatterns* d_isup;
  /** auto gen triggers; only kept for destructor cleanup */
  InstStrategyAutoGenTriggers* d_i_ag;
private:
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  /** current processing quantified formulas */
  std::vector< Node > d_quants;
private:
  /** is the engine incomplete for this quantifier */
  bool isIncomplete( Node q );
  /** do instantiation round */
  bool doInstantiationRound( Theory::Effort effort );
public:
  InstantiationEngine( QuantifiersEngine* qe );
  ~InstantiationEngine();
  /** initialize */
  void finishInit();
  void presolve();
  bool needsCheck( Theory::Effort e );
  void reset_round( Theory::Effort e );
  void check( Theory::Effort e, unsigned quant_e );
  bool checkComplete();
  void registerQuantifier( Node q );
  Node explain(TNode n){ return Node::null(); }
  /** add user pattern */
  void addUserPattern( Node f, Node pat );
  void addUserNoPattern( Node f, Node pat );
public:
  /** Identify this module */
  std::string identify() const { return "InstEngine"; }
};/* class InstantiationEngine */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__INSTANTIATION_ENGINE_H */
