/*********************                                                        */
/*! \file instantiation_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Instantiation Engine classes
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__INSTANTIATION_ENGINE_H
#define CVC4__THEORY__QUANTIFIERS__INSTANTIATION_ENGINE_H

#include <vector>

#include "theory/quantifiers/quant_relevance.h"
#include "theory/quantifiers/quant_util.h"

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
};/* class InstStrategy */

class InstantiationEngine : public QuantifiersModule {
 private:
  /** instantiation strategies */
  std::vector<InstStrategy*> d_instStrategies;
  /** user-pattern instantiation strategy */
  std::unique_ptr<InstStrategyUserPatterns> d_isup;
  /** auto gen triggers; only kept for destructor cleanup */
  std::unique_ptr<InstStrategyAutoGenTriggers> d_i_ag;

  /** current processing quantified formulas */
  std::vector<Node> d_quants;

  /** is the engine incomplete for this quantifier */
  bool isIncomplete(Node q);
  /** do instantiation round */
  void doInstantiationRound(Theory::Effort effort);

 public:
  InstantiationEngine(QuantifiersEngine* qe);
  ~InstantiationEngine();
  void presolve() override;
  bool needsCheck(Theory::Effort e) override;
  void reset_round(Theory::Effort e) override;
  void check(Theory::Effort e, QEffort quant_e) override;
  bool checkCompleteFor(Node q) override;
  void checkOwnership(Node q) override;
  void registerQuantifier(Node q) override;
  Node explain(TNode n) { return Node::null(); }
  /** add user pattern */
  void addUserPattern(Node q, Node pat);
  void addUserNoPattern(Node q, Node pat);
  /** Identify this module */
  std::string identify() const override { return "InstEngine"; }

 private:
  /** Return true if this module should process quantified formula q */
  bool shouldProcess(Node q);
  /** for computing relevance of quantifiers */
  std::unique_ptr<QuantRelevance> d_quant_rel;
}; /* class InstantiationEngine */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__INSTANTIATION_ENGINE_H */
