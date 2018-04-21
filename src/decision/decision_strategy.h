/*********************                                                        */
/*! \file decision_strategy.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Morgan Deters, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Decision strategy
 **
 ** Decision strategy
 **/

#include "cvc4_private.h"

#ifndef __CVC4__DECISION__DECISION_STRATEGY_H
#define __CVC4__DECISION__DECISION_STRATEGY_H

#include "prop/sat_solver_types.h"
#include "smt/term_formula_removal.h"

namespace CVC4 {

class DecisionEngine;

namespace context {
  class Context;
}/* CVC4::context namespace */

namespace decision {

class DecisionStrategy {
protected:
  DecisionEngine* d_decisionEngine;
public:
  DecisionStrategy(DecisionEngine* de, context::Context *c) :
    d_decisionEngine(de) {
  }

  virtual ~DecisionStrategy() { }

  virtual prop::SatLiteral getNext(bool&) = 0;

  virtual bool needIteSkolemMap() { return false; }

  virtual void notifyAssertionsAvailable() { return; }
};/* class DecisionStrategy */

class ITEDecisionStrategy : public DecisionStrategy {
public:
  ITEDecisionStrategy(DecisionEngine* de, context::Context *c) :
    DecisionStrategy(de, c) {
  }

  bool needIteSkolemMap() override { return true; }

  virtual void addAssertions(const std::vector<Node> &assertions,
                             unsigned assertionsEnd,
                             IteSkolemMap iteSkolemMap) = 0;
};/* class ITEDecisionStrategy */

class RelevancyStrategy : public ITEDecisionStrategy {
public:
  RelevancyStrategy(DecisionEngine* de, context::Context *c) :
    ITEDecisionStrategy(de, c) {
  }

  virtual bool isRelevant(TNode n) = 0;
  virtual prop::SatValue getPolarity(TNode n) = 0;
};/* class RelevancyStrategy */

}/* CVC4::decision namespace */
}/* CVC4 namespace */

#endif /* __CVC4__DECISION__DECISION_STRATEGY_H */
