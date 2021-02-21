/*********************                                                        */
/*! \file decision_strategy.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Decision strategy
 **
 ** Decision strategy
 **/

#include "cvc4_private.h"

#ifndef CVC4__DECISION__DECISION_STRATEGY_H
#define CVC4__DECISION__DECISION_STRATEGY_H

#include <vector>

#include "expr/node.h"
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
};/* class DecisionStrategy */

class ITEDecisionStrategy : public DecisionStrategy {
public:
  ITEDecisionStrategy(DecisionEngine* de, context::Context *c) :
    DecisionStrategy(de, c) {
  }
  /**
   * Add that assertion is an (input) assertion, not corresponding to a
   * skolem definition.
   */
  virtual void addAssertion(TNode assertion) = 0;
  /**
   * Add that lem is the skolem definition for skolem, which is a part of
   * the current assertions.
   */
  virtual void addSkolemDefinition(TNode lem, TNode skolem) = 0;
};/* class ITEDecisionStrategy */

}/* CVC4::decision namespace */
}/* CVC4 namespace */

#endif /* CVC4__DECISION__DECISION_STRATEGY_H */
