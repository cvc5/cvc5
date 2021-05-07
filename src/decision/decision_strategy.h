/******************************************************************************
 * Top contributors (to current version):
 *   Kshitij Bansal, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Decision strategy.
 */

#include "cvc5_private.h"

#ifndef CVC5__DECISION__DECISION_STRATEGY_H
#define CVC5__DECISION__DECISION_STRATEGY_H

#include <vector>

#include "expr/node.h"
#include "prop/sat_solver_types.h"
#include "smt/term_formula_removal.h"

namespace cvc5 {

class DecisionEngineOld;

namespace context {
  class Context;
  }  // namespace context

namespace decision {
  
class DecisionEngine;

class DecisionStrategy {
protected:
 DecisionEngineOld* d_decisionEngine;

public:
 DecisionStrategy(DecisionEngineOld* de, context::Context* c)
     : d_decisionEngine(de)
 {
  }

  virtual ~DecisionStrategy() { }

  virtual prop::SatLiteral getNext(bool&) = 0;
};/* class DecisionStrategy */

class ITEDecisionStrategy : public DecisionStrategy {
public:
 ITEDecisionStrategy(DecisionEngineOld* de, context::Context* c)
     : DecisionStrategy(de, c)
 {
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

}  // namespace decision
}  // namespace cvc5

#endif /* CVC5__DECISION__DECISION_STRATEGY_H */
