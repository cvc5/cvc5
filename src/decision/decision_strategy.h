/*********************                                                        */
/*! \file decision_strategy.h
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Decision stategy
 **
 ** Decision strategy
 **/

#ifndef __CVC4__DECISION__DECISION_STRATEGY_H
#define __CVC4__DECISION__DECISION_STRATEGY_H

#include "prop/sat_solver_types.h"

namespace CVC4 {

class DecisionEngine;

namespace context {
class Context;
}

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
  
  virtual bool needSimplifiedPreITEAssertions() { return false; }
  
  virtual void notifyAssertionsAvailable() { return; }
};

}/* decision namespace */
}/* CVC4 namespace */

#endif /* __CVC4__DECISION__DECISION_STRATEGY_H */
