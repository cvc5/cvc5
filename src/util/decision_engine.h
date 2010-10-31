/*********************                                                        */
/*! \file decision_engine.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A decision engine for CVC4
 **
 ** A decision engine for CVC4.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__DECISION_ENGINE_H
#define __CVC4__DECISION_ENGINE_H

#include "expr/node.h"

namespace CVC4 {

// In terms of abstraction, this is below (and provides services to)
// PropEngine.

/**
 * A decision mechanism for the next decision.
 */
class DecisionEngine {
public:
  /**
   * Destructor.
   */
  virtual ~DecisionEngine();

  /**
   * Get the next decision.
   */
  virtual Node nextDecision();// = 0

  /**
   * This is called by SmtEngine, at shutdown time, just before
   * destruction.  It is important because there are destruction
   * ordering issues between some parts of the system.  For now,
   * there's nothing to do here in the DecisionEngine.
   */
  virtual void shutdown() {
  }

  // TODO: design decision: decision engine should be notified of
  // propagated lits, and also why(?) (so that it can make decisions
  // based on the utility of various theories and various theory
  // literals).  How?  Maybe TheoryEngine has a backdoor into
  // DecisionEngine "behind the back" of the PropEngine?

};/* class DecisionEngine */

}/* CVC4 namespace */

#endif /* __CVC4__DECISION_ENGINE_H */
