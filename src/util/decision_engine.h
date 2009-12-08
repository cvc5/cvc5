/*********************                                           -*- C++ -*-  */
/** decision_engine.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#ifndef __CVC4__DECISION_ENGINE_H
#define __CVC4__DECISION_ENGINE_H

#include "cvc4_config.h"
#include "util/literal.h"

namespace CVC4 {

// In terms of abstraction, this is below (and provides services to)
// PropEngine.

/**
 * A decision mechanism for the next decision.
 */
class CVC4_PUBLIC DecisionEngine {
public:
  /**
   * Destructor.
   */
  virtual ~DecisionEngine();

  /**
   * Get the next decision.
   */
  virtual Literal nextDecision();// = 0

  // TODO: design decision: decision engine should be notified of
  // propagated lits, and also why(?) (so that it can make decisions
  // based on the utility of various theories and various theory
  // literals).  How?  Maybe TheoryEngine has a backdoor into
  // DecisionEngine "behind the back" of the PropEngine?

};/* class DecisionEngine */

}/* CVC4 namespace */

#endif /* __CVC4__DECISION_ENGINE_H */
