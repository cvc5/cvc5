/*********************                                           -*- C++ -*-  */
/** prop_engine.h
 ** This file is part of the CVC4 prototype.
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 **/

#ifndef __CVC4_PROP_ENGINE_H
#define __CVC4_PROP_ENGINE_H

#include "expr.h"
#include "decision_engine.h"
#include "theory_engine.h"

namespace CVC4 {

// In terms of abstraction, this is below (and provides services to)
// Prover and above (and requires the services of) a specific
// propositional solver, DPLL or otherwise.

class PropEngine {
  DecisionEngine* d_de;

public:
  /**
   * Create a PropEngine with a particular decision and theory engine.
   */
  PropEngine(DecisionEngine*, TheoryEngine*);

  /**
   * Converts to CNF if necessary.
   */
  void solve(Expr);

};/* class PropEngine */

}

#endif /* __CVC4_PROP_ENGINE_H */
