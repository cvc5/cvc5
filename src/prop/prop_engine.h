/*********************                                           -*- C++ -*-  */
/** prop_engine.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#ifndef __CVC4__PROP__PROP_ENGINE_H
#define __CVC4__PROP__PROP_ENGINE_H

#include "cvc4_expr.h"
#include "util/decision_engine.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace prop {

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

}/* CVC4::prop namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PROP__PROP_ENGINE_H */
