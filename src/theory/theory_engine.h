/*********************                                                        */
/** theory_engine.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** The theory engine.
 **/

#ifndef __CVC4__THEORY_ENGINE_H
#define __CVC4__THEORY_ENGINE_H

#include "expr/node.h"
#include "theory/theory.h"

namespace CVC4 {

class SmtEngine;

// In terms of abstraction, this is below (and provides services to)
// PropEngine.

/**
 * This is essentially an abstraction for a collection of theories.  A
 * TheoryEngine provides services to a PropEngine, making various
 * T-solvers look like a single unit to the propositional part of
 * CVC4.
 */
class TheoryEngine {

  SmtEngine* d_smt;

public:

  /**
   * Construct a theory engine.
   */
  TheoryEngine(SmtEngine* smt) : d_smt(smt) {
  }

  /**
   * Get the theory associated to a given Node.
   */
  CVC4::theory::Theory* theoryOf(const Node& n);

};/* class TheoryEngine */

}/* CVC4 namespace */

#endif /* __CVC4__THEORY_ENGINE_H */
