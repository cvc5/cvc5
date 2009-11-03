/*********************                                           -*- C++ -*-  */
/** theory_engine.h
 ** This file is part of the CVC4 prototype.
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 **/

#ifndef __CVC4_THEORY_ENGINE_H
#define __CVC4_THEORY_ENGINE_H

namespace CVC4 {

// In terms of abstraction, this is below (and provides services to)
// PropEngine.

/**
 * This is essentially an abstraction for a collection of theories.  A
 * TheoryEngine provides services to a PropEngine, making various
 * T-solvers look like a single unit to the propositional part of
 * CVC4.
 */
class TheoryEngine {
public:
};/* class TheoryEngine */

}/* CVC4 namespace */

#endif /* __CVC4_THEORY_ENGINE_H */
