/*********************                                                        */
/*! \file valuation.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A "valuation" proxy for TheoryEngine
 **
 ** A "valuation" proxy for TheoryEngine.  This class breaks the dependence
 ** of theories' getValue() implementations on TheoryEngine.  getValue()
 ** takes a Valuation, which delegates to TheoryEngine.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__VALUATION_H
#define __CVC4__THEORY__VALUATION_H

#include "expr/node.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

class Valuation {
  TheoryEngine* d_engine;
public:
  Valuation(TheoryEngine* engine) :
    d_engine(engine) {
  }

  Node getValue(TNode n);

  /**
   * Get the current SAT assignment to the node n.
   *
   * This is only permitted if n is a theory atom that has an associated
   * SAT literal (or its negation).
   *
   * @return Node::null() if no current assignment; otherwise true or false.
   */
  Node getSatValue(TNode n);

};/* class Valuation */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__VALUATION_H */
