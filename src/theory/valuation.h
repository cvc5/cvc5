/*********************                                                        */
/*! \file valuation.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): taking, barrett, dejan
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
#include "theory/substitutions.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * The status of an equality in the current context.
 */
enum EqualityStatus {
  /** The equality is known to be true and has been propagated */
  EQUALITY_TRUE_AND_PROPAGATED,
  /** The equality is known to be false and has been propagated */
  EQUALITY_FALSE_AND_PROPAGATED,
  /** The equality is known to be true */
  EQUALITY_TRUE,
  /** The equality is known to be false */
  EQUALITY_FALSE,
  /** The equality is not known, but is true in the current model */
  EQUALITY_TRUE_IN_MODEL,
  /** The equality is not known, but is false in the current model */
  EQUALITY_FALSE_IN_MODEL,
  /** The equality is completely unknown */
  EQUALITY_UNKNOWN
};

/**
 * Returns true if the two statuses are compatible, i.e. bot TRUE
 * or both FALSE (regardles of inmodel/propagation).
 */
bool equalityStatusCompatible(EqualityStatus s1, EqualityStatus s2);

class Valuation {
  TheoryEngine* d_engine;
public:
  Valuation(TheoryEngine* engine) :
    d_engine(engine) {
  }

  Node getValue(TNode n) const;

  /*
   * Return true if n has an associated SAT literal
   */
  bool isSatLiteral(TNode n) const;

  /**
   * Get the current SAT assignment to the node n.
   *
   * This is only permitted if n is a theory atom that has an associated
   * SAT literal (or its negation).
   *
   * @return Node::null() if no current assignment; otherwise true or false.
   */
  Node getSatValue(TNode n) const;

  /**
   * Returns true if the node has a current SAT assignment. If yes, the
   * argument "value" is set to its value.
   *
   * This is only permitted if n is a theory atom that has an associated
   * SAT literal.
   *
   * @return true if the literal has a current assignment, and returns the
   * value in the "value" argument; otherwise false and the "value"
   * argument is unmodified.
   */
  bool hasSatValue(TNode n, bool& value) const;

  /**
   * Returns the equality status of the two terms, from the theory that owns the domain type.
   * The types of a and b must be the same.
   */
  EqualityStatus getEqualityStatus(TNode a, TNode b);

  /**
   * Ensure that the given node will have a designated SAT literal
   * that is definitionally equal to it.  The result of this function
   * is a Node that can be queried via getSatValue().
   *
   * @return the actual node that's been "literalized," which may
   * differ from the input due to theory-rewriting and preprocessing,
   * as well as CNF conversion
   */
  Node ensureLiteral(TNode n) CVC4_WARN_UNUSED_RESULT;

};/* class Valuation */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__VALUATION_H */
