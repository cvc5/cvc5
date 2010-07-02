/*********************                                                        */
/*! \file arith_propagator.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/



#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_PROPAGATOR_H
#define __CVC4__THEORY__ARITH__ARITH_PROPAGATOR_H

#include "expr/node.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "context/cdo.h"
#include "theory/arith/ordered_bounds_list.h"

#include <algorithm>
#include <vector>

namespace CVC4 {
namespace theory {
namespace arith {

class ArithUnatePropagator {
private:
  /** Index of assertions. */
  context::CDList<Node> d_assertions;

  /** Index of the last assertion in d_assertions to be asserted. */
  context::CDO<unsigned int> d_pendingAssertions;

public:
  ArithUnatePropagator(context::Context* cxt);

  /**
   * Adds a new atom for the propagator to watch.
   * Atom is assumed to have been rewritten by TheoryArith::rewrite().
   */
  void addAtom(TNode atom);

  /**
   * Informs the propagator that a literal has been asserted to the theory.
   */
  void assertLiteral(TNode lit);


  /**
   * returns a vector of literals that are 
   */
  std::vector<Node> getImpliedLiterals();

  /** Explains a literal that was asserted in the current context. */
  Node explain(TNode lit);

private:
  /** returns true if the left hand side side left has been setup. */
  bool leftIsSetup(TNode left);

  /**
   * Sets up a left hand side.
   * This initializes the attributes PropagatorEqList, PropagatorGeqList, and PropagatorLeqList for left.
   */
  void setupLefthand(TNode left);

  /**
   * Given that the literal lit is now asserted,
   * enqueue additional entailed assertions in buffer.
   */
  void enqueueImpliedLiterals(TNode lit, std::vector<Node>& buffer);

  void enqueueEqualityImplications(TNode original, std::vector<Node>& buffer);
  void enqueueLowerBoundImplications(TNode atom, TNode original, std::vector<Node>& buffer);
  /**
   * Given that the literal original is now asserted, which is either (<= x c) or (not (>= x c)),
   * enqueue additional entailed assertions in buffer.
   */
  void enqueueUpperBoundImplications(TNode atom, TNode original, std::vector<Node>& buffer);
};



namespace propagator {

/** Basic memory management wrapper for deleting PropagatorEqList, PropagatorGeqList, and PropagatorLeqList.*/
struct ListCleanupStrategy{
  static void cleanup(OrderedBoundsList* l){
    Debug("arithgc") << "cleaning up  " << l << "\n";
    delete l;
  }
};


struct PropagatorEqListID {};
typedef expr::Attribute<PropagatorEqListID, OrderedBoundsList*, ListCleanupStrategy> PropagatorEqList;

struct PropagatorGeqListID {};
typedef expr::Attribute<PropagatorGeqListID, OrderedBoundsList*, ListCleanupStrategy> PropagatorGeqList;

struct PropagatorLeqListID {};
typedef expr::Attribute<PropagatorLeqListID, OrderedBoundsList*, ListCleanupStrategy> PropagatorLeqList;


struct PropagatorMarkedID {};
typedef expr::CDAttribute<PropagatorMarkedID, bool> PropagatorMarked;

struct PropagatorExplanationID {};
typedef expr::CDAttribute<PropagatorExplanationID, Node> PropagatorExplanation;
}/* CVC4::theory::arith::propagator */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__THEORY_ARITH_H */
