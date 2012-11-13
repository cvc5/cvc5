/*********************                                                        */
/*! \file bv_subtheory_eq.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): lianah, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Algebraic solver.
 **
 ** Algebraic solver.
 **/

#pragma once

#include "cvc4_private.h"
#include "theory/bv/bv_subtheory.h"

namespace CVC4 {
namespace theory {
namespace bv {

/**
 * Bitvector equality solver
 */
class EqualitySolver : public SubtheorySolver {

  // NotifyClass: handles call-back from congruence closure module

  class NotifyClass : public eq::EqualityEngineNotify {
    EqualitySolver& d_solver;

  public:
    NotifyClass(EqualitySolver& solver): d_solver(solver) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value);
    bool eqNotifyTriggerPredicate(TNode predicate, bool value);
    bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value);
    void eqNotifyConstantTermMerge(TNode t1, TNode t2);
    void eqNotifyNewClass(TNode t) { }
    void eqNotifyPreMerge(TNode t1, TNode t2) { }
    void eqNotifyPostMerge(TNode t1, TNode t2) { }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) { }
};


  /** The notify class for d_equalityEngine */
  NotifyClass d_notify;

  /** Equality engine */
  eq::EqualityEngine d_equalityEngine;

  /** Store a propagation to the bv solver */
  bool storePropagation(TNode literal);
  
  /** Store a conflict from merging two constants */
  void conflict(TNode a, TNode b);

  /** FIXME: for debugging purposes only */
  context::CDList<TNode> d_assertions; 
public:

  EqualitySolver(context::Context* c, TheoryBV* bv);

  void  preRegister(TNode node);
  bool  addAssertions(const std::vector<TNode>& assertions, Theory::Effort e);
  void  explain(TNode literal, std::vector<TNode>& assumptions);
  void  collectModelInfo(TheoryModel* m);
  void  addSharedTerm(TNode t) {
    d_equalityEngine.addTriggerTerm(t, THEORY_BV);
  }
  EqualityStatus getEqualityStatus(TNode a, TNode b) {
    if (d_equalityEngine.areEqual(a, b)) {
      // The terms are implied to be equal
      return EQUALITY_TRUE;
    }
    if (d_equalityEngine.areDisequal(a, b, false)) {
      // The terms are implied to be dis-equal
      return EQUALITY_FALSE;
    }
    return EQUALITY_UNKNOWN;
  }
};


}
}
}
