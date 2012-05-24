/*********************                                                        */
/*! \file bv_subtheory_eq.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Algebraic solver.
 **
 ** Algebraic solver.
 **/

#pragma once

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
    TheoryBV* d_bv;

  public:
    NotifyClass(TheoryBV* bv): d_bv(bv) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value);
    bool eqNotifyTriggerPredicate(TNode predicate, bool value);
    bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value);
    bool eqNotifyConstantTermMerge(TNode t1, TNode t2);
};


  /** The notify class for d_equalityEngine */
  NotifyClass d_notify;

  /** Equality engine */
  eq::EqualityEngine d_equalityEngine;

public:

  EqualitySolver(context::Context* c, TheoryBV* bv);

  void  preRegister(TNode node);
  bool  addAssertions(const std::vector<TNode>& assertions, Theory::Effort e);
  void  explain(TNode literal, std::vector<TNode>& assumptions);
  void  addSharedTerm(TNode t) {
    d_equalityEngine.addTriggerTerm(t, THEORY_BV);
  }
  EqualityStatus getEqualityStatus(TNode a, TNode b) {
    if (d_equalityEngine.areEqual(a, b)) {
      // The terms are implied to be equal
      return EQUALITY_TRUE;
    }
    if (d_equalityEngine.areDisequal(a, b)) {
      // The terms are implied to be dis-equal
      return EQUALITY_FALSE;
    }
    return EQUALITY_UNKNOWN;
  }
};


}
}
}
