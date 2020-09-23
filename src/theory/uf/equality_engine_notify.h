/*********************                                                        */
/*! \file equality_engine_notify.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The virtual class for notifications from the equality engine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__UF__EQUALITY_ENGINE_NOTIFY_H
#define CVC4__THEORY__UF__EQUALITY_ENGINE_NOTIFY_H

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace eq {

/**
 * Interface for equality engine notifications. All the notifications
 * are safe as TNodes, but not necessarily for negations.
 */
class EqualityEngineNotify
{
 public:
  virtual ~EqualityEngineNotify(){};

  /**
   * Notifies about a trigger predicate that became true or false. Notice that
   * predicate can be an equality.
   *
   * @param predicate the trigger predicate that became true or false
   * @param value the value of the predicate
   */
  virtual bool eqNotifyTriggerPredicate(TNode predicate, bool value) = 0;

  /**
   * Notifies about the merge of two trigger terms.
   *
   * @param tag the theory that both triggers were tagged with
   * @param t1 a term marked as trigger
   * @param t2 a term marked as trigger
   * @param value true if equal, false if dis-equal
   */
  virtual bool eqNotifyTriggerTermEquality(TheoryId tag,
                                           TNode t1,
                                           TNode t2,
                                           bool value) = 0;

  /**
   * Notifies about the merge of two constant terms. After this, all work is
   * suspended and all you can do is ask for explanations.
   *
   * @param t1 a constant term
   * @param t2 a constant term
   */
  virtual void eqNotifyConstantTermMerge(TNode t1, TNode t2) = 0;

  /**
   * Notifies about the creation of a new equality class.
   *
   * @param t the term forming the new class
   */
  virtual void eqNotifyNewClass(TNode t) = 0;

  /**
   * Notifies about the merge of two classes (just after the merge).
   *
   * @param t1 a term
   * @param t2 a term
   */
  virtual void eqNotifyMerge(TNode t1, TNode t2) = 0;

  /**
   * Notifies about the disequality of two terms.
   *
   * @param t1 a term
   * @param t2 a term
   * @param reason the reason
   */
  virtual void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) = 0;

}; /* class EqualityEngineNotify */

/**
 * Implementation of the notification interface that ignores all the
 * notifications.
 */
class EqualityEngineNotifyNone : public EqualityEngineNotify
{
 public:
  bool eqNotifyTriggerPredicate(TNode predicate, bool value) override
  {
    return true;
  }
  bool eqNotifyTriggerTermEquality(TheoryId tag,
                                   TNode t1,
                                   TNode t2,
                                   bool value) override
  {
    return true;
  }
  void eqNotifyConstantTermMerge(TNode t1, TNode t2) override {}
  void eqNotifyNewClass(TNode t) override {}
  void eqNotifyMerge(TNode t1, TNode t2) override {}
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override {}
}; /* class EqualityEngineNotifyNone */

}  // Namespace eq
}  // Namespace theory
}  // Namespace CVC4

#endif
