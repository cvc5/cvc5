/*********************                                                        */
/*! \file output_channel.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The theory output channel interface.
 **
 ** The theory output channel interface.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__OUTPUT_CHANNEL_H
#define __CVC4__THEORY__OUTPUT_CHANNEL_H

#include "util/Assert.h"
#include "theory/interrupted.h"

namespace CVC4 {
namespace theory {

/**
 * Generic "theory output channel" interface.
 */
class OutputChannel {
  /** Disallow copying: private constructor */
  OutputChannel(const OutputChannel&);

  /** Disallow assignment: private operator=() */
  OutputChannel& operator=(const OutputChannel&);

public:

  /**
   * Construct an OutputChannel.
   */
  OutputChannel() {
  }

  /**
   * Destructs an OutputChannel.  This implementation does nothing,
   * but we need a virtual destructor for safety in case subclasses
   * have a destructor.
   */
  virtual ~OutputChannel() {
  }

  /**
   * Notify the OutputChannel that a new fact has been received by
   * the theory.
   */
  virtual void newFact(TNode n) { }

  /**
   * With safePoint(), the theory signals that it is at a safe point
   * and can be interrupted.
   */
  virtual void safePoint() throw(Interrupted, AssertionException) {
  }

  /**
   * Indicate a theory conflict has arisen.
   *
   * @param n - a conflict at the current decision level.  This should
   * be an AND-kinded node of literals that are TRUE in the current
   * assignment and are in conflict (i.e., at least one must be
   * assigned false).
   *
   * @param safe - whether it is safe to be interrupted
   */
  virtual void conflict(TNode n, bool safe = false) throw(Interrupted, AssertionException) = 0;

  /**
   * Propagate a theory literal.
   *
   * @param n - a theory consequence at the current decision level.
   *
   * @param safe - whether it is safe to be interrupted
   */
  virtual void propagate(TNode n, bool safe = false) throw(Interrupted, AssertionException) = 0;

  /**
   * Tell the core that a valid theory lemma at decision level 0 has
   * been detected.  (This request a split.)
   *
   * @param n - a theory lemma valid at decision level 0
   * @param safe - whether it is safe to be interrupted
   */
  virtual void lemma(TNode n, bool safe = false) throw(Interrupted, AssertionException) = 0;

  /**
   * Tell the core to add the following valid lemma as if it were a user assertion.
   * This should NOT be called during solving, only preprocessing.
   *
   * @param n - a theory lemma valid to be asserted
   * @param safe - whether it is safe to be interrupted
   */
  virtual void augmentingLemma(TNode n, bool safe = false) throw(Interrupted, AssertionException) = 0;

  /**
   * Provide an explanation in response to an explanation request.
   *
   * @param n - an explanation
   * @param safe - whether it is safe to be interrupted
   */
  virtual void explanation(TNode n, bool safe = false) throw(Interrupted, AssertionException) = 0;

};/* class OutputChannel */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__OUTPUT_CHANNEL_H */
