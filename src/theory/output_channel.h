/*********************                                           -*- C++ -*-  */
/** output_channel.h
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
 ** The theory output channel interface.
 **/

#ifndef __CVC4__THEORY__OUTPUT_CHANNEL_H
#define __CVC4__THEORY__OUTPUT_CHANNEL_H

#include "theory/interrupted.h"

namespace CVC4 {
namespace theory {

/**
 * Generic "theory output channel" interface.
 */
class OutputChannel {
public:

  /**
   * With safePoint(), the theory signals that it is at a safe point
   * and can be interrupted.
   */
  virtual void safePoint() throw(Interrupted&) {
  }

  /**
   * Indicate a theory conflict has arisen.
   *
   * @param n - a conflict at the current decision level
   * @param safe - whether it is safe to be interrupted
   */
  virtual void conflict(Node n, bool safe = false) throw(Interrupted&) = 0;

  /**
   * Propagate a theory literal.
   *
   * @param n - a theory consequence at the current decision level
   * @param safe - whether it is safe to be interrupted
   */
  virtual void propagate(Node n, bool safe = false) throw(Interrupted&) = 0;

  /**
   * Tell the core that a valid theory lemma at decision level 0 has
   * been detected.  (This request a split.)
   *
   * @param n - a theory lemma valid at decision level 0
   * @param safe - whether it is safe to be interrupted
   */
  virtual void lemma(Node n, bool safe = false) throw(Interrupted&) = 0;

};/* class OutputChannel */

/**
 * Generic "theory output channel" interface for explanations.
 */
class ExplainOutputChannel {
public:

  /**
   * With safePoint(), the theory signals that it is at a safe point
   * and can be interrupted.  The default implementation never
   * interrupts.
   */
  virtual void safePoint() throw(Interrupted&) {
  }

  /**
   * Provide an explanation in response to an explanation request.
   *
   * @param n - an explanation
   * @param safe - whether it is safe to be interrupted
   */
  virtual void explanation(Node n, bool safe = false) throw(Interrupted&) = 0;
};/* class ExplainOutputChannel */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__OUTPUT_CHANNEL_H */
