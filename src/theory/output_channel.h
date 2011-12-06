/*********************                                                        */
/*! \file output_channel.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): taking, barrett
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The theory output channel interface
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
 * A LemmaStatus, returned from OutputChannel::lemma(), provides information
 * about the lemma added.  In particular, it contains the T-rewritten lemma
 * for inspection and the user-level at which the lemma will reside.
 */
class LemmaStatus {
  Node d_rewrittenLemma;
  unsigned d_level;

public:
  LemmaStatus(TNode rewrittenLemma, unsigned level) :
    d_rewrittenLemma(rewrittenLemma),
    d_level(level) {
  }

  /** Get the T-rewritten form of the lemma. */
  TNode getRewrittenLemma() const throw() { return d_rewrittenLemma; }

  /**
   * Get the user-level at which the lemma resides.  After this user level
   * is popped, the lemma is un-asserted from the SAT layer.  This level
   * will be 0 if the lemma didn't reach the SAT layer at all.
   */
  unsigned getLevel() const throw() { return d_level; }

};/* class LemmaStatus */

/**
 * Generic "theory output channel" interface.
 */
class OutputChannel {
  /** Disallow copying: private constructor */
  OutputChannel(const OutputChannel&) CVC4_UNDEFINED;

  /** Disallow assignment: private operator=() */
  OutputChannel& operator=(const OutputChannel&) CVC4_UNDEFINED;

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
   * assigned false), or else a literal by itself (in the case of a
   * unit conflict) which is assigned TRUE (and T-conflicting) in the
   * current assignment.
   */
  virtual void conflict(TNode n) throw(AssertionException) = 0;

  /**
   * Propagate a theory literal.
   *
   * @param n - a theory consequence at the current decision level
   */
  virtual void propagate(TNode n) throw(AssertionException) = 0;

  /**
   * Tell the core that a valid theory lemma at decision level 0 has
   * been detected.  (This requests a split.)
   *
   * @param n - a theory lemma valid at decision level 0
   * @param removable - whether the lemma can be removed at any point
   * @return the "status" of the lemma, including user level at which
   * the lemma resides; the lemma will be removed when this user level pops
   */
  virtual LemmaStatus lemma(TNode n, bool removable = false)
    throw(TypeCheckingExceptionPrivate, AssertionException) = 0;

  /**
   * Request a split on a new theory atom.  This is equivalent to
   * calling lemma({OR n (NOT n)}).
   *
   * @param n - a theory atom; must be of Boolean type
   */
  LemmaStatus split(TNode n)
    throw(TypeCheckingExceptionPrivate, AssertionException) {
    return lemma(n.orNode(n.notNode()));
  }

  /**
   * Notification from a theory that it realizes it is incomplete at
   * this context level.  If SAT is later determined by the
   * TheoryEngine, it should actually return an UNKNOWN result.
   */
  virtual void setIncomplete() throw(AssertionException) = 0;

  /**
   * "Spend" a "resource."  The meaning is specific to the context in
   * which the theory is operating, and may even be ignored.  The
   * intended meaning is that if the user has set a limit on the "units
   * of resource" that can be expended in a search, and that limit is
   * exceeded, then the search is terminated.  Note that the check for
   * termination occurs in the main search loop, so while theories
   * should call OutputChannel::spendResource() during particularly
   * long-running operations, they cannot rely on resource() to break
   * out of infinite or intractable computations.
   */
  virtual void spendResource() throw() {
  }

};/* class OutputChannel */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__OUTPUT_CHANNEL_H */
