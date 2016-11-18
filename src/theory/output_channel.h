/*********************                                                        */
/*! \file output_channel.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Liana Hadarean, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The theory output channel interface
 **
 ** The theory output channel interface.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__OUTPUT_CHANNEL_H
#define __CVC4__THEORY__OUTPUT_CHANNEL_H

#include "base/cvc4_assert.h"
#include "smt/logic_exception.h"
#include "theory/interrupted.h"
#include "proof/proof_manager.h"
#include "util/resource_manager.h"

namespace CVC4 {
namespace theory {

class Theory;

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
  virtual void safePoint(uint64_t amount)
      throw(Interrupted, UnsafeInterruptException, AssertionException)
  {}

  /**
   * Indicate a theory conflict has arisen.
   *
   * @param n - a conflict at the current decision level.  This should
   * be an AND-kinded node of literals that are TRUE in the current
   * assignment and are in conflict (i.e., at least one must be
   * assigned false), or else a literal by itself (in the case of a
   * unit conflict) which is assigned TRUE (and T-conflicting) in the
   * current assignment.
   * @param pf - a proof of the conflict. This is only non-null if proofs
   * are enabled.
   */
  virtual void conflict(TNode n, Proof* pf = NULL) throw(AssertionException, UnsafeInterruptException) = 0;

  /**
   * Propagate a theory literal.
   *
   * @param n - a theory consequence at the current decision level
   * @return false if an immediate conflict was encountered
   */
  virtual bool propagate(TNode n) throw(AssertionException, UnsafeInterruptException) = 0;

  /**
   * Tell the core that a valid theory lemma at decision level 0 has
   * been detected.  (This requests a split.)
   *
   * @param n - a theory lemma valid at decision level 0
   * @param rule - the proof rule for this lemma
   * @param removable - whether the lemma can be removed at any point
   * @param preprocess - whether to apply more aggressive preprocessing
   * @param sendAtoms - whether to ensure atoms are sent to the theory
   * @return the "status" of the lemma, including user level at which
   * the lemma resides; the lemma will be removed when this user level pops
   */
  virtual LemmaStatus lemma(TNode n, ProofRule rule,
                            bool removable = false,
                            bool preprocess = false,
                            bool sendAtoms = false) = 0;

  /**
   * Variant of the lemma function that does not require providing a proof rule.
   */
  virtual LemmaStatus lemma(TNode n,
                            bool removable = false,
                            bool preprocess = false,
                            bool sendAtoms = false) {
    return lemma(n, RULE_INVALID, removable, preprocess, sendAtoms);
  }

  /**
   * Request a split on a new theory atom.  This is equivalent to
   * calling lemma({OR n (NOT n)}).
   *
   * @param n - a theory atom; must be of Boolean type
   */
  LemmaStatus split(TNode n)
    throw(TypeCheckingExceptionPrivate, AssertionException, UnsafeInterruptException) {
    return splitLemma(n.orNode(n.notNode()));
  }

  virtual LemmaStatus splitLemma(TNode n, bool removable = false) = 0;

  /**
   * If a decision is made on n, it must be in the phase specified.
   * Note that this is enforced *globally*, i.e., it is completely
   * context-INdependent.  If you ever requirePhase() on a literal,
   * it is phase-locked forever and ever.  If it is to ever have the
   * other phase as its assignment, it will be because it has been
   * propagated that way (or it's a unit, at decision level 0).
   *
   * @param n - a theory atom with a SAT literal assigned; must have
   * been pre-registered
   * @param phase - the phase to decide on n
   */
  virtual void requirePhase(TNode n, bool phase)
    throw(Interrupted, TypeCheckingExceptionPrivate, AssertionException, UnsafeInterruptException) = 0;

  /**
   * Flips the most recent unflipped decision to the other phase and
   * returns true.  If all decisions have been flipped, the root
   * decision is re-flipped and flipDecision() returns false.  If no
   * decisions (flipped nor unflipped) are on the decision stack, the
   * state is not affected and flipDecision() returns false.
   *
   * For example, if l1, l2, and l3 are all decision literals, and
   * have been decided in positive phase, a series of flipDecision()
   * calls has the following effects:
   *
   * l1 l2 l3 <br/>
   * l1 l2 ~l3 <br/>
   * l1 ~l2 <br/>
   * ~l1 <br/>
   * l1 (and flipDecision() returns false)
   *
   * Naturally, flipDecision() might be interleaved with search.  For example:
   *
   * l1 l2 l3 <br/>
   * flipDecision() <br/>
   * l1 l2 ~l3 <br/>
   * flipDecision() <br/>
   * l1 ~l2 <br/>
   * SAT decides l3 <br/>
   * l1 ~l2 l3 <br/>
   * flipDecision() <br/>
   * l1 ~l2 ~l3 <br/>
   * flipDecision() <br/>
   * ~l1 <br/>
   * SAT decides l2 <br/>
   * ~l1 l2 <br/>
   * flipDecision() <br/>
   * ~l1 ~l2 <br/>
   * flipDecision() returns FALSE<br/>
   * l1
   *
   * @return true if a decision was flipped; false if no decision
   * could be flipped, or if the root decision was re-flipped
   */
  virtual bool flipDecision()
    throw(Interrupted, TypeCheckingExceptionPrivate, AssertionException, UnsafeInterruptException) = 0;

  /**
   * Notification from a theory that it realizes it is incomplete at
   * this context level.  If SAT is later determined by the
   * TheoryEngine, it should actually return an UNKNOWN result.
   */
  virtual void setIncomplete() throw(AssertionException, UnsafeInterruptException) = 0;

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
  virtual void spendResource(unsigned ammount) throw(UnsafeInterruptException) {}

  /**
   * Handle user attribute.
   * Associates theory t with the attribute attr.  Theory t will be
   * notified whenever an attribute of name attr is set on a node.
   * This can happen through, for example, the SMT-LIBv2 language.
   */
  virtual void handleUserAttribute(const char* attr, Theory* t) {}


  /** Demands that the search restart from sat search level 0.
   * Using this leads to non-termination issues.
   * It is appropriate for prototyping for theories.
   */
  virtual void demandRestart() throw(TypeCheckingExceptionPrivate, AssertionException, UnsafeInterruptException) {}

};/* class OutputChannel */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__OUTPUT_CHANNEL_H */
