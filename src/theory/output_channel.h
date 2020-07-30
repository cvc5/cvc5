/*********************                                                        */
/*! \file output_channel.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The theory output channel interface
 **
 ** The theory output channel interface.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__OUTPUT_CHANNEL_H
#define CVC4__THEORY__OUTPUT_CHANNEL_H

#include <memory>

#include "expr/proof_node.h"
#include "proof/proof_manager.h"
#include "smt/logic_exception.h"
#include "theory/interrupted.h"
#include "theory/trust_node.h"
#include "util/proof.h"
#include "util/resource_manager.h"

namespace CVC4 {
namespace theory {

/** Properties of lemmas */
enum class LemmaProperty : uint32_t
{
  // default
  NONE = 0,
  // whether the lemma is removable
  REMOVABLE = 1,
  // whether the lemma needs preprocessing
  PREPROCESS = 2,
  // whether the processing of the lemma should send atoms to the caller
  SEND_ATOMS = 4
};
/** Define operator lhs | rhs */
LemmaProperty operator|(LemmaProperty lhs, LemmaProperty rhs);
/** Define operator lhs |= rhs */
LemmaProperty& operator|=(LemmaProperty& lhs, LemmaProperty rhs);
/** Define operator lhs & rhs */
LemmaProperty operator&(LemmaProperty lhs, LemmaProperty rhs);
/** Define operator lhs &= rhs */
LemmaProperty& operator&=(LemmaProperty& lhs, LemmaProperty rhs);
/** is the removable bit set on p? */
bool isLemmaPropertyRemovable(LemmaProperty p);
/** is the preprocess bit set on p? */
bool isLemmaPropertyPreprocess(LemmaProperty p);
/** is the send atoms bit set on p? */
bool isLemmaPropertySendAtoms(LemmaProperty p);

/**
 * Writes an lemma property name to a stream.
 *
 * @param out The stream to write to
 * @param p The lemma property to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, LemmaProperty p);

class Theory;

/**
 * A LemmaStatus, returned from OutputChannel::lemma(), provides information
 * about the lemma added.  In particular, it contains the T-rewritten lemma
 * for inspection and the user-level at which the lemma will reside.
 */
class LemmaStatus {
 public:
  LemmaStatus(TNode rewrittenLemma, unsigned level);

  /** Get the T-rewritten form of the lemma. */
  TNode getRewrittenLemma() const;
  /**
   * Get the user-level at which the lemma resides.  After this user level
   * is popped, the lemma is un-asserted from the SAT layer.  This level
   * will be 0 if the lemma didn't reach the SAT layer at all.
   */
  unsigned getLevel() const;

 private:
  Node d_rewrittenLemma;
  unsigned d_level;
}; /* class LemmaStatus */

/**
 * Generic "theory output channel" interface.
 *
 * All methods can throw unrecoverable CVC4::Exception's unless otherwise
 * documented.
 */
class OutputChannel {
 public:
  /** Construct an OutputChannel. */
  OutputChannel() {}

  /**
   * Destructs an OutputChannel.  This implementation does nothing,
   * but we need a virtual destructor for safety in case subclasses
   * have a destructor.
   */
  virtual ~OutputChannel() {}

  OutputChannel(const OutputChannel&) = delete;
  OutputChannel& operator=(const OutputChannel&) = delete;

  /**
   * With safePoint(), the theory signals that it is at a safe point
   * and can be interrupted.
   *
   * @throws Interrupted if the theory can be safely interrupted.
   */
  virtual void safePoint(ResourceManager::Resource r) {}

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
  virtual void conflict(TNode n, std::unique_ptr<Proof> pf = nullptr) = 0;

  /**
   * Propagate a theory literal.
   *
   * @param n - a theory consequence at the current decision level
   * @return false if an immediate conflict was encountered
   */
  virtual bool propagate(TNode n) = 0;

  /**
   * Tell the core that a valid theory lemma at decision level 0 has
   * been detected.  (This requests a split.)
   *
   * @param n - a theory lemma valid at decision level 0
   * @param rule - the proof rule for this lemma
   * @param p The properties of the lemma
   * @return the "status" of the lemma, including user level at which
   * the lemma resides; the lemma will be removed when this user level pops
   */
  virtual LemmaStatus lemma(TNode n,
                            ProofRule rule,
                            LemmaProperty p = LemmaProperty::NONE) = 0;

  /**
   * Variant of the lemma function that does not require providing a proof rule.
   */
  virtual LemmaStatus lemma(TNode n, LemmaProperty p = LemmaProperty::NONE);

  /**
   * Request a split on a new theory atom.  This is equivalent to
   * calling lemma({OR n (NOT n)}).
   *
   * @param n - a theory atom; must be of Boolean type
   */
  LemmaStatus split(TNode n);

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
  virtual void requirePhase(TNode n, bool phase) = 0;

  /**
   * Notification from a theory that it realizes it is incomplete at
   * this context level.  If SAT is later determined by the
   * TheoryEngine, it should actually return an UNKNOWN result.
   */
  virtual void setIncomplete() = 0;

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
  virtual void spendResource(ResourceManager::Resource r) {}

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
  virtual void demandRestart() {}

  //---------------------------- new proof
  /**
   * Let pconf be the pair (Node conf, ProofGenerator * pfg). This method
   * sends conf on the output channel of this class whose proof can be generated
   * by the generator pfg. Apart from pfg, the interface for this method is
   * the same as OutputChannel.
   */
  virtual void trustedConflict(TrustNode pconf);
  /**
   * Let plem be the pair (Node lem, ProofGenerator * pfg).
   * Send lem on the output channel of this class whose proof can be generated
   * by the generator pfg. Apart from pfg, the interface for this method is
   * the same as OutputChannel.
   */
  virtual LemmaStatus trustedLemma(TrustNode lem,
                                   LemmaProperty p = LemmaProperty::NONE);
  //---------------------------- end new proof
}; /* class OutputChannel */

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__OUTPUT_CHANNEL_H */
