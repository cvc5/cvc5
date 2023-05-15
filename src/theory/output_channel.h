/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory output channel interface.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__OUTPUT_CHANNEL_H
#define CVC5__THEORY__OUTPUT_CHANNEL_H

#include "proof/trust_node.h"
#include "theory/incomplete_id.h"
#include "util/resource_manager.h"

namespace cvc5::internal {
namespace theory {

/** Properties of lemmas */
enum class LemmaProperty : uint32_t
{
  // default
  NONE = 0,
  // whether the lemma is removable
  REMOVABLE = 1,
  // whether the processing of the lemma should send atoms to the caller
  SEND_ATOMS = 2,
  // whether the lemma is part of the justification for answering "sat"
  NEEDS_JUSTIFY = 4
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
/** is the send atoms bit set on p? */
bool isLemmaPropertySendAtoms(LemmaProperty p);
/** is the needs justify bit set on p? */
bool isLemmaPropertyNeedsJustify(LemmaProperty p);

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
 * Generic "theory output channel" interface.
 *
 * All methods can throw unrecoverable cvc5::internal::Exception's unless otherwise
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
  virtual void safePoint(Resource r) {}

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
  virtual void conflict(TNode n) = 0;

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
   * @param p The properties of the lemma
   */
  virtual void lemma(TNode n, LemmaProperty p = LemmaProperty::NONE) = 0;

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
   * Notification from a theory that it realizes it is model unsound at
   * this SAT context level.  If SAT is later determined by the
   * TheoryEngine, it should actually return an UNKNOWN result.
   */
  virtual void setModelUnsound(IncompleteId id) = 0;
  /**
   * Notification from a theory that it realizes it is refutation unsound at
   * this user context level.  If UNSAT is later determined by the
   * TheoryEngine, it should actually return an UNKNOWN result.
   */
  virtual void setRefutationUnsound(IncompleteId id) = 0;

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
  virtual void spendResource(Resource r) {}

  /**
   * Handle user attribute.
   * Associates theory t with the attribute attr.  Theory t will be
   * notified whenever an attribute of name attr is set on a node.
   * This can happen through, for example, the SMT-LIBv2 language.
   */
  virtual void handleUserAttribute(const char* attr, Theory* t) {}

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
  virtual void trustedLemma(TrustNode lem,
                            LemmaProperty p = LemmaProperty::NONE);
  //---------------------------- end new proof
}; /* class OutputChannel */

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__OUTPUT_CHANNEL_H */
