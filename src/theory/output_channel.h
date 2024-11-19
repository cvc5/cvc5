/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory engine output channel.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__OUTPUT_CHANNEL_H
#define CVC5__THEORY__OUTPUT_CHANNEL_H

#include "expr/node.h"
#include "proof/trust_node.h"
#include "theory/incomplete_id.h"
#include "theory/inference_id.h"
#include "theory/lemma_property.h"
#include "theory/theory_id.h"
#include "util/resource_manager.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {

class TheoryEngine;

namespace theory {

class Theory;

/**
 * An output channel for Theory that passes messages back to a TheoryEngine
 * for a given Theory.
 *
 * Notice that it has interfaces trustedConflict and trustedLemma which are
 * used for ensuring that proof generators are associated with the lemmas
 * and conflicts sent on this output channel.
 */
class OutputChannel
{
  friend class internal::TheoryEngine;

 public:
  /** Default constructor */
  OutputChannel();
  /** Constructor for use by theory */
  OutputChannel(StatisticsRegistry& sr,
                TheoryEngine* engine,
                theory::TheoryId theory);
  /** Constructor for use by non-theory */
  OutputChannel(StatisticsRegistry& sr,
                TheoryEngine* engine,
                const std::string& name,
                size_t id = 0);
  virtual ~OutputChannel() {}

  /**
   * With safePoint(), the theory signals that it is at a safe point
   * and can be interrupted.
   *
   * @throws Interrupted if the theory can be safely interrupted.
   */
  virtual void safePoint(Resource r);
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
  virtual void conflict(TNode conflictNode, InferenceId id);
  /**
   * Propagate a theory literal.
   *
   * @param n - a theory consequence at the current decision level
   * @return false if an immediate conflict was encountered
   */
  virtual bool propagate(TNode literal);

  /**
   * Tell the core that a valid theory lemma at decision level 0 has
   * been detected.  (This requests a split.)
   *
   * @param n - a theory lemma valid at decision level 0
   * @param p The properties of the lemma
   */
  virtual void lemma(TNode lemma,
                     InferenceId id,
                     LemmaProperty p = LemmaProperty::NONE);
  /**
   * If a decision is made on n that is not requested from a theory, it must be
   * in the phase specified. Note that this is enforced *globally*, i.e., it is
   * completely context-INdependent.  If you ever preferPhase() on a literal,
   * it is phase-locked forever and ever.  If it is to ever have the
   * other phase as its assignment, it will be because it has been
   * propagated that way (or it's a unit, at decision level 0).
   *
   * @param n - a theory atom with a SAT literal assigned; must have
   * been pre-registered
   * @param phase - the phase to decide on n
   */
  virtual void preferPhase(TNode n, bool phase);
  /**
   * Notification from a theory that it realizes it is model unsound at
   * this SAT context level.  If SAT is later determined by the
   * TheoryEngine, it should actually return an UNKNOWN result.
   */
  virtual void setModelUnsound(IncompleteId id);
  /**
   * Notification from a theory that it realizes it is refutation unsound at
   * this user context level.  If UNSAT is later determined by the
   * TheoryEngine, it should actually return an UNKNOWN result.
   */
  virtual void setRefutationUnsound(IncompleteId id);
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
  virtual void spendResource(Resource r);

  /**
   * Let pconf be the pair (Node conf, ProofGenerator * pfg). This method
   * sends conf on the output channel of this class whose proof can be generated
   * by the generator pfg. Apart from pfg, the interface for this method is
   * the same as calling OutputChannel::lemma on conf.
   */
  virtual void trustedConflict(TrustNode pconf, InferenceId id);
  /**
   * Let plem be the pair (Node lem, ProofGenerator * pfg).
   * Send lem on the output channel of this class whose proof can be generated
   * by the generator pfg. Apart from pfg, the interface for this method is
   * the same as calling OutputChannel::lemma on lem.
   */
  virtual void trustedLemma(TrustNode plem,
                            InferenceId id,
                            LemmaProperty p = LemmaProperty::NONE);
  /**
   * Get the theory identifier
   */
  TheoryId getId() const;

 protected:
  /**
   * Statistics for a particular theory.
   */
  class Statistics
  {
   public:
    Statistics();
    Statistics(StatisticsRegistry& sr, const std::string& statPrefix);
    /** Number of calls to conflict, propagate, lemma, preferPhase */
    IntStat conflicts, propagations, lemmas, preferPhase, trustedConflicts,
        trustedLemmas;
  };
  /** The theory engine we're communicating with. */
  TheoryEngine* d_engine;
  /** The name of the owner of this channel. */
  std::string d_name;
  /** The statistics of the theory interractions. */
  Statistics d_statistics;
  /** The theory owning this channel. */
  theory::TheoryId d_theory;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__OUTPUT_CHANNEL_H */
