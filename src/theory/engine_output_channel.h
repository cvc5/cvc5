/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory engine output channel.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ENGINE_OUTPUT_CHANNEL_H
#define CVC5__THEORY__ENGINE_OUTPUT_CHANNEL_H

#include "expr/node.h"
#include "theory/output_channel.h"
#include "theory/theory_id.h"
#include "util/statistics_stats.h"

namespace cvc5 {

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
class EngineOutputChannel : public theory::OutputChannel
{
  friend class TheoryEngine;

 public:
  EngineOutputChannel(TheoryEngine* engine, theory::TheoryId theory);

  void safePoint(Resource r) override;

  void conflict(TNode conflictNode) override;
  bool propagate(TNode literal) override;

  void lemma(TNode lemma, LemmaProperty p = LemmaProperty::NONE) override;

  void demandRestart() override;

  void requirePhase(TNode n, bool phase) override;

  void setIncomplete(IncompleteId id) override;

  void spendResource(Resource r) override;

  /**
   * Let pconf be the pair (Node conf, ProofGenerator * pfg). This method
   * sends conf on the output channel of this class whose proof can be generated
   * by the generator pfg. Apart from pfg, the interface for this method is
   * the same as calling OutputChannel::lemma on conf.
   */
  void trustedConflict(TrustNode pconf) override;
  /**
   * Let plem be the pair (Node lem, ProofGenerator * pfg).
   * Send lem on the output channel of this class whose proof can be generated
   * by the generator pfg. Apart from pfg, the interface for this method is
   * the same as calling OutputChannel::lemma on lem.
   */
  void trustedLemma(TrustNode plem,
                    LemmaProperty p = LemmaProperty::NONE) override;

 protected:
  /**
   * Statistics for a particular theory.
   */
  class Statistics
  {
   public:
    Statistics(theory::TheoryId theory);
    /** Number of calls to conflict, propagate, lemma, requirePhase,
     * restartDemands */
    IntStat conflicts, propagations, lemmas, requirePhase, restartDemands,
        trustedConflicts, trustedLemmas;
  };
  /** The theory engine we're communicating with. */
  TheoryEngine* d_engine;
  /** The statistics of the theory interractions. */
  Statistics d_statistics;
  /** The theory owning this channel. */
  theory::TheoryId d_theory;
  /** A helper function for registering lemma recipes with the proof engine */
  void registerLemmaRecipe(Node lemma,
                           Node originalLemma,
                           bool preprocess,
                           theory::TheoryId theoryId);
};

}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__ENGINE_OUTPUT_CHANNEL_H */
