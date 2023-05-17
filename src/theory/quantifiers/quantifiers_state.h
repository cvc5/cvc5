/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for quantifiers state.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_STATE_H
#define CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_STATE_H

#include "theory/quantifiers/quantifiers_statistics.h"
#include "theory/theory.h"
#include "theory/theory_state.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * The quantifiers state.
 */
class QuantifiersState : public TheoryState
{
 public:
  QuantifiersState(Env& env,
                   Valuation val,
                   const LogicInfo& logicInfo);
  ~QuantifiersState() {}
  /**
   * Increment the instantiation counters, called once at the beginning of when
   * we perform a check with quantifiers engine for the given effort.
   */
  void incrementInstRoundCounters(Theory::Effort e);
  /**
   * Get whether we need to check at effort e based on the inst-when mode. This
   * option determines the policy of quantifier instantiation and theory
   * combination, e.g. does it run before, after, or interleaved with theory
   * combination. This is based on the state of the counters maintained by this
   * class.
   */
  bool getInstWhenNeedsCheck(Theory::Effort e) const;
  /** Get the number of instantiation rounds performed in this SAT context */
  uint64_t getInstRoundDepth() const;
  /** Get the total number of instantiation rounds performed */
  uint64_t getInstRounds() const;
  /** debug print equality engine on trace c */
  void debugPrintEqualityEngine(const char* c) const;
  /** get the logic info */
  const LogicInfo& getLogicInfo() const;
  /** get the stats */
  QuantifiersStatistics& getStats();

 private:
  /** The number of instantiation rounds in this SAT context */
  context::CDO<uint64_t> d_ierCounterc;
  /** The number of total instantiation rounds (full effort) */
  uint64_t d_ierCounter;
  /** The number of total instantiation rounds (last call effort) */
  uint64_t d_ierCounterLc;
  /**
   * A counter to remember the last value of d_ierCounterLc where we a
   * full effort check. This is used for interleaving theory combination
   * and quantifier instantiation rounds.
   */
  uint64_t d_ierCounterLastLc;
  /**
   * The number of instantiation rounds we run for each call to theory
   * combination.
   */
  uint64_t d_instWhenPhase;
  /** Information about the logic we're operating within. */
  const LogicInfo& d_logicInfo;
  /** The statistics */
  QuantifiersStatistics d_statistics;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_STATE_H */
