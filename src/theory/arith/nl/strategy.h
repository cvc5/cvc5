/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Yoni Zohar, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Strategies for the nonlinear extension.
 */

#ifndef CVC5__THEORY__ARITH__NL__STRATEGY_H
#define CVC5__THEORY__ARITH__NL__STRATEGY_H

#include <iosfwd>
#include <vector>

#include "options/options.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

/** The possible inference steps for the nonlinear extension */
enum class InferStep
{
  /** Break if any lemma is pending */
  BREAK,
  /** Flush waiting lemmas to be pending */
  FLUSH_WAITING_LEMMAS,

  /** Initialize the coverings solver */
  COVERINGS_INIT,
  /** A full coverings check */
  COVERINGS_FULL,

  /** Initialize the IAND solver */
  IAND_INIT,
  /** A full IAND check */
  IAND_FULL,
  /** An initial IAND check */
  IAND_INITIAL,

  /** Initialize the POW2 solver */
  POW2_INIT,
  /** A full POW2 check */
  POW2_FULL,
  /** An initial POW2 check */
  POW2_INITIAL,

  /** An ICP check */

  ICP,

  /** Initialize the NL solver */
  NL_INIT,
  /** Nl factoring lemmas */
  NL_FACTORING,
  /** Nl lemmas for monomial bound inference */
  NL_MONOMIAL_INFER_BOUNDS,
  /** Nl lemmas for monomial magnitudes (class 0) */
  NL_MONOMIAL_MAGNITUDE0,
  /** Nl lemmas for monomial magnitudes (class 1) */
  NL_MONOMIAL_MAGNITUDE1,
  /** Nl lemmas for monomial magnitudes (class 2) */
  NL_MONOMIAL_MAGNITUDE2,
  /** Nl lemmas for monomial signs */
  NL_MONOMIAL_SIGN,
  /** Nl lemmas for resolution bounds */
  NL_RESOLUTION_BOUNDS,
  /** Nl splitting at zero */
  NL_SPLIT_ZERO,
  /** Nl tangent plane lemmas */
  NL_TANGENT_PLANES,
  /** Nl tangent plane lemmas as waiting lemmas */
  NL_TANGENT_PLANES_WAITING,

  /** Initialize the transcendental solver */
  TRANS_INIT,
  /** Initial transcendental lemmas */
  TRANS_INITIAL,
  /** Monotonicity lemmas from transcendental solver */
  TRANS_MONOTONIC,
  /** Tangent planes from transcendental solver */
  TRANS_TANGENT_PLANES,
};

/** Streaming operator for InferStep */
std::ostream& operator<<(std::ostream& os, InferStep step);

/** A sequence of steps */
using StepSequence = std::vector<InferStep>;

/**
 * Stores an interleaving of multiple StepSequences.
 *
 * Every Branch of the interleaving holds a StepSequence s_i and a constant c_i.
 * Once initialized, the interleaving may be asked repeatedly for a
 * StepSequence. Repeated calls cycle through the branches, but will return
 * every branch repeatedly as specified by its constant.
 *
 * Let for example [(s_1, 1), (s_2, 2), (s_3, 1)], then the sequence returned by
 * get() would be: s_1, s_2, s_2, s_3, s_1, s_2, s_2, s_3, ...
 */
class Interleaving
{
 public:
  /** Add a new branch to this interleaving */
  void add(const StepSequence& ss, std::size_t constant = 1);
  /**
   * Reset the counter to start from the first branch for the next get() call
   */
  void resetCounter();
  /** Retrieve the next branch */
  const StepSequence& get();
  /** Check whether this interleaving is empty */
  bool empty() const;

 private:
  /** Represents a single branch in an interleaving */
  struct Branch
  {
    StepSequence d_steps;
    std::size_t d_interleavingConstant;
  };
  /** The current counter of get() calls */
  std::size_t d_counter = 0;
  /** The overall size of interleaving (considering constants) */
  std::size_t d_size = 0;
  /** The branches */
  std::vector<Branch> d_branches;
};

/**
 * A small wrapper around a StepSequence.
 *
 * This class makes handling a StepSequence slightly more convenient.
 * Also, it may help wrapping a more flexible strategy implementation in the
 * future.
 */
class StepGenerator
{
 public:
  StepGenerator(const StepSequence& ss) : d_steps(ss) {}
  /** Check if there is another step */
  bool hasNext() const;
  /** Get the next step */
  InferStep next();

 private:
  /** The StepSequence to process */
  const StepSequence& d_steps;
  /** The next step */
  std::size_t d_next = 0;
};

/**
 * A strategy for the nonlinear extension
 *
 * A strategy consists of multiple step sequences that are interleaved for every
 * Theory::Effort. The initialization creates the strategy. Calling
 * getStrategy() yields a StepGenerator that produces a sequence of InferSteps.
 */
class Strategy
{
 public:
  /** Is this strategy initialized? */
  bool isStrategyInit() const;
  /** Initialize this strategy */
  void initializeStrategy(const Options& options);
  /** Retrieve the strategy for the given effort e */
  StepGenerator getStrategy();

 private:
  /** The interleaving for this strategy */
  Interleaving d_interleaving;
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__NL__STRATEGY_H */
