/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A random number generator, implements the xorshift* generator
 * (see S. Vigna, An experimental exploration of Marsaglia's xorshift
 * generators, scrambled. ACM Trans. Math. Softw. 42(4): 30:1-30:23, 2016).
 */

#include "cvc5_private.h"

#ifndef CVC5__UTIL__RANDOM_H
#define CVC5__UTIL__RANDOM_H

namespace cvc5::internal {

class Random
{
 public:
  using result_type = uint64_t;

  /** Constructor. */
  Random(uint64_t seed);

  /** Get current RNG (singleton).  */
  static Random& getRandom()
  {
    static thread_local Random s_current(0);
    return s_current;
  }

  /** Get the minimum number that can be picked. */
  static constexpr uint64_t min() { return 0u; }

  /** Get the maximum number that can be picked. */
  static constexpr uint64_t max() { return UINT64_MAX; }

  /** Set seed of Random.  */
  void setSeed(uint64_t seed);

  /** Operator overload to pick random uin64_t number (see rand()). */
  uint64_t operator()();

  /** Next random uint64_t number. */
  uint64_t rand();

  /** Pick random uint64_t number between from and to (inclusive). */
  uint64_t pick(uint64_t from, uint64_t to);

  /** Pick random double number between from and to (inclusive). */
  double pickDouble(double from, double to);

  /** Pick with given probability (yes / no). */
  bool pickWithProb(double probability);

 private:
  /* The seed of the RNG. */
  uint64_t d_seed;
  /* The current state of the RNG. */
  uint64_t d_state;
};

}  // namespace cvc5::internal
#endif
