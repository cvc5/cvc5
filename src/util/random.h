/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A random number generator, based on the Mersenne-Twister engine.
 */

#ifndef CVC5__UTIL__RANDOM_H
#define CVC5__UTIL__RANDOM_H

#include <random>
#include <type_traits>

#include "base/check.h"
#include "cvc5_private.h"

#ifdef CVC5_GMP_IMP
#include <gmpxx.h>
#endif
#ifdef CVC5_CLN_IMP
#include <cln/random.h>
#endif

namespace cvc5::internal {

class Random
{
 public:
  using result_type = uint64_t;

  /** Constructor. */
  Random(uint64_t seed);
  /** Destructor. */
  ~Random();

  Random(const Random& rng) = delete;
  Random& operator=(const Random& rng) = delete;

  /** Get current RNG (singleton).  */
  static Random& getRandom()
  {
    static thread_local Random s_current(0);
    return s_current;
  }

  /** Get the minimum number that can be picked. */
  static constexpr uint64_t min() { return std::mt19937_64::min(); }

  /** Get the maximum number that can be picked. */
  static constexpr uint64_t max() { return std::mt19937_64::max(); }

  /** Set seed of Random.  */
  void setSeed(uint64_t seed);

  /** Operator overload to pick random uint64_t number. */
  uint64_t operator()();

  /** Pick an integral number with type T. */
  template <typename T,
            typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
  T pick()
  {
    std::uniform_int_distribution<T> dist;
    return dist(d_rng);
  }

  /**
   * Pick an integral number with type T between 'from' and 'to' (inclusive).
   */
  template <typename T,
            typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
  T pick(T from, T to)
  {
    Assert(from <= to);
    std::uniform_int_distribution<T> dist(from, to);
    return dist(d_rng);
  }

  /** Pick a floating point number with type T. */
  template <
      typename T,
      typename std::enable_if<std::is_floating_point<T>::value, int>::type = 0>
  T pick()
  {
    std::uniform_real_distribution<T> dist;
    return dist(d_rng);
  }

  /** Pick a floating point number with type T between 'from' and 'to'
   * ([from, to), upper bound exclusive). */
  template <
      typename T,
      typename std::enable_if<std::is_floating_point<T>::value, int>::type = 0>
  T pick(T from, T to)
  {
    Assert(from <= to);
    std::uniform_real_distribution<T> dist(from, to);
    return dist(d_rng);
  }

  /** Pick with given probability (yes / no). */
  bool pickWithProb(double probability);

#ifdef CVC5_GMP_IMP
  gmp_randstate_t* getGMPRandstate() { return &d_gmp_randstate; }
#endif
#ifdef CVC5_CLN_IMP
  cln::random_state* getCLNRandstate() { return &d_cln_randstate; }
#endif

 private:
  /* The seed of the RNG. */
  uint64_t d_seed;
  /** The underlying RNG Mersenne Twister engine. */
  std::mt19937_64 d_rng;

#ifdef CVC5_GMP_IMP
  gmp_randstate_t d_gmp_randstate;
#endif
#ifdef CVC5_CLN_IMP
  cln::random_state d_cln_randstate;
#endif
};

}  // namespace cvc5::internal
#endif
