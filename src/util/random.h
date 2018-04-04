/*********************                                                        */
/*! \file random.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A Random Number Generator.
 **
 ** A random number generator, implements the xorshift* generator
 ** (see S. Vigna, An experimental exploration of Marsaglia's xorshift
 ** generators, scrambled. ACM Trans. Math. Softw. 42(4): 30:1-30:23, 2016).
 **/

#include "cvc4_private.h"

#ifndef __CVC4__UTIL__RANDOM_H
#define __CVC4__UTIL__RANDOM_H

#include "base/tls.h"

namespace CVC4 {

class Random
{
 public:
  Random(uint64_t seed) { setSeed(seed); }

  /* Get current RNG (singleton).  */
  static Random& getRandom()
  {
    static CVC4_THREAD_LOCAL Random s_current(0);
    return s_current;
  }

  /* Set seed of Random.  */
  void setSeed(uint64_t seed)
  {
    d_seed = seed == 0 ? ~seed : seed;
    d_state = d_seed;
  }

  /* Next random uint64_t number. */
  uint64_t rand();
  /* Pick random uint64_t number between from and to (inclusive). */
  uint64_t pick(uint64_t from, uint64_t to);
  /* Pick random double number between from and to (inclusive). */
  double pickDouble(double from, double to);
  /* Pick with given probability (yes / no). */
  bool pickWithProb(double probability);

 private:
  /* The seed of the RNG. */
  uint64_t d_seed;
  /* The current state of the RNG. */
  uint64_t d_state;
};

}  // namespace CVC4
#endif
