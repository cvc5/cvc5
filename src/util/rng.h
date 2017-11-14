/*********************                                                        */
/*! \file rng.h
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

#ifndef __CVC4__RNG_H
#define __CVC4__RNG_H

namespace CVC4 {

class RNG
{
 public:
  RNG(RNG const&) = delete;
  void operator=(RNG const&) = delete;

  /* Get current RNG (singleton).  */
  static RNG& getRNG()
  {
    static RNG s_current(0);
    return s_current;
  }

  /* Set seed of RNG.  */
  void setSeed(uint64_t seed)
  {
    d_seed = seed;
    d_state = seed;
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
  RNG(uint64_t seed) : d_seed(seed), d_state(seed) {}
  /* The seed of the RNG. */
  uint64_t d_seed;
  /* The current state of the RNG. */
  uint64_t d_state;
};

}  // namespace CVC4
#endif
