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

#include "util/random.h"

#include "base/check.h"

namespace cvc5::internal {

Random::Random(uint64_t seed) { setSeed(seed); }

Random::~Random()
{
#ifdef CVC5_GMP_IMP
  gmp_randclear(d_gmp_randstate);
#endif
}

void Random::setSeed(uint64_t seed)
{
  d_seed = seed == 0 ? ~seed : seed;
  d_rng.seed(d_seed);
#ifdef CVC5_GMP_IMP
  gmp_randinit_mt(d_gmp_randstate);
  gmp_randseed_ui(d_gmp_randstate, d_seed);
#endif
#ifdef CVC5_CLN_IMP
  // cln::random_state stores a 64 bit seed split into 32-bit hi and lo parts.
  d_cln_randstate.seed.hi = static_cast<uint32_t>(d_seed >> 32);
  d_cln_randstate.seed.lo = static_cast<uint32_t>(d_seed);
#endif
}

uint64_t Random::operator()() { return d_rng(); }

bool Random::pickWithProb(double probability)
{
  Assert(probability <= 1);
  Assert(probability >= 0);
  uint64_t p = (uint64_t)(probability * 1000);
  uint64_t r = pick<uint64_t>(0, 999);
  return r < p;
}

}  // namespace cvc5::internal
