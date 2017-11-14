#include "util/rng.h"

#include <cfloat>
#include "base/cvc4_assert.h"

namespace CVC4 {

uint64_t RNG::rand()
{
  /* xorshift* generator (see S. Vigna, An experimental exploration of
   * Marsaglia's xorshift generators, scrambled. ACM Trans. Math. Softw.
   * 42(4): 30:1-30:23, 2016). */
  d_state ^= d_state >> 12;
  d_state ^= d_state << 25;
  d_state ^= d_state >> 27;
  d_state *= UINT64_C(2685821657736338717);
  return d_state;
}

uint64_t RNG::pick(uint64_t from, uint64_t to)
{
  Assert(from <= to);
  Assert(to <= UINT64_MAX);
  from = from == UINT64_MAX ? UINT64_MAX - 1 : from;
  to = to == UINT64_MAX ? UINT64_MAX - 1 : to;
  return (RNG::rand() % (to - from + 1)) + from;
}

double RNG::pickDouble(double from, double to)
{
  Assert(from <= to);
  Assert(to <= DBL_MAX);
  return RNG::rand() * (to - from ) + from;
}

bool RNG::pickWithProb(double probability)
{
  Assert(probability <= 1);
  uint64_t p = (uint64_t) (probability * 1000);
  uint64_t r = pick(0, 1000);
  return r < p;
}

}
