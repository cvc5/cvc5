/*********************                                                        */
/*! \file sampler.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sampler class that generates random values of different sorts
 **
 ** The Sampler class can be used to generate random values of different sorts
 ** with biased and unbiased distributions.
 **/

#include "util/sampler.h"

#include "base/check.h"
#include "util/bitvector.h"

namespace CVC4 {

BitVector Sampler::pickBvUniform(unsigned sz)
{
  Random& rnd = Random::getRandom();

  std::stringstream ss;
  for (unsigned i = 0; i < sz; i++)
  {
    ss << (rnd.pickWithProb(0.5) ? "1" : "0");
  }

  return BitVector(ss.str(), 2);
}

FloatingPoint Sampler::pickFpUniform(unsigned e, unsigned s)
{
  return FloatingPoint(e, s, pickBvUniform(e + s));
}

FloatingPoint Sampler::pickFpBiased(unsigned e, unsigned s)
{
  // The biased generation of random FP values is inspired by
  // PyMPF [0].
  //
  // [0] https://github.com/florianschanda/PyMPF

  Random& rnd = Random::getRandom();

  BitVector zero(1);
  BitVector one(1, static_cast<unsigned int>(1));

  BitVector sign(1);
  BitVector exp(e);
  BitVector sig(s - 1);

  if (rnd.pickWithProb(probSpecial))
  {
    // Generate special values

    uint64_t type = rnd.pick(0, 12);
    switch (type)
    {
      // NaN
      // sign = 1, exp = 11...11, sig = 11...11
      case 0:
        sign = one;
        exp = BitVector::mkOnes(e);
        sig = BitVector::mkOnes(s - 1);
        break;

      // +/- inf
      // sign = x, exp = 11...11, sig = 00...00
      case 1: sign = one; CVC4_FALLTHROUGH;
      case 2: exp = BitVector::mkOnes(e); break;

      // +/- zero
      // sign = x, exp = 00...00, sig = 00...00
      case 3: sign = one; CVC4_FALLTHROUGH;
      case 4: break;

      // +/- max subnormal
      // sign = x, exp = 00...00, sig = 11...11
      case 5: sign = one; CVC4_FALLTHROUGH;
      case 6: sig = BitVector::mkOnes(s - 1); break;

      // +/- min subnormal
      // sign = x, exp = 00...00, sig = 00...01
      case 7: sign = one; CVC4_FALLTHROUGH;
      case 8: sig = BitVector(s - 1, static_cast<unsigned int>(1)); break;

      // +/- max normal
      // sign = x, exp = 11...10, sig = 11...11
      case 9: sign = one; CVC4_FALLTHROUGH;
      case 10:
        exp = BitVector::mkOnes(e) - BitVector(e, static_cast<unsigned int>(1));
        sig = BitVector::mkOnes(s - 1);
        break;

      // +/- min normal
      // sign = x, exp = 00...01, sig = 00...00
      case 11: sign = one; CVC4_FALLTHROUGH;
      case 12: exp = BitVector(e, static_cast<unsigned int>(1)); break;

      default: Unreachable();
    }
  }
  else
  {
    // Generate normal and subnormal values

    // 50% chance of positive/negative sign
    if (rnd.pickWithProb(0.5))
    {
      sign = one;
    }

    uint64_t pattern = rnd.pick(0, 5);
    switch (pattern)
    {
      case 0:
        // sign = x, exp = xx...x0, sig = 11...11
        exp = pickBvUniform(e - 1).concat(zero);
        sig = BitVector::mkOnes(s - 1);
        break;

      case 1:
        // sign = x, exp = xx...x0, sig = 00...00
        exp = pickBvUniform(e - 1).concat(zero);
        break;

      case 2:
        // sign = x, exp = 0x...x1, sig = 11...11
        exp = zero.concat(pickBvUniform(e - 2).concat(one));
        sig = BitVector::mkOnes(s - 1);
        break;

      case 3:
        // sign = x, exp = xx...x0, sig = xx...xx
        exp = pickBvUniform(e - 1).concat(zero);
        sig = pickBvUniform(s - 1);
        break;

      case 4:
        // sign = x, exp = 0x...x1, sig = xx...xx
        exp = zero.concat(pickBvUniform(e - 2).concat(one));
        sig = pickBvUniform(s - 1);
        break;

      case 5:
      {
        // sign = x, exp = xx...xx0xx...xx, sig = xx...xx
        uint64_t lsbSize = rnd.pick(1, e - 2);
        uint64_t msbSize = e - lsbSize - 1;
        BitVector lsb = pickBvUniform(lsbSize);
        BitVector msb = pickBvUniform(msbSize);
        exp = msb.concat(zero.concat(lsb));
        sig = pickBvUniform(s - 1);
        break;
      }

      default: Unreachable();
    }
  }

  BitVector bv = sign.concat(exp.concat(sig));
  return FloatingPoint(e, s, bv);
}

}  // namespace CVC4
