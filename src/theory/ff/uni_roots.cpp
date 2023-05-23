/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Root finding for univariate polynomials in prime fields.
 *
 * Uses CoCoA for word-sized fields.
 *
 * Implements Rabin root-finding for larger ones.
 *
 * Reference: https://en.wikipedia.org/wiki/Berlekamp%E2%80%93Rabin_algorithm
 */

#ifdef CVC5_USE_COCOA

#include "theory/ff/uni_roots.h"

#include <CoCoA/BigInt.H>
#include <CoCoA/BigIntOps.H>
#include <CoCoA/PolyRing.H>
#include <CoCoA/RingZZ.H>
#include <CoCoA/SmallFpImpl.H>
#include <CoCoA/SparsePolyOps-RingElem.H>
#include <CoCoA/SparsePolyOps-vector.H>
#include <CoCoA/factor.H>
#include <CoCoA/factorization.H>
#include <CoCoA/random.H>
#include <CoCoA/ring.H>

#include <sstream>
#include <unordered_map>
#include <vector>

#include "smt/assertions.h"
#include "base/output.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

CoCoA::RingElem redMod(CoCoA::RingElem b, CoCoA::RingElem m)
{
  std::vector<CoCoA::RingElem> mm = {m};
  return CoCoA::NR(b, mm);
}

CoCoA::RingElem powerMod(CoCoA::RingElem b, CoCoA::BigInt e, CoCoA::RingElem m)
{
  CoCoA::RingElem acc = CoCoA::owner(b)->myOne();
  CoCoA::RingElem bPower = b;
  while (!CoCoA::IsZero(e))
  {
    if (CoCoA::IsOdd(e))
    {
      acc *= bPower;
      acc = redMod(acc, m);
    }
    bPower *= bPower;
    bPower = redMod(bPower, m);
    e /= 2;
  }
  return acc;
}

CoCoA::RingElem distinctRootsPoly(CoCoA::RingElem f)
{
  CoCoA::ring ring = CoCoA::owner(f);
  CoCoA::ring field = CoCoA::owner(f)->myBaseRing();
  int idx = CoCoA::UnivariateIndetIndex(f);
  Assert(idx >= 0);
  CoCoA::RingElem x = CoCoA::indet(ring, idx);
  CoCoA::BigInt q =
      CoCoA::power(CoCoA::characteristic(field), CoCoA::LogCardinality(field));
  CoCoA::RingElem fieldPoly = powerMod(x, q, f) - x;
  return gcd(f, fieldPoly);
}

template <typename T>
std::string sstring(const T& t)
{
  std::ostringstream o;
  o << t;
  return o.str();
}

// sorting based on strings because CoCoA can't compare field elements:
// it doesn't regard a integer quotient ring as an ordered domain.
std::vector<CoCoA::RingElem> sortHack(
    const std::vector<CoCoA::RingElem>& values)
{
  std::vector<std::string> strs;
  std::unordered_map<std::string, size_t> origIndices;
  for (const auto& v : values)
  {
    std::string s = sstring(v);
    origIndices.emplace(s, strs.size());
    strs.push_back(s);
  }
  std::sort(strs.begin(), strs.end());
  std::vector<CoCoA::RingElem> output;
  for (const auto& s : strs)
  {
    output.push_back(values[origIndices[s]]);
  }
  return output;
}

std::vector<CoCoA::RingElem> roots(CoCoA::RingElem f)
{
  CoCoA::ring ring = CoCoA::owner(f);
  CoCoA::ring field = CoCoA::owner(f)->myBaseRing();
  int idx = CoCoA::UnivariateIndetIndex(f);
  Assert(idx >= 0);
  CoCoA::RingElem x = CoCoA::indet(ring, idx);
  CoCoA::BigInt q = CoCoA::characteristic(field);
  std::vector<CoCoA::RingElem> output;

  // CoCoA has a good factorization routine, but it only works for small fields.
  bool isSmall = false;
  {
    // I don't know how to check directly if their small field impl applies, so
    // we try.
    try
    {
      CoCoA::SmallFpImpl ModP(CoCoA::ConvertTo<long>(q));
      isSmall = true;
    }
    catch (const CoCoA::ErrorInfo&)
    {
    }
  }
  if (isSmall)
  {
    // Use CoCoA
    const auto factors = CoCoA::factor(f);
    for (const auto& factor : factors.myFactors())
    {
      if (CoCoA::deg(factor) == 1)
      {
        Assert(CoCoA::IsOne(CoCoA::LC(factor)));
        output.push_back(-CoCoA::ConstantCoeff(factor));
      }
    }
  }
  else
  {
    // Rabin root finding

    // needed because of the random sampling below
    Assert(CoCoA::LogCardinality(field) == 1);
    Assert(CoCoA::IsOdd(q));
    CoCoA::BigInt s = q / 2;
    // Reduce the problem to factoring a product of linears
    std::vector<CoCoA::RingElem> toFactor{distinctRootsPoly(f)};
    while (toFactor.size())
    {
      // Grab a product of linears to factor
      CoCoA::RingElem p = toFactor.back();
      toFactor.pop_back();
      Trace("ff::roots") << "toFactor " << p << std::endl;
      if (CoCoA::deg(p) == 0)
      {
        // It's dead
      }
      else if (CoCoA::ConstantCoeff(p) == 0)
      {
        // It has a zero root
        output.push_back(CoCoA::ConstantCoeff(p));
        toFactor.push_back(p / x);
      }
      else if (CoCoA::deg(p) == 1)
      {
        // It is linear
        output.push_back(-CoCoA::ConstantCoeff(p));
      }
      else
      {
        // Its super-linear, without a zero
        while (true)
        {
          // guess random delta
          CoCoA::BigInt deltaInt = CoCoA::RandomBigInt(CoCoA::BigInt(0), q - 1);
          CoCoA::RingElem delta = CoCoA::RingElem(field, deltaInt);
          // Is the number of common roots with (x - delta)^(q/2) at least 1 and
          // less than all of them?
          CoCoA::RingElem h = gcd(p, powerMod(x - delta, s, p) - 1);
          if (0 < CoCoA::deg(h) && CoCoA::deg(h) < CoCoA::deg(p))
          {
            toFactor.push_back(h);
            toFactor.push_back(p / h);
            break;
          }
        }
      }
    }
  }
  return sortHack(output);
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
