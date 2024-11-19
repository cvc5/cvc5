/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * CoCoA utilities
 */

#ifdef CVC5_USE_COCOA

#include "theory/ff/cocoa_util.h"

// external includes
#include <CoCoA/BigIntOps.H>
#include <CoCoA/SparsePolyIter.H>
#include <CoCoA/SparsePolyOps-RingElem.H>
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/TmpGPoly.H>

// std includes

// internal includes

namespace cvc5::internal {
namespace theory {
namespace ff {

std::optional<Scalar> cocoaEval(Poly poly, const PartialPoint& values)
{
  CoCoA::ring coeffs = CoCoA::CoeffRing(CoCoA::owner(poly));
  Scalar out = CoCoA::zero(coeffs);
  for (auto it = CoCoA::BeginIter(poly), end = CoCoA::EndIter(poly); it != end;
       ++it)
  {
    Scalar term = CoCoA::coeff(it);
    std::vector<CoCoA::BigInt> exponents;
    CoCoA::BigExponents(exponents, CoCoA::PP(it));
    for (size_t i = 0, n = exponents.size(); i < n; ++i)
    {
      if (!CoCoA::IsZero(exponents[i]))
      {
        if (!values[i].has_value())
        {
          return {};
        }
        term *= CoCoA::power(*values[i], exponents[i]);
      }
    }
    out += term;
  }
  return {out};
}

Scalar cocoaEval(Poly poly, const Point& values)
{
  CoCoA::ring coeffs = CoCoA::CoeffRing(CoCoA::owner(poly));
  Scalar out = CoCoA::zero(coeffs);
  for (auto it = CoCoA::BeginIter(poly), end = CoCoA::EndIter(poly); it != end;
       ++it)
  {
    Scalar term = CoCoA::coeff(it);
    std::vector<CoCoA::BigInt> exponents;
    CoCoA::BigExponents(exponents, CoCoA::PP(it));
    for (size_t i = 0, n = exponents.size(); i < n; ++i)
    {
      if (!CoCoA::IsZero(exponents[i]))
      {
        term *= CoCoA::power(values[i], exponents[i]);
      }
    }
    out += term;
  }
  return out;
}

FiniteFieldValue cocoaFfToFfVal(const Scalar& elem, const FfSize& size)
{
  return {Integer(extractStr(elem), 10), size};
}

CoCoA::BigInt intToCocoa(const Integer& i)
{
  return CoCoA::BigIntFromString(i.toString());
}

const std::vector<Poly>& GBasisTimeout(const CoCoA::ideal& ideal,
                                       const ResourceManager* rm)
{
  if (rm == nullptr)
  {
    return CoCoA::GBasis(ideal);
  }
  double sec = static_cast<double>(rm->getRemainingTime()) / 1e3;
  Trace("ff::gb") << "Computing a GB; limit " << sec << "s" << std::endl;
  try
  {
    if (sec == 0)
    {
      return CoCoA::GBasis(ideal);
    }
    else
    {
      return CoCoA::GBasis(ideal, CoCoA::CpuTimeLimit(sec));
    }
  }
  catch (CoCoA::TimeoutException& t)
  {
    CoCoA::handlersEnabled = false;
    throw FfTimeoutException("GBasis");
  }
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
