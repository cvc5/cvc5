/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Base class for floating-point literal implementation.
 */

#include "util/floatingpoint_literal.h"

#include "base/check.h"
#include "util/floatingpoint_literal_symfpu_traits.h"
#include "util/rational.h"

// #ifdef CVC5_USE_MPFR
// #include "util/floatingpoint_literal_mpfr.h"
// #else
#include "util/floatingpoint_literal_symfpu.h"
// #endif

/* -------------------------------------------------------------------------- */

namespace cvc5::internal {

// #ifdef CVC5_USE_MPFR
// using FPLit = FloatingPointLiteralMPFR;
// #else
using FPLit = FloatingPointLiteralSymFPU;
// #endif

using SymFPUUnpackedFloatLiteral =
    ::symfpu::unpackedFloat<symfpuLiteral::traits>;

uint32_t FloatingPointLiteral::getUnpackedExponentWidth(FloatingPointSize& size)
{
  return SymFPUUnpackedFloatLiteral::exponentWidth(size);
}

uint32_t FloatingPointLiteral::getUnpackedSignificandWidth(
    FloatingPointSize& size)
{
  return SymFPUUnpackedFloatLiteral::significandWidth(size);
}

FloatingPointLiteral::~FloatingPointLiteral() {}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteral::create(
    uint32_t exp_size, uint32_t sig_size, const BitVector& bv)
{
  return std::unique_ptr<FloatingPointLiteral>(
      new FPLit(exp_size, sig_size, bv));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteral::create(
    const FloatingPointSize& size, const BitVector& bv)
{
  return std::unique_ptr<FloatingPointLiteral>(new FPLit(size, bv));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteral::create(
    const FloatingPointSize& size, SpecialConstKind kind)
{
  Assert(kind != SpecialConstKind::FPZERO && kind != SpecialConstKind::FPINF);
  return std::unique_ptr<FloatingPointLiteral>(new FPLit(size, kind));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteral::create(
    const FloatingPointSize& size, SpecialConstKind kind, bool sign)
{
  Assert(kind == SpecialConstKind::FPZERO || kind == SpecialConstKind::FPINF);
  return std::unique_ptr<FloatingPointLiteral>(new FPLit(size, kind, sign));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteral::create(
    const FloatingPointSize& size,
    const RoundingMode& rm,
    const BitVector& bv,
    bool signedBV)
{
  return std::unique_ptr<FloatingPointLiteral>(
      new FPLit(size, rm, bv, signedBV));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteral::createFromRational(
    const FloatingPointSize& size, const RoundingMode& rm, const Rational& r)
{
  return FPLit::fromRational(size, rm, r);
}

}  // namespace cvc5::internal
