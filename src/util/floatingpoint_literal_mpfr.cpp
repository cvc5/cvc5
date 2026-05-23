/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * MPFR-based floating-point literal implementation.
 *
 * Ported from Bitwuzla's MPFR floating-point implementation, see
 * https://github.com/bitwuzla/bitwuzla/blob/main/src/solver/fp/floating_point.cpp
 * (Copyright (C) 2022 by the Bitwuzla authors, MIT license).
 */
#include "util/floatingpoint_literal_mpfr.h"

#include <gmp.h>
#include <gmpxx.h>

#include <cassert>
#include <cstring>
#include <string>

#include "base/check.h"
#include "util/floatingpoint_literal_symfpu.h"
#include "util/rational.h"

/* -------------------------------------------------------------------------- */

namespace cvc5::internal {

/* -------------------------------------------------------------------------- */

namespace {

/** Maximum IEEE exponent value (= bias). */
int64_t ieeeExpMax(uint32_t expSize)
{
  Assert((mp_bits_per_limb == 64 && expSize < 64)
         || (mp_bits_per_limb == 32 && expSize < 32));
  uint64_t one = 1;
  return (one << (expSize - one)) - one;
}

/** Minimum IEEE exponent value. */
int64_t ieeeExpMin(uint32_t expSize)
{
  return static_cast<int64_t>(1) - ieeeExpMax(expSize);
}

/** Maximum MPFR exponent value. */
int64_t mpfrExpMax(uint32_t expSize) { return ieeeExpMax(expSize) + 1; }

/** Minimum MPFR exponent value. */
int64_t mpfrExpMin(uint32_t expSize, uint32_t sigSize)
{
  return ieeeExpMin(expSize) - static_cast<int64_t>(sigSize) + 2;
}

/** IEEE exponent bias. */
int64_t expBias(uint32_t expSize) { return ieeeExpMax(expSize); }

/** Convert IEEE exponent to MPFR exponent. */
mpfr_exp_t ieee2mpfrExp(uint32_t expSize, uint64_t ieeeExp)
{
  return ieeeExp - expBias(expSize) + 1;
}

/** Convert MPFR exponent to IEEE exponent. */
int64_t mpfr2ieeeExp(uint32_t expSize, mpfr_exp_t mpfrExp)
{
  return mpfrExp + expBias(expSize) - 1;
}

/** Set MPFR emin/emax for the given FP format. */
void setMpfrEminmax(uint32_t expSize, uint32_t sigSize)
{
  int64_t emin = mpfrExpMin(expSize, sigSize);
  int64_t emax = mpfrExpMax(expSize);
  CVC5_UNUSED int status;
  status = mpfr_set_emax(emax);
  Assert(status == 0);
  status = mpfr_set_emin(emin);
  Assert(status == 0);
  Assert(emin <= emax);
}

/** Reset MPFR emin/emax to maximum range. */
void resetMpfrFormat()
{
  mpfr_set_emax(mpfr_get_emax_max());
  mpfr_set_emin(mpfr_get_emin_min());
}

/** Subnormal threshold (exponents at or below this are subnormal). */
int64_t subThreshold(uint32_t expSize)
{
  return -static_cast<int64_t>(expBias(expSize) - 1);
}

/** Convert cvc5 RoundingMode to mpfr_rnd_t. */
mpfr_rnd_t rm2mpfr(const RoundingMode& rm)
{
  switch (rm)
  {
    case RoundingMode::ROUND_NEAREST_TIES_TO_AWAY: return MPFR_RNDNA;
    case RoundingMode::ROUND_NEAREST_TIES_TO_EVEN: return MPFR_RNDN;
    case RoundingMode::ROUND_TOWARD_NEGATIVE: return MPFR_RNDD;
    case RoundingMode::ROUND_TOWARD_POSITIVE: return MPFR_RNDU;
    default: Assert(rm == RoundingMode::ROUND_TOWARD_ZERO); return MPFR_RNDZ;
  }
}

const FloatingPointLiteralMPFR& asMPFR(const FloatingPointLiteral& lit)
{
  Assert(dynamic_cast<const FloatingPointLiteralMPFR*>(&lit) != nullptr);
  return static_cast<const FloatingPointLiteralMPFR&>(lit);
}

}  // namespace

/* -------------------------------------------------------------------------- */

FloatingPointLiteralMPFR::FloatingPointLiteralMPFR(uint32_t exp_size,
                                                   uint32_t sig_size,
                                                   const BitVector& bv)
    : FloatingPointLiteral(exp_size, sig_size)
{
  initMpfr();

  Assert(exp_size + sig_size == bv.getSize());

  // Extract sign, exponent, significand from IEEE BV
  uint32_t bw = bv.getSize();
  BitVector bvsign = bv.extract(bw - 1, bw - 1);
  BitVector bvexp = bv.extract(bw - 2, bw - 1 - exp_size);
  BitVector bvsig = bv.extract(sig_size - 2, 0);

  int32_t sign = (bvsign == BitVector::mkOne(1)) ? -1 : 1;

  if (bvexp == BitVector::mkOnes(exp_size))
  {
    // Exponent all ones: infinity or NaN
    if (bvsig == BitVector::mkZero(sig_size - 1))
    {
      mpfr_set_inf(d_mpfr, sign);
    }
    else
    {
      mpfr_set_nan(d_mpfr);
    }
  }
  else if (bvexp == BitVector::mkZero(exp_size))
  {
    if (bvsig == BitVector::mkZero(sig_size - 1))
    {
      // Zero
      mpfr_set_zero(d_mpfr, sign);
    }
    else
    {
      // Subnormal: 0.significand * 2^(1-bias)
      std::string signStr = sign < 0 ? "-" : "";
      std::string s = signStr + "0." + bvsig.toString();
      mpfr_set_str(d_mpfr, s.c_str(), 2, MPFR_RNDN);
      mpfr_exp_t exp = mpfr_get_exp(d_mpfr);
      mpfr_set_exp(d_mpfr, exp + ieee2mpfrExp(exp_size, 0));
    }
  }
  else
  {
    // Normal: 1.significand * 2^(exp-bias)
    std::string signStr = sign < 0 ? "-" : "";
    std::string s = signStr + "1." + bvsig.toString();
    mpfr_set_str(d_mpfr, s.c_str(), 2, MPFR_RNDN);
    mpfr_set_exp(d_mpfr,
                 ieee2mpfrExp(exp_size, bvexp.toInteger().toUnsignedInt()));
  }
}

FloatingPointLiteralMPFR::FloatingPointLiteralMPFR(
    const FloatingPointSize& size, const BitVector& bv)
    : FloatingPointLiteralMPFR(
          size.exponentWidth(), size.significandWidth(), bv)
{
}

FloatingPointLiteralMPFR::FloatingPointLiteralMPFR(
    const FloatingPointSize& size, CVC5_UNUSED SpecialConstKind kind)
    : FloatingPointLiteral(size)
{
  Assert(kind == SpecialConstKind::FPNAN);
  initMpfr();
  mpfr_set_nan(d_mpfr);
}

FloatingPointLiteralMPFR::FloatingPointLiteralMPFR(
    const FloatingPointSize& size, SpecialConstKind kind, bool sign)
    : FloatingPointLiteral(size)
{
  Assert(kind == SpecialConstKind::FPINF || kind == SpecialConstKind::FPZERO);
  initMpfr();
  if (kind == SpecialConstKind::FPINF)
  {
    mpfr_set_inf(d_mpfr, sign ? -1 : 1);
  }
  else
  {
    mpfr_set_zero(d_mpfr, sign ? -1 : 1);
  }
}

FloatingPointLiteralMPFR::FloatingPointLiteralMPFR(
    const FloatingPointSize& size,
    const RoundingMode& rm,
    const BitVector& bv,
    bool signedBV)
    : FloatingPointLiteral(size)
{
  initMpfr();
  mpfr_rnd_t rmMpfr = rm2mpfr(rm);

  // Convert bit-vector to mpz integer
  mpz_class bvMpz;
  if (signedBV)
  {
    // Signed interpretation
    bvMpz = bv.toSignedInteger().getValue();
  }
  else
  {
    // Unsigned interpretation
    bvMpz = bv.toInteger().getValue();
  }

  int32_t i = 0;
  if (rm == RoundingMode::ROUND_NEAREST_TIES_TO_AWAY)
  {
    i = mpfr_round_nearest_away(mpfr_set_z, d_mpfr, bvMpz.get_mpz_t());
    if (mpfr_regular_p(d_mpfr))
    {
      i = mpfr_round_nearest_away(mpfr_check_range, d_mpfr, i);
    }
  }
  else
  {
    i = mpfr_set_z(d_mpfr, bvMpz.get_mpz_t(), rmMpfr);
    if (mpfr_regular_p(d_mpfr))
    {
      i = mpfr_check_range(d_mpfr, i, rmMpfr);
    }
  }
  mpfr_subnormalize(d_mpfr, i, rmMpfr);
}

FloatingPointLiteralMPFR::FloatingPointLiteralMPFR(
    const FloatingPointLiteralMPFR& other)
    : FloatingPointLiteral(other.d_fp_size)
{
  initMpfr();
  mpfr_set(d_mpfr, other.d_mpfr, MPFR_RNDN);
}

FloatingPointLiteralMPFR::FloatingPointLiteralMPFR(
    FloatingPointLiteralMPFR&& other)
    : FloatingPointLiteral(other.d_fp_size)
{
  initMpfr();
  mpfr_swap(d_mpfr, other.d_mpfr);
}

FloatingPointLiteralMPFR& FloatingPointLiteralMPFR::operator=(
    const FloatingPointLiteralMPFR& other)
{
  if (d_fp_size.significandWidth() != other.d_fp_size.significandWidth())
  {
    mpfr_set_prec(d_mpfr, other.d_fp_size.significandWidth());
  }
  d_fp_size = other.d_fp_size;
  setMpfrEminmax(d_fp_size.exponentWidth(), d_fp_size.significandWidth());
  mpfr_set(d_mpfr, other.d_mpfr, MPFR_RNDN);
  return *this;
}

FloatingPointLiteralMPFR& FloatingPointLiteralMPFR::operator=(
    FloatingPointLiteralMPFR&& other)
{
  d_fp_size = other.d_fp_size;
  mpfr_swap(d_mpfr, other.d_mpfr);
  return *this;
}

FloatingPointLiteralMPFR::~FloatingPointLiteralMPFR() { mpfr_clear(d_mpfr); }

/* -------------------------------------------------------------------------- */

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralMPFR::fromRational(
    const FloatingPointSize& size, const RoundingMode& rm, const Rational& r)
{
  if (r.isZero())
  {
    return std::unique_ptr<FloatingPointLiteral>(
        new FloatingPointLiteralMPFR(size, SpecialConstKind::FPZERO, false));
  }

  // Create a zero literal, then set it from the rational via mpfr_set_q.
  auto* lit =
      new FloatingPointLiteralMPFR(size, SpecialConstKind::FPZERO, false);

  // Set emin/emax for the target format.
  lit->setMpfrFormat();

  mpq_t q;
  mpq_init(q);
  mpz_set(mpq_numref(q), r.getNumerator().getValue().get_mpz_t());
  mpz_set(mpq_denref(q), r.getDenominator().getValue().get_mpz_t());
  mpq_canonicalize(q);

  mpfr_rnd_t rmMpfr = rm2mpfr(rm);
  int32_t i = 0;
  if (rm == RoundingMode::ROUND_NEAREST_TIES_TO_AWAY)
  {
    i = mpfr_round_nearest_away(mpfr_set_q, lit->d_mpfr, q);
    if (mpfr_regular_p(lit->d_mpfr))
    {
      i = mpfr_round_nearest_away(mpfr_check_range, lit->d_mpfr, i);
    }
  }
  else
  {
    i = mpfr_set_q(lit->d_mpfr, q, rmMpfr);
    if (mpfr_regular_p(lit->d_mpfr))
    {
      i = mpfr_check_range(lit->d_mpfr, i, rmMpfr);
    }
  }
  mpfr_subnormalize(lit->d_mpfr, i, rmMpfr);
  mpq_clear(q);

  return std::unique_ptr<FloatingPointLiteral>(lit);
}

/* -------------------------------------------------------------------------- */
/* FloatingPointLiteral interface                                             */
/* -------------------------------------------------------------------------- */

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralMPFR::clone() const
{
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralMPFR(*this));
}

BitVector FloatingPointLiteralMPFR::pack(void) const
{
  uint32_t expSize = d_fp_size.exponentWidth();
  uint32_t sigSize = d_fp_size.significandWidth();

  if (isNaN())
  {
    // Canonical NaN: sign=0, exp=all-1s, sig=10...0 (matches symfpu)
    BitVector bvsign = BitVector::mkZero(1);
    BitVector bvexp = BitVector::mkOnes(expSize);
    BitVector bvsig = BitVector::mkMinSigned(sigSize - 1);
    return bvsign.concat(bvexp).concat(bvsig);
  }

  bool neg = isNegative();
  BitVector bvsign = neg ? BitVector::mkOne(1) : BitVector::mkZero(1);

  if (isZero())
  {
    return bvsign.concat(BitVector::mkZero(expSize))
        .concat(BitVector::mkZero(sigSize - 1));
  }

  if (isInfinite())
  {
    return bvsign.concat(BitVector::mkOnes(expSize))
        .concat(BitVector::mkZero(sigSize - 1));
  }

  setMpfrFormat();

  mpfr_exp_t exp;
  char* str = mpfr_get_str(nullptr, &exp, 2, sigSize, d_mpfr, MPFR_RNDN);
  Assert(strlen(str) > 1 && (str[0] != '-' || strlen(str) > 2));

  BitVector bvexp = BitVector::mkZero(expSize);
  BitVector bvsig(sigSize - 1);

  if (isNormal())
  {
    // Normal: skip sign char and leading '1', take rest as significand
    std::string sigStr = str[0] == '-' ? str + 2 : str + 1;
    int64_t ieeeExp = mpfr2ieeeExp(expSize, exp);
    bvexp = BitVector(expSize, Integer(ieeeExp));
    bvsig = BitVector(sigStr);
    // Ensure proper width (the string may be exactly sigSize-1 chars)
    if (bvsig.getSize() < sigSize - 1)
    {
      bvsig = bvsig.zeroExtend(sigSize - 1 - bvsig.getSize());
    }
    else if (bvsig.getSize() > sigSize - 1)
    {
      bvsig = bvsig.extract(sigSize - 2, 0);
    }
  }
  else
  {
    // Subnormal: the string includes leading digit
    std::string sigStr = str[0] == '-' ? str + 1 : str;
    // Resize to sigSize-1 chars (pad with zeros on right if needed)
    sigStr.resize(sigSize - 1, '0');
    int64_t shiftAmt = -mpfr2ieeeExp(expSize, exp);
    Assert(shiftAmt >= 0);
    bvsig = BitVector(sigStr);
    if (bvsig.getSize() < sigSize - 1)
    {
      bvsig = bvsig.zeroExtend(sigSize - 1 - bvsig.getSize());
    }
    // Right-shift to account for subnormal exponent offset
    if (shiftAmt > 0)
    {
      bvsig = bvsig.logicalRightShift(
          BitVector(bvsig.getSize(), static_cast<uint32_t>(shiftAmt)));
    }
  }

  mpfr_free_str(str);

  Assert(bvexp.getSize() == expSize);
  Assert(bvsig.getSize() == sigSize - 1);

  return bvsign.concat(bvexp).concat(bvsig);
}

/* -------------------------------------------------------------------------- */

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralMPFR::absolute() const
{
  FloatingPointLiteralMPFR res(*this);
  mpfr_abs(res.d_mpfr, d_mpfr, MPFR_RNDN);
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralMPFR(res));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralMPFR::negate() const
{
  FloatingPointLiteralMPFR res(*this);
  mpfr_neg(res.d_mpfr, d_mpfr, MPFR_RNDN);
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralMPFR(res));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralMPFR::add(
    const RoundingMode& rm, const FloatingPointLiteral& arg) const
{
  const auto& a = asMPFR(arg);
  Assert(d_fp_size == a.d_fp_size);
  FloatingPointLiteralMPFR res(*this);
  mpfr_rnd_t rmMpfr = rm2mpfr(rm);
  int32_t i = 0;
  if (rm == RoundingMode::ROUND_NEAREST_TIES_TO_AWAY)
  {
    i = mpfr_round_nearest_away(mpfr_add, res.d_mpfr, d_mpfr, a.d_mpfr);
  }
  else
  {
    i = mpfr_add(res.d_mpfr, d_mpfr, a.d_mpfr, rmMpfr);
  }
  mpfr_subnormalize(res.d_mpfr, i, rmMpfr);
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralMPFR(res));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralMPFR::sub(
    const RoundingMode& rm, const FloatingPointLiteral& arg) const
{
  const auto& a = asMPFR(arg);
  Assert(d_fp_size == a.d_fp_size);
  FloatingPointLiteralMPFR res(*this);
  mpfr_rnd_t rmMpfr = rm2mpfr(rm);
  int32_t i = 0;
  if (rm == RoundingMode::ROUND_NEAREST_TIES_TO_AWAY)
  {
    i = mpfr_round_nearest_away(mpfr_sub, res.d_mpfr, d_mpfr, a.d_mpfr);
  }
  else
  {
    i = mpfr_sub(res.d_mpfr, d_mpfr, a.d_mpfr, rmMpfr);
  }
  mpfr_subnormalize(res.d_mpfr, i, rmMpfr);
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralMPFR(res));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralMPFR::mult(
    const RoundingMode& rm, const FloatingPointLiteral& arg) const
{
  const auto& a = asMPFR(arg);
  Assert(d_fp_size == a.d_fp_size);
  FloatingPointLiteralMPFR res(*this);
  mpfr_rnd_t rmMpfr = rm2mpfr(rm);
  int32_t i = 0;
  if (rm == RoundingMode::ROUND_NEAREST_TIES_TO_AWAY)
  {
    i = mpfr_round_nearest_away(mpfr_mul, res.d_mpfr, d_mpfr, a.d_mpfr);
  }
  else
  {
    i = mpfr_mul(res.d_mpfr, d_mpfr, a.d_mpfr, rmMpfr);
  }
  mpfr_subnormalize(res.d_mpfr, i, rmMpfr);
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralMPFR(res));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralMPFR::div(
    const RoundingMode& rm, const FloatingPointLiteral& arg) const
{
  const auto& a = asMPFR(arg);
  Assert(d_fp_size == a.d_fp_size);
  FloatingPointLiteralMPFR res(*this);
  mpfr_rnd_t rmMpfr = rm2mpfr(rm);
  int32_t i = 0;
  if (rm == RoundingMode::ROUND_NEAREST_TIES_TO_AWAY)
  {
    i = mpfr_round_nearest_away(mpfr_div, res.d_mpfr, d_mpfr, a.d_mpfr);
  }
  else
  {
    i = mpfr_div(res.d_mpfr, d_mpfr, a.d_mpfr, rmMpfr);
  }
  mpfr_subnormalize(res.d_mpfr, i, rmMpfr);
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralMPFR(res));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralMPFR::fma(
    const RoundingMode& rm,
    const FloatingPointLiteral& arg1,
    const FloatingPointLiteral& arg2) const
{
  const auto& a1 = asMPFR(arg1);
  const auto& a2 = asMPFR(arg2);
  Assert(d_fp_size == a1.d_fp_size);
  Assert(d_fp_size == a2.d_fp_size);
  FloatingPointLiteralMPFR res(*this);
  mpfr_rnd_t rmMpfr = rm2mpfr(rm);
  int32_t i = 0;
  if (rm == RoundingMode::ROUND_NEAREST_TIES_TO_AWAY)
  {
    i = mpfr_round_nearest_away(
        mpfr_fma, res.d_mpfr, d_mpfr, a1.d_mpfr, a2.d_mpfr);
  }
  else
  {
    i = mpfr_fma(res.d_mpfr, d_mpfr, a1.d_mpfr, a2.d_mpfr, rmMpfr);
  }
  mpfr_subnormalize(res.d_mpfr, i, rmMpfr);
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralMPFR(res));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralMPFR::sqrt(
    const RoundingMode& rm) const
{
  FloatingPointLiteralMPFR res(*this);
  mpfr_rnd_t rmMpfr = rm2mpfr(rm);
  int32_t i = 0;
  if (rm == RoundingMode::ROUND_NEAREST_TIES_TO_AWAY)
  {
    i = mpfr_round_nearest_away(mpfr_sqrt, res.d_mpfr, d_mpfr);
  }
  else
  {
    i = mpfr_sqrt(res.d_mpfr, d_mpfr, rmMpfr);
  }
  mpfr_subnormalize(res.d_mpfr, i, rmMpfr);
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralMPFR(res));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralMPFR::rti(
    const RoundingMode& rm) const
{
  FloatingPointLiteralMPFR res(*this);
  mpfr_rnd_t rmMpfr = rm2mpfr(rm);
  int32_t i = 0;
  if (rm == RoundingMode::ROUND_NEAREST_TIES_TO_AWAY)
  {
    i = mpfr_round(res.d_mpfr, d_mpfr);
  }
  else
  {
    i = mpfr_rint(res.d_mpfr, d_mpfr, rmMpfr);
  }
  mpfr_subnormalize(res.d_mpfr, i, rmMpfr);
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralMPFR(res));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralMPFR::rem(
    const FloatingPointLiteral& arg) const
{
  const auto& a = asMPFR(arg);
  Assert(d_fp_size == a.d_fp_size);
  FloatingPointLiteralMPFR res(*this);
  int32_t i = mpfr_remainder(res.d_mpfr, d_mpfr, a.d_mpfr, MPFR_RNDN);
  mpfr_subnormalize(res.d_mpfr, i, MPFR_RNDN);
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralMPFR(res));
}

/* -------------------------------------------------------------------------- */

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralMPFR::maxTotal(
    const FloatingPointLiteral& arg, bool zeroCaseLeft) const
{
  const auto& a = asMPFR(arg);
  Assert(d_fp_size == a.d_fp_size);

  // IEEE 754: if one operand is NaN, return the non-NaN operand.
  // If both are NaN, return NaN.
  if (isNaN() && a.isNaN())
  {
    return clone();
  }
  if (isNaN())
  {
    return a.clone();
  }
  if (a.isNaN())
  {
    return clone();
  }

  // Handle the +-zero case
  if (isZero() && a.isZero())
  {
    if (isNegative() != a.isNegative())
    {
      if (zeroCaseLeft)
      {
        return clone();
      }
      return a.clone();
    }
    return clone();
  }

  FloatingPointLiteralMPFR res(*this);
  mpfr_max(res.d_mpfr, d_mpfr, a.d_mpfr, MPFR_RNDN);
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralMPFR(res));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralMPFR::minTotal(
    const FloatingPointLiteral& arg, bool zeroCaseLeft) const
{
  const auto& a = asMPFR(arg);
  Assert(d_fp_size == a.d_fp_size);

  // IEEE 754: if one operand is NaN, return the non-NaN operand.
  // If both are NaN, return NaN.
  if (isNaN() && a.isNaN())
  {
    return clone();
  }
  if (isNaN())
  {
    return a.clone();
  }
  if (a.isNaN())
  {
    return clone();
  }

  // Handle the +-zero case
  if (isZero() && a.isZero())
  {
    if (isNegative() != a.isNegative())
    {
      if (zeroCaseLeft)
      {
        return clone();
      }
      return a.clone();
    }
    return clone();
  }

  FloatingPointLiteralMPFR res(*this);
  mpfr_min(res.d_mpfr, d_mpfr, a.d_mpfr, MPFR_RNDN);
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralMPFR(res));
}

/* -------------------------------------------------------------------------- */

bool FloatingPointLiteralMPFR::operator==(const FloatingPointLiteral& fp) const
{
  const auto& other = asMPFR(fp);
  if (!(d_fp_size == other.d_fp_size))
  {
    return false;
  }

  bool nan1 = isNaN();
  bool nan2 = other.isNaN();
  if (nan1 || nan2)
  {
    // Syntactic equality: NaN == NaN is true
    return nan1 == nan2;
  }

  bool zero1 = isZero();
  bool zero2 = other.isZero();
  if (zero1 || zero2)
  {
    // Distinguish +0 from -0
    return zero1 == zero2 && isNegative() == other.isNegative();
  }

  return mpfr_equal_p(d_mpfr, other.d_mpfr) != 0;
}

bool FloatingPointLiteralMPFR::operator<=(const FloatingPointLiteral& arg) const
{
  const auto& a = asMPFR(arg);
  Assert(d_fp_size == a.d_fp_size);
  return mpfr_lessequal_p(d_mpfr, a.d_mpfr) != 0;
}

bool FloatingPointLiteralMPFR::operator<(const FloatingPointLiteral& arg) const
{
  const auto& a = asMPFR(arg);
  Assert(d_fp_size == a.d_fp_size);
  return mpfr_less_p(d_mpfr, a.d_mpfr) != 0;
}

/* -------------------------------------------------------------------------- */

BitVector FloatingPointLiteralMPFR::getUnpackedExponent() const
{
  // This is SymFPU specific, thus we go via SymFPU.
  FloatingPointLiteralSymFPU symfpu(d_fp_size, pack());
  return symfpu.getUnpackedExponent();
}

BitVector FloatingPointLiteralMPFR::getUnpackedSignificand() const
{
  // This is SymFPU specific, thus we go via SymFPU.
  FloatingPointLiteralSymFPU symfpu(d_fp_size, pack());
  return symfpu.getUnpackedSignificand();
}

bool FloatingPointLiteralMPFR::getSign() const
{
  if (isNaN())
  {
    return false;
  }
  return mpfr_signbit(d_mpfr) != 0;
}

/* -------------------------------------------------------------------------- */

bool FloatingPointLiteralMPFR::isNormal(void) const
{
  return mpfr_regular_p(d_mpfr) != 0
         && mpfr_get_exp(d_mpfr) > subThreshold(d_fp_size.exponentWidth());
}

bool FloatingPointLiteralMPFR::isSubnormal(void) const
{
  return mpfr_regular_p(d_mpfr) != 0
         && mpfr_get_exp(d_mpfr) <= subThreshold(d_fp_size.exponentWidth());
}

bool FloatingPointLiteralMPFR::isZero(void) const
{
  return mpfr_zero_p(d_mpfr) != 0;
}

bool FloatingPointLiteralMPFR::isInfinite(void) const
{
  return mpfr_inf_p(d_mpfr) != 0;
}

bool FloatingPointLiteralMPFR::isNaN(void) const
{
  return mpfr_nan_p(d_mpfr) != 0;
}

bool FloatingPointLiteralMPFR::isNegative(void) const
{
  return !isNaN() && mpfr_signbit(d_mpfr) != 0;
}

bool FloatingPointLiteralMPFR::isPositive(void) const
{
  return !isNaN() && mpfr_signbit(d_mpfr) == 0;
}

/* -------------------------------------------------------------------------- */

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralMPFR::convert(
    const FloatingPointSize& target, const RoundingMode& rm) const
{
  // Create a new literal of the target size initialized from this value
  FloatingPointLiteralMPFR res(target, SpecialConstKind::FPZERO, false);
  mpfr_rnd_t rmMpfr = rm2mpfr(rm);

  // Set emin/emax for the target format
  setMpfrEminmax(target.exponentWidth(), target.significandWidth());

  int32_t i = 0;
  if (rm == RoundingMode::ROUND_NEAREST_TIES_TO_AWAY)
  {
    i = mpfr_round_nearest_away(mpfr_set, res.d_mpfr, d_mpfr);
    if (mpfr_regular_p(res.d_mpfr))
    {
      i = mpfr_round_nearest_away(mpfr_check_range, res.d_mpfr, i);
    }
  }
  else
  {
    i = mpfr_set(res.d_mpfr, d_mpfr, rmMpfr);
    if (mpfr_regular_p(res.d_mpfr))
    {
      i = mpfr_check_range(res.d_mpfr, i, rmMpfr);
    }
  }
  mpfr_subnormalize(res.d_mpfr, i, rmMpfr);
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralMPFR(res));
}

BitVector FloatingPointLiteralMPFR::convertToSBVTotal(
    BitVectorSize width, const RoundingMode& rm, BitVector undefinedCase) const
{
  uint32_t w = width;

  // Undefined for NaN, infinity, or out-of-range values
  if (isNaN() || isInfinite())
  {
    return undefinedCase;
  }

  // Round to integer first
  mpfr_t rounded;
  resetMpfrFormat();
  mpfr_init2(rounded, d_fp_size.significandWidth());
  mpfr_rnd_t rmMpfr = rm2mpfr(rm);
  if (rm == RoundingMode::ROUND_NEAREST_TIES_TO_AWAY)
  {
    mpfr_round(rounded, d_mpfr);
  }
  else
  {
    mpfr_rint(rounded, d_mpfr, rmMpfr);
  }

  if (mpfr_zero_p(rounded))
  {
    mpfr_clear(rounded);
    return BitVector::mkZero(w);
  }

  // Check range: [-2^(w-1), 2^(w-1)-1]
  mpfr_t bound;
  mpfr_init2(bound, w + 1);

  // Check lower bound: -2^(w-1)
  mpfr_set_si_2exp(bound, -1, w - 1, MPFR_RNDN);
  if (mpfr_cmp(rounded, bound) < 0)
  {
    mpfr_clear(rounded);
    mpfr_clear(bound);
    return undefinedCase;
  }

  // Check upper bound: 2^(w-1) - 1
  mpfr_set_si_2exp(bound, 1, w - 1, MPFR_RNDN);
  mpfr_sub_ui(bound, bound, 1, MPFR_RNDN);
  if (mpfr_cmp(rounded, bound) > 0)
  {
    mpfr_clear(rounded);
    mpfr_clear(bound);
    return undefinedCase;
  }
  mpfr_clear(bound);

  // Extract the integer value
  mpz_class result;
  mpfr_get_z(result.get_mpz_t(), rounded, MPFR_RNDZ);
  mpfr_clear(rounded);

  // Convert to bit-vector (signed)
  Integer intVal(result);
  if (intVal.sgn() < 0)
  {
    // Two's complement representation
    Integer modulus = Integer(1).multiplyByPow2(w);
    intVal = modulus + intVal;
  }
  return BitVector(w, intVal);
}

BitVector FloatingPointLiteralMPFR::convertToUBVTotal(
    BitVectorSize width, const RoundingMode& rm, BitVector undefinedCase) const
{
  uint32_t w = width;

  if (isNaN() || isInfinite())
  {
    return undefinedCase;
  }

  // Round to integer first
  mpfr_t rounded;
  resetMpfrFormat();
  mpfr_init2(rounded, d_fp_size.significandWidth());
  mpfr_rnd_t rmMpfr = rm2mpfr(rm);
  if (rm == RoundingMode::ROUND_NEAREST_TIES_TO_AWAY)
  {
    mpfr_round(rounded, d_mpfr);
  }
  else
  {
    mpfr_rint(rounded, d_mpfr, rmMpfr);
  }

  if (mpfr_zero_p(rounded))
  {
    mpfr_clear(rounded);
    return BitVector::mkZero(w);
  }

  // Check range: [0, 2^w - 1]
  if (mpfr_sgn(rounded) < 0)
  {
    mpfr_clear(rounded);
    return undefinedCase;
  }

  mpfr_t bound;
  mpfr_init2(bound, w + 1);
  mpfr_set_si_2exp(bound, 1, w, MPFR_RNDN);
  mpfr_sub_ui(bound, bound, 1, MPFR_RNDN);
  if (mpfr_cmp(rounded, bound) > 0)
  {
    mpfr_clear(rounded);
    mpfr_clear(bound);
    return undefinedCase;
  }
  mpfr_clear(bound);

  // Extract the integer value
  mpz_class result;
  mpfr_get_z(result.get_mpz_t(), rounded, MPFR_RNDZ);
  mpfr_clear(rounded);

  return BitVector(w, Integer(result));
}

std::pair<Rational, bool> FloatingPointLiteralMPFR::convertToRational() const
{
  if (isNaN() || isInfinite())
  {
    return std::make_pair(Rational(0U, 1U), false);
  }
  if (isZero())
  {
    return std::make_pair(Rational(0U, 1U), true);
  }

  mpq_class mpq;
  mpfr_get_q(mpq.get_mpq_t(), d_mpfr);
  Rational res(mpq.get_str());
  return std::make_pair(res, true);
}

/* -------------------------------------------------------------------------- */

void FloatingPointLiteralMPFR::initMpfr()
{
  resetMpfrFormat();
  // MPFR precision = significandWidth (includes hidden bit).
  mpfr_init2(d_mpfr, d_fp_size.significandWidth());
  setMpfrFormat();
}

void FloatingPointLiteralMPFR::setMpfrFormat() const
{
  setMpfrEminmax(d_fp_size.exponentWidth(), d_fp_size.significandWidth());
}

mpfr_rnd_t FloatingPointLiteralMPFR::rmToMpfr(const RoundingMode& rm)
{
  return rm2mpfr(rm);
}

/* -------------------------------------------------------------------------- */

}  // namespace cvc5::internal
