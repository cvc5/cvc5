/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Util functions for theory FP.
 */
#include "theory/fp/theory_fp_utils.h"

#include "smt/logic_exception.h"

namespace cvc5::internal {
namespace theory {
namespace fp {
namespace utils {

Integer getCardinality(const TypeNode& type)
{
  Assert(type.getKind() == Kind::FLOATINGPOINT_TYPE);

  FloatingPointSize fps = type.getConst<FloatingPointSize>();

  /*
   * 1                    NaN
   * 2*1                  Infinities
   * 2*1                  Zeros
   * 2*(2^(s-1) -1)       Subnormal
   * 2*((2^e)-2)*2^(s-1)  Normal
   *
   *  = 1 + 2*2 + 2^s - 2 + 2^s * (2^e - 2)
   *  =       3 + 2^s * ((2^e)-1)
   */

  return Integer(3)
         + Integer(2).pow(fps.significandWidth())
               * (Integer(2).pow(fps.exponentWidth()) - Integer(1));
}

void checkForExperimentalFloatingPointType(const Node& n)
{
  TypeNode type = n.getType();
  if (type.isFloatingPoint())
  {
    uint32_t exp_sz = type.getFloatingPointExponentSize();
    uint32_t sig_sz = type.getFloatingPointSignificandSize();
    if (!((exp_sz == 8 && sig_sz == 24) || (exp_sz == 11 && sig_sz == 53)))
    {
      std::stringstream ss;
      ss << "FP term " << n << " with type whose size is " << exp_sz << "/"
         << sig_sz
         << " is not supported, only Float32 (8/24) or Float64 (11/53) types "
            "are supported in default mode. Try the experimental solver via "
            "--fp-exp. Note: There are known issues with the experimental "
            "solver, use at your own risk.";
      throw SafeLogicException(ss.str());
    }
  }
}

namespace {

/**
 * The magnitude the infinities overflow from, i.e., 2^(emax+1) for the given
 * format. It is not representable in the format, but it is the neighbor of
 * +-maxNormal that determines the boundaries of the outermost rounding cells:
 * a result rounded in an unbounded exponent range overflows iff its magnitude
 * is at least this value (see IEEE 754-2019, Section 7.4).
 * @param size The format.
 * @return The magnitude the infinities overflow from.
 */
Rational overflowMagnitude(const FloatingPointSize& size)
{
  FloatingPoint max = FloatingPoint::makeMaxNormal(size, false);
  Rational rmax = max.convertToRationalTotal(Rational(0));
  // The spacing of the largest binade. Note that nextDown(maxNormal) is in
  // that binade for any format, since the significand of maxNormal is all
  // ones and thus does not underflow into the binade below.
  Rational step =
      rmax - FloatingPoint::nextDown(max).convertToRationalTotal(Rational(0));
  return rmax + step;
}

}  // namespace

RoundingCellLowerBound roundingCellLowerBound(const FloatingPoint& c,
                                              RoundingMode rm)
{
  Assert(!c.isNaN());

  bool saturatesUp = rm == RoundingMode::ROUND_TOWARD_POSITIVE
                     || rm == RoundingMode::ROUND_TOWARD_ZERO;
  bool saturatesDown = rm == RoundingMode::ROUND_TOWARD_NEGATIVE
                       || rm == RoundingMode::ROUND_TOWARD_ZERO;

  // No real converts to less than -oo, thus all of them convert to at least
  // -oo. Note that this holds for every rounding mode, in particular for the
  // ones that never yield an infinity.
  if (c.isInfinite() && c.isNegative())
  {
    return {RoundingCellLowerBound::Kind::ALL};
  }
  // The rounding modes that round towards zero resp. towards -oo saturate at
  // maxNormal instead of overflowing to +oo, thus no real converts to +oo.
  if (c.isInfinite() && saturatesDown)
  {
    return {RoundingCellLowerBound::Kind::NONE};
  }
  FloatingPoint p = FloatingPoint::nextDown(c);
  // Dually, the rounding modes that round towards zero resp. towards +oo
  // saturate at -maxNormal, thus all reals convert to at least -maxNormal.
  if (p.isInfinite() && saturatesUp)
  {
    Assert(!c.isInfinite());
    return {RoundingCellLowerBound::Kind::ALL};
  }

  // The values of c and of the float below it. At the extremes of the format
  // one of the two is not representable; there the magnitude the infinities
  // overflow from stands in for the missing value, which is exactly what
  // rounding in an unbounded exponent range compares against.
  Rational rc, rp;
  if (c.isInfinite())
  {
    rc = overflowMagnitude(c.getSize());
    rp = p.convertToRationalTotal(Rational(0));
  }
  else
  {
    rc = c.convertToRationalTotal(Rational(0));
    rp = p.isInfinite() ? -overflowMagnitude(c.getSize())
                        : p.convertToRationalTotal(Rational(0));
  }
  switch (rm)
  {
    case RoundingMode::ROUND_TOWARD_POSITIVE:
      // x in (real(p), real(c)] rounds up to c
      return {RoundingCellLowerBound::Kind::BOUNDED, rp, true};
    case RoundingMode::ROUND_TOWARD_NEGATIVE:
      // x in [real(c), real(nextUp(c))) rounds down to c
      return {RoundingCellLowerBound::Kind::BOUNDED, rc, false};
    case RoundingMode::ROUND_TOWARD_ZERO:
      // positive: rounds down, as for ROUND_TOWARD_NEGATIVE
      // negative and zero: rounds up, as for ROUND_TOWARD_POSITIVE
      return rc > 0
                 ? RoundingCellLowerBound{RoundingCellLowerBound::Kind::BOUNDED,
                                          rc,
                                          false}
                 : RoundingCellLowerBound{
                       RoundingCellLowerBound::Kind::BOUNDED, rp, true};
    case RoundingMode::ROUND_NEAREST_TIES_TO_EVEN:
      // the tie (midpoint) rounds to the neighbor with even significand; the
      // significand lsbs of adjacent packed values alternate, thus the
      // boundary is strict iff the significand of c is odd. Note that this
      // also determines the tie at the overflow boundary correctly: the
      // significand of the infinities is zero, i.e., even, and IEEE 754-2019,
      // Section 7.4, indeed has the tie overflow.
      return {RoundingCellLowerBound::Kind::BOUNDED,
              (rp + rc) / 2,
              c.pack().getValue().testBit(0)};
    case RoundingMode::ROUND_NEAREST_TIES_TO_AWAY:
    {
      // the tie rounds away from zero: to c if the midpoint is positive,
      // to p if it is negative
      Rational t0 = (rp + rc) / 2;
      return {RoundingCellLowerBound::Kind::BOUNDED, t0, t0 < 0};
    }
    default: Unreachable() << "Unknown rounding mode";
  }
}

}  // namespace utils
}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal
