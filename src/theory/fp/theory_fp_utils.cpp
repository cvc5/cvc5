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

std::pair<Rational, bool> roundingCellLowerBound(const FloatingPoint& c,
                                                 RoundingMode rm)
{
  Assert(!c.isNaN() && !c.isInfinite());
  FloatingPoint p = FloatingPoint::nextDown(c);
  Assert(!p.isInfinite());
  Rational rc = c.convertToRationalTotal(Rational(0));
  Rational rp = p.convertToRationalTotal(Rational(0));
  switch (rm)
  {
    case RoundingMode::ROUND_TOWARD_POSITIVE:
      // x in (real(p), real(c)] rounds up to c
      return {rp, true};
    case RoundingMode::ROUND_TOWARD_NEGATIVE:
      // x in [real(c), real(nextUp(c))) rounds down to c
      return {rc, false};
    case RoundingMode::ROUND_TOWARD_ZERO:
      // positive: rounds down, as for ROUND_TOWARD_NEGATIVE
      // negative and zero: rounds up, as for ROUND_TOWARD_POSITIVE
      return rc > 0 ? std::make_pair(rc, false) : std::make_pair(rp, true);
    case RoundingMode::ROUND_NEAREST_TIES_TO_EVEN:
      // the tie (midpoint) rounds to the neighbor with even significand; the
      // significand lsbs of adjacent packed values alternate, thus the
      // boundary is strict iff the significand of c is odd
      return {(rp + rc) / 2, c.pack().getValue().testBit(0)};
    case RoundingMode::ROUND_NEAREST_TIES_TO_AWAY:
    {
      // the tie rounds away from zero: to c if the midpoint is positive,
      // to p if it is negative
      Rational t0 = (rp + rc) / 2;
      return {t0, t0 < 0};
    }
    default: Unreachable() << "Unknown rounding mode";
  }
}

}  // namespace utils
}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal
