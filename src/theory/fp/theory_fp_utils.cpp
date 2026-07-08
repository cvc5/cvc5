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

bool roundingCellLowerBound(const FloatingPoint& c,
                            RoundingMode rm,
                            Rational& t0,
                            bool& strict)
{
  if (c.isNaN() || c.isInfinite())
  {
    return false;
  }
  FloatingPoint p = FloatingPoint::predecessor(c);
  if (p.isInfinite())
  {
    return false;
  }
  Rational rc = c.convertToRationalTotal(Rational(0));
  Rational rp = p.convertToRationalTotal(Rational(0));
  switch (rm)
  {
    case RoundingMode::ROUND_TOWARD_POSITIVE:
      // x in (real(p), real(c)] rounds up to c
      t0 = rp;
      strict = true;
      return true;
    case RoundingMode::ROUND_TOWARD_NEGATIVE:
      // x in [real(c), real(succ(c))) rounds down to c
      t0 = rc;
      strict = false;
      return true;
    case RoundingMode::ROUND_TOWARD_ZERO:
      if (rc > 0)
      {
        // positive: rounds down, as for ROUND_TOWARD_NEGATIVE
        t0 = rc;
        strict = false;
      }
      else
      {
        // negative and zero: rounds up, as for ROUND_TOWARD_POSITIVE
        t0 = rp;
        strict = true;
      }
      return true;
    case RoundingMode::ROUND_NEAREST_TIES_TO_EVEN:
    {
      // the tie (midpoint) rounds to the neighbor with even significand;
      // the significand lsbs of adjacent packed values alternate
      t0 = (rp + rc) / 2;
      bool cEven = !c.pack().getValue().testBit(0);
      strict = !cEven;
      return true;
    }
    case RoundingMode::ROUND_NEAREST_TIES_TO_AWAY:
      // the tie rounds away from zero: to c if the midpoint is positive,
      // to p if it is negative
      t0 = (rp + rc) / 2;
      strict = t0 < 0;
      return true;
    default: Unreachable() << "Unknown rounding mode"; return false;
  }
}

}  // namespace utils
}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal
