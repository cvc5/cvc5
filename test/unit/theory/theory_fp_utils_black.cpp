/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the FP theory utility functions.
 */

#include <tuple>

#include "test.h"
#include "theory/fp/theory_fp_utils.h"
#include "util/bitvector.h"
#include "util/floatingpoint.h"
#include "util/rational.h"

namespace cvc5::internal {

using namespace theory::fp;

namespace test {

class TestTheoryBlackFpUtils : public TestInternal
{
 protected:
  /** Number of random values tested per format and rounding mode. */
#ifdef CVC5_SLOW_TESTS
  static constexpr uint32_t N_TESTS = 500;
#else
  static constexpr uint32_t N_TESTS = 20;
#endif

  void SetUp() override
  {
    TestInternal::SetUp();
    d_all_formats = {FloatingPointSize(5, 11),
                     FloatingPointSize(8, 24),
                     FloatingPointSize(11, 53),
                     FloatingPointSize(15, 113)};
    d_all_rms = {RoundingMode::ROUND_NEAREST_TIES_TO_EVEN,
                 RoundingMode::ROUND_NEAREST_TIES_TO_AWAY,
                 RoundingMode::ROUND_TOWARD_POSITIVE,
                 RoundingMode::ROUND_TOWARD_NEGATIVE,
                 RoundingMode::ROUND_TOWARD_ZERO};
  }

  /**
   * Whether a >=_fp b for non-NaN a and b, i.e., the order that places the
   * infinities outside the finite values and identifies -0 and +0.
   */
  static bool geqFp(const FloatingPoint& a, const FloatingPoint& b)
  {
    Assert(!a.isNaN() && !b.isNaN());
    if (a.isInfinite() && a.isPositive())
    {
      return true;
    }
    if (b.isInfinite() && b.isNegative())
    {
      return true;
    }
    // a is -oo and b is not, or b is +oo and a is finite
    if (a.isInfinite() || b.isInfinite())
    {
      return false;
    }
    return a.convertToRationalTotal(Rational(0))
           >= b.convertToRationalTotal(Rational(0));
  }

  /**
   * Check the contract of roundingCellLowerBound for float c, rounding mode
   * rm and a real sample point x:
   *   to_fp(rm, x) >=_fp c  iff  x is above the boundary b,
   * where >=_fp is geqFp() above, computed via the exact conversion of x.
   */
  void checkContractAt(const FloatingPoint& c,
                       RoundingMode rm,
                       const utils::RoundingCellLowerBound& b,
                       const Rational& x)
  {
    FloatingPoint fx(c.getSize(), rm, x);
    ASSERT_FALSE(fx.isNaN());
    bool above;
    switch (b.d_kind)
    {
      case utils::RoundingCellLowerBound::Kind::ALL: above = true; break;
      case utils::RoundingCellLowerBound::Kind::NONE: above = false; break;
      default: above = b.d_strict ? x > b.d_bound : x >= b.d_bound; break;
    }
    ASSERT_EQ(geqFp(fx, c), above)
        << "c = " << c << ", rm = " << rm
        << ", kind = " << static_cast<uint32_t>(b.d_kind)
        << ", t0 = " << b.d_bound << ", strict = " << b.d_strict
        << ", x = " << x;
  }

  /**
   * The boundary of a rounding cell that is expected to be bounded below.
   * @param c The float whose rounding cell is considered.
   * @param rm The rounding mode.
   * @return The boundary and its strictness.
   */
  std::pair<Rational, bool> bound(const FloatingPoint& c, RoundingMode rm)
  {
    utils::RoundingCellLowerBound b = utils::roundingCellLowerBound(c, rm);
    EXPECT_EQ(b.d_kind, utils::RoundingCellLowerBound::Kind::BOUNDED)
        << "c = " << c << ", rm = " << rm;
    return {b.d_bound, b.d_strict};
  }

  /**
   * The floats at the extremes of a format, where the rounding cells are
   * unbounded or empty depending on the rounding mode.
   */
  std::vector<FloatingPoint> extremes(const FloatingPointSize& size)
  {
    FloatingPoint maxNormalPos = FloatingPoint::makeMaxNormal(size, false);
    FloatingPoint maxNormalNeg = FloatingPoint::makeMaxNormal(size, true);
    return {FloatingPoint::makeInf(size, false),
            FloatingPoint::makeInf(size, true),
            maxNormalPos,
            maxNormalNeg,
            FloatingPoint::nextDown(maxNormalPos),
            FloatingPoint::nextUp(maxNormalNeg)};
  }

  std::vector<FloatingPointSize> d_all_formats;
  std::vector<RoundingMode> d_all_rms;
};

/* -------------------------------------------------------------------------- */

#ifdef CVC5_ASSERTIONS
TEST_F(TestTheoryBlackFpUtils, roundingCellLowerBoundPreconditions)
{
  // the preconditions do not depend on the format, one is enough here (death
  // tests fork the process and are expensive)
  FloatingPointSize size(5, 11);
  RoundingMode rm = RoundingMode::ROUND_NEAREST_TIES_TO_EVEN;
  // NaN is not in the range of the conversion and is unordered, so it has no
  // rounding cell. The infinities and the extremal finite values do have one,
  // see roundingCellLowerBoundExtremes below.
  ASSERT_DEATH(utils::roundingCellLowerBound(FloatingPoint::makeNaN(size), rm),
               "!c.isNaN\\(\\)");
}
#endif

TEST_F(TestTheoryBlackFpUtils, roundingCellLowerBoundKnownValues)
{
  // Hand-computed boundaries for c = 1.0 in Float16 (5, 11). The value
  // below 1.0 is 1 - 2^-11 = 2047/2048, so the midpoint towards
  // 1.0 is 4095/4096. The significand of 1.0 is even (all stored bits 0).
  FloatingPointSize f16(5, 11);
  FloatingPoint one(f16, RoundingMode::ROUND_NEAREST_TIES_TO_EVEN, Rational(1));
  Rational t0;
  bool strict;

  std::tie(t0, strict) = bound(one, RoundingMode::ROUND_TOWARD_POSITIVE);
  ASSERT_EQ(t0, Rational(2047, 2048));
  ASSERT_TRUE(strict);

  std::tie(t0, strict) = bound(one, RoundingMode::ROUND_TOWARD_NEGATIVE);
  ASSERT_EQ(t0, Rational(1));
  ASSERT_FALSE(strict);

  // positive values round towards zero as for ROUND_TOWARD_NEGATIVE
  std::tie(t0, strict) = bound(one, RoundingMode::ROUND_TOWARD_ZERO);
  ASSERT_EQ(t0, Rational(1));
  ASSERT_FALSE(strict);

  // the tie rounds to 1.0 (even), so the boundary is inclusive
  std::tie(t0, strict) = bound(one, RoundingMode::ROUND_NEAREST_TIES_TO_EVEN);
  ASSERT_EQ(t0, Rational(4095, 4096));
  ASSERT_FALSE(strict);

  // the positive tie rounds away from zero, i.e., up to 1.0
  std::tie(t0, strict) = bound(one, RoundingMode::ROUND_NEAREST_TIES_TO_AWAY);
  ASSERT_EQ(t0, Rational(4095, 4096));
  ASSERT_FALSE(strict);

  // For c = -1.0, the value below is -(1 + 2^-10) = -1025/1024 and the
  // midpoint towards -1.0 is -2049/2048.
  FloatingPoint mone(
      f16, RoundingMode::ROUND_NEAREST_TIES_TO_EVEN, Rational(-1));

  std::tie(t0, strict) = bound(mone, RoundingMode::ROUND_TOWARD_POSITIVE);
  ASSERT_EQ(t0, Rational(-1025, 1024));
  ASSERT_TRUE(strict);

  std::tie(t0, strict) = bound(mone, RoundingMode::ROUND_TOWARD_NEGATIVE);
  ASSERT_EQ(t0, Rational(-1));
  ASSERT_FALSE(strict);

  // negative values round towards zero as for ROUND_TOWARD_POSITIVE
  std::tie(t0, strict) = bound(mone, RoundingMode::ROUND_TOWARD_ZERO);
  ASSERT_EQ(t0, Rational(-1025, 1024));
  ASSERT_TRUE(strict);

  // the tie rounds to -1.0 (even), so the boundary is inclusive
  std::tie(t0, strict) = bound(mone, RoundingMode::ROUND_NEAREST_TIES_TO_EVEN);
  ASSERT_EQ(t0, Rational(-2049, 2048));
  ASSERT_FALSE(strict);

  // the negative tie rounds away from zero, i.e., down to -1025/1024, so
  // the boundary of -1.0's cell is exclusive
  std::tie(t0, strict) = bound(mone, RoundingMode::ROUND_NEAREST_TIES_TO_AWAY);
  ASSERT_EQ(t0, Rational(-2049, 2048));
  ASSERT_TRUE(strict);
}

TEST_F(TestTheoryBlackFpUtils, roundingCellLowerBoundExtremes)
{
  using Kind = utils::RoundingCellLowerBound::Kind;
  // Hand-computed boundaries at the extremes of Float16 (5, 11): the largest
  // finite value is 2^16 - 2^5 = 65504, the magnitude the infinities overflow
  // from is 2^16 = 65536, and the midpoint between the two is 65520.
  FloatingPointSize f16(5, 11);
  FloatingPoint inf = FloatingPoint::makeInf(f16, false);
  FloatingPoint ninf = FloatingPoint::makeInf(f16, true);
  FloatingPoint maxNormal = FloatingPoint::makeMaxNormal(f16, false);
  FloatingPoint nmaxNormal = FloatingPoint::makeMaxNormal(f16, true);
  Rational t0;
  bool strict;

  // Every real converts to at least -oo, under every rounding mode.
  for (RoundingMode rm : d_all_rms)
  {
    ASSERT_EQ(utils::roundingCellLowerBound(ninf, rm).d_kind, Kind::ALL);
  }

  // The nearest modes overflow to +oo at the midpoint, which is a tie that
  // rounds to +oo (the significand of the infinities is even), thus the
  // boundary is inclusive.
  for (RoundingMode rm : {RoundingMode::ROUND_NEAREST_TIES_TO_EVEN,
                          RoundingMode::ROUND_NEAREST_TIES_TO_AWAY})
  {
    std::tie(t0, strict) = bound(inf, rm);
    ASSERT_EQ(t0, Rational(65520));
    ASSERT_FALSE(strict);
  }
  // Rounding up overflows above the largest finite value.
  std::tie(t0, strict) = bound(inf, RoundingMode::ROUND_TOWARD_POSITIVE);
  ASSERT_EQ(t0, Rational(65504));
  ASSERT_TRUE(strict);
  // The modes that round down resp. towards zero saturate at the largest
  // finite value, thus no real converts to +oo.
  for (RoundingMode rm :
       {RoundingMode::ROUND_TOWARD_NEGATIVE, RoundingMode::ROUND_TOWARD_ZERO})
  {
    ASSERT_EQ(utils::roundingCellLowerBound(inf, rm).d_kind, Kind::NONE);
  }

  // Dually for the smallest finite value: the modes that round up resp.
  // towards zero saturate at it, thus every real converts to at least -65504.
  for (RoundingMode rm :
       {RoundingMode::ROUND_TOWARD_POSITIVE, RoundingMode::ROUND_TOWARD_ZERO})
  {
    ASSERT_EQ(utils::roundingCellLowerBound(nmaxNormal, rm).d_kind, Kind::ALL);
  }
  // The tie at -65520 rounds away to -oo, so the boundary of the cell of
  // -65504 is exclusive.
  for (RoundingMode rm : {RoundingMode::ROUND_NEAREST_TIES_TO_EVEN,
                          RoundingMode::ROUND_NEAREST_TIES_TO_AWAY})
  {
    std::tie(t0, strict) = bound(nmaxNormal, rm);
    ASSERT_EQ(t0, Rational(-65520));
    ASSERT_TRUE(strict);
  }
  // Rounding down overflows below the smallest finite value.
  std::tie(t0, strict) = bound(nmaxNormal, RoundingMode::ROUND_TOWARD_NEGATIVE);
  ASSERT_EQ(t0, Rational(-65504));
  ASSERT_FALSE(strict);

  // The cell of the largest finite value itself is the generic case: the
  // value below it is 65504 - 32 = 65472 and the tie at 65488 rounds to it
  // (the significand of 65504 is odd), so the boundary is exclusive.
  std::tie(t0, strict) =
      bound(maxNormal, RoundingMode::ROUND_NEAREST_TIES_TO_EVEN);
  ASSERT_EQ(t0, Rational(65488));
  ASSERT_TRUE(strict);
}

TEST_F(TestTheoryBlackFpUtils, roundingCellLowerBoundContract)
{
  using Kind = utils::RoundingCellLowerBound::Kind;
  // Validate the documented equivalence
  //   to_fp(rm, x) >=_fp c  iff  x is above the boundary
  // against the exact from-rational conversion, at sample points around the
  // boundary, at the values of c and its neighbors, and far outside the range
  // of the format on both sides. The equivalence is global, so any sample
  // point must agree. The floats at the extremes of the format, where the
  // boundary is degenerate, are always tested; the remaining ones are
  // sampled.
  for (const auto& size : d_all_formats)
  {
    uint32_t bvSize = size.exponentWidth() + size.significandWidth();
    Rational rmax = FloatingPoint::makeMaxNormal(size, false)
                        .convertToRationalTotal(Rational(0));
    Rational rminSub = FloatingPoint::makeMinSubnormal(size, false)
                           .convertToRationalTotal(Rational(0));
    std::vector<FloatingPoint> cs = extremes(size);
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      cs.emplace_back(size, BitVector::mkRandom(bvSize));
    }
    for (const FloatingPoint& c : cs)
    {
      // NaN has no rounding cell, the only precondition
      if (c.isNaN())
      {
        continue;
      }
      for (RoundingMode rm : d_all_rms)
      {
        utils::RoundingCellLowerBound b = utils::roundingCellLowerBound(c, rm);
        std::vector<Rational> xs = {
            Rational(0), rmax * 2, -rmax * 2, rminSub / 2, -rminSub / 2};
        if (!c.isInfinite())
        {
          xs.push_back(c.convertToRationalTotal(Rational(0)));
        }
        if (b.d_kind == Kind::BOUNDED)
        {
          // an offset that is smaller than the width of any rounding cell at
          // the magnitude of the boundary, so that the neighboring points lie
          // in the adjacent cells
          Rational t = b.d_bound < 0 ? -b.d_bound : b.d_bound;
          Rational delta =
              t.isZero()
                  ? rminSub / 4
                  : t / Rational(Integer(2).pow(size.significandWidth() + 3));
          xs.push_back(b.d_bound);
          xs.push_back(b.d_bound - delta);
          xs.push_back(b.d_bound + delta);
        }
        for (const Rational& x : xs)
        {
          checkContractAt(c, rm, b, x);
        }
      }
    }
  }
}

}  // namespace test
}  // namespace cvc5::internal
