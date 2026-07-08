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
   * Check the contract of roundingCellLowerBound for float c, rounding mode
   * rm and a real sample point x:
   *   to_fp(rm, x) >=_fp c  iff  (strict ? x > t0 : x >= t0),
   * where >=_fp compares the denoted extended real values (-0 and +0 both
   * denote 0), computed via the exact conversion of x.
   */
  void checkContractAt(const FloatingPoint& c,
                       RoundingMode rm,
                       const Rational& t0,
                       bool strict,
                       const Rational& x)
  {
    FloatingPoint fx(c.getSize(), rm, x);
    ASSERT_FALSE(fx.isNaN());
    bool geq;
    if (fx.isInfinite())
    {
      geq = fx.isPositive();
    }
    else
    {
      geq = fx.convertToRationalTotal(Rational(0))
            >= c.convertToRationalTotal(Rational(0));
    }
    ASSERT_EQ(geq, strict ? x > t0 : x >= t0)
        << "c = " << c << ", rm = " << rm << ", t0 = " << t0
        << ", strict = " << strict << ", x = " << x;
  }

  std::vector<FloatingPointSize> d_all_formats;
  std::vector<RoundingMode> d_all_rms;
};

/* -------------------------------------------------------------------------- */

TEST_F(TestTheoryBlackFpUtils, roundingCellLowerBoundUndefined)
{
  Rational t0;
  bool strict;
  for (const auto& size : d_all_formats)
  {
    for (RoundingMode rm : d_all_rms)
    {
      // no rounding cell for NaN and the infinities
      ASSERT_FALSE(utils::roundingCellLowerBound(
          FloatingPoint::makeNaN(size), rm, t0, strict));
      ASSERT_FALSE(utils::roundingCellLowerBound(
          FloatingPoint::makeInf(size, false), rm, t0, strict));
      ASSERT_FALSE(utils::roundingCellLowerBound(
          FloatingPoint::makeInf(size, true), rm, t0, strict));
      // the predecessor of -maxNormal is -oo, so its cell has no finite
      // lower boundary
      ASSERT_FALSE(utils::roundingCellLowerBound(
          FloatingPoint::makeMaxNormal(size, true), rm, t0, strict));
    }
  }
}

TEST_F(TestTheoryBlackFpUtils, roundingCellLowerBoundKnownValues)
{
  // Hand-computed boundaries for c = 1.0 in Float16 (5, 11). The
  // predecessor of 1.0 is 1 - 2^-11 = 2047/2048, so the midpoint towards
  // 1.0 is 4095/4096. The significand of 1.0 is even (all stored bits 0).
  FloatingPointSize f16(5, 11);
  FloatingPoint one(f16, RoundingMode::ROUND_NEAREST_TIES_TO_EVEN, Rational(1));
  Rational t0;
  bool strict;

  ASSERT_TRUE(utils::roundingCellLowerBound(
      one, RoundingMode::ROUND_TOWARD_POSITIVE, t0, strict));
  ASSERT_EQ(t0, Rational(2047, 2048));
  ASSERT_TRUE(strict);

  ASSERT_TRUE(utils::roundingCellLowerBound(
      one, RoundingMode::ROUND_TOWARD_NEGATIVE, t0, strict));
  ASSERT_EQ(t0, Rational(1));
  ASSERT_FALSE(strict);

  // positive values round towards zero as for ROUND_TOWARD_NEGATIVE
  ASSERT_TRUE(utils::roundingCellLowerBound(
      one, RoundingMode::ROUND_TOWARD_ZERO, t0, strict));
  ASSERT_EQ(t0, Rational(1));
  ASSERT_FALSE(strict);

  // the tie rounds to 1.0 (even), so the boundary is inclusive
  ASSERT_TRUE(utils::roundingCellLowerBound(
      one, RoundingMode::ROUND_NEAREST_TIES_TO_EVEN, t0, strict));
  ASSERT_EQ(t0, Rational(4095, 4096));
  ASSERT_FALSE(strict);

  // the positive tie rounds away from zero, i.e., up to 1.0
  ASSERT_TRUE(utils::roundingCellLowerBound(
      one, RoundingMode::ROUND_NEAREST_TIES_TO_AWAY, t0, strict));
  ASSERT_EQ(t0, Rational(4095, 4096));
  ASSERT_FALSE(strict);

  // For c = -1.0, the predecessor is -(1 + 2^-10) = -1025/1024 and the
  // midpoint towards -1.0 is -2049/2048.
  FloatingPoint mone(
      f16, RoundingMode::ROUND_NEAREST_TIES_TO_EVEN, Rational(-1));

  ASSERT_TRUE(utils::roundingCellLowerBound(
      mone, RoundingMode::ROUND_TOWARD_POSITIVE, t0, strict));
  ASSERT_EQ(t0, Rational(-1025, 1024));
  ASSERT_TRUE(strict);

  ASSERT_TRUE(utils::roundingCellLowerBound(
      mone, RoundingMode::ROUND_TOWARD_NEGATIVE, t0, strict));
  ASSERT_EQ(t0, Rational(-1));
  ASSERT_FALSE(strict);

  // negative values round towards zero as for ROUND_TOWARD_POSITIVE
  ASSERT_TRUE(utils::roundingCellLowerBound(
      mone, RoundingMode::ROUND_TOWARD_ZERO, t0, strict));
  ASSERT_EQ(t0, Rational(-1025, 1024));
  ASSERT_TRUE(strict);

  // the tie rounds to -1.0 (even), so the boundary is inclusive
  ASSERT_TRUE(utils::roundingCellLowerBound(
      mone, RoundingMode::ROUND_NEAREST_TIES_TO_EVEN, t0, strict));
  ASSERT_EQ(t0, Rational(-2049, 2048));
  ASSERT_FALSE(strict);

  // the negative tie rounds away from zero, i.e., down to -1025/1024, so
  // the boundary of -1.0's cell is exclusive
  ASSERT_TRUE(utils::roundingCellLowerBound(
      mone, RoundingMode::ROUND_NEAREST_TIES_TO_AWAY, t0, strict));
  ASSERT_EQ(t0, Rational(-2049, 2048));
  ASSERT_TRUE(strict);
}

TEST_F(TestTheoryBlackFpUtils, roundingCellLowerBoundContract)
{
  // Validate the documented equivalence
  //   to_fp(rm, x) >=_fp c  iff  (strict ? x > t0 : x >= t0)
  // against the exact from-rational conversion, at sample points around the
  // boundary, at the cell's own values, and far away on both sides. The
  // equivalence is global, so any sample point must agree.
  Rational t0;
  bool strict;
  for (const auto& size : d_all_formats)
  {
    uint32_t bvSize = size.exponentWidth() + size.significandWidth();
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      FloatingPoint c(size, BitVector::mkRandom(bvSize));
      for (RoundingMode rm : d_all_rms)
      {
        if (!utils::roundingCellLowerBound(c, rm, t0, strict))
        {
          ASSERT_TRUE(c.isNaN() || c.isInfinite()
                      || FloatingPoint::predecessor(c).isInfinite());
          continue;
        }
        Rational rc = c.convertToRationalTotal(Rational(0));
        Rational rp =
            FloatingPoint::predecessor(c).convertToRationalTotal(Rational(0));
        Rational quarter = (rc - rp) / 4;
        for (const Rational& x : {t0,
                                  t0 - quarter,
                                  t0 + quarter,
                                  rp,
                                  rc,
                                  (rp + rc) / 2,
                                  t0 - Rational(1000000),
                                  t0 + Rational(1000000)})
        {
          checkContractAt(c, rm, t0, strict, x);
        }
      }
    }
  }
}

}  // namespace test
}  // namespace cvc5::internal
