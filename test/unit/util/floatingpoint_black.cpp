/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::FloatingPoint.
 *
 * Cross-checks the MPFR and SymFPU floating-point literal backends.
 * Ported from Bitwuzla's FP unit tests, see
 * https://github.com/bitwuzla/bitwuzla/tree/main/test/unit/fp
 * (Copyright (C) 2022 by the Bitwuzla authors, MIT license).
 */

#include "base/check.h"
#include "test.h"
#include "util/floatingpoint.h"
#ifdef CVC5_USE_MPFR
#include "util/floatingpoint_literal_mpfr.h"
#endif
#include "util/floatingpoint_literal_symfpu.h"
#include "util/random.h"

namespace cvc5::internal {
namespace test {

/* -------------------------------------------------------------------------- */

class TestUtilBlackFloatingPoint : public TestInternal
{
 protected:
  static constexpr uint32_t N_TESTS = 1000;

  TestUtilBlackFloatingPoint()
      : d_rng(Random::getRandom()),
        d_fp16(5, 11),
        d_fp32(8, 24),
        d_fp64(11, 53),
        d_fp128(15, 113)
  {
  }

  void SetUp() override
  {
    TestInternal::SetUp();
    d_all_formats = {d_fp16, d_fp32, d_fp64, d_fp128};
    d_formats_32_128 = {d_fp32, d_fp64, d_fp128};
    d_all_rms = {RoundingMode::ROUND_NEAREST_TIES_TO_EVEN,
                 RoundingMode::ROUND_NEAREST_TIES_TO_AWAY,
                 RoundingMode::ROUND_TOWARD_POSITIVE,
                 RoundingMode::ROUND_TOWARD_NEGATIVE,
                 RoundingMode::ROUND_TOWARD_ZERO};
  }

  /** @return A random rounding mode. */
  RoundingMode pickRm()
  {
    return d_all_rms[d_rng.pick<size_t>() % d_all_rms.size()];
  }

  /** @return A random floating-point format. */
  FloatingPointSize pickFormat()
  {
    return d_all_formats[d_rng.pick<size_t>() % d_all_formats.size()];
  }

  /** Test `fun` exhaustively for all Float16 values. */
  void testForFloat16(
      std::function<void(const BitVector&, const BitVector&)> fun)
  {
    uint32_t expSize = 5;
    uint32_t sigBits = 10;  // significand width minus hidden bit
    for (uint32_t i = 0; i < (1u << expSize); ++i)
    {
      BitVector bvexp(expSize, i);
      for (uint32_t j = 0; j < (1u << sigBits); ++j)
      {
        BitVector bvsig(sigBits, j);
        fun(bvexp, bvsig);
      }
    }
  }

  /** Test `fun` for given formats. */
  void testForFormats(
      const std::vector<FloatingPointSize>& formats,
      uint32_t nTests,
      std::function<void(const FloatingPointSize&, const BitVector&)> fun)
  {
    for (const auto& f : formats)
    {
      uint32_t bvSize = f.exponentWidth() + f.significandWidth();
      for (uint32_t i = 0; i < nTests; ++i)
      {
        BitVector bv = BitVector::mkRandom(bvSize);
        fun(f, bv);
      }
    }
  }

  Random& d_rng;

  FloatingPointSize d_fp16;
  FloatingPointSize d_fp32;
  FloatingPointSize d_fp64;
  FloatingPointSize d_fp128;

  std::vector<FloatingPointSize> d_all_formats;
  std::vector<FloatingPointSize> d_formats_32_128;
  std::vector<RoundingMode> d_all_rms;
};

/* -------------------------------------------------------------------------- */

TEST_F(TestUtilBlackFloatingPoint, move)
{
  BitVector bv1 = BitVector::mkRandom(d_fp16.packedWidth());
  BitVector bv2 = BitVector::mkRandom(d_fp128.packedWidth());
  FloatingPoint fp1(d_fp16, bv1);
  FloatingPoint fp2(d_fp128, bv2);

  fp1 = std::move(fp2);
  ASSERT_EQ(fp1.pack(), bv2);
  ASSERT_EQ(fp1.getSize(), d_fp128);

  auto fp3 = std::move(fp1);
  ASSERT_EQ(fp3.pack(), bv2);
  ASSERT_EQ(fp3.getSize(), d_fp128);

  FloatingPoint fp4(std::move(fp3));
  ASSERT_EQ(fp4.pack(), bv2);
  ASSERT_EQ(fp4.getSize(), d_fp128);
}

TEST_F(TestUtilBlackFloatingPoint, makeMinSubnormal)
{
  for (const auto& size : d_all_formats)
  {
    FloatingPoint fp = FloatingPoint::makeMinSubnormal(size, true);
    ASSERT_TRUE(fp.isSubnormal());
    FloatingPoint mfp = FloatingPoint::makeMinSubnormal(size, false);
    ASSERT_TRUE(mfp.isSubnormal());
  }
}

TEST_F(TestUtilBlackFloatingPoint, makeMaxSubnormal)
{
  for (const auto& size : d_all_formats)
  {
    FloatingPoint fp = FloatingPoint::makeMaxSubnormal(size, true);
    ASSERT_TRUE(fp.isSubnormal());
    FloatingPoint mfp = FloatingPoint::makeMaxSubnormal(size, false);
    ASSERT_TRUE(mfp.isSubnormal());
  }
}

TEST_F(TestUtilBlackFloatingPoint, makeMinNormal)
{
  for (const auto& size : d_all_formats)
  {
    FloatingPoint fp = FloatingPoint::makeMinNormal(size, true);
    ASSERT_TRUE(fp.isNormal());
    FloatingPoint mfp = FloatingPoint::makeMinNormal(size, false);
    ASSERT_TRUE(mfp.isNormal());
  }
}

TEST_F(TestUtilBlackFloatingPoint, makeMaxNormal)
{
  for (const auto& size : d_all_formats)
  {
    FloatingPoint fp = FloatingPoint::makeMaxNormal(size, true);
    ASSERT_TRUE(fp.isNormal());
    FloatingPoint mfp = FloatingPoint::makeMaxNormal(size, false);
    ASSERT_TRUE(mfp.isNormal());
  }
}

TEST_F(TestUtilBlackFloatingPoint, fromSbv1)
{
  BitVector bv0(1, 0u);
  BitVector bv1(1, 1u);
  for (const auto& bv : {bv0, bv1})
  {
    for (bool sign : {true, false})
    {
      FloatingPoint fp(FloatingPointSize(5, 11),
                       RoundingMode::ROUND_NEAREST_TIES_TO_AWAY,
                       bv,
                       sign);
    }
  }
}

/* -------------------------------------------------------------------------- */
/* Crosscheck MPFR and SymFPU back ends.                                      */
/* -------------------------------------------------------------------------- */

#ifdef CVC5_USE_MPFR
namespace {
/** @return An FP literal with MPFR as the back end. */
FloatingPointLiteralMPFR fpMPFR(const FloatingPointSize& fmt,
                                const BitVector& bv)
{
  return FloatingPointLiteralMPFR(fmt, bv);
}

/** @return An FP literal with SymFPU as the back end. */
FloatingPointLiteralSymFPU fpSymFPU(const FloatingPointSize& fmt,
                                    const BitVector& bv)
{
  return FloatingPointLiteralSymFPU(fmt, bv);
}
}  // namespace

TEST_F(TestUtilBlackFloatingPoint, pack)
{
  // Exhaustive for Float16
  auto fun16 = [this](const BitVector& bvexp, const BitVector& bvsig) {
    for (bool sign : {false, true})
    {
      BitVector bvsign = sign ? BitVector::mkOne(1) : BitVector::mkZero(1);
      BitVector bv = bvsign.concat(bvexp).concat(bvsig);

      auto mpfr = fpMPFR(d_fp16, bv);
      auto sym = fpSymFPU(d_fp16, bv);

      BitVector packedMpfr = mpfr.pack();
      BitVector packedSym = sym.pack();

      // Both backends must produce the same packed representation.
      ASSERT_EQ(packedMpfr, packedSym)
          << "pack mismatch for bv=" << bv.toString();
    }
  };
  testForFloat16(fun16);

  // Random for larger formats
  testForFormats(d_formats_32_128,
                 N_TESTS,
                 [](const FloatingPointSize& fmt, const BitVector& bv) {
                   auto mpfr = fpMPFR(fmt, bv);
                   auto sym = fpSymFPU(fmt, bv);
                   ASSERT_EQ(mpfr.pack(), sym.pack());
                 });
}

TEST_F(TestUtilBlackFloatingPoint, classification)
{
  BitVector ezero = BitVector::mkZero(5);
  BitVector eones = BitVector::mkOnes(5);
  BitVector szero = BitVector::mkZero(10);
  auto fun16 = [&, this](const BitVector& bvexp, const BitVector& bvsig) {
    for (bool sign : {false, true})
    {
      BitVector bvsign = sign ? BitVector::mkOne(1) : BitVector::mkZero(1);
      BitVector bv = bvsign.concat(bvexp).concat(bvsig);

      auto mpfr = fpMPFR(d_fp16, bv);
      auto sym = fpSymFPU(d_fp16, bv);

      ASSERT_EQ(mpfr.isNormal(), sym.isNormal());
      ASSERT_EQ(mpfr.isSubnormal(), sym.isSubnormal());
      ASSERT_EQ(mpfr.isZero(), sym.isZero());
      ASSERT_EQ(mpfr.isInfinite(), sym.isInfinite());
      ASSERT_EQ(mpfr.isNaN(), sym.isNaN());
      ASSERT_EQ(mpfr.isNegative(), sym.isNegative());
      ASSERT_EQ(mpfr.isPositive(), sym.isPositive());
      ASSERT_EQ(mpfr.getSign(), sym.getSign());

      if (bvexp != ezero)
      {
        if (bvexp != eones)
        {
          ASSERT_TRUE(mpfr.isNormal());
          ASSERT_FALSE(mpfr.isSubnormal());
          ASSERT_FALSE(mpfr.isInfinite());
          ASSERT_FALSE(mpfr.isNaN());
          ASSERT_FALSE(mpfr.isZero());
        }
        else
        {
          if (bvsig == szero)
          {
            ASSERT_TRUE(mpfr.isInfinite());
            ASSERT_FALSE(mpfr.isNormal());
            ASSERT_FALSE(mpfr.isSubnormal());
            ASSERT_FALSE(mpfr.isNaN());
            ASSERT_FALSE(mpfr.isZero());
          }
          else
          {
            ASSERT_TRUE(mpfr.isNaN());
            ASSERT_FALSE(mpfr.isNormal());
            ASSERT_FALSE(mpfr.isSubnormal());
            ASSERT_FALSE(mpfr.isInfinite());
            ASSERT_FALSE(mpfr.isZero());
          }
        }
      }
      else
      {
        if (bvsig == szero)
        {
          ASSERT_TRUE(mpfr.isZero());
          ASSERT_FALSE(mpfr.isNormal());
          ASSERT_FALSE(mpfr.isSubnormal());
          ASSERT_FALSE(mpfr.isInfinite());
          ASSERT_FALSE(mpfr.isNaN());
        }
        else
        {
          ASSERT_TRUE(mpfr.isSubnormal());
          ASSERT_FALSE(mpfr.isNormal());
          ASSERT_FALSE(mpfr.isInfinite());
          ASSERT_FALSE(mpfr.isNaN());
          ASSERT_FALSE(mpfr.isZero());
        }
      }
    }
  };
  testForFloat16(fun16);
  testForFormats(d_formats_32_128,
                 N_TESTS,
                 [](const FloatingPointSize& fmt, const BitVector& bv1) {
                   auto mpfr = fpMPFR(fmt, bv1);
                   auto sym = fpSymFPU(fmt, bv1);
                   ASSERT_EQ(mpfr.isNormal(), sym.isNormal());
                   ASSERT_EQ(mpfr.isSubnormal(), sym.isSubnormal());
                   ASSERT_EQ(mpfr.isZero(), sym.isZero());
                   ASSERT_EQ(mpfr.isNaN(), sym.isNaN());
                   ASSERT_EQ(mpfr.isInfinite(), sym.isInfinite());
                 });
}

TEST_F(TestUtilBlackFloatingPoint, components)
{
  auto fun16 = [this](const BitVector& bvexp, const BitVector& bvsig) {
    for (bool sign : {false, true})
    {
      BitVector bvsign = sign ? BitVector::mkOne(1) : BitVector::mkZero(1);
      BitVector bv = bvsign.concat(bvexp).concat(bvsig);

      auto mpfr = fpMPFR(d_fp16, bv);
      auto sym = fpSymFPU(d_fp16, bv);

      ASSERT_EQ(mpfr.getUnpackedExponent(), sym.getUnpackedExponent());
      ASSERT_EQ(mpfr.getUnpackedSignificand(), sym.getUnpackedSignificand());
    }
  };
  testForFloat16(fun16);
}

TEST_F(TestUtilBlackFloatingPoint, specialConstants)
{
  for (const auto& size : d_all_formats)
  {
    using SCKind = FloatingPointLiteral::SpecialConstKind;
    // NaN
    {
      auto mpfr = FloatingPointLiteralMPFR(size, SCKind::FPNAN);
      auto sym = FloatingPointLiteralSymFPU(size, SCKind::FPNAN);
      ASSERT_EQ(mpfr.pack(), sym.pack());
      ASSERT_TRUE(mpfr.isNaN());
      ASSERT_FALSE(mpfr.isInfinite());
      ASSERT_FALSE(mpfr.isNormal());
      ASSERT_FALSE(mpfr.isSubnormal());
      ASSERT_FALSE(mpfr.isZero());
    }
    for (bool sign : {false, true})
    {
      // +inf, -inf
      {
        auto mpfr = FloatingPointLiteralMPFR(size, SCKind::FPINF, sign);
        auto sym = FloatingPointLiteralSymFPU(size, SCKind::FPINF, sign);
        ASSERT_EQ(mpfr.pack(), sym.pack());
        ASSERT_TRUE(mpfr.isInfinite());
        ASSERT_FALSE(mpfr.isNaN());
        ASSERT_FALSE(mpfr.isNormal());
        ASSERT_FALSE(mpfr.isSubnormal());
        ASSERT_FALSE(mpfr.isZero());
      }
      // +zero, -zero
      {
        auto mpfr = FloatingPointLiteralMPFR(size, SCKind::FPZERO, sign);
        auto sym = FloatingPointLiteralSymFPU(size, SCKind::FPZERO, sign);
        ASSERT_EQ(mpfr.pack(), sym.pack());
        ASSERT_TRUE(mpfr.isZero());
        ASSERT_FALSE(mpfr.isInfinite());
        ASSERT_FALSE(mpfr.isNaN());
        ASSERT_FALSE(mpfr.isNormal());
        ASSERT_FALSE(mpfr.isSubnormal());
      }
    }
  }
}

TEST_F(TestUtilBlackFloatingPoint, fromUbvSbv)
{
  // Exhaustive for Float16
  for (uint64_t bw = 2; bw <= 16; ++bw)
  {
    for (uint64_t i = 0; i < (1ul << bw); ++i)
    {
      BitVector bv = BitVector(bw, i);
      for (RoundingMode rm : d_all_rms)
      {
        for (bool sign : {false, true})
        {
          FloatingPointLiteralMPFR mpfr(d_fp16, rm, bv, sign);
          FloatingPointLiteralSymFPU symfpu(d_fp16, rm, bv, sign);
          ASSERT_EQ(mpfr.pack(), symfpu.pack());
        }
      }
    }
  }
  for (const auto& f : d_all_formats)
  {
    for (uint64_t bw = 1; bw <= 16; ++bw)
    {
      for (uint64_t i = 0; i < 10; ++i)
      {
        auto bv = BitVector::mkRandom(bw);
        for (RoundingMode rm : d_all_rms)
        {
          for (auto sign : {false, true})
          {
            FloatingPointLiteralMPFR mpfr(f, rm, bv, sign);
            FloatingPointLiteralSymFPU symfpu(f, rm, bv, sign);
            ASSERT_EQ(mpfr.pack(), symfpu.pack());
          }
        }
      }
    }
  }
}

/* -------------------------------------------------------------------------- */
/* Unary operators without FM: fp.abs, fp.neg */
/* -------------------------------------------------------------------------- */

#define TEST_UNARY_OP(NAME, METHOD)                                           \
  TEST_F(TestUtilBlackFloatingPoint, NAME)                                    \
  {                                                                           \
    auto fun16 = [this](const BitVector& bvexp, const BitVector& bvsig) {     \
      for (bool sign : {false, true})                                         \
      {                                                                       \
        BitVector bvsign = sign ? BitVector::mkOne(1) : BitVector::mkZero(1); \
        BitVector bv = bvsign.concat(bvexp).concat(bvsig);                    \
        auto mpfr = fpMPFR(d_fp16, bv);                                       \
        auto sym = fpSymFPU(d_fp16, bv);                                      \
        ASSERT_EQ(mpfr.METHOD()->pack(), sym.METHOD()->pack());               \
      }                                                                       \
    };                                                                        \
    testForFloat16(fun16);                                                    \
    testForFormats(d_formats_32_128,                                          \
                   N_TESTS,                                                   \
                   [](const FloatingPointSize& fmt, const BitVector& bv) {    \
                     auto mpfr = fpMPFR(fmt, bv);                             \
                     auto sym = fpSymFPU(fmt, bv);                            \
                     ASSERT_EQ(mpfr.METHOD()->pack(), sym.METHOD()->pack());  \
                   });                                                        \
  }

TEST_UNARY_OP(absolute, absolute)
TEST_UNARY_OP(negate, negate)

#undef TEST_UNARY_OP

/* -------------------------------------------------------------------------- */
/* Unary operators with RM: fp.sqrt, fp.rti                                   */
/* -------------------------------------------------------------------------- */

#define TEST_UNARY_RM_OP(NAME, METHOD)                                         \
  TEST_F(TestUtilBlackFloatingPoint, NAME)                                     \
  {                                                                            \
    auto fun16 = [this](const BitVector& bvexp, const BitVector& bvsig) {      \
      for (bool sign : {false, true})                                          \
      {                                                                        \
        BitVector bvsign = sign ? BitVector::mkOne(1) : BitVector::mkZero(1);  \
        BitVector bv = bvsign.concat(bvexp).concat(bvsig);                     \
        auto mpfr = fpMPFR(d_fp16, bv);                                        \
        auto sym = fpSymFPU(d_fp16, bv);                                       \
        for (auto rm : d_all_rms)                                              \
        {                                                                      \
          ASSERT_EQ(mpfr.METHOD(rm)->pack(), sym.METHOD(rm)->pack());          \
        }                                                                      \
      }                                                                        \
    };                                                                         \
    testForFloat16(fun16);                                                     \
    testForFormats(d_formats_32_128,                                           \
                   N_TESTS,                                                    \
                   [this](const FloatingPointSize& fmt, const BitVector& bv) { \
                     auto mpfr = fpMPFR(fmt, bv);                              \
                     auto sym = fpSymFPU(fmt, bv);                             \
                     for (auto rm : d_all_rms)                                 \
                     {                                                         \
                       ASSERT_EQ(mpfr.METHOD(rm)->pack(),                      \
                                 sym.METHOD(rm)->pack());                      \
                     }                                                         \
                   });                                                         \
  }

TEST_UNARY_RM_OP(fpSqrt, sqrt)
TEST_UNARY_RM_OP(fpRti, rti)

#undef TEST_UNARY_RM_OP

/* -------------------------------------------------------------------------- */
/* Binary operator without RM: fp.rem                                         */
/* -------------------------------------------------------------------------- */

TEST_F(TestUtilBlackFloatingPoint, fpRem)
{
  // Exhaustive for Float16 (one operand exhaustive, other random)
  auto fun16 = [this](const BitVector& bvexp, const BitVector& bvsig) {
    bool sign = d_rng() & 1;
    BitVector bvsign = sign ? BitVector::mkOne(1) : BitVector::mkZero(1);
    BitVector bv1 = bvsign.concat(bvexp).concat(bvsig);
    BitVector bv2 = BitVector::mkRandom(16);

    auto mpfr1 = fpMPFR(d_fp16, bv1);
    auto mpfr2 = fpMPFR(d_fp16, bv2);
    auto sym1 = fpSymFPU(d_fp16, bv1);
    auto sym2 = fpSymFPU(d_fp16, bv2);

    ASSERT_EQ(mpfr1.rem(mpfr2)->pack(), sym1.rem(sym2)->pack());
  };
  testForFloat16(fun16);

  testForFormats(d_formats_32_128,
                 N_TESTS,
                 [](const FloatingPointSize& fmt, const BitVector& bv1) {
                   BitVector bv2 = BitVector::mkRandom(fmt.packedWidth());
                   auto mpfr1 = fpMPFR(fmt, bv1);
                   auto mpfr2 = fpMPFR(fmt, bv2);
                   auto sym1 = fpSymFPU(fmt, bv1);
                   auto sym2 = fpSymFPU(fmt, bv2);
                   ASSERT_EQ(mpfr1.rem(mpfr2)->pack(), sym1.rem(sym2)->pack());
                 });
}

/* -------------------------------------------------------------------------- */
/* Binary operators with RM: fp.add, fp.sub, fp.mult, fp.div                  */
/* -------------------------------------------------------------------------- */

#define TEST_BINARY_RM_OP(NAME, METHOD)                                     \
  TEST_F(TestUtilBlackFloatingPoint, NAME)                                  \
  {                                                                         \
    auto fun16 = [this](const BitVector& bvexp, const BitVector& bvsig) {   \
      bool sign = d_rng() & 1;                                              \
      BitVector bvsign = sign ? BitVector::mkOne(1) : BitVector::mkZero(1); \
      BitVector bv1 = bvsign.concat(bvexp).concat(bvsig);                   \
      BitVector bv2 = BitVector::mkRandom(16);                              \
      auto mpfr1 = fpMPFR(d_fp16, bv1);                                     \
      auto mpfr2 = fpMPFR(d_fp16, bv2);                                     \
      auto sym1 = fpSymFPU(d_fp16, bv1);                                    \
      auto sym2 = fpSymFPU(d_fp16, bv2);                                    \
      for (auto rm : d_all_rms)                                             \
      {                                                                     \
        ASSERT_EQ(mpfr1.METHOD(rm, mpfr2)->pack(),                          \
                  sym1.METHOD(rm, sym2)->pack());                           \
      }                                                                     \
    };                                                                      \
    testForFloat16(fun16);                                                  \
    testForFormats(                                                         \
        d_formats_32_128,                                                   \
        N_TESTS,                                                            \
        [this](const FloatingPointSize& fmt, const BitVector& bv1) {        \
          BitVector bv2 = BitVector::mkRandom(fmt.packedWidth());           \
          auto mpfr1 = fpMPFR(fmt, bv1);                                    \
          auto mpfr2 = fpMPFR(fmt, bv2);                                    \
          auto sym1 = fpSymFPU(fmt, bv1);                                   \
          auto sym2 = fpSymFPU(fmt, bv2);                                   \
          for (auto rm : d_all_rms)                                         \
          {                                                                 \
            ASSERT_EQ(mpfr1.METHOD(rm, mpfr2)->pack(),                      \
                      sym1.METHOD(rm, sym2)->pack());                       \
          }                                                                 \
        });                                                                 \
  }

TEST_BINARY_RM_OP(fpAdd, add)
TEST_BINARY_RM_OP(fpSub, sub)
TEST_BINARY_RM_OP(fpMult, mult)
TEST_BINARY_RM_OP(fpDiv, div)

#undef TEST_BINARY_RM_OP

/* -------------------------------------------------------------------------- */
/* Ternary operator with RM: fp.fma                                           */
/* -------------------------------------------------------------------------- */

TEST_F(TestUtilBlackFloatingPoint, fpFma)
{
  auto fun16 = [this](const BitVector& bvexp, const BitVector& bvsig) {
    bool sign = d_rng() & 1;
    BitVector bvsign = sign ? BitVector::mkOne(1) : BitVector::mkZero(1);
    BitVector bv1 = bvsign.concat(bvexp).concat(bvsig);
    BitVector bv2 = BitVector::mkRandom(16);
    BitVector bv3 = BitVector::mkRandom(16);

    auto mpfr1 = fpMPFR(d_fp16, bv1);
    auto mpfr2 = fpMPFR(d_fp16, bv2);
    auto mpfr3 = fpMPFR(d_fp16, bv3);
    auto sym1 = fpSymFPU(d_fp16, bv1);
    auto sym2 = fpSymFPU(d_fp16, bv2);
    auto sym3 = fpSymFPU(d_fp16, bv3);

    for (auto rm : d_all_rms)
    {
      ASSERT_EQ(mpfr1.fma(rm, mpfr2, mpfr3)->pack(),
                sym1.fma(rm, sym2, sym3)->pack());
    }
  };
  testForFloat16(fun16);

  testForFormats(d_formats_32_128,
                 N_TESTS,
                 [this](const FloatingPointSize& fmt, const BitVector& bv1) {
                   BitVector bv2 = BitVector::mkRandom(fmt.packedWidth());
                   BitVector bv3 = BitVector::mkRandom(fmt.packedWidth());
                   auto mpfr1 = fpMPFR(fmt, bv1);
                   auto mpfr2 = fpMPFR(fmt, bv2);
                   auto mpfr3 = fpMPFR(fmt, bv3);
                   auto sym1 = fpSymFPU(fmt, bv1);
                   auto sym2 = fpSymFPU(fmt, bv2);
                   auto sym3 = fpSymFPU(fmt, bv3);
                   for (auto rm : d_all_rms)
                   {
                     ASSERT_EQ(mpfr1.fma(rm, mpfr2, mpfr3)->pack(),
                               sym1.fma(rm, sym2, sym3)->pack());
                   }
                 });
}

/* -------------------------------------------------------------------------- */
/* Min/Max                                                                    */
/* -------------------------------------------------------------------------- */

TEST_F(TestUtilBlackFloatingPoint, fpMinMax)
{
  auto fun16 = [this](const BitVector& bvexp, const BitVector& bvsig) {
    bool sign = d_rng() & 1;
    BitVector bvsign = sign ? BitVector::mkOne(1) : BitVector::mkZero(1);
    BitVector bv1 = bvsign.concat(bvexp).concat(bvsig);
    BitVector bv2 = BitVector::mkRandom(16);

    auto mpfr1 = fpMPFR(d_fp16, bv1);
    auto mpfr2 = fpMPFR(d_fp16, bv2);
    auto sym1 = fpSymFPU(d_fp16, bv1);
    auto sym2 = fpSymFPU(d_fp16, bv2);

    for (bool zeroCaseLeft : {false, true})
    {
      ASSERT_EQ(mpfr1.maxTotal(mpfr2, zeroCaseLeft)->pack(),
                sym1.maxTotal(sym2, zeroCaseLeft)->pack());
      ASSERT_EQ(mpfr1.minTotal(mpfr2, zeroCaseLeft)->pack(),
                sym1.minTotal(sym2, zeroCaseLeft)->pack());
    }
  };
  testForFloat16(fun16);
}

/* -------------------------------------------------------------------------- */
/* Comparisons: ==, <=, <                                                     */
/* -------------------------------------------------------------------------- */

TEST_F(TestUtilBlackFloatingPoint, comparisons)
{
  auto fun16 = [this](const BitVector& bvexp, const BitVector& bvsig) {
    bool sign = d_rng() & 1;
    BitVector bvsign = sign ? BitVector::mkOne(1) : BitVector::mkZero(1);
    BitVector bv1 = bvsign.concat(bvexp).concat(bvsig);
    BitVector bv2 = BitVector::mkRandom(16);

    auto mpfr1 = fpMPFR(d_fp16, bv1);
    auto mpfr2 = fpMPFR(d_fp16, bv2);
    auto sym1 = fpSymFPU(d_fp16, bv1);
    auto sym2 = fpSymFPU(d_fp16, bv2);

    ASSERT_EQ(mpfr1 == mpfr2, sym1 == sym2);
    ASSERT_EQ(mpfr1 <= mpfr2, sym1 <= sym2);
    ASSERT_EQ(mpfr1 < mpfr2, sym1 < sym2);

    // Self-comparison
    ASSERT_EQ(mpfr1 == mpfr1, sym1 == sym1);
    ASSERT_EQ(mpfr1 <= mpfr1, sym1 <= sym1);
    ASSERT_EQ(mpfr1 < mpfr1, sym1 < sym1);
  };
  testForFloat16(fun16);
}

/* -------------------------------------------------------------------------- */
/* Convert (FP to FP)                                                         */
/* -------------------------------------------------------------------------- */

TEST_F(TestUtilBlackFloatingPoint, fpConvert)
{
  for (uint32_t i = 0; i < N_TESTS; ++i)
  {
    FloatingPointSize srcFmt = pickFormat();
    FloatingPointSize dstFmt = pickFormat();
    BitVector bv = BitVector::mkRandom(srcFmt.packedWidth());
    RoundingMode rm = pickRm();

    auto mpfr = fpMPFR(srcFmt, bv);
    auto sym = fpSymFPU(srcFmt, bv);

    ASSERT_EQ(mpfr.convert(dstFmt, rm)->pack(),
              sym.convert(dstFmt, rm)->pack());
  }
}

/* -------------------------------------------------------------------------- */
/* Convert to BV (signed / unsigned)                                          */
/* -------------------------------------------------------------------------- */

TEST_F(TestUtilBlackFloatingPoint, convertToBV)
{
  for (uint32_t i = 0; i < N_TESTS; ++i)
  {
    FloatingPointSize fmt = pickFormat();
    BitVector bv = BitVector::mkRandom(fmt.packedWidth());
    RoundingMode rm = pickRm();
    uint32_t width = 4 + (d_rng() % 61);
    BitVector undef = BitVector::mkRandom(width);

    auto mpfr = fpMPFR(fmt, bv);
    auto sym = fpSymFPU(fmt, bv);

    ASSERT_EQ(mpfr.convertToSBVTotal(width, rm, undef),
              sym.convertToSBVTotal(width, rm, undef));
    ASSERT_EQ(mpfr.convertToUBVTotal(width, rm, undef),
              sym.convertToUBVTotal(width, rm, undef));
  }
}

/* -------------------------------------------------------------------------- */
/* Chained operations                                                         */
/* -------------------------------------------------------------------------- */

TEST_F(TestUtilBlackFloatingPoint, chainedAddMul)
{
  testForFormats(d_all_formats,
                 N_TESTS,
                 [this](const FloatingPointSize& fmt, const BitVector& bv1) {
                   BitVector bv2 = BitVector::mkRandom(fmt.packedWidth());
                   BitVector bv3 = BitVector::mkRandom(fmt.packedWidth());

                   auto mpfr1 = fpMPFR(fmt, bv1);
                   auto mpfr2 = fpMPFR(fmt, bv2);
                   auto mpfr3 = fpMPFR(fmt, bv3);
                   auto sym1 = fpSymFPU(fmt, bv1);
                   auto sym2 = fpSymFPU(fmt, bv2);
                   auto sym3 = fpSymFPU(fmt, bv3);

                   RoundingMode rm1 = pickRm();
                   RoundingMode rm2 = pickRm();

                   // (a + b) * c
                   ASSERT_EQ(mpfr1.add(rm1, mpfr2)->mult(rm2, mpfr3)->pack(),
                             sym1.add(rm1, sym2)->mult(rm2, sym3)->pack());
                 });
}

TEST_F(TestUtilBlackFloatingPoint, chainedAbsAdd)
{
  testForFormats(d_all_formats,
                 N_TESTS,
                 [this](const FloatingPointSize& fmt, const BitVector& bv1) {
                   BitVector bv2 = BitVector::mkRandom(fmt.packedWidth());

                   auto mpfr1 = fpMPFR(fmt, bv1);
                   auto mpfr2 = fpMPFR(fmt, bv2);
                   auto sym1 = fpSymFPU(fmt, bv1);
                   auto sym2 = fpSymFPU(fmt, bv2);

                   RoundingMode rm = pickRm();

                   // abs(a + b)
                   ASSERT_EQ(mpfr1.add(rm, mpfr2)->absolute()->pack(),
                             sym1.add(rm, sym2)->absolute()->pack());
                   // neg(a + b)
                   ASSERT_EQ(mpfr1.add(rm, mpfr2)->negate()->pack(),
                             sym1.add(rm, sym2)->negate()->pack());
                 });
}

TEST_F(TestUtilBlackFloatingPoint, chainedSqrtAdd)
{
  testForFormats(d_all_formats,
                 N_TESTS,
                 [this](const FloatingPointSize& fmt, const BitVector& bv1) {
                   BitVector bv2 = BitVector::mkRandom(fmt.packedWidth());

                   auto mpfr1 = fpMPFR(fmt, bv1);
                   auto mpfr2 = fpMPFR(fmt, bv2);
                   auto sym1 = fpSymFPU(fmt, bv1);
                   auto sym2 = fpSymFPU(fmt, bv2);

                   RoundingMode rm1 = pickRm();
                   RoundingMode rm2 = pickRm();

                   // sqrt(a + b)
                   ASSERT_EQ(mpfr1.add(rm2, mpfr2)->sqrt(rm1)->pack(),
                             sym1.add(rm2, sym2)->sqrt(rm1)->pack());
                   // rti(a + b)
                   ASSERT_EQ(mpfr1.add(rm2, mpfr2)->rti(rm1)->pack(),
                             sym1.add(rm2, sym2)->rti(rm1)->pack());
                 });
}

TEST_F(TestUtilBlackFloatingPoint, chainedRemAdd)
{
  testForFormats(d_all_formats,
                 100,
                 [this](const FloatingPointSize& fmt, const BitVector& bv1) {
                   BitVector bv2 = BitVector::mkRandom(fmt.packedWidth());
                   BitVector bv3 = BitVector::mkRandom(fmt.packedWidth());

                   auto mpfr1 = fpMPFR(fmt, bv1);
                   auto mpfr2 = fpMPFR(fmt, bv2);
                   auto mpfr3 = fpMPFR(fmt, bv3);
                   auto sym1 = fpSymFPU(fmt, bv1);
                   auto sym2 = fpSymFPU(fmt, bv2);
                   auto sym3 = fpSymFPU(fmt, bv3);

                   RoundingMode rm = pickRm();

                   // (a + b) rem c
                   ASSERT_EQ(mpfr1.add(rm, mpfr2)->rem(mpfr3)->pack(),
                             sym1.add(rm, sym2)->rem(sym3)->pack());
                   // (a rem b) + c
                   ASSERT_EQ(mpfr1.rem(mpfr2)->add(rm, mpfr3)->pack(),
                             sym1.rem(sym2)->add(rm, sym3)->pack());
                 });
}
#endif

}  // namespace test
}  // namespace cvc5::internal
