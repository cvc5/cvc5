/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Exhaustive tests for the word-blasted encodings of floating-point
 * operations in small formats.
 */

#include <functional>
#include <utility>
#include <vector>

#include "smt/solver_engine.h"
#include "test_node.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"
#include "util/floatingpoint.h"
#include "util/result.h"
#include "util/roundingmode.h"

namespace cvc5::internal {

using namespace theory;

namespace test {

/**
 * For each instance, we check the validity of `table` for
 * - operator `<op>`
 * - a symbolic rounding mode `rm`
 * - a symbolic bit-vector term `b`, whose bits give the operands of `<op>`,
 *   either directly or reinterpreted as floating-point values via
 *   (_ to_fp e s)
 * - a decision tree `table` constructed over all rounding modes and values of
 *   `b`, whose leaves are (= (<op> rm b) v) for the expected results `v`
 *   computed by FloatingPoint.
 *
 * The decision tree is Boolean rather than a tree over the results, i.e.,
 * (= (<op> rm b) (ite c v1 v2)), since cvc5 introduces a fresh constant for
 * each ite of floating-point sort, which is considerably slower.
 *
 * FloatingPoint is an independent reference only if cvc5 is configured with
 * MPFR. Otherwise, it is SymFPU as well, and these tests check the symbolic
 * against the concrete instantiation of SymFPU.
 *
 * @note Script contrib/check-fp-word-blaster.py performs the same check for
 *       larger formats.
 */
class TestTheoryBlackFpWordBlaster : public TestNode
{
 protected:
  using Format = std::pair<uint32_t, uint32_t>;

  /**
   * The maximum format sizes (exponent plus significand size) and bit-vector
   * sizes of the inputs of each test. The default sizes include the smallest
   * formats with incorrect encodings in unpatched SymFPU (see
   * cmake/deps-utils/symfpu-*.patch), e.g., (3 4) and (3 5) for rti,
   * (3 2) -> (2 4) and (3 4) -> (2 5) for to_fp from floating-point and
   * 3-bit bit-vectors -> (2 4) for to_fp from bit-vectors.
   */
#ifdef CVC5_SLOW_TESTS
  static constexpr uint32_t MAX_SIZE_RTI = 11;
  static constexpr uint32_t MAX_SIZE_TO_FP_SRC = 8;
  static constexpr uint32_t MAX_SIZE_TO_FP_DST = 11;
  static constexpr uint32_t MAX_SIZE_TO_FP_BV = 8;
  static constexpr uint32_t MAX_SIZE_UNARY = 8;
  static constexpr uint32_t MAX_SIZE_BINARY = 5;
  static constexpr uint32_t MAX_SIZE_FMA = 4;
#else
  static constexpr uint32_t MAX_SIZE_RTI = 8;
  static constexpr uint32_t MAX_SIZE_TO_FP_SRC = 7;
  static constexpr uint32_t MAX_SIZE_TO_FP_DST = 7;
  static constexpr uint32_t MAX_SIZE_TO_FP_BV = 4;
  static constexpr uint32_t MAX_SIZE_UNARY = 6;
  static constexpr uint32_t MAX_SIZE_BINARY = 4;
  static constexpr uint32_t MAX_SIZE_FMA = 0;
#endif

  void SetUp() override
  {
    TestNode::SetUp();
    d_rm =
        d_skolemManager->mkDummySkolem("rm", d_nodeManager->roundingModeType());
    d_rms = {RoundingMode::ROUND_NEAREST_TIES_TO_EVEN,
             RoundingMode::ROUND_NEAREST_TIES_TO_AWAY,
             RoundingMode::ROUND_TOWARD_POSITIVE,
             RoundingMode::ROUND_TOWARD_NEGATIVE,
             RoundingMode::ROUND_TOWARD_ZERO};
  }

  /**
   * Get all formats of at most the given size.
   * @param maxSize The maximum size of the formats, given as the sum of
   *                exponent and significand size.
   * @return The formats.
   */
  static std::vector<Format> formats(uint32_t maxSize)
  {
    std::vector<Format> res;
    for (uint32_t expSize = 2; expSize < maxSize; ++expSize)
    {
      for (uint32_t sigSize = 2; expSize + sigSize <= maxSize; ++sigSize)
      {
        res.emplace_back(expSize, sigSize);
      }
    }
    return res;
  }

  /**
   * Get the i-th floating-point operand given by the bits of a bit-vector
   * term.
   * @param b      The bit-vector term.
   * @param format The format of the operand.
   * @param i      The index of the operand.
   * @return The operand.
   */
  Node operand(const Node& b, const Format& format, uint32_t i)
  {
    uint32_t size = format.first + format.second;
    return d_nodeManager->mkNode(
        d_nodeManager->mkConst(
            FloatingPointToFPIEEEBitVector(format.first, format.second)),
        bv::utils::mkExtract(b, (i + 1) * size - 1, i * size));
  }

  /**
   * Get the i-th floating-point operand given by the bits of a bit-vector
   * value.
   * @param bv     The bit-vector value.
   * @param format The format of the operand.
   * @param i      The index of the operand.
   * @return The operand.
   */
  static FloatingPoint operand(const BitVector& bv,
                               const Format& format,
                               uint32_t i)
  {
    uint32_t size = format.first + format.second;
    return FloatingPoint(
        format.first, format.second, bv.extract((i + 1) * size - 1, i * size));
  }

  /**
   * Check the word-blasted encoding of an operation for all rounding modes
   * and all values of a bit-vector input.
   * @param bvSize   The size of the bit-vector input.
   * @param mkTerm   The function to create the operation for a given rounding
   *                 mode and bit-vector input.
   * @param expected The function to compute the expected result value for a
   *                 given rounding mode and bit-vector value.
   * @return The result of the satisfiability check, unsat if the encoding is
   *         correct.
   */
  Result::Status check(
      uint32_t bvSize,
      const std::function<Node(const Node&, const Node&)>& mkTerm,
      const std::function<Node(RoundingMode, const BitVector&)>& expected)
  {
    Node b = d_skolemManager->mkDummySkolem(
        "b", d_nodeManager->mkBitVectorType(bvSize));
    Node term = mkTerm(d_rm, b);
    Node table;
    for (RoundingMode rm : d_rms)
    {
      std::vector<Node> values;
      for (uint64_t i = 0, n = uint64_t{1} << bvSize; i < n; ++i)
      {
        values.push_back(expected(rm, BitVector(bvSize, i)));
      }
      Node tree = mkTree(b, term, values, 0, bvSize);
      table = table.isNull()
                  ? tree
                  : d_nodeManager->mkNode(
                        Kind::ITE,
                        d_nodeManager->mkNode(
                            Kind::EQUAL, d_rm, d_nodeManager->mkConst(rm)),
                        tree,
                        table);
    }
    SolverEngine slv(d_nodeManager.get());
    slv.setOption("fp-exp", "true");
    // Bit-blasting into the main SAT solver is considerably faster than
    // lazy bit-blasting here.
    slv.setOption("bv-solver", "bitblast-internal");
    slv.assertFormula(table.notNode());
    return slv.checkSat().getStatus();
  }

  /** The rounding mode constant. */
  Node d_rm;
  /** All rounding modes. */
  std::vector<RoundingMode> d_rms;

 private:
  /**
   * Create a decision tree that checks for each value of the lower `size`
   * bits of `b` that `term` evaluates to its expected result.
   *
   * This encodes the expected results for one rounding mode, which are
   * computed concretely for every value of `b`, as a formula over `b` that
   * is compared against the word-blasted encoding of `term` (see check()).
   * The tree splits on the most significant bit first and its leaf for value
   * `i` of the lower `size` bits of `b` is (= term values[offset + i]). If
   * both subtrees of a split are equal, the split is omitted. This keeps the
   * tree small, since inputs that only differ in their lower bits often have
   * the same result, e.g., all NaNs, or all values that round to the same
   * integral value.
   *
   * @param b      The bit-vector input.
   * @param term   The operation applied to `b`.
   * @param values The expected results, indexed by the value of `b`.
   * @param offset The index of the first leaf of the tree in `values`.
   * @param size   The number of bits to split on.
   * @return The decision tree.
   */
  Node mkTree(const Node& b,
              const Node& term,
              const std::vector<Node>& values,
              uint64_t offset,
              uint32_t size)
  {
    if (size == 0)
    {
      return d_nodeManager->mkNode(Kind::EQUAL, term, values[offset]);
    }
    uint64_t half = uint64_t{1} << (size - 1);
    Node lo = mkTree(b, term, values, offset, size - 1);
    Node hi = mkTree(b, term, values, offset + half, size - 1);
    if (lo == hi)
    {
      return lo;
    }
    Node bit = bv::utils::mkExtract(b, size - 1, size - 1);
    return d_nodeManager->mkNode(
        Kind::ITE,
        d_nodeManager->mkNode(
            Kind::EQUAL, bit, bv::utils::mkOne(d_nodeManager.get(), 1)),
        hi,
        lo);
  }
};

TEST_F(TestTheoryBlackFpWordBlaster, rti)
{
  for (const Format& format : formats(MAX_SIZE_RTI))
  {
    auto mkTerm = [&](const Node& rm, const Node& b) {
      return d_nodeManager->mkNode(
          Kind::FLOATINGPOINT_RTI, rm, operand(b, format, 0));
    };
    auto expected = [&](RoundingMode rm, const BitVector& bv) {
      return d_nodeManager->mkConst(operand(bv, format, 0).rti(rm));
    };
    ASSERT_EQ(check(format.first + format.second, mkTerm, expected),
              Result::UNSAT)
        << "(_ FloatingPoint " << format.first << " " << format.second << ")";
  }
}

TEST_F(TestTheoryBlackFpWordBlaster, to_fp_from_fp)
{
  for (const Format& src : formats(MAX_SIZE_TO_FP_SRC))
  {
    for (const Format& dst : formats(MAX_SIZE_TO_FP_DST))
    {
      auto mkTerm = [&](const Node& rm, const Node& b) {
        return d_nodeManager->mkNode(
            d_nodeManager->mkConst(
                FloatingPointToFPFloatingPoint(dst.first, dst.second)),
            rm,
            operand(b, src, 0));
      };
      auto expected = [&](RoundingMode rm, const BitVector& bv) {
        return d_nodeManager->mkConst(
            operand(bv, src, 0)
                .convert(FloatingPointSize(dst.first, dst.second), rm));
      };
      ASSERT_EQ(check(src.first + src.second, mkTerm, expected), Result::UNSAT)
          << "(_ FloatingPoint " << src.first << " " << src.second
          << ") -> (_ FloatingPoint " << dst.first << " " << dst.second << ")";
    }
  }
}

TEST_F(TestTheoryBlackFpWordBlaster, to_fp_from_bv)
{
  for (uint32_t bvSize = 1; bvSize <= MAX_SIZE_TO_FP_BV; ++bvSize)
  {
    for (const Format& format : formats(MAX_SIZE_TO_FP_DST))
    {
      for (bool isSigned : {false, true})
      {
        auto mkTerm = [&](const Node& rm, const Node& b) {
          Node op =
              isSigned
                  ? d_nodeManager->mkConst(FloatingPointToFPSignedBitVector(
                        format.first, format.second))
                  : d_nodeManager->mkConst(FloatingPointToFPUnsignedBitVector(
                        format.first, format.second));
          return d_nodeManager->mkNode(op, rm, b);
        };
        auto expected = [&](RoundingMode rm, const BitVector& bv) {
          return d_nodeManager->mkConst(
              FloatingPoint(FloatingPointSize(format.first, format.second),
                            rm,
                            bv,
                            isSigned));
        };
        ASSERT_EQ(check(bvSize, mkTerm, expected), Result::UNSAT)
            << "(_ BitVec " << bvSize << ") -> (_ FloatingPoint "
            << format.first << " " << format.second
            << "), signed: " << isSigned;
      }
    }
  }
}

TEST_F(TestTheoryBlackFpWordBlaster, unary)
{
  for (const Format& format : formats(MAX_SIZE_UNARY))
  {
    for (Kind kind : {Kind::FLOATINGPOINT_ABS,
                      Kind::FLOATINGPOINT_NEG,
                      Kind::FLOATINGPOINT_SQRT,
                      Kind::FLOATINGPOINT_IS_INF,
                      Kind::FLOATINGPOINT_IS_NAN,
                      Kind::FLOATINGPOINT_IS_NEG,
                      Kind::FLOATINGPOINT_IS_NORMAL,
                      Kind::FLOATINGPOINT_IS_POS,
                      Kind::FLOATINGPOINT_IS_SUBNORMAL,
                      Kind::FLOATINGPOINT_IS_ZERO})
    {
      auto mkTerm = [&](const Node& rm, const Node& b) {
        Node x = operand(b, format, 0);
        return kind == Kind::FLOATINGPOINT_SQRT
                   ? d_nodeManager->mkNode(kind, rm, x)
                   : d_nodeManager->mkNode(kind, x);
      };
      auto expected = [&](RoundingMode rm, const BitVector& bv) {
        FloatingPoint x = operand(bv, format, 0);
        switch (kind)
        {
          case Kind::FLOATINGPOINT_ABS:
            return d_nodeManager->mkConst(x.absolute());
          case Kind::FLOATINGPOINT_NEG:
            return d_nodeManager->mkConst(x.negate());
          case Kind::FLOATINGPOINT_SQRT:
            return d_nodeManager->mkConst(x.sqrt(rm));
          case Kind::FLOATINGPOINT_IS_INF:
            return d_nodeManager->mkConst(x.isInfinite());
          case Kind::FLOATINGPOINT_IS_NAN:
            return d_nodeManager->mkConst(x.isNaN());
          case Kind::FLOATINGPOINT_IS_NEG:
            return d_nodeManager->mkConst(x.isNegative());
          case Kind::FLOATINGPOINT_IS_NORMAL:
            return d_nodeManager->mkConst(x.isNormal());
          case Kind::FLOATINGPOINT_IS_POS:
            return d_nodeManager->mkConst(x.isPositive());
          case Kind::FLOATINGPOINT_IS_SUBNORMAL:
            return d_nodeManager->mkConst(x.isSubnormal());
          default: Assert(kind == Kind::FLOATINGPOINT_IS_ZERO);
        }
        return d_nodeManager->mkConst(x.isZero());
      };
      ASSERT_EQ(check(format.first + format.second, mkTerm, expected),
                Result::UNSAT)
          << kind << " (_ FloatingPoint " << format.first << " "
          << format.second << ")";
    }
  }
}

TEST_F(TestTheoryBlackFpWordBlaster, binary)
{
  for (const Format& format : formats(MAX_SIZE_BINARY))
  {
    for (Kind kind : {Kind::FLOATINGPOINT_ADD,
                      Kind::FLOATINGPOINT_SUB,
                      Kind::FLOATINGPOINT_MULT,
                      Kind::FLOATINGPOINT_DIV,
                      Kind::FLOATINGPOINT_REM,
                      Kind::FLOATINGPOINT_EQ,
                      Kind::FLOATINGPOINT_LT,
                      Kind::FLOATINGPOINT_LEQ,
                      Kind::EQUAL})
    {
      bool hasRm = kind == Kind::FLOATINGPOINT_ADD
                   || kind == Kind::FLOATINGPOINT_SUB
                   || kind == Kind::FLOATINGPOINT_MULT
                   || kind == Kind::FLOATINGPOINT_DIV;
      auto mkTerm = [&](const Node& rm, const Node& b) {
        Node x = operand(b, format, 0);
        Node y = operand(b, format, 1);
        return hasRm ? d_nodeManager->mkNode(kind, rm, x, y)
                     : d_nodeManager->mkNode(kind, x, y);
      };
      auto expected = [&](RoundingMode rm, const BitVector& bv) {
        FloatingPoint x = operand(bv, format, 0);
        FloatingPoint y = operand(bv, format, 1);
        switch (kind)
        {
          case Kind::FLOATINGPOINT_ADD:
            return d_nodeManager->mkConst(x.add(rm, y));
          case Kind::FLOATINGPOINT_SUB:
            return d_nodeManager->mkConst(x.sub(rm, y));
          case Kind::FLOATINGPOINT_MULT:
            return d_nodeManager->mkConst(x.mult(rm, y));
          case Kind::FLOATINGPOINT_DIV:
            return d_nodeManager->mkConst(x.div(rm, y));
          case Kind::FLOATINGPOINT_REM: return d_nodeManager->mkConst(x.rem(y));
          case Kind::FLOATINGPOINT_EQ:
            // IEEE equality, false for NaN and true for -zero and +zero.
            return d_nodeManager->mkConst(x <= y && y <= x);
          case Kind::FLOATINGPOINT_LT: return d_nodeManager->mkConst(x < y);
          case Kind::FLOATINGPOINT_LEQ: return d_nodeManager->mkConst(x <= y);
          default: Assert(kind == Kind::EQUAL);
        }
        return d_nodeManager->mkConst(x == y);
      };
      ASSERT_EQ(check(2 * (format.first + format.second), mkTerm, expected),
                Result::UNSAT)
          << kind << " (_ FloatingPoint " << format.first << " "
          << format.second << ")";
    }
  }
}

TEST_F(TestTheoryBlackFpWordBlaster, fma)
{
  for (const Format& format : formats(MAX_SIZE_FMA))
  {
    auto mkTerm = [&](const Node& rm, const Node& b) {
      return d_nodeManager->mkNode(Kind::FLOATINGPOINT_FMA,
                                   {rm,
                                    operand(b, format, 0),
                                    operand(b, format, 1),
                                    operand(b, format, 2)});
    };
    auto expected = [&](RoundingMode rm, const BitVector& bv) {
      return d_nodeManager->mkConst(
          operand(bv, format, 0)
              .fma(rm, operand(bv, format, 1), operand(bv, format, 2)));
    };
    ASSERT_EQ(check(3 * (format.first + format.second), mkTerm, expected),
              Result::UNSAT)
        << "(_ FloatingPoint " << format.first << " " << format.second << ")";
  }
}

}  // namespace test
}  // namespace cvc5::internal
