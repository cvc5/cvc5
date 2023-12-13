/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of ff term parsing.
 */

#include <memory>
#include <utility>

#include "test_with_smt_parser.h"
#include "theory/ff/parse.h"

namespace cvc5::internal {

using namespace theory::ff;

namespace test {

class TestFfNodeParser : public TestWithSmtParser
{
};

TEST_F(TestFfNodeParser, bitConstraint)
{
  {
    doCommand("(define-sort F () (_ FiniteField 7))");
    doCommand("(declare-const x F)");
    EXPECT_TRUE(
        parse::bitConstraint(
            parseNode("(= (ff.mul x (ff.add (as ff-1 F) x)) (as ff0 F))"))
            .has_value());
    EXPECT_TRUE(
        parse::bitConstraint(
            parseNode("(= (as ff0 F) (ff.mul x (ff.add (as ff-1 F) x)))"))
            .has_value());
    EXPECT_TRUE(
        parse::bitConstraint(parseNode("(= x (ff.mul x x))")).has_value());
    EXPECT_FALSE(
        parse::bitConstraint(parseNode("(= x (ff.mul x x x))")).has_value());
    EXPECT_TRUE(
        parse::bitConstraint(
            parseNode(
                "(= (as ff0 F) (ff.add (ff.mul x x) (ff.mul (as ff-1 F) x)))"))
            .has_value());
    EXPECT_TRUE(
        parse::bitConstraint(
            parseNode("(= (as ff0 F) (ff.add (ff.mul (as ff-1 F) x x) x))"))
            .has_value());
    EXPECT_TRUE(
        parse::bitConstraint(
            parseNode("(= (as ff0 F) (ff.add (ff.mul x x (as ff-1 F)) x))"))
            .has_value());
    EXPECT_FALSE(
        parse::bitConstraint(parseNode("(= (as ff0 F) x)")).has_value());
    EXPECT_FALSE(parse::bitConstraint(parseNode("(= (as ff0 F) (ff.mul x x))"))
                     .has_value());
  }
}

TEST_F(TestFfNodeParser, linearMonomial)
{
  {
    doCommand("(define-sort F () (_ FiniteField 7))");
    doCommand("(declare-const x F)");
    doCommand("(declare-const y F)");
    EXPECT_TRUE(
        parse::linearMonomial(parseNode("(ff.mul x (as ff1 F))")).has_value());
    EXPECT_TRUE(
        parse::linearMonomial(parseNode("(ff.mul (as ff1 F) x)")).has_value());
    EXPECT_TRUE(parse::linearMonomial(parseNode("x")).has_value());
    EXPECT_TRUE(parse::linearMonomial(parseNode("(ff.neg x)")).has_value());
    EXPECT_FALSE(parse::linearMonomial(parseNode("(ff.add x y)")).has_value());
  }
}

TEST_F(TestFfNodeParser, extractLinearMonomials)
{
  {
    doCommand("(define-sort F () (_ FiniteField 5))");
    doCommand("(declare-const x F)");
    doCommand("(declare-const y F)");
    doCommand("(declare-const b0 F)");
    doCommand("(declare-const b1 F)");
    doCommand("(declare-const b2 F)");
    doCommand("(declare-const b3 F)");
    Node x = parseNode("x");
    Node y = parseNode("y");
    Node b0 = parseNode("b0");
    Node b1 = parseNode("b1");
    Node b2 = parseNode("b2");
    Node b3 = parseNode("b3");

    {
      // none
      const auto res =
          parse::extractLinearMonomials(parseNode("(ff.add "
                                                  "(ff.mul x y) "
                                                  "(ff.mul x y) "
                                                  "(ff.add x y) "
                                                  ")"));
      EXPECT_TRUE(res.has_value());
      const auto& [linearMonomials, others] = res.value();
      EXPECT_EQ(linearMonomials.size(), 0);
      EXPECT_EQ(others.size(), 3);
    }

    {
      // neg
      const auto res =
          parse::extractLinearMonomials(parseNode("(ff.add "
                                                  "(ff.mul x y) "
                                                  "(ff.neg x) "
                                                  "(ff.add x y) "
                                                  ")"));
      EXPECT_TRUE(res.has_value());
      const auto& [linearMonomials, others] = res.value();
      EXPECT_EQ(linearMonomials.size(), 1);
      EXPECT_EQ(linearMonomials[0].second.toSignedInteger(), -1);
      EXPECT_EQ(linearMonomials[0].first, x);
      EXPECT_EQ(others.size(), 2);
    }

    {
      // a few
      const auto res =
          parse::extractLinearMonomials(parseNode("(ff.add "
                                                  "(ff.mul x y) "
                                                  "(ff.mul x y) "
                                                  "(ff.mul (as ff3 F) y) "
                                                  "(ff.mul (as ff-1 F) x) "
                                                  "(ff.add x y) "
                                                  "(as ff4 F) "
                                                  ")"));
      EXPECT_TRUE(res.has_value());
      const auto& [linearMonomials, others] = res.value();
      EXPECT_EQ(linearMonomials.size(), 2);
      EXPECT_EQ(others.size(), 4);
    }
  }
}

TEST_F(TestFfNodeParser, bitSumsSimple)
{
  {
    doCommand("(define-sort F () (_ FiniteField 103))");
    doCommand("(declare-const x F)");
    doCommand("(declare-const y F)");
    doCommand("(declare-const b0 F)");
    doCommand("(declare-const b1 F)");
    doCommand("(declare-const b2 F)");
    doCommand("(declare-const b3 F)");
    Node b0 = parseNode("b0");
    Node b1 = parseNode("b1");
    Node b2 = parseNode("b2");
    Node b3 = parseNode("b3");
    std::unordered_set<Node> bits = {b0, b1, b2, b3};
    {
      // bitsum with implicit 1 coeff
      const auto res = parse::bitSums(
          parseNode("(ff.add x y b0 (ff.mul (as ff2 F) b1))"), bits);
      EXPECT_TRUE(res.has_value());
      const auto& [bitSums, others] = res.value();
      EXPECT_EQ(bitSums.size(), 1);
      EXPECT_EQ(bitSums[0].first.getValue(), 1);
      EXPECT_EQ(bitSums[0].second.size(), 2);
      EXPECT_EQ(bitSums[0].second[0], b0);
      EXPECT_EQ(bitSums[0].second[1], b1);
      EXPECT_EQ(others.size(), 2);
    }
    {
      // bitsum with negative coeffs
      const auto res = parse::bitSums(parseNode("(ff.add "
                                                "(ff.mul x y) "
                                                "x "
                                                "y "
                                                "(ff.mul (as ff-1 F) b0) "
                                                "(ff.mul (as ff-2 F) b1) "
                                                "(ff.mul (as ff-4 F) b2) "
                                                ")"),
                                      bits);
      EXPECT_TRUE(res.has_value());
      const auto& [bitSums, others] = res.value();
      EXPECT_EQ(bitSums.size(), 1);
      EXPECT_EQ(bitSums[0].first.toSignedInteger(), -1);
      EXPECT_EQ(bitSums[0].second.size(), 3);
      EXPECT_EQ(bitSums[0].second[0], b0);
      EXPECT_EQ(bitSums[0].second[1], b1);
      EXPECT_EQ(bitSums[0].second[2], b2);
      EXPECT_EQ(others.size(), 3);
    }
    {
      // bitsum with negative coeffs, and a gap followed by a single bit
      const auto res = parse::bitSums(
          parseNode("(ff.add (ff.mul x y) x y (ff.mul (as ff-1 F) b0) (ff.mul "
                    "(as ff-2 F) b1) (ff.mul (as ff-8 F) b3))"),
          bits);
      EXPECT_TRUE(res.has_value());
      const auto& [bitSums, others] = res.value();
      EXPECT_EQ(bitSums.size(), 1);
      EXPECT_EQ(bitSums[0].first.toSignedInteger(), -1);
      EXPECT_EQ(bitSums[0].second.size(), 2);
      EXPECT_EQ(bitSums[0].second[0], b0);
      EXPECT_EQ(bitSums[0].second[1], b1);
      EXPECT_EQ(others.size(), 4);
    }
    {
      // bitsum with negative coeffs and a stray bit
      const auto res = parse::bitSums(
          parseNode("(ff.add (ff.mul x y) x y (ff.mul (as ff-1 F) b0) (ff.mul "
                    "(as ff-2 F) b1) (ff.mul (as ff1 F) b3))"),
          bits);
      EXPECT_TRUE(res.has_value());
      const auto& [bitSums, others] = res.value();
      EXPECT_EQ(bitSums.size(), 1);
      EXPECT_EQ(bitSums[0].first.toSignedInteger(), -1);
      EXPECT_EQ(bitSums[0].second.size(), 2);
      EXPECT_EQ(bitSums[0].second[0], b0);
      EXPECT_EQ(bitSums[0].second[1], b1);
      EXPECT_EQ(others.size(), 4);
    }
    {
      // two bitsums with a gap
      const auto res = parse::bitSums(parseNode("(ff.add"
                                                "(ff.mul x y)"
                                                "y"
                                                "(ff.mul (as ff1 F) b0)"
                                                "(ff.mul (as ff2 F) b1)"
                                                "(ff.mul (as ff4 F) x)"
                                                "(ff.mul (as ff8 F) b2) "
                                                "(ff.mul (as ff16 F) b3)"
                                                ")"),
                                      bits);
      EXPECT_TRUE(res.has_value());
      const auto& [bitSums, others] = res.value();
      EXPECT_EQ(bitSums.size(), 1);
      EXPECT_EQ(bitSums[0].first.toSignedInteger(), 1);
      EXPECT_EQ(bitSums[0].second.size(), 5);
      EXPECT_EQ(others.size(), 2);
    }
    {
      // bitsum with weird, positive start
      const auto res = parse::bitSums(parseNode("(ff.add"
                                                "(ff.mul (as ff6 F) b0)"
                                                "(ff.mul (as ff12 F) b1)"
                                                "(ff.mul (as ff24 F) b2)"
                                                ")"),
                                      bits);
      EXPECT_TRUE(res.has_value());
      const auto& [bitSums, others] = res.value();
      EXPECT_EQ(bitSums.size(), 1);
      EXPECT_EQ(bitSums[0].first.toSignedInteger(), 6);
      EXPECT_EQ(bitSums[0].second.size(), 3);
      EXPECT_EQ(others.size(), 0);
    }
    {
      // bitsum with weird, positive and negative start
      const auto res = parse::bitSums(parseNode("(ff.add"
                                                "(ff.mul (as ff6 F) b0)"
                                                "(ff.mul (as ff12 F) b1)"
                                                "(ff.mul (as ff-4 F) b2)"
                                                "(ff.mul (as ff-8 F) b3)"
                                                ")"),
                                      bits);
      EXPECT_TRUE(res.has_value());
      const auto& [bitSums, others] = res.value();
      EXPECT_EQ(bitSums.size(), 2);
      EXPECT_EQ(bitSums[0].first.toSignedInteger(), -4);
      EXPECT_EQ(bitSums[0].second.size(), 2);
      EXPECT_EQ(bitSums[1].first.toSignedInteger(), 6);
      EXPECT_EQ(bitSums[1].second.size(), 2);
      EXPECT_EQ(others.size(), 0);
    }
  }
}

}  // namespace test
}  // namespace cvc5::internal
