/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for the strings/sequences rewriter.
 */

#include <iostream>
#include <memory>
#include <vector>

#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/sequence.h"
#include "test_smt.h"
#include "theory/rewriter.h"
#include "theory/strings/arith_entail.h"
#include "theory/strings/sequences_rewriter.h"
#include "theory/strings/strings_entail.h"
#include "theory/strings/strings_rewriter.h"
#include "util/rational.h"
#include "util/string.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory;
using namespace cvc5::internal::theory::strings;

namespace cvc5::internal {
namespace test {

class TestTheoryWhiteSequencesRewriter : public TestSmt
{
 protected:
  void SetUp() override
  {
    TestSmt::SetUp();
    Options opts;
    d_rewriter = d_slvEngine->getEnv().getRewriter();
    d_seqRewriter.reset(new SequencesRewriter(d_rewriter, nullptr));
  }

  Rewriter* d_rewriter;
  std::unique_ptr<SequencesRewriter> d_seqRewriter;

  void inNormalForm(Node t)
  {
    Node res_t = d_rewriter->extendedRewrite(t);

    std::cout << std::endl;
    std::cout << t << " ---> " << res_t << std::endl;
    ASSERT_EQ(t, res_t);
  }

  void sameNormalForm(Node t1, Node t2)
  {
    Node res_t1 = d_rewriter->extendedRewrite(t1);
    Node res_t2 = d_rewriter->extendedRewrite(t2);

    std::cout << std::endl;
    std::cout << t1 << " ---> " << res_t1 << std::endl;
    std::cout << t2 << " ---> " << res_t2 << std::endl;
    ASSERT_EQ(res_t1, res_t2);
  }

  void differentNormalForms(Node t1, Node t2)
  {
    Node res_t1 = d_rewriter->extendedRewrite(t1);
    Node res_t2 = d_rewriter->extendedRewrite(t2);

    std::cout << std::endl;
    std::cout << t1 << " ---> " << res_t1 << std::endl;
    std::cout << t2 << " ---> " << res_t2 << std::endl;
    ASSERT_NE(res_t1, res_t2);
  }
};

TEST_F(TestTheoryWhiteSequencesRewriter, check_entail_length_one)
{
  StringsEntail& se = d_seqRewriter->getStringsEntail();
  TypeNode intType = d_nodeManager->integerType();
  TypeNode strType = d_nodeManager->stringType();

  Node a = d_nodeManager->mkConst(String("A"));
  Node abcd = d_nodeManager->mkConst(String("ABCD"));
  Node aaad = d_nodeManager->mkConst(String("AAAD"));
  Node b = d_nodeManager->mkConst(String("B"));
  Node x = d_nodeManager->mkVar("x", strType);
  Node y = d_nodeManager->mkVar("y", strType);
  Node negOne = d_nodeManager->mkConstInt(Rational(-1));
  Node zero = d_nodeManager->mkConstInt(Rational(0));
  Node one = d_nodeManager->mkConstInt(Rational(1));
  Node two = d_nodeManager->mkConstInt(Rational(2));
  Node three = d_nodeManager->mkConstInt(Rational(3));
  Node i = d_nodeManager->mkVar("i", intType);

  ASSERT_TRUE(se.checkLengthOne(a));
  ASSERT_TRUE(se.checkLengthOne(a, true));

  Node substr = d_nodeManager->mkNode(kind::STRING_SUBSTR, x, zero, one);
  ASSERT_TRUE(se.checkLengthOne(substr));
  ASSERT_FALSE(se.checkLengthOne(substr, true));

  substr =
      d_nodeManager->mkNode(kind::STRING_SUBSTR,
                            d_nodeManager->mkNode(kind::STRING_CONCAT, a, x),
                            zero,
                            one);
  ASSERT_TRUE(se.checkLengthOne(substr));
  ASSERT_TRUE(se.checkLengthOne(substr, true));

  substr = d_nodeManager->mkNode(kind::STRING_SUBSTR, x, zero, two);
  ASSERT_FALSE(se.checkLengthOne(substr));
  ASSERT_FALSE(se.checkLengthOne(substr, true));
}

TEST_F(TestTheoryWhiteSequencesRewriter, check_entail_arith)
{
  ArithEntail& ae = d_seqRewriter->getArithEntail();
  TypeNode intType = d_nodeManager->integerType();
  TypeNode strType = d_nodeManager->stringType();

  Node z = d_nodeManager->mkVar("z", strType);
  Node n = d_nodeManager->mkVar("n", intType);
  Node one = d_nodeManager->mkConstInt(Rational(1));

  // 1 >= (str.len (str.substr z n 1)) ---> true
  Node substr_z = d_nodeManager->mkNode(
      kind::STRING_LENGTH,
      d_nodeManager->mkNode(kind::STRING_SUBSTR, z, n, one));
  ASSERT_TRUE(ae.check(one, substr_z));

  // (str.len (str.substr z n 1)) >= 1 ---> false
  ASSERT_FALSE(ae.check(substr_z, one));
}

TEST_F(TestTheoryWhiteSequencesRewriter, check_entail_with_with_assumption)
{
  ArithEntail& ae = d_seqRewriter->getArithEntail();
  TypeNode intType = d_nodeManager->integerType();
  TypeNode strType = d_nodeManager->stringType();

  Node x = d_nodeManager->mkVar("x", intType);
  Node y = d_nodeManager->mkVar("y", strType);
  Node z = d_nodeManager->mkVar("z", intType);

  Node zero = d_nodeManager->mkConstInt(Rational(0));
  Node one = d_nodeManager->mkConstInt(Rational(1));

  Node empty = d_nodeManager->mkConst(String(""));
  Node a = d_nodeManager->mkConst(String("A"));

  Node slen_y = d_nodeManager->mkNode(kind::STRING_LENGTH, y);
  Node x_plus_slen_y = d_nodeManager->mkNode(kind::ADD, x, slen_y);
  Node x_plus_slen_y_eq_zero = d_rewriter->rewrite(
      d_nodeManager->mkNode(kind::EQUAL, x_plus_slen_y, zero));

  // x + (str.len y) = 0 |= 0 >= x --> true
  ASSERT_TRUE(ae.checkWithAssumption(x_plus_slen_y_eq_zero, zero, x, false));

  // x + (str.len y) = 0 |= 0 > x --> false
  ASSERT_FALSE(ae.checkWithAssumption(x_plus_slen_y_eq_zero, zero, x, true));

  Node x_plus_slen_y_plus_z_eq_zero = d_rewriter->rewrite(d_nodeManager->mkNode(
      kind::EQUAL, d_nodeManager->mkNode(kind::ADD, x_plus_slen_y, z), zero));

  // x + (str.len y) + z = 0 |= 0 > x --> false
  ASSERT_FALSE(
      ae.checkWithAssumption(x_plus_slen_y_plus_z_eq_zero, zero, x, true));

  Node x_plus_slen_y_plus_slen_y_eq_zero =
      d_rewriter->rewrite(d_nodeManager->mkNode(
          kind::EQUAL,
          d_nodeManager->mkNode(kind::ADD, x_plus_slen_y, slen_y),
          zero));

  // x + (str.len y) + (str.len y) = 0 |= 0 >= x --> true
  ASSERT_TRUE(ae.checkWithAssumption(
      x_plus_slen_y_plus_slen_y_eq_zero, zero, x, false));

  Node five = d_nodeManager->mkConstInt(Rational(5));
  Node six = d_nodeManager->mkConstInt(Rational(6));
  Node x_plus_five = d_nodeManager->mkNode(kind::ADD, x, five);
  Node x_plus_five_lt_six =
      d_rewriter->rewrite(d_nodeManager->mkNode(kind::LT, x_plus_five, six));

  // x + 5 < 6 |= 0 >= x --> true
  ASSERT_TRUE(ae.checkWithAssumption(x_plus_five_lt_six, zero, x, false));

  // x + 5 < 6 |= 0 > x --> false
  ASSERT_TRUE(!ae.checkWithAssumption(x_plus_five_lt_six, zero, x, true));

  Node neg_x = d_nodeManager->mkNode(kind::NEG, x);
  Node x_plus_five_lt_five =
      d_rewriter->rewrite(d_nodeManager->mkNode(kind::LT, x_plus_five, five));

  // x + 5 < 5 |= -x >= 0 --> true
  ASSERT_TRUE(ae.checkWithAssumption(x_plus_five_lt_five, neg_x, zero, false));

  // x + 5 < 5 |= 0 > x --> true
  ASSERT_TRUE(ae.checkWithAssumption(x_plus_five_lt_five, zero, x, false));

  // 0 < x |= x >= (str.len (int.to.str x))
  Node assm = d_rewriter->rewrite(d_nodeManager->mkNode(kind::LT, zero, x));
  ASSERT_TRUE(ae.checkWithAssumption(
      assm,
      x,
      d_nodeManager->mkNode(kind::STRING_LENGTH,
                            d_nodeManager->mkNode(kind::STRING_ITOS, x)),
      false));
}

TEST_F(TestTheoryWhiteSequencesRewriter, rewrite_nth)
{
  TypeNode intType = d_nodeManager->integerType();

  Node x = d_nodeManager->mkVar("x", intType);
  Node y = d_nodeManager->mkVar("y", intType);
  Node z = d_nodeManager->mkVar("z", intType);
  Node w = d_nodeManager->mkVar("w", intType);
  Node v = d_nodeManager->mkVar("v", intType);

  Node zero = d_nodeManager->mkConstInt(0);
  Node one = d_nodeManager->mkConstInt(1);
  // Position that is greater than the maximum value that can be represented
  // with a uint32_t
  Node largePos = d_nodeManager->mkConstInt(
      static_cast<uint64_t>(std::numeric_limits<uint32_t>::max()) + 1);

  Node s01 = d_nodeManager->mkConst(Sequence(intType, {zero, one}));
  Node sx = d_nodeManager->mkNode(SEQ_UNIT, x);
  Node sy = d_nodeManager->mkNode(SEQ_UNIT, y);
  Node sz = d_nodeManager->mkNode(SEQ_UNIT, z);
  Node sw = d_nodeManager->mkNode(SEQ_UNIT, w);
  Node sv = d_nodeManager->mkNode(SEQ_UNIT, v);
  Node xyz = d_nodeManager->mkNode(STRING_CONCAT, sx, sy, sz);
  Node wv = d_nodeManager->mkNode(STRING_CONCAT, sw, sv);

  {
    // Same normal form for:
    //
    // (seq.nth (seq.unit x) 0)
    //
    // x
    Node n = d_nodeManager->mkNode(SEQ_NTH, sx, zero);
    sameNormalForm(n, x);
  }

  {
    // Same normal form for:
    //
    // (seq.nth (seq.++ (seq.unit x) (seq.unit y) (seq.unit z)) 0)
    //
    // x
    Node n = d_nodeManager->mkNode(SEQ_NTH, xyz, zero);
    sameNormalForm(n, x);
  }

  {
    // Same normal form for:
    //
    // (seq.nth (seq.++ (seq.unit x) (seq.unit y) (seq.unit z)) 0)
    //
    // x
    Node n = d_nodeManager->mkNode(SEQ_NTH, xyz, one);
    sameNormalForm(n, y);
  }

  {
    // Check that there are no errors when trying to rewrite
    // (seq.nth (seq.++ (seq.unit 0) (seq.unit 1)) n) where n cannot be
    // represented as a 32-bit integer
    Node n = d_nodeManager->mkNode(SEQ_NTH, s01, largePos);
    sameNormalForm(n, n);
  }
}

TEST_F(TestTheoryWhiteSequencesRewriter, rewrite_substr)
{
  StringsRewriter sr(d_rewriter, nullptr);
  TypeNode intType = d_nodeManager->integerType();
  TypeNode strType = d_nodeManager->stringType();

  Node empty = d_nodeManager->mkConst(String(""));
  Node a = d_nodeManager->mkConst(String("A"));
  Node b = d_nodeManager->mkConst(String("B"));
  Node abcd = d_nodeManager->mkConst(String("ABCD"));
  Node negone = d_nodeManager->mkConstInt(Rational(-1));
  Node zero = d_nodeManager->mkConstInt(Rational(0));
  Node one = d_nodeManager->mkConstInt(Rational(1));
  Node two = d_nodeManager->mkConstInt(Rational(2));
  Node three = d_nodeManager->mkConstInt(Rational(3));

  Node s = d_nodeManager->mkVar("s", strType);
  Node s2 = d_nodeManager->mkVar("s2", strType);
  Node x = d_nodeManager->mkVar("x", intType);
  Node y = d_nodeManager->mkVar("y", intType);

  // (str.substr "A" x x) --> ""
  Node n = d_nodeManager->mkNode(kind::STRING_SUBSTR, a, x, x);
  Node res = sr.rewriteSubstr(n);
  ASSERT_EQ(res, empty);

  // (str.substr "A" (+ x 1) x) -> ""
  n = d_nodeManager->mkNode(
      kind::STRING_SUBSTR,
      a,
      d_nodeManager->mkNode(
          kind::ADD, x, d_nodeManager->mkConstInt(Rational(1))),
      x);
  sameNormalForm(n, empty);

  // (str.substr "A" (+ x (str.len s2)) x) -> ""
  n = d_nodeManager->mkNode(
      kind::STRING_SUBSTR,
      a,
      d_nodeManager->mkNode(
          kind::ADD, x, d_nodeManager->mkNode(kind::STRING_LENGTH, s)),
      x);
  sameNormalForm(n, empty);

  // (str.substr "A" x y) -> (str.substr "A" x y)
  n = d_nodeManager->mkNode(kind::STRING_SUBSTR, a, x, y);
  res = sr.rewriteSubstr(n);
  ASSERT_EQ(res, n);

  // (str.substr "ABCD" (+ x 3) x) -> ""
  n = d_nodeManager->mkNode(
      kind::STRING_SUBSTR, abcd, d_nodeManager->mkNode(kind::ADD, x, three), x);
  sameNormalForm(n, empty);

  // (str.substr "ABCD" (+ x 2) x) -> (str.substr "ABCD" (+ x 2) x)
  n = d_nodeManager->mkNode(
      kind::STRING_SUBSTR, abcd, d_nodeManager->mkNode(kind::ADD, x, two), x);
  res = sr.rewriteSubstr(n);
  sameNormalForm(res, n);

  // (str.substr (str.substr s x x) x x) -> ""
  n = d_nodeManager->mkNode(kind::STRING_SUBSTR,
                            d_nodeManager->mkNode(kind::STRING_SUBSTR, s, x, x),
                            x,
                            x);
  sameNormalForm(n, empty);

  // Same normal form for:
  //
  // (str.substr (str.replace "" s "B") x x)
  //
  // (str.replace "" s (str.substr "B" x x)))
  Node lhs = d_nodeManager->mkNode(
      kind::STRING_SUBSTR,
      d_nodeManager->mkNode(kind::STRING_REPLACE, empty, s, b),
      x,
      x);
  Node rhs = d_nodeManager->mkNode(
      kind::STRING_REPLACE,
      empty,
      s,
      d_nodeManager->mkNode(kind::STRING_SUBSTR, b, x, x));
  sameNormalForm(lhs, rhs);

  // Same normal form:
  //
  // (str.substr (str.replace s "A" "B") 0 x)
  //
  // (str.replace (str.substr s 0 x) "A" "B")
  Node substr_repl = d_nodeManager->mkNode(
      kind::STRING_SUBSTR,
      d_nodeManager->mkNode(kind::STRING_REPLACE, s, a, b),
      zero,
      x);
  Node repl_substr = d_nodeManager->mkNode(
      kind::STRING_REPLACE,
      d_nodeManager->mkNode(kind::STRING_SUBSTR, s, zero, x),
      a,
      b);
  sameNormalForm(substr_repl, repl_substr);

  // Same normal form:
  //
  // (str.substr (str.replace s (str.substr (str.++ s2 "A") 0 1) "B") 0 x)
  //
  // (str.replace (str.substr s 0 x) (str.substr (str.++ s2 "A") 0 1) "B")
  Node substr_y =
      d_nodeManager->mkNode(kind::STRING_SUBSTR,
                            d_nodeManager->mkNode(kind::STRING_CONCAT, s2, a),
                            zero,
                            one);
  substr_repl = d_nodeManager->mkNode(
      kind::STRING_SUBSTR,
      d_nodeManager->mkNode(kind::STRING_REPLACE, s, substr_y, b),
      zero,
      x);
  repl_substr = d_nodeManager->mkNode(
      kind::STRING_REPLACE,
      d_nodeManager->mkNode(kind::STRING_SUBSTR, s, zero, x),
      substr_y,
      b);
  sameNormalForm(substr_repl, repl_substr);

  // (str.substr (str.int.to.str x) x x) ---> empty
  Node substr_itos = d_nodeManager->mkNode(
      kind::STRING_SUBSTR, d_nodeManager->mkNode(kind::STRING_ITOS, x), x, x);
  sameNormalForm(substr_itos, empty);

  // (str.substr s (* (- 1) (str.len s)) 1) ---> empty
  Node substr = d_nodeManager->mkNode(
      kind::STRING_SUBSTR,
      s,
      d_nodeManager->mkNode(
          kind::MULT, negone, d_nodeManager->mkNode(kind::STRING_LENGTH, s)),
      one);
  sameNormalForm(substr, empty);
}

TEST_F(TestTheoryWhiteSequencesRewriter, rewrite_update)
{
  TypeNode intType = d_nodeManager->integerType();

  Node x = d_nodeManager->mkVar("x", intType);
  Node y = d_nodeManager->mkVar("y", intType);
  Node z = d_nodeManager->mkVar("z", intType);
  Node w = d_nodeManager->mkVar("w", intType);
  Node v = d_nodeManager->mkVar("v", intType);

  Node negOne = d_nodeManager->mkConstInt(-1);
  Node zero = d_nodeManager->mkConstInt(0);
  Node one = d_nodeManager->mkConstInt(1);
  Node three = d_nodeManager->mkConstInt(3);

  Node sx = d_nodeManager->mkNode(SEQ_UNIT, x);
  Node sy = d_nodeManager->mkNode(SEQ_UNIT, y);
  Node sz = d_nodeManager->mkNode(SEQ_UNIT, z);
  Node sw = d_nodeManager->mkNode(SEQ_UNIT, w);
  Node sv = d_nodeManager->mkNode(SEQ_UNIT, v);
  Node xyz = d_nodeManager->mkNode(STRING_CONCAT, sx, sy, sz);
  Node wv = d_nodeManager->mkNode(STRING_CONCAT, sw, sv);

  {
    // Same normal form for:
    //
    // (seq.update
    //   (seq.unit x))
    //   0
    //   (seq.unit w))
    //
    // (seq.unit w)
    Node n = d_nodeManager->mkNode(STRING_UPDATE, sx, zero, sw);
    sameNormalForm(n, sw);
  }

  {
    // Same normal form for:
    //
    // (seq.update
    //   (seq.++ (seq.unit x) (seq.unit y) (seq.unit z))
    //   0
    //   (seq.unit w))
    //
    // (seq.++ (seq.unit w) (seq.unit y) (seq.unit z))
    Node n = d_nodeManager->mkNode(STRING_UPDATE, xyz, zero, sw);
    Node wyz = d_nodeManager->mkNode(STRING_CONCAT, sw, sy, sz);
    sameNormalForm(n, wyz);
  }

  {
    // Same normal form for:
    //
    // (seq.update
    //   (seq.++ (seq.unit x) (seq.unit y) (seq.unit z))
    //   1
    //   (seq.unit w))
    //
    // (seq.++ (seq.unit x) (seq.unit w) (seq.unit z))
    Node n = d_nodeManager->mkNode(STRING_UPDATE, xyz, one, sw);
    Node xwz = d_nodeManager->mkNode(STRING_CONCAT, sx, sw, sz);
    sameNormalForm(n, xwz);
  }

  {
    // Same normal form for:
    //
    // (seq.update
    //   (seq.++ (seq.unit x) (seq.unit y) (seq.unit z))
    //   1
    //   (seq.++ (seq.unit w) (seq.unit v)))
    //
    // (seq.++ (seq.unit x) (seq.unit w) (seq.unit v))
    Node n = d_nodeManager->mkNode(STRING_UPDATE, xyz, one, wv);
    Node xwv = d_nodeManager->mkNode(STRING_CONCAT, sx, sw, sv);
    sameNormalForm(n, xwv);
  }

  {
    // Same normal form for:
    //
    // (seq.update
    //   (seq.++ (seq.unit x) (seq.unit y) (seq.unit z))
    //   -1
    //   (seq.++ (seq.unit w) (seq.unit v)))
    //
    //  (seq.++ (seq.unit x) (seq.unit y) (seq.unit z))
    Node n = d_nodeManager->mkNode(STRING_UPDATE, xyz, negOne, wv);
    sameNormalForm(n, xyz);
  }

  {
    // Same normal form for:
    //
    // (seq.update
    //   (seq.++ (seq.unit x) (seq.unit y) (seq.unit z))
    //   3
    //   w)
    //
    //  (seq.++ (seq.unit x) (seq.unit y) (seq.unit z))
    Node n = d_nodeManager->mkNode(STRING_UPDATE, xyz, three, sw);
    sameNormalForm(n, xyz);
  }
}

TEST_F(TestTheoryWhiteSequencesRewriter, rewrite_concat)
{
  TypeNode intType = d_nodeManager->integerType();
  TypeNode strType = d_nodeManager->stringType();

  Node empty = d_nodeManager->mkConst(String(""));
  Node a = d_nodeManager->mkConst(String("A"));
  Node zero = d_nodeManager->mkConstInt(Rational(0));
  Node three = d_nodeManager->mkConstInt(Rational(3));

  Node i = d_nodeManager->mkVar("i", intType);
  Node s = d_nodeManager->mkVar("s", strType);
  Node x = d_nodeManager->mkVar("x", strType);
  Node y = d_nodeManager->mkVar("y", strType);

  // Same normal form for:
  //
  // (str.++ (str.replace "A" x "") "A")
  //
  // (str.++ "A" (str.replace "A" x ""))
  Node repl_a_x_e = d_nodeManager->mkNode(kind::STRING_REPLACE, a, x, empty);
  Node repl_a = d_nodeManager->mkNode(kind::STRING_CONCAT, repl_a_x_e, a);
  Node a_repl = d_nodeManager->mkNode(kind::STRING_CONCAT, a, repl_a_x_e);
  sameNormalForm(repl_a, a_repl);

  // Same normal form for:
  //
  // (str.++ y (str.replace "" x (str.substr y 0 3)) (str.substr y 0 3) "A"
  // (str.substr y 0 3))
  //
  // (str.++ y (str.substr y 0 3) (str.replace "" x (str.substr y 0 3)) "A"
  // (str.substr y 0 3))
  Node z = d_nodeManager->mkNode(kind::STRING_SUBSTR, y, zero, three);
  Node repl_e_x_z = d_nodeManager->mkNode(kind::STRING_REPLACE, empty, x, z);
  repl_a = d_nodeManager->mkNode(kind::STRING_CONCAT, {y, repl_e_x_z, z, a, z});
  a_repl = d_nodeManager->mkNode(kind::STRING_CONCAT, {y, z, repl_e_x_z, a, z});
  sameNormalForm(repl_a, a_repl);

  // Same normal form for:
  //
  // (str.++ "A" (str.replace "A" x "") (str.substr "A" 0 i))
  //
  // (str.++ (str.substr "A" 0 i) (str.replace "A" x "") "A")
  Node substr_a = d_nodeManager->mkNode(kind::STRING_SUBSTR, a, zero, i);
  Node a_substr_repl =
      d_nodeManager->mkNode(kind::STRING_CONCAT, a, substr_a, repl_a_x_e);
  Node substr_repl_a =
      d_nodeManager->mkNode(kind::STRING_CONCAT, substr_a, repl_a_x_e, a);
  sameNormalForm(a_substr_repl, substr_repl_a);

  // Same normal form for:
  //
  // (str.++ (str.replace "" x (str.substr "A" 0 i)) (str.substr "A" 0 i)
  // (str.at "A" i))
  //
  // (str.++ (str.at "A" i) (str.replace "" x (str.substr "A" 0 i)) (str.substr
  // "A" 0 i))
  Node charat_a = d_nodeManager->mkNode(kind::STRING_CHARAT, a, i);
  Node repl_e_x_s =
      d_nodeManager->mkNode(kind::STRING_REPLACE, empty, x, substr_a);
  Node repl_substr_a = d_nodeManager->mkNode(
      kind::STRING_CONCAT, repl_e_x_s, substr_a, charat_a);
  Node a_repl_substr = d_nodeManager->mkNode(
      kind::STRING_CONCAT, charat_a, repl_e_x_s, substr_a);
  sameNormalForm(repl_substr_a, a_repl_substr);
}

TEST_F(TestTheoryWhiteSequencesRewriter, length_preserve_rewrite)
{
  StringsRewriter sr(d_rewriter, nullptr);
  TypeNode intType = d_nodeManager->integerType();
  TypeNode strType = d_nodeManager->stringType();

  Node empty = d_nodeManager->mkConst(String(""));
  Node abcd = d_nodeManager->mkConst(String("ABCD"));
  Node f = d_nodeManager->mkConst(String("F"));
  Node gh = d_nodeManager->mkConst(String("GH"));
  Node ij = d_nodeManager->mkConst(String("IJ"));

  Node i = d_nodeManager->mkVar("i", intType);
  Node s = d_nodeManager->mkVar("s", strType);
  Node x = d_nodeManager->mkVar("x", strType);
  Node y = d_nodeManager->mkVar("y", strType);

  // Same length preserving rewrite for:
  //
  // (str.++ "ABCD" (str.++ x x))
  //
  // (str.++ "GH" (str.repl "GH" "IJ") "IJ")
  Node concat1 =
      d_nodeManager->mkNode(kind::STRING_CONCAT,
                            abcd,
                            d_nodeManager->mkNode(kind::STRING_CONCAT, x, x));
  Node concat2 = d_nodeManager->mkNode(
      kind::STRING_CONCAT,
      {gh, x, d_nodeManager->mkNode(kind::STRING_REPLACE, x, gh, ij), ij});
  Node res_concat1 = sr.lengthPreserveRewrite(concat1);
  Node res_concat2 = sr.lengthPreserveRewrite(concat2);
  ASSERT_EQ(res_concat1, res_concat2);
}

TEST_F(TestTheoryWhiteSequencesRewriter, rewrite_indexOf)
{
  TypeNode intType = d_nodeManager->integerType();
  TypeNode strType = d_nodeManager->stringType();

  Node a = d_nodeManager->mkConst(String("A"));
  Node abcd = d_nodeManager->mkConst(String("ABCD"));
  Node aaad = d_nodeManager->mkConst(String("AAAD"));
  Node b = d_nodeManager->mkConst(String("B"));
  Node c = d_nodeManager->mkConst(String("C"));
  Node ccc = d_nodeManager->mkConst(String("CCC"));
  Node x = d_nodeManager->mkVar("x", strType);
  Node y = d_nodeManager->mkVar("y", strType);
  Node negOne = d_nodeManager->mkConstInt(Rational(-1));
  Node zero = d_nodeManager->mkConstInt(Rational(0));
  Node one = d_nodeManager->mkConstInt(Rational(1));
  Node two = d_nodeManager->mkConstInt(Rational(2));
  Node three = d_nodeManager->mkConstInt(Rational(3));
  Node i = d_nodeManager->mkVar("i", intType);
  Node j = d_nodeManager->mkVar("j", intType);

  // Same normal form for:
  //
  // (str.to.int (str.indexof "A" x 1))
  //
  // (str.to.int (str.indexof "B" x 1))
  Node a_idof_x = d_nodeManager->mkNode(kind::STRING_INDEXOF, a, x, two);
  Node itos_a_idof_x = d_nodeManager->mkNode(kind::STRING_ITOS, a_idof_x);
  Node b_idof_x = d_nodeManager->mkNode(kind::STRING_INDEXOF, b, x, two);
  Node itos_b_idof_x = d_nodeManager->mkNode(kind::STRING_ITOS, b_idof_x);
  sameNormalForm(itos_a_idof_x, itos_b_idof_x);

  // Same normal form for:
  //
  // (str.indexof (str.++ "ABCD" x) y 3)
  //
  // (str.indexof (str.++ "AAAD" x) y 3)
  Node idof_abcd =
      d_nodeManager->mkNode(kind::STRING_INDEXOF,
                            d_nodeManager->mkNode(kind::STRING_CONCAT, abcd, x),
                            y,
                            three);
  Node idof_aaad =
      d_nodeManager->mkNode(kind::STRING_INDEXOF,
                            d_nodeManager->mkNode(kind::STRING_CONCAT, aaad, x),
                            y,
                            three);
  sameNormalForm(idof_abcd, idof_aaad);

  // (str.indexof (str.substr x 1 i) "A" i) ---> -1
  Node idof_substr = d_nodeManager->mkNode(
      kind::STRING_INDEXOF,
      d_nodeManager->mkNode(kind::STRING_SUBSTR, x, one, i),
      a,
      i);
  sameNormalForm(idof_substr, negOne);

  {
    // Same normal form for:
    //
    // (str.indexof (str.++ "B" "C" "A" x y) "A" 0)
    //
    // (+ 2 (str.indexof (str.++ "A" x y) "A" 0))
    Node lhs = d_nodeManager->mkNode(
        kind::STRING_INDEXOF,
        d_nodeManager->mkNode(kind::STRING_CONCAT, {b, c, a, x, y}),
        a,
        zero);
    Node rhs = d_nodeManager->mkNode(
        kind::ADD,
        two,
        d_nodeManager->mkNode(
            kind::STRING_INDEXOF,
            d_nodeManager->mkNode(kind::STRING_CONCAT, a, x, y),
            a,
            zero));
    sameNormalForm(lhs, rhs);
  }
}

TEST_F(TestTheoryWhiteSequencesRewriter, rewrite_replace)
{
  TypeNode intType = d_nodeManager->integerType();
  TypeNode strType = d_nodeManager->stringType();

  Node empty = d_nodeManager->mkConst(String(""));
  Node a = d_nodeManager->mkConst(String("A"));
  Node ab = d_nodeManager->mkConst(String("AB"));
  Node b = d_nodeManager->mkConst(String("B"));
  Node c = d_nodeManager->mkConst(String("C"));
  Node d = d_nodeManager->mkConst(String("D"));
  Node x = d_nodeManager->mkVar("x", strType);
  Node y = d_nodeManager->mkVar("y", strType);
  Node z = d_nodeManager->mkVar("z", strType);
  Node zero = d_nodeManager->mkConstInt(Rational(0));
  Node one = d_nodeManager->mkConstInt(Rational(1));
  Node n = d_nodeManager->mkVar("n", intType);

  // (str.replace (str.replace x "B" x) x "A") -->
  //   (str.replace (str.replace x "B" "A") x "A")
  Node repl_repl = d_nodeManager->mkNode(
      kind::STRING_REPLACE,
      d_nodeManager->mkNode(kind::STRING_REPLACE, x, b, x),
      x,
      a);
  Node repl_repl_short = d_nodeManager->mkNode(
      kind::STRING_REPLACE,
      d_nodeManager->mkNode(kind::STRING_REPLACE, x, b, a),
      x,
      a);
  sameNormalForm(repl_repl, repl_repl_short);

  // (str.replace "A" (str.replace "B", x, "C") "D") --> "A"
  repl_repl = d_nodeManager->mkNode(
      kind::STRING_REPLACE,
      a,
      d_nodeManager->mkNode(kind::STRING_REPLACE, b, x, c),
      d);
  sameNormalForm(repl_repl, a);

  // (str.replace "A" (str.replace "B", x, "A") "D") -/-> "A"
  repl_repl = d_nodeManager->mkNode(
      kind::STRING_REPLACE,
      a,
      d_nodeManager->mkNode(kind::STRING_REPLACE, b, x, a),
      d);
  differentNormalForms(repl_repl, a);

  // Same normal form for:
  //
  // (str.replace x (str.++ x y z) y)
  //
  // (str.replace x (str.++ x y z) z)
  Node xyz = d_nodeManager->mkNode(kind::STRING_CONCAT, x, y, z);
  Node repl_x_xyz = d_nodeManager->mkNode(kind::STRING_REPLACE, x, xyz, y);
  Node repl_x_zyx = d_nodeManager->mkNode(kind::STRING_REPLACE, x, xyz, z);
  sameNormalForm(repl_x_xyz, repl_x_zyx);

  // (str.replace "" (str.++ x x) x) --> ""
  Node repl_empty_xx =
      d_nodeManager->mkNode(kind::STRING_REPLACE,
                            empty,
                            d_nodeManager->mkNode(kind::STRING_CONCAT, x, x),
                            x);
  sameNormalForm(repl_empty_xx, empty);

  // (str.replace "AB" (str.++ x "A") x) --> (str.replace "AB" (str.++ x "A")
  // "")
  Node repl_ab_xa_x =
      d_nodeManager->mkNode(kind::STRING_REPLACE,
                            d_nodeManager->mkNode(kind::STRING_CONCAT, a, b),
                            d_nodeManager->mkNode(kind::STRING_CONCAT, x, a),
                            x);
  Node repl_ab_xa_e =
      d_nodeManager->mkNode(kind::STRING_REPLACE,
                            d_nodeManager->mkNode(kind::STRING_CONCAT, a, b),
                            d_nodeManager->mkNode(kind::STRING_CONCAT, x, a),
                            empty);
  sameNormalForm(repl_ab_xa_x, repl_ab_xa_e);

  // (str.replace "AB" (str.++ x "A") x) -/-> (str.replace "AB" (str.++ "A" x)
  // "")
  Node repl_ab_ax_e =
      d_nodeManager->mkNode(kind::STRING_REPLACE,
                            d_nodeManager->mkNode(kind::STRING_CONCAT, a, b),
                            d_nodeManager->mkNode(kind::STRING_CONCAT, a, x),
                            empty);
  differentNormalForms(repl_ab_ax_e, repl_ab_xa_e);

  // (str.replace "" (str.replace y x "A") y) ---> ""
  repl_repl = d_nodeManager->mkNode(
      kind::STRING_REPLACE,
      empty,
      d_nodeManager->mkNode(kind::STRING_REPLACE, y, x, a),
      y);
  sameNormalForm(repl_repl, empty);

  // (str.replace "" (str.replace x y x) x) ---> ""
  repl_repl = d_nodeManager->mkNode(
      kind::STRING_REPLACE,
      empty,
      d_nodeManager->mkNode(kind::STRING_REPLACE, x, y, x),
      x);
  sameNormalForm(repl_repl, empty);

  // (str.replace "" (str.substr x 0 1) x) ---> ""
  repl_repl = d_nodeManager->mkNode(
      kind::STRING_REPLACE,
      empty,
      d_nodeManager->mkNode(kind::STRING_SUBSTR, x, zero, one),
      x);
  sameNormalForm(repl_repl, empty);

  // Same normal form for:
  //
  // (str.replace "" (str.replace x y x) y)
  //
  // (str.replace "" x y)
  repl_repl = d_nodeManager->mkNode(
      kind::STRING_REPLACE,
      empty,
      d_nodeManager->mkNode(kind::STRING_REPLACE, x, y, x),
      y);
  Node repl = d_nodeManager->mkNode(kind::STRING_REPLACE, empty, x, y);
  sameNormalForm(repl_repl, repl);

  // Same normal form:
  //
  // (str.replace "B" (str.replace x "A" "B") "B")
  //
  // (str.replace "B" x "B"))
  repl_repl = d_nodeManager->mkNode(
      kind::STRING_REPLACE,
      b,
      d_nodeManager->mkNode(kind::STRING_REPLACE, x, a, b),
      b);
  repl = d_nodeManager->mkNode(kind::STRING_REPLACE, b, x, b);
  sameNormalForm(repl_repl, repl);

  // Different normal forms for:
  //
  // (str.replace "B" (str.replace "" x "A") "B")
  //
  // (str.replace "B" x "B")
  repl_repl = d_nodeManager->mkNode(
      kind::STRING_REPLACE,
      b,
      d_nodeManager->mkNode(kind::STRING_REPLACE, empty, x, a),
      b);
  repl = d_nodeManager->mkNode(kind::STRING_REPLACE, b, x, b);
  differentNormalForms(repl_repl, repl);

  {
    // Same normal form:
    //
    // (str.replace (str.++ "AB" x) "C" y)
    //
    // (str.++ "AB" (str.replace x "C" y))
    Node lhs =
        d_nodeManager->mkNode(kind::STRING_REPLACE,
                              d_nodeManager->mkNode(kind::STRING_CONCAT, ab, x),
                              c,
                              y);
    Node rhs = d_nodeManager->mkNode(
        kind::STRING_CONCAT,
        ab,
        d_nodeManager->mkNode(kind::STRING_REPLACE, x, c, y));
    sameNormalForm(lhs, rhs);
  }
}

TEST_F(TestTheoryWhiteSequencesRewriter, rewrite_replace_re)
{
  TypeNode intType = d_nodeManager->integerType();
  TypeNode strType = d_nodeManager->stringType();

  std::vector<Node> emptyVec;
  Node sigStar = d_nodeManager->mkNode(
      kind::REGEXP_STAR, d_nodeManager->mkNode(kind::REGEXP_ALLCHAR, emptyVec));
  Node foo = d_nodeManager->mkConst(String("FOO"));
  Node a = d_nodeManager->mkConst(String("A"));
  Node b = d_nodeManager->mkConst(String("B"));
  Node re =
      d_nodeManager->mkNode(kind::REGEXP_CONCAT,
                            d_nodeManager->mkNode(kind::STRING_TO_REGEXP, a),
                            sigStar,
                            d_nodeManager->mkNode(kind::STRING_TO_REGEXP, b));

  // Same normal form:
  //
  // (str.replace_re
  //   "AZZZB"
  //   (re.++ (str.to_re "A") re.all (str.to_re "B"))
  //   "FOO")
  //
  // "FOO"
  {
    Node t = d_nodeManager->mkNode(kind::STRING_REPLACE_RE,
                                   d_nodeManager->mkConst(String("AZZZB")),
                                   re,
                                   foo);
    Node res = d_nodeManager->mkConst(String("FOO"));
    sameNormalForm(t, res);
  }

  // Same normal form:
  //
  // (str.replace_re
  //   "ZAZZZBZZB"
  //   (re.++ (str.to_re "A") re.all (str.to_re "B"))
  //   "FOO")
  //
  // "ZFOOZZB"
  {
    Node t = d_nodeManager->mkNode(kind::STRING_REPLACE_RE,
                                   d_nodeManager->mkConst(String("ZAZZZBZZB")),
                                   re,
                                   foo);
    Node res = d_nodeManager->mkConst(String("ZFOOZZB"));
    sameNormalForm(t, res);
  }

  // Same normal form:
  //
  // (str.replace_re
  //   "ZAZZZBZAZB"
  //   (re.++ (str.to_re "A") re.all (str.to_re "B"))
  //   "FOO")
  //
  // "ZFOOZAZB"
  {
    Node t = d_nodeManager->mkNode(kind::STRING_REPLACE_RE,
                                   d_nodeManager->mkConst(String("ZAZZZBZAZB")),
                                   re,
                                   foo);
    Node res = d_nodeManager->mkConst(String("ZFOOZAZB"));
    sameNormalForm(t, res);
  }

  // Same normal form:
  //
  // (str.replace_re
  //   "ZZZ"
  //   (re.++ (str.to_re "A") re.all (str.to_re "B"))
  //   "FOO")
  //
  // "ZZZ"
  {
    Node t = d_nodeManager->mkNode(kind::STRING_REPLACE_RE,
                                   d_nodeManager->mkConst(String("ZZZ")),
                                   re,
                                   foo);
    Node res = d_nodeManager->mkConst(String("ZZZ"));
    sameNormalForm(t, res);
  }

  // Same normal form:
  //
  // (str.replace_re
  //   "ZZZ"
  //   re.all
  //   "FOO")
  //
  // "FOOZZZ"
  {
    Node t = d_nodeManager->mkNode(kind::STRING_REPLACE_RE,
                                   d_nodeManager->mkConst(String("ZZZ")),
                                   sigStar,
                                   foo);
    Node res = d_nodeManager->mkConst(String("FOOZZZ"));
    sameNormalForm(t, res);
  }

  // Same normal form:
  //
  // (str.replace_re
  //   ""
  //   re.all
  //   "FOO")
  //
  // "FOO"
  {
    Node t = d_nodeManager->mkNode(kind::STRING_REPLACE_RE,
                                   d_nodeManager->mkConst(String("")),
                                   sigStar,
                                   foo);
    Node res = d_nodeManager->mkConst(String("FOO"));
    sameNormalForm(t, res);
  }
}

TEST_F(TestTheoryWhiteSequencesRewriter, rewrite_replace_all)
{
  TypeNode intType = d_nodeManager->integerType();
  TypeNode strType = d_nodeManager->stringType();

  std::vector<Node> emptyVec;
  Node sigStar = d_nodeManager->mkNode(
      kind::REGEXP_STAR, d_nodeManager->mkNode(kind::REGEXP_ALLCHAR, emptyVec));
  Node foo = d_nodeManager->mkConst(String("FOO"));
  Node a = d_nodeManager->mkConst(String("A"));
  Node b = d_nodeManager->mkConst(String("B"));
  Node re =
      d_nodeManager->mkNode(kind::REGEXP_CONCAT,
                            d_nodeManager->mkNode(kind::STRING_TO_REGEXP, a),
                            sigStar,
                            d_nodeManager->mkNode(kind::STRING_TO_REGEXP, b));

  // Same normal form:
  //
  // (str.replace_re
  //   "AZZZB"
  //   (re.++ (str.to_re "A") re.all (str.to_re "B"))
  //   "FOO")
  //
  // "FOO"
  {
    Node t = d_nodeManager->mkNode(kind::STRING_REPLACE_RE_ALL,
                                   d_nodeManager->mkConst(String("AZZZB")),
                                   re,
                                   foo);
    Node res = d_nodeManager->mkConst(String("FOO"));
    sameNormalForm(t, res);
  }

  // Same normal form:
  //
  // (str.replace_re
  //   "ZAZZZBZZB"
  //   (re.++ (str.to_re "A") re.all (str.to_re "B"))
  //   "FOO")
  //
  // "ZFOOZZB"
  {
    Node t = d_nodeManager->mkNode(kind::STRING_REPLACE_RE_ALL,
                                   d_nodeManager->mkConst(String("ZAZZZBZZB")),
                                   re,
                                   foo);
    Node res = d_nodeManager->mkConst(String("ZFOOZZB"));
    sameNormalForm(t, res);
  }

  // Same normal form:
  //
  // (str.replace_re
  //   "ZAZZZBZAZB"
  //   (re.++ (str.to_re "A") re.all (str.to_re "B"))
  //   "FOO")
  //
  // "ZFOOZFOO"
  {
    Node t = d_nodeManager->mkNode(kind::STRING_REPLACE_RE_ALL,
                                   d_nodeManager->mkConst(String("ZAZZZBZAZB")),
                                   re,
                                   foo);
    Node res = d_nodeManager->mkConst(String("ZFOOZFOO"));
    sameNormalForm(t, res);
  }

  // Same normal form:
  //
  // (str.replace_re
  //   "ZZZ"
  //   (re.++ (str.to_re "A") re.all (str.to_re "B"))
  //   "FOO")
  //
  // "ZZZ"
  {
    Node t = d_nodeManager->mkNode(kind::STRING_REPLACE_RE_ALL,
                                   d_nodeManager->mkConst(String("ZZZ")),
                                   re,
                                   foo);
    Node res = d_nodeManager->mkConst(String("ZZZ"));
    sameNormalForm(t, res);
  }

  // Same normal form:
  //
  // (str.replace_re
  //   "ZZZ"
  //   re.all
  //   "FOO")
  //
  // "FOOFOOFOO"
  {
    Node t = d_nodeManager->mkNode(kind::STRING_REPLACE_RE_ALL,
                                   d_nodeManager->mkConst(String("ZZZ")),
                                   sigStar,
                                   foo);
    Node res = d_nodeManager->mkConst(String("FOOFOOFOO"));
    sameNormalForm(t, res);
  }

  // Same normal form:
  //
  // (str.replace_re
  //   ""
  //   re.all
  //   "FOO")
  //
  // ""
  {
    Node t = d_nodeManager->mkNode(kind::STRING_REPLACE_RE_ALL,
                                   d_nodeManager->mkConst(String("")),
                                   sigStar,
                                   foo);
    Node res = d_nodeManager->mkConst(String(""));
    sameNormalForm(t, res);
  }
}

TEST_F(TestTheoryWhiteSequencesRewriter, rewrite_contains)
{
  TypeNode intType = d_nodeManager->integerType();
  TypeNode strType = d_nodeManager->stringType();

  Node empty = d_nodeManager->mkConst(String(""));
  Node a = d_nodeManager->mkConst(String("A"));
  Node ab = d_nodeManager->mkConst(String("AB"));
  Node b = d_nodeManager->mkConst(String("B"));
  Node c = d_nodeManager->mkConst(String("C"));
  Node e = d_nodeManager->mkConst(String("E"));
  Node h = d_nodeManager->mkConst(String("H"));
  Node j = d_nodeManager->mkConst(String("J"));
  Node p = d_nodeManager->mkConst(String("P"));
  Node abc = d_nodeManager->mkConst(String("ABC"));
  Node def = d_nodeManager->mkConst(String("DEF"));
  Node ghi = d_nodeManager->mkConst(String("GHI"));
  Node x = d_nodeManager->mkVar("x", strType);
  Node y = d_nodeManager->mkVar("y", strType);
  Node xy = d_nodeManager->mkNode(kind::STRING_CONCAT, x, y);
  Node yx = d_nodeManager->mkNode(kind::STRING_CONCAT, y, x);
  Node z = d_nodeManager->mkVar("z", strType);
  Node n = d_nodeManager->mkVar("n", intType);
  Node m = d_nodeManager->mkVar("m", intType);
  Node one = d_nodeManager->mkConstInt(Rational(1));
  Node two = d_nodeManager->mkConstInt(Rational(2));
  Node three = d_nodeManager->mkConstInt(Rational(3));
  Node four = d_nodeManager->mkConstInt(Rational(4));
  Node t = d_nodeManager->mkConst(true);
  Node f = d_nodeManager->mkConst(false);

  // Same normal form for:
  //
  // (str.replace "A" (str.substr x 1 3) y z)
  //
  // (str.replace "A" (str.substr x 1 4) y z)
  Node substr_3 = d_nodeManager->mkNode(
      kind::STRING_REPLACE,
      a,
      d_nodeManager->mkNode(kind::STRING_SUBSTR, x, one, three),
      z);
  Node substr_4 = d_nodeManager->mkNode(
      kind::STRING_REPLACE,
      a,
      d_nodeManager->mkNode(kind::STRING_SUBSTR, x, one, four),
      z);
  sameNormalForm(substr_3, substr_4);

  // Same normal form for:
  //
  // (str.replace "A" (str.++ y (str.substr x 1 3)) y z)
  //
  // (str.replace "A" (str.++ y (str.substr x 1 4)) y z)
  Node concat_substr_3 = d_nodeManager->mkNode(
      kind::STRING_REPLACE,
      a,
      d_nodeManager->mkNode(
          kind::STRING_CONCAT,
          y,
          d_nodeManager->mkNode(kind::STRING_SUBSTR, x, one, three)),
      z);
  Node concat_substr_4 = d_nodeManager->mkNode(
      kind::STRING_REPLACE,
      a,
      d_nodeManager->mkNode(
          kind::STRING_CONCAT,
          y,
          d_nodeManager->mkNode(kind::STRING_SUBSTR, x, one, four)),
      z);
  sameNormalForm(concat_substr_3, concat_substr_4);

  // (str.contains "A" (str.++ a (str.replace "B", x, "C")) --> false
  Node ctn_repl = d_nodeManager->mkNode(
      kind::STRING_CONTAINS,
      a,
      d_nodeManager->mkNode(
          kind::STRING_CONCAT,
          a,
          d_nodeManager->mkNode(kind::STRING_REPLACE, b, x, c)));
  sameNormalForm(ctn_repl, f);

  // (str.contains x (str.++ x x)) --> (= x "")
  Node x_cnts_x_x = d_nodeManager->mkNode(
      kind::STRING_CONTAINS, x, d_nodeManager->mkNode(kind::STRING_CONCAT, x, x));
  sameNormalForm(x_cnts_x_x, d_nodeManager->mkNode(kind::EQUAL, x, empty));

  // Same normal form for:
  //
  // (str.contains (str.++ y x) (str.++ x z y))
  //
  // (and (str.contains (str.++ y x) (str.++ x y)) (= z ""))
  Node yx_cnts_xzy = d_nodeManager->mkNode(
      kind::STRING_CONTAINS,
      yx,
      d_nodeManager->mkNode(kind::STRING_CONCAT, x, z, y));
  Node yx_cnts_xy =
      d_nodeManager->mkNode(kind::AND,
                            d_nodeManager->mkNode(kind::EQUAL, z, empty),
                            d_nodeManager->mkNode(kind::STRING_CONTAINS, yx, xy));
  sameNormalForm(yx_cnts_xzy, yx_cnts_xy);

  // Same normal form for:
  //
  // (str.contains (str.substr x n (str.len y)) y)
  //
  // (= (str.substr x n (str.len y)) y)
  Node ctn_substr = d_nodeManager->mkNode(
      kind::STRING_CONTAINS,
      d_nodeManager->mkNode(kind::STRING_SUBSTR,
                            x,
                            n,
                            d_nodeManager->mkNode(kind::STRING_LENGTH, y)),
      y);
  Node substr_eq = d_nodeManager->mkNode(
      kind::EQUAL,
      d_nodeManager->mkNode(kind::STRING_SUBSTR,
                            x,
                            n,
                            d_nodeManager->mkNode(kind::STRING_LENGTH, y)),
      y);
  sameNormalForm(ctn_substr, substr_eq);

  // Same normal form for:
  //
  // (str.contains x (str.replace y x y))
  //
  // (str.contains x y)
  Node ctn_repl_y_x_y = d_nodeManager->mkNode(
      kind::STRING_CONTAINS,
      x,
      d_nodeManager->mkNode(kind::STRING_REPLACE, y, x, y));
  Node ctn_x_y = d_nodeManager->mkNode(kind::STRING_CONTAINS, x, y);
  sameNormalForm(ctn_repl_y_x_y, ctn_repl_y_x_y);

  // Same normal form for:
  //
  // (str.contains x (str.replace x y x))
  //
  // (= x (str.replace x y x))
  Node ctn_repl_self = d_nodeManager->mkNode(
      kind::STRING_CONTAINS,
      x,
      d_nodeManager->mkNode(kind::STRING_REPLACE, x, y, x));
  Node eq_repl = d_nodeManager->mkNode(
      kind::EQUAL, x, d_nodeManager->mkNode(kind::STRING_REPLACE, x, y, x));
  sameNormalForm(ctn_repl_self, eq_repl);

  // (str.contains x (str.++ "A" (str.replace x y x))) ---> false
  Node ctn_repl_self_f = d_nodeManager->mkNode(
      kind::STRING_CONTAINS,
      x,
      d_nodeManager->mkNode(
          kind::STRING_CONCAT,
          a,
          d_nodeManager->mkNode(kind::STRING_REPLACE, x, y, x)));
  sameNormalForm(ctn_repl_self_f, f);

  // Same normal form for:
  //
  // (str.contains x (str.replace "" x y))
  //
  // (= "" (str.replace "" x y))
  Node ctn_repl_empty = d_nodeManager->mkNode(
      kind::STRING_CONTAINS,
      x,
      d_nodeManager->mkNode(kind::STRING_REPLACE, empty, x, y));
  Node eq_repl_empty = d_nodeManager->mkNode(
      kind::EQUAL,
      empty,
      d_nodeManager->mkNode(kind::STRING_REPLACE, empty, x, y));
  sameNormalForm(ctn_repl_empty, eq_repl_empty);

  // Same normal form for:
  //
  // (str.contains x (str.++ x y))
  //
  // (= "" y)
  Node ctn_x_x_y = d_nodeManager->mkNode(
      kind::STRING_CONTAINS, x, d_nodeManager->mkNode(kind::STRING_CONCAT, x, y));
  Node eq_emp_y = d_nodeManager->mkNode(kind::EQUAL, empty, y);
  sameNormalForm(ctn_x_x_y, eq_emp_y);

  // Same normal form for:
  //
  // (str.contains (str.++ y x) (str.++ x y))
  //
  // (= (str.++ y x) (str.++ x y))
  Node ctn_yxxy = d_nodeManager->mkNode(kind::STRING_CONTAINS, yx, xy);
  Node eq_yxxy = d_nodeManager->mkNode(kind::EQUAL, yx, xy);
  sameNormalForm(ctn_yxxy, eq_yxxy);

  // (str.contains (str.replace x y x) x) ---> true
  ctn_repl = d_nodeManager->mkNode(
      kind::STRING_CONTAINS,
      d_nodeManager->mkNode(kind::STRING_REPLACE, x, y, x),
      x);
  sameNormalForm(ctn_repl, t);

  // (str.contains (str.replace (str.++ x y) z (str.++ y x)) x) ---> true
  ctn_repl = d_nodeManager->mkNode(
      kind::STRING_CONTAINS,
      d_nodeManager->mkNode(kind::STRING_REPLACE, xy, z, yx),
      x);
  sameNormalForm(ctn_repl, t);

  // (str.contains (str.++ z (str.replace (str.++ x y) z (str.++ y x))) x)
  //   ---> true
  ctn_repl = d_nodeManager->mkNode(
      kind::STRING_CONTAINS,
      d_nodeManager->mkNode(
          kind::STRING_CONCAT,
          z,
          d_nodeManager->mkNode(kind::STRING_REPLACE, xy, z, yx)),
      x);
  sameNormalForm(ctn_repl, t);

  // Same normal form for:
  //
  // (str.contains (str.replace x y x) y)
  //
  // (str.contains x y)
  Node lhs = d_nodeManager->mkNode(
      kind::STRING_CONTAINS,
      d_nodeManager->mkNode(kind::STRING_REPLACE, x, y, x),
      y);
  Node rhs = d_nodeManager->mkNode(kind::STRING_CONTAINS, x, y);
  sameNormalForm(lhs, rhs);

  // Same normal form for:
  //
  // (str.contains (str.replace x y x) "B")
  //
  // (str.contains x "B")
  lhs = d_nodeManager->mkNode(
      kind::STRING_CONTAINS,
      d_nodeManager->mkNode(kind::STRING_REPLACE, x, y, x),
      b);
  rhs = d_nodeManager->mkNode(kind::STRING_CONTAINS, x, b);
  sameNormalForm(lhs, rhs);

  // Same normal form for:
  //
  // (str.contains (str.replace x y x) (str.substr z n 1))
  //
  // (str.contains x (str.substr z n 1))
  Node substr_z = d_nodeManager->mkNode(kind::STRING_SUBSTR, z, n, one);
  lhs = d_nodeManager->mkNode(
      kind::STRING_CONTAINS,
      d_nodeManager->mkNode(kind::STRING_REPLACE, x, y, x),
      substr_z);
  rhs = d_nodeManager->mkNode(kind::STRING_CONTAINS, x, substr_z);
  sameNormalForm(lhs, rhs);

  // Same normal form for:
  //
  // (str.contains (str.replace x y z) z)
  //
  // (str.contains (str.replace x z y) y)
  lhs = d_nodeManager->mkNode(
      kind::STRING_CONTAINS,
      d_nodeManager->mkNode(kind::STRING_REPLACE, x, y, z),
      z);
  rhs = d_nodeManager->mkNode(
      kind::STRING_CONTAINS,
      d_nodeManager->mkNode(kind::STRING_REPLACE, x, z, y),
      y);
  sameNormalForm(lhs, rhs);

  // Same normal form for:
  //
  // (str.contains (str.replace x "A" "B") "A")
  //
  // (str.contains (str.replace x "A" "") "A")
  lhs = d_nodeManager->mkNode(
      kind::STRING_CONTAINS,
      d_nodeManager->mkNode(kind::STRING_REPLACE, x, a, b),
      a);
  rhs = d_nodeManager->mkNode(
      kind::STRING_CONTAINS,
      d_nodeManager->mkNode(kind::STRING_REPLACE, x, a, empty),
      a);
  sameNormalForm(lhs, rhs);

  {
    // (str.contains (str.++ x "A") (str.++ "B" x)) ---> false
    Node ctn =
        d_nodeManager->mkNode(kind::STRING_CONTAINS,
                              d_nodeManager->mkNode(kind::STRING_CONCAT, x, a),
                              d_nodeManager->mkNode(kind::STRING_CONCAT, b, x));
    sameNormalForm(ctn, f);
  }

  {
    // Same normal form for:
    //
    // (str.contains (str.replace x "ABC" "DEF") "GHI")
    //
    // (str.contains x "GHI")
    lhs = d_nodeManager->mkNode(
        kind::STRING_CONTAINS,
        d_nodeManager->mkNode(kind::STRING_REPLACE, x, abc, def),
        ghi);
    rhs = d_nodeManager->mkNode(kind::STRING_CONTAINS, x, ghi);
    sameNormalForm(lhs, rhs);
  }

  {
    // Different normal forms for:
    //
    // (str.contains (str.replace x "ABC" "DEF") "B")
    //
    // (str.contains x "B")
    lhs = d_nodeManager->mkNode(
        kind::STRING_CONTAINS,
        d_nodeManager->mkNode(kind::STRING_REPLACE, x, abc, def),
        b);
    rhs = d_nodeManager->mkNode(kind::STRING_CONTAINS, x, b);
    differentNormalForms(lhs, rhs);
  }

  {
    // Different normal forms for:
    //
    // (str.contains (str.replace x "B" "DEF") "ABC")
    //
    // (str.contains x "ABC")
    lhs = d_nodeManager->mkNode(
        kind::STRING_CONTAINS,
        d_nodeManager->mkNode(kind::STRING_REPLACE, x, b, def),
        abc);
    rhs = d_nodeManager->mkNode(kind::STRING_CONTAINS, x, abc);
    differentNormalForms(lhs, rhs);
  }

  {
    // Same normal form for:
    //
    // (str.contains "ABC" (str.at x n))
    //
    // (or (= x "")
    //     (= x "A") (= x "B") (= x "C"))
    Node cat = d_nodeManager->mkNode(kind::STRING_CHARAT, x, n);
    lhs = d_nodeManager->mkNode(kind::STRING_CONTAINS, abc, cat);
    rhs = d_nodeManager->mkNode(kind::OR,
                                {d_nodeManager->mkNode(kind::EQUAL, cat, empty),
                                 d_nodeManager->mkNode(kind::EQUAL, cat, a),
                                 d_nodeManager->mkNode(kind::EQUAL, cat, b),
                                 d_nodeManager->mkNode(kind::EQUAL, cat, c)});
    sameNormalForm(lhs, rhs);
  }
}

TEST_F(TestTheoryWhiteSequencesRewriter, infer_eqs_from_contains)
{
  StringsEntail& se = d_seqRewriter->getStringsEntail();
  TypeNode strType = d_nodeManager->stringType();

  Node empty = d_nodeManager->mkConst(String(""));
  Node a = d_nodeManager->mkConst(String("A"));
  Node b = d_nodeManager->mkConst(String("B"));
  Node x = d_nodeManager->mkVar("x", strType);
  Node y = d_nodeManager->mkVar("y", strType);
  Node xy = d_nodeManager->mkNode(kind::STRING_CONCAT, x, y);
  Node f = d_nodeManager->mkConst(false);

  // inferEqsFromContains("", (str.++ x y)) returns something equivalent to
  // (= "" y)
  Node empty_x_y =
      d_nodeManager->mkNode(kind::AND,
                            d_nodeManager->mkNode(kind::EQUAL, empty, x),
                            d_nodeManager->mkNode(kind::EQUAL, empty, y));
  sameNormalForm(se.inferEqsFromContains(empty, xy), empty_x_y);

  // inferEqsFromContains(x, (str.++ x y)) returns false
  Node bxya = d_nodeManager->mkNode(kind::STRING_CONCAT, {b, y, x, a});
  sameNormalForm(se.inferEqsFromContains(x, bxya), f);

  // inferEqsFromContains(x, y) returns null
  Node n = se.inferEqsFromContains(x, y);
  ASSERT_TRUE(n.isNull());

  // inferEqsFromContains(x, x) returns something equivalent to (= x x)
  Node eq_x_x = d_nodeManager->mkNode(kind::EQUAL, x, x);
  sameNormalForm(se.inferEqsFromContains(x, x), eq_x_x);

  // inferEqsFromContains((str.replace x "B" "A"), x) returns something
  // equivalent to (= (str.replace x "B" "A") x)
  Node repl = d_nodeManager->mkNode(kind::STRING_REPLACE, x, b, a);
  Node eq_repl_x = d_nodeManager->mkNode(kind::EQUAL, repl, x);
  sameNormalForm(se.inferEqsFromContains(repl, x), eq_repl_x);

  // inferEqsFromContains(x, (str.replace x "B" "A")) returns something
  // equivalent to (= (str.replace x "B" "A") x)
  Node eq_x_repl = d_nodeManager->mkNode(kind::EQUAL, x, repl);
  sameNormalForm(se.inferEqsFromContains(x, repl), eq_x_repl);
}

TEST_F(TestTheoryWhiteSequencesRewriter, rewrite_prefix_suffix)
{
  TypeNode strType = d_nodeManager->stringType();

  Node empty = d_nodeManager->mkConst(String(""));
  Node a = d_nodeManager->mkConst(String("A"));
  Node x = d_nodeManager->mkVar("x", strType);
  Node y = d_nodeManager->mkVar("y", strType);
  Node xx = d_nodeManager->mkNode(kind::STRING_CONCAT, x, x);
  Node xxa = d_nodeManager->mkNode(kind::STRING_CONCAT, x, x, a);
  Node xy = d_nodeManager->mkNode(kind::STRING_CONCAT, x, y);
  Node f = d_nodeManager->mkConst(false);

  // Same normal form for:
  //
  // (str.prefix (str.++ x y) x)
  //
  // (= y "")
  Node p_xy = d_nodeManager->mkNode(kind::STRING_PREFIX, xy, x);
  Node empty_y = d_nodeManager->mkNode(kind::EQUAL, y, empty);
  sameNormalForm(p_xy, empty_y);

  // Same normal form for:
  //
  // (str.suffix (str.++ x x) x)
  //
  // (= x "")
  Node p_xx = d_nodeManager->mkNode(kind::STRING_SUFFIX, xx, x);
  Node empty_x = d_nodeManager->mkNode(kind::EQUAL, x, empty);
  sameNormalForm(p_xx, empty_x);

  // (str.suffix x (str.++ x x "A")) ---> false
  Node p_xxa = d_nodeManager->mkNode(kind::STRING_SUFFIX, xxa, x);
  sameNormalForm(p_xxa, f);
}

TEST_F(TestTheoryWhiteSequencesRewriter, rewrite_equality_ext)
{
  TypeNode strType = d_nodeManager->stringType();
  TypeNode intType = d_nodeManager->integerType();

  Node empty = d_nodeManager->mkConst(String(""));
  Node a = d_nodeManager->mkConst(String("A"));
  Node aaa = d_nodeManager->mkConst(String("AAA"));
  Node b = d_nodeManager->mkConst(String("B"));
  Node ba = d_nodeManager->mkConst(String("BA"));
  Node w = d_nodeManager->mkVar("w", strType);
  Node x = d_nodeManager->mkVar("x", strType);
  Node y = d_nodeManager->mkVar("y", strType);
  Node z = d_nodeManager->mkVar("z", strType);
  Node xxa = d_nodeManager->mkNode(kind::STRING_CONCAT, x, x, a);
  Node f = d_nodeManager->mkConst(false);
  Node n = d_nodeManager->mkVar("n", intType);
  Node zero = d_nodeManager->mkConstInt(Rational(0));
  Node one = d_nodeManager->mkConstInt(Rational(1));
  Node three = d_nodeManager->mkConstInt(Rational(3));

  // Same normal form for:
  //
  // (= "" (str.replace "" x "B"))
  //
  // (not (= x ""))
  Node empty_repl = d_nodeManager->mkNode(
      kind::EQUAL,
      empty,
      d_nodeManager->mkNode(kind::STRING_REPLACE, empty, x, b));
  Node empty_x = d_nodeManager->mkNode(
      kind::NOT, d_nodeManager->mkNode(kind::EQUAL, x, empty));
  sameNormalForm(empty_repl, empty_x);

  // Same normal form for:
  //
  // (= "" (str.replace x y (str.++ x x "A")))
  //
  // (and (= x "") (not (= y "")))
  Node empty_repl_xaa = d_nodeManager->mkNode(
      kind::EQUAL,
      empty,
      d_nodeManager->mkNode(kind::STRING_REPLACE, x, y, xxa));
  Node empty_xy = d_nodeManager->mkNode(
      kind::AND,
      d_nodeManager->mkNode(kind::EQUAL, x, empty),
      d_nodeManager->mkNode(kind::NOT,
                            d_nodeManager->mkNode(kind::EQUAL, y, empty)));
  sameNormalForm(empty_repl_xaa, empty_xy);

  // (= "" (str.replace (str.++ x x "A") x y)) ---> false
  Node empty_repl_xxaxy = d_nodeManager->mkNode(
      kind::EQUAL,
      empty,
      d_nodeManager->mkNode(kind::STRING_REPLACE, xxa, x, y));
  Node eq_xxa_repl = d_nodeManager->mkNode(
      kind::EQUAL,
      xxa,
      d_nodeManager->mkNode(kind::STRING_REPLACE, empty, y, x));
  sameNormalForm(empty_repl_xxaxy, f);

  // Same normal form for:
  //
  // (= "" (str.replace "A" x y))
  //
  // (= "A" (str.replace "" y x))
  Node empty_repl_axy = d_nodeManager->mkNode(
      kind::EQUAL, empty, d_nodeManager->mkNode(kind::STRING_REPLACE, a, x, y));
  Node eq_a_repl = d_nodeManager->mkNode(
      kind::EQUAL, a, d_nodeManager->mkNode(kind::STRING_REPLACE, empty, y, x));
  sameNormalForm(empty_repl_axy, eq_a_repl);

  // Same normal form for:
  //
  // (= "" (str.replace x "A" ""))
  //
  // (str.prefix x "A")
  Node empty_repl_a = d_nodeManager->mkNode(
      kind::EQUAL,
      empty,
      d_nodeManager->mkNode(kind::STRING_REPLACE, x, a, empty));
  Node prefix_a = d_nodeManager->mkNode(kind::STRING_PREFIX, x, a);
  sameNormalForm(empty_repl_a, prefix_a);

  // Same normal form for:
  //
  // (= "" (str.substr x 1 2))
  //
  // (<= (str.len x) 1)
  Node empty_substr = d_nodeManager->mkNode(
      kind::EQUAL,
      empty,
      d_nodeManager->mkNode(kind::STRING_SUBSTR, x, one, three));
  Node leq_len_x = d_nodeManager->mkNode(
      kind::LEQ, d_nodeManager->mkNode(kind::STRING_LENGTH, x), one);
  sameNormalForm(empty_substr, leq_len_x);

  // Different normal form for:
  //
  // (= "" (str.substr x 0 n))
  //
  // (<= n 0)
  Node empty_substr_x = d_nodeManager->mkNode(
      kind::EQUAL,
      empty,
      d_nodeManager->mkNode(kind::STRING_SUBSTR, x, zero, n));
  Node leq_n = d_nodeManager->mkNode(kind::LEQ, n, zero);
  differentNormalForms(empty_substr_x, leq_n);

  // Same normal form for:
  //
  // (= "" (str.substr "A" 0 n))
  //
  // (<= n 0)
  Node empty_substr_a = d_nodeManager->mkNode(
      kind::EQUAL,
      empty,
      d_nodeManager->mkNode(kind::STRING_SUBSTR, a, zero, n));
  sameNormalForm(empty_substr_a, leq_n);

  // Same normal form for:
  //
  // (= (str.++ x x a) (str.replace y (str.++ x x a) y))
  //
  // (= (str.++ x x a) y)
  Node eq_xxa_repl_y = d_nodeManager->mkNode(
      kind::EQUAL, xxa, d_nodeManager->mkNode(kind::STRING_REPLACE, y, xxa, y));
  Node eq_xxa_y = d_nodeManager->mkNode(kind::EQUAL, xxa, y);
  sameNormalForm(eq_xxa_repl_y, eq_xxa_y);

  // (= (str.++ x x a) (str.replace (str.++ x x a) "A" "B")) ---> false
  Node eq_xxa_repl_xxa = d_nodeManager->mkNode(
      kind::EQUAL, xxa, d_nodeManager->mkNode(kind::STRING_REPLACE, xxa, a, b));
  sameNormalForm(eq_xxa_repl_xxa, f);

  // Same normal form for:
  //
  // (= (str.replace x "A" "B") "")
  //
  // (= x "")
  Node eq_repl = d_nodeManager->mkNode(
      kind::EQUAL, d_nodeManager->mkNode(kind::STRING_REPLACE, x, a, b), empty);
  Node eq_x = d_nodeManager->mkNode(kind::EQUAL, x, empty);
  sameNormalForm(eq_repl, eq_x);

  {
    // Same normal form for:
    //
    // (= (str.replace y "A" "B") "B")
    //
    // (= (str.replace y "B" "A") "A")
    Node lhs = d_nodeManager->mkNode(
        kind::EQUAL, d_nodeManager->mkNode(kind::STRING_REPLACE, x, a, b), b);
    Node rhs = d_nodeManager->mkNode(
        kind::EQUAL, d_nodeManager->mkNode(kind::STRING_REPLACE, x, b, a), a);
    sameNormalForm(lhs, rhs);
  }

  {
    // Same normal form for:
    //
    // (= (str.++ x "A" y) (str.++ "A" "A" (str.substr "AAA" 0 n)))
    //
    // (= (str.++ y x) (str.++ (str.substr "AAA" 0 n) "A"))
    Node lhs = d_nodeManager->mkNode(
        kind::EQUAL,
        d_nodeManager->mkNode(kind::STRING_CONCAT, x, a, y),
        d_nodeManager->mkNode(
            kind::STRING_CONCAT,
            a,
            a,
            d_nodeManager->mkNode(kind::STRING_SUBSTR, aaa, zero, n)));
    Node rhs = d_nodeManager->mkNode(
        kind::EQUAL,
        d_nodeManager->mkNode(kind::STRING_CONCAT, x, y),
        d_nodeManager->mkNode(
            kind::STRING_CONCAT,
            d_nodeManager->mkNode(kind::STRING_SUBSTR, aaa, zero, n),
            a));
    sameNormalForm(lhs, rhs);
  }

  {
    // Same normal form for:
    //
    // (= (str.++ "A" x) "A")
    //
    // (= x "")
    Node lhs = d_nodeManager->mkNode(
        kind::EQUAL, d_nodeManager->mkNode(kind::STRING_CONCAT, a, x), a);
    Node rhs = d_nodeManager->mkNode(kind::EQUAL, x, empty);
    sameNormalForm(lhs, rhs);
  }

  {
    // (= (str.++ x "A") "") ---> false
    Node eq = d_nodeManager->mkNode(
        kind::EQUAL, d_nodeManager->mkNode(kind::STRING_CONCAT, x, a), empty);
    sameNormalForm(eq, f);
  }

  {
    // (= (str.++ x "B") "AAA") ---> false
    Node eq = d_nodeManager->mkNode(
        kind::EQUAL, d_nodeManager->mkNode(kind::STRING_CONCAT, x, b), aaa);
    sameNormalForm(eq, f);
  }

  {
    // (= (str.++ x "AAA") "A") ---> false
    Node eq = d_nodeManager->mkNode(
        kind::EQUAL, d_nodeManager->mkNode(kind::STRING_CONCAT, x, aaa), a);
    sameNormalForm(eq, f);
  }

  {
    // (= (str.++ "AAA" (str.substr "A" 0 n)) (str.++ x "B")) ---> false
    Node eq = d_nodeManager->mkNode(
        kind::EQUAL,
        d_nodeManager->mkNode(
            kind::STRING_CONCAT,
            aaa,
            d_nodeManager->mkNode(
                kind::STRING_CONCAT,
                a,
                a,
                d_nodeManager->mkNode(kind::STRING_SUBSTR, x, zero, n))),
        d_nodeManager->mkNode(kind::STRING_CONCAT, x, b));
    sameNormalForm(eq, f);
  }

  {
    // (= (str.++ "A" (int.to.str n)) "A") -/-> false
    Node eq = d_nodeManager->mkNode(
        kind::EQUAL,
        d_nodeManager->mkNode(kind::STRING_CONCAT,
                              a,
                              d_nodeManager->mkNode(kind::STRING_ITOS, n)),
        a);
    differentNormalForms(eq, f);
  }

  {
    // (= (str.++ "A" x y) (str.++ x "B" z)) --> false
    Node eq = d_nodeManager->mkNode(
        kind::EQUAL,
        d_nodeManager->mkNode(kind::STRING_CONCAT, a, x, y),
        d_nodeManager->mkNode(kind::STRING_CONCAT, x, b, z));
    sameNormalForm(eq, f);
  }

  {
    // (= (str.++ "B" x y) (str.++ x "AAA" z)) --> false
    Node eq = d_nodeManager->mkNode(
        kind::EQUAL,
        d_nodeManager->mkNode(kind::STRING_CONCAT, b, x, y),
        d_nodeManager->mkNode(kind::STRING_CONCAT, x, aaa, z));
    sameNormalForm(eq, f);
  }

  {
    Node xrepl = d_nodeManager->mkNode(kind::STRING_REPLACE, x, a, b);

    // Same normal form for:
    //
    // (= (str.++ "B" (str.replace x "A" "B") z y w)
    //    (str.++ z x "BA" z))
    //
    // (and (= (str.++ "B" (str.replace x "A" "B") z)
    //         (str.++ z x "B"))
    //      (= (str.++ y w) (str.++ "A" z)))
    Node lhs = d_nodeManager->mkNode(
        kind::EQUAL,
        d_nodeManager->mkNode(kind::STRING_CONCAT, {b, xrepl, z, y, w}),
        d_nodeManager->mkNode(kind::STRING_CONCAT, {z, x, ba, z}));
    Node rhs = d_nodeManager->mkNode(
        kind::AND,
        d_nodeManager->mkNode(
            kind::EQUAL,
            d_nodeManager->mkNode(kind::STRING_CONCAT, b, xrepl, z),
            d_nodeManager->mkNode(kind::STRING_CONCAT, z, x, b)),
        d_nodeManager->mkNode(
            kind::EQUAL,
            d_nodeManager->mkNode(kind::STRING_CONCAT, y, w),
            d_nodeManager->mkNode(kind::STRING_CONCAT, a, z)));
    sameNormalForm(lhs, rhs);
  }
}

TEST_F(TestTheoryWhiteSequencesRewriter, strip_constant_endpoints)
{
  StringsEntail& se = d_seqRewriter->getStringsEntail();
  TypeNode intType = d_nodeManager->integerType();
  TypeNode strType = d_nodeManager->stringType();

  Node empty = d_nodeManager->mkConst(String(""));
  Node a = d_nodeManager->mkConst(String("A"));
  Node ab = d_nodeManager->mkConst(String("AB"));
  Node abc = d_nodeManager->mkConst(String("ABC"));
  Node abcd = d_nodeManager->mkConst(String("ABCD"));
  Node bc = d_nodeManager->mkConst(String("BC"));
  Node c = d_nodeManager->mkConst(String("C"));
  Node cd = d_nodeManager->mkConst(String("CD"));
  Node x = d_nodeManager->mkVar("x", strType);
  Node y = d_nodeManager->mkVar("y", strType);
  Node n = d_nodeManager->mkVar("n", intType);

  {
    // stripConstantEndpoints({ "" }, { "A" }, {}, {}, 0) ---> false
    std::vector<Node> n1 = {empty};
    std::vector<Node> n2 = {a};
    std::vector<Node> nb;
    std::vector<Node> ne;
    bool res = se.stripConstantEndpoints(n1, n2, nb, ne, 0);
    ASSERT_FALSE(res);
  }

  {
    // stripConstantEndpoints({ "A" }, { "A". (int.to.str n) }, {}, {}, 0)
    // ---> false
    std::vector<Node> n1 = {a};
    std::vector<Node> n2 = {a, d_nodeManager->mkNode(kind::STRING_ITOS, n)};
    std::vector<Node> nb;
    std::vector<Node> ne;
    bool res = se.stripConstantEndpoints(n1, n2, nb, ne, 0);
    ASSERT_FALSE(res);
  }

  {
    // stripConstantEndpoints({ "ABCD" }, { "C" }, {}, {}, 1)
    // ---> true
    // n1 is updated to { "CD" }
    // nb is updated to { "AB" }
    std::vector<Node> n1 = {abcd};
    std::vector<Node> n2 = {c};
    std::vector<Node> nb;
    std::vector<Node> ne;
    std::vector<Node> n1r = {cd};
    std::vector<Node> nbr = {ab};
    bool res = se.stripConstantEndpoints(n1, n2, nb, ne, 1);
    ASSERT_TRUE(res);
    ASSERT_EQ(n1, n1r);
    ASSERT_EQ(nb, nbr);
  }

  {
    // stripConstantEndpoints({ "ABC", x }, { "CD" }, {}, {}, 1)
    // ---> true
    // n1 is updated to { "C", x }
    // nb is updated to { "AB" }
    std::vector<Node> n1 = {abc, x};
    std::vector<Node> n2 = {cd};
    std::vector<Node> nb;
    std::vector<Node> ne;
    std::vector<Node> n1r = {c, x};
    std::vector<Node> nbr = {ab};
    bool res = se.stripConstantEndpoints(n1, n2, nb, ne, 1);
    ASSERT_TRUE(res);
    ASSERT_EQ(n1, n1r);
    ASSERT_EQ(nb, nbr);
  }

  {
    // stripConstantEndpoints({ "ABC" }, { "A" }, {}, {}, -1)
    // ---> true
    // n1 is updated to { "A" }
    // nb is updated to { "BC" }
    std::vector<Node> n1 = {abc};
    std::vector<Node> n2 = {a};
    std::vector<Node> nb;
    std::vector<Node> ne;
    std::vector<Node> n1r = {a};
    std::vector<Node> ner = {bc};
    bool res = se.stripConstantEndpoints(n1, n2, nb, ne, -1);
    ASSERT_TRUE(res);
    ASSERT_EQ(n1, n1r);
    ASSERT_EQ(ne, ner);
  }

  {
    // stripConstantEndpoints({ x, "ABC" }, { y, "A" }, {}, {}, -1)
    // ---> true
    // n1 is updated to { x, "A" }
    // nb is updated to { "BC" }
    std::vector<Node> n1 = {x, abc};
    std::vector<Node> n2 = {y, a};
    std::vector<Node> nb;
    std::vector<Node> ne;
    std::vector<Node> n1r = {x, a};
    std::vector<Node> ner = {bc};
    bool res = se.stripConstantEndpoints(n1, n2, nb, ne, -1);
    ASSERT_TRUE(res);
    ASSERT_EQ(n1, n1r);
    ASSERT_EQ(ne, ner);
  }
}

TEST_F(TestTheoryWhiteSequencesRewriter, rewrite_membership)
{
  TypeNode strType = d_nodeManager->stringType();

  std::vector<Node> vec_empty;
  Node abc = d_nodeManager->mkConst(String("ABC"));
  Node re_abc = d_nodeManager->mkNode(kind::STRING_TO_REGEXP, abc);
  Node x = d_nodeManager->mkVar("x", strType);

  {
    // Same normal form for:
    //
    // (str.in.re x (re.++ (re.* re.allchar)
    //                     (re.* re.allchar)
    //                     (str.to.re "ABC")
    //                     (re.* re.allchar)))
    //
    // (str.contains x "ABC")
    Node sig_star = d_nodeManager->mkNode(
        kind::REGEXP_STAR,
        d_nodeManager->mkNode(kind::REGEXP_ALLCHAR, vec_empty));
    Node lhs = d_nodeManager->mkNode(
        kind::STRING_IN_REGEXP,
        x,
        d_nodeManager->mkNode(kind::REGEXP_CONCAT,
                              {sig_star, sig_star, re_abc, sig_star}));
    Node rhs = d_nodeManager->mkNode(kind::STRING_CONTAINS, x, abc);
    sameNormalForm(lhs, rhs);
  }

  {
    // Different normal forms for:
    //
    // (str.in.re x (re.++ (re.* re.allchar) (str.to.re "ABC")))
    //
    // (str.contains x "ABC")
    Node sig_star = d_nodeManager->mkNode(
        kind::REGEXP_STAR,
        d_nodeManager->mkNode(kind::REGEXP_ALLCHAR, vec_empty));
    Node lhs = d_nodeManager->mkNode(
        kind::STRING_IN_REGEXP,
        x,
        d_nodeManager->mkNode(kind::REGEXP_CONCAT, sig_star, re_abc));
    Node rhs = d_nodeManager->mkNode(kind::STRING_CONTAINS, x, abc);
    differentNormalForms(lhs, rhs);
  }
}

TEST_F(TestTheoryWhiteSequencesRewriter, rewrite_regexp_concat)
{
  TypeNode strType = d_nodeManager->stringType();

  std::vector<Node> emptyArgs;
  Node x = d_nodeManager->mkVar("x", strType);
  Node y = d_nodeManager->mkVar("y", strType);
  Node allStar = d_nodeManager->mkNode(
      kind::REGEXP_STAR,
      d_nodeManager->mkNode(kind::REGEXP_ALLCHAR, emptyArgs));
  Node xReg = d_nodeManager->mkNode(kind::STRING_TO_REGEXP, x);
  Node yReg = d_nodeManager->mkNode(kind::STRING_TO_REGEXP, y);

  {
    // In normal form:
    //
    // (re.++ (re.* re.allchar) (re.union (str.to.re x) (str.to.re y)))
    Node n = d_nodeManager->mkNode(
        kind::REGEXP_CONCAT,
        allStar,
        d_nodeManager->mkNode(kind::REGEXP_UNION, xReg, yReg));
    inNormalForm(n);
  }

  {
    // In normal form:
    //
    // (re.++ (str.to.re x) (re.* re.allchar))
    Node n = d_nodeManager->mkNode(kind::REGEXP_CONCAT, xReg, allStar);
    inNormalForm(n);
  }
}
}  // namespace test
}  // namespace cvc5::internal
