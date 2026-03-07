/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for lia star extension.
 */

#ifdef CVC5_USE_NORMALIZ

#include <iostream>
#include <memory>
#include <vector>

#include "cvc5/cvc5.h"
#include "cvc5/cvc5_parser.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/env.h"
#include "test_smt.h"
#include "theory/arith/liastar/liastar_extension.h"
#include "theory/arith/liastar/liastar_utils.h"
#include "util/rational.h"

namespace cvc5::internal {
using namespace cvc5;
using namespace cvc5::parser;
using namespace theory;
using namespace theory::arith;
using namespace theory::arith::liastar;

namespace test {

class TestLiaStarUtils : public TestSmt
{
 protected:
  TypeNode intType, boolType;
  Node trueConst, falseConst;
  Node negativeOne, zero, one, two, three, nine, twentyOne;
  Node a, b, c, d, f, g, u, v, x, y, z;
  NodeManager* nm;
  Env* e;

  void SetUp() override
  {
    TestSmt::SetUp();
    d_slvEngine->setOption("dag-thresh", "0", true);
    d_slvEngine->setOption("trace", "liastar-ext-smt", true);
    nm = d_nodeManager.get();
    e = &d_slvEngine->getEnv();
    intType = nm->integerType();
    boolType = nm->booleanType();
    trueConst = nm->mkConst<bool>(true);
    falseConst = nm->mkConst<bool>(false);
    negativeOne = nm->mkConstInt(Rational(-1));
    zero = nm->mkConstInt(Rational(0));
    one = nm->mkConstInt(Rational(1));
    two = nm->mkConstInt(Rational(2));
    three = nm->mkConstInt(Rational(3));
    nine = nm->mkConstInt(Rational(9));
    twentyOne = nm->mkConstInt(Rational(21));
    a = nm->mkBoundVar("a", boolType);
    b = nm->mkBoundVar("b", boolType);
    c = nm->mkBoundVar("c", boolType);
    d = nm->mkBoundVar("d", boolType);
    f = nm->mkBoundVar("f", boolType);
    g = nm->mkBoundVar("g", boolType);
    u = nm->mkBoundVar("u", boolType);
    v = nm->mkBoundVar("v", boolType);
    x = nm->mkBoundVar("x", boolType);
    y = nm->mkBoundVar("y", boolType);
    z = nm->mkBoundVar("z", boolType);
  }
};

TEST_F(TestLiaStarUtils, distribute1)
{
  // (and
  //   (or
  //     (and
  //        (or f g)
  //        (or x y))
  //      z)
  //     (or u v)
  //   (and a b)
  //  )

  Node or_fg = nm->mkNode(Kind::OR, {f, g});
  Node or_xy = nm->mkNode(Kind::OR, {x, y});
  Node or_uv = nm->mkNode(Kind::OR, {u, v});
  Node and_ab = nm->mkNode(Kind::AND, {a, b});
  Node and_or_fg_or_xy = nm->mkNode(Kind::AND, {or_fg, or_xy});
  Node and_z = nm->mkNode(Kind::AND, {and_or_fg_or_xy, z});
  Node or_uv_z = nm->mkNode(Kind::OR, {or_uv, and_z});
  Node and_outer = nm->mkNode(Kind::AND, {or_uv_z, and_ab});
  Node dnf = LiaStarUtils::distribute(and_outer, e);
  dnf = LiaStarUtils::recursiveFlatten(nm, dnf);
  ASSERT_EQ(
      "(or (and u a b) (and v a b) (and f x z a b) (and g x z a b) (and f y z "
      "a b) (and g y z a b))",
      dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF1)
{
  // (not (>= (+ (* 3 x) (* (- 1) y)) 9)), i.e., not (3*x - y >= 9)
  x = nm->mkBoundVar("x", intType);
  y = nm->mkBoundVar("y", intType);

  Node threeTimesX = nm->mkNode(Kind::MULT, three, x);
  Node minus = nm->mkNode(Kind::SUB, threeTimesX, y);
  Node geq = nm->mkNode(Kind::GEQ, minus, nine);
  Node notGEQ = geq.notNode();
  Node dnf = LiaStarUtils::toDNF(notGEQ, e);
  ASSERT_EQ("(< (- (* 3 x) y) 9)", dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF2)
{
  // (and (or a b) (or c d))
  Node or_a_b = a.orNode(b);
  Node or_c_d = c.orNode(d);
  Node and = or_a_b.andNode(or_c_d);
  Node dnf = LiaStarUtils::toDNF(and, e);
  ASSERT_EQ("(or (and a c) (and b c) (and a d) (and b d))", dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF3)
{
  // (and (or (and a x) b) (or c d))
  Node and_a_x = a.andNode(x);
  Node or_a_b = and_a_x.orNode(b);
  Node or_c_d = c.orNode(d);
  Node and = or_a_b.andNode(or_c_d);
  Node dnf = LiaStarUtils::toDNF(and, e);
  ASSERT_EQ("(or (and a x c) (and b c) (and a x d) (and b d))", dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF4)
{
  // (and (or a (and b x)) (or c d))
  Node and_b_x = b.andNode(x);
  Node or_a_b = a.orNode(and_b_x);
  Node or_c_d = c.orNode(d);
  Node and = or_a_b.andNode(or_c_d);
  Node dnf = LiaStarUtils::toDNF(and, e);
  ASSERT_EQ("(or (and a c) (and b x c) (and a d) (and b x d))", dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF5)
{
  // (and (or a b x) (or c d))
  Node or1 = nm->mkNode(Kind::OR, {a, b, x});
  Node or2 = nm->mkNode(Kind::OR, {c, d});
  Node and = or1.andNode(or2);
  Node dnf = LiaStarUtils::toDNF(and, e);
  ASSERT_EQ("(or (and a c) (and b c) (and x c) (and a d) (and b d) (and x d))",
            dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF6)
{
  // (and (or a b) (or c d) (or x y))
  Node or1 = nm->mkNode(Kind::OR, {a, b});
  Node or2 = nm->mkNode(Kind::OR, {c, d});
  Node or3 = nm->mkNode(Kind::OR, {x, y});
  Node and = nm->mkNode(Kind::AND, {or1, or2, or3});
  Node dnf = LiaStarUtils::toDNF(and, e);
  ASSERT_EQ(
      "(or (and a c x) (and b c x) (and a d x) (and b d x) (and a c y) (and b "
      "c y) (and a d y) (and b d y))",
      dnf.toString());
}

TEST_F(TestLiaStarUtils, toDNF7)
{
  TermManager tm;
  Solver slv(tm);
  SymbolManager sm(tm);
  Env env(tm.d_nm.get(), slv.d_originalOptions.get());
  InputParser parser(&slv, &sm);

  std::stringstream ss;
  ss << "(set-logic ALL)"
     << "(declare-const a Int)" << std::endl
     << "(declare-const b Int)" << std::endl
     << "(declare-const c Int)" << std::endl
     << "(declare-const d Int)" << std::endl
     << "(declare-const e Int)" << std::endl
     << "(declare-const g Int)" << std::endl
     << "(declare-const h Int)" << std::endl
     << "(declare-const i Int)" << std::endl
     << "(declare-const U Int)" << std::endl
     << "(declare-const f Int)" << std::endl
     << "(declare-const A Int)" << std::endl
     << "(declare-const B Int)" << std::endl
     << "(declare-const t Int)" << std::endl
     << "(declare-const n Int)" << std::endl;

  parser.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss, "MyStream");
  Command cmd;
  while (true)
  {
    cmd = parser.nextCommand();
    if (cmd.isNull())
    {
      break;
    }
    // invoke the command on the solver and the symbol manager, print the result
    // to std::cout
    cmd.invoke(&slv, &sm, std::cout);
  }

  InputParser parser2(&slv, &sm);
  std::stringstream ss2;
  ss2 << "(and (or (and (= a 0) (>= (+ U (* (- 1) f)) 0)) (and (= a 1) (< (+ U "
         "(* (- 1) f)) 0))) (or (and (= b 1) (>= U 1)) (and (= b 0) (< U 1))) "
         "(or (and (= c 1) (>= f 1)) (and (= c 0) (< f 1))) (or (and (= d 0) "
         "(>= (+ U (* (- 1) B)) 0)) (and (= d 1) (< (+ U (* (- 1) B)) 0))) (or "
         "(and (= e 1) (>= B 1)) (and (= e 0) (< B 1))) (or (and (= g 0) (>= "
         "(+ U (* (- 1) A)) 0)) (and (= g 1) (< (+ U (* (- 1) A)) 0))) (or "
         "(and (= h 1) (>= A 1)) (and (= h 0) (< A 1))) (or (and (= i 1) (or "
         "(and (>= (+ U (* (- 1) f)) 1) (or (and (>= (+ (* (- 1) U) f B) 0) "
         "(>= (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (and (>= B 0) (>= "
         "(+ A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1)) (and (>= (+ (* (- 1) "
         "U) f A) 0) (< (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (and "
         "(>= A 0) (< (+ A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1)))) (and (>= "
         "0 1) (< (+ U (* (- 1) f)) 1) (or (and (>= (+ (* (- 1) U) f B) 0) (>= "
         "(+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (and (>= B 0) (>= (+ "
         "A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1)) (and (>= (+ (* (- 1) U) f "
         "A) 0) (< (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (and (>= A "
         "0) (< (+ A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1)))) (and (>= B 1) "
         "(>= (+ A (* (- 1) B)) 1) (or (< (+ (* (- 1) U) f B) 0) (< (+ A (* (- "
         "1) B)) 1) (< (+ U (* (- 1) f)) 1)) (or (< B 0) (< (+ A (* (- 1) B)) "
         "1) (>= (+ U (* (- 1) f)) 1)) (or (< (+ (* (- 1) U) f A) 0) (>= (+ A "
         "(* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1)) (or (< A 0) (>= (+ A (* (- "
         "1) B)) 1) (>= (+ U (* (- 1) f)) 1))) (and (>= A 1) (< (+ A (* (- 1) "
         "B)) 1) (or (< (+ (* (- 1) U) f B) 0) (< (+ A (* (- 1) B)) 1) (< (+ U "
         "(* (- 1) f)) 1)) (or (< B 0) (< (+ A (* (- 1) B)) 1) (>= (+ U (* (- "
         "1) f)) 1)) (or (< (+ (* (- 1) U) f A) 0) (>= (+ A (* (- 1) B)) 1) (< "
         "(+ U (* (- 1) f)) 1)) (or (< A 0) (>= (+ A (* (- 1) B)) 1) (>= (+ U "
         "(* (- 1) f)) 1))))) (and (= i 0) (or (< (+ U (* (- 1) f)) 1) (and "
         "(or (< (+ (* (- 1) U) f B) 0) (< (+ A (* (- 1) B)) 1) (< (+ U (* (- "
         "1) f)) 1)) (or (< B 0) (< (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) "
         "1)) (or (< (+ (* (- 1) U) f A) 0) (>= (+ A (* (- 1) B)) 1) (< (+ U "
         "(* (- 1) f)) 1)) (or (< A 0) (>= (+ A (* (- 1) B)) 1) (>= (+ U (* (- "
         "1) f)) 1)))) (or (< 0 1) (>= (+ U (* (- 1) f)) 1) (and (or (< (+ (* "
         "(- 1) U) f B) 0) (< (+ A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1)) "
         "(or (< B 0) (< (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (or (< "
         "(+ (* (- 1) U) f A) 0) (>= (+ A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) "
         "1)) (or (< A 0) (>= (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)))) "
         "(or (< B 1) (< (+ A (* (- 1) B)) 1) (and (>= (+ (* (- 1) U) f B) 0) "
         "(>= (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (and (>= B 0) (>= "
         "(+ A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1)) (and (>= (+ (* (- 1) "
         "U) f A) 0) (< (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (and "
         "(>= A 0) (< (+ A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1))) (or (< A "
         "1) (>= (+ A (* (- 1) B)) 1) (and (>= (+ (* (- 1) U) f B) 0) (>= (+ A "
         "(* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (and (>= B 0) (>= (+ A (* "
         "(- 1) B)) 1) (< (+ U (* (- 1) f)) 1)) (and (>= (+ (* (- 1) U) f A) "
         "0) (< (+ A (* (- 1) B)) 1) (>= (+ U (* (- 1) f)) 1)) (and (>= A 0) "
         "(< (+ A (* (- 1) B)) 1) (< (+ U (* (- 1) f)) 1))))) (>= f 0) (>= U "
         "0) (>= B 0) (>= A 0))"
      << std::endl;
  parser2.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss2, "MyStream2");

  Term t = parser2.nextTerm();
  // Node dnf = LiaStarUtils::toDNF(*(t.d_node.get()), env);
}

TEST_F(TestLiaStarUtils, toDnf8)
{
  TermManager tm;
  Solver slv(tm);
  SymbolManager sm(tm);
  Env env(tm.d_nm.get(), slv.d_originalOptions.get());
  // construct an input parser associated the solver above
  InputParser parser(&slv, &sm);

  std::stringstream ss;
  ss << "(set-logic ALL)"
     << "(declare-const a Int)" << std::endl
     << "(declare-const b Int)" << std::endl
     << "(declare-const c Int)" << std::endl
     << "(declare-const d Int)" << std::endl
     << "(declare-const e Int)" << std::endl
     << "(declare-const g Int)" << std::endl
     << "(declare-const h Int)" << std::endl
     << "(declare-const i Int)" << std::endl
     << "(declare-const U Int)" << std::endl
     << "(declare-const f Int)" << std::endl
     << "(declare-const A Int)" << std::endl
     << "(declare-const B Int)" << std::endl
     << "(declare-const t Int)" << std::endl
     << "(declare-const n Int)" << std::endl;

  parser.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss, "MyStream");
  Command cmd;
  while (true)
  {
    cmd = parser.nextCommand();
    if (cmd.isNull())
    {
      break;
    }
    // invoke the command on the solver and the symbol manager, print the result
    // to std::cout
    cmd.invoke(&slv, &sm, std::cout);
  }

  InputParser parser2(&slv, &sm);
  std::stringstream ss2;
  ss2 << "(or"
      << "(and (= i 1)"
      << "  (or"
      << "    (and"
      << "      (>= (+ U (* (- 1) f)) 1)"
      << "      (or"
      << "        (and"
      << "          (>= (+ (* (- 1) U) f B) 0)"
      << "          (>= (+ A (* (- 1) B)) 1)"
      << "          (>= (+ U (* (- 1) f)) 1))"
      << "        (and (>= B 0)"
      << "          (>= (+ A (* (- 1) B)) 1)"
      << "          (< (+ U (* (- 1) f)) 1))"
      << "        (and"
      << "          (>= (+ (* (- 1) U) f A) 0)"
      << "          (< (+ A (* (- 1) B)) 1)"
      << "          (>= (+ U (* (- 1) f)) 1))"
      << "        (and (>= A 0)"
      << "          (< (+ A (* (- 1) B)) 1)"
      << "          (< (+ U (* (- 1) f)) 1))))"
      << "    (and (>= 0 1)"
      << "      (< (+ U (* (- 1) f)) 1)"
      << "      (or"
      << "        (and"
      << "          (>= (+ (* (- 1) U) f B) 0)"
      << "          (>= (+ A (* (- 1) B)) 1)"
      << "          (>= (+ U (* (- 1) f)) 1))"
      << "        (and (>= B 0)"
      << "          (>= (+ A (* (- 1) B)) 1)"
      << "          (< (+ U (* (- 1) f)) 1))"
      << "        (and"
      << "          (>= (+ (* (- 1) U) f A) 0)"
      << "          (< (+ A (* (- 1) B)) 1)"
      << "          (>= (+ U (* (- 1) f)) 1))"
      << "        (and (>= A 0)"
      << "          (< (+ A (* (- 1) B)) 1)"
      << "          (< (+ U (* (- 1) f)) 1))))"
      << "    (and (>= B 1)"
      << "      (>= (+ A (* (- 1) B)) 1)"
      << "      (or"
      << "        (< (+ (* (- 1) U) f B) 0)"
      << "        (< (+ A (* (- 1) B)) 1)"
      << "        (< (+ U (* (- 1) f)) 1))"
      << "      (or (< B 0)"
      << "        (< (+ A (* (- 1) B)) 1)"
      << "        (>= (+ U (* (- 1) f)) 1))"
      << "      (or"
      << "        (< (+ (* (- 1) U) f A) 0)"
      << "        (>= (+ A (* (- 1) B)) 1)"
      << "        (< (+ U (* (- 1) f)) 1))"
      << "      (or (< A 0)"
      << "        (>= (+ A (* (- 1) B)) 1)"
      << "        (>= (+ U (* (- 1) f)) 1)))"
      << "    (and (>= A 1)"
      << "      (< (+ A (* (- 1) B)) 1)"
      << "      (or"
      << "        (< (+ (* (- 1) U) f B) 0)"
      << "        (< (+ A (* (- 1) B)) 1)"
      << "        (< (+ U (* (- 1) f)) 1))"
      << "      (or (< B 0)"
      << "        (< (+ A (* (- 1) B)) 1)"
      << "        (>= (+ U (* (- 1) f)) 1))"
      << "      (or"
      << "        (< (+ (* (- 1) U) f A) 0)"
      << "        (>= (+ A (* (- 1) B)) 1)"
      << "        (< (+ U (* (- 1) f)) 1))"
      << "      (or (< A 0)"
      << "        (>= (+ A (* (- 1) B)) 1)"
      << "        (>= (+ U (* (- 1) f)) 1)))))"
      << "(and (= i 0)"
      << "  (or"
      << "    (< (+ U (* (- 1) f)) 1)"
      << "    (and"
      << "      (or"
      << "        (< (+ (* (- 1) U) f B) 0)"
      << "        (< (+ A (* (- 1) B)) 1)"
      << "        (< (+ U (* (- 1) f)) 1))"
      << "      (or (< B 0)"
      << "        (< (+ A (* (- 1) B)) 1)"
      << "        (>= (+ U (* (- 1) f)) 1))"
      << "      (or"
      << "        (< (+ (* (- 1) U) f A) 0)"
      << "        (>= (+ A (* (- 1) B)) 1)"
      << "        (< (+ U (* (- 1) f)) 1))"
      << "      (or (< A 0)"
      << "        (>= (+ A (* (- 1) B)) 1)"
      << "        (>= (+ U (* (- 1) f)) 1))))"
      << "  (or (< 0 1)"
      << "    (>= (+ U (* (- 1) f)) 1)"
      << "    (and"
      << "      (or"
      << "        (< (+ (* (- 1) U) f B) 0)"
      << "        (< (+ A (* (- 1) B)) 1)"
      << "        (< (+ U (* (- 1) f)) 1))"
      << "      (or (< B 0)"
      << "        (< (+ A (* (- 1) B)) 1)"
      << "        (>= (+ U (* (- 1) f)) 1))"
      << "      (or"
      << "        (< (+ (* (- 1) U) f A) 0)"
      << "        (>= (+ A (* (- 1) B)) 1)"
      << "        (< (+ U (* (- 1) f)) 1))"
      << "      (or (< A 0)"
      << "        (>= (+ A (* (- 1) B)) 1)"
      << "        (>= (+ U (* (- 1) f)) 1))))"
      << "  (or (< B 1)"
      << "    (< (+ A (* (- 1) B)) 1)"
      << "    (and"
      << "      (>= (+ (* (- 1) U) f B) 0)"
      << "      (>= (+ A (* (- 1) B)) 1)"
      << "      (>= (+ U (* (- 1) f)) 1))"
      << "    (and (>= B 0)"
      << "      (>= (+ A (* (- 1) B)) 1)"
      << "      (< (+ U (* (- 1) f)) 1))"
      << "    (and"
      << "      (>= (+ (* (- 1) U) f A) 0)"
      << "      (< (+ A (* (- 1) B)) 1)"
      << "      (>= (+ U (* (- 1) f)) 1))"
      << "    (and (>= A 0)"
      << "      (< (+ A (* (- 1) B)) 1)"
      << "      (< (+ U (* (- 1) f)) 1)))"
      << "  (or (< A 1)"
      << "    (>= (+ A (* (- 1) B)) 1)"
      << "    (and"
      << "      (>= (+ (* (- 1) U) f B) 0)"
      << "      (>= (+ A (* (- 1) B)) 1)"
      << "      (>= (+ U (* (- 1) f)) 1))"
      << "    (and (>= B 0)"
      << "      (>= (+ A (* (- 1) B)) 1)"
      << "      (< (+ U (* (- 1) f)) 1))"
      << "    (and"
      << "      (>= (+ (* (- 1) U) f A) 0)"
      << "      (< (+ A (* (- 1) B)) 1)"
      << "      (>= (+ U (* (- 1) f)) 1))"
      << "    (and (>= A 0)"
      << "      (< (+ A (* (- 1) B)) 1)"
      << "      (< (+ U (* (- 1) f)) 1)))))" << std::endl;
  parser2.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss2, "MyStream2");

  Term t = parser2.nextTerm();
  // Node dnf = LiaStarUtils::toDNF(*(t.d_node.get()), env);
}

}  // namespace test
}  // namespace cvc5::internal

#endif /* CVC5_USE_NORMALIZ */