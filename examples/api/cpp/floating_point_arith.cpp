/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mudathir Mohamed, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An example of solving floating-point problems with cvc5's cpp API.
 *
 * This example shows to create floating-point types, variables and expressions,
 * and how to create rounding mode constants by solving toy problems. The
 * example also shows making special values (such as NaN and +oo) and converting
 * an IEEE 754-2008 bit-vector to a floating-point number.
 */

#include <cvc5/cvc5.h>

#include <iostream>
#include <cassert>

using namespace cvc5;

int main()
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("incremental", "true");
  solver.setOption("produce-models", "true");

  // Make single precision floating-point variables
  Sort fpt32 = tm.mkFloatingPointSort(8, 24);
  Term a = tm.mkConst(fpt32, "a");
  Term b = tm.mkConst(fpt32, "b");
  Term c = tm.mkConst(fpt32, "c");
  Term d = tm.mkConst(fpt32, "d");
  Term e = tm.mkConst(fpt32, "e");
  // Rounding mode
  Term rm = tm.mkRoundingMode(RoundingMode::ROUND_NEAREST_TIES_TO_EVEN);

  std::cout << "Show that fused multiplication and addition `(fp.fma RM a b c)`"
            << std::endl
            << "is different from `(fp.add RM (fp.mul a b) c)`:" << std::endl;
  solver.push(1);
  Term fma = tm.mkTerm(Kind::FLOATINGPOINT_FMA, {rm, a, b, c});
  Term mul = tm.mkTerm(Kind::FLOATINGPOINT_MULT, {rm, a, b});
  Term add = tm.mkTerm(Kind::FLOATINGPOINT_ADD, {rm, mul, c});
  solver.assertFormula(tm.mkTerm(Kind::DISTINCT, {fma, add}));
  Result r = solver.checkSat();  // result is sat
  std::cout << "Expect sat: " << r << std::endl;
  std::cout << "Value of `a`: " << solver.getValue(a) << std::endl;
  std::cout << "Value of `b`: " << solver.getValue(b) << std::endl;
  std::cout << "Value of `c`: " << solver.getValue(c) << std::endl;
  std::cout << "Value of `(fp.fma RNE a b c)`: " << solver.getValue(fma)
            << std::endl;
  std::cout << "Value of `(fp.add RNE (fp.mul a b) c)`: "
            << solver.getValue(add) << std::endl;
  std::cout << std::endl;
  solver.pop(1);

  std::cout << "Show that floating-point addition is not associative:"
            << std::endl;
  std::cout << "(a + (b + c)) != ((a + b) + c)" << std::endl;
  solver.push(1);
  solver.assertFormula(tm.mkTerm(
      Kind::DISTINCT,
      {tm.mkTerm(Kind::FLOATINGPOINT_ADD,
                 {rm, a, tm.mkTerm(Kind::FLOATINGPOINT_ADD, {rm, b, c})}),
       tm.mkTerm(Kind::FLOATINGPOINT_ADD,
                 {rm, tm.mkTerm(Kind::FLOATINGPOINT_ADD, {rm, a, b}), c})}));

  r = solver.checkSat();  // result is sat
  std::cout << "Expect sat: " << r << std::endl;
  assert (r.isSat());

  std::cout << "Value of `a`: " << solver.getValue(a) << std::endl;
  std::cout << "Value of `b`: " << solver.getValue(b) << std::endl;
  std::cout << "Value of `c`: " << solver.getValue(c) << std::endl;
  std::cout << std::endl;

  std::cout << "Now, restrict `a` to be either NaN or positive infinity:"
            << std::endl;
  Term nan = tm.mkFloatingPointNaN(8, 24);
  Term inf = tm.mkFloatingPointPosInf(8, 24);
  solver.assertFormula(tm.mkTerm(
      Kind::OR,
      {tm.mkTerm(Kind::EQUAL, {a, inf}), tm.mkTerm(Kind::EQUAL, {a, nan})}));

  r = solver.checkSat();  // result is sat
  std::cout << "Expect sat: " << r << std::endl;
  assert (r.isSat());

  std::cout << "Value of `a`: " << solver.getValue(a) << std::endl;
  std::cout << "Value of `b`: " << solver.getValue(b) << std::endl;
  std::cout << "Value of `c`: " << solver.getValue(c) << std::endl;
  std::cout << std::endl;
  solver.pop(1);

  std::cout << "Now, try to find a (normal) floating-point number that rounds"
            << std::endl
            << "to different integer values for different rounding modes:"
            << std::endl;
  solver.push(1);
  Term rtp = tm.mkRoundingMode(RoundingMode::ROUND_TOWARD_POSITIVE);
  Term rtn = tm.mkRoundingMode(RoundingMode::ROUND_TOWARD_NEGATIVE);
  Op op = tm.mkOp(Kind::FLOATINGPOINT_TO_UBV, {16});  // (_ fp.to_ubv 16)
  Term lhs = tm.mkTerm(op, {rtp, d});
  Term rhs = tm.mkTerm(op, {rtn, d});
  solver.assertFormula(tm.mkTerm(Kind::FLOATINGPOINT_IS_NORMAL, {d}));
  solver.assertFormula(
      tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::EQUAL, {lhs, rhs})}));

  r = solver.checkSat();  // result is sat
  std::cout << "Expect sat: " << r << std::endl;
  assert (r.isSat());
  std::cout << std::endl;

  std::cout << "Get value of `d` as floating-point, bit-vector and real:"
            << std::endl;
  Term val = solver.getValue(d);
  std::cout << "Value of `d`: " << val << std::endl;
  std::cout << "Value of `((_ fp.to_ubv 16) RTP d)`: " << solver.getValue(lhs)
            << std::endl;
  std::cout << "Value of `((_ fp.to_ubv 16) RTN d)`: " << solver.getValue(rhs)
            << std::endl;
  std::cout << "Value of `(fp.to_real d)` "
            << solver.getValue(tm.mkTerm(Kind::FLOATINGPOINT_TO_REAL, {val}))
            << std::endl;
  std::cout << std::endl;
  solver.pop(1);

  std::cout << "Finally, try to find a floating-point number between positive"
            << std::endl
            << "zero and the smallest positive floating-point number:"
            << std::endl;
  Term zero = tm.mkFloatingPointPosZero(8, 24);
  Term smallest = tm.mkFloatingPoint(8, 24, tm.mkBitVector(32, 1));
  solver.assertFormula(
      tm.mkTerm(Kind::AND,
                {tm.mkTerm(Kind::FLOATINGPOINT_LT, {zero, e}),
                 tm.mkTerm(Kind::FLOATINGPOINT_LT, {e, smallest})}));

  r = solver.checkSat();  // result is unsat
  std::cout << "Expect unsat: " << r << std::endl;
  assert(r.isUnsat());
}
