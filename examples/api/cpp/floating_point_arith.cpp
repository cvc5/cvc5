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

using namespace std;
using namespace cvc5;

int main()
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("produce-models", "true");

  // Make single precision floating-point variables
  Sort fpt32 = tm.mkFloatingPointSort(8, 24);
  Term a = tm.mkConst(fpt32, "a");
  Term b = tm.mkConst(fpt32, "b");
  Term c = tm.mkConst(fpt32, "c");
  Term d = tm.mkConst(fpt32, "d");
  Term e = tm.mkConst(fpt32, "e");

  // Assert that floating-point addition is not associative:
  // (a + (b + c)) != ((a + b) + c)
  Term rm = tm.mkRoundingMode(RoundingMode::ROUND_NEAREST_TIES_TO_EVEN);
  Term lhs = tm.mkTerm(Kind::FLOATINGPOINT_ADD,
                       {rm, a, tm.mkTerm(Kind::FLOATINGPOINT_ADD, {rm, b, c})});
  Term rhs = tm.mkTerm(Kind::FLOATINGPOINT_ADD,
                       {rm, tm.mkTerm(Kind::FLOATINGPOINT_ADD, {rm, a, b}), c});
  solver.assertFormula(tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::EQUAL, {a, b})}));

  Result r = solver.checkSat();  // result is sat
  assert (r.isSat());

  cout << "a = " << solver.getValue(a) << endl;
  cout << "b = " << solver.getValue(b) << endl;
  cout << "c = " << solver.getValue(c) << endl;

  // Now, let's restrict `a` to be either NaN or positive infinity
  Term nan = tm.mkFloatingPointNaN(8, 24);
  Term inf = tm.mkFloatingPointPosInf(8, 24);
  solver.assertFormula(tm.mkTerm(
      Kind::OR,
      {tm.mkTerm(Kind::EQUAL, {a, inf}), tm.mkTerm(Kind::EQUAL, {a, nan})}));

  r = solver.checkSat();  // result is sat
  assert (r.isSat());

  cout << "a = " << solver.getValue(a) << endl;
  cout << "b = " << solver.getValue(b) << endl;
  cout << "c = " << solver.getValue(c) << endl;

  // And now for something completely different. Let's try to find a (normal)
  // floating-point number that rounds to different integer values for
  // different rounding modes.
  Term rtp = tm.mkRoundingMode(RoundingMode::ROUND_TOWARD_POSITIVE);
  Term rtn = tm.mkRoundingMode(RoundingMode::ROUND_TOWARD_NEGATIVE);
  Op op = tm.mkOp(Kind::FLOATINGPOINT_TO_SBV, {16});  // (_ fp.to_sbv 16)
  lhs = tm.mkTerm(op, {rtp, d});
  rhs = tm.mkTerm(op, {rtn, d});
  solver.assertFormula(tm.mkTerm(Kind::FLOATINGPOINT_IS_NORMAL, {d}));
  solver.assertFormula(
      tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::EQUAL, {lhs, rhs})}));

  r = solver.checkSat();  // result is sat
  assert (r.isSat());

  // Convert the result to a rational and print it
  Term val = solver.getValue(d);
  Term realVal = solver.getValue(tm.mkTerm(Kind::FLOATINGPOINT_TO_REAL, {val}));
  cout << "d = " << val << " = " << realVal << endl;
  cout << "((_ fp.to_sbv 16) RTP d) = " << solver.getValue(lhs) << endl;
  cout << "((_ fp.to_sbv 16) RTN d) = " << solver.getValue(rhs) << endl;

  // For our final trick, let's try to find a floating-point number between
  // positive zero and the smallest positive floating-point number
  Term zero = tm.mkFloatingPointPosZero(8, 24);
  Term smallest = tm.mkFloatingPoint(8, 24, tm.mkBitVector(32, 0b001));
  solver.assertFormula(
      tm.mkTerm(Kind::AND,
                {tm.mkTerm(Kind::FLOATINGPOINT_LT, {zero, e}),
                 tm.mkTerm(Kind::FLOATINGPOINT_LT, {e, smallest})}));

  r = solver.checkSat();  // result is unsat
  assert (!r.isSat());
}
