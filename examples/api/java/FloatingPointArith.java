/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An example of solving floating-point problems with cvc5's Java API
 *
 * This example shows to create floating-point types, variables and expressions,
 * and how to create rounding mode constants by solving toy problems. The
 * example also shows making special values (such as NaN and +oo) and converting
 * an IEEE 754-2008 bit-vector to a floating-point number.
 */

import static io.github.cvc5.Kind.*;

import io.github.cvc5.*;

public class FloatingPointArith
{
  public static void main(String[] args) throws CVC5ApiException
  {
    Solver solver = new Solver();
    {
      solver.setOption("produce-models", "true");

      // Make single precision floating-point variables
      Sort fpt32 = solver.mkFloatingPointSort(8, 24);
      Term a = solver.mkConst(fpt32, "a");
      Term b = solver.mkConst(fpt32, "b");
      Term c = solver.mkConst(fpt32, "c");
      Term d = solver.mkConst(fpt32, "d");
      Term e = solver.mkConst(fpt32, "e");

      // Assert that floating-point addition is not associative:
      // (a + (b + c)) != ((a + b) + c)
      Term rm = solver.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_EVEN);
      Term lhs = solver.mkTerm(
          Kind.FLOATINGPOINT_ADD, rm, a, solver.mkTerm(Kind.FLOATINGPOINT_ADD, rm, b, c));
      Term rhs = solver.mkTerm(
          Kind.FLOATINGPOINT_ADD, rm, solver.mkTerm(Kind.FLOATINGPOINT_ADD, rm, a, b), c);
      solver.assertFormula(solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, a, b)));

      Result r = solver.checkSat(); // result is sat
      assert r.isSat();

      System.out.println("a = " + solver.getValue(a));
      System.out.println("b = " + solver.getValue(b));
      System.out.println("c = " + solver.getValue(c));

      // Now, let's restrict `a` to be either NaN or positive infinity
      Term nan = solver.mkFloatingPointNaN(8, 24);
      Term inf = solver.mkFloatingPointPosInf(8, 24);
      solver.assertFormula(solver.mkTerm(
          Kind.OR, solver.mkTerm(Kind.EQUAL, a, inf), solver.mkTerm(Kind.EQUAL, a, nan)));

      r = solver.checkSat(); // result is sat
      assert r.isSat();

      System.out.println("a = " + solver.getValue(a));
      System.out.println("b = " + solver.getValue(b));
      System.out.println("c = " + solver.getValue(c));

      // And now for something completely different. Let's try to find a (normal)
      // floating-point number that rounds to different integer values for
      // different rounding modes.
      Term rtp = solver.mkRoundingMode(RoundingMode.ROUND_TOWARD_POSITIVE);
      Term rtn = solver.mkRoundingMode(RoundingMode.ROUND_TOWARD_NEGATIVE);
      Op op = solver.mkOp(Kind.FLOATINGPOINT_TO_SBV, 16); // (_ fp.to_sbv 16)
      lhs = solver.mkTerm(op, rtp, d);
      rhs = solver.mkTerm(op, rtn, d);
      solver.assertFormula(solver.mkTerm(Kind.FLOATINGPOINT_IS_NORMAL, d));
      solver.assertFormula(solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, lhs, rhs)));

      r = solver.checkSat(); // result is sat
      assert r.isSat();

      // Convert the result to a rational and print it
      Term val = solver.getValue(d);
      Term realVal = solver.getValue(solver.mkTerm(FLOATINGPOINT_TO_REAL, val));
      System.out.println("d = " + val + " = " + realVal);
      System.out.println("((_ fp.to_sbv 16) RTP d) = " + solver.getValue(lhs));
      System.out.println("((_ fp.to_sbv 16) RTN d) = " + solver.getValue(rhs));

      // For our final trick, let's try to find a floating-point number between
      // positive zero and the smallest positive floating-point number
      Term zero = solver.mkFloatingPointPosZero(8, 24);
      Term smallest = solver.mkFloatingPoint(8, 24, solver.mkBitVector(32, 0b001));
      solver.assertFormula(solver.mkTerm(Kind.AND,
          solver.mkTerm(Kind.FLOATINGPOINT_LT, zero, e),
          solver.mkTerm(Kind.FLOATINGPOINT_LT, e, smallest)));

      r = solver.checkSat(); // result is unsat
      assert !r.isSat();
    }
  }
}
