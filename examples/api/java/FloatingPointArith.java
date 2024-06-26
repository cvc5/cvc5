/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);
    {
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
      Term rm = tm.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_EVEN);

      System.out.println("Show that fused multiplication and addition `(fp.fma RM a b c)`");
      System.out.println("is different from `(fp.add RM (fp.mul a b) c)`:");
      solver.push(1);
      Term fma = tm.mkTerm(Kind.FLOATINGPOINT_FMA, new Term[] {rm, a, b, c});
      Term mul = tm.mkTerm(Kind.FLOATINGPOINT_MULT, rm, a, b);
      Term add = tm.mkTerm(Kind.FLOATINGPOINT_ADD, rm, mul, c);
      solver.assertFormula(tm.mkTerm(Kind.DISTINCT, fma, add));
      Result r = solver.checkSat(); // result is sat
      System.out.println("Expect sat: " + r);
      System.out.println("Value of `a`: " + solver.getValue(a));
      System.out.println("Value of `b`: " + solver.getValue(b));
      System.out.println("Value of `c`: " + solver.getValue(c));
      System.out.println("Value of `(fp.fma RNE a b c)`: " + solver.getValue(fma));
      System.out.println("Value of `(fp.add RNE (fp.mul a b) c)`: " + solver.getValue(add));
      System.out.println();
      solver.pop(1);

      System.out.println("Show that floating-point addition is not associative:");
      System.out.println("(a + (b + c)) != ((a + b) + c)");
      Term lhs =
          tm.mkTerm(Kind.FLOATINGPOINT_ADD, rm, a, tm.mkTerm(Kind.FLOATINGPOINT_ADD, rm, b, c));
      Term rhs =
          tm.mkTerm(Kind.FLOATINGPOINT_ADD, rm, tm.mkTerm(Kind.FLOATINGPOINT_ADD, rm, a, b), c);
      solver.assertFormula(tm.mkTerm(Kind.NOT, tm.mkTerm(Kind.EQUAL, a, b)));

      r = solver.checkSat(); // result is sat
      assert r.isSat();

      System.out.println("Value of `a`: " + solver.getValue(a));
      System.out.println("Value of `b`: " + solver.getValue(b));
      System.out.println("Value of `c`: " + solver.getValue(c));

      System.out.println("Now, restrict `a` to be either NaN or positive infinity:");
      Term nan = tm.mkFloatingPointNaN(8, 24);
      Term inf = tm.mkFloatingPointPosInf(8, 24);
      solver.assertFormula(
          tm.mkTerm(Kind.OR, tm.mkTerm(Kind.EQUAL, a, inf), tm.mkTerm(Kind.EQUAL, a, nan)));

      r = solver.checkSat(); // result is sat
      assert r.isSat();

      System.out.println("Value of `a`: " + solver.getValue(a));
      System.out.println("Value of `b`: " + solver.getValue(b));
      System.out.println("Value of `c`: " + solver.getValue(c));

      System.out.println("Now, try to find a (normal) floating-point number that rounds");
      System.out.println("to different integer values for different rounding modes:");
      Term rtp = tm.mkRoundingMode(RoundingMode.ROUND_TOWARD_POSITIVE);
      Term rtn = tm.mkRoundingMode(RoundingMode.ROUND_TOWARD_NEGATIVE);
      Op op = tm.mkOp(Kind.FLOATINGPOINT_TO_UBV, 16); // (_ fp.to_ubv 16)
      lhs = tm.mkTerm(op, rtp, d);
      rhs = tm.mkTerm(op, rtn, d);
      solver.assertFormula(tm.mkTerm(Kind.FLOATINGPOINT_IS_NORMAL, d));
      solver.assertFormula(tm.mkTerm(Kind.NOT, tm.mkTerm(Kind.EQUAL, lhs, rhs)));

      r = solver.checkSat(); // result is sat
      assert r.isSat();

      System.out.println("Get value of `d` as floating-point, bit-vector and real:");
      Term val = solver.getValue(d);
      System.out.println("Value of `d`: " + val);
      System.out.println("Value of `((_ fp.to_ubv 16) RTP d)`: " + solver.getValue(lhs));
      System.out.println("Value of `((_ fp.to_ubv 16) RTN d)`: " + solver.getValue(rhs));
      System.out.println("Value of `(fp.to_real d)`: "
          + solver.getValue(tm.mkTerm(Kind.FLOATINGPOINT_TO_REAL, val)));

      System.out.println("Finally, try to find a floating-point number between positive");
      System.out.println("zero and the smallest positive floating-point number:");
      Term zero = tm.mkFloatingPointPosZero(8, 24);
      Term smallest = tm.mkFloatingPoint(8, 24, tm.mkBitVector(32, 0b001));
      solver.assertFormula(tm.mkTerm(Kind.AND,
          tm.mkTerm(Kind.FLOATINGPOINT_LT, zero, e),
          tm.mkTerm(Kind.FLOATINGPOINT_LT, e, smallest)));

      r = solver.checkSat(); // result is unsat
      assert !r.isSat();
    }
    Context.deletePointers();
  }
}
