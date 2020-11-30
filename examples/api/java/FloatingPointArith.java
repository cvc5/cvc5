/*********************                                                        */
/*! \file FloatingPointArith.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An example of solving floating-point problems with CVC4's Java API
 **
 ** This example shows how to check whether CVC4 was built with floating-point
 ** support, how to create floating-point types, variables and expressions, and
 ** how to create rounding mode constants by solving toy problems. The example
 ** also shows making special values (such as NaN and +oo) and converting an
 ** IEEE 754-2008 bit-vector to a floating-point number.
 **/

import edu.stanford.CVC4.*;
import java.util.Iterator;

public class FloatingPointArith {
  public static void main(String[] args) {
    System.loadLibrary("cvc4jni");

    // Test whether CVC4 was built with floating-point support
    if (!Configuration.isBuiltWithSymFPU()) {
      System.out.println("CVC4 was built without floating-point support.");
      System.out.println("Configure with --symfpu and rebuild CVC4 to run");
      System.out.println("this example.");
      System.exit(77);
    }

    ExprManager em = new ExprManager();
    SmtEngine smt = new SmtEngine(em);

    // Enable the model production
    smt.setOption("produce-models", new SExpr(true));

    // Make single precision floating-point variables
    FloatingPointType fpt32 = em.mkFloatingPointType(8, 24);
    Expr a = em.mkVar("a", fpt32);
    Expr b = em.mkVar("b", fpt32);
    Expr c = em.mkVar("c", fpt32);
    Expr d = em.mkVar("d", fpt32);
    Expr e = em.mkVar("e", fpt32);

    // Assert that floating-point addition is not associative:
    // (a + (b + c)) != ((a + b) + c)
    Expr rm = em.mkConst(RoundingMode.roundNearestTiesToEven);
    Expr lhs = em.mkExpr(Kind.FLOATINGPOINT_PLUS,
        rm,
        a,
        em.mkExpr(Kind.FLOATINGPOINT_PLUS, rm, b, c));
    Expr rhs = em.mkExpr(Kind.FLOATINGPOINT_PLUS,
        rm,
        em.mkExpr(Kind.FLOATINGPOINT_PLUS, rm, a, b),
        c);
    smt.assertFormula(em.mkExpr(Kind.NOT, em.mkExpr(Kind.EQUAL, a, b)));

    Result r = smt.checkSat(); // result is sat
    assert r.isSat() == Result.Sat.SAT;

    System.out.println("a = " + smt.getValue(a));
    System.out.println("b = " + smt.getValue(b));
    System.out.println("c = " + smt.getValue(c));

    // Now, let's restrict `a` to be either NaN or positive infinity
    FloatingPointSize fps32 = new FloatingPointSize(8, 24);
    Expr nan = em.mkConst(FloatingPoint.makeNaN(fps32));
    Expr inf = em.mkConst(FloatingPoint.makeInf(fps32, /* sign */ true));
    smt.assertFormula(em.mkExpr(
        Kind.OR, em.mkExpr(Kind.EQUAL, a, inf), em.mkExpr(Kind.EQUAL, a, nan)));

    r = smt.checkSat(); // result is sat
    assert r.isSat() == Result.Sat.SAT;

    System.out.println("a = " + smt.getValue(a));
    System.out.println("b = " + smt.getValue(b));
    System.out.println("c = " + smt.getValue(c));

    // And now for something completely different. Let's try to find a (normal)
    // floating-point number that rounds to different integer values for
    // different rounding modes.
    Expr rtp = em.mkConst(RoundingMode.roundTowardPositive);
    Expr rtn = em.mkConst(RoundingMode.roundTowardNegative);
    Expr op = em.mkConst(new FloatingPointToSBV(16)); // (_ fp.to_sbv 16)
    lhs = em.mkExpr(op, rtp, d);
    rhs = em.mkExpr(op, rtn, d);
    smt.assertFormula(em.mkExpr(Kind.FLOATINGPOINT_ISN, d));
    smt.assertFormula(em.mkExpr(Kind.NOT, em.mkExpr(Kind.EQUAL, lhs, rhs)));

    r = smt.checkSat(); // result is sat
    assert r.isSat() == Result.Sat.SAT;

    // Convert the result to a rational and print it
    Expr val = smt.getValue(d);
    Rational realVal =
        val.getConstFloatingPoint().convertToRationalTotal(new Rational(0));
    System.out.println("d = " + val + " = " + realVal);
    System.out.println("((_ fp.to_sbv 16) RTP d) = " + smt.getValue(lhs));
    System.out.println("((_ fp.to_sbv 16) RTN d) = " + smt.getValue(rhs));

    // For our final trick, let's try to find a floating-point number between
    // positive zero and the smallest positive floating-point number
    Expr zero = em.mkConst(FloatingPoint.makeZero(fps32, /* sign */ true));
    Expr smallest =
        em.mkConst(new FloatingPoint(8, 24, new BitVector(32, 0b001)));
    smt.assertFormula(em.mkExpr(Kind.AND,
        em.mkExpr(Kind.FLOATINGPOINT_LT, zero, e),
        em.mkExpr(Kind.FLOATINGPOINT_LT, e, smallest)));

    r = smt.checkSat(); // result is unsat
    assert r.isSat() == Result.Sat.UNSAT;
  }
}
