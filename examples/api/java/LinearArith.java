/*********************                                                        */
/*! \file LinearArith.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the linear arithmetic capabilities of CVC4
 **
 ** A simple demonstration of the linear arithmetic solving capabilities and
 ** the push pop of CVC4. This also gives an example option.
 **/

import edu.stanford.CVC4.*;

public class LinearArith {
  public static void main(String[] args) {
    System.loadLibrary("cvc4jni");

    ExprManager em = new ExprManager();
    SmtEngine smt = new SmtEngine(em);

    smt.setLogic("QF_LIRA"); // Set the logic

    // Prove that if given x (Integer) and y (Real) then
    // the maximum value of y - x is 2/3

    // Types
    Type real = em.realType();
    Type integer = em.integerType();

    // Variables
    Expr x = em.mkVar("x", integer);
    Expr y = em.mkVar("y", real);

    // Constants
    Expr three = em.mkConst(new Rational(3));
    Expr neg2 = em.mkConst(new Rational(-2));
    Expr two_thirds = em.mkConst(new Rational(2,3));

    // Terms
    Expr three_y = em.mkExpr(Kind.MULT, three, y);
    Expr diff = em.mkExpr(Kind.MINUS, y, x);

    // Formulas
    Expr x_geq_3y = em.mkExpr(Kind.GEQ, x, three_y);
    Expr x_leq_y = em.mkExpr(Kind.LEQ, x, y);
    Expr neg2_lt_x = em.mkExpr(Kind.LT, neg2, x);

    Expr assumptions =
      em.mkExpr(Kind.AND, x_geq_3y, x_leq_y, neg2_lt_x);

    System.out.println("Given the assumptions " + assumptions);
    smt.assertFormula(assumptions);


    smt.push();
    Expr diff_leq_two_thirds = em.mkExpr(Kind.LEQ, diff, two_thirds);
    System.out.println("Prove that " + diff_leq_two_thirds + " with CVC4.");
    System.out.println("CVC4 should report ENTAILED.");
    System.out.println(
        "Result from CVC4 is: " + smt.checkEntailed(diff_leq_two_thirds));
    smt.pop();

    System.out.println();

    smt.push();
    Expr diff_is_two_thirds = em.mkExpr(Kind.EQUAL, diff, two_thirds);
    smt.assertFormula(diff_is_two_thirds);
    System.out.println("Show that the asserts are consistent with ");
    System.out.println(diff_is_two_thirds + " with CVC4.");
    System.out.println("CVC4 should report SAT.");
    System.out.println("Result from CVC4 is: " + smt.checkSat(em.mkConst(true)));
    smt.pop();

    System.out.println("Thus the maximum value of (y - x) is 2/3.");
  }
}
