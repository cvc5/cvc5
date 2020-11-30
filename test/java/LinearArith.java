/*********************                                                        */
/*! \file LinearArith.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Pat Hawks, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

import static org.junit.Assert.assertEquals;

import edu.stanford.CVC4.*;
import org.junit.Before;
import org.junit.Test;

public class LinearArith {
  static {
    System.loadLibrary("cvc4jni");
  }
  ExprManager em;
  SmtEngine smt;

  @Before
  public void initialize() {
    em = new ExprManager();
    smt = new SmtEngine(em);
  }

  @Test
  public void evaluatesExpression() {
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
    smt.assertFormula(assumptions);
    smt.push();
    Expr diff_leq_two_thirds = em.mkExpr(Kind.LEQ, diff, two_thirds);

    assertEquals(Result.Entailment.ENTAILED,
        smt.checkEntailed(diff_leq_two_thirds).isEntailed());

    smt.pop();

    smt.push();
    Expr diff_is_two_thirds = em.mkExpr(Kind.EQUAL, diff, two_thirds);
    smt.assertFormula(diff_is_two_thirds);

    assertEquals(
        Result.Sat.SAT,
        smt.checkSat(em.mkConst(true)).isSat()
    );

    smt.pop();
  }
}
