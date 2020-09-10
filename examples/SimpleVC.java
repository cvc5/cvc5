/*********************                                                        */
/*! \file SimpleVC.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Aina Niemetz, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the Java interface
 **
 ** A simple demonstration of the Java interface.
 **
 ** To run the resulting class file, you need to do something like the
 ** following:
 **
 **   java \
 **     -cp path/to/CVC4.jar:SimpleVC.jar \
 **     -Djava.library.path=/dir/containing/libcvc4jni.so \
 **     SimpleVC
 **
 **/

import edu.stanford.CVC4.*;

public class SimpleVC {
  public static void main(String[] args) {
    System.loadLibrary("cvc4jni");

    ExprManager em = new ExprManager();
    SmtEngine smt = new SmtEngine(em);

    // Prove that for integers x and y:
    //   x > 0 AND y > 0  =>  2x + y >= 3

    Type integer = em.integerType();

    Expr x = em.mkVar("x", integer);
    Expr y = em.mkVar("y", integer);
    Expr zero = em.mkConst(new Rational(0));

    Expr x_positive = em.mkExpr(Kind.GT, x, zero);
    Expr y_positive = em.mkExpr(Kind.GT, y, zero);

    Expr two = em.mkConst(new Rational(2));
    Expr twox = em.mkExpr(Kind.MULT, two, x);
    Expr twox_plus_y = em.mkExpr(Kind.PLUS, twox, y);

    Expr three = em.mkConst(new Rational(3));
    Expr twox_plus_y_geq_3 = em.mkExpr(Kind.GEQ, twox_plus_y, three);

    Expr formula =
        em.mkExpr(Kind.AND, x_positive, y_positive).impExpr(twox_plus_y_geq_3);

    System.out.println(
        "Checking entailment of formula " + formula + " with CVC4.");
    System.out.println("CVC4 should report ENTAILED.");
    System.out.println("Result from CVC4 is: " + smt.checkEntailed(formula));
  }
}
