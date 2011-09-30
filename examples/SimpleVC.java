/*********************                                                        */
/*! \file SimpleVC.java
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A simple demonstration of the Java interface
 **
 ** A simple demonstration of the Java interface.
 **
 ** To run the resulting class file, you need to do something like the
 ** following:
 **
 **   java \
 **     -classpath path/to/cvc4.jar \
 **     -Djava.library.path=/dir/containing/libcvc4bindings_java.so \
 **     SimpleVC
 **
 ** For example, if you are building CVC4 without specifying your own
 ** build directory, the build process puts everything in builds/, and
 ** you can run this example (after building it with "make") like this:
 **
 **   java \
 **     -classpath builds/examples:builds/src/bindings/cvc4.jar \
 **     -Djava.library.path=builds/src/bindings/.libs \
 **     SimpleVC
 **/

import edu.nyu.acsys.CVC4.*;
import edu.nyu.acsys.CVC4.Integer;// to override java.lang.Integer name lookup

public class SimpleVC {
  public static void main(String[] args) {
    System.loadLibrary("cvc4bindings_java");

    ExprManager em = new ExprManager();
    SmtEngine smt = new SmtEngine(em);

    // Prove that for integers x and y:
    //   x > 0 AND y > 0  =>  2x + y >= 3

    Type integer = em.integerType();

    Expr x = em.mkVar("x", integer);
    Expr y = em.mkVar("y", integer);
    Expr zero = em.mkConst(new Integer(0));

    Expr x_positive = em.mkExpr(Kind.GT, x, zero);
    Expr y_positive = em.mkExpr(Kind.GT, y, zero);

    Expr two = em.mkConst(new Integer(2));
    Expr twox = em.mkExpr(Kind.MULT, two, x);
    Expr twox_plus_y = em.mkExpr(Kind.PLUS, twox, y);

    Expr three = em.mkConst(new Integer(3));
    Expr twox_plus_y_geq_3 = em.mkExpr(Kind.GEQ, twox_plus_y, three);

    BoolExpr formula =
      new BoolExpr(em.mkExpr(Kind.AND, x_positive, y_positive)).
      impExpr(new BoolExpr(twox_plus_y_geq_3));

    System.out.println("Checking validity of formula " + formula + " with CVC4.");
    System.out.println("CVC4 should report VALID.");
    System.out.println("Result from CVC4 is: " + smt.query(formula));
  }
}
