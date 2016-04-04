/*********************                                                        */
/*! \file SimpleVCCompat.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the Java compatibility interface
 ** (quite similar to the old CVC3 Java interface)
 **
 ** A simple demonstration of the Java compatibility interface
 ** (quite similar to the old CVC3 Java interface).
 **
 ** To run the resulting class file, you need to do something like the
 ** following:
 **
 **   java \
 **     -classpath path/to/CVC4compat.jar \
 **     -Djava.library.path=/dir/containing/libcvc4bindings_java_compat.so \
 **     SimpleVCCompat
 **
 ** For example, if you are building CVC4 without specifying your own
 ** build directory, the build process puts everything in builds/, and
 ** you can run this example (after building it with "make") like this:
 **
 **   java \
 **     -classpath builds/examples:builds/src/bindings/compat/java/CVC4compat.jar \
 **     -Djava.library.path=builds/src/bindings/compat/java/.libs \
 **     SimpleVCCompat
 **/

import cvc3.*;

public class SimpleVCCompat {
  public static void main(String[] args) {
    ValidityChecker vc = ValidityChecker.create();

    // Prove that for integers x and y:
    //   x > 0 AND y > 0  =>  2x + y >= 3

    Type integer = vc.intType();

    Expr x = vc.varExpr("x", integer);
    Expr y = vc.varExpr("y", integer);
    Expr zero = vc.ratExpr(0);

    Expr x_positive = vc.gtExpr(x, zero);
    Expr y_positive = vc.gtExpr(y, zero);

    Expr two = vc.ratExpr(2);
    Expr twox = vc.multExpr(two, x);
    Expr twox_plus_y = vc.plusExpr(twox, y);

    Expr three = vc.ratExpr(3);
    Expr twox_plus_y_geq_3 = vc.geExpr(twox_plus_y, three);

    Expr formula = vc.impliesExpr(vc.andExpr(x_positive, y_positive),
                                  twox_plus_y_geq_3);

    System.out.println("Checking validity of formula " + formula + " with CVC4.");
    System.out.println("CVC4 should report VALID.");
    System.out.println("Result from CVC4 is: " + vc.query(formula));
  }
}
