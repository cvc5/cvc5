/*********************                                                        */
/*! \file Strings.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Tianyi Liang, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Reasoning about strings with CVC4 via Java API.
 **
 ** A simple demonstration of reasoning about strings with CVC4 via Jave API.
 **/

import edu.stanford.CVC4.*;

public class Strings {
  public static void main(String[] args) {
    System.loadLibrary("cvc4jni");

    ExprManager em = new ExprManager();
    SmtEngine smt = new SmtEngine(em);

    // Set the logic
    smt.setLogic("S");

    // Produce models
    smt.setOption("produce-models", new SExpr(true));
    // The option strings-exp is needed
    smt.setOption("strings-exp", new SExpr(true));
	// output-language
    smt.setOption("output-language", new SExpr("smt2"));

    // String type
    Type string = em.stringType();

    // String constants
    Expr ab  = em.mkConst(new CVC4String("ab"));
    Expr abc = em.mkConst(new CVC4String("abc"));
    // Variables
    Expr x = em.mkVar("x", string);
    Expr y = em.mkVar("y", string);
    Expr z = em.mkVar("z", string);

    // String concatenation: x.ab.y
    Expr lhs = em.mkExpr(Kind.STRING_CONCAT, x, ab, y);
    // String concatenation: abc.z
    Expr rhs = em.mkExpr(Kind.STRING_CONCAT, abc, z);;
    // x.ab.y = abc.z
    Expr formula1 = em.mkExpr(Kind.EQUAL, lhs, rhs);

    // Length of y: |y|
    Expr leny = em.mkExpr(Kind.STRING_LENGTH, y);
    // |y| >= 0
    Expr formula2 = em.mkExpr(Kind.GEQ, leny, em.mkConst(new Rational(0)));

    // Regular expression: (ab[c-e]*f)|g|h
    Expr r = em.mkExpr(Kind.REGEXP_UNION,
      em.mkExpr(Kind.REGEXP_CONCAT,
        em.mkExpr(Kind.STRING_TO_REGEXP, em.mkConst(new CVC4String("ab"))),
        em.mkExpr(Kind.REGEXP_STAR,
          em.mkExpr(Kind.REGEXP_RANGE, em.mkConst(new CVC4String("c")), em.mkConst(new CVC4String("e")))),
        em.mkExpr(Kind.STRING_TO_REGEXP, em.mkConst(new CVC4String("f")))),
      em.mkExpr(Kind.STRING_TO_REGEXP, em.mkConst(new CVC4String("g"))),
      em.mkExpr(Kind.STRING_TO_REGEXP, em.mkConst(new CVC4String("h"))));

    // String variables
    Expr s1 = em.mkVar("s1", string);
    Expr s2 = em.mkVar("s2", string);
    // String concatenation: s1.s2
    Expr s = em.mkExpr(Kind.STRING_CONCAT, s1, s2);

    // s1.s2 in (ab[c-e]*f)|g|h
    Expr formula3 = em.mkExpr(Kind.STRING_IN_REGEXP, s, r);

	// Make a query
    Expr q = em.mkExpr(Kind.AND,
      formula1,
      formula2,
      formula3);

     // check sat
     Result result = smt.checkSat(q);
     System.out.println("CVC4 reports: " + q + " is " + result + ".");

     System.out.println("  x  = " + smt.getValue(x));
     System.out.println("  s1.s2 = " + smt.getValue(s));
  }
}
