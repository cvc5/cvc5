/*********************                                                        */
/*! \file Strings.java
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Reasoning about strings with CVC4 via Java API.
 **
 ** A simple demonstration of reasoning about strings with CVC4 via Jave API.
 **/

import edu.nyu.acsys.CVC4.*;

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

    // Variables
    Expr x = em.mkVar("x", string);
    Expr y = em.mkVar("y", string);
    Expr z = em.mkVar("z", string);

    // String concatenation: x.y
    Expr lhs = em.mkExpr(Kind.STRING_CONCAT, x, y);
    // String concatenation: z.z
    Expr rhs = em.mkExpr(Kind.STRING_CONCAT, z, z);;
    // x.y = z.z
    Expr formula1 = em.mkExpr(Kind.EQUAL, lhs, rhs);

    // Length of y: |y|
    Expr leny = em.mkExpr(Kind.STRING_LENGTH, y);
    // |y| >= 1
    Expr formula2 = em.mkExpr(Kind.GEQ, leny, em.mkConst(new Rational(1)));

    // Make a query
    Expr q = em.mkExpr(Kind.AND,
      formula1,
      formula2);

     // check sat
     Result result = smt.checkSat(q);
     System.out.println("CVC4 reports: " + q + " is " + result + ".");

     System.out.println("  x  = " + smt.getValue(x));
  }
}
