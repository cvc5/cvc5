/*********************                                                        */
/*! \file Exceptions.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Catching CVC4 exceptions via the Java API.
 **
 ** A simple demonstration of catching CVC4 execptions via the Java API.
 **/

import edu.stanford.CVC4.*;

public class Exceptions {
  public static void main(String[] args) {
    System.loadLibrary("cvc4jni");

    ExprManager em = new ExprManager();
    SmtEngine smt = new SmtEngine(em);

    smt.setOption("produce-models", new SExpr(true));

    // Setting an invalid option
    try {
      smt.setOption("non-existing", new SExpr(true));
      System.exit(1);
    } catch (edu.stanford.CVC4.Exception e) {
      System.out.println(e.toString());
    }

    // Creating a term with an invalid type
    try {
      Type integer = em.integerType();
      Expr x = em.mkVar("x", integer);
      Expr invalidExpr = em.mkExpr(Kind.AND, x, x);
      smt.checkSat(invalidExpr);
      System.exit(1);
    } catch (edu.stanford.CVC4.Exception e) {
      System.out.println(e.toString());
    }

    // Asking for a model after unsat result
    try {
      smt.checkSat(em.mkConst(false));
      smt.getModel();
      System.exit(1);
    } catch (edu.stanford.CVC4.Exception e) {
      System.out.println(e.toString());
    }
  }
}
