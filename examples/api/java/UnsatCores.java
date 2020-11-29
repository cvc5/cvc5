/*********************                                                        */
/*! \file UnsatCores.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An example of interacting with unsat cores using CVC4's Java API
 **
 ** An example of interacting with unsat cores using CVC4's Java API.
 **/

import edu.stanford.CVC4.*;
import java.util.Iterator;

public class UnsatCores {
  public static void main(String[] args) {
    System.loadLibrary("cvc4jni");

    ExprManager em = new ExprManager();
    SmtEngine smt = new SmtEngine(em);

    // Enable the production of unsat cores
    smt.setOption("produce-unsat-cores", new SExpr(true));

    Type boolType = em.booleanType();
    Expr a = em.mkVar("A", boolType);
    Expr b = em.mkVar("B", boolType);

    // A ^ B
    smt.assertFormula(em.mkExpr(Kind.AND, a, b));
    // ~(A v B)
    smt.assertFormula(em.mkExpr(Kind.NOT, em.mkExpr(Kind.OR, a, b)));

    Result res = smt.checkSat(); // result is unsat

    // Retrieve the unsat core
    UnsatCore unsatCore = smt.getUnsatCore();
    
    // Print the unsat core
    System.out.println("Unsat Core: " + unsatCore);

    // Iterate over expressions in the unsat core. The `UnsatCore` class
    // implements the `Iterable<Expr>` interface.
    System.out.println("--- Unsat Core ---");
    for (Expr e : unsatCore) {
      System.out.println(e);
    }
  }
}
