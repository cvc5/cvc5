/*********************                                                        */
/*! \file BitVectorsAndArrays.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Test case for issue #2846
 **
 ** This test case tests whether the dependency information for keeping the
 ** ExprManager alive is maintained correctly.
 **/

import edu.stanford.CVC4.*;
import org.junit.Test;

public class Issue2846 {
  static {
    System.loadLibrary("cvc4jni");
  }

  @Test
  public void test() throws InterruptedException {
    testInternal();
    gc("h");
  }

  private static void testInternal() throws InterruptedException {
    ExprManager em = new ExprManager();
    SmtEngine smt = new SmtEngine(em);
    smt.setOption("produce-models", new SExpr(true));
    Expr x = em.mkVar("x", em.integerType());
    Expr y = em.mkVar("y", em.integerType());
    Expr z = em.mkVar("z", em.integerType());
    gc("a");
    Expr a1 = em.mkExpr(Kind.GT, x, em.mkExpr(Kind.PLUS, y, z));
    gc("b");
    smt.assertFormula(a1);
    gc("c");
    Expr a2 = em.mkExpr(Kind.LT, y, z);
    gc("d");
    smt.assertFormula(a2);
    gc("e");
    System.out.println(a1);
    System.out.println(a2);
    gc("f");
    Result res = smt.checkSat();
    gc("g");
    System.out.println("Res = " + res);
    System.out.println("x =  " + smt.getValue(x));
    System.out.println("y =  " + smt.getValue(y));
    System.out.println("z =  " + smt.getValue(z));
  }

  private static void gc(String msg) throws InterruptedException {
    System.out.println("calling gc " + msg);
    Thread.sleep(100);
    System.gc();
  }
}
