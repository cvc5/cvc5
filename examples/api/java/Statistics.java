/*********************                                                        */
/*! \file Statistics.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An example of accessing CVC4's statistics using the Java API
 **
 ** An example of accessing CVC4's statistics using the Java API.
 **/

import edu.stanford.CVC4.*;
import java.util.Iterator;

public class Statistics {
  public static void main(String[] args) {
    System.loadLibrary("cvc4jni");

    ExprManager em = new ExprManager();
    SmtEngine smt = new SmtEngine(em);

    Type boolType = em.booleanType();
    Expr a = em.mkVar("A", boolType);
    Expr b = em.mkVar("B", boolType);

    // A ^ B
    smt.assertFormula(em.mkExpr(Kind.AND, a, b));

    Result res = smt.checkSat();

    // Get the statistics from the `SmtEngine` and iterate over them. The
    // `Statistics` class implements the `Iterable<Statistic>` interface. A
    // `Statistic` is a pair that consists of a name and an `SExpr` that stores
    // the value of the statistic.
    edu.stanford.CVC4.Statistics stats = smt.getStatistics();
    for (Statistic stat : stats) {
      System.out.println(stat.getFirst() + " = " + stat.getSecond());
    }
  }
}
