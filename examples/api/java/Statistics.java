/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An example of accessing CVC4's statistics using the Java API.
 */

import cvc5.*;

public class Statistics {
  public static void main(String[] args) {
    Solver solver = new Solver();

    Sort boolSort = solver.getBooleanSort();
    Term a = solver.mkConst(boolSort, "A");
    Term b = solver.mkConst(boolSort, "B");

    // A ^ B
    solver.assertFormula(solver.mkTerm(Kind.AND, a, b));

    Result res = solver.checkSat();

    // Get the statistics from the `SmtEngine` and iterate over them. The
    // `Statistics` class implements the `Iterable<Statistic>` interface. A
    // `Statistic` is a pair that consists of a name and an `SExpr` that stores
    // the value of the statistic.
//    Statistics stats = solver.getStatistics();
//    for (Statistic stat : stats) {
//      System.out.println(stat.getFirst() + " = " + stat.getSecond());
//    }
  }
}
