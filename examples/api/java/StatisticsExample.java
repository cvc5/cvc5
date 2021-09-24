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

import static cvc5.Kind.*;

import cvc5.*;
import java.util.List;
import java.util.Map;

public class StatisticsExample
{
  public static void main(String[] args)
  {
    Solver slv = new Solver();
    // String type
    Sort string = slv.getStringSort();

    // std::string
    String str_ab = "ab";
    // String constants
    Term ab = slv.mkString(str_ab);
    Term abc = slv.mkString("abc");
    // String variables
    Term x = slv.mkConst(string, "x");
    Term y = slv.mkConst(string, "y");
    Term z = slv.mkConst(string, "z");

    // String concatenation: x.ab.y
    Term lhs = slv.mkTerm(STRING_CONCAT, x, ab, y);
    // String concatenation: abc.z
    Term rhs = slv.mkTerm(STRING_CONCAT, abc, z);
    // x.ab.y = abc.z
    Term formula1 = slv.mkTerm(EQUAL, lhs, rhs);

    // Length of y: |y|
    Term leny = slv.mkTerm(STRING_LENGTH, y);
    // |y| >= 0
    Term formula2 = slv.mkTerm(GEQ, leny, slv.mkInteger(0));

    // Regular expression: (ab[c-e]*f)|g|h
    Term r = slv.mkTerm(REGEXP_UNION,
        slv.mkTerm(REGEXP_CONCAT,
            slv.mkTerm(STRING_TO_REGEXP, slv.mkString("ab")),
            slv.mkTerm(REGEXP_STAR, slv.mkTerm(REGEXP_RANGE, slv.mkString("c"), slv.mkString("e"))),
            slv.mkTerm(STRING_TO_REGEXP, slv.mkString("f"))),
        slv.mkTerm(STRING_TO_REGEXP, slv.mkString("g")),
        slv.mkTerm(STRING_TO_REGEXP, slv.mkString("h")));

    // String variables
    Term s1 = slv.mkConst(string, "s1");
    Term s2 = slv.mkConst(string, "s2");
    // String concatenation: s1.s2
    Term s = slv.mkTerm(STRING_CONCAT, s1, s2);

    // s1.s2 in (ab[c-e]*f)|g|h
    Term formula3 = slv.mkTerm(STRING_IN_REGEXP, s, r);

    // Make a query
    Term q = slv.mkTerm(AND, formula1, formula2, formula3);

    // check sat
    Result result = slv.checkSatAssuming(q);

    // Get the statistics from the `SmtEngine` and iterate over them. The
    // `Statistics` class implements the `Iterable<Statistic>` interface. A
    // `Statistic` is a pair that consists of a name and an `SExpr` that stores
    // the value of the statistic.
    Statistics stats = slv.getStatistics();
    for (Pair<String, Stat> pair : stats)
    {
      Stat stat = pair.second;
      if (stat.isInt())
      {
        System.out.println(pair.first + " = " + stat.getInt());
      }
      else if (stat.isDouble())
      {
        System.out.println(pair.first + " = " + stat.getDouble());
      }
      else if (stat.isString())
      {
        System.out.println(pair.first + " = " + stat.getString());
      }
      else if (stat.isHistogram())
      {
        System.out.println("-------------------------------------------------------");
        System.out.println(pair.first + " : Map");
        for (Map.Entry<String, Long> entry : stat.getHistogram().entrySet())
        {
          System.out.println(entry.getKey() + " = " + entry.getValue());
        }
        System.out.println("-------------------------------------------------------");
      }
    }
  }
}
