/******************************************************************************
 * Top contributors (to current version):
 *   Daniel Larraz, Mudathir Mohamed, Tianyi Liang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of reasoning about strings with cvc5 via C++ API.
 */

import static io.github.cvc5.Kind.*;

import io.github.cvc5.*;

public class Strings
{
  public static void main(String args[]) throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver slv = new Solver(tm);
    {
      // Set the logic
      slv.setLogic("QF_SLIA");
      // Produce models
      slv.setOption("produce-models", "true");
      // The option strings-exp is needed
      slv.setOption("strings-exp", "true");
      // Set output language to SMTLIB2
      slv.setOption("output-language", "smt2");

      // String type
      Sort string = tm.getStringSort();

      // std::string
      String str_ab = "ab";
      // String constants
      Term ab = tm.mkString(str_ab);
      Term abc = tm.mkString("abc");
      // String variables
      Term x = tm.mkConst(string, "x");
      Term y = tm.mkConst(string, "y");
      Term z = tm.mkConst(string, "z");

      // String concatenation: x.ab.y
      Term lhs = tm.mkTerm(STRING_CONCAT, x, ab, y);
      // String concatenation: abc.z
      Term rhs = tm.mkTerm(STRING_CONCAT, abc, z);
      // x.ab.y = abc.z
      Term formula1 = tm.mkTerm(EQUAL, lhs, rhs);

      // Length of y: |y|
      Term leny = tm.mkTerm(STRING_LENGTH, y);
      // |y| >= 0
      Term formula2 = tm.mkTerm(GEQ, leny, tm.mkInteger(0));

      // Regular expression: (ab[c-e]*f)|g|h
      Term r = tm.mkTerm(REGEXP_UNION,
          tm.mkTerm(REGEXP_CONCAT,
              tm.mkTerm(STRING_TO_REGEXP, tm.mkString("ab")),
              tm.mkTerm(REGEXP_STAR, tm.mkTerm(REGEXP_RANGE, tm.mkString("c"), tm.mkString("e"))),
              tm.mkTerm(STRING_TO_REGEXP, tm.mkString("f"))),
          tm.mkTerm(STRING_TO_REGEXP, tm.mkString("g")),
          tm.mkTerm(STRING_TO_REGEXP, tm.mkString("h")));

      // String variables
      Term s1 = tm.mkConst(string, "s1");
      Term s2 = tm.mkConst(string, "s2");
      // String concatenation: s1.s2
      Term s = tm.mkTerm(STRING_CONCAT, s1, s2);

      // s1.s2 in (ab[c-e]*f)|g|h
      Term formula3 = tm.mkTerm(STRING_IN_REGEXP, s, r);

      // Make a query
      Term q = tm.mkTerm(AND, formula1, formula2, formula3);

      // check sat
      Result result = slv.checkSatAssuming(q);
      System.out.println("cvc5 reports: " + q + " is " + result + ".");

      if (result.isSat())
      {
        System.out.println("  x  = " + slv.getValue(x));
        System.out.println("  s1.s2 = " + slv.getValue(s));
      }
    }
    Context.deletePointers();
  }
}
