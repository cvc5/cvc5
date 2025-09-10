/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Daniel Larraz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of reasoning about sequences with cvc5 via C++ API.
 */

import static io.github.cvc5.Kind.*;

import io.github.cvc5.*;

public class Sequences
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

      // Sequence sort
      Sort intSeq = tm.mkSequenceSort(tm.getIntegerSort());

      // Sequence variables
      Term x = tm.mkConst(intSeq, "x");
      Term y = tm.mkConst(intSeq, "y");

      // Empty sequence
      Term empty = tm.mkEmptySequence(tm.getIntegerSort());
      // Sequence concatenation: x.y.empty
      Term concat = tm.mkTerm(SEQ_CONCAT, x, y, empty);
      // Sequence length: |x.y.empty|
      Term concat_len = tm.mkTerm(SEQ_LENGTH, concat);
      // |x.y.empty| > 1
      Term formula1 = tm.mkTerm(GT, concat_len, tm.mkInteger(1));
      // Sequence unit: seq(1)
      Term unit = tm.mkTerm(SEQ_UNIT, tm.mkInteger(1));
      // x = seq(1)
      Term formula2 = tm.mkTerm(EQUAL, x, unit);

      // Make a query
      Term q = tm.mkTerm(AND, formula1, formula2);

      // check sat
      Result result = slv.checkSatAssuming(q);
      System.out.println("cvc5 reports: " + q + " is " + result + ".");

      if (result.isSat())
      {
        System.out.println("  x = " + slv.getValue(x));
        System.out.println("  y = " + slv.getValue(y));
      }
    }
    Context.deletePointers();
  }
}