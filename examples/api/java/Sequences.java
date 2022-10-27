/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
    Solver slv = new Solver();
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
      Sort intSeq = slv.mkSequenceSort(slv.getIntegerSort());

      // Sequence variables
      Term x = slv.mkConst(intSeq, "x");
      Term y = slv.mkConst(intSeq, "y");

      // Empty sequence
      Term empty = slv.mkEmptySequence(slv.getIntegerSort());
      // Sequence concatenation: x.y.empty
      Term concat = slv.mkTerm(SEQ_CONCAT, x, y, empty);
      // Sequence length: |x.y.empty|
      Term concat_len = slv.mkTerm(SEQ_LENGTH, concat);
      // |x.y.empty| > 1
      Term formula1 = slv.mkTerm(GT, concat_len, slv.mkInteger(1));
      // Sequence unit: seq(1)
      Term unit = slv.mkTerm(SEQ_UNIT, slv.mkInteger(1));
      // x = seq(1)
      Term formula2 = slv.mkTerm(EQUAL, x, unit);

      // Make a query
      Term q = slv.mkTerm(AND, formula1, formula2);

      // check sat
      Result result = slv.checkSatAssuming(q);
      System.out.println("cvc5 reports: " + q + " is " + result + ".");

      if (result.isSat())
      {
        System.out.println("  x = " + slv.getValue(x));
        System.out.println("  y = " + slv.getValue(y));
      }
    }
  }
}