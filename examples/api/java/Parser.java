/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of using the parser via Java API.
 */

import io.github.cvc5.*;
import io.github.cvc5.modes.*;
public class Parser
{
  public static void main(String args[]) throws CVC5ApiException
  {
    Solver slv = new Solver();

    // set that we should print success after each successful command
    slv.setOption("print-success", "true");

    // construct an input parser associated the solver above
    InputParser parser = new InputParser(slv);

    String ss = "";
    ss += "(set-logic QF_LIA)\n";
    ss += "(declare-fun a () Int)\n";
    ss += "(declare-fun b () Int)\n";
    ss += "(declare-fun c () Int)\n";
    ss += "(assert (> a (+ b c)))\n";
    ss += "(assert (< a b))\n";
    ss += "(assert (> c 0))\n";
    parser.setStringInput(InputLanguage.SMT_LIB_2_6, ss, "MyStream");

    // get the symbol manager of the parser, used when invoking commands below
    SymbolManager sm = parser.getSymbolManager();

    // parse commands until finished
    Command cmd;
    while (true)
    {
      cmd = parser.nextCommand();
      if (cmd.isNull())
      {
        break;
      }
      System.out.println("Executing command " + cmd + ":");
      // invoke the command on the solver and the symbol manager, print the result
      // to standard output
      System.out.println(cmd.invoke(slv, sm));
    }
    System.out.println("Finished parsing commands");

    // now, check sat with the solver
    Result r = slv.checkSat();
    System.out.println("expected: unsat");
    System.out.println("result: " + r);
  }
}
