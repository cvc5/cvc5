/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of using multiple parsers with the same symbol manager
 * via Java API.
 */

import io.github.cvc5.*;
import io.github.cvc5.modes.*;
public class ParserSymbolManager
{
  public static void main(String args[]) throws CVC5ApiException
  {
    Solver slv = new Solver();

    SymbolManager sm = new SymbolManager(slv);

    // construct an input parser associated the solver above
    InputParser parser = new InputParser(slv, sm);

    String ss = "";
    ss += "(set-logic QF_LIA)\n";
    ss += "(declare-fun a () Int)\n";
    ss += "(declare-fun b () Int)\n";
    ss += "(declare-fun c () Bool)\n";
    parser.setStringInput(InputLanguage.SMT_LIB_2_6, ss, "MyStream");

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
      // invoke the command on the solver and the symbol manager, print the
      // result to std::cout
      System.out.print(cmd.invoke(slv, sm));
    }
    System.out.println("Finished parsing commands");

    // Note that sm now has a,b,c in its symbol table.

    // Now, construct a new parser with the same symbol manager. We will parse
    // terms with it.
    InputParser parser2 = new InputParser(slv, sm);
    String ss2 = "";
    ss2 += "(+ a b)\n";
    ss2 += "(- a 10)\n";
    ss2 += "(>= 0 45)\n";
    ss2 += "(and c c)\n";
    ss2 += "true\n";
    parser2.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "MyStream2");
    parser2.appendIncrementalStringInput(ss2);

    // parse terms until finished
    Term t;
    do
    {
      t = parser2.nextTerm();
      System.out.println("Parsed term: " + t);
    } while (!t.isNull());
    System.out.println("Finished parsing terms");
  }
}
