/******************************************************************************
 * Top contributors (to current version):
 *   Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * "Ouroborous" test: does cvc5 read its own output?
 *
 * The "Ouroborous" test, named after the serpent that swallows its
 * own tail, ensures that cvc5 can parse some input, output it again
 * (in any of its languages) and then parse it again.  The result of
 * the first parse must be equal to the result of the second parse;
 * both strings and expressions are compared for equality.
 *
 * To add a new test, simply add a call to runTestString() under
 * runTest(), below.  If you don't specify an input language,
 * LANG_SMTLIB_V2 is used.  If your example depends on symbolic constants,
 * you'll need to declare them in the "declarations" global, just
 * below, in SMT-LIBv2 form (but they're good for all languages).
 */

import io.github.cvc5.*;
import io.github.cvc5.modes.*;
import java.io.*;

public class Ouroborous
{
  public static void main(String[] args)
  {
    try
    {
      System.exit(runTest());
    }
    catch (CVC5ApiException e)
    {
      System.err.println(e.getMessage());
    }
    catch (Exception e)
    {
      System.err.println("non-cvc5 exception thrown");
      e.printStackTrace();
    }
    System.exit(1);
  }

  private static String parse(String instr, String inputLanguage, String outputLanguage)
      throws CVC5ApiException
  {
    assert inputLanguage.equals("smt2");
    assert outputLanguage.equals("smt2");

    String declarations = "(set-logic ALL)\n"
        + "(declare-sort U 0)\n"
        + "(declare-fun f (U) U)\n"
        + "(declare-fun x () U)\n"
        + "(declare-fun y () U)\n"
        + "(assert (= (f x) x))\n"
        + "(declare-fun a () (Array U (Array U U)))\n";

    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);

    solver.setOption("input-language", inputLanguage);
    solver.setOption("output-language", outputLanguage);
    SymbolManager symman = new SymbolManager(tm);
    InputParser parser = new InputParser(solver, symman);

    parser.setStringInput(InputLanguage.SMT_LIB_2_6, declarations, "internal-buffer");

    Command c;
    while (true)
    {
      c = parser.nextCommand();
      if (c == null || c.isNull())
      {
        break;
      }
      c.invoke(solver, symman);
    }
    assert parser.done();

    parser.setStringInput(InputLanguage.SMT_LIB_2_6, instr, "internal-buffer");

    Term e = parser.nextTerm();
    String s = e.toString();
    assert parser.nextTerm() == null; // should be no more terms
    return s;
  }

  private static String translate(String instr, String inputLanguage, String outputLanguage)
      throws CVC5ApiException
  {
    assert inputLanguage.equals("smt2");
    assert outputLanguage.equals("smt2");

    System.out.println("==============================================");
    System.out.println(
        "translating from " + inputLanguage + " to " + outputLanguage + " this string:");
    System.out.println(instr);

    String outstr = parse(instr, inputLanguage, outputLanguage);

    System.out.println("got this:");
    System.out.println(outstr);
    System.out.println("reparsing as " + outputLanguage);

    String poutstr = parse(outstr, outputLanguage, outputLanguage);
    assert outstr.equals(poutstr);

    System.out.println("got same expressions " + outstr + " and " + poutstr);
    System.out.println("==============================================");

    return outstr;
  }

  private static void runTestString(String instr, String instrLanguage) throws CVC5ApiException
  {
    System.out.println();
    System.out.println("starting with: " + instr);
    System.out.println("   in language " + instrLanguage);

    String smt2str = translate(instr, instrLanguage, "smt2");
    System.out.println("in SMT2      : " + smt2str);

    String outstr = translate(smt2str, "smt2", "smt2");
    System.out.println("to SMT2 : " + outstr);
    System.out.println();

    assert outstr.equals(smt2str);
  }

  private static int runTest() throws CVC5ApiException
  {
    runTestString("(= (f (f y)) x)", "smt2");
    runTestString("(= ((_ extract 2 1) (bvnot (bvadd #b000 #b011))) #b10)", "smt2");
    runTestString("((_ extract 2 0) (bvnot (bvadd (bvmul #b001 #b011) #b011)))", "smt2");
    return 0;
  }
}