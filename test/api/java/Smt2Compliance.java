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
 * A test of SMT-LIBv2 commands, checks for compliant output.
 */

import io.github.cvc5.*;
import io.github.cvc5.modes.*;

public class Smt2Compliance
{
  public static void testGetInfo(Solver solver, String key)
  {
    SymbolManager sm = new SymbolManager(solver.getTermManager());
    InputParser p = new InputParser(solver, sm);

    String s = "(get-info " + key + ")";
    p.setStringInput(InputLanguage.SMT_LIB_2_6, s, "<internal>");

    Command c = p.nextCommand();
    assert (!c.isNull());

    System.out.println(c);

    s = c.invoke(solver, sm);

    c = p.nextCommand();
    assert (c.isNull());

    System.out.println(s);
  }

  public static void main(String[] args)
  {
    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);

    solver.setOption("input-language", "smtlib2");
    solver.setOption("output-language", "smtlib2");

    testGetInfo(solver, ":error-behavior");
    testGetInfo(solver, ":name");
    testGetInfo(solver, ":authors");
    testGetInfo(solver, ":version");
    testGetInfo(solver, ":status");
    testGetInfo(solver, ":reason-unknown");
    testGetInfo(solver, ":arbitrary-undefined-keyword");
    testGetInfo(solver, ":<="); // legal
    testGetInfo(solver, ":->"); // legal
    testGetInfo(solver, ":all-statistics");

    System.exit(0);
  }
}
