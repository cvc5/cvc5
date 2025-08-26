/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of InputParser SMT-LIbv2 inputs.
 */

package tests;

import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import io.github.cvc5.modes.*;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class InputParserTest extends ParserTest
{
  Command parseLogicCommand(InputParser p, String logic)
  {
    p.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "input_parser_black");
    p.appendIncrementalStringInput("(set-logic " + logic + ")\n");
    return p.nextCommand();
  }

  @Test
  void getSolver()
  {
    InputParser p = new InputParser(d_solver);
    assertEquals(p.getSolver(), d_solver);
  }

  @Test
  void getSymbolManager()
  {
    InputParser p = new InputParser(d_solver);
    // a symbol manager is allocated
    assertNotEquals(p.getSymbolManager(), null);

    InputParser p2 = new InputParser(d_solver, d_symman);
    assertEquals(p2.getSymbolManager(), d_symman);
  }

  @Test
  void setFileInput()
  {
    InputParser p = new InputParser(d_solver);
    assertThrows(CVC5ParserException.class,
        () -> p.setFileInput(InputLanguage.SMT_LIB_2_6, "nonexistent.smt2"));
  }

  @Test
  void setAndAppendIncrementalStringInput()
  {
    InputParser p = new InputParser(d_solver);
    p.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "input_parser_black");
    p.appendIncrementalStringInput("(set-logic ALL)");
    p.appendIncrementalStringInput("(declare-fun a () Bool)");
    p.appendIncrementalStringInput("(declare-fun b () Int)");

    final Command cmd1 = p.nextCommand();
    assertNotEquals(cmd1.isNull(), true);
    assertDoesNotThrow(() -> cmd1.invoke(d_solver, d_symman));

    final Command cmd2 = p.nextCommand();
    assertNotEquals(cmd2.isNull(), true);
    assertDoesNotThrow(() -> cmd2.invoke(d_solver, d_symman));

    final Command cmd3 = p.nextCommand();
    assertNotEquals(cmd3.isNull(), true);
    assertDoesNotThrow(() -> cmd3.invoke(d_solver, d_symman));
  }

  @Test
  void setAndAppendIncrementalStringInputInterleave()
  {
    InputParser p = new InputParser(d_solver);
    p.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "input_parser_black");
    p.appendIncrementalStringInput("(set-logic ALL)");

    final Command cmd1 = p.nextCommand();
    assertNotEquals(cmd1.isNull(), true);
    assertDoesNotThrow(() -> cmd1.invoke(d_solver, d_symman));
    p.appendIncrementalStringInput("(declare-fun a () Bool)");

    final Command cmd2 = p.nextCommand();
    assertNotEquals(cmd2.isNull(), true);
    assertDoesNotThrow(() -> cmd2.invoke(d_solver, d_symman));
    p.appendIncrementalStringInput("(declare-fun b () Int)");

    final Command cmd3 = p.nextCommand();
    assertNotEquals(cmd3.isNull(), true);
    assertDoesNotThrow(() -> cmd3.invoke(d_solver, d_symman));
  }

  @Test
  void appendIncrementalNoSet()
  {
    InputParser p = new InputParser(d_solver);
    assertThrows(CVC5ApiException.class, () -> p.appendIncrementalStringInput("(set-logic ALL)"));
  }

  @Test
  void setStringInput()
  {
    InputParser p = new InputParser(d_solver);
    p.setStringInput(InputLanguage.SMT_LIB_2_6, "(set-logic ALL)", "input_parser_black");
    final Command cmd1 = p.nextCommand();
    assertNotEquals(cmd1.isNull(), true);
    assertDoesNotThrow(() -> cmd1.invoke(d_solver, d_symman));
    final Command cmd2 = p.nextCommand();
    assertEquals(cmd2.isNull(), true);
  }

  @Test
  void nextCommand()
  {
    InputParser p = new InputParser(d_solver);
    assertThrows(CVC5ApiException.class, () -> p.nextCommand());
    p.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "input_parser_black");
    p.appendIncrementalStringInput("");
    Command cmd = p.nextCommand();
    assertEquals(cmd.isNull(), true);
  }

  @Test
  void nextCommandNoInput()
  {
    InputParser p = new InputParser(d_solver);
    p.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "input_parser_black");
    Command cmd = p.nextCommand();
    assertEquals(cmd.isNull(), true);
    Term t = p.nextTerm();
    assertEquals(t.isNull(), true);
  }

  @Test
  void nextTerm()
  {
    InputParser p = new InputParser(d_solver);
    assertThrows(CVC5ApiException.class, () -> p.nextTerm());
    p.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "input_parser_black");
    p.appendIncrementalStringInput("");
    assertEquals(p.nextTerm().isNull(), true);
  }

  @Test
  void nextTerm2()
  {
    InputParser p = new InputParser(d_solver, d_symman);
    p.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "input_parser_black");
    // parse a declaration command
    p.appendIncrementalStringInput("(declare-fun a () Int)\n");
    final Command cmd1 = p.nextCommand();
    assertNotEquals(cmd1.isNull(), true);
    assertDoesNotThrow(() -> cmd1.invoke(d_solver, d_symman));
    // now parse some terms

    p.appendIncrementalStringInput("45\n");
    assertDoesNotThrow(() -> {
      Term t = p.nextTerm();
      assertEquals(t.isNull(), false);
    });

    p.appendIncrementalStringInput("(+ a 1)\n");
    assertDoesNotThrow(() -> {
      Term t = p.nextTerm();
      assertEquals(t.isNull(), false);
      assertEquals(t.getKind(), Kind.ADD);
    });

    p.appendIncrementalStringInput("(+ b 1)\n");
    assertThrows(CVC5ParserException.class, () -> { Term t = p.nextTerm(); });
  }

  @Test
  void multipleParsers() throws CVC5ApiException
  {
    InputParser p = new InputParser(d_solver, d_symman);
    // set a logic for the parser
    Command cmd = parseLogicCommand(p, "QF_LIA");
    assertDoesNotThrow(() -> cmd.invoke(d_solver, d_symman));
    assertEquals(d_solver.isLogicSet(), true);
    assertEquals(d_solver.getLogic(), "QF_LIA");
    assertEquals(d_symman.isLogicSet(), true);
    assertEquals(d_symman.getLogic(), "QF_LIA");
    // cannot set logic on solver now
    assertThrows(CVC5ApiException.class, () -> d_solver.setLogic("QF_LRA"));

    // possible to construct another parser with the same solver and symbol
    // manager
    InputParser p2 = new InputParser(d_solver, p.getSymbolManager());

    // possible to construct another parser with a fresh solver
    Solver s2 = new Solver(d_tm);
    InputParser p3 = new InputParser(s2, d_symman);
    p3.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "input_parser_black");
    // logic is automatically set on the solver
    assertEquals(s2.isLogicSet(), true);
    assertEquals(s2.getLogic(), "QF_LIA");
    // we cannot set the logic since it has already been set
    assertThrows(CVC5ParserException.class, () -> parseLogicCommand(p3, "QF_LRA"));
    assertEquals(p3.done(), true);

    // using a solver with the same logic is allowed
    Solver s3 = new Solver(d_tm);
    s3.setLogic("QF_LIA");
    InputParser p4 = new InputParser(s3, d_symman);
    p4.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "input_parser_black");

    // using a solver with a different logic is not allowed
    Solver s4 = new Solver(d_tm);
    s4.setLogic("QF_LRA");
    InputParser p5 = new InputParser(s4, d_symman);
    assertThrows(CVC5ApiException.class,
        () -> p5.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "input_parser_black"));
  }
  @Test
  void getDeclaredTermsAndSorts()
  {
    InputParser p = new InputParser(d_solver, d_symman);
    p.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "input_parser_black");
    p.appendIncrementalStringInput("(set-logic ALL)");
    p.appendIncrementalStringInput("(declare-sort U 0)");
    p.appendIncrementalStringInput("(declare-fun x () U)");
    for (int i = 0; i < 3; i++)
    {
      final Command cmd = p.nextCommand();
      assertNotEquals(cmd.isNull(), true);
      assertDoesNotThrow(() -> cmd.invoke(d_solver, d_symman));
    }
    Sort[] sorts = d_symman.getDeclaredSorts();
    Term[] terms = d_symman.getDeclaredTerms();
    assertEquals(sorts.length, 1);
    assertEquals(terms.length, 1);
    assertEquals(terms[0].getSort(), sorts[0]);
  }
}
