/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the lifetime guarantees of the Java parser API.
 *
 * A symbol manager keeps the internal node manager alive (it holds its own
 * copy of the term manager). Terms and sorts obtained through the parser must
 * therefore remain usable after the parser, symbol manager, solver and term
 * manager that produced them have been deterministically freed.
 *
 * Mirrors test/unit/api/cpp/api_parser_lifetime_black.cpp.
 */

package tests;

import static io.github.cvc5.Kind.*;
import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import io.github.cvc5.modes.*;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

class ParserLifetimeTest
{
  @AfterEach
  void tearDown()
  {
    Context.deletePointers();
  }

  @Test
  void symbolManagerOutlivesTermManager() throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    SymbolManager sm = new SymbolManager(tm);
    // Deterministically free the native term manager; the symbol manager
    // keeps the node manager alive through its own copy of the term manager.
    tm.deletePointer();
    assertFalse(sm.isLogicSet());
    assertEquals(0, sm.getDeclaredTerms().length);
    assertEquals(0, sm.getDeclaredSorts().length);
  }

  @Test
  void declaredSymbolsOutliveParserAndManagers() throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);
    SymbolManager sm = new SymbolManager(tm);
    InputParser p = new InputParser(solver, sm);
    p.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "parser_lifetime");
    p.appendIncrementalStringInput("(set-logic ALL)\n");
    p.appendIncrementalStringInput("(declare-sort U 0)\n");
    p.appendIncrementalStringInput("(declare-fun a () Int)\n");
    p.appendIncrementalStringInput("(declare-fun b () U)\n");
    for (Command cmd = p.nextCommand(); !cmd.isNull(); cmd = p.nextCommand())
    {
      cmd.invoke(solver, sm);
    }
    Term[] terms = sm.getDeclaredTerms();
    Sort[] sorts = sm.getDeclaredSorts();
    assertEquals(2, terms.length);
    assertEquals(1, sorts.length);
    // Deterministically free parser, symbol manager, solver and term manager.
    p.deletePointer();
    sm.deletePointer();
    solver.deletePointer();
    tm.deletePointer();
    for (Term t : terms)
    {
      assertFalse(t.isNull());
      assertDoesNotThrow(() -> t.getSort());
      assertDoesNotThrow(() -> t.toString());
    }
    for (Sort s : sorts)
    {
      assertFalse(s.isNull());
      assertDoesNotThrow(() -> s.toString());
    }
  }

  @Test
  void parsedTermOutlivesParserAndManagers() throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);
    SymbolManager sm = new SymbolManager(tm);
    InputParser p = new InputParser(solver, sm);
    p.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "parser_lifetime");
    p.appendIncrementalStringInput("(set-logic ALL)\n");
    p.appendIncrementalStringInput("(declare-fun x () Int)\n");
    Command cmd = p.nextCommand();
    cmd.invoke(solver, sm);
    cmd = p.nextCommand();
    cmd.invoke(solver, sm);
    p.appendIncrementalStringInput("(+ x 1)\n");
    Term t = p.nextTerm();
    p.deletePointer();
    sm.deletePointer();
    solver.deletePointer();
    tm.deletePointer();
    assertFalse(t.isNull());
    assertEquals(ADD, t.getKind());
    assertTrue(t.getSort().isInteger());
    assertDoesNotThrow(() -> t.toString());
  }

  @Test
  void parsedTermOutlivesParserWithInternalSymbolManager() throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);
    // This parser allocates and owns its own symbol manager.
    InputParser p = new InputParser(solver);
    p.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "parser_lifetime");
    p.appendIncrementalStringInput("(set-logic ALL)\n");
    p.appendIncrementalStringInput("(declare-fun x () Int)\n");
    Command cmd = p.nextCommand();
    cmd.invoke(solver, p.getSymbolManager());
    cmd = p.nextCommand();
    cmd.invoke(solver, p.getSymbolManager());
    p.appendIncrementalStringInput("(* x 2)\n");
    Term t = p.nextTerm();
    p.deletePointer();
    solver.deletePointer();
    tm.deletePointer();
    assertFalse(t.isNull());
    assertEquals(MULT, t.getKind());
    assertTrue(t.getSort().isInteger());
    assertDoesNotThrow(() -> t.toString());
  }
}
