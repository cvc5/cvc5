/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
    assertThrows(CVC5ApiException.class, () ->
        p.setFileInput(InputLanguage.SMT_LIB_2_6, "nonexistent.smt2"));
  }

  // @Test
  // void setStreamInput()
  // {
  //   InputParser p = new InputParser(d_solver);
  //   std::stringstream ss;
  //   ss << "(set-logic QF_LIA)" << std::endl;
  //   ss << "(declare-fun a () Bool)" << std::endl;
  //   ss << "(declare-fun b () Int)" << std::endl;
  //   p.setStreamInput(InputLanguage.SMT_LIB_2_6, ss, "input_parser_black");
  //   assertEquals(p.done(), false);
  //   Command cmd;
  //   std::stringstream out;
  //   while (true)
  //   {
  //     cmd = p.nextCommand();
  //     if (cmd.isNull())
  //     {
  //       break;
  //     }
  //     assertDoesNotThrow(() ->cmd.invoke(d_solver, d_symman.get(), out));
  //   }
  //   assertEquals(p.done(), true);
  // }

  // @Test
  // void setAndAppendIncrementalStringInput()
  // {
  //   std::stringstream out;
  //   InputParser p = new InputParser(d_solver);
  //   p.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "input_parser_black");
  //   Command cmd;
  //   p.appendIncrementalStringInput("(set-logic ALL)");
  //   cmd = p.nextCommand();
  //   assertNotEquals(cmd.isNull(), true);
  //   assertDoesNotThrow(() ->cmd.invoke(d_solver, d_symman.get(), out));
  //   p.appendIncrementalStringInput("(declare-fun a () Bool)");
  //   cmd = p.nextCommand();
  //   assertNotEquals(cmd.isNull(), true);
  //   assertDoesNotThrow(() ->cmd.invoke(d_solver, d_symman.get(), out));
  //   p.appendIncrementalStringInput("(declare-fun b () Int)");
  //   cmd = p.nextCommand();
  //   assertNotEquals(cmd.isNull(), true);
  //   assertDoesNotThrow(() ->cmd.invoke(d_solver, d_symman.get(), out));
  // }

  // @Test
  // void nextCommand()
  // {
  //   InputParser p = new InputParser(d_solver);
  //   assertThrows(CVC5ApiException.class, () ->p.nextCommand());
  //   std::stringstream ss;
  //   p.setStreamInput(InputLanguage.SMT_LIB_2_6, ss, "input_parser_black");
  //   Command cmd = p.nextCommand();
  //   assertEquals(cmd.isNull(), true);
  // }

  // @Test
  // void nextTerm()
  // {
  //   InputParser p = new InputParser(d_solver);
  //   assertThrows(CVC5ApiException.class, () ->p.nextTerm());
  //   std::stringstream ss;
  //   p.setStreamInput(InputLanguage.SMT_LIB_2_6, ss, "input_parser_black");
  //   assertEquals(p.nextTerm().isNull(), true);
  // }

  // @Test
  // void nextTerm2()
  // {
  //   std::stringstream out;
  //   InputParser p(d_solver, d_symman.get());
  //   p.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "input_parser_black");
  //   // parse a declaration command
  //   p.appendIncrementalStringInput("(declare-fun a () Int)");
  //   Command cmd = p.nextCommand();
  //   assertNotEquals(cmd.isNull(), true);
  //   assertDoesNotThrow(() ->cmd.invoke(d_solver, d_symman.get(), out));
  //   // now parse some terms
  //   Term t;
  //   p.appendIncrementalStringInput("45");
  //   assertDoesNotThrow(() ->t = p.nextTerm());
  //   assertEquals(t.isNull(), false);
  //   p.appendIncrementalStringInput("(+ a 1)");
  //   assertDoesNotThrow(() ->t = p.nextTerm());
  //   assertEquals(t.isNull(), false);
  //   assertEquals(t.getKind(), Kind::ADD);
  //   p.appendIncrementalStringInput("(+ b 1)");
  //   assertThrows(CVC5ApiException.class, () ->t = p.nextTerm(), ParserException);
  // }

  // @Test
  // void multipleParsers()
  // {
  //   std::stringstream out;
  //   InputParser p(d_solver, d_symman.get());
  //   // set a logic for the parser
  //   Command cmd = parseLogicCommand(p, "QF_LIA");
  //   assertDoesNotThrow(() ->cmd.invoke(d_solver, d_symman.get(), out));
  //   assertEquals(d_solver.isLogicSet(), true);
  //   assertEquals(d_solver.getLogic(), "QF_LIA");
  //   assertEquals(d_symman -> isLogicSet(), true);
  //   assertEquals(d_symman -> getLogic(), "QF_LIA");
  //   // cannot set logic on solver now
  //   assertThrows(CVC5ApiException.class, () ->d_solver.setLogic("QF_LRA"));

  //   // possible to construct another parser with the same solver and symbol
  //   // manager
  //   InputParser p2(d_solver, p.getSymbolManager());

  //   // possible to construct another parser with a fresh solver
  //   Solver s2;
  //   InputParser p3(s2, d_symman.get());
  //   p3.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "input_parser_black");
  //   // logic is automatically set on the solver
  //   assertEquals(s2.isLogicSet(), true);
  //   assertEquals(s2.getLogic(), "QF_LIA");
  //   // we cannot set the logic since it has already been set
  //   assertThrows(CVC5ApiException.class, () ->parseLogicCommand(p3, "QF_LRA"), ParserException);

  //   // using a solver with the same logic is allowed
  //   Solver s3;
  //   s3.setLogic("QF_LIA");
  //   InputParser p4(s3, d_symman.get());
  //   p4.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "input_parser_black");

  //   // using a solver with a different logic is not allowed
  //   Solver s4;
  //   s4.setLogic("QF_LRA");
  //   InputParser p5(s4, d_symman.get());
  //   assertThrows(CVC5ApiException.class, () ->
  //       p5.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "input_parser_black"),
  //       CVC5ApiException);
  // }
}
