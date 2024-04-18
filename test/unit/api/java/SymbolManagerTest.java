/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of SymbolManager.
 */

package tests;

import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import io.github.cvc5.modes.*;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class SymbolManagerTest extends ParserTest
{
  void parseAndSetLogic(String logic)
  {
    InputParser parser = new InputParser(d_solver, d_symman);
    parser.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "symbol_manager_test");
    parser.appendIncrementalStringInput("(set-logic " + logic + ")\n");
    Command cmd = parser.nextCommand();
    assertNotEquals(cmd.isNull(), true);
    cmd.invoke(d_solver, d_symman);
  }

  @Test
  void isLogicSet()
  {
    assertEquals(d_symman.isLogicSet(), false);
    parseAndSetLogic("QF_LIA");
    assertEquals(d_symman.isLogicSet(), true);
  }

  @Test
  void getLogic()
  {
    assertThrows(CVC5ApiException.class, () -> d_symman.getLogic());
    parseAndSetLogic("QF_LIA");
    assertEquals(d_symman.getLogic(), "QF_LIA");
  }
  @Test
  void getDeclaredTermsAndSorts()
  {
    assertEquals(d_symman.getDeclaredSorts().length, 0);
    assertEquals(d_symman.getDeclaredTerms().length, 0);
  }
}
