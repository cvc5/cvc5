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
 * Black box testing of Command.
 */

package tests;

import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import io.github.cvc5.modes.*;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class CommandTest extends ParserTest
{
  Command parseCommand(String cmdStr)
  {
    InputParser parser = new InputParser(d_solver, d_symman);
    parser.setIncrementalStringInput(InputLanguage.SMT_LIB_2_6, "command_black");
    parser.appendIncrementalStringInput(cmdStr);
    return parser.nextCommand();
  }

  @Test
  void invoke()
  {
    Command cmd;
    // set logic command can be executed
    cmd = parseCommand("(set-logic QF_LIA)");
    assertNotEquals(cmd.isNull(), true);
    cmd.invoke(d_solver, d_symman);
    // get model not available
    cmd = parseCommand("(get-model)");
    assertNotEquals(cmd.isNull(), true);
    String result = cmd.invoke(d_solver, d_symman);
    assertEquals(
        "(error \"Cannot get model unless model generation is enabled (try --produce-models)\")\n",
        result);
    // logic already set
    assertThrows(CVC5ParserException.class, () -> parseCommand("(set-logic QF_LRA)"));
  }

  @Test
  void commandToString()
  {
    Command cmd;
    cmd = parseCommand("(set-logic QF_LIA )");
    assertNotEquals(cmd.isNull(), true);
    // note normalizes wrt whitespace
    assertEquals(cmd.toString(), "(set-logic QF_LIA)");
  }

  @Test
  void getCommandName()
  {
    Command cmd;
    cmd = parseCommand("(get-model)");
    assertNotEquals(cmd.isNull(), true);
    assertEquals(cmd.getCommandName(), "get-model");
  }
}
