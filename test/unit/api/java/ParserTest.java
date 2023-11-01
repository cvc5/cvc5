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
 * Common header for parser API unit test.
 */

package tests;

import io.github.cvc5.*;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.TestInfo;

class ParserTest
{
  protected Solver d_solver;
  protected SymbolManager d_symman;

  @BeforeEach
  void setUp(TestInfo testInfo)
  {
    System.out.println("Setting up test: " + testInfo.getDisplayName());
    d_solver = new Solver();
    d_solver.setOption("parse-only", "true");
    d_symman = new SymbolManager(d_solver);
  }

  @AfterEach
  void tearDown(TestInfo testInfo)
  {
    System.out.println("Tearing down test: " + testInfo.getDisplayName());
    Context.deletePointers();
  }
}
