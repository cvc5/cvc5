/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Result class
 */

package tests;

import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.api.*;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class SynthResultTest
{
  private Solver d_solver;

  @BeforeEach void setUp()
  {
    d_solver = new Solver();
  }

  @AfterEach void tearDown()
  {
    d_solver.close();
  }

  @Test void isNull()
  {
    SynthResult res_null = d_solver.getNullSynthResult();
    assertTrue(res_null.isNull());
    assertFalse(res_null.isSat());
    assertFalse(res_null.isUnsat());
    assertFalse(res_null.isUnknown());
  }
}
