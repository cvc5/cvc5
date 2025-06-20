/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the OmtResult class
 */

package tests;

import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

class OmtResultTest
{

  private TermManager d_tm;
  private Solver d_solver;

  @BeforeEach
  void setUp()
  {
    d_tm = new TermManager();
    d_solver = new Solver(d_tm);
  }

  @AfterEach
  void tearDown()
  {
    Context.deletePointers();
  }

  @Test
  void isNull()
  { 
    OmtResult resNull = new OmtResult(); 
    assertTrue(resNull.isNull());
    assertFalse(resNull.isOptimal());
    assertFalse(resNull.isLimitOptimal());
    assertFalse(resNull.isNonOptimal());
    assertFalse(resNull.isUnbounded());
    assertFalse(resNull.isUnsat());
    assertFalse(resNull.isUnknown());
    assertEquals(resNull.toString(), "(NONE)");
  }

  @Test
  void equalDisequalHash()
  {
    OmtResult res1 = new OmtResult(); 
    OmtResult res2 = new OmtResult(); 
    assertTrue(res1.equals(res1));
    assertEquals(res1.hashCode(), res1.hashCode());
    assertEquals(res1.hashCode(), res2.hashCode());
  }
}
