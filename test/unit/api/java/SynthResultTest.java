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
 * Black box testing of the SynthResult class
 */

package tests;

import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class SynthResultTest
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
    SynthResult res_null = new SynthResult();
    assertTrue(res_null.isNull());
    assertFalse(res_null.hasSolution());
    assertFalse(res_null.hasNoSolution());
    assertFalse(res_null.isUnknown());
  }

  @Test
  void hasSolution()
  {
    d_solver.setOption("sygus", "true");
    Term f = d_solver.synthFun("f", new Term[] {}, d_tm.getBooleanSort());
    Term boolTerm = d_tm.mkTrue();
    d_solver.addSygusConstraint(boolTerm);
    SynthResult res = d_solver.checkSynth();
    assertFalse(res.isNull());
    assertTrue(res.hasSolution());
    assertFalse(res.hasNoSolution());
    assertFalse(res.isUnknown());
    assertEquals(res.toString(), "(SOLUTION)");
  }

  @Test
  void hasNoSolution()
  {
    SynthResult res_null = new SynthResult();
    assertFalse(res_null.hasSolution());
  }

  @Test
  void isUnknown()
  {
    d_solver.setOption("sygus", "true");
    Term f = d_solver.synthFun("f", new Term[] {}, d_tm.getBooleanSort());
    Term boolTerm = d_tm.mkTrue();
    d_solver.addSygusConstraint(boolTerm);
    SynthResult res = d_solver.checkSynth();
    assertFalse(res.isNull());
    assertTrue(res.hasSolution());
    assertFalse(res.hasNoSolution());
    assertFalse(res.isUnknown());
  }

  @Test
  void equalHash()
  {
    d_solver.setOption("sygus", "true");
    d_solver.synthFun("f", new Term[] {}, d_tm.getBooleanSort());
    Term tfalse = d_tm.mkFalse();
    Term ttrue = d_tm.mkTrue();
    d_solver.addSygusConstraint(ttrue);
    SynthResult res1 = d_solver.checkSynth();
    d_solver.addSygusConstraint(tfalse);
    SynthResult res2 = d_solver.checkSynth();
    assertTrue(res1.equals(res1));
    assertFalse(res1.equals(res2));
    assertEquals(res1.hashCode(), res1.hashCode());
    assertNotEquals(res1.hashCode(), res2.hashCode());
  }
}
