/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Result class
 */

package tests;

import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class ResultTest
{
  private Solver d_solver;

  @BeforeEach
  void setUp()
  {
    d_solver = new Solver();
  }

  @AfterEach
  void tearDown()
  {
    Context.deletePointers();
  }

  @Test
  void isNull()
  {
    Result res_null = new Result();
    assertTrue(res_null.isNull());
    assertFalse(res_null.isSat());
    assertFalse(res_null.isUnsat());
    assertFalse(res_null.isUnknown());
    Sort u_sort = d_solver.mkUninterpretedSort("u");
    Term x = d_solver.mkConst(u_sort, "x");
    d_solver.assertFormula(x.eqTerm(x));
    Result res = d_solver.checkSat();
    assertFalse(res.isNull());
  }

  @Test
  void eq()
  {
    Sort u_sort = d_solver.mkUninterpretedSort();
    Term x = d_solver.mkConst(u_sort, "x");
    d_solver.assertFormula(x.eqTerm(x));
    Result res = null;
    Result res2 = d_solver.checkSat();
    Result res3 = d_solver.checkSat();
    assertTrue(res != res2);
    res = res2;
    assertEquals(res, res2);
    assertEquals(res3, res2);
    assertEquals(res.toString(), "sat");
  }

  @Test
  void isSat()
  {
    Sort u_sort = d_solver.mkUninterpretedSort("u");
    Term x = d_solver.mkConst(u_sort, "x");
    d_solver.assertFormula(x.eqTerm(x));
    Result res = d_solver.checkSat();
    assertTrue(res.isSat());
    assertFalse(res.isUnknown());
  }

  @Test
  void isUnsat()
  {
    Sort u_sort = d_solver.mkUninterpretedSort();
    Term x = d_solver.mkConst(u_sort, "x");
    d_solver.assertFormula(x.eqTerm(x).notTerm());
    Result res = d_solver.checkSat();
    assertTrue(res.isUnsat());
    assertFalse(res.isUnknown());
  }

  @Test
  void isUnknown() throws CVC5ApiException
  {
    d_solver.setLogic("QF_NIA");
    d_solver.setOption("incremental", "false");
    d_solver.setOption("solve-int-as-bv", "32");
    Sort int_sort = d_solver.getIntegerSort();
    Term x = d_solver.mkConst(int_sort, "x");
    d_solver.assertFormula(x.eqTerm(x).notTerm());
    Result res = d_solver.checkSat();
    assertFalse(res.isSat());
    assertTrue(res.isUnknown());
    UnknownExplanation ue = res.getUnknownExplanation();
    assertEquals(ue, UnknownExplanation.UNKNOWN_REASON);
    assertEquals(ue.toString(), "UNKNOWN_REASON");
  }
}
