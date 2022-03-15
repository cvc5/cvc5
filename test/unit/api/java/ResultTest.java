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

class ResultTest
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
    Result res_null = d_solver.getNullResult();
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

  @Test void eq()
  {
    Sort u_sort = d_solver.mkUninterpretedSort("u");
    Term x = d_solver.mkConst(u_sort, "x");
    d_solver.assertFormula(x.eqTerm(x));
    Result res;
    Result res2 = d_solver.checkSat();
    Result res3 = d_solver.checkSat();
    res = res2;
    assertEquals(res, res2);
    assertEquals(res3, res2);
  }

  @Test void isSat()
  {
    Sort u_sort = d_solver.mkUninterpretedSort("u");
    Term x = d_solver.mkConst(u_sort, "x");
    d_solver.assertFormula(x.eqTerm(x));
    Result res = d_solver.checkSat();
    assertTrue(res.isSat());
    assertFalse(res.isUnknown());
  }

  @Test void isUnsat()
  {
    Sort u_sort = d_solver.mkUninterpretedSort("u");
    Term x = d_solver.mkConst(u_sort, "x");
    d_solver.assertFormula(x.eqTerm(x).notTerm());
    Result res = d_solver.checkSat();
    assertTrue(res.isUnsat());
    assertFalse(res.isUnknown());
  }

  @Test void isUnknown() throws CVC5ApiException
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
  }
}
