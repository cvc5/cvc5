/******************************************************************************
 * Top contributors (to current version):
 *   Makai Mann, Aina Niemetz, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Op class.
 */

package tests;
import static io.github.cvc5.api.Kind.*;
import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.api.*;
import java.util.Arrays;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class OpTest
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

  @Test void getKind() throws CVC5ApiException
  {
    Op x;
    x = d_solver.mkOp(BITVECTOR_EXTRACT, 31, 1);
    assertDoesNotThrow(() -> x.getKind());
  }

  @Test void isNull() throws CVC5ApiException
  {
    Op x = d_solver.getNullOp();
    assertTrue(x.isNull());
    x = d_solver.mkOp(BITVECTOR_EXTRACT, 31, 1);
    assertFalse(x.isNull());
  }

  @Test void opFromKind()
  {
    assertDoesNotThrow(() -> d_solver.mkOp(ADD));
    assertThrows(CVC5ApiException.class, () -> d_solver.mkOp(BITVECTOR_EXTRACT));
  }


  @Test void opScopingToString() throws CVC5ApiException
  {
    Op bitvector_repeat_ot = d_solver.mkOp(BITVECTOR_REPEAT, 5);
    String op_repr = bitvector_repeat_ot.toString();

    Solver solver2;
    assertEquals(bitvector_repeat_ot.toString(), op_repr);
  }
}
