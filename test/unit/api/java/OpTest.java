/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Mudathir Mohamed, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Op class.
 */

package tests;
import static io.github.cvc5.Kind.*;
import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class OpTest
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
  void getKind() throws CVC5ApiException
  {
    Op x;
    x = d_solver.mkOp(BITVECTOR_EXTRACT, 31, 1);
    assertDoesNotThrow(() -> x.getKind());
  }

  @Test
  void isNull() throws CVC5ApiException
  {
    Op x = new Op();
    assertTrue(x.isNull());
    Op y = d_solver.mkOp(BITVECTOR_EXTRACT, 31, 1);
    assertFalse(y.isNull());
    assertTrue(x != y);
  }

  @Test
  void opFromKind()
  {
    assertDoesNotThrow(() -> d_solver.mkOp(ADD));
    assertThrows(CVC5ApiException.class, () -> d_solver.mkOp(BITVECTOR_EXTRACT));
  }

  @Test
  void getNumIndices() throws CVC5ApiException
  {
    // Operators with 0 indices
    Op plus = d_solver.mkOp(ADD);

    assertEquals(0, plus.getNumIndices());

    // Operators with 1 index
    Op divisible = d_solver.mkOp(DIVISIBLE, 4);
    Op bvRepeat = d_solver.mkOp(BITVECTOR_REPEAT, 5);
    Op bvZeroExtend = d_solver.mkOp(BITVECTOR_ZERO_EXTEND, 6);
    Op bvSignExtend = d_solver.mkOp(BITVECTOR_SIGN_EXTEND, 7);
    Op bvRotateLeft = d_solver.mkOp(BITVECTOR_ROTATE_LEFT, 8);
    Op bvRotateRight = d_solver.mkOp(BITVECTOR_ROTATE_RIGHT, 9);
    Op intToBv = d_solver.mkOp(INT_TO_BITVECTOR, 10);
    Op iand = d_solver.mkOp(IAND, 11);
    Op fpToUbv = d_solver.mkOp(FLOATINGPOINT_TO_UBV, 12);
    Op fpToSbv = d_solver.mkOp(FLOATINGPOINT_TO_SBV, 13);

    assertEquals(1, divisible.getNumIndices());
    assertEquals(1, bvRepeat.getNumIndices());
    assertEquals(1, bvZeroExtend.getNumIndices());
    assertEquals(1, bvSignExtend.getNumIndices());
    assertEquals(1, bvRotateLeft.getNumIndices());
    assertEquals(1, bvRotateRight.getNumIndices());
    assertEquals(1, intToBv.getNumIndices());
    assertEquals(1, iand.getNumIndices());
    assertEquals(1, fpToUbv.getNumIndices());
    assertEquals(1, fpToSbv.getNumIndices());

    // Operators with 2 indices
    Op bvExtract = d_solver.mkOp(BITVECTOR_EXTRACT, 1, 0);
    Op toFpFromIeeeBv = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_IEEE_BV, 3, 2);
    Op toFpFromFp = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_FP, 5, 4);
    Op toFpFromReal = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_REAL, 7, 6);
    Op toFpFromSbv = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_SBV, 9, 8);
    Op toFpFromUbv = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_UBV, 11, 10);
    Op regexpLoop = d_solver.mkOp(REGEXP_LOOP, 15, 14);

    assertEquals(2, bvExtract.getNumIndices());
    assertEquals(2, toFpFromIeeeBv.getNumIndices());
    assertEquals(2, toFpFromFp.getNumIndices());
    assertEquals(2, toFpFromReal.getNumIndices());
    assertEquals(2, toFpFromSbv.getNumIndices());
    assertEquals(2, toFpFromUbv.getNumIndices());
    assertEquals(2, regexpLoop.getNumIndices());

    // Operators with n indices
    int[] indices = {0, 3, 2, 0, 1, 2};
    Op tupleProject = d_solver.mkOp(TUPLE_PROJECT, indices);
    assertEquals(6, tupleProject.getNumIndices());

    Op relationProject = d_solver.mkOp(RELATION_PROJECT, indices);
    assertEquals(6, relationProject.getNumIndices());

    Op tableProject = d_solver.mkOp(TABLE_PROJECT, indices);
    assertEquals(6, tableProject.getNumIndices());
  }

  @Test
  void opSubscriptOperator() throws CVC5ApiException
  {
    // Operators with 0 indices
    Op plus = d_solver.mkOp(ADD);

    assertThrows(CVC5ApiException.class, () -> plus.get(0));

    // Operators with 1 index
    Op divisible = d_solver.mkOp(DIVISIBLE, 4);
    Op bvRepeat = d_solver.mkOp(BITVECTOR_REPEAT, 5);
    Op bvZeroExtend = d_solver.mkOp(BITVECTOR_ZERO_EXTEND, 6);
    Op bvSignExtend = d_solver.mkOp(BITVECTOR_SIGN_EXTEND, 7);
    Op bvRotateLeft = d_solver.mkOp(BITVECTOR_ROTATE_LEFT, 8);
    Op bvRotateRight = d_solver.mkOp(BITVECTOR_ROTATE_RIGHT, 9);
    Op intToBv = d_solver.mkOp(INT_TO_BITVECTOR, 10);
    Op iand = d_solver.mkOp(IAND, 11);
    Op fpToUbv = d_solver.mkOp(FLOATINGPOINT_TO_UBV, 12);
    Op fpToSbv = d_solver.mkOp(FLOATINGPOINT_TO_SBV, 13);
    Op regexpRepeat = d_solver.mkOp(REGEXP_REPEAT, 14);

    assertEquals(4, divisible.get(0).getIntegerValue().intValue());
    assertEquals(5, bvRepeat.get(0).getIntegerValue().intValue());
    assertEquals(6, bvZeroExtend.get(0).getIntegerValue().intValue());
    assertEquals(7, bvSignExtend.get(0).getIntegerValue().intValue());
    assertEquals(8, bvRotateLeft.get(0).getIntegerValue().intValue());
    assertEquals(9, bvRotateRight.get(0).getIntegerValue().intValue());
    assertEquals(10, intToBv.get(0).getIntegerValue().intValue());
    assertEquals(11, iand.get(0).getIntegerValue().intValue());
    assertEquals(12, fpToUbv.get(0).getIntegerValue().intValue());
    assertEquals(13, fpToSbv.get(0).getIntegerValue().intValue());
    assertEquals(14, regexpRepeat.get(0).getIntegerValue().intValue());

    // Operators with 2 indices
    Op bvExtract = d_solver.mkOp(BITVECTOR_EXTRACT, 1, 0);
    Op toFpFromIeeeBv = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_IEEE_BV, 3, 2);
    Op toFpFromFp = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_FP, 5, 4);
    Op toFpFromReal = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_REAL, 7, 6);
    Op toFpFromSbv = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_SBV, 9, 8);
    Op toFpFromUbv = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_UBV, 11, 10);
    Op regexpLoop = d_solver.mkOp(REGEXP_LOOP, 15, 14);

    assertEquals(1, bvExtract.get(0).getIntegerValue().intValue());
    assertEquals(0, bvExtract.get(1).getIntegerValue().intValue());
    assertEquals(3, toFpFromIeeeBv.get(0).getIntegerValue().intValue());
    assertEquals(2, toFpFromIeeeBv.get(1).getIntegerValue().intValue());
    assertEquals(5, toFpFromFp.get(0).getIntegerValue().intValue());
    assertEquals(4, toFpFromFp.get(1).getIntegerValue().intValue());
    assertEquals(7, toFpFromReal.get(0).getIntegerValue().intValue());
    assertEquals(6, toFpFromReal.get(1).getIntegerValue().intValue());
    assertEquals(9, toFpFromSbv.get(0).getIntegerValue().intValue());
    assertEquals(8, toFpFromSbv.get(1).getIntegerValue().intValue());
    assertEquals(11, toFpFromUbv.get(0).getIntegerValue().intValue());
    assertEquals(10, toFpFromUbv.get(1).getIntegerValue().intValue());
    assertEquals(15, regexpLoop.get(0).getIntegerValue().intValue());
    assertEquals(14, regexpLoop.get(1).getIntegerValue().intValue());

    // Operators with n indices
    int[] indices = {0, 3, 2, 0, 1, 2};
    Op tupleProject = d_solver.mkOp(TUPLE_PROJECT, indices);
    for (int i = 0, size = tupleProject.getNumIndices(); i < size; i++)
    {
      assertEquals(indices[i], tupleProject.get(i).getIntegerValue().intValue());
    }
  }

  @Test
  void opScopingToString() throws CVC5ApiException
  {
    Op bitvector_repeat_ot = d_solver.mkOp(BITVECTOR_REPEAT, 5);
    String op_repr = bitvector_repeat_ot.toString();

    Solver solver2;
    assertEquals(bitvector_repeat_ot.toString(), op_repr);
  }
}
