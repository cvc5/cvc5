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

  @Test void getIndicesString() throws CVC5ApiException
  {
    Op x = d_solver.getNullOp();
    assertThrows(CVC5ApiException.class, () -> x.getStringIndices());

    Op divisible_ot = d_solver.mkOp(DIVISIBLE, 4);
    assertTrue(divisible_ot.isIndexed());
    String divisible_idx = divisible_ot.getStringIndices()[0];
    assertEquals(divisible_idx, "4");
  }

  @Test void getIndicesUint() throws CVC5ApiException
  {
    Op bitvector_repeat_ot = d_solver.mkOp(BITVECTOR_REPEAT, 5);
    assertTrue(bitvector_repeat_ot.isIndexed());
    int bitvector_repeat_idx = bitvector_repeat_ot.getIntegerIndices()[0];
    assertEquals(bitvector_repeat_idx, 5);

    // unlike bitvector_repeat_ot.getIndices<std::pair<uint32_t, uint32_t>>() in
    // c++, this does not throw in Java
    // assertThrows(CVC5ApiException.class,
    //              () -> bitvector_repeat_ot.getIntegerIndices());

    Op bitvector_zero_extend_ot = d_solver.mkOp(BITVECTOR_ZERO_EXTEND, 6);
    int bitvector_zero_extend_idx = bitvector_zero_extend_ot.getIntegerIndices()[0];
    assertEquals(bitvector_zero_extend_idx, 6);

    Op bitvector_sign_extend_ot = d_solver.mkOp(BITVECTOR_SIGN_EXTEND, 7);
    int bitvector_sign_extend_idx = bitvector_sign_extend_ot.getIntegerIndices()[0];
    assertEquals(bitvector_sign_extend_idx, 7);

    Op bitvector_rotate_left_ot = d_solver.mkOp(BITVECTOR_ROTATE_LEFT, 8);
    int bitvector_rotate_left_idx = bitvector_rotate_left_ot.getIntegerIndices()[0];
    assertEquals(bitvector_rotate_left_idx, 8);

    Op bitvector_rotate_right_ot = d_solver.mkOp(BITVECTOR_ROTATE_RIGHT, 9);
    int bitvector_rotate_right_idx = bitvector_rotate_right_ot.getIntegerIndices()[0];
    assertEquals(bitvector_rotate_right_idx, 9);

    Op int_to_bitvector_ot = d_solver.mkOp(INT_TO_BITVECTOR, 10);
    int int_to_bitvector_idx = int_to_bitvector_ot.getIntegerIndices()[0];
    assertEquals(int_to_bitvector_idx, 10);

    Op floatingpoint_to_ubv_ot = d_solver.mkOp(FLOATINGPOINT_TO_UBV, 11);
    int floatingpoint_to_ubv_idx = floatingpoint_to_ubv_ot.getIntegerIndices()[0];
    assertEquals(floatingpoint_to_ubv_idx, 11);

    Op floatingpoint_to_sbv_ot = d_solver.mkOp(FLOATINGPOINT_TO_SBV, 13);
    int floatingpoint_to_sbv_idx = floatingpoint_to_sbv_ot.getIntegerIndices()[0];
    assertEquals(floatingpoint_to_sbv_idx, 13);
  }

  @Test void getIndicesPairUint() throws CVC5ApiException
  {
    Op bitvector_extract_ot = d_solver.mkOp(BITVECTOR_EXTRACT, 4, 0);
    assertTrue(bitvector_extract_ot.isIndexed());
    int[] bitvector_extract_indices = bitvector_extract_ot.getIntegerIndices();
    assertArrayEquals(bitvector_extract_indices, new int[] {4, 0});

    Op floatingpoint_to_fp_ieee_bitvector_ot =
        d_solver.mkOp(FLOATINGPOINT_TO_FP_IEEE_BITVECTOR, 4, 25);
    int[] floatingpoint_to_fp_ieee_bitvector_indices =
        floatingpoint_to_fp_ieee_bitvector_ot.getIntegerIndices();
    assertArrayEquals(floatingpoint_to_fp_ieee_bitvector_indices, new int[] {4, 25});

    Op floatingpoint_to_fp_floatingpoint_ot =
        d_solver.mkOp(FLOATINGPOINT_TO_FP_FLOATINGPOINT, 4, 25);
    int[] floatingpoint_to_fp_floatingpoint_indices =
        floatingpoint_to_fp_floatingpoint_ot.getIntegerIndices();
    assertArrayEquals(floatingpoint_to_fp_floatingpoint_indices, new int[] {4, 25});

    Op floatingpoint_to_fp_real_ot = d_solver.mkOp(FLOATINGPOINT_TO_FP_REAL, 4, 25);
    int[] floatingpoint_to_fp_real_indices = floatingpoint_to_fp_real_ot.getIntegerIndices();
    assertArrayEquals(floatingpoint_to_fp_real_indices, new int[] {4, 25});

    Op floatingpoint_to_fp_signed_bitvector_ot =
        d_solver.mkOp(FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR, 4, 25);
    int[] floatingpoint_to_fp_signed_bitvector_indices =
        floatingpoint_to_fp_signed_bitvector_ot.getIntegerIndices();
    assertArrayEquals(floatingpoint_to_fp_signed_bitvector_indices, new int[] {4, 25});

    Op floatingpoint_to_fp_unsigned_bitvector_ot =
        d_solver.mkOp(FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR, 4, 25);
    int[] floatingpoint_to_fp_unsigned_bitvector_indices =
        floatingpoint_to_fp_unsigned_bitvector_ot.getIntegerIndices();
    assertArrayEquals(floatingpoint_to_fp_unsigned_bitvector_indices, new int[] {4, 25});

    Op floatingpoint_to_fp_generic_ot = d_solver.mkOp(FLOATINGPOINT_TO_FP_GENERIC, 4, 25);
    int[] floatingpoint_to_fp_generic_indices = floatingpoint_to_fp_generic_ot.getIntegerIndices();
    assertArrayEquals(floatingpoint_to_fp_generic_indices, new int[] {4, 25});
    assertThrows(CVC5ApiException.class, () -> floatingpoint_to_fp_generic_ot.getStringIndices());
  }

  @Test void opScopingToString() throws CVC5ApiException
  {
    Op bitvector_repeat_ot = d_solver.mkOp(BITVECTOR_REPEAT, 5);
    String op_repr = bitvector_repeat_ot.toString();

    Solver solver2;
    assertEquals(bitvector_repeat_ot.toString(), op_repr);
  }
}
