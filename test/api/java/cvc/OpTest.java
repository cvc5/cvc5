package cvc;

import static cvc.Kind.*;
import static org.junit.jupiter.api.Assertions.*;

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
    //    d_solver.deletePointer();
  }

  @Test void getKind() throws CVCApiException
  {
    Op x = d_solver.mkOp(BITVECTOR_EXTRACT, 31, 1);
    assertDoesNotThrow(() -> x.getKind());
  }

  @Test void isNull() throws CVCApiException
  {
    Op x = d_solver.mkOp();
    assertTrue(x.isNull());
    x = d_solver.mkOp(BITVECTOR_EXTRACT, 31, 1);
    assertFalse(x.isNull());
  }

  @Test void opFromKind()
  {
    Op plus = d_solver.mkOp(PLUS);
    assertFalse(plus.isIndexed());
    assertThrows(CVCApiException.class, () -> plus.getIntegerIndex());

    assertDoesNotThrow(() -> d_solver.mkOp(PLUS));
    assertEquals(plus, d_solver.mkOp(PLUS));
    assertThrows(CVCApiException.class, () -> d_solver.mkOp(BITVECTOR_EXTRACT));
  }

  @Test void getIndicesString() throws CVCApiException
  {
    Op x = d_solver.mkOp();
    assertThrows(CVCApiException.class, () -> x.getStringIndices());

    Op divisible_ot = d_solver.mkOp(DIVISIBLE, 4);
    assertTrue(divisible_ot.isIndexed());
    String divisible_idx = divisible_ot.getStringIndices();
    assertEquals(divisible_idx, "4");

    Op record_update_ot = d_solver.mkOp(RECORD_UPDATE, "test");
    String record_update_idx = record_update_ot.getStringIndices();
    assertEquals(record_update_idx, "test");
    assertThrows(CVCApiException.class, () -> record_update_ot.getIntegerIndex());
  }

  @Test void getIndicesUint() throws CVCApiException
  {
    Op bitvector_repeat_ot = d_solver.mkOp(BITVECTOR_REPEAT, 5);
    assertTrue(bitvector_repeat_ot.isIndexed());
    int bitvector_repeat_idx = bitvector_repeat_ot.getIntegerIndex();
    assertEquals(bitvector_repeat_idx, 5);

    assertThrows(CVCApiException.class, () -> bitvector_repeat_ot.getIntegerPairIndices());

    Op bitvector_zero_extend_ot = d_solver.mkOp(BITVECTOR_ZERO_EXTEND, 6);
    int bitvector_zero_extend_idx = bitvector_zero_extend_ot.getIntegerIndex();
    assertEquals(bitvector_zero_extend_idx, 6);

    Op bitvector_sign_extend_ot = d_solver.mkOp(BITVECTOR_SIGN_EXTEND, 7);
    int bitvector_sign_extend_idx = bitvector_sign_extend_ot.getIntegerIndex();
    assertEquals(bitvector_sign_extend_idx, 7);

    Op bitvector_rotate_left_ot = d_solver.mkOp(BITVECTOR_ROTATE_LEFT, 8);
    int bitvector_rotate_left_idx = bitvector_rotate_left_ot.getIntegerIndex();
    assertEquals(bitvector_rotate_left_idx, 8);

    Op bitvector_rotate_right_ot = d_solver.mkOp(BITVECTOR_ROTATE_RIGHT, 9);
    int bitvector_rotate_right_idx = bitvector_rotate_right_ot.getIntegerIndex();
    assertEquals(bitvector_rotate_right_idx, 9);

    Op int_to_bitvector_ot = d_solver.mkOp(INT_TO_BITVECTOR, 10);
    int int_to_bitvector_idx = int_to_bitvector_ot.getIntegerIndex();
    assertEquals(int_to_bitvector_idx, 10);

    Op floatingpoint_to_ubv_ot = d_solver.mkOp(FLOATINGPOINT_TO_UBV, 11);
    int floatingpoint_to_ubv_idx = floatingpoint_to_ubv_ot.getIntegerIndex();
    assertEquals(floatingpoint_to_ubv_idx, 11);

    Op floatingpoint_to_sbv_ot = d_solver.mkOp(FLOATINGPOINT_TO_SBV, 13);
    int floatingpoint_to_sbv_idx = floatingpoint_to_sbv_ot.getIntegerIndex();
    assertEquals(floatingpoint_to_sbv_idx, 13);

    Op tuple_update_ot = d_solver.mkOp(TUPLE_UPDATE, 5);
    int tuple_update_idx = tuple_update_ot.getIntegerIndex();
    assertEquals(tuple_update_idx, 5);
    assertThrows(CVCApiException.class, () -> tuple_update_ot.getStringIndices());
  }

  @Test void getIndicesPairUint() throws CVCApiException
  {
    Op bitvector_extract_ot = d_solver.mkOp(BITVECTOR_EXTRACT, 4, 0);
    assertTrue(bitvector_extract_ot.isIndexed());
    Pair<Integer, Integer> bitvector_extract_indices = bitvector_extract_ot.getIntegerPairIndices();
    assertTrue((bitvector_extract_indices.equals(new Pair<Integer, Integer>(4, 0))));

    Op floatingpoint_to_fp_ieee_bitvector_ot =
        d_solver.mkOp(FLOATINGPOINT_TO_FP_IEEE_BITVECTOR, 4, 25);
    Pair<Integer, Integer> floatingpoint_to_fp_ieee_bitvector_indices =
        floatingpoint_to_fp_ieee_bitvector_ot.getIntegerPairIndices();
    assertTrue(
        floatingpoint_to_fp_ieee_bitvector_indices.equals(new Pair<Integer, Integer>(4, 25)));

    Op floatingpoint_to_fp_floatingpoint_ot =
        d_solver.mkOp(FLOATINGPOINT_TO_FP_FLOATINGPOINT, 4, 25);
    Pair<Integer, Integer> floatingpoint_to_fp_floatingpoint_indices =
        floatingpoint_to_fp_floatingpoint_ot.getIntegerPairIndices();
    assertTrue(floatingpoint_to_fp_floatingpoint_indices.equals(new Pair<Integer, Integer>(4, 25)));

    Op floatingpoint_to_fp_real_ot = d_solver.mkOp(FLOATINGPOINT_TO_FP_REAL, 4, 25);
    Pair<Integer, Integer> floatingpoint_to_fp_real_indices =
        floatingpoint_to_fp_real_ot.getIntegerPairIndices();
    assertTrue(floatingpoint_to_fp_real_indices.equals(new Pair<Integer, Integer>(4, 25)));

    Op floatingpoint_to_fp_signed_bitvector_ot =
        d_solver.mkOp(FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR, 4, 25);
    Pair<Integer, Integer> floatingpoint_to_fp_signed_bitvector_indices =
        floatingpoint_to_fp_signed_bitvector_ot.getIntegerPairIndices();
    assertTrue(
        floatingpoint_to_fp_signed_bitvector_indices.equals(new Pair<Integer, Integer>(4, 25)));

    Op floatingpoint_to_fp_unsigned_bitvector_ot =
        d_solver.mkOp(FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR, 4, 25);
    Pair<Integer, Integer> floatingpoint_to_fp_unsigned_bitvector_indices =
        floatingpoint_to_fp_unsigned_bitvector_ot.getIntegerPairIndices();
    assertTrue(
        floatingpoint_to_fp_unsigned_bitvector_indices.equals(new Pair<Integer, Integer>(4, 25)));

    Op floatingpoint_to_fp_generic_ot = d_solver.mkOp(FLOATINGPOINT_TO_FP_GENERIC, 4, 25);
    Pair<Integer, Integer> floatingpoint_to_fp_generic_indices =
        floatingpoint_to_fp_generic_ot.getIntegerPairIndices();
    assertTrue(floatingpoint_to_fp_generic_indices.equals(new Pair<Integer, Integer>(4, 25)));
    assertThrows(CVCApiException.class, () -> floatingpoint_to_fp_generic_ot.getStringIndices());
  }

  @Test void opScopingToString() throws CVCApiException
  {
    Op bitvector_repeat_ot = d_solver.mkOp(BITVECTOR_REPEAT, 5);
    String op_repr = bitvector_repeat_ot.toString();
    Solver solver2;
    assertEquals(bitvector_repeat_ot.toString(), op_repr);
  }
}