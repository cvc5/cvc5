###############################################################################
# Top contributors (to current version):
#   Yoni Zohar
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Unit tests for op API.
#
# Obtained by translating test/unit/api/op_black.cpp
##

import pytest
import pycvc5
from pycvc5 import kinds
from pycvc5 import Sort


@pytest.fixture
def solver():
    return pycvc5.Solver()


def test_get_kind(solver):
  x = d_solver.mkOp(kinds.BVExtract, 31, 1)
  x.getKind()


def test_is_null(solver):
  assert x.isNull()
  x = d_solver.mkOp(kinds.BVExtract, 31, 1)
  assert not x.isNull()


def test_op_from_kind(solver):
  d_solver.mkOp(PLUS)
  with pytest.raises(RuntimeError):
      d_solver.mkOp(kinds.BVExtract)


def test_get_num_indices(solver):
  plus = d_solver.mkOp(PLUS)
  divisible = d_solver.mkOp(DIVISIBLE, 4)
  bitvector_repeat = d_solver.mkOp(BITVECTOR_REPEAT, 5)
  bitvector_zero_extend = d_solver.mkOp(BITVECTOR_ZERO_EXTEND, 6)
  bitvector_sign_extend = d_solver.mkOp(BITVECTOR_SIGN_EXTEND, 7)
  bitvector_rotate_left = d_solver.mkOp(BITVECTOR_ROTATE_LEFT, 8)
  bitvector_rotate_right = d_solver.mkOp(BITVECTOR_ROTATE_RIGHT, 9)
  int_to_bitvector = d_solver.mkOp(INT_TO_BITVECTOR, 10)
  iand = d_solver.mkOp(IAND, 3)
  floatingpoint_to_ubv = d_solver.mkOp(FLOATINGPOINT_TO_UBV, 11)
  floatingopint_to_sbv = d_solver.mkOp(FLOATINGPOINT_TO_SBV, 13)
  floatingpoint_to_fp_ieee_bitvector =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_IEEE_BITVECTOR, 4, 25)
  floatingpoint_to_fp_floatingpoint =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_FLOATINGPOINT, 4, 25)
  floatingpoint_to_fp_real = d_solver.mkOp(FLOATINGPOINT_TO_FP_REAL, 4, 25)
  floatingpoint_to_fp_signed_bitvector =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR, 4, 25)
  floatingpoint_to_fp_unsigned_bitvector =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR, 4, 25)
  floatingpoint_to_fp_generic =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_GENERIC, 4, 25)
  regexp_loop = d_solver.mkOp(REGEXP_LOOP, 2, 3)

  assert 0 == plus.getNumIndices()
  assert 1 == divisible.getNumIndices()
  assert 1 == bitvector_repeat.getNumIndices()
  assert 1 == bitvector_zero_extend.getNumIndices()
  assert 1 == bitvector_sign_extend.getNumIndices()
  assert 1 == bitvector_rotate_left.getNumIndices()
  assert 1 == bitvector_rotate_right.getNumIndices()
  assert 1 == int_to_bitvector.getNumIndices()
  assert 1 == iand.getNumIndices()
  assert 1 == floatingpoint_to_ubv.getNumIndices()
  assert 1 == floatingopint_to_sbv.getNumIndices()
  assert 2 == floatingpoint_to_fp_ieee_bitvector.getNumIndices()
  assert 2 == floatingpoint_to_fp_floatingpoint.getNumIndices()
  assert 2 == floatingpoint_to_fp_real.getNumIndices()
  assert 2 == floatingpoint_to_fp_signed_bitvector.getNumIndices()
  assert 2 == floatingpoint_to_fp_unsigned_bitvector.getNumIndices()
  assert 2 == floatingpoint_to_fp_generic.getNumIndices()
  assert 2 == regexp_loop.getNumIndices()


def test_get_indices_string(solver):
  x = Op(solver)
  with pytest.raises(RuntimeError):
      x.getIndices[string]()

  divisible_ot = d_solver.mkOp(DIVISIBLE, 4)
  assert divisible_ot.isIndexed()
  std::string divisible_idx = divisible_ot.getIndices[string]()
  assert divisible_idx == "4"


def test_get_indices_uint(solver):
  bitvector_repeat_ot = d_solver.mkOp(BITVECTOR_REPEAT, 5)
  assert bitvector_repeat_ot.isIndexed()
  uint32_t bitvector_repeat_idx = bitvector_repeat_ot.getIndices<uint32_t>()
  assert bitvector_repeat_idx == 5
  with pytest.raises(RuntimeError):
      bitvector_repeat_ot.getIndices<std::pair<uint32_t, uint32_t>>()

  bitvector_zero_extend_ot = d_solver.mkOp(BITVECTOR_ZERO_EXTEND, 6)
  uint32_t bitvector_zero_extend_idx =
      bitvector_zero_extend_ot.getIndices<uint32_t>()
  assert bitvector_zero_extend_idx == 6

  bitvector_sign_extend_ot = d_solver.mkOp(BITVECTOR_SIGN_EXTEND, 7)
  uint32_t bitvector_sign_extend_idx =
      bitvector_sign_extend_ot.getIndices<uint32_t>()
  assert bitvector_sign_extend_idx == 7

  bitvector_rotate_left_ot = d_solver.mkOp(BITVECTOR_ROTATE_LEFT, 8)
  uint32_t bitvector_rotate_left_idx =
      bitvector_rotate_left_ot.getIndices<uint32_t>()
  assert bitvector_rotate_left_idx == 8

  bitvector_rotate_right_ot = d_solver.mkOp(BITVECTOR_ROTATE_RIGHT, 9)
  uint32_t bitvector_rotate_right_idx =
      bitvector_rotate_right_ot.getIndices<uint32_t>()
  assert bitvector_rotate_right_idx == 9

  int_to_bitvector_ot = d_solver.mkOp(INT_TO_BITVECTOR, 10)
  uint32_t int_to_bitvector_idx = int_to_bitvector_ot.getIndices<uint32_t>()
  assert int_to_bitvector_idx == 10

  floatingpoint_to_ubv_ot = d_solver.mkOp(FLOATINGPOINT_TO_UBV, 11)
  uint32_t floatingpoint_to_ubv_idx =
      floatingpoint_to_ubv_ot.getIndices<uint32_t>()
  assert floatingpoint_to_ubv_idx == 11

  floatingpoint_to_sbv_ot = d_solver.mkOp(FLOATINGPOINT_TO_SBV, 13)
  uint32_t floatingpoint_to_sbv_idx =
      floatingpoint_to_sbv_ot.getIndices<uint32_t>()
  assert floatingpoint_to_sbv_idx == 13


def test_get_indices_pair_uint(solver):
  bitvector_extract_ot = d_solver.mkOp(kinds.BVExtract, 4, 0)
  assert bitvector_extract_ot.isIndexed()
  std::pair<uint32_t, uint32_t> bitvector_extract_indices =
      bitvector_extract_ot.getIndices<std::pair<uint32_t, uint32_t>>()
  assert bitvector_extract_indices == std::pair<uint32_t, uint32_t>{4, 0}

  floatingpoint_to_fp_ieee_bitvector_ot =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_IEEE_BITVECTOR, 4, 25)
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_ieee_bitvector_indices =
      floatingpoint_to_fp_ieee_bitvector_ot
          .getIndices<std::pair<uint32_t, uint32_t>>()
  assert floatingpoint_to_fp_ieee_bitvector_indices
               == std::pair<uint32_t, uint32_t>{4, 25}

  floatingpoint_to_fp_floatingpoint_ot =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_FLOATINGPOINT, 4, 25)
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_floatingpoint_indices =
      floatingpoint_to_fp_floatingpoint_ot
          .getIndices<std::pair<uint32_t, uint32_t>>()
  assert floatingpoint_to_fp_floatingpoint_indices
               == std::pair<uint32_t, uint32_t>{4, 25}

  floatingpoint_to_fp_real_ot =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_REAL, 4, 25)
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_real_indices =
      floatingpoint_to_fp_real_ot.getIndices<std::pair<uint32_t, uint32_t>>()
  assert floatingpoint_to_fp_real_indices
               == std::pair<uint32_t, uint32_t>{4, 25}

  floatingpoint_to_fp_signed_bitvector_ot =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR, 4, 25)
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_signed_bitvector_indices =
      floatingpoint_to_fp_signed_bitvector_ot
          .getIndices<std::pair<uint32_t, uint32_t>>()
  assert floatingpoint_to_fp_signed_bitvector_indices
               == std::pair<uint32_t, uint32_t>{4, 25}

  floatingpoint_to_fp_unsigned_bitvector_ot =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR, 4, 25)
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_unsigned_bitvector_indices =
      floatingpoint_to_fp_unsigned_bitvector_ot
          .getIndices<std::pair<uint32_t, uint32_t>>()
  assert floatingpoint_to_fp_unsigned_bitvector_indices
               == std::pair<uint32_t, uint32_t>{4, 25}

  floatingpoint_to_fp_generic_ot =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_GENERIC, 4, 25)
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_generic_indices =
      floatingpoint_to_fp_generic_ot
          .getIndices<std::pair<uint32_t, uint32_t>>()
  assert floatingpoint_to_fp_generic_indices
               == std::pair<uint32_t, uint32_t>{4, 25}
  with pytest.raises(RuntimeError):
      floatingpoint_to_fp_generic_ot.getIndices[string]()


def test_op_scoping_to_string(solver):
  bitvector_repeat_ot = d_solver.mkOp(BITVECTOR_REPEAT, 5)
  std::string op_repr = bitvector_repeat_ot.toString()
  assert bitvector_repeat_ot.toString() == op_repr

