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
from pycvc5 import Op


@pytest.fixture
def solver():
    return pycvc5.Solver()


def test_get_kind(solver):
    x = solver.mkOp(kinds.BVExtract, 31, 1)
    x.getKind()


def test_is_null(solver):
    x = Op(solver)
    assert x.isNull()
    x = solver.mkOp(kinds.BVExtract, 31, 1)
    assert not x.isNull()


def test_op_from_kind(solver):
    solver.mkOp(kinds.Plus)
    with pytest.raises(RuntimeError):
        solver.mkOp(kinds.BVExtract)


def test_get_num_indices(solver):
    plus = solver.mkOp(kinds.Plus)
    divisible = solver.mkOp(kinds.Divisible, 4)
    bitvector_repeat = solver.mkOp(kinds.BVRepeat, 5)
    bitvector_zero_extend = solver.mkOp(kinds.BVZeroExtend, 6)
    bitvector_sign_extend = solver.mkOp(kinds.BVSignExtend, 7)
    bitvector_rotate_left = solver.mkOp(kinds.BVRotateLeft, 8)
    bitvector_rotate_right = solver.mkOp(kinds.BVRotateRight, 9)
    int_to_bitvector = solver.mkOp(kinds.IntToBV, 10)
    iand = solver.mkOp(kinds.Iand, 3)
    floatingpoint_to_ubv = solver.mkOp(kinds.FPToUbv, 11)
    floatingopint_to_sbv = solver.mkOp(kinds.FPToSbv, 13)
    floatingpoint_to_fp_ieee_bitvector = solver.mkOp(kinds.FPToFpIeeeBV, 4, 25)
    floatingpoint_to_fp_floatingpoint = solver.mkOp(kinds.FPToFpFP, 4, 25)
    floatingpoint_to_fp_real = solver.mkOp(kinds.FPToFpReal, 4, 25)
    floatingpoint_to_fp_signed_bitvector = solver.mkOp(kinds.FPToFpSignedBV, 4,
                                                       25)
    floatingpoint_to_fp_unsigned_bitvector = solver.mkOp(
        kinds.FPToFpUnsignedBV, 4, 25)
    floatingpoint_to_fp_generic = solver.mkOp(kinds.FPToFpGeneric, 4, 25)
    regexp_loop = solver.mkOp(kinds.RegexpLoop, 2, 3)

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

def test_op_indices_list(solver):
    with_list = solver.mkOp(kinds.TupleProject, [4, 25])
    assert 2 == with_list.getNumIndices()

def test_get_indices_string(solver):
    x = Op(solver)
    with pytest.raises(RuntimeError):
        x.getIndices()

    divisible_ot = solver.mkOp(kinds.Divisible, 4)
    assert divisible_ot.isIndexed()
    divisible_idx = divisible_ot.getIndices()
    assert divisible_idx == "4"


def test_get_indices_uint(solver):
    bitvector_repeat_ot = solver.mkOp(kinds.BVRepeat, 5)
    assert bitvector_repeat_ot.isIndexed()
    bitvector_repeat_idx = bitvector_repeat_ot.getIndices()
    assert bitvector_repeat_idx == 5

    bitvector_zero_extend_ot = solver.mkOp(kinds.BVZeroExtend, 6)
    bitvector_zero_extend_idx = bitvector_zero_extend_ot.getIndices()
    assert bitvector_zero_extend_idx == 6

    bitvector_sign_extend_ot = solver.mkOp(kinds.BVSignExtend, 7)
    bitvector_sign_extend_idx = bitvector_sign_extend_ot.getIndices()
    assert bitvector_sign_extend_idx == 7

    bitvector_rotate_left_ot = solver.mkOp(kinds.BVRotateLeft, 8)
    bitvector_rotate_left_idx = bitvector_rotate_left_ot.getIndices()
    assert bitvector_rotate_left_idx == 8

    bitvector_rotate_right_ot = solver.mkOp(kinds.BVRotateRight, 9)
    bitvector_rotate_right_idx = bitvector_rotate_right_ot.getIndices()
    assert bitvector_rotate_right_idx == 9

    int_to_bitvector_ot = solver.mkOp(kinds.IntToBV, 10)
    int_to_bitvector_idx = int_to_bitvector_ot.getIndices()
    assert int_to_bitvector_idx == 10

    floatingpoint_to_ubv_ot = solver.mkOp(kinds.FPToUbv, 11)
    floatingpoint_to_ubv_idx = floatingpoint_to_ubv_ot.getIndices()
    assert floatingpoint_to_ubv_idx == 11

    floatingpoint_to_sbv_ot = solver.mkOp(kinds.FPToSbv, 13)
    floatingpoint_to_sbv_idx = floatingpoint_to_sbv_ot.getIndices()
    assert floatingpoint_to_sbv_idx == 13


def test_get_indices_pair_uint(solver):
    bitvector_extract_ot = solver.mkOp(kinds.BVExtract, 4, 0)
    assert bitvector_extract_ot.isIndexed()
    bitvector_extract_indices = bitvector_extract_ot.getIndices()
    assert bitvector_extract_indices == (4, 0)

    floatingpoint_to_fp_ieee_bitvector_ot = solver.mkOp(
        kinds.FPToFpIeeeBV, 4, 25)
    floatingpoint_to_fp_ieee_bitvector_indices = floatingpoint_to_fp_ieee_bitvector_ot.getIndices(
    )
    assert floatingpoint_to_fp_ieee_bitvector_indices == (4, 25)

    floatingpoint_to_fp_floatingpoint_ot = solver.mkOp(kinds.FPToFpFP, 4, 25)
    floatingpoint_to_fp_floatingpoint_indices = floatingpoint_to_fp_floatingpoint_ot.getIndices(
    )
    assert floatingpoint_to_fp_floatingpoint_indices == (4, 25)

    floatingpoint_to_fp_real_ot = solver.mkOp(kinds.FPToFpReal, 4, 25)
    floatingpoint_to_fp_real_indices = floatingpoint_to_fp_real_ot.getIndices()
    assert floatingpoint_to_fp_real_indices == (4, 25)

    floatingpoint_to_fp_signed_bitvector_ot = solver.mkOp(
        kinds.FPToFpSignedBV, 4, 25)
    floatingpoint_to_fp_signed_bitvector_indices = floatingpoint_to_fp_signed_bitvector_ot.getIndices(
    )
    assert floatingpoint_to_fp_signed_bitvector_indices == (4, 25)

    floatingpoint_to_fp_unsigned_bitvector_ot = solver.mkOp(
        kinds.FPToFpUnsignedBV, 4, 25)
    floatingpoint_to_fp_unsigned_bitvector_indices = floatingpoint_to_fp_unsigned_bitvector_ot.getIndices(
    )
    assert floatingpoint_to_fp_unsigned_bitvector_indices == (4, 25)

    floatingpoint_to_fp_generic_ot = solver.mkOp(kinds.FPToFpGeneric, 4, 25)
    floatingpoint_to_fp_generic_indices = floatingpoint_to_fp_generic_ot.getIndices(
    )
    assert floatingpoint_to_fp_generic_indices == (4, 25)


def test_op_scoping_to_string(solver):
    bitvector_repeat_ot = solver.mkOp(kinds.BVRepeat, 5)
    op_repr = str(bitvector_repeat_ot)
    assert str(bitvector_repeat_ot) == op_repr
