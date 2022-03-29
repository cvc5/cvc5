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
import cvc5
from cvc5 import Kind
from cvc5 import Sort
from cvc5 import Op


@pytest.fixture
def solver():
    return cvc5.Solver()


def test_get_kind(solver):
    x = solver.mkOp(Kind.BVExtract, 31, 1)
    x.getKind()


def test_is_null(solver):
    x = Op(solver)
    assert x.isNull()
    x = solver.mkOp(Kind.BVExtract, 31, 1)
    assert not x.isNull()


def test_op_from_kind(solver):
    solver.mkOp(Kind.Add)
    with pytest.raises(RuntimeError):
        solver.mkOp(Kind.BVExtract)


def test_get_num_indices(solver):
    # Operators with 0 indices
    plus = solver.mkOp(Kind.Add)

    assert 0 == plus.getNumIndices()

    # Operators with 1 index
    divisible = solver.mkOp(Kind.Divisible, 4)
    bitvector_repeat = solver.mkOp(Kind.BVRepeat, 5)
    bitvector_zero_extend = solver.mkOp(Kind.BVZeroExtend, 6)
    bitvector_sign_extend = solver.mkOp(Kind.BVSignExtend, 7)
    bitvector_rotate_left = solver.mkOp(Kind.BVRotateLeft, 8)
    bitvector_rotate_right = solver.mkOp(Kind.BVRotateRight, 9)
    int_to_bitvector = solver.mkOp(Kind.IntToBV, 10)
    iand = solver.mkOp(Kind.Iand, 3)
    floatingpoint_to_ubv = solver.mkOp(Kind.FPToUbv, 11)
    floatingopint_to_sbv = solver.mkOp(Kind.FPToSbv, 13)

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

    # Operators with 2 indices
    bitvector_extract = solver.mkOp(Kind.BVExtract, 4, 25)
    floatingpoint_to_fp_from_ieee_bv = solver.mkOp(Kind.FPToFpFromIeeeBv, 4,
                                                   25)
    floatingpoint_to_fp_from_fp = solver.mkOp(Kind.FPToFpFromFp, 4, 25)
    floatingpoint_to_fp_from_real = solver.mkOp(Kind.FPToFpFromReal, 4, 25)
    floatingpoint_to_fp_from_sbv = solver.mkOp(Kind.FPToFpFromSbv, 4, 25)
    floatingpoint_to_fp_from_ubv = solver.mkOp(Kind.FPToFpFromUbv, 4, 25)
    regexp_loop = solver.mkOp(Kind.RegexpLoop, 2, 3)

    assert 2 == bitvector_extract.getNumIndices()
    assert 2 == floatingpoint_to_fp_from_ieee_bv.getNumIndices()
    assert 2 == floatingpoint_to_fp_from_fp.getNumIndices()
    assert 2 == floatingpoint_to_fp_from_real.getNumIndices()
    assert 2 == floatingpoint_to_fp_from_sbv.getNumIndices()
    assert 2 == floatingpoint_to_fp_from_ubv.getNumIndices()
    assert 2 == regexp_loop.getNumIndices()

    # Operators with n indices
    indices = [0, 3, 2, 0, 1, 2]
    tuple_project_op = solver.mkOp(Kind.TupleProject, *indices)
    assert len(indices) == tuple_project_op.getNumIndices()


def test_subscript_operator(solver):
    # Operators with 0 indices
    plus = solver.mkOp(Kind.Add)

    with pytest.raises(RuntimeError):
        plus[0]

    # Operators with 1 index
    divisible = solver.mkOp(Kind.Divisible, 4)
    bitvector_repeat = solver.mkOp(Kind.BVRepeat, 5)
    bitvector_zero_extend = solver.mkOp(Kind.BVZeroExtend, 6)
    bitvector_sign_extend = solver.mkOp(Kind.BVSignExtend, 7)
    bitvector_rotate_left = solver.mkOp(Kind.BVRotateLeft, 8)
    bitvector_rotate_right = solver.mkOp(Kind.BVRotateRight, 9)
    int_to_bitvector = solver.mkOp(Kind.IntToBV, 10)
    iand = solver.mkOp(Kind.Iand, 11)
    floatingpoint_to_ubv = solver.mkOp(Kind.FPToUbv, 12)
    floatingopint_to_sbv = solver.mkOp(Kind.FPToSbv, 13)

    assert 4 == divisible[0].getIntegerValue()
    assert 5 == bitvector_repeat[0].getIntegerValue()
    assert 6 == bitvector_zero_extend[0].getIntegerValue()
    assert 7 == bitvector_sign_extend[0].getIntegerValue()
    assert 8 == bitvector_rotate_left[0].getIntegerValue()
    assert 9 == bitvector_rotate_right[0].getIntegerValue()
    assert 10 == int_to_bitvector[0].getIntegerValue()
    assert 11 == iand[0].getIntegerValue()
    assert 12 == floatingpoint_to_ubv[0].getIntegerValue()
    assert 13 == floatingopint_to_sbv[0].getIntegerValue()

    # Operators with 2 indices
    bitvector_extract = solver.mkOp(Kind.BVExtract, 1, 0)
    floatingpoint_to_fp_from_ieee_bv = solver.mkOp(Kind.FPToFpFromIeeeBv, 3, 2)
    floatingpoint_to_fp_from_fp = solver.mkOp(Kind.FPToFpFromFp, 5, 4)
    floatingpoint_to_fp_from_real = solver.mkOp(Kind.FPToFpFromReal, 7, 6)
    floatingpoint_to_fp_from_sbv = solver.mkOp(Kind.FPToFpFromSbv, 9, 8)
    floatingpoint_to_fp_from_ubv = solver.mkOp(Kind.FPToFpFromUbv, 11, 10)
    regexp_loop = solver.mkOp(Kind.RegexpLoop, 15, 14)

    assert 1 == bitvector_extract[0].getIntegerValue()
    assert 0 == bitvector_extract[1].getIntegerValue()
    assert 3 == floatingpoint_to_fp_from_ieee_bv[0].getIntegerValue()
    assert 2 == floatingpoint_to_fp_from_ieee_bv[1].getIntegerValue()
    assert 5 == floatingpoint_to_fp_from_fp[0].getIntegerValue()
    assert 4 == floatingpoint_to_fp_from_fp[1].getIntegerValue()
    assert 7 == floatingpoint_to_fp_from_real[0].getIntegerValue()
    assert 6 == floatingpoint_to_fp_from_real[1].getIntegerValue()
    assert 9 == floatingpoint_to_fp_from_sbv[0].getIntegerValue()
    assert 8 == floatingpoint_to_fp_from_sbv[1].getIntegerValue()
    assert 11 == floatingpoint_to_fp_from_ubv[0].getIntegerValue()
    assert 10 == floatingpoint_to_fp_from_ubv[1].getIntegerValue()
    assert 15 == regexp_loop[0].getIntegerValue()
    assert 14 == regexp_loop[1].getIntegerValue()

    # Operators with n indices
    indices = [0, 3, 2, 0, 1, 2]
    tuple_project_op = solver.mkOp(Kind.TupleProject, *indices)
    for i in range(len(indices)):
        assert indices[i] == tuple_project_op[i].getIntegerValue()


def test_op_scoping_to_string(solver):
    bitvector_repeat_ot = solver.mkOp(Kind.BVRepeat, 5)
    op_repr = str(bitvector_repeat_ot)
    assert str(bitvector_repeat_ot) == op_repr
