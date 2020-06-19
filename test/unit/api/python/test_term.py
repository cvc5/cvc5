import pytest

import pycvc4
from pycvc4 import kinds


def test_get_kind():
    solver = pycvc4.Solver()
    intsort = solver.getIntegerSort()
    x = solver.mkConst(intsort, 'x')
    y = solver.mkConst(intsort, 'y')
    xpy = solver.mkTerm(kinds.Plus, x, y)
    assert xpy.getKind() == kinds.Plus

    funsort = solver.mkFunctionSort(intsort, intsort)
    f = solver.mkConst(funsort, 'f')
    assert f.getKind() == kinds.Constant

    fx = solver.mkTerm(kinds.ApplyUf, f, x)
    assert fx.getKind() == kinds.ApplyUf


def test_eq():
    solver = pycvc4.Solver()
    usort = solver.mkUninterpretedSort('u')
    x = solver.mkConst(usort, 'x')
    y = solver.mkConst(usort, 'y')
    z = x

    assert x == x
    assert x == z
    assert not (x != x)
    assert x != y
    assert y != z


def test_get_sort():
    solver = pycvc4.Solver()
    intsort = solver.getIntegerSort()
    bvsort8 = solver.mkBitVectorSort(8)

    x = solver.mkConst(intsort, 'x')
    y = solver.mkConst(intsort, 'y')

    a = solver.mkConst(bvsort8, 'a')
    b = solver.mkConst(bvsort8, 'b')

    assert x.getSort() == intsort
    assert solver.mkTerm(kinds.Plus, x, y).getSort() == intsort

    assert a.getSort() == bvsort8
    assert solver.mkTerm(kinds.BVConcat, a, b).getSort() == solver.mkBitVectorSort(16)

def test_get_op():
    solver = pycvc4.Solver()
    intsort = solver.getIntegerSort()
    funsort = solver.mkFunctionSort(intsort, intsort)

    x = solver.mkConst(intsort, 'x')
    f = solver.mkConst(funsort, 'f')

    fx = solver.mkTerm(kinds.ApplyUf, f, x)

    assert not x.hasOp()

    try:
        op = x.getOp()
        assert False
    except:
        assert True

    assert fx.hasOp()
    assert fx.getOp().getKind() == kinds.ApplyUf
    # equivalent check
    assert fx.getOp() == solver.mkOp(kinds.ApplyUf)


def test_is_const():
    solver = pycvc4.Solver()
    intsort = solver.getIntegerSort()
    one = solver.mkReal(1)
    x = solver.mkConst(intsort, 'x')
    xpone = solver.mkTerm(kinds.Plus, x, one)
    onepone = solver.mkTerm(kinds.Plus, one, one)
    assert not x.isConst()
    assert one.isConst()
    assert not xpone.isConst()
    assert not onepone.isConst()
