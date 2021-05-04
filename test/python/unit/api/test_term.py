###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Makai Mann, Andres Noetzli
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##



import pytest
import pycvc5
from pycvc5 import kinds
from pycvc5 import Sort, Term

@pytest.fixture
def solver():
    return pycvc5.Solver()


def test_eq(solver):
  uSort = solver.mkUninterpretedSort("u")
  x = solver.mkVar(uSort, "x")
  y = solver.mkVar(uSort, "y")
  z = Term(solver)

  assert x == x
  assert not x != x
  assert not x == y
  assert x != y
  assert not (x == z)
  assert x != z

def test_get_kind(solver):
  uSort = solver.mkUninterpretedSort("u")
  intSort = solver.getIntegerSort()
  boolSort = solver.getBooleanSort()
  funSort1 = solver.mkFunctionSort(uSort, intSort)
  funSort2 = solver.mkFunctionSort(intSort, boolSort)

  n = Term(solver)
  with pytest.raises(RuntimeError):
      n.getKind()
  x = solver.mkVar(uSort, "x")
  x.getKind()
  y = solver.mkVar(uSort, "y")
  y.getKind()

  f = solver.mkVar(funSort1, "f")
  f.getKind()
  p = solver.mkVar(funSort2, "p")
  p.getKind()

  zero = solver.mkInteger(0)
  zero.getKind()

  f_x = solver.mkTerm(kinds.ApplyUf, f, x)
  f_x.getKind()
  f_y = solver.mkTerm(kinds.ApplyUf, f, y)
  f_y.getKind()
  sum = solver.mkTerm(kinds.Plus, f_x, f_y)
  sum.getKind()
  p_0 = solver.mkTerm(kinds.ApplyUf, p, zero)
  p_0.getKind()
  p_f_y = solver.mkTerm(kinds.ApplyUf, p, f_y)
  p_f_y.getKind()

  # Sequence kinds do not exist internally, test that the API properly
  # converts them back.
  seqSort = solver.mkSequenceSort(intSort)
  s = solver.mkConst(seqSort, "s")
  ss = solver.mkTerm(kinds.SeqConcat, s, s)
  assert ss.getKind() == kinds.SeqConcat

def test_get_sort(solver):
  bvSort = solver.mkBitVectorSort(8)
  intSort = solver.getIntegerSort()
  boolSort = solver.getBooleanSort()
  funSort1 = solver.mkFunctionSort(bvSort, intSort)
  funSort2 = solver.mkFunctionSort(intSort, boolSort)

  n = Term(solver)
  with pytest.raises(RuntimeError):
      n.getSort()
  x = solver.mkVar(bvSort, "x")
  x.getSort()
  assert x.getSort() == bvSort
  y = solver.mkVar(bvSort, "y")
  y.getSort()
  assert y.getSort() == bvSort

  f = solver.mkVar(funSort1, "f")
  f.getSort()
  assert f.getSort() == funSort1
  p = solver.mkVar(funSort2, "p")
  p.getSort()
  assert p.getSort() == funSort2

  zero = solver.mkInteger(0)
  zero.getSort()
  assert zero.getSort() == intSort

  f_x = solver.mkTerm(kinds.ApplyUf, f, x)
  f_x.getSort()
  assert f_x.getSort() == intSort
  f_y = solver.mkTerm(kinds.ApplyUf, f, y)
  f_y.getSort()
  assert f_y.getSort() == intSort
  sum = solver.mkTerm(kinds.Plus, f_x, f_y)
  sum.getSort()
  assert sum.getSort() == intSort
  p_0 = solver.mkTerm(kinds.ApplyUf, p, zero)
  p_0.getSort()
  assert p_0.getSort() == boolSort
  p_f_y = solver.mkTerm(kinds.ApplyUf, p, f_y)
  p_f_y.getSort()
  assert p_f_y.getSort() == boolSort

def test_is_null(solver):
  x = Term(solver)
  assert x.isNull()
  x = solver.mkVar(solver.mkBitVectorSort(4), "x")
  assert not x.isNull()

def test_not_term(solver):
  bvSort = solver.mkBitVectorSort(8)
  intSort = solver.getIntegerSort()
  boolSort = solver.getBooleanSort()
  funSort1 = solver.mkFunctionSort(bvSort, intSort)
  funSort2 = solver.mkFunctionSort(intSort, boolSort)

  with pytest.raises(RuntimeError):
      Term(solver).notTerm()
  b = solver.mkTrue()
  b.notTerm()
  x = solver.mkVar(solver.mkBitVectorSort(8), "x")
  with pytest.raises(RuntimeError):
      x.notTerm()
  f = solver.mkVar(funSort1, "f")
  with pytest.raises(RuntimeError):
      f.notTerm()
  p = solver.mkVar(funSort2, "p")
  with pytest.raises(RuntimeError):
      p.notTerm()
  zero = solver.mkInteger(0)
  with pytest.raises(RuntimeError):
      zero.notTerm()
  f_x = solver.mkTerm(kinds.ApplyUf, f, x)
  with pytest.raises(RuntimeError):
      f_x.notTerm()
  sum = solver.mkTerm(kinds.Plus, f_x, f_x)
  with pytest.raises(RuntimeError):
      sum.notTerm()
  p_0 = solver.mkTerm(kinds.ApplyUf, p, zero)
  p_0.notTerm()
  p_f_x = solver.mkTerm(kinds.ApplyUf, p, f_x)
  p_f_x.notTerm()

def test_and_term(solver):
  bvSort = solver.mkBitVectorSort(8)
  intSort = solver.getIntegerSort()
  boolSort = solver.getBooleanSort()
  funSort1 = solver.mkFunctionSort(bvSort, intSort)
  funSort2 = solver.mkFunctionSort(intSort, boolSort)

  b = solver.mkTrue()
  with pytest.raises(RuntimeError):
      Term(solver).andTerm(b)
  with pytest.raises(RuntimeError):
      b.andTerm(Term(solver))
  b.andTerm(b)
  x = solver.mkVar(solver.mkBitVectorSort(8), "x")
  with pytest.raises(RuntimeError):
      x.andTerm(b)
  with pytest.raises(RuntimeError):
      x.andTerm(x)
  f = solver.mkVar(funSort1, "f")
  with pytest.raises(RuntimeError):
      f.andTerm(b)
  with pytest.raises(RuntimeError):
      f.andTerm(x)
  with pytest.raises(RuntimeError):
      f.andTerm(f)
  p = solver.mkVar(funSort2, "p")
  with pytest.raises(RuntimeError):
      p.andTerm(b)
  with pytest.raises(RuntimeError):
      p.andTerm(x)
  with pytest.raises(RuntimeError):
      p.andTerm(f)
  with pytest.raises(RuntimeError):
      p.andTerm(p)
  zero = solver.mkInteger(0)
  with pytest.raises(RuntimeError):
      zero.andTerm(b)
  with pytest.raises(RuntimeError):
      zero.andTerm(x)
  with pytest.raises(RuntimeError):
      zero.andTerm(f)
  with pytest.raises(RuntimeError):
      zero.andTerm(p)
  with pytest.raises(RuntimeError):
      zero.andTerm(zero)
  f_x = solver.mkTerm(kinds.ApplyUf, f, x)
  with pytest.raises(RuntimeError):
      f_x.andTerm(b)
  with pytest.raises(RuntimeError):
      f_x.andTerm(x)
  with pytest.raises(RuntimeError):
      f_x.andTerm(f)
  with pytest.raises(RuntimeError):
      f_x.andTerm(p)
  with pytest.raises(RuntimeError):
      f_x.andTerm(zero)
  with pytest.raises(RuntimeError):
      f_x.andTerm(f_x)
  sum = solver.mkTerm(kinds.Plus, f_x, f_x)
  with pytest.raises(RuntimeError):
      sum.andTerm(b)
  with pytest.raises(RuntimeError):
      sum.andTerm(x)
  with pytest.raises(RuntimeError):
      sum.andTerm(f)
  with pytest.raises(RuntimeError):
      sum.andTerm(p)
  with pytest.raises(RuntimeError):
      sum.andTerm(zero)
  with pytest.raises(RuntimeError):
      sum.andTerm(f_x)
  with pytest.raises(RuntimeError):
      sum.andTerm(sum)
  p_0 = solver.mkTerm(kinds.ApplyUf, p, zero)
  p_0.andTerm(b)
  with pytest.raises(RuntimeError):
      p_0.andTerm(x)
  with pytest.raises(RuntimeError):
      p_0.andTerm(f)
  with pytest.raises(RuntimeError):
      p_0.andTerm(p)
  with pytest.raises(RuntimeError):
      p_0.andTerm(zero)
  with pytest.raises(RuntimeError):
      p_0.andTerm(f_x)
  with pytest.raises(RuntimeError):
      p_0.andTerm(sum)
  p_0.andTerm(p_0)
  p_f_x = solver.mkTerm(kinds.ApplyUf, p, f_x)
  p_f_x.andTerm(b)
  with pytest.raises(RuntimeError):
      p_f_x.andTerm(x)
  with pytest.raises(RuntimeError):
      p_f_x.andTerm(f)
  with pytest.raises(RuntimeError):
      p_f_x.andTerm(p)
  with pytest.raises(RuntimeError):
      p_f_x.andTerm(zero)
  with pytest.raises(RuntimeError):
      p_f_x.andTerm(f_x)
  with pytest.raises(RuntimeError):
      p_f_x.andTerm(sum)
  p_f_x.andTerm(p_0)
  p_f_x.andTerm(p_f_x)

def test_or_term(solver):
  bvSort = solver.mkBitVectorSort(8)
  intSort = solver.getIntegerSort()
  boolSort = solver.getBooleanSort()
  funSort1 = solver.mkFunctionSort(bvSort, intSort)
  funSort2 = solver.mkFunctionSort(intSort, boolSort)

  b = solver.mkTrue()
  with pytest.raises(RuntimeError):
      Term(solver).orTerm(b)
  with pytest.raises(RuntimeError):
      b.orTerm(Term(solver))
  b.orTerm(b)
  x = solver.mkVar(solver.mkBitVectorSort(8), "x")
  with pytest.raises(RuntimeError):
      x.orTerm(b)
  with pytest.raises(RuntimeError):
      x.orTerm(x)
  f = solver.mkVar(funSort1, "f")
  with pytest.raises(RuntimeError):
      f.orTerm(b)
  with pytest.raises(RuntimeError):
      f.orTerm(x)
  with pytest.raises(RuntimeError):
      f.orTerm(f)
  p = solver.mkVar(funSort2, "p")
  with pytest.raises(RuntimeError):
      p.orTerm(b)
  with pytest.raises(RuntimeError):
      p.orTerm(x)
  with pytest.raises(RuntimeError):
      p.orTerm(f)
  with pytest.raises(RuntimeError):
      p.orTerm(p)
  zero = solver.mkInteger(0)
  with pytest.raises(RuntimeError):
      zero.orTerm(b)
  with pytest.raises(RuntimeError):
      zero.orTerm(x)
  with pytest.raises(RuntimeError):
      zero.orTerm(f)
  with pytest.raises(RuntimeError):
      zero.orTerm(p)
  with pytest.raises(RuntimeError):
      zero.orTerm(zero)
  f_x = solver.mkTerm(kinds.ApplyUf, f, x)
  with pytest.raises(RuntimeError):
      f_x.orTerm(b)
  with pytest.raises(RuntimeError):
      f_x.orTerm(x)
  with pytest.raises(RuntimeError):
      f_x.orTerm(f)
  with pytest.raises(RuntimeError):
      f_x.orTerm(p)
  with pytest.raises(RuntimeError):
      f_x.orTerm(zero)
  with pytest.raises(RuntimeError):
      f_x.orTerm(f_x)
  sum = solver.mkTerm(kinds.Plus, f_x, f_x)
  with pytest.raises(RuntimeError):
      sum.orTerm(b)
  with pytest.raises(RuntimeError):
      sum.orTerm(x)
  with pytest.raises(RuntimeError):
      sum.orTerm(f)
  with pytest.raises(RuntimeError):
      sum.orTerm(p)
  with pytest.raises(RuntimeError):
      sum.orTerm(zero)
  with pytest.raises(RuntimeError):
      sum.orTerm(f_x)
  with pytest.raises(RuntimeError):
      sum.orTerm(sum)
  p_0 = solver.mkTerm(kinds.ApplyUf, p, zero)
  p_0.orTerm(b)
  with pytest.raises(RuntimeError):
      p_0.orTerm(x)
  with pytest.raises(RuntimeError):
      p_0.orTerm(f)
  with pytest.raises(RuntimeError):
      p_0.orTerm(p)
  with pytest.raises(RuntimeError):
      p_0.orTerm(zero)
  with pytest.raises(RuntimeError):
      p_0.orTerm(f_x)
  with pytest.raises(RuntimeError):
      p_0.orTerm(sum)
  p_0.orTerm(p_0)
  p_f_x = solver.mkTerm(kinds.ApplyUf, p, f_x)
  p_f_x.orTerm(b)
  with pytest.raises(RuntimeError):
      p_f_x.orTerm(x)
  with pytest.raises(RuntimeError):
      p_f_x.orTerm(f)
  with pytest.raises(RuntimeError):
      p_f_x.orTerm(p)
  with pytest.raises(RuntimeError):
      p_f_x.orTerm(zero)
  with pytest.raises(RuntimeError):
      p_f_x.orTerm(f_x)
  with pytest.raises(RuntimeError):
      p_f_x.orTerm(sum)
  p_f_x.orTerm(p_0)
  p_f_x.orTerm(p_f_x)

def test_xor_term(solver):
  bvSort = solver.mkBitVectorSort(8)
  intSort = solver.getIntegerSort()
  boolSort = solver.getBooleanSort()
  funSort1 = solver.mkFunctionSort(bvSort, intSort)
  funSort2 = solver.mkFunctionSort(intSort, boolSort)

  b = solver.mkTrue()
  with pytest.raises(RuntimeError):
      Term(solver).xorTerm(b)
  with pytest.raises(RuntimeError):
      b.xorTerm(Term(solver))
  b.xorTerm(b)
  x = solver.mkVar(solver.mkBitVectorSort(8), "x")
  with pytest.raises(RuntimeError):
      x.xorTerm(b)
  with pytest.raises(RuntimeError):
      x.xorTerm(x)
  f = solver.mkVar(funSort1, "f")
  with pytest.raises(RuntimeError):
      f.xorTerm(b)
  with pytest.raises(RuntimeError):
      f.xorTerm(x)
  with pytest.raises(RuntimeError):
      f.xorTerm(f)
  p = solver.mkVar(funSort2, "p")
  with pytest.raises(RuntimeError):
      p.xorTerm(b)
  with pytest.raises(RuntimeError):
      p.xorTerm(x)
  with pytest.raises(RuntimeError):
      p.xorTerm(f)
  with pytest.raises(RuntimeError):
      p.xorTerm(p)
  zero = solver.mkInteger(0)
  with pytest.raises(RuntimeError):
      zero.xorTerm(b)
  with pytest.raises(RuntimeError):
      zero.xorTerm(x)
  with pytest.raises(RuntimeError):
      zero.xorTerm(f)
  with pytest.raises(RuntimeError):
      zero.xorTerm(p)
  with pytest.raises(RuntimeError):
      zero.xorTerm(zero)
  f_x = solver.mkTerm(kinds.ApplyUf, f, x)
  with pytest.raises(RuntimeError):
      f_x.xorTerm(b)
  with pytest.raises(RuntimeError):
      f_x.xorTerm(x)
  with pytest.raises(RuntimeError):
      f_x.xorTerm(f)
  with pytest.raises(RuntimeError):
      f_x.xorTerm(p)
  with pytest.raises(RuntimeError):
      f_x.xorTerm(zero)
  with pytest.raises(RuntimeError):
      f_x.xorTerm(f_x)
  sum = solver.mkTerm(kinds.Plus, f_x, f_x)
  with pytest.raises(RuntimeError):
      sum.xorTerm(b)
  with pytest.raises(RuntimeError):
      sum.xorTerm(x)
  with pytest.raises(RuntimeError):
      sum.xorTerm(f)
  with pytest.raises(RuntimeError):
      sum.xorTerm(p)
  with pytest.raises(RuntimeError):
      sum.xorTerm(zero)
  with pytest.raises(RuntimeError):
      sum.xorTerm(f_x)
  with pytest.raises(RuntimeError):
      sum.xorTerm(sum)
  p_0 = solver.mkTerm(kinds.ApplyUf, p, zero)
  p_0.xorTerm(b)
  with pytest.raises(RuntimeError):
      p_0.xorTerm(x)
  with pytest.raises(RuntimeError):
      p_0.xorTerm(f)
  with pytest.raises(RuntimeError):
      p_0.xorTerm(p)
  with pytest.raises(RuntimeError):
      p_0.xorTerm(zero)
  with pytest.raises(RuntimeError):
      p_0.xorTerm(f_x)
  with pytest.raises(RuntimeError):
      p_0.xorTerm(sum)
  p_0.xorTerm(p_0)
  p_f_x = solver.mkTerm(kinds.ApplyUf, p, f_x)
  p_f_x.xorTerm(b)
  with pytest.raises(RuntimeError):
      p_f_x.xorTerm(x)
  with pytest.raises(RuntimeError):
      p_f_x.xorTerm(f)
  with pytest.raises(RuntimeError):
      p_f_x.xorTerm(p)
  with pytest.raises(RuntimeError):
      p_f_x.xorTerm(zero)
  with pytest.raises(RuntimeError):
      p_f_x.xorTerm(f_x)
  with pytest.raises(RuntimeError):
      p_f_x.xorTerm(sum)
  p_f_x.xorTerm(p_0)
  p_f_x.xorTerm(p_f_x)

def test_eq_term(solver):
  bvSort = solver.mkBitVectorSort(8)
  intSort = solver.getIntegerSort()
  boolSort = solver.getBooleanSort()
  funSort1 = solver.mkFunctionSort(bvSort, intSort)
  funSort2 = solver.mkFunctionSort(intSort, boolSort)

  b = solver.mkTrue()
  with pytest.raises(RuntimeError):
      Term(solver).eqTerm(b)
  with pytest.raises(RuntimeError):
      b.eqTerm(Term(solver))
  b.eqTerm(b)
  x = solver.mkVar(solver.mkBitVectorSort(8), "x")
  with pytest.raises(RuntimeError):
      x.eqTerm(b)
  x.eqTerm(x)
  f = solver.mkVar(funSort1, "f")
  with pytest.raises(RuntimeError):
      f.eqTerm(b)
  with pytest.raises(RuntimeError):
      f.eqTerm(x)
  f.eqTerm(f)
  p = solver.mkVar(funSort2, "p")
  with pytest.raises(RuntimeError):
      p.eqTerm(b)
  with pytest.raises(RuntimeError):
      p.eqTerm(x)
  with pytest.raises(RuntimeError):
      p.eqTerm(f)
  p.eqTerm(p)
  zero = solver.mkInteger(0)
  with pytest.raises(RuntimeError):
      zero.eqTerm(b)
  with pytest.raises(RuntimeError):
      zero.eqTerm(x)
  with pytest.raises(RuntimeError):
      zero.eqTerm(f)
  with pytest.raises(RuntimeError):
      zero.eqTerm(p)
  zero.eqTerm(zero)
  f_x = solver.mkTerm(kinds.ApplyUf, f, x)
  with pytest.raises(RuntimeError):
      f_x.eqTerm(b)
  with pytest.raises(RuntimeError):
      f_x.eqTerm(x)
  with pytest.raises(RuntimeError):
      f_x.eqTerm(f)
  with pytest.raises(RuntimeError):
      f_x.eqTerm(p)
  f_x.eqTerm(zero)
  f_x.eqTerm(f_x)
  sum = solver.mkTerm(kinds.Plus, f_x, f_x)
  with pytest.raises(RuntimeError):
      sum.eqTerm(b)
  with pytest.raises(RuntimeError):
      sum.eqTerm(x)
  with pytest.raises(RuntimeError):
      sum.eqTerm(f)
  with pytest.raises(RuntimeError):
      sum.eqTerm(p)
  sum.eqTerm(zero)
  sum.eqTerm(f_x)
  sum.eqTerm(sum)
  p_0 = solver.mkTerm(kinds.ApplyUf, p, zero)
  p_0.eqTerm(b)
  with pytest.raises(RuntimeError):
      p_0.eqTerm(x)
  with pytest.raises(RuntimeError):
      p_0.eqTerm(f)
  with pytest.raises(RuntimeError):
      p_0.eqTerm(p)
  with pytest.raises(RuntimeError):
      p_0.eqTerm(zero)
  with pytest.raises(RuntimeError):
      p_0.eqTerm(f_x)
  with pytest.raises(RuntimeError):
      p_0.eqTerm(sum)
  p_0.eqTerm(p_0)
  p_f_x = solver.mkTerm(kinds.ApplyUf, p, f_x)
  p_f_x.eqTerm(b)
  with pytest.raises(RuntimeError):
      p_f_x.eqTerm(x)
  with pytest.raises(RuntimeError):
      p_f_x.eqTerm(f)
  with pytest.raises(RuntimeError):
      p_f_x.eqTerm(p)
  with pytest.raises(RuntimeError):
      p_f_x.eqTerm(zero)
  with pytest.raises(RuntimeError):
      p_f_x.eqTerm(f_x)
  with pytest.raises(RuntimeError):
      p_f_x.eqTerm(sum)
  p_f_x.eqTerm(p_0)
  p_f_x.eqTerm(p_f_x)

def test_imp_term(solver):
  bvSort = solver.mkBitVectorSort(8)
  intSort = solver.getIntegerSort()
  boolSort = solver.getBooleanSort()
  funSort1 = solver.mkFunctionSort(bvSort, intSort)
  funSort2 = solver.mkFunctionSort(intSort, boolSort)

  b = solver.mkTrue()
  with pytest.raises(RuntimeError):
      Term(solver).impTerm(b)
  with pytest.raises(RuntimeError):
      b.impTerm(Term(solver))
  b.impTerm(b)
  x = solver.mkVar(solver.mkBitVectorSort(8), "x")
  with pytest.raises(RuntimeError):
      x.impTerm(b)
  with pytest.raises(RuntimeError):
      x.impTerm(x)
  f = solver.mkVar(funSort1, "f")
  with pytest.raises(RuntimeError):
      f.impTerm(b)
  with pytest.raises(RuntimeError):
      f.impTerm(x)
  with pytest.raises(RuntimeError):
      f.impTerm(f)
  p = solver.mkVar(funSort2, "p")
  with pytest.raises(RuntimeError):
      p.impTerm(b)
  with pytest.raises(RuntimeError):
      p.impTerm(x)
  with pytest.raises(RuntimeError):
      p.impTerm(f)
  with pytest.raises(RuntimeError):
      p.impTerm(p)
  zero = solver.mkInteger(0)
  with pytest.raises(RuntimeError):
      zero.impTerm(b)
  with pytest.raises(RuntimeError):
      zero.impTerm(x)
  with pytest.raises(RuntimeError):
      zero.impTerm(f)
  with pytest.raises(RuntimeError):
      zero.impTerm(p)
  with pytest.raises(RuntimeError):
      zero.impTerm(zero)
  f_x = solver.mkTerm(kinds.ApplyUf, f, x)
  with pytest.raises(RuntimeError):
      f_x.impTerm(b)
  with pytest.raises(RuntimeError):
      f_x.impTerm(x)
  with pytest.raises(RuntimeError):
      f_x.impTerm(f)
  with pytest.raises(RuntimeError):
      f_x.impTerm(p)
  with pytest.raises(RuntimeError):
      f_x.impTerm(zero)
  with pytest.raises(RuntimeError):
      f_x.impTerm(f_x)
  sum = solver.mkTerm(kinds.Plus, f_x, f_x)
  with pytest.raises(RuntimeError):
      sum.impTerm(b)
  with pytest.raises(RuntimeError):
      sum.impTerm(x)
  with pytest.raises(RuntimeError):
      sum.impTerm(f)
  with pytest.raises(RuntimeError):
      sum.impTerm(p)
  with pytest.raises(RuntimeError):
      sum.impTerm(zero)
  with pytest.raises(RuntimeError):
      sum.impTerm(f_x)
  with pytest.raises(RuntimeError):
      sum.impTerm(sum)
  p_0 = solver.mkTerm(kinds.ApplyUf, p, zero)
  p_0.impTerm(b)
  with pytest.raises(RuntimeError):
      p_0.impTerm(x)
  with pytest.raises(RuntimeError):
      p_0.impTerm(f)
  with pytest.raises(RuntimeError):
      p_0.impTerm(p)
  with pytest.raises(RuntimeError):
      p_0.impTerm(zero)
  with pytest.raises(RuntimeError):
      p_0.impTerm(f_x)
  with pytest.raises(RuntimeError):
      p_0.impTerm(sum)
  p_0.impTerm(p_0)
  p_f_x = solver.mkTerm(kinds.ApplyUf, p, f_x)
  p_f_x.impTerm(b)
  with pytest.raises(RuntimeError):
      p_f_x.impTerm(x)
  with pytest.raises(RuntimeError):
      p_f_x.impTerm(f)
  with pytest.raises(RuntimeError):
      p_f_x.impTerm(p)
  with pytest.raises(RuntimeError):
      p_f_x.impTerm(zero)
  with pytest.raises(RuntimeError):
      p_f_x.impTerm(f_x)
  with pytest.raises(RuntimeError):
      p_f_x.impTerm(sum)
  p_f_x.impTerm(p_0)
  p_f_x.impTerm(p_f_x)

def test_ite_term(solver):
  bvSort = solver.mkBitVectorSort(8)
  intSort = solver.getIntegerSort()
  boolSort = solver.getBooleanSort()
  funSort1 = solver.mkFunctionSort(bvSort, intSort)
  funSort2 = solver.mkFunctionSort(intSort, boolSort)

  b = solver.mkTrue()
  with pytest.raises(RuntimeError):
      Term(solver).iteTerm(b, b)
  with pytest.raises(RuntimeError):
      b.iteTerm(Term(solver), b)
  with pytest.raises(RuntimeError):
      b.iteTerm(b, Term(solver))
  b.iteTerm(b, b)
  x = solver.mkVar(solver.mkBitVectorSort(8), "x")
  b.iteTerm(x, x)
  b.iteTerm(b, b)
  with pytest.raises(RuntimeError):
      b.iteTerm(x, b)
  with pytest.raises(RuntimeError):
      x.iteTerm(x, x)
  with pytest.raises(RuntimeError):
      x.iteTerm(x, b)
  f = solver.mkVar(funSort1, "f")
  with pytest.raises(RuntimeError):
      f.iteTerm(b, b)
  with pytest.raises(RuntimeError):
      x.iteTerm(b, x)
  p = solver.mkVar(funSort2, "p")
  with pytest.raises(RuntimeError):
      p.iteTerm(b, b)
  with pytest.raises(RuntimeError):
      p.iteTerm(x, b)
  zero = solver.mkInteger(0)
  with pytest.raises(RuntimeError):
      zero.iteTerm(x, x)
  with pytest.raises(RuntimeError):
      zero.iteTerm(x, b)
  f_x = solver.mkTerm(kinds.ApplyUf, f, x)
  with pytest.raises(RuntimeError):
      f_x.iteTerm(b, b)
  with pytest.raises(RuntimeError):
      f_x.iteTerm(b, x)
  sum = solver.mkTerm(kinds.Plus, f_x, f_x)
  with pytest.raises(RuntimeError):
      sum.iteTerm(x, x)
  with pytest.raises(RuntimeError):
      sum.iteTerm(b, x)
  p_0 = solver.mkTerm(kinds.ApplyUf, p, zero)
  p_0.iteTerm(b, b)
  p_0.iteTerm(x, x)
  with pytest.raises(RuntimeError):
      p_0.iteTerm(x, b)
  p_f_x = solver.mkTerm(kinds.ApplyUf, p, f_x)
  p_f_x.iteTerm(b, b)
  p_f_x.iteTerm(x, x)
  with pytest.raises(RuntimeError):
      p_f_x.iteTerm(x, b)

def test_term_assignment(solver):
  t1 = solver.mkInteger(1)
  t2 = t1
  t2 = solver.mkInteger(2)
  assert t1 == solver.mkInteger(1)

def test_const_array(solver):
  intsort = solver.getIntegerSort()
  arrsort = solver.mkArraySort(intsort, intsort)
  a = solver.mkConst(arrsort, "a")
  one = solver.mkInteger(1)
  constarr = solver.mkConstArray(arrsort, one)

  assert constarr.getKind() == kinds.ConstArray
  assert constarr.getConstArrayBase() == one
  with pytest.raises(RuntimeError):
      a.getConstArrayBase()

  arrsort =       solver.mkArraySort(solver.getRealSort(), solver.getRealSort())
  zero_array = solver.mkConstArray(arrsort, solver.mkReal(0))
  stores = solver.mkTerm(
      kinds.Store, zero_array, solver.mkReal(1), solver.mkReal(2))
  stores =       solver.mkTerm(kinds.Store, stores, solver.mkReal(2), solver.mkReal(3))
  stores =       solver.mkTerm(kinds.Store, stores, solver.mkReal(4), solver.mkReal(5))

def test_const_sequence_elements(solver):
  realsort = solver.getRealSort()
  seqsort = solver.mkSequenceSort(realsort)
  s = solver.mkEmptySequence(seqsort)

  assert s.getKind() == kinds.ConstSequence
  # empty sequence has zero elements
  cs = s.getConstSequenceElements()
  assert len(cs) == 0

  # A seq.unit app is not a constant sequence (regardless of whether it is
  # applied to a constant).
  su = solver.mkTerm(kinds.SeqUnit, solver.mkReal(1))
  with pytest.raises(RuntimeError):
      su.getConstSequenceElements()

def test_term_scoped_to_string(solver):
  intsort = solver.getIntegerSort()
  x = solver.mkConst(intsort, "x")
  assert str(x) == "x"
  solver2 = pycvc5.Solver()
  assert str(x) == "x"
