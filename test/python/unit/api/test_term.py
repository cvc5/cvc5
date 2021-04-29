###############################################################################
# Top contributors (to current version):
#   Makai Mann, Andres Noetzli
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

def assert_eq(x, y):
    assert x == y

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

def test_getId(solver):
  n = Term(solver)
  with pytest.raises(RuntimeError):
      n.getId()
  x = solver.mkVar(solver.getIntegerSort(), "x")
  x.getId()
  y = x
  assert_eq(x.getId(), y.getId())

  z = solver.mkVar(solver.getIntegerSort(), "z")
  assert x.getId() != z.getId()

def test_getKind(solver):
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
  assert_eq(ss.getKind(), kinds.SeqConcat)

def test_getSort(solver):
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
  assert_eq(x.getSort(), bvSort)
  y = solver.mkVar(bvSort, "y")
  y.getSort()
  assert_eq(y.getSort(), bvSort)

  f = solver.mkVar(funSort1, "f")
  f.getSort()
  assert_eq(f.getSort(), funSort1)
  p = solver.mkVar(funSort2, "p")
  p.getSort()
  assert_eq(p.getSort(), funSort2)

  zero = solver.mkInteger(0)
  zero.getSort()
  assert_eq(zero.getSort(), intSort)

  f_x = solver.mkTerm(kinds.ApplyUf, f, x)
  f_x.getSort()
  assert_eq(f_x.getSort(), intSort)
  f_y = solver.mkTerm(kinds.ApplyUf, f, y)
  f_y.getSort()
  assert_eq(f_y.getSort(), intSort)
  sum = solver.mkTerm(kinds.Plus, f_x, f_y)
  sum.getSort()
  assert_eq(sum.getSort(), intSort)
  p_0 = solver.mkTerm(kinds.ApplyUf, p, zero)
  p_0.getSort()
  assert_eq(p_0.getSort(), boolSort)
  p_f_y = solver.mkTerm(kinds.ApplyUf, p, f_y)
  p_f_y.getSort()
  assert_eq(p_f_y.getSort(), boolSort)

def test_getOp(solver):
  intsort = solver.getIntegerSort()
  bvsort = solver.mkBitVectorSort(8)
  arrsort = solver.mkArraySort(bvsort, intsort)
  funsort = solver.mkFunctionSort(intsort, bvsort)

  x = solver.mkConst(intsort, "x")
  a = solver.mkConst(arrsort, "a")
  b = solver.mkConst(bvsort, "b")

  assert not x.hasOp()
  with pytest.raises(RuntimeError):
      x.getOp()

  ab = solver.mkTerm(kinds.Select, a, b)
  ext = solver.mkOp(kinds.BVExtract, 4, 0)
  extb = solver.mkTerm(ext, b)

  assert ab.hasOp()
  assert not ab.getOp().isIndexed()
  # can compare directly to a Kind (will invoke constructor)
  assert extb.hasOp()
  assert extb.getOp().isIndexed()
  assert_eq(extb.getOp(), ext)

  f = solver.mkConst(funsort, "f")
  fx = solver.mkTerm(kinds.ApplyUf, f, x)

  assert not f.hasOp()
  with pytest.raises(RuntimeError):
      f.getOp()
  assert fx.hasOp()
  children = [c for c in fx]
  # testing rebuild from op and children
  assert_eq(fx, solver.mkTerm(fx.getOp(), children))

  # Test Datatypes Ops
  sort = solver.mkParamSort("T")
  listDecl = solver.mkDatatypeDecl("paramlist", sort)
  cons = solver.mkDatatypeConstructorDecl("cons")
  nil = solver.mkDatatypeConstructorDecl("nil")
  cons.addSelector("head", sort)
  cons.addSelectorSelf("tail")
  listDecl.addConstructor(cons)
  listDecl.addConstructor(nil)
  listSort = solver.mkDatatypeSort(listDecl)
  intListSort = listSort.instantiate([solver.getIntegerSort()])
  c = solver.mkConst(intListSort, "c")
  list1 = listSort.getDatatype()
  # list datatype constructor and selector operator terms
  consOpTerm = list1.getConstructorTerm("cons")
  nilOpTerm = list1.getConstructorTerm("nil")
  headOpTerm = list1["cons"].getSelectorTerm("head")
  tailOpTerm = list1["cons"].getSelectorTerm("tail")

  nilTerm = solver.mkTerm(APPLY_CONSTRUCTOR, nilOpTerm)
  consTerm = solver.mkTerm(
      APPLY_CONSTRUCTOR, consOpTerm, solver.mkInteger(0), nilTerm)
  headTerm = solver.mkTerm(APPLY_kinds.SelectOR, headOpTerm, consTerm)
  tailTerm = solver.mkTerm(APPLY_kinds.SelectOR, tailOpTerm, consTerm)

  assert nilTerm.hasOp()
  assert consTerm.hasOp()
  assert headTerm.hasOp()
  assert tailTerm.hasOp()

  # Test rebuilding
  children.clear()
  children.insert(children.begin(), headTerm.begin(), headTerm.end())
  assert_eq(headTerm, solver.mkTerm(headTerm.getOp(), children))

def test_isNull(solver):
  x = Term(solver)
  assert x.isNull()
  x = solver.mkVar(solver.mkBitVectorSort(4), "x")
  assert not x.isNull()

def test_notTerm(solver):
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

def test_andTerm(solver):
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

def test_orTerm(solver):
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

def test_xorTerm(solver):
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

def test_eqTerm(solver):
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

def test_impTerm(solver):
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

def test_iteTerm(solver):
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

def test_termAssignment(solver):
  t1 = solver.mkInteger(1)
  t2 = t1
  t2 = solver.mkInteger(2)
  assert_eq(t1, solver.mkInteger(1))

def test_termCompare(solver):
  t1 = solver.mkInteger(1)
  t2 = solver.mkTerm(kinds.Plus, solver.mkInteger(2), solver.mkInteger(2))
  t3 = solver.mkTerm(kinds.Plus, solver.mkInteger(2), solver.mkInteger(2))
  assert t2 >= t3
  assert t2 <= t3
  assert (t1 > t2) != (t1 < t2)
  assert (t1 > t2 or t1 == t2) == (t1 >= t2)

def test_termChildren(solver):
  # simple term 2+3
  two = solver.mkInteger(2)
  t1 = solver.mkTerm(kinds.Plus, two, solver.mkInteger(3))
  assert_eq(t1[0], two)
  assert_eq(t1.getNumChildren(), 2)
  tnull = Term(solver)
  with pytest.raises(RuntimeError):
      tnull.getNumChildren()

  # apply term f(2)
  intSort = solver.getIntegerSort()
  fsort = solver.mkFunctionSort(intSort, intSort)
  f = solver.mkConst(fsort, "f")
  t2 = solver.mkTerm(kinds.ApplyUf, f, two)
  # due to our higher-order view of terms, we treat f as a child of kinds.ApplyUf
  assert_eq(t2.getNumChildren(), 2)
  assert_eq(t2[0], f)
  assert_eq(t2[1], two)
  with pytest.raises(RuntimeError):
      tnull[0]

def test_getInteger(solver):
  int1 = solver.mkInteger("-18446744073709551616")
  int2 = solver.mkInteger("-18446744073709551615")
  int3 = solver.mkInteger("-4294967296")
  int4 = solver.mkInteger("-4294967295")
  int5 = solver.mkInteger("-10")
  int6 = solver.mkInteger("0")
  int7 = solver.mkInteger("10")
  int8 = solver.mkInteger("4294967295")
  int9 = solver.mkInteger("4294967296")
  int10 = solver.mkInteger("18446744073709551615")
  int11 = solver.mkInteger("18446744073709551616")
  int12 = solver.mkInteger("-0")

  with pytest.raises(RuntimeError):
      solver.mkInteger("")
  with pytest.raises(RuntimeError):
      solver.mkInteger("-")
  with pytest.raises(RuntimeError):
      solver.mkInteger("-1-")
  with pytest.raises(RuntimeError):
      solver.mkInteger("0.0")
  with pytest.raises(RuntimeError):
      solver.mkInteger("-0.1")
  with pytest.raises(RuntimeError):
      solver.mkInteger("012")
  with pytest.raises(RuntimeError):
      solver.mkInteger("0000")
  with pytest.raises(RuntimeError):
      solver.mkInteger("-01")
  with pytest.raises(RuntimeError):
      solver.mkInteger("-00")

  assert  not int1.isInt32() and not int1.isUInt32() and not int1.isInt64() and not int1.isUInt64() and int1.isInteger()
  assert_eq(int1.getInteger(), "-18446744073709551616")
  assert not int2.isInt32() and not int2.isUInt32() and not int2.isInt64() and not int2.isUInt64() and int2.isInteger()
  assert_eq(int2.getInteger(), "-18446744073709551615")
  assert not int3.isInt32() and not int3.isUInt32() and int3.isInt64() and not int3.isUInt64() and int3.isInteger()
  assert_eq(int3.getInt64(), -4294967296)
  assert_eq(int3.getInteger(), "-4294967296")
  assert not int4.isInt32() and not int4.isUInt32() and int4.isInt64() and not int4.isUInt64() and int4.isInteger()
  assert_eq(int4.getInt64(), -4294967295)
  assert_eq(int4.getInteger(), "-4294967295")
  assert int5.isInt32() and not int5.isUInt32() and int5.isInt64() and not int5.isUInt64() and int5.isInteger()
  assert_eq(int5.getInt32(), -10)
  assert_eq(int5.getInt64(), -10)
  assert_eq(int5.getInteger(), "-10")
  assert int6.isInt32() and int6.isUInt32() and int6.isInt64() and int6.isUInt64() and int6.isInteger()
  assert_eq(int6.getInt32(), 0)
  assert_eq(int6.getUInt32(), 0)
  assert_eq(int6.getInt64(), 0)
  assert_eq(int6.getUInt64(), 0)
  assert_eq(int6.getInteger(), "0")
  assert int7.isInt32() and int7.isUInt32() and int7.isInt64() and int7.isUInt64() and int7.isInteger()
  assert_eq(int7.getInt32(), 10)
  assert_eq(int7.getUInt32(), 10)
  assert_eq(int7.getInt64(), 10)
  assert_eq(int7.getUInt64(), 10)
  assert_eq(int7.getInteger(), "10")
  assert not int8.isInt32() and int8.isUInt32() and int8.isInt64() and int8.isUInt64() and int8.isInteger()
  assert_eq(int8.getUInt32(), 4294967295)
  assert_eq(int8.getInt64(), 4294967295)
  assert_eq(int8.getUInt64(), 4294967295)
  assert_eq(int8.getInteger(), "4294967295")
  assert not int9.isInt32() and not int9.isUInt32() and int9.isInt64() and int9.isUInt64() and int9.isInteger()
  assert_eq(int9.getInt64(), 4294967296)
  assert_eq(int9.getUInt64(), 4294967296)
  assert_eq(int9.getInteger(), "4294967296")
  assert not int10.isInt32() and not int10.isUInt32() and not int10.isInt64() and int10.isUInt64() and int10.isInteger()
  assert_eq(int10.getUInt64(), 18446744073709551615)
  assert_eq(int10.getInteger(), "18446744073709551615")
  assert not int11.isInt32() and not int11.isUInt32() and not int11.isInt64() and not int11.isUInt64() and int11.isInteger()
  assert_eq(int11.getInteger(), "18446744073709551616")

def test_getString(solver):
  assert(false)
  s1 = solver.mkString("abcde")
  assert s1.isString()
  assert_eq(s1.getString(), "abcde")

def test_substitute(solver):
  x = solver.mkConst(solver.getIntegerSort(), "x")
  one = solver.mkInteger(1)
  ttrue = solver.mkTrue()
  xpx = solver.mkTerm(kinds.Plus, x, x)
  onepone = solver.mkTerm(kinds.Plus, one, one)

  assert_eq(xpx.substitute(x, one), onepone)
  assert_eq(onepone.substitute(one, x), xpx)
  # incorrect due to type
  with pytest.raises(RuntimeError):
      xpx.substitute(one, ttrue)

  # simultaneous substitution
  y = solver.mkConst(solver.getIntegerSort(), "y")
  xpy = solver.mkTerm(kinds.Plus, x, y)
  xpone = solver.mkTerm(kinds.Plus, y, one)
  es = list(Term)
  rs = list(Term)
  es.push_back(x)
  rs.push_back(y)
  es.push_back(y)
  rs.push_back(one)
  assert_eq(xpy.substitute(es, rs), xpone)

  # incorrect substitution due to arity
  rs.pop_back()
  with pytest.raises(RuntimeError):
      xpy.substitute(es, rs)

  # incorrect substitution due to types
  rs.push_back(ttrue)
  with pytest.raises(RuntimeError):
      xpy.substitute(es, rs)

  # null cannot substitute
  tnull
  with pytest.raises(RuntimeError):
      tnull.substitute(one, x)
  with pytest.raises(RuntimeError):
      xpx.substitute(tnull, x)
  with pytest.raises(RuntimeError):
      xpx.substitute(x, tnull)
  rs.pop_back()
  rs.push_back(tnull)
  with pytest.raises(RuntimeError):
      xpy.substitute(es, rs)
  es.clear()
  rs.clear()
  es.push_back(x)
  rs.push_back(y)
  with pytest.raises(RuntimeError):
      tnull.substitute(es, rs)
  es.push_back(tnull)
  rs.push_back(one)
  with pytest.raises(RuntimeError):
      xpx.substitute(es, rs)

def test_constArray(solver):
  intsort = solver.getIntegerSort()
  arrsort = solver.mkArraySort(intsort, intsort)
  a = solver.mkConst(arrsort, "a")
  one = solver.mkInteger(1)
  constarr = solver.mkConstArray(arrsort, one)

  assert_eq(constarr.getKind(), kinds.ConstArray)
  assert_eq(constarr.getConstArrayBase(), one)
  with pytest.raises(RuntimeError):
      a.getConstArrayBase()

  arrsort =       solver.mkArraySort(solver.getRealSort(), solver.getRealSort())
  zero_array = solver.mkConstArray(arrsort, solver.mkReal(0))
  stores = solver.mkTerm(
      kinds.Store, zero_array, solver.mkReal(1), solver.mkReal(2))
  stores =       solver.mkTerm(kinds.Store, stores, solver.mkReal(2), solver.mkReal(3))
  stores =       solver.mkTerm(kinds.Store, stores, solver.mkReal(4), solver.mkReal(5))

def test_constSequenceElements(solver):
  realsort = solver.getRealSort()
  seqsort = solver.mkSequenceSort(realsort)
  s = solver.mkEmptySequence(seqsort)

  assert_eq(s.getKind(), kinds.ConstSequence)
  # empty sequence has zero elements
  cs = s.getConstSequenceElements()
  assert len(cs) == 0

  # A seq.unit app is not a constant sequence (regardless of whether it is
  # applied to a constant).
  su = solver.mkTerm(kinds.SeqUnit, solver.mkReal(1))
  with pytest.raises(RuntimeError):
      su.getConstSequenceElements()

def test_termScopedToString(solver):
  intsort = solver.getIntegerSort()
  x = solver.mkConst(intsort, "x")
  assert_eq(str(x), "x")
  solver2 = pycvc5.Solver()
  assert_eq(str(x), "x")






#def test_getitem():
#    solver = pycvc5.Solver()
#    intsort = solver.getIntegerSort()
#    x = solver.mkConst(intsort, 'x')
#    y = solver.mkConst(intsort, 'y')
#    xpy = solver.mkTerm(kinds.Plus, x, y)
#
#    assert xpy[0] == x
#    assert xpy[1] == y
#
#
#def test_get_kind():
#    solver = pycvc5.Solver()
#    intsort = solver.getIntegerSort()
#    x = solver.mkConst(intsort, 'x')
#    y = solver.mkConst(intsort, 'y')
#    xpy = solver.mkTerm(kinds.Plus, x, y)
#    assert xpy.getKind() == kinds.Plus
#
#    funsort = solver.mkFunctionSort(intsort, intsort)
#    f = solver.mkConst(funsort, 'f')
#    assert f.getKind() == kinds.Constant
#
#    fx = solver.mkTerm(kinds.kinds.ApplyUf, f, x)
#    assert fx.getKind() == kinds.kinds.ApplyUf
#
#    # Sequence kinds do not exist internally, test that the API properly
#    # converts them back.
#    seqsort = solver.mkSequenceSort(intsort)
#    s = solver.mkConst(seqsort, 's')
#    ss = solver.mkTerm(kinds.SeqConcat, s, s)
#    assert ss.getKind() == kinds.SeqConcat
#
#
#def test_eq():
#    solver = pycvc5.Solver()
#    usort = solver.mkUninterpretedSort('u')
#    x = solver.mkConst(usort, 'x')
#    y = solver.mkConst(usort, 'y')
#    z = x
#
#    assert x == x
#    assert x == z
#    assert not (x != x)
#    assert x != y
#    assert y != z
#
#
#def test_get_sort():
#    solver = pycvc5.Solver()
#    intsort = solver.getIntegerSort()
#    bvsort8 = solver.mkBitVectorSort(8)
#
#    x = solver.mkConst(intsort, 'x')
#    y = solver.mkConst(intsort, 'y')
#
#    a = solver.mkConst(bvsort8, 'a')
#    b = solver.mkConst(bvsort8, 'b')
#
#    assert x.getSort() == intsort
#    assert solver.mkTerm(kinds.Plus, x, y).getSort() == intsort
#
#    assert a.getSort() == bvsort8
#    assert solver.mkTerm(kinds.BVConcat, a, b).getSort() == solver.mkBitVectorSort(16)
#
#def test_get_op():
#    solver = pycvc5.Solver()
#    intsort = solver.getIntegerSort()
#    funsort = solver.mkFunctionSort(intsort, intsort)
#
#    x = solver.mkConst(intsort, 'x')
#    f = solver.mkConst(funsort, 'f')
#
#    fx = solver.mkTerm(kinds.kinds.ApplyUf, f, x)
#
#    assert not x.hasOp()
#
#    try:
#        op = x.getOp()
#        assert False
#    except:
#        assert True
#
#    assert fx.hasOp()
#    assert fx.getOp().getKind() == kinds.kinds.ApplyUf
#    # equivalent check
#    assert fx.getOp() == solver.mkOp(kinds.kinds.ApplyUf)
#
#
#def test_const_sequence_elements():
#    solver = pycvc5.Solver()
#    realsort = solver.getRealSort()
#    seqsort = solver.mkSequenceSort(realsort)
#    s = solver.mkEmptySequence(seqsort)
#
#    assert s.getKind() == kinds.ConstSequence
#    # empty sequence has zero elements
#    cs = s.getConstSequenceElements()
#    assert len(cs) == 0
#
#    # A seq.unit app is not a constant sequence (regardless of whether it is
#    # applied to a constant).
#    su = solver.mkTerm(kinds.SeqUnit, solver.mkReal(1))
#    try:
#        su.getConstSequenceElements()
#        assert False
#    except:
#        assert True
