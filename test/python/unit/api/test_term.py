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
from pycvc5 import Sort


@pytest.fixture
def solver():
    return pycvc5.Solver()


def test_eq(solver):
  uSort = d_solver.mkUninterpretedSort("u")
  x = d_solver.mkVar(uSort, "x")
  y = d_solver.mkVar(uSort, "y")
  z = Term()

  ASSERT_TRUE(x == x)
  ASSERT_FALSE(x != x)
  ASSERT_FALSE(x == y)
  ASSERT_TRUE(x != y)
  ASSERT_FALSE((x == z))
  ASSERT_TRUE(x != z)

def test_getId(solver):
  n = Term()
  ASSERT_THROW(n.getId(), CVC5ApiException)
  x = d_solver.mkVar(d_solver.getIntegerSort(), "x")
  ASSERT_NO_THROW(x.getId())
  y = x
  ASSERT_EQ(x.getId(), y.getId())

  z = d_solver.mkVar(d_solver.getIntegerSort(), "z")
  ASSERT_NE(x.getId(), z.getId())

def test_getKind(solver):
  uSort = d_solver.mkUninterpretedSort("u")
  intSort = d_solver.getIntegerSort()
  boolSort = d_solver.getBooleanSort()
  funSort1 = d_solver.mkFunctionSort(uSort, intSort)
  funSort2 = d_solver.mkFunctionSort(intSort, boolSort)

  n = Term()
  ASSERT_THROW(n.getKind(), CVC5ApiException)
  x = d_solver.mkVar(uSort, "x")
  ASSERT_NO_THROW(x.getKind())
  y = d_solver.mkVar(uSort, "y")
  ASSERT_NO_THROW(y.getKind())

  f = d_solver.mkVar(funSort1, "f")
  ASSERT_NO_THROW(f.getKind())
  p = d_solver.mkVar(funSort2, "p")
  ASSERT_NO_THROW(p.getKind())

  zero = d_solver.mkInteger(0)
  ASSERT_NO_THROW(zero.getKind())

  f_x = d_solver.mkTerm(APPLY_UF, f, x)
  ASSERT_NO_THROW(f_x.getKind())
  f_y = d_solver.mkTerm(APPLY_UF, f, y)
  ASSERT_NO_THROW(f_y.getKind())
  sum = d_solver.mkTerm(PLUS, f_x, f_y)
  ASSERT_NO_THROW(sum.getKind())
  p_0 = d_solver.mkTerm(APPLY_UF, p, zero)
  ASSERT_NO_THROW(p_0.getKind())
  p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y)
  ASSERT_NO_THROW(p_f_y.getKind())

  # Sequence kinds do not exist internally, test that the API properly
  # converts them back.
  seqSort = d_solver.mkSequenceSort(intSort)
  s = d_solver.mkConst(seqSort, "s")
  ss = d_solver.mkTerm(SEQ_CONCAT, s, s)
  ASSERT_EQ(ss.getKind(), SEQ_CONCAT)

def test_getSort(solver):
  bvSort = d_solver.mkBitVectorSort(8)
  intSort = d_solver.getIntegerSort()
  boolSort = d_solver.getBooleanSort()
  funSort1 = d_solver.mkFunctionSort(bvSort, intSort)
  funSort2 = d_solver.mkFunctionSort(intSort, boolSort)

  n = Term()
  ASSERT_THROW(n.getSort(), CVC5ApiException)
  x = d_solver.mkVar(bvSort, "x")
  ASSERT_NO_THROW(x.getSort())
  ASSERT_EQ(x.getSort(), bvSort)
  y = d_solver.mkVar(bvSort, "y")
  ASSERT_NO_THROW(y.getSort())
  ASSERT_EQ(y.getSort(), bvSort)

  f = d_solver.mkVar(funSort1, "f")
  ASSERT_NO_THROW(f.getSort())
  ASSERT_EQ(f.getSort(), funSort1)
  p = d_solver.mkVar(funSort2, "p")
  ASSERT_NO_THROW(p.getSort())
  ASSERT_EQ(p.getSort(), funSort2)

  zero = d_solver.mkInteger(0)
  ASSERT_NO_THROW(zero.getSort())
  ASSERT_EQ(zero.getSort(), intSort)

  f_x = d_solver.mkTerm(APPLY_UF, f, x)
  ASSERT_NO_THROW(f_x.getSort())
  ASSERT_EQ(f_x.getSort(), intSort)
  f_y = d_solver.mkTerm(APPLY_UF, f, y)
  ASSERT_NO_THROW(f_y.getSort())
  ASSERT_EQ(f_y.getSort(), intSort)
  sum = d_solver.mkTerm(PLUS, f_x, f_y)
  ASSERT_NO_THROW(sum.getSort())
  ASSERT_EQ(sum.getSort(), intSort)
  p_0 = d_solver.mkTerm(APPLY_UF, p, zero)
  ASSERT_NO_THROW(p_0.getSort())
  ASSERT_EQ(p_0.getSort(), boolSort)
  p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y)
  ASSERT_NO_THROW(p_f_y.getSort())
  ASSERT_EQ(p_f_y.getSort(), boolSort)

def test_getOp(solver):
  intsort = d_solver.getIntegerSort()
  bvsort = d_solver.mkBitVectorSort(8)
  arrsort = d_solver.mkArraySort(bvsort, intsort)
  funsort = d_solver.mkFunctionSort(intsort, bvsort)

  x = d_solver.mkConst(intsort, "x")
  a = d_solver.mkConst(arrsort, "a")
  b = d_solver.mkConst(bvsort, "b")

  ASSERT_FALSE(x.hasOp())
  ASSERT_THROW(x.getOp(), CVC5ApiException)

  ab = d_solver.mkTerm(SELECT, a, b)
  ext = d_solver.mkOp(BITVECTOR_EXTRACT, 4, 0)
  extb = d_solver.mkTerm(ext, b)

  ASSERT_TRUE(ab.hasOp())
  ASSERT_FALSE(ab.getOp().isIndexed())
  # can compare directly to a Kind (will invoke constructor)
  ASSERT_TRUE(extb.hasOp())
  ASSERT_TRUE(extb.getOp().isIndexed())
  ASSERT_EQ(extb.getOp(), ext)

  f = d_solver.mkConst(funsort, "f")
  fx = d_solver.mkTerm(APPLY_UF, f, x)

  ASSERT_FALSE(f.hasOp())
  ASSERT_THROW(f.getOp(), CVC5ApiException)
  ASSERT_TRUE(fx.hasOp())
  children = [c for c in fx]
  # testing rebuild from op and children
  ASSERT_EQ(fx, d_solver.mkTerm(fx.getOp(), children))

  # Test Datatypes Ops
  sort = d_solver.mkParamSort("T")
  glistDecl = d_solver.mkDatatypeDecl("paramlist", sort)
  cons = d_solver.mkDatatypeConstructorDecl("cons")
  nil = d_solver.mkDatatypeConstructorDecl("nil")
  cons.addSelector("head", sort)
  cons.addSelectorSelf("tail")
  listDecl.addConstructor(cons)
  listDecl.addConstructor(nil)
  listSort = d_solver.mkDatatypeSort(listDecl)
  intListSort = listSort.instantiate([d_solver.getIntegerSort()])
  c = d_solver.mkConst(intListSort, "c")
  list1 = listSort.getDatatype()
  # list datatype constructor and selector operator terms
  consOpTerm = list1.getConstructorTerm("cons")
  nilOpTerm = list1.getConstructorTerm("nil")
  headOpTerm = list1["cons"].getSelectorTerm("head")
  tailOpTerm = list1["cons"].getSelectorTerm("tail")

  nilTerm = d_solver.mkTerm(APPLY_CONSTRUCTOR, nilOpTerm)
  consTerm = d_solver.mkTerm(
      APPLY_CONSTRUCTOR, consOpTerm, d_solver.mkInteger(0), nilTerm)
  headTerm = d_solver.mkTerm(APPLY_SELECTOR, headOpTerm, consTerm)
  tailTerm = d_solver.mkTerm(APPLY_SELECTOR, tailOpTerm, consTerm)

  ASSERT_TRUE(nilTerm.hasOp())
  ASSERT_TRUE(consTerm.hasOp())
  ASSERT_TRUE(headTerm.hasOp())
  ASSERT_TRUE(tailTerm.hasOp())

  # Test rebuilding
  children.clear()
  children.insert(children.begin(), headTerm.begin(), headTerm.end())
  ASSERT_EQ(headTerm, d_solver.mkTerm(headTerm.getOp(), children))

def test_isNull(solver):
  x
  ASSERT_TRUE(x.isNull())
  x = d_solver.mkVar(d_solver.mkBitVectorSort(4), "x")
  ASSERT_FALSE(x.isNull())

def test_notTerm(solver):
  bvSort = d_solver.mkBitVectorSort(8)
  intSort = d_solver.getIntegerSort()
  boolSort = d_solver.getBooleanSort()
  funSort1 = d_solver.mkFunctionSort(bvSort, intSort)
  funSort2 = d_solver.mkFunctionSort(intSort, boolSort)

  ASSERT_THROW(Term().notTerm(), CVC5ApiException)
  b = d_solver.mkTrue()
  ASSERT_NO_THROW(b.notTerm())
  x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x")
  ASSERT_THROW(x.notTerm(), CVC5ApiException)
  f = d_solver.mkVar(funSort1, "f")
  ASSERT_THROW(f.notTerm(), CVC5ApiException)
  p = d_solver.mkVar(funSort2, "p")
  ASSERT_THROW(p.notTerm(), CVC5ApiException)
  zero = d_solver.mkInteger(0)
  ASSERT_THROW(zero.notTerm(), CVC5ApiException)
  f_x = d_solver.mkTerm(APPLY_UF, f, x)
  ASSERT_THROW(f_x.notTerm(), CVC5ApiException)
  sum = d_solver.mkTerm(PLUS, f_x, f_x)
  ASSERT_THROW(sum.notTerm(), CVC5ApiException)
  p_0 = d_solver.mkTerm(APPLY_UF, p, zero)
  ASSERT_NO_THROW(p_0.notTerm())
  p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x)
  ASSERT_NO_THROW(p_f_x.notTerm())

def test_andTerm(solver):
  bvSort = d_solver.mkBitVectorSort(8)
  intSort = d_solver.getIntegerSort()
  boolSort = d_solver.getBooleanSort()
  funSort1 = d_solver.mkFunctionSort(bvSort, intSort)
  funSort2 = d_solver.mkFunctionSort(intSort, boolSort)

  b = d_solver.mkTrue()
  ASSERT_THROW(Term().andTerm(b), CVC5ApiException)
  ASSERT_THROW(b.andTerm(Term()), CVC5ApiException)
  ASSERT_NO_THROW(b.andTerm(b))
  x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x")
  ASSERT_THROW(x.andTerm(b), CVC5ApiException)
  ASSERT_THROW(x.andTerm(x), CVC5ApiException)
  f = d_solver.mkVar(funSort1, "f")
  ASSERT_THROW(f.andTerm(b), CVC5ApiException)
  ASSERT_THROW(f.andTerm(x), CVC5ApiException)
  ASSERT_THROW(f.andTerm(f), CVC5ApiException)
  p = d_solver.mkVar(funSort2, "p")
  ASSERT_THROW(p.andTerm(b), CVC5ApiException)
  ASSERT_THROW(p.andTerm(x), CVC5ApiException)
  ASSERT_THROW(p.andTerm(f), CVC5ApiException)
  ASSERT_THROW(p.andTerm(p), CVC5ApiException)
  zero = d_solver.mkInteger(0)
  ASSERT_THROW(zero.andTerm(b), CVC5ApiException)
  ASSERT_THROW(zero.andTerm(x), CVC5ApiException)
  ASSERT_THROW(zero.andTerm(f), CVC5ApiException)
  ASSERT_THROW(zero.andTerm(p), CVC5ApiException)
  ASSERT_THROW(zero.andTerm(zero), CVC5ApiException)
  f_x = d_solver.mkTerm(APPLY_UF, f, x)
  ASSERT_THROW(f_x.andTerm(b), CVC5ApiException)
  ASSERT_THROW(f_x.andTerm(x), CVC5ApiException)
  ASSERT_THROW(f_x.andTerm(f), CVC5ApiException)
  ASSERT_THROW(f_x.andTerm(p), CVC5ApiException)
  ASSERT_THROW(f_x.andTerm(zero), CVC5ApiException)
  ASSERT_THROW(f_x.andTerm(f_x), CVC5ApiException)
  sum = d_solver.mkTerm(PLUS, f_x, f_x)
  ASSERT_THROW(sum.andTerm(b), CVC5ApiException)
  ASSERT_THROW(sum.andTerm(x), CVC5ApiException)
  ASSERT_THROW(sum.andTerm(f), CVC5ApiException)
  ASSERT_THROW(sum.andTerm(p), CVC5ApiException)
  ASSERT_THROW(sum.andTerm(zero), CVC5ApiException)
  ASSERT_THROW(sum.andTerm(f_x), CVC5ApiException)
  ASSERT_THROW(sum.andTerm(sum), CVC5ApiException)
  p_0 = d_solver.mkTerm(APPLY_UF, p, zero)
  ASSERT_NO_THROW(p_0.andTerm(b))
  ASSERT_THROW(p_0.andTerm(x), CVC5ApiException)
  ASSERT_THROW(p_0.andTerm(f), CVC5ApiException)
  ASSERT_THROW(p_0.andTerm(p), CVC5ApiException)
  ASSERT_THROW(p_0.andTerm(zero), CVC5ApiException)
  ASSERT_THROW(p_0.andTerm(f_x), CVC5ApiException)
  ASSERT_THROW(p_0.andTerm(sum), CVC5ApiException)
  ASSERT_NO_THROW(p_0.andTerm(p_0))
  p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x)
  ASSERT_NO_THROW(p_f_x.andTerm(b))
  ASSERT_THROW(p_f_x.andTerm(x), CVC5ApiException)
  ASSERT_THROW(p_f_x.andTerm(f), CVC5ApiException)
  ASSERT_THROW(p_f_x.andTerm(p), CVC5ApiException)
  ASSERT_THROW(p_f_x.andTerm(zero), CVC5ApiException)
  ASSERT_THROW(p_f_x.andTerm(f_x), CVC5ApiException)
  ASSERT_THROW(p_f_x.andTerm(sum), CVC5ApiException)
  ASSERT_NO_THROW(p_f_x.andTerm(p_0))
  ASSERT_NO_THROW(p_f_x.andTerm(p_f_x))

def test_orTerm(solver):
  bvSort = d_solver.mkBitVectorSort(8)
  intSort = d_solver.getIntegerSort()
  boolSort = d_solver.getBooleanSort()
  funSort1 = d_solver.mkFunctionSort(bvSort, intSort)
  funSort2 = d_solver.mkFunctionSort(intSort, boolSort)

  b = d_solver.mkTrue()
  ASSERT_THROW(Term().orTerm(b), CVC5ApiException)
  ASSERT_THROW(b.orTerm(Term()), CVC5ApiException)
  ASSERT_NO_THROW(b.orTerm(b))
  x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x")
  ASSERT_THROW(x.orTerm(b), CVC5ApiException)
  ASSERT_THROW(x.orTerm(x), CVC5ApiException)
  f = d_solver.mkVar(funSort1, "f")
  ASSERT_THROW(f.orTerm(b), CVC5ApiException)
  ASSERT_THROW(f.orTerm(x), CVC5ApiException)
  ASSERT_THROW(f.orTerm(f), CVC5ApiException)
  p = d_solver.mkVar(funSort2, "p")
  ASSERT_THROW(p.orTerm(b), CVC5ApiException)
  ASSERT_THROW(p.orTerm(x), CVC5ApiException)
  ASSERT_THROW(p.orTerm(f), CVC5ApiException)
  ASSERT_THROW(p.orTerm(p), CVC5ApiException)
  zero = d_solver.mkInteger(0)
  ASSERT_THROW(zero.orTerm(b), CVC5ApiException)
  ASSERT_THROW(zero.orTerm(x), CVC5ApiException)
  ASSERT_THROW(zero.orTerm(f), CVC5ApiException)
  ASSERT_THROW(zero.orTerm(p), CVC5ApiException)
  ASSERT_THROW(zero.orTerm(zero), CVC5ApiException)
  f_x = d_solver.mkTerm(APPLY_UF, f, x)
  ASSERT_THROW(f_x.orTerm(b), CVC5ApiException)
  ASSERT_THROW(f_x.orTerm(x), CVC5ApiException)
  ASSERT_THROW(f_x.orTerm(f), CVC5ApiException)
  ASSERT_THROW(f_x.orTerm(p), CVC5ApiException)
  ASSERT_THROW(f_x.orTerm(zero), CVC5ApiException)
  ASSERT_THROW(f_x.orTerm(f_x), CVC5ApiException)
  sum = d_solver.mkTerm(PLUS, f_x, f_x)
  ASSERT_THROW(sum.orTerm(b), CVC5ApiException)
  ASSERT_THROW(sum.orTerm(x), CVC5ApiException)
  ASSERT_THROW(sum.orTerm(f), CVC5ApiException)
  ASSERT_THROW(sum.orTerm(p), CVC5ApiException)
  ASSERT_THROW(sum.orTerm(zero), CVC5ApiException)
  ASSERT_THROW(sum.orTerm(f_x), CVC5ApiException)
  ASSERT_THROW(sum.orTerm(sum), CVC5ApiException)
  p_0 = d_solver.mkTerm(APPLY_UF, p, zero)
  ASSERT_NO_THROW(p_0.orTerm(b))
  ASSERT_THROW(p_0.orTerm(x), CVC5ApiException)
  ASSERT_THROW(p_0.orTerm(f), CVC5ApiException)
  ASSERT_THROW(p_0.orTerm(p), CVC5ApiException)
  ASSERT_THROW(p_0.orTerm(zero), CVC5ApiException)
  ASSERT_THROW(p_0.orTerm(f_x), CVC5ApiException)
  ASSERT_THROW(p_0.orTerm(sum), CVC5ApiException)
  ASSERT_NO_THROW(p_0.orTerm(p_0))
  p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x)
  ASSERT_NO_THROW(p_f_x.orTerm(b))
  ASSERT_THROW(p_f_x.orTerm(x), CVC5ApiException)
  ASSERT_THROW(p_f_x.orTerm(f), CVC5ApiException)
  ASSERT_THROW(p_f_x.orTerm(p), CVC5ApiException)
  ASSERT_THROW(p_f_x.orTerm(zero), CVC5ApiException)
  ASSERT_THROW(p_f_x.orTerm(f_x), CVC5ApiException)
  ASSERT_THROW(p_f_x.orTerm(sum), CVC5ApiException)
  ASSERT_NO_THROW(p_f_x.orTerm(p_0))
  ASSERT_NO_THROW(p_f_x.orTerm(p_f_x))

def test_xorTerm(solver):
  bvSort = d_solver.mkBitVectorSort(8)
  intSort = d_solver.getIntegerSort()
  boolSort = d_solver.getBooleanSort()
  funSort1 = d_solver.mkFunctionSort(bvSort, intSort)
  funSort2 = d_solver.mkFunctionSort(intSort, boolSort)

  b = d_solver.mkTrue()
  ASSERT_THROW(Term().xorTerm(b), CVC5ApiException)
  ASSERT_THROW(b.xorTerm(Term()), CVC5ApiException)
  ASSERT_NO_THROW(b.xorTerm(b))
  x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x")
  ASSERT_THROW(x.xorTerm(b), CVC5ApiException)
  ASSERT_THROW(x.xorTerm(x), CVC5ApiException)
  f = d_solver.mkVar(funSort1, "f")
  ASSERT_THROW(f.xorTerm(b), CVC5ApiException)
  ASSERT_THROW(f.xorTerm(x), CVC5ApiException)
  ASSERT_THROW(f.xorTerm(f), CVC5ApiException)
  p = d_solver.mkVar(funSort2, "p")
  ASSERT_THROW(p.xorTerm(b), CVC5ApiException)
  ASSERT_THROW(p.xorTerm(x), CVC5ApiException)
  ASSERT_THROW(p.xorTerm(f), CVC5ApiException)
  ASSERT_THROW(p.xorTerm(p), CVC5ApiException)
  zero = d_solver.mkInteger(0)
  ASSERT_THROW(zero.xorTerm(b), CVC5ApiException)
  ASSERT_THROW(zero.xorTerm(x), CVC5ApiException)
  ASSERT_THROW(zero.xorTerm(f), CVC5ApiException)
  ASSERT_THROW(zero.xorTerm(p), CVC5ApiException)
  ASSERT_THROW(zero.xorTerm(zero), CVC5ApiException)
  f_x = d_solver.mkTerm(APPLY_UF, f, x)
  ASSERT_THROW(f_x.xorTerm(b), CVC5ApiException)
  ASSERT_THROW(f_x.xorTerm(x), CVC5ApiException)
  ASSERT_THROW(f_x.xorTerm(f), CVC5ApiException)
  ASSERT_THROW(f_x.xorTerm(p), CVC5ApiException)
  ASSERT_THROW(f_x.xorTerm(zero), CVC5ApiException)
  ASSERT_THROW(f_x.xorTerm(f_x), CVC5ApiException)
  sum = d_solver.mkTerm(PLUS, f_x, f_x)
  ASSERT_THROW(sum.xorTerm(b), CVC5ApiException)
  ASSERT_THROW(sum.xorTerm(x), CVC5ApiException)
  ASSERT_THROW(sum.xorTerm(f), CVC5ApiException)
  ASSERT_THROW(sum.xorTerm(p), CVC5ApiException)
  ASSERT_THROW(sum.xorTerm(zero), CVC5ApiException)
  ASSERT_THROW(sum.xorTerm(f_x), CVC5ApiException)
  ASSERT_THROW(sum.xorTerm(sum), CVC5ApiException)
  p_0 = d_solver.mkTerm(APPLY_UF, p, zero)
  ASSERT_NO_THROW(p_0.xorTerm(b))
  ASSERT_THROW(p_0.xorTerm(x), CVC5ApiException)
  ASSERT_THROW(p_0.xorTerm(f), CVC5ApiException)
  ASSERT_THROW(p_0.xorTerm(p), CVC5ApiException)
  ASSERT_THROW(p_0.xorTerm(zero), CVC5ApiException)
  ASSERT_THROW(p_0.xorTerm(f_x), CVC5ApiException)
  ASSERT_THROW(p_0.xorTerm(sum), CVC5ApiException)
  ASSERT_NO_THROW(p_0.xorTerm(p_0))
  p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x)
  ASSERT_NO_THROW(p_f_x.xorTerm(b))
  ASSERT_THROW(p_f_x.xorTerm(x), CVC5ApiException)
  ASSERT_THROW(p_f_x.xorTerm(f), CVC5ApiException)
  ASSERT_THROW(p_f_x.xorTerm(p), CVC5ApiException)
  ASSERT_THROW(p_f_x.xorTerm(zero), CVC5ApiException)
  ASSERT_THROW(p_f_x.xorTerm(f_x), CVC5ApiException)
  ASSERT_THROW(p_f_x.xorTerm(sum), CVC5ApiException)
  ASSERT_NO_THROW(p_f_x.xorTerm(p_0))
  ASSERT_NO_THROW(p_f_x.xorTerm(p_f_x))

def test_eqTerm(solver):
  bvSort = d_solver.mkBitVectorSort(8)
  intSort = d_solver.getIntegerSort()
  boolSort = d_solver.getBooleanSort()
  funSort1 = d_solver.mkFunctionSort(bvSort, intSort)
  funSort2 = d_solver.mkFunctionSort(intSort, boolSort)

  b = d_solver.mkTrue()
  ASSERT_THROW(Term().eqTerm(b), CVC5ApiException)
  ASSERT_THROW(b.eqTerm(Term()), CVC5ApiException)
  ASSERT_NO_THROW(b.eqTerm(b))
  x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x")
  ASSERT_THROW(x.eqTerm(b), CVC5ApiException)
  ASSERT_NO_THROW(x.eqTerm(x))
  f = d_solver.mkVar(funSort1, "f")
  ASSERT_THROW(f.eqTerm(b), CVC5ApiException)
  ASSERT_THROW(f.eqTerm(x), CVC5ApiException)
  ASSERT_NO_THROW(f.eqTerm(f))
  p = d_solver.mkVar(funSort2, "p")
  ASSERT_THROW(p.eqTerm(b), CVC5ApiException)
  ASSERT_THROW(p.eqTerm(x), CVC5ApiException)
  ASSERT_THROW(p.eqTerm(f), CVC5ApiException)
  ASSERT_NO_THROW(p.eqTerm(p))
  zero = d_solver.mkInteger(0)
  ASSERT_THROW(zero.eqTerm(b), CVC5ApiException)
  ASSERT_THROW(zero.eqTerm(x), CVC5ApiException)
  ASSERT_THROW(zero.eqTerm(f), CVC5ApiException)
  ASSERT_THROW(zero.eqTerm(p), CVC5ApiException)
  ASSERT_NO_THROW(zero.eqTerm(zero))
  f_x = d_solver.mkTerm(APPLY_UF, f, x)
  ASSERT_THROW(f_x.eqTerm(b), CVC5ApiException)
  ASSERT_THROW(f_x.eqTerm(x), CVC5ApiException)
  ASSERT_THROW(f_x.eqTerm(f), CVC5ApiException)
  ASSERT_THROW(f_x.eqTerm(p), CVC5ApiException)
  ASSERT_NO_THROW(f_x.eqTerm(zero))
  ASSERT_NO_THROW(f_x.eqTerm(f_x))
  sum = d_solver.mkTerm(PLUS, f_x, f_x)
  ASSERT_THROW(sum.eqTerm(b), CVC5ApiException)
  ASSERT_THROW(sum.eqTerm(x), CVC5ApiException)
  ASSERT_THROW(sum.eqTerm(f), CVC5ApiException)
  ASSERT_THROW(sum.eqTerm(p), CVC5ApiException)
  ASSERT_NO_THROW(sum.eqTerm(zero))
  ASSERT_NO_THROW(sum.eqTerm(f_x))
  ASSERT_NO_THROW(sum.eqTerm(sum))
  p_0 = d_solver.mkTerm(APPLY_UF, p, zero)
  ASSERT_NO_THROW(p_0.eqTerm(b))
  ASSERT_THROW(p_0.eqTerm(x), CVC5ApiException)
  ASSERT_THROW(p_0.eqTerm(f), CVC5ApiException)
  ASSERT_THROW(p_0.eqTerm(p), CVC5ApiException)
  ASSERT_THROW(p_0.eqTerm(zero), CVC5ApiException)
  ASSERT_THROW(p_0.eqTerm(f_x), CVC5ApiException)
  ASSERT_THROW(p_0.eqTerm(sum), CVC5ApiException)
  ASSERT_NO_THROW(p_0.eqTerm(p_0))
  p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x)
  ASSERT_NO_THROW(p_f_x.eqTerm(b))
  ASSERT_THROW(p_f_x.eqTerm(x), CVC5ApiException)
  ASSERT_THROW(p_f_x.eqTerm(f), CVC5ApiException)
  ASSERT_THROW(p_f_x.eqTerm(p), CVC5ApiException)
  ASSERT_THROW(p_f_x.eqTerm(zero), CVC5ApiException)
  ASSERT_THROW(p_f_x.eqTerm(f_x), CVC5ApiException)
  ASSERT_THROW(p_f_x.eqTerm(sum), CVC5ApiException)
  ASSERT_NO_THROW(p_f_x.eqTerm(p_0))
  ASSERT_NO_THROW(p_f_x.eqTerm(p_f_x))

def test_impTerm(solver):
  bvSort = d_solver.mkBitVectorSort(8)
  intSort = d_solver.getIntegerSort()
  boolSort = d_solver.getBooleanSort()
  funSort1 = d_solver.mkFunctionSort(bvSort, intSort)
  funSort2 = d_solver.mkFunctionSort(intSort, boolSort)

  b = d_solver.mkTrue()
  ASSERT_THROW(Term().impTerm(b), CVC5ApiException)
  ASSERT_THROW(b.impTerm(Term()), CVC5ApiException)
  ASSERT_NO_THROW(b.impTerm(b))
  x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x")
  ASSERT_THROW(x.impTerm(b), CVC5ApiException)
  ASSERT_THROW(x.impTerm(x), CVC5ApiException)
  f = d_solver.mkVar(funSort1, "f")
  ASSERT_THROW(f.impTerm(b), CVC5ApiException)
  ASSERT_THROW(f.impTerm(x), CVC5ApiException)
  ASSERT_THROW(f.impTerm(f), CVC5ApiException)
  p = d_solver.mkVar(funSort2, "p")
  ASSERT_THROW(p.impTerm(b), CVC5ApiException)
  ASSERT_THROW(p.impTerm(x), CVC5ApiException)
  ASSERT_THROW(p.impTerm(f), CVC5ApiException)
  ASSERT_THROW(p.impTerm(p), CVC5ApiException)
  zero = d_solver.mkInteger(0)
  ASSERT_THROW(zero.impTerm(b), CVC5ApiException)
  ASSERT_THROW(zero.impTerm(x), CVC5ApiException)
  ASSERT_THROW(zero.impTerm(f), CVC5ApiException)
  ASSERT_THROW(zero.impTerm(p), CVC5ApiException)
  ASSERT_THROW(zero.impTerm(zero), CVC5ApiException)
  f_x = d_solver.mkTerm(APPLY_UF, f, x)
  ASSERT_THROW(f_x.impTerm(b), CVC5ApiException)
  ASSERT_THROW(f_x.impTerm(x), CVC5ApiException)
  ASSERT_THROW(f_x.impTerm(f), CVC5ApiException)
  ASSERT_THROW(f_x.impTerm(p), CVC5ApiException)
  ASSERT_THROW(f_x.impTerm(zero), CVC5ApiException)
  ASSERT_THROW(f_x.impTerm(f_x), CVC5ApiException)
  sum = d_solver.mkTerm(PLUS, f_x, f_x)
  ASSERT_THROW(sum.impTerm(b), CVC5ApiException)
  ASSERT_THROW(sum.impTerm(x), CVC5ApiException)
  ASSERT_THROW(sum.impTerm(f), CVC5ApiException)
  ASSERT_THROW(sum.impTerm(p), CVC5ApiException)
  ASSERT_THROW(sum.impTerm(zero), CVC5ApiException)
  ASSERT_THROW(sum.impTerm(f_x), CVC5ApiException)
  ASSERT_THROW(sum.impTerm(sum), CVC5ApiException)
  p_0 = d_solver.mkTerm(APPLY_UF, p, zero)
  ASSERT_NO_THROW(p_0.impTerm(b))
  ASSERT_THROW(p_0.impTerm(x), CVC5ApiException)
  ASSERT_THROW(p_0.impTerm(f), CVC5ApiException)
  ASSERT_THROW(p_0.impTerm(p), CVC5ApiException)
  ASSERT_THROW(p_0.impTerm(zero), CVC5ApiException)
  ASSERT_THROW(p_0.impTerm(f_x), CVC5ApiException)
  ASSERT_THROW(p_0.impTerm(sum), CVC5ApiException)
  ASSERT_NO_THROW(p_0.impTerm(p_0))
  p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x)
  ASSERT_NO_THROW(p_f_x.impTerm(b))
  ASSERT_THROW(p_f_x.impTerm(x), CVC5ApiException)
  ASSERT_THROW(p_f_x.impTerm(f), CVC5ApiException)
  ASSERT_THROW(p_f_x.impTerm(p), CVC5ApiException)
  ASSERT_THROW(p_f_x.impTerm(zero), CVC5ApiException)
  ASSERT_THROW(p_f_x.impTerm(f_x), CVC5ApiException)
  ASSERT_THROW(p_f_x.impTerm(sum), CVC5ApiException)
  ASSERT_NO_THROW(p_f_x.impTerm(p_0))
  ASSERT_NO_THROW(p_f_x.impTerm(p_f_x))

def test_iteTerm(solver):
  bvSort = d_solver.mkBitVectorSort(8)
  intSort = d_solver.getIntegerSort()
  boolSort = d_solver.getBooleanSort()
  funSort1 = d_solver.mkFunctionSort(bvSort, intSort)
  funSort2 = d_solver.mkFunctionSort(intSort, boolSort)

  b = d_solver.mkTrue()
  ASSERT_THROW(Term().iteTerm(b, b), CVC5ApiException)
  ASSERT_THROW(b.iteTerm(Term(), b), CVC5ApiException)
  ASSERT_THROW(b.iteTerm(b, Term()), CVC5ApiException)
  ASSERT_NO_THROW(b.iteTerm(b, b))
  x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x")
  ASSERT_NO_THROW(b.iteTerm(x, x))
  ASSERT_NO_THROW(b.iteTerm(b, b))
  ASSERT_THROW(b.iteTerm(x, b), CVC5ApiException)
  ASSERT_THROW(x.iteTerm(x, x), CVC5ApiException)
  ASSERT_THROW(x.iteTerm(x, b), CVC5ApiException)
  f = d_solver.mkVar(funSort1, "f")
  ASSERT_THROW(f.iteTerm(b, b), CVC5ApiException)
  ASSERT_THROW(x.iteTerm(b, x), CVC5ApiException)
  p = d_solver.mkVar(funSort2, "p")
  ASSERT_THROW(p.iteTerm(b, b), CVC5ApiException)
  ASSERT_THROW(p.iteTerm(x, b), CVC5ApiException)
  zero = d_solver.mkInteger(0)
  ASSERT_THROW(zero.iteTerm(x, x), CVC5ApiException)
  ASSERT_THROW(zero.iteTerm(x, b), CVC5ApiException)
  f_x = d_solver.mkTerm(APPLY_UF, f, x)
  ASSERT_THROW(f_x.iteTerm(b, b), CVC5ApiException)
  ASSERT_THROW(f_x.iteTerm(b, x), CVC5ApiException)
  sum = d_solver.mkTerm(PLUS, f_x, f_x)
  ASSERT_THROW(sum.iteTerm(x, x), CVC5ApiException)
  ASSERT_THROW(sum.iteTerm(b, x), CVC5ApiException)
  p_0 = d_solver.mkTerm(APPLY_UF, p, zero)
  ASSERT_NO_THROW(p_0.iteTerm(b, b))
  ASSERT_NO_THROW(p_0.iteTerm(x, x))
  ASSERT_THROW(p_0.iteTerm(x, b), CVC5ApiException)
  p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x)
  ASSERT_NO_THROW(p_f_x.iteTerm(b, b))
  ASSERT_NO_THROW(p_f_x.iteTerm(x, x))
  ASSERT_THROW(p_f_x.iteTerm(x, b), CVC5ApiException)

def test_termAssignment(solver):
  t1 = d_solver.mkInteger(1)
  t2 = t1
  t2 = d_solver.mkInteger(2)
  ASSERT_EQ(t1, d_solver.mkInteger(1))

def test_termCompare(solver):
  t1 = d_solver.mkInteger(1)
  t2 = d_solver.mkTerm(PLUS, d_solver.mkInteger(2), d_solver.mkInteger(2))
  t3 = d_solver.mkTerm(PLUS, d_solver.mkInteger(2), d_solver.mkInteger(2))
  ASSERT_TRUE(t2 >= t3)
  ASSERT_TRUE(t2 <= t3)
  ASSERT_TRUE((t1 > t2) != (t1 < t2))
  ASSERT_TRUE((t1 > t2 or t1 == t2) == (t1 >= t2))

def test_termChildren(solver):
  # simple term 2+3
  two = d_solver.mkInteger(2)
  t1 = d_solver.mkTerm(PLUS, two, d_solver.mkInteger(3))
  ASSERT_EQ(t1[0], two)
  ASSERT_EQ(t1.getNumChildren(), 2)
  tnull
  ASSERT_THROW(tnull.getNumChildren(), CVC5ApiException)

  # apply term f(2)
  intSort = d_solver.getIntegerSort()
  fsort = d_solver.mkFunctionSort(intSort, intSort)
  f = d_solver.mkConst(fsort, "f")
  t2 = d_solver.mkTerm(APPLY_UF, f, two)
  # due to our higher-order view of terms, we treat f as a child of APPLY_UF
  ASSERT_EQ(t2.getNumChildren(), 2)
  ASSERT_EQ(t2[0], f)
  ASSERT_EQ(t2[1], two)
  ASSERT_THROW(tnull[0], CVC5ApiException)

def test_getInteger(solver):
  int1 = d_solver.mkInteger("-18446744073709551616")
  int2 = d_solver.mkInteger("-18446744073709551615")
  int3 = d_solver.mkInteger("-4294967296")
  int4 = d_solver.mkInteger("-4294967295")
  int5 = d_solver.mkInteger("-10")
  int6 = d_solver.mkInteger("0")
  int7 = d_solver.mkInteger("10")
  int8 = d_solver.mkInteger("4294967295")
  int9 = d_solver.mkInteger("4294967296")
  int10 = d_solver.mkInteger("18446744073709551615")
  int11 = d_solver.mkInteger("18446744073709551616")
  int12 = d_solver.mkInteger("-0")

  ASSERT_THROW(d_solver.mkInteger(""), CVC5ApiException)
  ASSERT_THROW(d_solver.mkInteger("-"), CVC5ApiException)
  ASSERT_THROW(d_solver.mkInteger("-1-"), CVC5ApiException)
  ASSERT_THROW(d_solver.mkInteger("0.0"), CVC5ApiException)
  ASSERT_THROW(d_solver.mkInteger("-0.1"), CVC5ApiException)
  ASSERT_THROW(d_solver.mkInteger("012"), CVC5ApiException)
  ASSERT_THROW(d_solver.mkInteger("0000"), CVC5ApiException)
  ASSERT_THROW(d_solver.mkInteger("-01"), CVC5ApiException)
  ASSERT_THROW(d_solver.mkInteger("-00"), CVC5ApiException)

  ASSERT_TRUE( not int1.isInt32() and not int1.isUInt32() and not int1.isInt64() and not int1.isUInt64() and int1.isInteger())
  ASSERT_EQ(int1.getInteger(), "-18446744073709551616")
  ASSERT_TRUE(not int2.isInt32() and not int2.isUInt32() and not int2.isInt64() and not int2.isUInt64() and int2.isInteger())
  ASSERT_EQ(int2.getInteger(), "-18446744073709551615")
  ASSERT_TRUE(not int3.isInt32() and not int3.isUInt32() and int3.isInt64() and not int3.isUInt64() and int3.isInteger())
  ASSERT_EQ(int3.getInt64(), -4294967296)
  ASSERT_EQ(int3.getInteger(), "-4294967296")
  ASSERT_TRUE(not int4.isInt32() and not int4.isUInt32() and int4.isInt64() and not int4.isUInt64() and int4.isInteger())
  ASSERT_EQ(int4.getInt64(), -4294967295)
  ASSERT_EQ(int4.getInteger(), "-4294967295")
  ASSERT_TRUE(int5.isInt32() and not int5.isUInt32() and int5.isInt64()
              and not int5.isUInt64() and int5.isInteger())
  ASSERT_EQ(int5.getInt32(), -10)
  ASSERT_EQ(int5.getInt64(), -10)
  ASSERT_EQ(int5.getInteger(), "-10")
  ASSERT_TRUE(int6.isInt32() and int6.isUInt32() and int6.isInt64()
              and int6.isUInt64() and int6.isInteger())
  ASSERT_EQ(int6.getInt32(), 0)
  ASSERT_EQ(int6.getUInt32(), 0)
  ASSERT_EQ(int6.getInt64(), 0)
  ASSERT_EQ(int6.getUInt64(), 0)
  ASSERT_EQ(int6.getInteger(), "0")
  ASSERT_TRUE(int7.isInt32() and int7.isUInt32() and int7.isInt64()
              and int7.isUInt64() and int7.isInteger())
  ASSERT_EQ(int7.getInt32(), 10)
  ASSERT_EQ(int7.getUInt32(), 10)
  ASSERT_EQ(int7.getInt64(), 10)
  ASSERT_EQ(int7.getUInt64(), 10)
  ASSERT_EQ(int7.getInteger(), "10")
  ASSERT_TRUE(not int8.isInt32() and int8.isUInt32() and int8.isInt64() and int8.isUInt64() and int8.isInteger())
  ASSERT_EQ(int8.getUInt32(), 4294967295)
  ASSERT_EQ(int8.getInt64(), 4294967295)
  ASSERT_EQ(int8.getUInt64(), 4294967295)
  ASSERT_EQ(int8.getInteger(), "4294967295")
  ASSERT_TRUE(not int9.isInt32() and not int9.isUInt32() and int9.isInt64()
              and int9.isUInt64() and int9.isInteger())
  ASSERT_EQ(int9.getInt64(), 4294967296)
  ASSERT_EQ(int9.getUInt64(), 4294967296)
  ASSERT_EQ(int9.getInteger(), "4294967296")
  ASSERT_TRUE(not int10.isInt32() and not int10.isUInt32() and not int10.isInt64()
              and int10.isUInt64() and int10.isInteger())
  ASSERT_EQ(int10.getUInt64(), 18446744073709551615)
  ASSERT_EQ(int10.getInteger(), "18446744073709551615")
  ASSERT_TRUE(not int11.isInt32() and not int11.isUInt32() and not int11.isInt64()
              and not int11.isUInt64() and int11.isInteger())
  ASSERT_EQ(int11.getInteger(), "18446744073709551616")

def test_getString(solver):
  s1 = d_solver.mkString("abcde")
  ASSERT_TRUE(s1.isString())
  ASSERT_EQ(s1.getString(), "abcde")

def test_substitute(solver):
  x = d_solver.mkConst(d_solver.getIntegerSort(), "x")
  one = d_solver.mkInteger(1)
  ttrue = d_solver.mkTrue()
  xpx = d_solver.mkTerm(PLUS, x, x)
  onepone = d_solver.mkTerm(PLUS, one, one)

  ASSERT_EQ(xpx.substitute(x, one), onepone)
  ASSERT_EQ(onepone.substitute(one, x), xpx)
  # incorrect due to type
  ASSERT_THROW(xpx.substitute(one, ttrue), CVC5ApiException)

  # simultaneous substitution
  y = d_solver.mkConst(d_solver.getIntegerSort(), "y")
  xpy = d_solver.mkTerm(PLUS, x, y)
  xpone = d_solver.mkTerm(PLUS, y, one)
  es = list(Term)
  rs = list(Term)
  es.push_back(x)
  rs.push_back(y)
  es.push_back(y)
  rs.push_back(one)
  ASSERT_EQ(xpy.substitute(es, rs), xpone)

  # incorrect substitution due to arity
  rs.pop_back()
  ASSERT_THROW(xpy.substitute(es, rs), CVC5ApiException)

  # incorrect substitution due to types
  rs.push_back(ttrue)
  ASSERT_THROW(xpy.substitute(es, rs), CVC5ApiException)

  # null cannot substitute
  tnull
  ASSERT_THROW(tnull.substitute(one, x), CVC5ApiException)
  ASSERT_THROW(xpx.substitute(tnull, x), CVC5ApiException)
  ASSERT_THROW(xpx.substitute(x, tnull), CVC5ApiException)
  rs.pop_back()
  rs.push_back(tnull)
  ASSERT_THROW(xpy.substitute(es, rs), CVC5ApiException)
  es.clear()
  rs.clear()
  es.push_back(x)
  rs.push_back(y)
  ASSERT_THROW(tnull.substitute(es, rs), CVC5ApiException)
  es.push_back(tnull)
  rs.push_back(one)
  ASSERT_THROW(xpx.substitute(es, rs), CVC5ApiException)

def test_constArray(solver):
  intsort = d_solver.getIntegerSort()
  arrsort = d_solver.mkArraySort(intsort, intsort)
  a = d_solver.mkConst(arrsort, "a")
  one = d_solver.mkInteger(1)
  constarr = d_solver.mkConstArray(arrsort, one)

  ASSERT_EQ(constarr.getKind(), CONST_ARRAY)
  ASSERT_EQ(constarr.getConstArrayBase(), one)
  ASSERT_THROW(a.getConstArrayBase(), CVC5ApiException)

  arrsort =       d_solver.mkArraySort(d_solver.getRealSort(), d_solver.getRealSort())
  zero_array = d_solver.mkConstArray(arrsort, d_solver.mkReal(0))
  stores = d_solver.mkTerm(
      STORE, zero_array, d_solver.mkReal(1), d_solver.mkReal(2))
  stores =       d_solver.mkTerm(STORE, stores, d_solver.mkReal(2), d_solver.mkReal(3))
  stores =       d_solver.mkTerm(STORE, stores, d_solver.mkReal(4), d_solver.mkReal(5))

def test_constSequenceElements(solver):
  realsort = d_solver.getRealSort()
  seqsort = d_solver.mkSequenceSort(realsort)
  s = d_solver.mkEmptySequence(seqsort)

  ASSERT_EQ(s.getKind(), CONST_SEQUENCE)
  # empty sequence has zero elements
  cs = s.getConstSequenceElements()
  ASSERT_TRUE(cs.empty())

  # A seq.unit app is not a constant sequence (regardless of whether it is
  # applied to a constant).
  su = d_solver.mkTerm(SEQ_UNIT, d_solver.mkReal(1))
  ASSERT_THROW(su.getConstSequenceElements(), CVC5ApiException)

def test_termScopedToString(solver):
  intsort = d_solver.getIntegerSort()
  x = d_solver.mkConst(intsort, "x")
  ASSERT_EQ(x.toString(), "x")
  solver2 = pycvc4.Solver()
  ASSERT_EQ(x.toString(), "x")






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
#    fx = solver.mkTerm(kinds.ApplyUf, f, x)
#    assert fx.getKind() == kinds.ApplyUf
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
#    fx = solver.mkTerm(kinds.ApplyUf, f, x)
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
#    assert fx.getOp().getKind() == kinds.ApplyUf
#    # equivalent check
#    assert fx.getOp() == solver.mkOp(kinds.ApplyUf)
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
