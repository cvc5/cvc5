/*********************                                                        */
/*! \file term_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Makai Mann, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the Term class
 **/

#include "test_api.h"

namespace CVC4 {

using namespace api;

namespace test {

class TestApiTermBlack : public TestApi
{
};

TEST_F(TestApiTermBlack, eq)
{
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkVar(uSort, "x");
  Term y = d_solver.mkVar(uSort, "y");
  Term z;

  ASSERT_TRUE(x == x);
  ASSERT_FALSE(x != x);
  ASSERT_FALSE(x == y);
  ASSERT_TRUE(x != y);
  ASSERT_FALSE((x == z));
  ASSERT_TRUE(x != z);
}

TEST_F(TestApiTermBlack, getId)
{
  Term n;
  ASSERT_THROW(n.getId(), CVC4ApiException);
  Term x = d_solver.mkVar(d_solver.getIntegerSort(), "x");
  ASSERT_NO_THROW(x.getId());
  Term y = x;
  EXPECT_EQ(x.getId(), y.getId());

  Term z = d_solver.mkVar(d_solver.getIntegerSort(), "z");
  EXPECT_NE(x.getId(), z.getId());
}

TEST_F(TestApiTermBlack, getKind)
{
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(uSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  Term n;
  ASSERT_THROW(n.getKind(), CVC4ApiException);
  Term x = d_solver.mkVar(uSort, "x");
  ASSERT_NO_THROW(x.getKind());
  Term y = d_solver.mkVar(uSort, "y");
  ASSERT_NO_THROW(y.getKind());

  Term f = d_solver.mkVar(funSort1, "f");
  ASSERT_NO_THROW(f.getKind());
  Term p = d_solver.mkVar(funSort2, "p");
  ASSERT_NO_THROW(p.getKind());

  Term zero = d_solver.mkInteger(0);
  ASSERT_NO_THROW(zero.getKind());

  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  ASSERT_NO_THROW(f_x.getKind());
  Term f_y = d_solver.mkTerm(APPLY_UF, f, y);
  ASSERT_NO_THROW(f_y.getKind());
  Term sum = d_solver.mkTerm(PLUS, f_x, f_y);
  ASSERT_NO_THROW(sum.getKind());
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  ASSERT_NO_THROW(p_0.getKind());
  Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);
  ASSERT_NO_THROW(p_f_y.getKind());

  // Sequence kinds do not exist internally, test that the API properly
  // converts them back.
  Sort seqSort = d_solver.mkSequenceSort(intSort);
  Term s = d_solver.mkConst(seqSort, "s");
  Term ss = d_solver.mkTerm(SEQ_CONCAT, s, s);
  EXPECT_EQ(ss.getKind(), SEQ_CONCAT);
}

TEST_F(TestApiTermBlack, getSort)
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  Term n;
  ASSERT_THROW(n.getSort(), CVC4ApiException);
  Term x = d_solver.mkVar(bvSort, "x");
  ASSERT_NO_THROW(x.getSort());
  EXPECT_EQ(x.getSort(), bvSort);
  Term y = d_solver.mkVar(bvSort, "y");
  ASSERT_NO_THROW(y.getSort());
  EXPECT_EQ(y.getSort(), bvSort);

  Term f = d_solver.mkVar(funSort1, "f");
  ASSERT_NO_THROW(f.getSort());
  EXPECT_EQ(f.getSort(), funSort1);
  Term p = d_solver.mkVar(funSort2, "p");
  ASSERT_NO_THROW(p.getSort());
  EXPECT_EQ(p.getSort(), funSort2);

  Term zero = d_solver.mkInteger(0);
  ASSERT_NO_THROW(zero.getSort());
  EXPECT_EQ(zero.getSort(), intSort);

  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  ASSERT_NO_THROW(f_x.getSort());
  EXPECT_EQ(f_x.getSort(), intSort);
  Term f_y = d_solver.mkTerm(APPLY_UF, f, y);
  ASSERT_NO_THROW(f_y.getSort());
  EXPECT_EQ(f_y.getSort(), intSort);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_y);
  ASSERT_NO_THROW(sum.getSort());
  EXPECT_EQ(sum.getSort(), intSort);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  ASSERT_NO_THROW(p_0.getSort());
  EXPECT_EQ(p_0.getSort(), boolSort);
  Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);
  ASSERT_NO_THROW(p_f_y.getSort());
  EXPECT_EQ(p_f_y.getSort(), boolSort);
}

TEST_F(TestApiTermBlack, getOp)
{
  Sort intsort = d_solver.getIntegerSort();
  Sort bvsort = d_solver.mkBitVectorSort(8);
  Sort arrsort = d_solver.mkArraySort(bvsort, intsort);
  Sort funsort = d_solver.mkFunctionSort(intsort, bvsort);

  Term x = d_solver.mkConst(intsort, "x");
  Term a = d_solver.mkConst(arrsort, "a");
  Term b = d_solver.mkConst(bvsort, "b");

  ASSERT_FALSE(x.hasOp());
  ASSERT_THROW(x.getOp(), CVC4ApiException);

  Term ab = d_solver.mkTerm(SELECT, a, b);
  Op ext = d_solver.mkOp(BITVECTOR_EXTRACT, 4, 0);
  Term extb = d_solver.mkTerm(ext, b);

  ASSERT_TRUE(ab.hasOp());
  EXPECT_EQ(ab.getOp(), Op(&d_solver, SELECT));
  ASSERT_FALSE(ab.getOp().isIndexed());
  // can compare directly to a Kind (will invoke Op constructor)
  EXPECT_EQ(ab.getOp(), Op(&d_solver, SELECT));
  ASSERT_TRUE(extb.hasOp());
  ASSERT_TRUE(extb.getOp().isIndexed());
  EXPECT_EQ(extb.getOp(), ext);

  Term f = d_solver.mkConst(funsort, "f");
  Term fx = d_solver.mkTerm(APPLY_UF, f, x);

  ASSERT_FALSE(f.hasOp());
  ASSERT_THROW(f.getOp(), CVC4ApiException);
  ASSERT_TRUE(fx.hasOp());
  EXPECT_EQ(fx.getOp(), Op(&d_solver, APPLY_UF));
  std::vector<Term> children(fx.begin(), fx.end());
  // testing rebuild from op and children
  EXPECT_EQ(fx, d_solver.mkTerm(fx.getOp(), children));

  // Test Datatypes Ops
  Sort sort = d_solver.mkParamSort("T");
  DatatypeDecl listDecl = d_solver.mkDatatypeDecl("paramlist", sort);
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  cons.addSelector("head", sort);
  cons.addSelectorSelf("tail");
  listDecl.addConstructor(cons);
  listDecl.addConstructor(nil);
  Sort listSort = d_solver.mkDatatypeSort(listDecl);
  Sort intListSort =
      listSort.instantiate(std::vector<Sort>{d_solver.getIntegerSort()});
  Term c = d_solver.mkConst(intListSort, "c");
  Datatype list = listSort.getDatatype();
  // list datatype constructor and selector operator terms
  Term consOpTerm = list.getConstructorTerm("cons");
  Term nilOpTerm = list.getConstructorTerm("nil");
  Term headOpTerm = list["cons"].getSelectorTerm("head");
  Term tailOpTerm = list["cons"].getSelectorTerm("tail");

  Term nilTerm = d_solver.mkTerm(APPLY_CONSTRUCTOR, nilOpTerm);
  Term consTerm = d_solver.mkTerm(
      APPLY_CONSTRUCTOR, consOpTerm, d_solver.mkInteger(0), nilTerm);
  Term headTerm = d_solver.mkTerm(APPLY_SELECTOR, headOpTerm, consTerm);
  Term tailTerm = d_solver.mkTerm(APPLY_SELECTOR, tailOpTerm, consTerm);

  ASSERT_TRUE(nilTerm.hasOp());
  ASSERT_TRUE(consTerm.hasOp());
  ASSERT_TRUE(headTerm.hasOp());
  ASSERT_TRUE(tailTerm.hasOp());

  EXPECT_EQ(nilTerm.getOp(), Op(&d_solver, APPLY_CONSTRUCTOR));
  EXPECT_EQ(consTerm.getOp(), Op(&d_solver, APPLY_CONSTRUCTOR));
  EXPECT_EQ(headTerm.getOp(), Op(&d_solver, APPLY_SELECTOR));
  EXPECT_EQ(tailTerm.getOp(), Op(&d_solver, APPLY_SELECTOR));

  // Test rebuilding
  children.clear();
  children.insert(children.begin(), headTerm.begin(), headTerm.end());
  EXPECT_EQ(headTerm, d_solver.mkTerm(headTerm.getOp(), children));
}

TEST_F(TestApiTermBlack, isNull)
{
  Term x;
  ASSERT_TRUE(x.isNull());
  x = d_solver.mkVar(d_solver.mkBitVectorSort(4), "x");
  ASSERT_FALSE(x.isNull());
}

TEST_F(TestApiTermBlack, notTerm)
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  ASSERT_THROW(Term().notTerm(), CVC4ApiException);
  Term b = d_solver.mkTrue();
  ASSERT_NO_THROW(b.notTerm());
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  ASSERT_THROW(x.notTerm(), CVC4ApiException);
  Term f = d_solver.mkVar(funSort1, "f");
  ASSERT_THROW(f.notTerm(), CVC4ApiException);
  Term p = d_solver.mkVar(funSort2, "p");
  ASSERT_THROW(p.notTerm(), CVC4ApiException);
  Term zero = d_solver.mkInteger(0);
  ASSERT_THROW(zero.notTerm(), CVC4ApiException);
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  ASSERT_THROW(f_x.notTerm(), CVC4ApiException);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
  ASSERT_THROW(sum.notTerm(), CVC4ApiException);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  ASSERT_NO_THROW(p_0.notTerm());
  Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
  ASSERT_NO_THROW(p_f_x.notTerm());
}

TEST_F(TestApiTermBlack, andTerm)
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  Term b = d_solver.mkTrue();
  ASSERT_THROW(Term().andTerm(b), CVC4ApiException);
  ASSERT_THROW(b.andTerm(Term()), CVC4ApiException);
  ASSERT_NO_THROW(b.andTerm(b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  ASSERT_THROW(x.andTerm(b), CVC4ApiException);
  ASSERT_THROW(x.andTerm(x), CVC4ApiException);
  Term f = d_solver.mkVar(funSort1, "f");
  ASSERT_THROW(f.andTerm(b), CVC4ApiException);
  ASSERT_THROW(f.andTerm(x), CVC4ApiException);
  ASSERT_THROW(f.andTerm(f), CVC4ApiException);
  Term p = d_solver.mkVar(funSort2, "p");
  ASSERT_THROW(p.andTerm(b), CVC4ApiException);
  ASSERT_THROW(p.andTerm(x), CVC4ApiException);
  ASSERT_THROW(p.andTerm(f), CVC4ApiException);
  ASSERT_THROW(p.andTerm(p), CVC4ApiException);
  Term zero = d_solver.mkInteger(0);
  ASSERT_THROW(zero.andTerm(b), CVC4ApiException);
  ASSERT_THROW(zero.andTerm(x), CVC4ApiException);
  ASSERT_THROW(zero.andTerm(f), CVC4ApiException);
  ASSERT_THROW(zero.andTerm(p), CVC4ApiException);
  ASSERT_THROW(zero.andTerm(zero), CVC4ApiException);
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  ASSERT_THROW(f_x.andTerm(b), CVC4ApiException);
  ASSERT_THROW(f_x.andTerm(x), CVC4ApiException);
  ASSERT_THROW(f_x.andTerm(f), CVC4ApiException);
  ASSERT_THROW(f_x.andTerm(p), CVC4ApiException);
  ASSERT_THROW(f_x.andTerm(zero), CVC4ApiException);
  ASSERT_THROW(f_x.andTerm(f_x), CVC4ApiException);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
  ASSERT_THROW(sum.andTerm(b), CVC4ApiException);
  ASSERT_THROW(sum.andTerm(x), CVC4ApiException);
  ASSERT_THROW(sum.andTerm(f), CVC4ApiException);
  ASSERT_THROW(sum.andTerm(p), CVC4ApiException);
  ASSERT_THROW(sum.andTerm(zero), CVC4ApiException);
  ASSERT_THROW(sum.andTerm(f_x), CVC4ApiException);
  ASSERT_THROW(sum.andTerm(sum), CVC4ApiException);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  ASSERT_NO_THROW(p_0.andTerm(b));
  ASSERT_THROW(p_0.andTerm(x), CVC4ApiException);
  ASSERT_THROW(p_0.andTerm(f), CVC4ApiException);
  ASSERT_THROW(p_0.andTerm(p), CVC4ApiException);
  ASSERT_THROW(p_0.andTerm(zero), CVC4ApiException);
  ASSERT_THROW(p_0.andTerm(f_x), CVC4ApiException);
  ASSERT_THROW(p_0.andTerm(sum), CVC4ApiException);
  ASSERT_NO_THROW(p_0.andTerm(p_0));
  Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
  ASSERT_NO_THROW(p_f_x.andTerm(b));
  ASSERT_THROW(p_f_x.andTerm(x), CVC4ApiException);
  ASSERT_THROW(p_f_x.andTerm(f), CVC4ApiException);
  ASSERT_THROW(p_f_x.andTerm(p), CVC4ApiException);
  ASSERT_THROW(p_f_x.andTerm(zero), CVC4ApiException);
  ASSERT_THROW(p_f_x.andTerm(f_x), CVC4ApiException);
  ASSERT_THROW(p_f_x.andTerm(sum), CVC4ApiException);
  ASSERT_NO_THROW(p_f_x.andTerm(p_0));
  ASSERT_NO_THROW(p_f_x.andTerm(p_f_x));
}

TEST_F(TestApiTermBlack, orTerm)
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  Term b = d_solver.mkTrue();
  ASSERT_THROW(Term().orTerm(b), CVC4ApiException);
  ASSERT_THROW(b.orTerm(Term()), CVC4ApiException);
  ASSERT_NO_THROW(b.orTerm(b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  ASSERT_THROW(x.orTerm(b), CVC4ApiException);
  ASSERT_THROW(x.orTerm(x), CVC4ApiException);
  Term f = d_solver.mkVar(funSort1, "f");
  ASSERT_THROW(f.orTerm(b), CVC4ApiException);
  ASSERT_THROW(f.orTerm(x), CVC4ApiException);
  ASSERT_THROW(f.orTerm(f), CVC4ApiException);
  Term p = d_solver.mkVar(funSort2, "p");
  ASSERT_THROW(p.orTerm(b), CVC4ApiException);
  ASSERT_THROW(p.orTerm(x), CVC4ApiException);
  ASSERT_THROW(p.orTerm(f), CVC4ApiException);
  ASSERT_THROW(p.orTerm(p), CVC4ApiException);
  Term zero = d_solver.mkInteger(0);
  ASSERT_THROW(zero.orTerm(b), CVC4ApiException);
  ASSERT_THROW(zero.orTerm(x), CVC4ApiException);
  ASSERT_THROW(zero.orTerm(f), CVC4ApiException);
  ASSERT_THROW(zero.orTerm(p), CVC4ApiException);
  ASSERT_THROW(zero.orTerm(zero), CVC4ApiException);
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  ASSERT_THROW(f_x.orTerm(b), CVC4ApiException);
  ASSERT_THROW(f_x.orTerm(x), CVC4ApiException);
  ASSERT_THROW(f_x.orTerm(f), CVC4ApiException);
  ASSERT_THROW(f_x.orTerm(p), CVC4ApiException);
  ASSERT_THROW(f_x.orTerm(zero), CVC4ApiException);
  ASSERT_THROW(f_x.orTerm(f_x), CVC4ApiException);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
  ASSERT_THROW(sum.orTerm(b), CVC4ApiException);
  ASSERT_THROW(sum.orTerm(x), CVC4ApiException);
  ASSERT_THROW(sum.orTerm(f), CVC4ApiException);
  ASSERT_THROW(sum.orTerm(p), CVC4ApiException);
  ASSERT_THROW(sum.orTerm(zero), CVC4ApiException);
  ASSERT_THROW(sum.orTerm(f_x), CVC4ApiException);
  ASSERT_THROW(sum.orTerm(sum), CVC4ApiException);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  ASSERT_NO_THROW(p_0.orTerm(b));
  ASSERT_THROW(p_0.orTerm(x), CVC4ApiException);
  ASSERT_THROW(p_0.orTerm(f), CVC4ApiException);
  ASSERT_THROW(p_0.orTerm(p), CVC4ApiException);
  ASSERT_THROW(p_0.orTerm(zero), CVC4ApiException);
  ASSERT_THROW(p_0.orTerm(f_x), CVC4ApiException);
  ASSERT_THROW(p_0.orTerm(sum), CVC4ApiException);
  ASSERT_NO_THROW(p_0.orTerm(p_0));
  Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
  ASSERT_NO_THROW(p_f_x.orTerm(b));
  ASSERT_THROW(p_f_x.orTerm(x), CVC4ApiException);
  ASSERT_THROW(p_f_x.orTerm(f), CVC4ApiException);
  ASSERT_THROW(p_f_x.orTerm(p), CVC4ApiException);
  ASSERT_THROW(p_f_x.orTerm(zero), CVC4ApiException);
  ASSERT_THROW(p_f_x.orTerm(f_x), CVC4ApiException);
  ASSERT_THROW(p_f_x.orTerm(sum), CVC4ApiException);
  ASSERT_NO_THROW(p_f_x.orTerm(p_0));
  ASSERT_NO_THROW(p_f_x.orTerm(p_f_x));
}

TEST_F(TestApiTermBlack, xorTerm)
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  Term b = d_solver.mkTrue();
  ASSERT_THROW(Term().xorTerm(b), CVC4ApiException);
  ASSERT_THROW(b.xorTerm(Term()), CVC4ApiException);
  ASSERT_NO_THROW(b.xorTerm(b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  ASSERT_THROW(x.xorTerm(b), CVC4ApiException);
  ASSERT_THROW(x.xorTerm(x), CVC4ApiException);
  Term f = d_solver.mkVar(funSort1, "f");
  ASSERT_THROW(f.xorTerm(b), CVC4ApiException);
  ASSERT_THROW(f.xorTerm(x), CVC4ApiException);
  ASSERT_THROW(f.xorTerm(f), CVC4ApiException);
  Term p = d_solver.mkVar(funSort2, "p");
  ASSERT_THROW(p.xorTerm(b), CVC4ApiException);
  ASSERT_THROW(p.xorTerm(x), CVC4ApiException);
  ASSERT_THROW(p.xorTerm(f), CVC4ApiException);
  ASSERT_THROW(p.xorTerm(p), CVC4ApiException);
  Term zero = d_solver.mkInteger(0);
  ASSERT_THROW(zero.xorTerm(b), CVC4ApiException);
  ASSERT_THROW(zero.xorTerm(x), CVC4ApiException);
  ASSERT_THROW(zero.xorTerm(f), CVC4ApiException);
  ASSERT_THROW(zero.xorTerm(p), CVC4ApiException);
  ASSERT_THROW(zero.xorTerm(zero), CVC4ApiException);
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  ASSERT_THROW(f_x.xorTerm(b), CVC4ApiException);
  ASSERT_THROW(f_x.xorTerm(x), CVC4ApiException);
  ASSERT_THROW(f_x.xorTerm(f), CVC4ApiException);
  ASSERT_THROW(f_x.xorTerm(p), CVC4ApiException);
  ASSERT_THROW(f_x.xorTerm(zero), CVC4ApiException);
  ASSERT_THROW(f_x.xorTerm(f_x), CVC4ApiException);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
  ASSERT_THROW(sum.xorTerm(b), CVC4ApiException);
  ASSERT_THROW(sum.xorTerm(x), CVC4ApiException);
  ASSERT_THROW(sum.xorTerm(f), CVC4ApiException);
  ASSERT_THROW(sum.xorTerm(p), CVC4ApiException);
  ASSERT_THROW(sum.xorTerm(zero), CVC4ApiException);
  ASSERT_THROW(sum.xorTerm(f_x), CVC4ApiException);
  ASSERT_THROW(sum.xorTerm(sum), CVC4ApiException);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  ASSERT_NO_THROW(p_0.xorTerm(b));
  ASSERT_THROW(p_0.xorTerm(x), CVC4ApiException);
  ASSERT_THROW(p_0.xorTerm(f), CVC4ApiException);
  ASSERT_THROW(p_0.xorTerm(p), CVC4ApiException);
  ASSERT_THROW(p_0.xorTerm(zero), CVC4ApiException);
  ASSERT_THROW(p_0.xorTerm(f_x), CVC4ApiException);
  ASSERT_THROW(p_0.xorTerm(sum), CVC4ApiException);
  ASSERT_NO_THROW(p_0.xorTerm(p_0));
  Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
  ASSERT_NO_THROW(p_f_x.xorTerm(b));
  ASSERT_THROW(p_f_x.xorTerm(x), CVC4ApiException);
  ASSERT_THROW(p_f_x.xorTerm(f), CVC4ApiException);
  ASSERT_THROW(p_f_x.xorTerm(p), CVC4ApiException);
  ASSERT_THROW(p_f_x.xorTerm(zero), CVC4ApiException);
  ASSERT_THROW(p_f_x.xorTerm(f_x), CVC4ApiException);
  ASSERT_THROW(p_f_x.xorTerm(sum), CVC4ApiException);
  ASSERT_NO_THROW(p_f_x.xorTerm(p_0));
  ASSERT_NO_THROW(p_f_x.xorTerm(p_f_x));
}

TEST_F(TestApiTermBlack, eqTerm)
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  Term b = d_solver.mkTrue();
  ASSERT_THROW(Term().eqTerm(b), CVC4ApiException);
  ASSERT_THROW(b.eqTerm(Term()), CVC4ApiException);
  ASSERT_NO_THROW(b.eqTerm(b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  ASSERT_THROW(x.eqTerm(b), CVC4ApiException);
  ASSERT_NO_THROW(x.eqTerm(x));
  Term f = d_solver.mkVar(funSort1, "f");
  ASSERT_THROW(f.eqTerm(b), CVC4ApiException);
  ASSERT_THROW(f.eqTerm(x), CVC4ApiException);
  ASSERT_NO_THROW(f.eqTerm(f));
  Term p = d_solver.mkVar(funSort2, "p");
  ASSERT_THROW(p.eqTerm(b), CVC4ApiException);
  ASSERT_THROW(p.eqTerm(x), CVC4ApiException);
  ASSERT_THROW(p.eqTerm(f), CVC4ApiException);
  ASSERT_NO_THROW(p.eqTerm(p));
  Term zero = d_solver.mkInteger(0);
  ASSERT_THROW(zero.eqTerm(b), CVC4ApiException);
  ASSERT_THROW(zero.eqTerm(x), CVC4ApiException);
  ASSERT_THROW(zero.eqTerm(f), CVC4ApiException);
  ASSERT_THROW(zero.eqTerm(p), CVC4ApiException);
  ASSERT_NO_THROW(zero.eqTerm(zero));
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  ASSERT_THROW(f_x.eqTerm(b), CVC4ApiException);
  ASSERT_THROW(f_x.eqTerm(x), CVC4ApiException);
  ASSERT_THROW(f_x.eqTerm(f), CVC4ApiException);
  ASSERT_THROW(f_x.eqTerm(p), CVC4ApiException);
  ASSERT_NO_THROW(f_x.eqTerm(zero));
  ASSERT_NO_THROW(f_x.eqTerm(f_x));
  Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
  ASSERT_THROW(sum.eqTerm(b), CVC4ApiException);
  ASSERT_THROW(sum.eqTerm(x), CVC4ApiException);
  ASSERT_THROW(sum.eqTerm(f), CVC4ApiException);
  ASSERT_THROW(sum.eqTerm(p), CVC4ApiException);
  ASSERT_NO_THROW(sum.eqTerm(zero));
  ASSERT_NO_THROW(sum.eqTerm(f_x));
  ASSERT_NO_THROW(sum.eqTerm(sum));
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  ASSERT_NO_THROW(p_0.eqTerm(b));
  ASSERT_THROW(p_0.eqTerm(x), CVC4ApiException);
  ASSERT_THROW(p_0.eqTerm(f), CVC4ApiException);
  ASSERT_THROW(p_0.eqTerm(p), CVC4ApiException);
  ASSERT_THROW(p_0.eqTerm(zero), CVC4ApiException);
  ASSERT_THROW(p_0.eqTerm(f_x), CVC4ApiException);
  ASSERT_THROW(p_0.eqTerm(sum), CVC4ApiException);
  ASSERT_NO_THROW(p_0.eqTerm(p_0));
  Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
  ASSERT_NO_THROW(p_f_x.eqTerm(b));
  ASSERT_THROW(p_f_x.eqTerm(x), CVC4ApiException);
  ASSERT_THROW(p_f_x.eqTerm(f), CVC4ApiException);
  ASSERT_THROW(p_f_x.eqTerm(p), CVC4ApiException);
  ASSERT_THROW(p_f_x.eqTerm(zero), CVC4ApiException);
  ASSERT_THROW(p_f_x.eqTerm(f_x), CVC4ApiException);
  ASSERT_THROW(p_f_x.eqTerm(sum), CVC4ApiException);
  ASSERT_NO_THROW(p_f_x.eqTerm(p_0));
  ASSERT_NO_THROW(p_f_x.eqTerm(p_f_x));
}

TEST_F(TestApiTermBlack, impTerm)
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  Term b = d_solver.mkTrue();
  ASSERT_THROW(Term().impTerm(b), CVC4ApiException);
  ASSERT_THROW(b.impTerm(Term()), CVC4ApiException);
  ASSERT_NO_THROW(b.impTerm(b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  ASSERT_THROW(x.impTerm(b), CVC4ApiException);
  ASSERT_THROW(x.impTerm(x), CVC4ApiException);
  Term f = d_solver.mkVar(funSort1, "f");
  ASSERT_THROW(f.impTerm(b), CVC4ApiException);
  ASSERT_THROW(f.impTerm(x), CVC4ApiException);
  ASSERT_THROW(f.impTerm(f), CVC4ApiException);
  Term p = d_solver.mkVar(funSort2, "p");
  ASSERT_THROW(p.impTerm(b), CVC4ApiException);
  ASSERT_THROW(p.impTerm(x), CVC4ApiException);
  ASSERT_THROW(p.impTerm(f), CVC4ApiException);
  ASSERT_THROW(p.impTerm(p), CVC4ApiException);
  Term zero = d_solver.mkInteger(0);
  ASSERT_THROW(zero.impTerm(b), CVC4ApiException);
  ASSERT_THROW(zero.impTerm(x), CVC4ApiException);
  ASSERT_THROW(zero.impTerm(f), CVC4ApiException);
  ASSERT_THROW(zero.impTerm(p), CVC4ApiException);
  ASSERT_THROW(zero.impTerm(zero), CVC4ApiException);
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  ASSERT_THROW(f_x.impTerm(b), CVC4ApiException);
  ASSERT_THROW(f_x.impTerm(x), CVC4ApiException);
  ASSERT_THROW(f_x.impTerm(f), CVC4ApiException);
  ASSERT_THROW(f_x.impTerm(p), CVC4ApiException);
  ASSERT_THROW(f_x.impTerm(zero), CVC4ApiException);
  ASSERT_THROW(f_x.impTerm(f_x), CVC4ApiException);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
  ASSERT_THROW(sum.impTerm(b), CVC4ApiException);
  ASSERT_THROW(sum.impTerm(x), CVC4ApiException);
  ASSERT_THROW(sum.impTerm(f), CVC4ApiException);
  ASSERT_THROW(sum.impTerm(p), CVC4ApiException);
  ASSERT_THROW(sum.impTerm(zero), CVC4ApiException);
  ASSERT_THROW(sum.impTerm(f_x), CVC4ApiException);
  ASSERT_THROW(sum.impTerm(sum), CVC4ApiException);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  ASSERT_NO_THROW(p_0.impTerm(b));
  ASSERT_THROW(p_0.impTerm(x), CVC4ApiException);
  ASSERT_THROW(p_0.impTerm(f), CVC4ApiException);
  ASSERT_THROW(p_0.impTerm(p), CVC4ApiException);
  ASSERT_THROW(p_0.impTerm(zero), CVC4ApiException);
  ASSERT_THROW(p_0.impTerm(f_x), CVC4ApiException);
  ASSERT_THROW(p_0.impTerm(sum), CVC4ApiException);
  ASSERT_NO_THROW(p_0.impTerm(p_0));
  Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
  ASSERT_NO_THROW(p_f_x.impTerm(b));
  ASSERT_THROW(p_f_x.impTerm(x), CVC4ApiException);
  ASSERT_THROW(p_f_x.impTerm(f), CVC4ApiException);
  ASSERT_THROW(p_f_x.impTerm(p), CVC4ApiException);
  ASSERT_THROW(p_f_x.impTerm(zero), CVC4ApiException);
  ASSERT_THROW(p_f_x.impTerm(f_x), CVC4ApiException);
  ASSERT_THROW(p_f_x.impTerm(sum), CVC4ApiException);
  ASSERT_NO_THROW(p_f_x.impTerm(p_0));
  ASSERT_NO_THROW(p_f_x.impTerm(p_f_x));
}

TEST_F(TestApiTermBlack, iteTerm)
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  Term b = d_solver.mkTrue();
  ASSERT_THROW(Term().iteTerm(b, b), CVC4ApiException);
  ASSERT_THROW(b.iteTerm(Term(), b), CVC4ApiException);
  ASSERT_THROW(b.iteTerm(b, Term()), CVC4ApiException);
  ASSERT_NO_THROW(b.iteTerm(b, b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  ASSERT_NO_THROW(b.iteTerm(x, x));
  ASSERT_NO_THROW(b.iteTerm(b, b));
  ASSERT_THROW(b.iteTerm(x, b), CVC4ApiException);
  ASSERT_THROW(x.iteTerm(x, x), CVC4ApiException);
  ASSERT_THROW(x.iteTerm(x, b), CVC4ApiException);
  Term f = d_solver.mkVar(funSort1, "f");
  ASSERT_THROW(f.iteTerm(b, b), CVC4ApiException);
  ASSERT_THROW(x.iteTerm(b, x), CVC4ApiException);
  Term p = d_solver.mkVar(funSort2, "p");
  ASSERT_THROW(p.iteTerm(b, b), CVC4ApiException);
  ASSERT_THROW(p.iteTerm(x, b), CVC4ApiException);
  Term zero = d_solver.mkInteger(0);
  ASSERT_THROW(zero.iteTerm(x, x), CVC4ApiException);
  ASSERT_THROW(zero.iteTerm(x, b), CVC4ApiException);
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  ASSERT_THROW(f_x.iteTerm(b, b), CVC4ApiException);
  ASSERT_THROW(f_x.iteTerm(b, x), CVC4ApiException);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
  ASSERT_THROW(sum.iteTerm(x, x), CVC4ApiException);
  ASSERT_THROW(sum.iteTerm(b, x), CVC4ApiException);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  ASSERT_NO_THROW(p_0.iteTerm(b, b));
  ASSERT_NO_THROW(p_0.iteTerm(x, x));
  ASSERT_THROW(p_0.iteTerm(x, b), CVC4ApiException);
  Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
  ASSERT_NO_THROW(p_f_x.iteTerm(b, b));
  ASSERT_NO_THROW(p_f_x.iteTerm(x, x));
  ASSERT_THROW(p_f_x.iteTerm(x, b), CVC4ApiException);
}

TEST_F(TestApiTermBlack, termAssignment)
{
  Term t1 = d_solver.mkInteger(1);
  Term t2 = t1;
  t2 = d_solver.mkInteger(2);
  EXPECT_EQ(t1, d_solver.mkInteger(1));
}

TEST_F(TestApiTermBlack, termCompare)
{
  Term t1 = d_solver.mkInteger(1);
  Term t2 = d_solver.mkTerm(PLUS, d_solver.mkInteger(2), d_solver.mkInteger(2));
  Term t3 = d_solver.mkTerm(PLUS, d_solver.mkInteger(2), d_solver.mkInteger(2));
  ASSERT_TRUE(t2 >= t3);
  ASSERT_TRUE(t2 <= t3);
  ASSERT_TRUE((t1 > t2) != (t1 < t2));
  ASSERT_TRUE((t1 > t2 || t1 == t2) == (t1 >= t2));
}

TEST_F(TestApiTermBlack, termChildren)
{
  // simple term 2+3
  Term two = d_solver.mkInteger(2);
  Term t1 = d_solver.mkTerm(PLUS, two, d_solver.mkInteger(3));
  EXPECT_EQ(t1[0], two);
  EXPECT_EQ(t1.getNumChildren(), 2);
  Term tnull;
  ASSERT_THROW(tnull.getNumChildren(), CVC4ApiException);

  // apply term f(2)
  Sort intSort = d_solver.getIntegerSort();
  Sort fsort = d_solver.mkFunctionSort(intSort, intSort);
  Term f = d_solver.mkConst(fsort, "f");
  Term t2 = d_solver.mkTerm(APPLY_UF, f, two);
  // due to our higher-order view of terms, we treat f as a child of APPLY_UF
  ASSERT_EQ(t2.getNumChildren(), 2);
  EXPECT_EQ(t2[0], f);
  EXPECT_EQ(t2[1], two);
  ASSERT_THROW(tnull[0], CVC4ApiException);
}

TEST_F(TestApiTermBlack, getInteger)
{
  Term int1 = d_solver.mkInteger("-18446744073709551616");
  Term int2 = d_solver.mkInteger("-18446744073709551615");
  Term int3 = d_solver.mkInteger("-4294967296");
  Term int4 = d_solver.mkInteger("-4294967295");
  Term int5 = d_solver.mkInteger("-10");
  Term int6 = d_solver.mkInteger("0");
  Term int7 = d_solver.mkInteger("10");
  Term int8 = d_solver.mkInteger("4294967295");
  Term int9 = d_solver.mkInteger("4294967296");
  Term int10 = d_solver.mkInteger("18446744073709551615");
  Term int11 = d_solver.mkInteger("18446744073709551616");

  EXPECT_TRUE(!int1.isInt32() && !int1.isUInt32() && !int1.isInt64()
              && !int1.isUInt64() && int1.isInteger());
  EXPECT_EQ(int1.getInteger(), "-18446744073709551616");
  EXPECT_TRUE(!int2.isInt32() && !int2.isUInt32() && !int2.isInt64()
              && !int2.isUInt64() && int2.isInteger());
  EXPECT_EQ(int2.getInteger(), "-18446744073709551615");
  EXPECT_TRUE(!int3.isInt32() && !int3.isUInt32() && int3.isInt64()
              && !int3.isUInt64() && int3.isInteger());
  EXPECT_EQ(int3.getInt64(), -4294967296);
  EXPECT_EQ(int3.getInteger(), "-4294967296");
  EXPECT_TRUE(!int4.isInt32() && !int4.isUInt32() && int4.isInt64()
              && !int4.isUInt64() && int4.isInteger());
  EXPECT_EQ(int4.getInt64(), -4294967295);
  EXPECT_EQ(int4.getInteger(), "-4294967295");
  EXPECT_TRUE(int5.isInt32() && !int5.isUInt32() && int5.isInt64()
              && !int5.isUInt64() && int5.isInteger());
  EXPECT_EQ(int5.getInt32(), -10);
  EXPECT_EQ(int5.getInt64(), -10);
  EXPECT_EQ(int5.getInteger(), "-10");
  EXPECT_TRUE(int6.isInt32() && int6.isUInt32() && int6.isInt64()
              && int6.isUInt64() && int6.isInteger());
  EXPECT_EQ(int6.getInt32(), 0);
  EXPECT_EQ(int6.getUInt32(), 0);
  EXPECT_EQ(int6.getInt64(), 0);
  EXPECT_EQ(int6.getUInt64(), 0);
  EXPECT_EQ(int6.getInteger(), "0");
  EXPECT_TRUE(int7.isInt32() && int7.isUInt32() && int7.isInt64()
              && int7.isUInt64() && int7.isInteger());
  EXPECT_EQ(int7.getInt32(), 10);
  EXPECT_EQ(int7.getUInt32(), 10);
  EXPECT_EQ(int7.getInt64(), 10);
  EXPECT_EQ(int7.getUInt64(), 10);
  EXPECT_EQ(int7.getInteger(), "10");
  EXPECT_TRUE(!int8.isInt32() && int8.isUInt32() && int8.isInt64()
              && int8.isUInt64() && int8.isInteger());
  EXPECT_EQ(int8.getUInt32(), 4294967295);
  EXPECT_EQ(int8.getInt64(), 4294967295);
  EXPECT_EQ(int8.getUInt64(), 4294967295);
  EXPECT_EQ(int8.getInteger(), "4294967295");
  EXPECT_TRUE(!int9.isInt32() && !int9.isUInt32() && int9.isInt64()
              && int9.isUInt64() && int9.isInteger());
  EXPECT_EQ(int9.getInt64(), 4294967296);
  EXPECT_EQ(int9.getUInt64(), 4294967296);
  EXPECT_EQ(int9.getInteger(), "4294967296");
  EXPECT_TRUE(!int10.isInt32() && !int10.isUInt32() && !int10.isInt64()
              && int10.isUInt64() && int10.isInteger());
  EXPECT_EQ(int10.getUInt64(), 18446744073709551615ull);
  EXPECT_EQ(int10.getInteger(), "18446744073709551615");
  EXPECT_TRUE(!int11.isInt32() && !int11.isUInt32() && !int11.isInt64()
              && !int11.isUInt64() && int11.isInteger());
  EXPECT_EQ(int11.getInteger(), "18446744073709551616");
}

TEST_F(TestApiTermBlack, getString)
{
  Term s1 = d_solver.mkString("abcde");
  EXPECT_TRUE(s1.isString());
  EXPECT_EQ(s1.getString(), L"abcde");
}

TEST_F(TestApiTermBlack, substitute)
{
  Term x = d_solver.mkConst(d_solver.getIntegerSort(), "x");
  Term one = d_solver.mkInteger(1);
  Term ttrue = d_solver.mkTrue();
  Term xpx = d_solver.mkTerm(PLUS, x, x);
  Term onepone = d_solver.mkTerm(PLUS, one, one);

  EXPECT_EQ(xpx.substitute(x, one), onepone);
  EXPECT_EQ(onepone.substitute(one, x), xpx);
  // incorrect due to type
  ASSERT_THROW(xpx.substitute(one, ttrue), CVC4ApiException);

  // simultaneous substitution
  Term y = d_solver.mkConst(d_solver.getIntegerSort(), "y");
  Term xpy = d_solver.mkTerm(PLUS, x, y);
  Term xpone = d_solver.mkTerm(PLUS, y, one);
  std::vector<Term> es;
  std::vector<Term> rs;
  es.push_back(x);
  rs.push_back(y);
  es.push_back(y);
  rs.push_back(one);
  EXPECT_EQ(xpy.substitute(es, rs), xpone);

  // incorrect substitution due to arity
  rs.pop_back();
  ASSERT_THROW(xpy.substitute(es, rs), CVC4ApiException);

  // incorrect substitution due to types
  rs.push_back(ttrue);
  ASSERT_THROW(xpy.substitute(es, rs), CVC4ApiException);

  // null cannot substitute
  Term tnull;
  ASSERT_THROW(tnull.substitute(one, x), CVC4ApiException);
  ASSERT_THROW(xpx.substitute(tnull, x), CVC4ApiException);
  ASSERT_THROW(xpx.substitute(x, tnull), CVC4ApiException);
  rs.pop_back();
  rs.push_back(tnull);
  ASSERT_THROW(xpy.substitute(es, rs), CVC4ApiException);
  es.clear();
  rs.clear();
  es.push_back(x);
  rs.push_back(y);
  ASSERT_THROW(tnull.substitute(es, rs), CVC4ApiException);
  es.push_back(tnull);
  rs.push_back(one);
  ASSERT_THROW(xpx.substitute(es, rs), CVC4ApiException);
}

TEST_F(TestApiTermBlack, constArray)
{
  Sort intsort = d_solver.getIntegerSort();
  Sort arrsort = d_solver.mkArraySort(intsort, intsort);
  Term a = d_solver.mkConst(arrsort, "a");
  Term one = d_solver.mkInteger(1);
  Term constarr = d_solver.mkConstArray(arrsort, one);

  EXPECT_EQ(constarr.getKind(), CONST_ARRAY);
  EXPECT_EQ(constarr.getConstArrayBase(), one);
  ASSERT_THROW(a.getConstArrayBase(), CVC4ApiException);

  arrsort =
      d_solver.mkArraySort(d_solver.getRealSort(), d_solver.getRealSort());
  Term zero_array = d_solver.mkConstArray(arrsort, d_solver.mkReal(0));
  Term stores = d_solver.mkTerm(
      STORE, zero_array, d_solver.mkReal(1), d_solver.mkReal(2));
  stores =
      d_solver.mkTerm(STORE, stores, d_solver.mkReal(2), d_solver.mkReal(3));
  stores =
      d_solver.mkTerm(STORE, stores, d_solver.mkReal(4), d_solver.mkReal(5));
}

TEST_F(TestApiTermBlack, constSequenceElements)
{
  Sort realsort = d_solver.getRealSort();
  Sort seqsort = d_solver.mkSequenceSort(realsort);
  Term s = d_solver.mkEmptySequence(seqsort);

  EXPECT_EQ(s.getKind(), CONST_SEQUENCE);
  // empty sequence has zero elements
  std::vector<Term> cs = s.getConstSequenceElements();
  ASSERT_TRUE(cs.empty());

  // A seq.unit app is not a constant sequence (regardless of whether it is
  // applied to a constant).
  Term su = d_solver.mkTerm(SEQ_UNIT, d_solver.mkReal(1));
  ASSERT_THROW(su.getConstSequenceElements(), CVC4ApiException);
}

TEST_F(TestApiTermBlack, termScopedToString)
{
  Sort intsort = d_solver.getIntegerSort();
  Term x = d_solver.mkConst(intsort, "x");
  EXPECT_EQ(x.toString(), "x");
  Solver solver2;
  EXPECT_EQ(x.toString(), "x");
}
}  // namespace test
}  // namespace CVC4
