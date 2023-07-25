/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Term class.
 */

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackTerm : public TestApi
{
};

TEST_F(TestApiBlackTerm, eq)
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

TEST_F(TestApiBlackTerm, getId)
{
  Term n;
  ASSERT_THROW(n.getId(), CVC5ApiException);
  Term x = d_solver.mkVar(d_solver.getIntegerSort(), "x");
  ASSERT_NO_THROW(x.getId());
  Term y = x;
  ASSERT_EQ(x.getId(), y.getId());

  Term z = d_solver.mkVar(d_solver.getIntegerSort(), "z");
  ASSERT_NE(x.getId(), z.getId());
}

TEST_F(TestApiBlackTerm, getKind)
{
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort({uSort}, intSort);
  Sort funSort2 = d_solver.mkFunctionSort({intSort}, boolSort);

  Term n;
  ASSERT_THROW(n.getKind(), CVC5ApiException);
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

  Term f_x = d_solver.mkTerm(APPLY_UF, {f, x});
  ASSERT_NO_THROW(f_x.getKind());
  Term f_y = d_solver.mkTerm(APPLY_UF, {f, y});
  ASSERT_NO_THROW(f_y.getKind());
  Term sum = d_solver.mkTerm(ADD, {f_x, f_y});
  ASSERT_NO_THROW(sum.getKind());
  Term p_0 = d_solver.mkTerm(APPLY_UF, {p, zero});
  ASSERT_NO_THROW(p_0.getKind());
  Term p_f_y = d_solver.mkTerm(APPLY_UF, {p, f_y});
  ASSERT_NO_THROW(p_f_y.getKind());

  // Sequence kinds do not exist internally, test that the API properly
  // converts them back.
  Sort seqSort = d_solver.mkSequenceSort(intSort);
  Term s = d_solver.mkConst(seqSort, "s");
  Term ss = d_solver.mkTerm(SEQ_CONCAT, {s, s});
  ASSERT_EQ(ss.getKind(), SEQ_CONCAT);
}

TEST_F(TestApiBlackTerm, getSort)
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort({bvSort}, intSort);
  Sort funSort2 = d_solver.mkFunctionSort({intSort}, boolSort);

  Term n;
  ASSERT_THROW(n.getSort(), CVC5ApiException);
  Term x = d_solver.mkVar(bvSort, "x");
  ASSERT_NO_THROW(x.getSort());
  ASSERT_EQ(x.getSort(), bvSort);
  Term y = d_solver.mkVar(bvSort, "y");
  ASSERT_NO_THROW(y.getSort());
  ASSERT_EQ(y.getSort(), bvSort);

  Term f = d_solver.mkVar(funSort1, "f");
  ASSERT_NO_THROW(f.getSort());
  ASSERT_EQ(f.getSort(), funSort1);
  Term p = d_solver.mkVar(funSort2, "p");
  ASSERT_NO_THROW(p.getSort());
  ASSERT_EQ(p.getSort(), funSort2);

  Term zero = d_solver.mkInteger(0);
  ASSERT_NO_THROW(zero.getSort());
  ASSERT_EQ(zero.getSort(), intSort);

  Term f_x = d_solver.mkTerm(APPLY_UF, {f, x});
  ASSERT_NO_THROW(f_x.getSort());
  ASSERT_EQ(f_x.getSort(), intSort);
  Term f_y = d_solver.mkTerm(APPLY_UF, {f, y});
  ASSERT_NO_THROW(f_y.getSort());
  ASSERT_EQ(f_y.getSort(), intSort);
  Term sum = d_solver.mkTerm(ADD, {f_x, f_y});
  ASSERT_NO_THROW(sum.getSort());
  ASSERT_EQ(sum.getSort(), intSort);
  Term p_0 = d_solver.mkTerm(APPLY_UF, {p, zero});
  ASSERT_NO_THROW(p_0.getSort());
  ASSERT_EQ(p_0.getSort(), boolSort);
  Term p_f_y = d_solver.mkTerm(APPLY_UF, {p, f_y});
  ASSERT_NO_THROW(p_f_y.getSort());
  ASSERT_EQ(p_f_y.getSort(), boolSort);
}

TEST_F(TestApiBlackTerm, getOp)
{
  Sort intsort = d_solver.getIntegerSort();
  Sort bvsort = d_solver.mkBitVectorSort(8);
  Sort arrsort = d_solver.mkArraySort(bvsort, intsort);
  Sort funsort = d_solver.mkFunctionSort({intsort}, bvsort);

  Term x = d_solver.mkConst(intsort, "x");
  Term a = d_solver.mkConst(arrsort, "a");
  Term b = d_solver.mkConst(bvsort, "b");

  ASSERT_FALSE(x.hasOp());
  ASSERT_THROW(x.getOp(), CVC5ApiException);

  Term ab = d_solver.mkTerm(SELECT, {a, b});
  Op ext = d_solver.mkOp(BITVECTOR_EXTRACT, {4, 0});
  Term extb = d_solver.mkTerm(ext, {b});

  ASSERT_TRUE(ab.hasOp());
  ASSERT_FALSE(ab.getOp().isIndexed());
  // can compare directly to a Kind (will invoke Op constructor)
  ASSERT_TRUE(extb.hasOp());
  ASSERT_TRUE(extb.getOp().isIndexed());
  ASSERT_EQ(extb.getOp(), ext);

  Term f = d_solver.mkConst(funsort, "f");
  Term fx = d_solver.mkTerm(APPLY_UF, {f, x});

  ASSERT_FALSE(f.hasOp());
  ASSERT_THROW(f.getOp(), CVC5ApiException);
  ASSERT_TRUE(fx.hasOp());
  std::vector<Term> children(fx.begin(), fx.end());
  // testing rebuild from op and children
  ASSERT_EQ(fx, d_solver.mkTerm(fx.getOp(), children));

  // Test Datatypes Ops
  Sort sort = d_solver.mkParamSort("T");
  DatatypeDecl listDecl = d_solver.mkDatatypeDecl("paramlist", {sort});
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
  Term consOpTerm = list.getConstructor("cons").getTerm();
  Term nilOpTerm = list.getConstructor("nil").getTerm();
  Term headOpTerm = list["cons"].getSelector("head").getTerm();
  Term tailOpTerm = list["cons"].getSelector("tail").getTerm();

  Term nilTerm = d_solver.mkTerm(APPLY_CONSTRUCTOR, {nilOpTerm});
  Term consTerm = d_solver.mkTerm(APPLY_CONSTRUCTOR,
                                  {consOpTerm, d_solver.mkInteger(0), nilTerm});
  Term headTerm = d_solver.mkTerm(APPLY_SELECTOR, {headOpTerm, consTerm});
  Term tailTerm = d_solver.mkTerm(APPLY_SELECTOR, {tailOpTerm, consTerm});

  ASSERT_TRUE(nilTerm.hasOp());
  ASSERT_TRUE(consTerm.hasOp());
  ASSERT_TRUE(headTerm.hasOp());
  ASSERT_TRUE(tailTerm.hasOp());

  // Test rebuilding
  children.clear();
  children.insert(children.begin(), headTerm.begin(), headTerm.end());
  ASSERT_EQ(headTerm, d_solver.mkTerm(headTerm.getOp(), children));
}

TEST_F(TestApiBlackTerm, hasGetSymbol)
{
  Term n;
  Term t = d_solver.mkBoolean(true);
  Term c = d_solver.mkConst(d_solver.getBooleanSort(), "|\\|");

  ASSERT_THROW(n.hasSymbol(), CVC5ApiException);
  ASSERT_FALSE(t.hasSymbol());
  ASSERT_TRUE(c.hasSymbol());

  ASSERT_THROW(n.getSymbol(), CVC5ApiException);
  ASSERT_THROW(t.getSymbol(), CVC5ApiException);
  ASSERT_EQ(c.getSymbol(), "|\\|");
}

TEST_F(TestApiBlackTerm, isNull)
{
  Term x;
  ASSERT_TRUE(x.isNull());
  x = d_solver.mkVar(d_solver.mkBitVectorSort(4), "x");
  ASSERT_FALSE(x.isNull());
}

TEST_F(TestApiBlackTerm, notTerm)
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort({bvSort}, intSort);
  Sort funSort2 = d_solver.mkFunctionSort({intSort}, boolSort);

  ASSERT_THROW(Term().notTerm(), CVC5ApiException);
  Term b = d_solver.mkTrue();
  ASSERT_NO_THROW(b.notTerm());
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  ASSERT_THROW(x.notTerm(), CVC5ApiException);
  Term f = d_solver.mkVar(funSort1, "f");
  ASSERT_THROW(f.notTerm(), CVC5ApiException);
  Term p = d_solver.mkVar(funSort2, "p");
  ASSERT_THROW(p.notTerm(), CVC5ApiException);
  Term zero = d_solver.mkInteger(0);
  ASSERT_THROW(zero.notTerm(), CVC5ApiException);
  Term f_x = d_solver.mkTerm(APPLY_UF, {f, x});
  ASSERT_THROW(f_x.notTerm(), CVC5ApiException);
  Term sum = d_solver.mkTerm(ADD, {f_x, f_x});
  ASSERT_THROW(sum.notTerm(), CVC5ApiException);
  Term p_0 = d_solver.mkTerm(APPLY_UF, {p, zero});
  ASSERT_NO_THROW(p_0.notTerm());
  Term p_f_x = d_solver.mkTerm(APPLY_UF, {p, f_x});
  ASSERT_NO_THROW(p_f_x.notTerm());
}

TEST_F(TestApiBlackTerm, andTerm)
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort({bvSort}, intSort);
  Sort funSort2 = d_solver.mkFunctionSort({intSort}, boolSort);

  Term b = d_solver.mkTrue();
  ASSERT_THROW(Term().andTerm(b), CVC5ApiException);
  ASSERT_THROW(b.andTerm(Term()), CVC5ApiException);
  ASSERT_NO_THROW(b.andTerm(b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  ASSERT_THROW(x.andTerm(b), CVC5ApiException);
  ASSERT_THROW(x.andTerm(x), CVC5ApiException);
  Term f = d_solver.mkVar(funSort1, "f");
  ASSERT_THROW(f.andTerm(b), CVC5ApiException);
  ASSERT_THROW(f.andTerm(x), CVC5ApiException);
  ASSERT_THROW(f.andTerm(f), CVC5ApiException);
  Term p = d_solver.mkVar(funSort2, "p");
  ASSERT_THROW(p.andTerm(b), CVC5ApiException);
  ASSERT_THROW(p.andTerm(x), CVC5ApiException);
  ASSERT_THROW(p.andTerm(f), CVC5ApiException);
  ASSERT_THROW(p.andTerm(p), CVC5ApiException);
  Term zero = d_solver.mkInteger(0);
  ASSERT_THROW(zero.andTerm(b), CVC5ApiException);
  ASSERT_THROW(zero.andTerm(x), CVC5ApiException);
  ASSERT_THROW(zero.andTerm(f), CVC5ApiException);
  ASSERT_THROW(zero.andTerm(p), CVC5ApiException);
  ASSERT_THROW(zero.andTerm(zero), CVC5ApiException);
  Term f_x = d_solver.mkTerm(APPLY_UF, {f, x});
  ASSERT_THROW(f_x.andTerm(b), CVC5ApiException);
  ASSERT_THROW(f_x.andTerm(x), CVC5ApiException);
  ASSERT_THROW(f_x.andTerm(f), CVC5ApiException);
  ASSERT_THROW(f_x.andTerm(p), CVC5ApiException);
  ASSERT_THROW(f_x.andTerm(zero), CVC5ApiException);
  ASSERT_THROW(f_x.andTerm(f_x), CVC5ApiException);
  Term sum = d_solver.mkTerm(ADD, {f_x, f_x});
  ASSERT_THROW(sum.andTerm(b), CVC5ApiException);
  ASSERT_THROW(sum.andTerm(x), CVC5ApiException);
  ASSERT_THROW(sum.andTerm(f), CVC5ApiException);
  ASSERT_THROW(sum.andTerm(p), CVC5ApiException);
  ASSERT_THROW(sum.andTerm(zero), CVC5ApiException);
  ASSERT_THROW(sum.andTerm(f_x), CVC5ApiException);
  ASSERT_THROW(sum.andTerm(sum), CVC5ApiException);
  Term p_0 = d_solver.mkTerm(APPLY_UF, {p, zero});
  ASSERT_NO_THROW(p_0.andTerm(b));
  ASSERT_THROW(p_0.andTerm(x), CVC5ApiException);
  ASSERT_THROW(p_0.andTerm(f), CVC5ApiException);
  ASSERT_THROW(p_0.andTerm(p), CVC5ApiException);
  ASSERT_THROW(p_0.andTerm(zero), CVC5ApiException);
  ASSERT_THROW(p_0.andTerm(f_x), CVC5ApiException);
  ASSERT_THROW(p_0.andTerm(sum), CVC5ApiException);
  ASSERT_NO_THROW(p_0.andTerm(p_0));
  Term p_f_x = d_solver.mkTerm(APPLY_UF, {p, f_x});
  ASSERT_NO_THROW(p_f_x.andTerm(b));
  ASSERT_THROW(p_f_x.andTerm(x), CVC5ApiException);
  ASSERT_THROW(p_f_x.andTerm(f), CVC5ApiException);
  ASSERT_THROW(p_f_x.andTerm(p), CVC5ApiException);
  ASSERT_THROW(p_f_x.andTerm(zero), CVC5ApiException);
  ASSERT_THROW(p_f_x.andTerm(f_x), CVC5ApiException);
  ASSERT_THROW(p_f_x.andTerm(sum), CVC5ApiException);
  ASSERT_NO_THROW(p_f_x.andTerm(p_0));
  ASSERT_NO_THROW(p_f_x.andTerm(p_f_x));
}

TEST_F(TestApiBlackTerm, orTerm)
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort({bvSort}, intSort);
  Sort funSort2 = d_solver.mkFunctionSort({intSort}, boolSort);

  Term b = d_solver.mkTrue();
  ASSERT_THROW(Term().orTerm(b), CVC5ApiException);
  ASSERT_THROW(b.orTerm(Term()), CVC5ApiException);
  ASSERT_NO_THROW(b.orTerm(b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  ASSERT_THROW(x.orTerm(b), CVC5ApiException);
  ASSERT_THROW(x.orTerm(x), CVC5ApiException);
  Term f = d_solver.mkVar(funSort1, "f");
  ASSERT_THROW(f.orTerm(b), CVC5ApiException);
  ASSERT_THROW(f.orTerm(x), CVC5ApiException);
  ASSERT_THROW(f.orTerm(f), CVC5ApiException);
  Term p = d_solver.mkVar(funSort2, "p");
  ASSERT_THROW(p.orTerm(b), CVC5ApiException);
  ASSERT_THROW(p.orTerm(x), CVC5ApiException);
  ASSERT_THROW(p.orTerm(f), CVC5ApiException);
  ASSERT_THROW(p.orTerm(p), CVC5ApiException);
  Term zero = d_solver.mkInteger(0);
  ASSERT_THROW(zero.orTerm(b), CVC5ApiException);
  ASSERT_THROW(zero.orTerm(x), CVC5ApiException);
  ASSERT_THROW(zero.orTerm(f), CVC5ApiException);
  ASSERT_THROW(zero.orTerm(p), CVC5ApiException);
  ASSERT_THROW(zero.orTerm(zero), CVC5ApiException);
  Term f_x = d_solver.mkTerm(APPLY_UF, {f, x});
  ASSERT_THROW(f_x.orTerm(b), CVC5ApiException);
  ASSERT_THROW(f_x.orTerm(x), CVC5ApiException);
  ASSERT_THROW(f_x.orTerm(f), CVC5ApiException);
  ASSERT_THROW(f_x.orTerm(p), CVC5ApiException);
  ASSERT_THROW(f_x.orTerm(zero), CVC5ApiException);
  ASSERT_THROW(f_x.orTerm(f_x), CVC5ApiException);
  Term sum = d_solver.mkTerm(ADD, {f_x, f_x});
  ASSERT_THROW(sum.orTerm(b), CVC5ApiException);
  ASSERT_THROW(sum.orTerm(x), CVC5ApiException);
  ASSERT_THROW(sum.orTerm(f), CVC5ApiException);
  ASSERT_THROW(sum.orTerm(p), CVC5ApiException);
  ASSERT_THROW(sum.orTerm(zero), CVC5ApiException);
  ASSERT_THROW(sum.orTerm(f_x), CVC5ApiException);
  ASSERT_THROW(sum.orTerm(sum), CVC5ApiException);
  Term p_0 = d_solver.mkTerm(APPLY_UF, {p, zero});
  ASSERT_NO_THROW(p_0.orTerm(b));
  ASSERT_THROW(p_0.orTerm(x), CVC5ApiException);
  ASSERT_THROW(p_0.orTerm(f), CVC5ApiException);
  ASSERT_THROW(p_0.orTerm(p), CVC5ApiException);
  ASSERT_THROW(p_0.orTerm(zero), CVC5ApiException);
  ASSERT_THROW(p_0.orTerm(f_x), CVC5ApiException);
  ASSERT_THROW(p_0.orTerm(sum), CVC5ApiException);
  ASSERT_NO_THROW(p_0.orTerm(p_0));
  Term p_f_x = d_solver.mkTerm(APPLY_UF, {p, f_x});
  ASSERT_NO_THROW(p_f_x.orTerm(b));
  ASSERT_THROW(p_f_x.orTerm(x), CVC5ApiException);
  ASSERT_THROW(p_f_x.orTerm(f), CVC5ApiException);
  ASSERT_THROW(p_f_x.orTerm(p), CVC5ApiException);
  ASSERT_THROW(p_f_x.orTerm(zero), CVC5ApiException);
  ASSERT_THROW(p_f_x.orTerm(f_x), CVC5ApiException);
  ASSERT_THROW(p_f_x.orTerm(sum), CVC5ApiException);
  ASSERT_NO_THROW(p_f_x.orTerm(p_0));
  ASSERT_NO_THROW(p_f_x.orTerm(p_f_x));
}

TEST_F(TestApiBlackTerm, xorTerm)
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort({bvSort}, intSort);
  Sort funSort2 = d_solver.mkFunctionSort({intSort}, boolSort);

  Term b = d_solver.mkTrue();
  ASSERT_THROW(Term().xorTerm(b), CVC5ApiException);
  ASSERT_THROW(b.xorTerm(Term()), CVC5ApiException);
  ASSERT_NO_THROW(b.xorTerm(b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  ASSERT_THROW(x.xorTerm(b), CVC5ApiException);
  ASSERT_THROW(x.xorTerm(x), CVC5ApiException);
  Term f = d_solver.mkVar(funSort1, "f");
  ASSERT_THROW(f.xorTerm(b), CVC5ApiException);
  ASSERT_THROW(f.xorTerm(x), CVC5ApiException);
  ASSERT_THROW(f.xorTerm(f), CVC5ApiException);
  Term p = d_solver.mkVar(funSort2, "p");
  ASSERT_THROW(p.xorTerm(b), CVC5ApiException);
  ASSERT_THROW(p.xorTerm(x), CVC5ApiException);
  ASSERT_THROW(p.xorTerm(f), CVC5ApiException);
  ASSERT_THROW(p.xorTerm(p), CVC5ApiException);
  Term zero = d_solver.mkInteger(0);
  ASSERT_THROW(zero.xorTerm(b), CVC5ApiException);
  ASSERT_THROW(zero.xorTerm(x), CVC5ApiException);
  ASSERT_THROW(zero.xorTerm(f), CVC5ApiException);
  ASSERT_THROW(zero.xorTerm(p), CVC5ApiException);
  ASSERT_THROW(zero.xorTerm(zero), CVC5ApiException);
  Term f_x = d_solver.mkTerm(APPLY_UF, {f, x});
  ASSERT_THROW(f_x.xorTerm(b), CVC5ApiException);
  ASSERT_THROW(f_x.xorTerm(x), CVC5ApiException);
  ASSERT_THROW(f_x.xorTerm(f), CVC5ApiException);
  ASSERT_THROW(f_x.xorTerm(p), CVC5ApiException);
  ASSERT_THROW(f_x.xorTerm(zero), CVC5ApiException);
  ASSERT_THROW(f_x.xorTerm(f_x), CVC5ApiException);
  Term sum = d_solver.mkTerm(ADD, {f_x, f_x});
  ASSERT_THROW(sum.xorTerm(b), CVC5ApiException);
  ASSERT_THROW(sum.xorTerm(x), CVC5ApiException);
  ASSERT_THROW(sum.xorTerm(f), CVC5ApiException);
  ASSERT_THROW(sum.xorTerm(p), CVC5ApiException);
  ASSERT_THROW(sum.xorTerm(zero), CVC5ApiException);
  ASSERT_THROW(sum.xorTerm(f_x), CVC5ApiException);
  ASSERT_THROW(sum.xorTerm(sum), CVC5ApiException);
  Term p_0 = d_solver.mkTerm(APPLY_UF, {p, zero});
  ASSERT_NO_THROW(p_0.xorTerm(b));
  ASSERT_THROW(p_0.xorTerm(x), CVC5ApiException);
  ASSERT_THROW(p_0.xorTerm(f), CVC5ApiException);
  ASSERT_THROW(p_0.xorTerm(p), CVC5ApiException);
  ASSERT_THROW(p_0.xorTerm(zero), CVC5ApiException);
  ASSERT_THROW(p_0.xorTerm(f_x), CVC5ApiException);
  ASSERT_THROW(p_0.xorTerm(sum), CVC5ApiException);
  ASSERT_NO_THROW(p_0.xorTerm(p_0));
  Term p_f_x = d_solver.mkTerm(APPLY_UF, {p, f_x});
  ASSERT_NO_THROW(p_f_x.xorTerm(b));
  ASSERT_THROW(p_f_x.xorTerm(x), CVC5ApiException);
  ASSERT_THROW(p_f_x.xorTerm(f), CVC5ApiException);
  ASSERT_THROW(p_f_x.xorTerm(p), CVC5ApiException);
  ASSERT_THROW(p_f_x.xorTerm(zero), CVC5ApiException);
  ASSERT_THROW(p_f_x.xorTerm(f_x), CVC5ApiException);
  ASSERT_THROW(p_f_x.xorTerm(sum), CVC5ApiException);
  ASSERT_NO_THROW(p_f_x.xorTerm(p_0));
  ASSERT_NO_THROW(p_f_x.xorTerm(p_f_x));
}

TEST_F(TestApiBlackTerm, eqTerm)
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort({bvSort}, intSort);
  Sort funSort2 = d_solver.mkFunctionSort({intSort}, boolSort);

  Term b = d_solver.mkTrue();
  ASSERT_THROW(Term().eqTerm(b), CVC5ApiException);
  ASSERT_THROW(b.eqTerm(Term()), CVC5ApiException);
  ASSERT_NO_THROW(b.eqTerm(b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  ASSERT_THROW(x.eqTerm(b), CVC5ApiException);
  ASSERT_NO_THROW(x.eqTerm(x));
  Term f = d_solver.mkVar(funSort1, "f");
  ASSERT_THROW(f.eqTerm(b), CVC5ApiException);
  ASSERT_THROW(f.eqTerm(x), CVC5ApiException);
  ASSERT_NO_THROW(f.eqTerm(f));
  Term p = d_solver.mkVar(funSort2, "p");
  ASSERT_THROW(p.eqTerm(b), CVC5ApiException);
  ASSERT_THROW(p.eqTerm(x), CVC5ApiException);
  ASSERT_THROW(p.eqTerm(f), CVC5ApiException);
  ASSERT_NO_THROW(p.eqTerm(p));
  Term zero = d_solver.mkInteger(0);
  ASSERT_THROW(zero.eqTerm(b), CVC5ApiException);
  ASSERT_THROW(zero.eqTerm(x), CVC5ApiException);
  ASSERT_THROW(zero.eqTerm(f), CVC5ApiException);
  ASSERT_THROW(zero.eqTerm(p), CVC5ApiException);
  ASSERT_NO_THROW(zero.eqTerm(zero));
  Term f_x = d_solver.mkTerm(APPLY_UF, {f, x});
  ASSERT_THROW(f_x.eqTerm(b), CVC5ApiException);
  ASSERT_THROW(f_x.eqTerm(x), CVC5ApiException);
  ASSERT_THROW(f_x.eqTerm(f), CVC5ApiException);
  ASSERT_THROW(f_x.eqTerm(p), CVC5ApiException);
  ASSERT_NO_THROW(f_x.eqTerm(zero));
  ASSERT_NO_THROW(f_x.eqTerm(f_x));
  Term sum = d_solver.mkTerm(ADD, {f_x, f_x});
  ASSERT_THROW(sum.eqTerm(b), CVC5ApiException);
  ASSERT_THROW(sum.eqTerm(x), CVC5ApiException);
  ASSERT_THROW(sum.eqTerm(f), CVC5ApiException);
  ASSERT_THROW(sum.eqTerm(p), CVC5ApiException);
  ASSERT_NO_THROW(sum.eqTerm(zero));
  ASSERT_NO_THROW(sum.eqTerm(f_x));
  ASSERT_NO_THROW(sum.eqTerm(sum));
  Term p_0 = d_solver.mkTerm(APPLY_UF, {p, zero});
  ASSERT_NO_THROW(p_0.eqTerm(b));
  ASSERT_THROW(p_0.eqTerm(x), CVC5ApiException);
  ASSERT_THROW(p_0.eqTerm(f), CVC5ApiException);
  ASSERT_THROW(p_0.eqTerm(p), CVC5ApiException);
  ASSERT_THROW(p_0.eqTerm(zero), CVC5ApiException);
  ASSERT_THROW(p_0.eqTerm(f_x), CVC5ApiException);
  ASSERT_THROW(p_0.eqTerm(sum), CVC5ApiException);
  ASSERT_NO_THROW(p_0.eqTerm(p_0));
  Term p_f_x = d_solver.mkTerm(APPLY_UF, {p, f_x});
  ASSERT_NO_THROW(p_f_x.eqTerm(b));
  ASSERT_THROW(p_f_x.eqTerm(x), CVC5ApiException);
  ASSERT_THROW(p_f_x.eqTerm(f), CVC5ApiException);
  ASSERT_THROW(p_f_x.eqTerm(p), CVC5ApiException);
  ASSERT_THROW(p_f_x.eqTerm(zero), CVC5ApiException);
  ASSERT_THROW(p_f_x.eqTerm(f_x), CVC5ApiException);
  ASSERT_THROW(p_f_x.eqTerm(sum), CVC5ApiException);
  ASSERT_NO_THROW(p_f_x.eqTerm(p_0));
  ASSERT_NO_THROW(p_f_x.eqTerm(p_f_x));
}

TEST_F(TestApiBlackTerm, impTerm)
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort({bvSort}, intSort);
  Sort funSort2 = d_solver.mkFunctionSort({intSort}, boolSort);

  Term b = d_solver.mkTrue();
  ASSERT_THROW(Term().impTerm(b), CVC5ApiException);
  ASSERT_THROW(b.impTerm(Term()), CVC5ApiException);
  ASSERT_NO_THROW(b.impTerm(b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  ASSERT_THROW(x.impTerm(b), CVC5ApiException);
  ASSERT_THROW(x.impTerm(x), CVC5ApiException);
  Term f = d_solver.mkVar(funSort1, "f");
  ASSERT_THROW(f.impTerm(b), CVC5ApiException);
  ASSERT_THROW(f.impTerm(x), CVC5ApiException);
  ASSERT_THROW(f.impTerm(f), CVC5ApiException);
  Term p = d_solver.mkVar(funSort2, "p");
  ASSERT_THROW(p.impTerm(b), CVC5ApiException);
  ASSERT_THROW(p.impTerm(x), CVC5ApiException);
  ASSERT_THROW(p.impTerm(f), CVC5ApiException);
  ASSERT_THROW(p.impTerm(p), CVC5ApiException);
  Term zero = d_solver.mkInteger(0);
  ASSERT_THROW(zero.impTerm(b), CVC5ApiException);
  ASSERT_THROW(zero.impTerm(x), CVC5ApiException);
  ASSERT_THROW(zero.impTerm(f), CVC5ApiException);
  ASSERT_THROW(zero.impTerm(p), CVC5ApiException);
  ASSERT_THROW(zero.impTerm(zero), CVC5ApiException);
  Term f_x = d_solver.mkTerm(APPLY_UF, {f, x});
  ASSERT_THROW(f_x.impTerm(b), CVC5ApiException);
  ASSERT_THROW(f_x.impTerm(x), CVC5ApiException);
  ASSERT_THROW(f_x.impTerm(f), CVC5ApiException);
  ASSERT_THROW(f_x.impTerm(p), CVC5ApiException);
  ASSERT_THROW(f_x.impTerm(zero), CVC5ApiException);
  ASSERT_THROW(f_x.impTerm(f_x), CVC5ApiException);
  Term sum = d_solver.mkTerm(ADD, {f_x, f_x});
  ASSERT_THROW(sum.impTerm(b), CVC5ApiException);
  ASSERT_THROW(sum.impTerm(x), CVC5ApiException);
  ASSERT_THROW(sum.impTerm(f), CVC5ApiException);
  ASSERT_THROW(sum.impTerm(p), CVC5ApiException);
  ASSERT_THROW(sum.impTerm(zero), CVC5ApiException);
  ASSERT_THROW(sum.impTerm(f_x), CVC5ApiException);
  ASSERT_THROW(sum.impTerm(sum), CVC5ApiException);
  Term p_0 = d_solver.mkTerm(APPLY_UF, {p, zero});
  ASSERT_NO_THROW(p_0.impTerm(b));
  ASSERT_THROW(p_0.impTerm(x), CVC5ApiException);
  ASSERT_THROW(p_0.impTerm(f), CVC5ApiException);
  ASSERT_THROW(p_0.impTerm(p), CVC5ApiException);
  ASSERT_THROW(p_0.impTerm(zero), CVC5ApiException);
  ASSERT_THROW(p_0.impTerm(f_x), CVC5ApiException);
  ASSERT_THROW(p_0.impTerm(sum), CVC5ApiException);
  ASSERT_NO_THROW(p_0.impTerm(p_0));
  Term p_f_x = d_solver.mkTerm(APPLY_UF, {p, f_x});
  ASSERT_NO_THROW(p_f_x.impTerm(b));
  ASSERT_THROW(p_f_x.impTerm(x), CVC5ApiException);
  ASSERT_THROW(p_f_x.impTerm(f), CVC5ApiException);
  ASSERT_THROW(p_f_x.impTerm(p), CVC5ApiException);
  ASSERT_THROW(p_f_x.impTerm(zero), CVC5ApiException);
  ASSERT_THROW(p_f_x.impTerm(f_x), CVC5ApiException);
  ASSERT_THROW(p_f_x.impTerm(sum), CVC5ApiException);
  ASSERT_NO_THROW(p_f_x.impTerm(p_0));
  ASSERT_NO_THROW(p_f_x.impTerm(p_f_x));
}

TEST_F(TestApiBlackTerm, iteTerm)
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort({bvSort}, intSort);
  Sort funSort2 = d_solver.mkFunctionSort({intSort}, boolSort);

  Term b = d_solver.mkTrue();
  ASSERT_THROW(Term().iteTerm(b, b), CVC5ApiException);
  ASSERT_THROW(b.iteTerm(Term(), b), CVC5ApiException);
  ASSERT_THROW(b.iteTerm(b, Term()), CVC5ApiException);
  ASSERT_NO_THROW(b.iteTerm(b, b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  ASSERT_NO_THROW(b.iteTerm(x, x));
  ASSERT_NO_THROW(b.iteTerm(b, b));
  ASSERT_THROW(b.iteTerm(x, b), CVC5ApiException);
  ASSERT_THROW(x.iteTerm(x, x), CVC5ApiException);
  ASSERT_THROW(x.iteTerm(x, b), CVC5ApiException);
  Term f = d_solver.mkVar(funSort1, "f");
  ASSERT_THROW(f.iteTerm(b, b), CVC5ApiException);
  ASSERT_THROW(x.iteTerm(b, x), CVC5ApiException);
  Term p = d_solver.mkVar(funSort2, "p");
  ASSERT_THROW(p.iteTerm(b, b), CVC5ApiException);
  ASSERT_THROW(p.iteTerm(x, b), CVC5ApiException);
  Term zero = d_solver.mkInteger(0);
  ASSERT_THROW(zero.iteTerm(x, x), CVC5ApiException);
  ASSERT_THROW(zero.iteTerm(x, b), CVC5ApiException);
  Term f_x = d_solver.mkTerm(APPLY_UF, {f, x});
  ASSERT_THROW(f_x.iteTerm(b, b), CVC5ApiException);
  ASSERT_THROW(f_x.iteTerm(b, x), CVC5ApiException);
  Term sum = d_solver.mkTerm(ADD, {f_x, f_x});
  ASSERT_THROW(sum.iteTerm(x, x), CVC5ApiException);
  ASSERT_THROW(sum.iteTerm(b, x), CVC5ApiException);
  Term p_0 = d_solver.mkTerm(APPLY_UF, {p, zero});
  ASSERT_NO_THROW(p_0.iteTerm(b, b));
  ASSERT_NO_THROW(p_0.iteTerm(x, x));
  ASSERT_THROW(p_0.iteTerm(x, b), CVC5ApiException);
  Term p_f_x = d_solver.mkTerm(APPLY_UF, {p, f_x});
  ASSERT_NO_THROW(p_f_x.iteTerm(b, b));
  ASSERT_NO_THROW(p_f_x.iteTerm(x, x));
  ASSERT_THROW(p_f_x.iteTerm(x, b), CVC5ApiException);
}

TEST_F(TestApiBlackTerm, termAssignment)
{
  Term t1 = d_solver.mkInteger(1);
  Term t2 = t1;
  t2 = d_solver.mkInteger(2);
  ASSERT_EQ(t1, d_solver.mkInteger(1));
}

TEST_F(TestApiBlackTerm, termCompare)
{
  Term t1 = d_solver.mkInteger(1);
  Term t2 =
      d_solver.mkTerm(ADD, {d_solver.mkInteger(2), d_solver.mkInteger(2)});
  Term t3 =
      d_solver.mkTerm(ADD, {d_solver.mkInteger(2), d_solver.mkInteger(2)});
  ASSERT_TRUE(t2 >= t3);
  ASSERT_TRUE(t2 <= t3);
  ASSERT_TRUE((t1 > t2) != (t1 < t2));
  ASSERT_TRUE((t1 > t2 || t1 == t2) == (t1 >= t2));
}

TEST_F(TestApiBlackTerm, termChildren)
{
  // simple term 2+3
  Term two = d_solver.mkInteger(2);
  Term t1 = d_solver.mkTerm(ADD, {two, d_solver.mkInteger(3)});
  ASSERT_EQ(t1[0], two);
  ASSERT_EQ(t1.getNumChildren(), 2);
  Term tnull;
  ASSERT_THROW(tnull.getNumChildren(), CVC5ApiException);

  Term::const_iterator it;
  it = t1.begin();
  ASSERT_TRUE((*it).isIntegerValue());
  it++;
  ASSERT_TRUE((*it).isIntegerValue());
  ++it;
  ASSERT_EQ(it, t1.end());

  // apply term f(2)
  Sort intSort = d_solver.getIntegerSort();
  Sort fsort = d_solver.mkFunctionSort({intSort}, intSort);
  Term f = d_solver.mkConst(fsort, "f");
  Term t2 = d_solver.mkTerm(APPLY_UF, {f, two});
  // due to our higher-order view of terms, we treat f as a child of APPLY_UF
  ASSERT_EQ(t2.getNumChildren(), 2);
  ASSERT_EQ(t2[0], f);
  ASSERT_EQ(t2[1], two);
  ASSERT_THROW(tnull[0], CVC5ApiException);
}

TEST_F(TestApiBlackTerm, getInteger)
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
  Term int12 = d_solver.mkInteger("-0");

  ASSERT_THROW(d_solver.mkInteger(""), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger("-"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger("-1-"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger("0.0"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger("-0.1"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger("012"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger("0000"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger("-01"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger("-00"), CVC5ApiException);

  ASSERT_TRUE(!int1.isInt32Value() && !int1.isUInt32Value()
              && !int1.isInt64Value() && !int1.isUInt64Value()
              && int1.isIntegerValue());
  ASSERT_EQ(int1.getIntegerValue(), "-18446744073709551616");
  ASSERT_TRUE(int1.getRealOrIntegerValueSign() == -1);
  ASSERT_TRUE(!int2.isInt32Value() && !int2.isUInt32Value()
              && !int2.isInt64Value() && !int2.isUInt64Value()
              && int2.isIntegerValue());
  ASSERT_EQ(int2.getIntegerValue(), "-18446744073709551615");
  ASSERT_TRUE(!int3.isInt32Value() && !int3.isUInt32Value()
              && int3.isInt64Value() && !int3.isUInt64Value()
              && int3.isIntegerValue());
  ASSERT_EQ(int3.getInt64Value(), -4294967296);
  ASSERT_EQ(int3.getIntegerValue(), "-4294967296");
  ASSERT_TRUE(!int4.isInt32Value() && !int4.isUInt32Value()
              && int4.isInt64Value() && !int4.isUInt64Value()
              && int4.isIntegerValue());
  ASSERT_EQ(int4.getInt64Value(), -4294967295);
  ASSERT_EQ(int4.getIntegerValue(), "-4294967295");
  ASSERT_TRUE(int5.isInt32Value() && !int5.isUInt32Value()
              && int5.isInt64Value() && !int5.isUInt64Value()
              && int5.isIntegerValue());
  ASSERT_EQ(int5.getInt32Value(), -10);
  ASSERT_EQ(int5.getInt64Value(), -10);
  ASSERT_EQ(int5.getIntegerValue(), "-10");
  ASSERT_TRUE(int6.isInt32Value() && int6.isUInt32Value() && int6.isInt64Value()
              && int6.isUInt64Value() && int6.isIntegerValue());
  ASSERT_EQ(int6.getInt32Value(), 0);
  ASSERT_EQ(int6.getUInt32Value(), 0);
  ASSERT_EQ(int6.getInt64Value(), 0);
  ASSERT_EQ(int6.getUInt64Value(), 0);
  ASSERT_EQ(int6.getIntegerValue(), "0");
  ASSERT_TRUE(int6.getRealOrIntegerValueSign() == 0);
  ASSERT_TRUE(int7.isInt32Value() && int7.isUInt32Value() && int7.isInt64Value()
              && int7.isUInt64Value() && int7.isIntegerValue());
  ASSERT_EQ(int7.getInt32Value(), 10);
  ASSERT_EQ(int7.getUInt32Value(), 10);
  ASSERT_EQ(int7.getInt64Value(), 10);
  ASSERT_EQ(int7.getUInt64Value(), 10);
  ASSERT_EQ(int7.getIntegerValue(), "10");
  ASSERT_TRUE(int7.getRealOrIntegerValueSign() == 1);
  ASSERT_TRUE(!int8.isInt32Value() && int8.isUInt32Value()
              && int8.isInt64Value() && int8.isUInt64Value()
              && int8.isIntegerValue());
  ASSERT_EQ(int8.getUInt32Value(), 4294967295);
  ASSERT_EQ(int8.getInt64Value(), 4294967295);
  ASSERT_EQ(int8.getUInt64Value(), 4294967295);
  ASSERT_EQ(int8.getIntegerValue(), "4294967295");
  ASSERT_TRUE(!int9.isInt32Value() && !int9.isUInt32Value()
              && int9.isInt64Value() && int9.isUInt64Value()
              && int9.isIntegerValue());
  ASSERT_EQ(int9.getInt64Value(), 4294967296);
  ASSERT_EQ(int9.getUInt64Value(), 4294967296);
  ASSERT_EQ(int9.getIntegerValue(), "4294967296");
  ASSERT_TRUE(!int10.isInt32Value() && !int10.isUInt32Value()
              && !int10.isInt64Value() && int10.isUInt64Value()
              && int10.isIntegerValue());
  ASSERT_EQ(int10.getUInt64Value(), 18446744073709551615ull);
  ASSERT_EQ(int10.getIntegerValue(), "18446744073709551615");
  ASSERT_TRUE(!int11.isInt32Value() && !int11.isUInt32Value()
              && !int11.isInt64Value() && !int11.isUInt64Value()
              && int11.isIntegerValue());
  ASSERT_EQ(int11.getIntegerValue(), "18446744073709551616");
}

TEST_F(TestApiBlackTerm, getString)
{
  Term s1 = d_solver.mkString("abcde");
  ASSERT_TRUE(s1.isStringValue());
  ASSERT_EQ(s1.getStringValue(), L"abcde");
}

TEST_F(TestApiBlackTerm, getReal)
{
  Term real1 = d_solver.mkReal("0");
  Term real2 = d_solver.mkReal(".0");
  Term real3 = d_solver.mkReal("-17");
  Term real4 = d_solver.mkReal("-3/5");
  Term real5 = d_solver.mkReal("12.7");
  Term real6 = d_solver.mkReal("1/4294967297");
  Term real7 = d_solver.mkReal("4294967297");
  Term real8 = d_solver.mkReal("1/18446744073709551617");
  Term real9 = d_solver.mkReal("18446744073709551617");
  Term real10 = d_solver.mkReal("2343.2343");

  ASSERT_TRUE(real1.isRealValue() && real1.isReal64Value()
              && real1.isReal32Value());
  ASSERT_TRUE(real2.isRealValue() && real2.isReal64Value()
              && real2.isReal32Value());
  ASSERT_TRUE(real3.isRealValue() && real3.isReal64Value()
              && real3.isReal32Value());
  ASSERT_TRUE(real4.isRealValue() && real4.isReal64Value()
              && real4.isReal32Value());
  ASSERT_TRUE(real5.isRealValue() && real5.isReal64Value()
              && real5.isReal32Value());
  ASSERT_TRUE(real6.isRealValue() && real6.isReal64Value());
  ASSERT_TRUE(real7.isRealValue() && real7.isReal64Value());
  ASSERT_TRUE(real8.isRealValue());
  ASSERT_TRUE(real9.isRealValue());
  ASSERT_TRUE(real10.isRealValue());

  ASSERT_EQ((std::pair<int32_t, uint32_t>(0, 1)), real1.getReal32Value());
  ASSERT_EQ((std::pair<int64_t, uint64_t>(0, 1)), real1.getReal64Value());
  ASSERT_EQ("0/1", real1.getRealValue());

  ASSERT_EQ((std::pair<int32_t, uint32_t>(0, 1)), real2.getReal32Value());
  ASSERT_EQ((std::pair<int64_t, uint64_t>(0, 1)), real2.getReal64Value());
  ASSERT_EQ("0/1", real2.getRealValue());

  ASSERT_EQ((std::pair<int32_t, uint32_t>(-17, 1)), real3.getReal32Value());
  ASSERT_EQ((std::pair<int64_t, uint64_t>(-17, 1)), real3.getReal64Value());
  ASSERT_EQ("-17/1", real3.getRealValue());

  ASSERT_EQ((std::pair<int32_t, uint32_t>(-3, 5)), real4.getReal32Value());
  ASSERT_EQ((std::pair<int64_t, uint64_t>(-3, 5)), real4.getReal64Value());
  ASSERT_EQ("-3/5", real4.getRealValue());

  ASSERT_EQ((std::pair<int32_t, uint32_t>(127, 10)), real5.getReal32Value());
  ASSERT_EQ((std::pair<int64_t, uint64_t>(127, 10)), real5.getReal64Value());
  ASSERT_EQ("127/10", real5.getRealValue());

  ASSERT_EQ((std::pair<int64_t, uint64_t>(1, 4294967297)),
            real6.getReal64Value());
  ASSERT_EQ("1/4294967297", real6.getRealValue());

  ASSERT_EQ((std::pair<int64_t, uint64_t>(4294967297, 1)),
            real7.getReal64Value());
  ASSERT_EQ("4294967297/1", real7.getRealValue());

  ASSERT_EQ("1/18446744073709551617", real8.getRealValue());

  ASSERT_EQ("18446744073709551617/1", real9.getRealValue());

  ASSERT_EQ("23432343/10000", real10.getRealValue());
}

TEST_F(TestApiBlackTerm, getConstArrayBase)
{
  Sort intsort = d_solver.getIntegerSort();
  Sort arrsort = d_solver.mkArraySort(intsort, intsort);
  Term one = d_solver.mkInteger(1);
  Term constarr = d_solver.mkConstArray(arrsort, one);

  ASSERT_TRUE(constarr.isConstArray());
  ASSERT_EQ(one, constarr.getConstArrayBase());

  Term a = d_solver.mkConst(arrsort, "a");
  ASSERT_THROW(a.getConstArrayBase(), CVC5ApiException);
  ASSERT_THROW(one.getConstArrayBase(), CVC5ApiException);
}

TEST_F(TestApiBlackTerm, getBoolean)
{
  Term b1 = d_solver.mkBoolean(true);
  Term b2 = d_solver.mkBoolean(false);

  ASSERT_TRUE(b1.isBooleanValue());
  ASSERT_TRUE(b2.isBooleanValue());
  ASSERT_TRUE(b1.getBooleanValue());
  ASSERT_FALSE(b2.getBooleanValue());
}

TEST_F(TestApiBlackTerm, getBitVector)
{
  Term b1 = d_solver.mkBitVector(8, 15);
  Term b2 = d_solver.mkBitVector(8, "00001111", 2);
  Term b3 = d_solver.mkBitVector(8, "15", 10);
  Term b4 = d_solver.mkBitVector(8, "0f", 16);
  Term b5 = d_solver.mkBitVector(9, "00001111", 2);
  Term b6 = d_solver.mkBitVector(9, "15", 10);
  Term b7 = d_solver.mkBitVector(9, "0f", 16);

  ASSERT_TRUE(b1.isBitVectorValue());
  ASSERT_TRUE(b2.isBitVectorValue());
  ASSERT_TRUE(b3.isBitVectorValue());
  ASSERT_TRUE(b4.isBitVectorValue());
  ASSERT_TRUE(b5.isBitVectorValue());
  ASSERT_TRUE(b6.isBitVectorValue());
  ASSERT_TRUE(b7.isBitVectorValue());

  ASSERT_EQ("00001111", b1.getBitVectorValue(2));
  ASSERT_EQ("15", b1.getBitVectorValue(10));
  ASSERT_EQ("f", b1.getBitVectorValue(16));
  ASSERT_EQ("00001111", b2.getBitVectorValue(2));
  ASSERT_EQ("15", b2.getBitVectorValue(10));
  ASSERT_EQ("f", b2.getBitVectorValue(16));
  ASSERT_EQ("00001111", b3.getBitVectorValue(2));
  ASSERT_EQ("15", b3.getBitVectorValue(10));
  ASSERT_EQ("f", b3.getBitVectorValue(16));
  ASSERT_EQ("00001111", b4.getBitVectorValue(2));
  ASSERT_EQ("15", b4.getBitVectorValue(10));
  ASSERT_EQ("f", b4.getBitVectorValue(16));
  ASSERT_EQ("000001111", b5.getBitVectorValue(2));
  ASSERT_EQ("15", b5.getBitVectorValue(10));
  ASSERT_EQ("f", b5.getBitVectorValue(16));
  ASSERT_EQ("000001111", b6.getBitVectorValue(2));
  ASSERT_EQ("15", b6.getBitVectorValue(10));
  ASSERT_EQ("f", b6.getBitVectorValue(16));
  ASSERT_EQ("000001111", b7.getBitVectorValue(2));
  ASSERT_EQ("15", b7.getBitVectorValue(10));
  ASSERT_EQ("f", b7.getBitVectorValue(16));
}

TEST_F(TestApiBlackTerm, isFiniteFieldValue)
{
  Sort fS = d_solver.mkFiniteFieldSort("7");
  Term fV = d_solver.mkFiniteFieldElem("1", fS);
  ASSERT_TRUE(fV.isFiniteFieldValue());
  Term b1 = d_solver.mkBitVector(8, 15);
  ASSERT_FALSE(b1.isFiniteFieldValue());
}

TEST_F(TestApiBlackTerm, getFiniteFieldValue)
{
  Sort fS = d_solver.mkFiniteFieldSort("7");
  Term fV = d_solver.mkFiniteFieldElem("1", fS);
  ASSERT_EQ("1", fV.getFiniteFieldValue());
  ASSERT_THROW(Term().getFiniteFieldValue(), CVC5ApiException);
  Term b1 = d_solver.mkBitVector(8, 15);
  ASSERT_THROW(b1.getFiniteFieldValue(), CVC5ApiException);
}

TEST_F(TestApiBlackTerm, getUninterpretedSortValue)
{
  d_solver.setOption("produce-models", "true");
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkConst(uSort, "x");
  Term y = d_solver.mkConst(uSort, "y");
  d_solver.assertFormula(d_solver.mkTerm(EQUAL, {x, y}));
  ASSERT_TRUE(d_solver.checkSat().isSat());
  Term vx = d_solver.getValue(x);
  Term vy = d_solver.getValue(y);
  ASSERT_TRUE(vx.isUninterpretedSortValue());
  ASSERT_TRUE(vy.isUninterpretedSortValue());
  ASSERT_EQ(vx.getUninterpretedSortValue(), vy.getUninterpretedSortValue());
}

TEST_F(TestApiBlackTerm, isRoundingModeValue)
{
  ASSERT_FALSE(d_solver.mkInteger(15).isRoundingModeValue());
  ASSERT_TRUE(d_solver.mkRoundingMode(RoundingMode::ROUND_NEAREST_TIES_TO_EVEN)
                  .isRoundingModeValue());
  ASSERT_FALSE(
      d_solver.mkConst(d_solver.getRoundingModeSort()).isRoundingModeValue());
}

TEST_F(TestApiBlackTerm, getRoundingModeValue)
{
  ASSERT_THROW(d_solver.mkInteger(15).getRoundingModeValue(), CVC5ApiException);
  ASSERT_EQ(d_solver.mkRoundingMode(RoundingMode::ROUND_NEAREST_TIES_TO_EVEN)
                .getRoundingModeValue(),
            RoundingMode::ROUND_NEAREST_TIES_TO_EVEN);
  ASSERT_EQ(d_solver.mkRoundingMode(RoundingMode::ROUND_TOWARD_POSITIVE)
                .getRoundingModeValue(),
            RoundingMode::ROUND_TOWARD_POSITIVE);
  ASSERT_EQ(d_solver.mkRoundingMode(RoundingMode::ROUND_TOWARD_NEGATIVE)
                .getRoundingModeValue(),
            RoundingMode::ROUND_TOWARD_NEGATIVE);
  ASSERT_EQ(d_solver.mkRoundingMode(RoundingMode::ROUND_TOWARD_ZERO)
                .getRoundingModeValue(),
            RoundingMode::ROUND_TOWARD_ZERO);
  ASSERT_EQ(d_solver.mkRoundingMode(RoundingMode::ROUND_NEAREST_TIES_TO_AWAY)
                .getRoundingModeValue(),
            RoundingMode::ROUND_NEAREST_TIES_TO_AWAY);
}

TEST_F(TestApiBlackTerm, getTuple)
{
  Term t1 = d_solver.mkInteger(15);
  Term t2 = d_solver.mkReal(17, 25);
  Term t3 = d_solver.mkString("abc");

  Term tup = d_solver.mkTuple({t1, t2, t3});

  ASSERT_TRUE(tup.isTupleValue());
  ASSERT_EQ(std::vector<Term>({t1, t2, t3}), tup.getTupleValue());
}

TEST_F(TestApiBlackTerm, getFloatingPoint)
{
  Term bvval = d_solver.mkBitVector(16, "0000110000000011", 2);
  Term fp = d_solver.mkFloatingPoint(5, 11, bvval);

  ASSERT_TRUE(fp.isFloatingPointValue());
  ASSERT_FALSE(fp.isFloatingPointPosZero());
  ASSERT_FALSE(fp.isFloatingPointNegZero());
  ASSERT_FALSE(fp.isFloatingPointPosInf());
  ASSERT_FALSE(fp.isFloatingPointNegInf());
  ASSERT_FALSE(fp.isFloatingPointNaN());
  ASSERT_EQ(std::make_tuple(5u, 11u, bvval), fp.getFloatingPointValue());

  ASSERT_TRUE(d_solver.mkFloatingPointPosZero(5, 11).isFloatingPointPosZero());
  ASSERT_TRUE(d_solver.mkFloatingPointNegZero(5, 11).isFloatingPointNegZero());
  ASSERT_TRUE(d_solver.mkFloatingPointPosInf(5, 11).isFloatingPointPosInf());
  ASSERT_TRUE(d_solver.mkFloatingPointNegInf(5, 11).isFloatingPointNegInf());
  ASSERT_TRUE(d_solver.mkFloatingPointNaN(5, 11).isFloatingPointNaN());
}

TEST_F(TestApiBlackTerm, getSet)
{
  Sort s = d_solver.mkSetSort(d_solver.getIntegerSort());

  Term i1 = d_solver.mkInteger(5);
  Term i2 = d_solver.mkInteger(7);

  Term s1 = d_solver.mkEmptySet(s);
  Term s2 = d_solver.mkTerm(Kind::SET_SINGLETON, {i1});
  Term s3 = d_solver.mkTerm(Kind::SET_SINGLETON, {i1});
  Term s4 = d_solver.mkTerm(Kind::SET_SINGLETON, {i2});
  Term s5 = d_solver.mkTerm(Kind::SET_UNION,
                            {s2, d_solver.mkTerm(Kind::SET_UNION, {s3, s4})});

  ASSERT_TRUE(s1.isSetValue());
  ASSERT_TRUE(s2.isSetValue());
  ASSERT_TRUE(s3.isSetValue());
  ASSERT_TRUE(s4.isSetValue());
  ASSERT_FALSE(s5.isSetValue());
  s5 = d_solver.simplify(s5);
  ASSERT_TRUE(s5.isSetValue());

  ASSERT_EQ(std::set<Term>({}), s1.getSetValue());
  ASSERT_EQ(std::set<Term>({i1}), s2.getSetValue());
  ASSERT_EQ(std::set<Term>({i1}), s3.getSetValue());
  ASSERT_EQ(std::set<Term>({i2}), s4.getSetValue());
  ASSERT_EQ(std::set<Term>({i1, i2}), s5.getSetValue());
}

TEST_F(TestApiBlackTerm, getSequence)
{
  Sort s = d_solver.mkSequenceSort(d_solver.getIntegerSort());

  Term i1 = d_solver.mkInteger(5);
  Term i2 = d_solver.mkInteger(7);

  Term s1 = d_solver.mkEmptySequence(s);
  Term s2 = d_solver.mkTerm(Kind::SEQ_UNIT, {i1});
  Term s3 = d_solver.mkTerm(Kind::SEQ_UNIT, {i1});
  Term s4 = d_solver.mkTerm(Kind::SEQ_UNIT, {i2});
  Term s5 = d_solver.mkTerm(Kind::SEQ_CONCAT,
                            {s2, d_solver.mkTerm(Kind::SEQ_CONCAT, {s3, s4})});

  ASSERT_TRUE(s1.isSequenceValue());
  ASSERT_TRUE(!s2.isSequenceValue());
  ASSERT_TRUE(!s3.isSequenceValue());
  ASSERT_TRUE(!s4.isSequenceValue());
  ASSERT_TRUE(!s5.isSequenceValue());

  s2 = d_solver.simplify(s2);
  s3 = d_solver.simplify(s3);
  s4 = d_solver.simplify(s4);
  s5 = d_solver.simplify(s5);

  ASSERT_EQ(std::vector<Term>({}), s1.getSequenceValue());
  ASSERT_EQ(std::vector<Term>({i1}), s2.getSequenceValue());
  ASSERT_EQ(std::vector<Term>({i1}), s3.getSequenceValue());
  ASSERT_EQ(std::vector<Term>({i2}), s4.getSequenceValue());
  ASSERT_EQ(std::vector<Term>({i1, i1, i2}), s5.getSequenceValue());
}

TEST_F(TestApiBlackTerm, substitute)
{
  Term x = d_solver.mkConst(d_solver.getIntegerSort(), "x");
  Term one = d_solver.mkInteger(1);
  Term ttrue = d_solver.mkTrue();
  Term xpx = d_solver.mkTerm(ADD, {x, x});
  Term onepone = d_solver.mkTerm(ADD, {one, one});

  ASSERT_EQ(xpx.substitute(x, one), onepone);
  ASSERT_EQ(onepone.substitute(one, x), xpx);
  // incorrect due to type
  ASSERT_THROW(xpx.substitute(one, ttrue), CVC5ApiException);

  // simultaneous substitution
  Term y = d_solver.mkConst(d_solver.getIntegerSort(), "y");
  Term xpy = d_solver.mkTerm(ADD, {x, y});
  Term xpone = d_solver.mkTerm(ADD, {y, one});
  std::vector<Term> es;
  std::vector<Term> rs;
  es.push_back(x);
  rs.push_back(y);
  es.push_back(y);
  rs.push_back(one);
  ASSERT_EQ(xpy.substitute(es, rs), xpone);

  // incorrect substitution due to arity
  rs.pop_back();
  ASSERT_THROW(xpy.substitute(es, rs), CVC5ApiException);

  // incorrect substitution due to types
  rs.push_back(ttrue);
  ASSERT_THROW(xpy.substitute(es, rs), CVC5ApiException);

  // null cannot substitute
  Term tnull;
  ASSERT_THROW(tnull.substitute(one, x), CVC5ApiException);
  ASSERT_THROW(xpx.substitute(tnull, x), CVC5ApiException);
  ASSERT_THROW(xpx.substitute(x, tnull), CVC5ApiException);
  rs.pop_back();
  rs.push_back(tnull);
  ASSERT_THROW(xpy.substitute(es, rs), CVC5ApiException);
  es.clear();
  rs.clear();
  es.push_back(x);
  rs.push_back(y);
  ASSERT_THROW(tnull.substitute(es, rs), CVC5ApiException);
  es.push_back(tnull);
  rs.push_back(one);
  ASSERT_THROW(xpx.substitute(es, rs), CVC5ApiException);
}

TEST_F(TestApiBlackTerm, constArray)
{
  Sort intsort = d_solver.getIntegerSort();
  Sort arrsort = d_solver.mkArraySort(intsort, intsort);
  Term a = d_solver.mkConst(arrsort, "a");
  Term one = d_solver.mkInteger(1);
  Term two = d_solver.mkBitVector(2, 2);
  Term iconst = d_solver.mkConst(intsort);
  Term constarr = d_solver.mkConstArray(arrsort, one);

  ASSERT_THROW(d_solver.mkConstArray(arrsort, two), CVC5ApiException);
  ASSERT_THROW(d_solver.mkConstArray(arrsort, iconst), CVC5ApiException);

  ASSERT_EQ(constarr.getKind(), CONST_ARRAY);
  ASSERT_EQ(constarr.getConstArrayBase(), one);
  ASSERT_THROW(a.getConstArrayBase(), CVC5ApiException);

  arrsort =
      d_solver.mkArraySort(d_solver.getRealSort(), d_solver.getRealSort());
  Term zero_array = d_solver.mkConstArray(arrsort, d_solver.mkReal(0));
  Term stores = d_solver.mkTerm(
      STORE, {zero_array, d_solver.mkReal(1), d_solver.mkReal(2)});
  stores =
      d_solver.mkTerm(STORE, {stores, d_solver.mkReal(2), d_solver.mkReal(3)});
  stores =
      d_solver.mkTerm(STORE, {stores, d_solver.mkReal(4), d_solver.mkReal(5)});
}

TEST_F(TestApiBlackTerm, getSequenceValue)
{
  Sort realsort = d_solver.getRealSort();
  Sort seqsort = d_solver.mkSequenceSort(realsort);
  Term s = d_solver.mkEmptySequence(seqsort);

  ASSERT_EQ(s.getKind(), CONST_SEQUENCE);
  // empty sequence has zero elements
  std::vector<Term> cs = s.getSequenceValue();
  ASSERT_TRUE(cs.empty());

  // A seq.unit app is not a constant sequence (regardless of whether it is
  // applied to a constant).
  Term su = d_solver.mkTerm(SEQ_UNIT, {d_solver.mkReal(1)});
  ASSERT_THROW(su.getSequenceValue(), CVC5ApiException);
}

TEST_F(TestApiBlackTerm, getCardinalityConstraint)
{
  Sort su = d_solver.mkUninterpretedSort("u");
  Term t = d_solver.mkCardinalityConstraint(su, 3);
  ASSERT_TRUE(t.isCardinalityConstraint());
  std::pair<Sort, uint32_t> cc = t.getCardinalityConstraint();
  ASSERT_EQ(cc.first, su);
  ASSERT_EQ(cc.second, 3);
  Term x = d_solver.mkConst(d_solver.getIntegerSort(), "x");
  ASSERT_FALSE(x.isCardinalityConstraint());
  ASSERT_THROW(x.getCardinalityConstraint(), CVC5ApiException);
  Term nullt;
  ASSERT_THROW(nullt.isCardinalityConstraint(), CVC5ApiException);
}

TEST_F(TestApiBlackTerm, getRealAlgebraicNumber)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setLogic("QF_NRA");
  Sort realsort = d_solver.getRealSort();
  Term x = d_solver.mkConst(realsort, "x");
  Term x2 = d_solver.mkTerm(MULT, {x, x});
  Term two = d_solver.mkReal(2, 1);
  Term eq = d_solver.mkTerm(EQUAL, {x2, two});
  d_solver.assertFormula(eq);
  // Note that check-sat should only return "sat" if libpoly is enabled.
  // Otherwise, we do not test the following functionality.
  if (d_solver.checkSat().isSat())
  {
    // We find a model for (x*x = 2), where x should be a real algebraic number.
    // We assert that its defining polynomial is non-null and its lower and
    // upper bounds are real.
    Term vx = d_solver.getValue(x);
    ASSERT_TRUE(vx.isRealAlgebraicNumber());
    Term y = d_solver.mkVar(realsort, "y");
    Term poly = vx.getRealAlgebraicNumberDefiningPolynomial(y);
    ASSERT_TRUE(!poly.isNull());
    Term lb = vx.getRealAlgebraicNumberLowerBound();
    ASSERT_TRUE(lb.isRealValue());
    Term ub = vx.getRealAlgebraicNumberUpperBound();
    ASSERT_TRUE(ub.isRealValue());
  }
}

TEST_F(TestApiBlackTerm, termScopedToString)
{
  Sort intsort = d_solver.getIntegerSort();
  Term x = d_solver.mkConst(intsort, "x");
  ASSERT_EQ(x.toString(), "x");
  Solver solver2;
  ASSERT_EQ(x.toString(), "x");
}

TEST_F(TestApiBlackTerm, toString) {
  ASSERT_NO_THROW(Term().toString());

  Sort intsort = d_solver.getIntegerSort();
  Term x = d_solver.mkConst(intsort, "x");
  std::stringstream ss;

  ss << std::vector<Term>{x, x};
  ss << std::set<Term>{x, x};
  ss << std::unordered_set<Term>{x, x};
}
}  // namespace test
}  // namespace cvc5::internal
