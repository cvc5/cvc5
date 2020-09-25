/*********************                                                        */
/*! \file term_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Andrew Reynolds, Makai Mann
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the Term class
 **/

#include <cxxtest/TestSuite.h>

#include "api/cvc4cpp.h"

using namespace CVC4::api;

class TermBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override {}
  void tearDown() override {}

  void testEq();
  void testGetId();
  void testGetKind();
  void testGetSort();
  void testGetOp();
  void testIsNull();
  void testNotTerm();
  void testAndTerm();
  void testOrTerm();
  void testXorTerm();
  void testEqTerm();
  void testImpTerm();
  void testIteTerm();

  void testTermAssignment();
  void testTermCompare();
  void testTermChildren();
  void testSubstitute();
  void testIsConst();
  void testConstArray();
  void testConstSequenceElements();

 private:
  Solver d_solver;
};

void TermBlack::testEq()
{
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkVar(uSort, "x");
  Term y = d_solver.mkVar(uSort, "y");
  Term z;

  TS_ASSERT(x == x);
  TS_ASSERT(!(x != x));
  TS_ASSERT(!(x == y));
  TS_ASSERT(x != y);
  TS_ASSERT(!(x == z));
  TS_ASSERT(x != z);
}

void TermBlack::testGetId()
{
  Term n;
  TS_ASSERT_THROWS(n.getId(), CVC4ApiException&);
  Term x = d_solver.mkVar(d_solver.getIntegerSort(), "x");
  TS_ASSERT_THROWS_NOTHING(x.getId());
  Term y = x;
  TS_ASSERT_EQUALS(x.getId(), y.getId());

  Term z = d_solver.mkVar(d_solver.getIntegerSort(), "z");
  TS_ASSERT_DIFFERS(x.getId(), z.getId());
}

void TermBlack::testGetKind()
{
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(uSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  Term n;
  TS_ASSERT_THROWS(n.getKind(), CVC4ApiException&);
  Term x = d_solver.mkVar(uSort, "x");
  TS_ASSERT_THROWS_NOTHING(x.getKind());
  Term y = d_solver.mkVar(uSort, "y");
  TS_ASSERT_THROWS_NOTHING(y.getKind());

  Term f = d_solver.mkVar(funSort1, "f");
  TS_ASSERT_THROWS_NOTHING(f.getKind());
  Term p = d_solver.mkVar(funSort2, "p");
  TS_ASSERT_THROWS_NOTHING(p.getKind());

  Term zero = d_solver.mkReal(0);
  TS_ASSERT_THROWS_NOTHING(zero.getKind());

  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  TS_ASSERT_THROWS_NOTHING(f_x.getKind());
  Term f_y = d_solver.mkTerm(APPLY_UF, f, y);
  TS_ASSERT_THROWS_NOTHING(f_y.getKind());
  Term sum = d_solver.mkTerm(PLUS, f_x, f_y);
  TS_ASSERT_THROWS_NOTHING(sum.getKind());
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  TS_ASSERT_THROWS_NOTHING(p_0.getKind());
  Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);
  TS_ASSERT_THROWS_NOTHING(p_f_y.getKind());

  // Sequence kinds do not exist internally, test that the API properly
  // converts them back.
  Sort seqSort = d_solver.mkSequenceSort(intSort);
  Term s = d_solver.mkConst(seqSort, "s");
  Term ss = d_solver.mkTerm(SEQ_CONCAT, s, s);
  TS_ASSERT(ss.getKind() == SEQ_CONCAT);
}

void TermBlack::testGetSort()
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  Term n;
  TS_ASSERT_THROWS(n.getSort(), CVC4ApiException&);
  Term x = d_solver.mkVar(bvSort, "x");
  TS_ASSERT_THROWS_NOTHING(x.getSort());
  TS_ASSERT(x.getSort() == bvSort);
  Term y = d_solver.mkVar(bvSort, "y");
  TS_ASSERT_THROWS_NOTHING(y.getSort());
  TS_ASSERT(y.getSort() == bvSort);

  Term f = d_solver.mkVar(funSort1, "f");
  TS_ASSERT_THROWS_NOTHING(f.getSort());
  TS_ASSERT(f.getSort() == funSort1);
  Term p = d_solver.mkVar(funSort2, "p");
  TS_ASSERT_THROWS_NOTHING(p.getSort());
  TS_ASSERT(p.getSort() == funSort2);

  Term zero = d_solver.mkReal(0);
  TS_ASSERT_THROWS_NOTHING(zero.getSort());
  TS_ASSERT(zero.getSort() == intSort);

  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  TS_ASSERT_THROWS_NOTHING(f_x.getSort());
  TS_ASSERT(f_x.getSort() == intSort);
  Term f_y = d_solver.mkTerm(APPLY_UF, f, y);
  TS_ASSERT_THROWS_NOTHING(f_y.getSort());
  TS_ASSERT(f_y.getSort() == intSort);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_y);
  TS_ASSERT_THROWS_NOTHING(sum.getSort());
  TS_ASSERT(sum.getSort() == intSort);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  TS_ASSERT_THROWS_NOTHING(p_0.getSort());
  TS_ASSERT(p_0.getSort() == boolSort);
  Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);
  TS_ASSERT_THROWS_NOTHING(p_f_y.getSort());
  TS_ASSERT(p_f_y.getSort() == boolSort);
}

void TermBlack::testGetOp()
{
  Sort intsort = d_solver.getIntegerSort();
  Sort bvsort = d_solver.mkBitVectorSort(8);
  Sort arrsort = d_solver.mkArraySort(bvsort, intsort);
  Sort funsort = d_solver.mkFunctionSort(intsort, bvsort);

  Term x = d_solver.mkConst(intsort, "x");
  Term a = d_solver.mkConst(arrsort, "a");
  Term b = d_solver.mkConst(bvsort, "b");

  TS_ASSERT(!x.hasOp());
  TS_ASSERT_THROWS(x.getOp(), CVC4ApiException&);

  Term ab = d_solver.mkTerm(SELECT, a, b);
  Op ext = d_solver.mkOp(BITVECTOR_EXTRACT, 4, 0);
  Term extb = d_solver.mkTerm(ext, b);

  TS_ASSERT(ab.hasOp());
  TS_ASSERT_EQUALS(ab.getOp(), Op(&d_solver, SELECT));
  TS_ASSERT(!ab.getOp().isIndexed());
  // can compare directly to a Kind (will invoke Op constructor)
  TS_ASSERT_EQUALS(ab.getOp(), Op(&d_solver, SELECT));
  TS_ASSERT(extb.hasOp());
  TS_ASSERT(extb.getOp().isIndexed());
  TS_ASSERT_EQUALS(extb.getOp(), ext);

  Term f = d_solver.mkConst(funsort, "f");
  Term fx = d_solver.mkTerm(APPLY_UF, f, x);

  TS_ASSERT(!f.hasOp());
  TS_ASSERT_THROWS(f.getOp(), CVC4ApiException&);
  TS_ASSERT(fx.hasOp());
  TS_ASSERT_EQUALS(fx.getOp(), Op(&d_solver, APPLY_UF));
  std::vector<Term> children(fx.begin(), fx.end());
  // testing rebuild from op and children
  TS_ASSERT_EQUALS(fx, d_solver.mkTerm(fx.getOp(), children));

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
      APPLY_CONSTRUCTOR, consOpTerm, d_solver.mkReal(0), nilTerm);
  Term headTerm = d_solver.mkTerm(APPLY_SELECTOR, headOpTerm, consTerm);
  Term tailTerm = d_solver.mkTerm(APPLY_SELECTOR, tailOpTerm, consTerm);

  TS_ASSERT(nilTerm.hasOp());
  TS_ASSERT(consTerm.hasOp());
  TS_ASSERT(headTerm.hasOp());
  TS_ASSERT(tailTerm.hasOp());

  TS_ASSERT_EQUALS(nilTerm.getOp(), Op(&d_solver, APPLY_CONSTRUCTOR));
  TS_ASSERT_EQUALS(consTerm.getOp(), Op(&d_solver, APPLY_CONSTRUCTOR));
  TS_ASSERT_EQUALS(headTerm.getOp(), Op(&d_solver, APPLY_SELECTOR));
  TS_ASSERT_EQUALS(tailTerm.getOp(), Op(&d_solver, APPLY_SELECTOR));

  // Test rebuilding
  children.clear();
  children.insert(children.begin(), headTerm.begin(), headTerm.end());
  TS_ASSERT_EQUALS(headTerm, d_solver.mkTerm(headTerm.getOp(), children));
}

void TermBlack::testIsNull()
{
  Term x;
  TS_ASSERT(x.isNull());
  x = d_solver.mkVar(d_solver.mkBitVectorSort(4), "x");
  TS_ASSERT(!x.isNull());
}

void TermBlack::testNotTerm()
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  TS_ASSERT_THROWS(Term().notTerm(), CVC4ApiException&);
  Term b = d_solver.mkTrue();
  TS_ASSERT_THROWS_NOTHING(b.notTerm());
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  TS_ASSERT_THROWS(x.notTerm(), CVC4ApiException&);
  Term f = d_solver.mkVar(funSort1, "f");
  TS_ASSERT_THROWS(f.notTerm(), CVC4ApiException&);
  Term p = d_solver.mkVar(funSort2, "p");
  TS_ASSERT_THROWS(p.notTerm(), CVC4ApiException&);
  Term zero = d_solver.mkReal(0);
  TS_ASSERT_THROWS(zero.notTerm(), CVC4ApiException&);
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  TS_ASSERT_THROWS(f_x.notTerm(), CVC4ApiException&);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
  TS_ASSERT_THROWS(sum.notTerm(), CVC4ApiException&);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  TS_ASSERT_THROWS_NOTHING(p_0.notTerm());
  Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
  TS_ASSERT_THROWS_NOTHING(p_f_x.notTerm());
}

void TermBlack::testAndTerm()
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  Term b = d_solver.mkTrue();
  TS_ASSERT_THROWS(Term().andTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(b.andTerm(Term()), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(b.andTerm(b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  TS_ASSERT_THROWS(x.andTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(x.andTerm(x), CVC4ApiException&);
  Term f = d_solver.mkVar(funSort1, "f");
  TS_ASSERT_THROWS(f.andTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(f.andTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(f.andTerm(f), CVC4ApiException&);
  Term p = d_solver.mkVar(funSort2, "p");
  TS_ASSERT_THROWS(p.andTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(p.andTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(p.andTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(p.andTerm(p), CVC4ApiException&);
  Term zero = d_solver.mkReal(0);
  TS_ASSERT_THROWS(zero.andTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.andTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.andTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.andTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.andTerm(zero), CVC4ApiException&);
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  TS_ASSERT_THROWS(f_x.andTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.andTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.andTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.andTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.andTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.andTerm(f_x), CVC4ApiException&);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
  TS_ASSERT_THROWS(sum.andTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.andTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.andTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.andTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.andTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.andTerm(f_x), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.andTerm(sum), CVC4ApiException&);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  TS_ASSERT_THROWS_NOTHING(p_0.andTerm(b));
  TS_ASSERT_THROWS(p_0.andTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.andTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.andTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.andTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.andTerm(f_x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.andTerm(sum), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(p_0.andTerm(p_0));
  Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
  TS_ASSERT_THROWS_NOTHING(p_f_x.andTerm(b));
  TS_ASSERT_THROWS(p_f_x.andTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.andTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.andTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.andTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.andTerm(f_x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.andTerm(sum), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(p_f_x.andTerm(p_0));
  TS_ASSERT_THROWS_NOTHING(p_f_x.andTerm(p_f_x));
}

void TermBlack::testOrTerm()
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  Term b = d_solver.mkTrue();
  TS_ASSERT_THROWS(Term().orTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(b.orTerm(Term()), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(b.orTerm(b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  TS_ASSERT_THROWS(x.orTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(x.orTerm(x), CVC4ApiException&);
  Term f = d_solver.mkVar(funSort1, "f");
  TS_ASSERT_THROWS(f.orTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(f.orTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(f.orTerm(f), CVC4ApiException&);
  Term p = d_solver.mkVar(funSort2, "p");
  TS_ASSERT_THROWS(p.orTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(p.orTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(p.orTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(p.orTerm(p), CVC4ApiException&);
  Term zero = d_solver.mkReal(0);
  TS_ASSERT_THROWS(zero.orTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.orTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.orTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.orTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.orTerm(zero), CVC4ApiException&);
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  TS_ASSERT_THROWS(f_x.orTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.orTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.orTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.orTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.orTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.orTerm(f_x), CVC4ApiException&);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
  TS_ASSERT_THROWS(sum.orTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.orTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.orTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.orTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.orTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.orTerm(f_x), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.orTerm(sum), CVC4ApiException&);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  TS_ASSERT_THROWS_NOTHING(p_0.orTerm(b));
  TS_ASSERT_THROWS(p_0.orTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.orTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.orTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.orTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.orTerm(f_x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.orTerm(sum), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(p_0.orTerm(p_0));
  Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
  TS_ASSERT_THROWS_NOTHING(p_f_x.orTerm(b));
  TS_ASSERT_THROWS(p_f_x.orTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.orTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.orTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.orTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.orTerm(f_x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.orTerm(sum), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(p_f_x.orTerm(p_0));
  TS_ASSERT_THROWS_NOTHING(p_f_x.orTerm(p_f_x));
}

void TermBlack::testXorTerm()
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  Term b = d_solver.mkTrue();
  TS_ASSERT_THROWS(Term().xorTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(b.xorTerm(Term()), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(b.xorTerm(b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  TS_ASSERT_THROWS(x.xorTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(x.xorTerm(x), CVC4ApiException&);
  Term f = d_solver.mkVar(funSort1, "f");
  TS_ASSERT_THROWS(f.xorTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(f.xorTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(f.xorTerm(f), CVC4ApiException&);
  Term p = d_solver.mkVar(funSort2, "p");
  TS_ASSERT_THROWS(p.xorTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(p.xorTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(p.xorTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(p.xorTerm(p), CVC4ApiException&);
  Term zero = d_solver.mkReal(0);
  TS_ASSERT_THROWS(zero.xorTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.xorTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.xorTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.xorTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.xorTerm(zero), CVC4ApiException&);
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  TS_ASSERT_THROWS(f_x.xorTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.xorTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.xorTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.xorTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.xorTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.xorTerm(f_x), CVC4ApiException&);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
  TS_ASSERT_THROWS(sum.xorTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.xorTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.xorTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.xorTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.xorTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.xorTerm(f_x), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.xorTerm(sum), CVC4ApiException&);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  TS_ASSERT_THROWS_NOTHING(p_0.xorTerm(b));
  TS_ASSERT_THROWS(p_0.xorTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.xorTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.xorTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.xorTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.xorTerm(f_x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.xorTerm(sum), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(p_0.xorTerm(p_0));
  Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
  TS_ASSERT_THROWS_NOTHING(p_f_x.xorTerm(b));
  TS_ASSERT_THROWS(p_f_x.xorTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.xorTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.xorTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.xorTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.xorTerm(f_x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.xorTerm(sum), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(p_f_x.xorTerm(p_0));
  TS_ASSERT_THROWS_NOTHING(p_f_x.xorTerm(p_f_x));
}

void TermBlack::testEqTerm()
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  Term b = d_solver.mkTrue();
  TS_ASSERT_THROWS(Term().eqTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(b.eqTerm(Term()), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(b.eqTerm(b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  TS_ASSERT_THROWS(x.eqTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(x.eqTerm(x));
  Term f = d_solver.mkVar(funSort1, "f");
  TS_ASSERT_THROWS(f.eqTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(f.eqTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(f.eqTerm(f));
  Term p = d_solver.mkVar(funSort2, "p");
  TS_ASSERT_THROWS(p.eqTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(p.eqTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(p.eqTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(p.eqTerm(p));
  Term zero = d_solver.mkReal(0);
  TS_ASSERT_THROWS(zero.eqTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.eqTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.eqTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.eqTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(zero.eqTerm(zero));
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  TS_ASSERT_THROWS(f_x.eqTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.eqTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.eqTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.eqTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(f_x.eqTerm(zero));
  TS_ASSERT_THROWS_NOTHING(f_x.eqTerm(f_x));
  Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
  TS_ASSERT_THROWS(sum.eqTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.eqTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.eqTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.eqTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(sum.eqTerm(zero));
  TS_ASSERT_THROWS_NOTHING(sum.eqTerm(f_x));
  TS_ASSERT_THROWS_NOTHING(sum.eqTerm(sum));
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  TS_ASSERT_THROWS_NOTHING(p_0.eqTerm(b));
  TS_ASSERT_THROWS(p_0.eqTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.eqTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.eqTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.eqTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.eqTerm(f_x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.eqTerm(sum), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(p_0.eqTerm(p_0));
  Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
  TS_ASSERT_THROWS_NOTHING(p_f_x.eqTerm(b));
  TS_ASSERT_THROWS(p_f_x.eqTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.eqTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.eqTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.eqTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.eqTerm(f_x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.eqTerm(sum), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(p_f_x.eqTerm(p_0));
  TS_ASSERT_THROWS_NOTHING(p_f_x.eqTerm(p_f_x));
}

void TermBlack::testImpTerm()
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  Term b = d_solver.mkTrue();
  TS_ASSERT_THROWS(Term().impTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(b.impTerm(Term()), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(b.impTerm(b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  TS_ASSERT_THROWS(x.impTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(x.impTerm(x), CVC4ApiException&);
  Term f = d_solver.mkVar(funSort1, "f");
  TS_ASSERT_THROWS(f.impTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(f.impTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(f.impTerm(f), CVC4ApiException&);
  Term p = d_solver.mkVar(funSort2, "p");
  TS_ASSERT_THROWS(p.impTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(p.impTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(p.impTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(p.impTerm(p), CVC4ApiException&);
  Term zero = d_solver.mkReal(0);
  TS_ASSERT_THROWS(zero.impTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.impTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.impTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.impTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.impTerm(zero), CVC4ApiException&);
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  TS_ASSERT_THROWS(f_x.impTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.impTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.impTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.impTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.impTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.impTerm(f_x), CVC4ApiException&);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
  TS_ASSERT_THROWS(sum.impTerm(b), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.impTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.impTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.impTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.impTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.impTerm(f_x), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.impTerm(sum), CVC4ApiException&);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  TS_ASSERT_THROWS_NOTHING(p_0.impTerm(b));
  TS_ASSERT_THROWS(p_0.impTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.impTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.impTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.impTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.impTerm(f_x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_0.impTerm(sum), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(p_0.impTerm(p_0));
  Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
  TS_ASSERT_THROWS_NOTHING(p_f_x.impTerm(b));
  TS_ASSERT_THROWS(p_f_x.impTerm(x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.impTerm(f), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.impTerm(p), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.impTerm(zero), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.impTerm(f_x), CVC4ApiException&);
  TS_ASSERT_THROWS(p_f_x.impTerm(sum), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(p_f_x.impTerm(p_0));
  TS_ASSERT_THROWS_NOTHING(p_f_x.impTerm(p_f_x));
}

void TermBlack::testIteTerm()
{
  Sort bvSort = d_solver.mkBitVectorSort(8);
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
  Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

  Term b = d_solver.mkTrue();
  TS_ASSERT_THROWS(Term().iteTerm(b, b), CVC4ApiException&);
  TS_ASSERT_THROWS(b.iteTerm(Term(), b), CVC4ApiException&);
  TS_ASSERT_THROWS(b.iteTerm(b, Term()), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(b.iteTerm(b, b));
  Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
  TS_ASSERT_THROWS_NOTHING(b.iteTerm(x, x));
  TS_ASSERT_THROWS_NOTHING(b.iteTerm(b, b));
  TS_ASSERT_THROWS(b.iteTerm(x, b), CVC4ApiException&);
  TS_ASSERT_THROWS(x.iteTerm(x, x), CVC4ApiException&);
  TS_ASSERT_THROWS(x.iteTerm(x, b), CVC4ApiException&);
  Term f = d_solver.mkVar(funSort1, "f");
  TS_ASSERT_THROWS(f.iteTerm(b, b), CVC4ApiException&);
  TS_ASSERT_THROWS(x.iteTerm(b, x), CVC4ApiException&);
  Term p = d_solver.mkVar(funSort2, "p");
  TS_ASSERT_THROWS(p.iteTerm(b, b), CVC4ApiException&);
  TS_ASSERT_THROWS(p.iteTerm(x, b), CVC4ApiException&);
  Term zero = d_solver.mkReal(0);
  TS_ASSERT_THROWS(zero.iteTerm(x, x), CVC4ApiException&);
  TS_ASSERT_THROWS(zero.iteTerm(x, b), CVC4ApiException&);
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  TS_ASSERT_THROWS(f_x.iteTerm(b, b), CVC4ApiException&);
  TS_ASSERT_THROWS(f_x.iteTerm(b, x), CVC4ApiException&);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
  TS_ASSERT_THROWS(sum.iteTerm(x, x), CVC4ApiException&);
  TS_ASSERT_THROWS(sum.iteTerm(b, x), CVC4ApiException&);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  TS_ASSERT_THROWS_NOTHING(p_0.iteTerm(b, b));
  TS_ASSERT_THROWS_NOTHING(p_0.iteTerm(x, x));
  TS_ASSERT_THROWS(p_0.iteTerm(x, b), CVC4ApiException&);
  Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
  TS_ASSERT_THROWS_NOTHING(p_f_x.iteTerm(b, b));
  TS_ASSERT_THROWS_NOTHING(p_f_x.iteTerm(x, x));
  TS_ASSERT_THROWS(p_f_x.iteTerm(x, b), CVC4ApiException&);
}

void TermBlack::testTermAssignment()
{
  Term t1 = d_solver.mkReal(1);
  Term t2 = t1;
  t2 = d_solver.mkReal(2);
  TS_ASSERT_EQUALS(t1, d_solver.mkReal(1));
}

void TermBlack::testTermCompare()
{
  Term t1 = d_solver.mkReal(1);
  Term t2 = d_solver.mkTerm(PLUS, d_solver.mkReal(2), d_solver.mkReal(2));
  Term t3 = d_solver.mkTerm(PLUS, d_solver.mkReal(2), d_solver.mkReal(2));
  TS_ASSERT(t2 >= t3);
  TS_ASSERT(t2 <= t3);
  TS_ASSERT((t1 > t2) != (t1 < t2));
  TS_ASSERT((t1 > t2 || t1 == t2) == (t1 >= t2));
}

void TermBlack::testTermChildren()
{
  // simple term 2+3
  Term two = d_solver.mkReal(2);
  Term t1 = d_solver.mkTerm(PLUS, two, d_solver.mkReal(3));
  TS_ASSERT(t1[0] == two);
  TS_ASSERT(t1.getNumChildren() == 2);
  Term tnull;
  TS_ASSERT_THROWS(tnull.getNumChildren(), CVC4ApiException&);

  // apply term f(2)
  Sort intSort = d_solver.getIntegerSort();
  Sort fsort = d_solver.mkFunctionSort(intSort, intSort);
  Term f = d_solver.mkConst(fsort, "f");
  Term t2 = d_solver.mkTerm(APPLY_UF, f, two);
  // due to our higher-order view of terms, we treat f as a child of APPLY_UF
  TS_ASSERT(t2.getNumChildren() == 2);
  TS_ASSERT_EQUALS(t2[0], f);
  TS_ASSERT_EQUALS(t2[1], two);
  TS_ASSERT_THROWS(tnull[0], CVC4ApiException&);
}

void TermBlack::testSubstitute()
{
  Term x = d_solver.mkConst(d_solver.getIntegerSort(), "x");
  Term one = d_solver.mkReal(1);
  Term ttrue = d_solver.mkTrue();
  Term xpx = d_solver.mkTerm(PLUS, x, x);
  Term onepone = d_solver.mkTerm(PLUS, one, one);

  TS_ASSERT_EQUALS(xpx.substitute(x, one), onepone);
  TS_ASSERT_EQUALS(onepone.substitute(one, x), xpx);
  // incorrect due to type
  TS_ASSERT_THROWS(xpx.substitute(one, ttrue), CVC4ApiException&);

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
  TS_ASSERT_EQUALS(xpy.substitute(es, rs), xpone);

  // incorrect substitution due to arity
  rs.pop_back();
  TS_ASSERT_THROWS(xpy.substitute(es, rs), CVC4ApiException&);

  // incorrect substitution due to types
  rs.push_back(ttrue);
  TS_ASSERT_THROWS(xpy.substitute(es, rs), CVC4ApiException&);

  // null cannot substitute
  Term tnull;
  TS_ASSERT_THROWS(tnull.substitute(one, x), CVC4ApiException&);
  TS_ASSERT_THROWS(xpx.substitute(tnull, x), CVC4ApiException&);
  TS_ASSERT_THROWS(xpx.substitute(x, tnull), CVC4ApiException&);
  rs.pop_back();
  rs.push_back(tnull);
  TS_ASSERT_THROWS(xpy.substitute(es, rs), CVC4ApiException&);
  es.clear();
  rs.clear();
  es.push_back(x);
  rs.push_back(y);
  TS_ASSERT_THROWS(tnull.substitute(es, rs), CVC4ApiException&);
  es.push_back(tnull);
  rs.push_back(one);
  TS_ASSERT_THROWS(xpx.substitute(es, rs), CVC4ApiException&);
}

void TermBlack::testIsConst()
{
  Term x = d_solver.mkConst(d_solver.getIntegerSort(), "x");
  Term one = d_solver.mkReal(1);
  Term xpone = d_solver.mkTerm(PLUS, x, one);
  Term onepone = d_solver.mkTerm(PLUS, one, one);
  TS_ASSERT(!x.isConst());
  TS_ASSERT(one.isConst());
  TS_ASSERT(!xpone.isConst());
  TS_ASSERT(!onepone.isConst());
  Term tnull;
  TS_ASSERT_THROWS(tnull.isConst(), CVC4ApiException&);
}

void TermBlack::testConstArray()
{
  Sort intsort = d_solver.getIntegerSort();
  Sort arrsort = d_solver.mkArraySort(intsort, intsort);
  Term a = d_solver.mkConst(arrsort, "a");
  Term one = d_solver.mkReal(1);
  Term constarr = d_solver.mkConstArray(arrsort, one);

  TS_ASSERT(!a.isConst());
  TS_ASSERT(constarr.isConst());

  TS_ASSERT_EQUALS(constarr.getKind(), CONST_ARRAY);
  TS_ASSERT_EQUALS(constarr.getConstArrayBase(), one);
  TS_ASSERT_THROWS(a.getConstArrayBase(), CVC4ApiException&);
}

void TermBlack::testConstSequenceElements()
{
  Sort realsort = d_solver.getRealSort();
  Sort seqsort = d_solver.mkSequenceSort(realsort);
  Term s = d_solver.mkEmptySequence(seqsort);

  TS_ASSERT(s.isConst());

  TS_ASSERT_EQUALS(s.getKind(), CONST_SEQUENCE);
  // empty sequence has zero elements
  std::vector<Term> cs = s.getConstSequenceElements();
  TS_ASSERT(cs.empty());

  // A seq.unit app is not a constant sequence (regardless of whether it is
  // applied to a constant).
  Term su = d_solver.mkTerm(SEQ_UNIT, d_solver.mkReal(1));
  TS_ASSERT_THROWS(su.getConstSequenceElements(), CVC4ApiException&);
}
