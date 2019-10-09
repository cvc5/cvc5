/*********************                                                        */
/*! \file term_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
  void testIsNull();
  void testIsParameterized();
  void testNotTerm();
  void testAndTerm();
  void testOrTerm();
  void testXorTerm();
  void testEqTerm();
  void testImpTerm();
  void testIteTerm();

  void testTermAssignment();

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

void TermBlack::testIsParameterized()
{
  Term n;
  TS_ASSERT_THROWS(n.isParameterized(), CVC4ApiException&);
  Term x = d_solver.mkVar(d_solver.getIntegerSort(), "x");
  TS_ASSERT_THROWS_NOTHING(x.isParameterized());
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
