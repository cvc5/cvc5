/*********************                                                        */
/*! \file api_guards_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the guards of the C++ API functions.
 **
 ** Black box testing of the guards of the C++ API functions.
 **/

#include <cxxtest/TestSuite.h>

#include "api/cvc4cpp.h"

using namespace CVC4::api;

class SolverBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override;
  void tearDown() override;

  void testMkBitVectorSort();
  void testMkFloatingPointSort();
  void testMkDatatypeSort();
  void testMkFunctionSort();
  void testMkPredicateSort();
  void testMkTupleSort();
  void testDeclareFun();
  void testDefineFun();
  void testDefineFunRec();
  void testDefineFunsRec();

 private:
  Solver d_solver;
};

void SolverBlack::setUp() {}

void SolverBlack::tearDown() {}

void SolverBlack::testMkBitVectorSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkBitVectorSort(32));
  TS_ASSERT_THROWS(d_solver.mkBitVectorSort(0), CVC4ApiException&);
}

void SolverBlack::testMkFloatingPointSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkFloatingPointSort(4, 8));
  TS_ASSERT_THROWS(d_solver.mkFloatingPointSort(0, 8), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkFloatingPointSort(4, 0), CVC4ApiException&);
}

void SolverBlack::testMkDatatypeSort()
{
  DatatypeDecl dtypeSpec("list");
  DatatypeConstructorDecl cons("cons");
  DatatypeSelectorDecl head("head", d_solver.getIntegerSort());
  cons.addSelector(head);
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil("nil");
  dtypeSpec.addConstructor(nil);
  TS_ASSERT_THROWS_NOTHING(d_solver.mkDatatypeSort(dtypeSpec));
  DatatypeDecl throwsDtypeSpec("list");
  TS_ASSERT_THROWS(d_solver.mkDatatypeSort(throwsDtypeSpec), CVC4ApiException&);
}

void SolverBlack::testMkFunctionSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkFunctionSort(
      d_solver.mkUninterpretedSort("u"), d_solver.getIntegerSort()));
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  TS_ASSERT_THROWS(d_solver.mkFunctionSort(funSort, d_solver.getIntegerSort()),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkFunctionSort(d_solver.getIntegerSort(), funSort),
                   CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(d_solver.mkFunctionSort(
      {d_solver.mkUninterpretedSort("u"), d_solver.getIntegerSort()},
      d_solver.getIntegerSort()));
  Sort funSort2 = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                          d_solver.getIntegerSort());
  TS_ASSERT_THROWS(
      d_solver.mkFunctionSort({funSort2, d_solver.mkUninterpretedSort("u")},
                              d_solver.getIntegerSort()),
      CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkFunctionSort({d_solver.getIntegerSort(),
                                            d_solver.mkUninterpretedSort("u")},
                                           funSort2),
                   CVC4ApiException&);
}

void SolverBlack::testMkPredicateSort()
{
  TS_ASSERT_THROWS_NOTHING(
      d_solver.mkPredicateSort({d_solver.getIntegerSort()}));
  TS_ASSERT_THROWS(d_solver.mkPredicateSort({}), CVC4ApiException&);
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  TS_ASSERT_THROWS(
      d_solver.mkPredicateSort({d_solver.getIntegerSort(), funSort}),
      CVC4ApiException&);
}

void SolverBlack::testMkTupleSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkTupleSort({d_solver.getIntegerSort()}));
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  TS_ASSERT_THROWS(d_solver.mkTupleSort({d_solver.getIntegerSort(), funSort}),
                   CVC4ApiException&);
}

void SolverBlack::testDeclareFun()
{
  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  TS_ASSERT_THROWS_NOTHING(d_solver.declareFun("f1", bvSort));
  TS_ASSERT_THROWS_NOTHING(d_solver.declareFun("f2", funSort));
  TS_ASSERT_THROWS_NOTHING(
      d_solver.declareFun("f3", {bvSort, d_solver.getIntegerSort()}, bvSort));
  TS_ASSERT_THROWS(d_solver.declareFun("f4", {bvSort, funSort}, bvSort),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.declareFun("f5", {bvSort, bvSort}, funSort),
                   CVC4ApiException&);
}

void SolverBlack::testDefineFun()
{
  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort funSort1 = d_solver.mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                          d_solver.getIntegerSort());
  Term b1 = d_solver.mkBoundVar("b1", bvSort);
  Term b11 = d_solver.mkBoundVar("b1", bvSort);
  Term b2 = d_solver.mkBoundVar("b2", d_solver.getIntegerSort());
  Term b3 = d_solver.mkBoundVar("b3", funSort2);
  Term v1 = d_solver.mkBoundVar("v1", bvSort);
  Term v2 = d_solver.mkBoundVar("v2", d_solver.getIntegerSort());
  Term v3 = d_solver.mkVar("v3", funSort2);
  Term f1 = d_solver.declareFun("f1", funSort1);
  Term f2 = d_solver.declareFun("f2", funSort2);
  Term f3 = d_solver.declareFun("f3", bvSort);
  TS_ASSERT_THROWS_NOTHING(d_solver.defineFun("f", {}, bvSort, v1));
  TS_ASSERT_THROWS_NOTHING(d_solver.defineFun("ff", {b1, b2}, bvSort, v1));
  TS_ASSERT_THROWS_NOTHING(d_solver.defineFun(f1, {b1, b11}, v1));
  TS_ASSERT_THROWS(d_solver.defineFun("fff", {b1}, bvSort, v3),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.defineFun("ffff", {b1}, funSort2, v3),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.defineFun("fffff", {b1, b3}, bvSort, v1),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.defineFun(f1, {b1}, v1), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.defineFun(f1, {b1, b11}, v2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.defineFun(f1, {b1, b11}, v3), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.defineFun(f2, {b1}, v2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.defineFun(f3, {b1}, v1), CVC4ApiException&);
}

void SolverBlack::testDefineFunRec()
{
  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort funSort1 = d_solver.mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                          d_solver.getIntegerSort());
  Term b1 = d_solver.mkBoundVar("b1", bvSort);
  Term b11 = d_solver.mkBoundVar("b1", bvSort);
  Term b2 = d_solver.mkBoundVar("b2", d_solver.getIntegerSort());
  Term b3 = d_solver.mkBoundVar("b3", funSort2);
  Term v1 = d_solver.mkBoundVar("v1", bvSort);
  Term v2 = d_solver.mkBoundVar("v2", d_solver.getIntegerSort());
  Term v3 = d_solver.mkVar("v3", funSort2);
  Term f1 = d_solver.declareFun("f1", funSort1);
  Term f2 = d_solver.declareFun("f2", funSort2);
  Term f3 = d_solver.declareFun("f3", bvSort);
  TS_ASSERT_THROWS_NOTHING(d_solver.defineFunRec("f", {}, bvSort, v1));
  TS_ASSERT_THROWS_NOTHING(d_solver.defineFunRec("ff", {b1, b2}, bvSort, v1));
  TS_ASSERT_THROWS_NOTHING(d_solver.defineFunRec(f1, {b1, b11}, v1));
  TS_ASSERT_THROWS(d_solver.defineFunRec("fff", {b1}, bvSort, v3),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.defineFunRec("ffff", {b1}, funSort2, v3),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.defineFunRec("fffff", {b1, b3}, bvSort, v1),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.defineFunRec(f1, {b1}, v1), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.defineFunRec(f1, {b1, b11}, v2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.defineFunRec(f1, {b1, b11}, v3), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.defineFunRec(f2, {b1}, v2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.defineFunRec(f3, {b1}, v1), CVC4ApiException&);
}

void SolverBlack::testDefineFunsRec()
{
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort funSort1 = d_solver.mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_solver.mkFunctionSort(uSort, d_solver.getIntegerSort());
  Term b1 = d_solver.mkBoundVar("b1", bvSort);
  Term b11 = d_solver.mkBoundVar("b1", bvSort);
  Term b2 = d_solver.mkBoundVar("b2", d_solver.getIntegerSort());
  Term b3 = d_solver.mkBoundVar("b3", funSort2);
  Term b4 = d_solver.mkBoundVar("b4", uSort);
  Term v1 = d_solver.mkBoundVar("v1", bvSort);
  Term v2 = d_solver.mkBoundVar("v2", d_solver.getIntegerSort());
  Term v3 = d_solver.mkVar("v3", funSort2);
  Term v4 = d_solver.mkVar("v4", uSort);
  Term f1 = d_solver.declareFun("f1", funSort1);
  Term f2 = d_solver.declareFun("f2", funSort2);
  Term f3 = d_solver.declareFun("f3", bvSort);
  TS_ASSERT_THROWS_NOTHING(
      d_solver.defineFunsRec({f1, f2}, {{b1, b11}, {b4}}, {v1, v2}));
  TS_ASSERT_THROWS(
      d_solver.defineFunsRec({f1, f3}, {{b1, b11}, {b4}}, {v1, v2}),
      CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.defineFunsRec({f1, f2}, {{b1}, {b4}}, {v1, v2}),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.defineFunsRec({f1, f2}, {{b1, b2}, {b4}}, {v1, v2}),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver.defineFunsRec({f1, f2}, {{b1, b11}, {b4}}, {v1, v4}),
      CVC4ApiException&);
}
