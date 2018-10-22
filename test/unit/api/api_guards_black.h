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

class ApiGuardsBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override;
  void tearDown() override;

  void testSolverMkBitVectorSort();
  void testSolverMkFloatingPointSort();
  void testSolverMkDatatypeSort();
  void testSolverMkFunctionSort();
  void testSolverMkPredicateSort();
  void testSolverMkTupleSort();
  void testSortGetDatatype();
  void testSortInstantiate();
  void testSortGetFunctionArity();
  void testSortGetFunctionDomainSorts();
  void testSortGetFunctionCodomainSort();
  void testSortGetArrayIndexSort();
  void testSortGetArrayElementSort();
  void testSortGetSetElementSort();
  void testSortGetUninterpretedSortName();
  void testSortIsUninterpretedSortParameterized();
  void testSortGetUninterpretedSortParamSorts();
  void testSortGetUninterpretedSortConstructorName();
  void testSortGetUninterpretedSortConstructorArity();
  void testSortGetBVSize();
  void testSortGetFPExponentSize();
  void testSortGetFPSignificandSize();
  void testSortGetDatatypeParamSorts();
  void testSortGetDatatypeArity();
  void testSortGetTupleLength();
  void testSortGetTupleSorts();
  void testSolverDeclareFun();
  void testSolverDefineFun();
  void testSolverDefineFunRec();
  void testSolverDefineFunsRec();

 private:
  Solver d_solver;
};

void ApiGuardsBlack::setUp() {}

void ApiGuardsBlack::tearDown() {}

void ApiGuardsBlack::testSolverMkBitVectorSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkBitVectorSort(32));
  TS_ASSERT_THROWS(d_solver.mkBitVectorSort(0), CVC4ApiException&);
}

void ApiGuardsBlack::testSolverMkFloatingPointSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkFloatingPointSort(4, 8));
  TS_ASSERT_THROWS(d_solver.mkFloatingPointSort(0, 8), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkFloatingPointSort(4, 0), CVC4ApiException&);
}

void ApiGuardsBlack::testSolverMkDatatypeSort()
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

void ApiGuardsBlack::testSolverMkFunctionSort()
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

void ApiGuardsBlack::testSolverMkPredicateSort()
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

void ApiGuardsBlack::testSolverMkTupleSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkTupleSort({d_solver.getIntegerSort()}));
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  TS_ASSERT_THROWS(d_solver.mkTupleSort({d_solver.getIntegerSort(), funSort}),
                   CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetDatatype()
{
  // create datatype sort, check should not fail
  DatatypeDecl dtypeSpec("list");
  DatatypeConstructorDecl cons("cons");
  DatatypeSelectorDecl head("head", d_solver.getIntegerSort());
  cons.addSelector(head);
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil("nil");
  dtypeSpec.addConstructor(nil);
  Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
  TS_ASSERT_THROWS_NOTHING(dtypeSort.getDatatype());
  // create bv sort, check should fail
  Sort bvSort = d_solver.mkBitVectorSort(32);
  TS_ASSERT_THROWS(bvSort.getDatatype(), CVC4ApiException&);
}

void ApiGuardsBlack::testSortInstantiate()
{
  // instantiate parametric datatype, check should not fail
  Sort sort = d_solver.mkParamSort("T");
  DatatypeDecl paramDtypeSpec("paramlist", sort);
  DatatypeConstructorDecl paramCons("cons");
  DatatypeConstructorDecl paramNil("nil");
  DatatypeSelectorDecl paramHead("head", sort);
  paramCons.addSelector(paramHead);
  paramDtypeSpec.addConstructor(paramCons);
  paramDtypeSpec.addConstructor(paramNil);
  Sort paramDtypeSort = d_solver.mkDatatypeSort(paramDtypeSpec);
  TS_ASSERT_THROWS_NOTHING(
      paramDtypeSort.instantiate(std::vector<Sort>{d_solver.getIntegerSort()}));
  // instantiate non-parametric datatype sort, check should fail
  DatatypeDecl dtypeSpec("list");
  DatatypeConstructorDecl cons("cons");
  DatatypeSelectorDecl head("head", d_solver.getIntegerSort());
  cons.addSelector(head);
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil("nil");
  dtypeSpec.addConstructor(nil);
  Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
  TS_ASSERT_THROWS(
      dtypeSort.instantiate(std::vector<Sort>{d_solver.getIntegerSort()}),
      CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetFunctionArity()
{
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  TS_ASSERT_THROWS_NOTHING(funSort.getFunctionArity());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  TS_ASSERT_THROWS(bvSort.getFunctionArity(), CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetFunctionDomainSorts()
{
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  TS_ASSERT_THROWS_NOTHING(funSort.getFunctionDomainSorts());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  TS_ASSERT_THROWS(bvSort.getFunctionDomainSorts(), CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetFunctionCodomainSort()
{
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  TS_ASSERT_THROWS_NOTHING(funSort.getFunctionCodomainSort());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  TS_ASSERT_THROWS(bvSort.getFunctionCodomainSort(), CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetArrayIndexSort()
{
  Sort elementSort = d_solver.mkBitVectorSort(32);
  Sort indexSort = d_solver.mkBitVectorSort(32);
  Sort arraySort = d_solver.mkArraySort(indexSort, elementSort);
  TS_ASSERT_THROWS_NOTHING(arraySort.getArrayIndexSort());
  TS_ASSERT_THROWS(indexSort.getArrayIndexSort(), CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetArrayElementSort()
{
  Sort elementSort = d_solver.mkBitVectorSort(32);
  Sort indexSort = d_solver.mkBitVectorSort(32);
  Sort arraySort = d_solver.mkArraySort(indexSort, elementSort);
  TS_ASSERT_THROWS_NOTHING(arraySort.getArrayElementSort());
  TS_ASSERT_THROWS(indexSort.getArrayElementSort(), CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetSetElementSort()
{
  Sort setSort = d_solver.mkSetSort(d_solver.getIntegerSort());
  TS_ASSERT_THROWS_NOTHING(setSort.getSetElementSort());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  TS_ASSERT_THROWS(bvSort.getSetElementSort(), CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetUninterpretedSortName()
{
  Sort uSort = d_solver.mkUninterpretedSort("u");
  TS_ASSERT_THROWS_NOTHING(uSort.getUninterpretedSortName());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  TS_ASSERT_THROWS(bvSort.getUninterpretedSortName(), CVC4ApiException&);
}

void ApiGuardsBlack::testSortIsUninterpretedSortParameterized()
{
  Sort uSort = d_solver.mkUninterpretedSort("u");
  TS_ASSERT_THROWS_NOTHING(uSort.isUninterpretedSortParameterized());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  TS_ASSERT_THROWS(bvSort.isUninterpretedSortParameterized(),
                   CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetUninterpretedSortParamSorts()
{
  Sort uSort = d_solver.mkUninterpretedSort("u");
  TS_ASSERT_THROWS_NOTHING(uSort.getUninterpretedSortParamSorts());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  TS_ASSERT_THROWS(bvSort.getUninterpretedSortParamSorts(), CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetUninterpretedSortConstructorName()
{
  Sort sSort = d_solver.mkSortConstructorSort("s", 2);
  TS_ASSERT_THROWS_NOTHING(sSort.getSortConstructorName());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  TS_ASSERT_THROWS(bvSort.getSortConstructorName(), CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetUninterpretedSortConstructorArity()
{
  Sort sSort = d_solver.mkSortConstructorSort("s", 2);
  TS_ASSERT_THROWS_NOTHING(sSort.getSortConstructorArity());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  TS_ASSERT_THROWS(bvSort.getSortConstructorArity(), CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetBVSize()
{
  Sort bvSort = d_solver.mkBitVectorSort(32);
  TS_ASSERT_THROWS_NOTHING(bvSort.getBVSize());
  Sort setSort = d_solver.mkSetSort(d_solver.getIntegerSort());
  TS_ASSERT_THROWS(setSort.getBVSize(), CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetFPExponentSize()
{
  Sort fpSort = d_solver.mkFloatingPointSort(4, 8);
  TS_ASSERT_THROWS_NOTHING(fpSort.getFPExponentSize());
  Sort setSort = d_solver.mkSetSort(d_solver.getIntegerSort());
  TS_ASSERT_THROWS(setSort.getFPExponentSize(), CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetFPSignificandSize()
{
  Sort fpSort = d_solver.mkFloatingPointSort(4, 8);
  TS_ASSERT_THROWS_NOTHING(fpSort.getFPSignificandSize());
  Sort setSort = d_solver.mkSetSort(d_solver.getIntegerSort());
  TS_ASSERT_THROWS(setSort.getFPSignificandSize(), CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetDatatypeParamSorts()
{
  // create parametric datatype, check should not fail
  Sort sort = d_solver.mkParamSort("T");
  DatatypeDecl paramDtypeSpec("paramlist", sort);
  DatatypeConstructorDecl paramCons("cons");
  DatatypeConstructorDecl paramNil("nil");
  DatatypeSelectorDecl paramHead("head", sort);
  paramCons.addSelector(paramHead);
  paramDtypeSpec.addConstructor(paramCons);
  paramDtypeSpec.addConstructor(paramNil);
  Sort paramDtypeSort = d_solver.mkDatatypeSort(paramDtypeSpec);
  TS_ASSERT_THROWS_NOTHING(paramDtypeSort.getDatatypeParamSorts());
  // create non-parametric datatype sort, check should fail
  DatatypeDecl dtypeSpec("list");
  DatatypeConstructorDecl cons("cons");
  DatatypeSelectorDecl head("head", d_solver.getIntegerSort());
  cons.addSelector(head);
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil("nil");
  dtypeSpec.addConstructor(nil);
  Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
  TS_ASSERT_THROWS(dtypeSort.getDatatypeParamSorts(), CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetDatatypeArity()
{
  // create datatype sort, check should not fail
  DatatypeDecl dtypeSpec("list");
  DatatypeConstructorDecl cons("cons");
  DatatypeSelectorDecl head("head", d_solver.getIntegerSort());
  cons.addSelector(head);
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil("nil");
  dtypeSpec.addConstructor(nil);
  Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
  TS_ASSERT_THROWS_NOTHING(dtypeSort.getDatatypeArity());
  // create bv sort, check should fail
  Sort bvSort = d_solver.mkBitVectorSort(32);
  TS_ASSERT_THROWS(bvSort.getDatatypeArity(), CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetTupleLength()
{
  Sort tupleSort = d_solver.mkTupleSort(
      {d_solver.getIntegerSort(), d_solver.getIntegerSort()});
  TS_ASSERT_THROWS_NOTHING(tupleSort.getTupleLength());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  TS_ASSERT_THROWS(bvSort.getTupleLength(), CVC4ApiException&);
}

void ApiGuardsBlack::testSortGetTupleSorts()
{
  Sort tupleSort = d_solver.mkTupleSort(
      {d_solver.getIntegerSort(), d_solver.getIntegerSort()});
  TS_ASSERT_THROWS_NOTHING(tupleSort.getTupleSorts());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  TS_ASSERT_THROWS(bvSort.getTupleSorts(), CVC4ApiException&);
}

void ApiGuardsBlack::testSolverDeclareFun()
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

void ApiGuardsBlack::testSolverDefineFun()
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

void ApiGuardsBlack::testSolverDefineFunRec()
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

void ApiGuardsBlack::testSolverDefineFunsRec()
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
