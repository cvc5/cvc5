/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the guards of the C++ API functions.
 */

#include "test_api.h"

namespace cvc5 {

using namespace api;

namespace test {

class TestApiBlackSort : public TestApi
{
 protected:
  Sort create_datatype_sort()
  {
    DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", d_solver.getIntegerSort());
    cons.addSelectorSelf("tail");
    dtypeSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
    dtypeSpec.addConstructor(nil);
    return d_solver.mkDatatypeSort(dtypeSpec);
  }

  Sort create_param_datatype_sort()
  {
    Sort sort = d_solver.mkParamSort("T");
    DatatypeDecl paramDtypeSpec = d_solver.mkDatatypeDecl("paramlist", sort);
    DatatypeConstructorDecl paramCons =
        d_solver.mkDatatypeConstructorDecl("cons");
    DatatypeConstructorDecl paramNil =
        d_solver.mkDatatypeConstructorDecl("nil");
    paramCons.addSelector("head", sort);
    paramDtypeSpec.addConstructor(paramCons);
    paramDtypeSpec.addConstructor(paramNil);
    return d_solver.mkDatatypeSort(paramDtypeSpec);
  }
};

TEST_F(TestApiBlackSort, operators_comparison)
{
  ASSERT_NO_THROW(d_solver.getIntegerSort() == Sort());
  ASSERT_NO_THROW(d_solver.getIntegerSort() != Sort());
  ASSERT_NO_THROW(d_solver.getIntegerSort() < Sort());
  ASSERT_NO_THROW(d_solver.getIntegerSort() <= Sort());
  ASSERT_NO_THROW(d_solver.getIntegerSort() > Sort());
  ASSERT_NO_THROW(d_solver.getIntegerSort() >= Sort());
}

TEST_F(TestApiBlackSort, hasGetSymbol)
{
  Sort n;
  Sort b = d_solver.getBooleanSort();
  Sort s0 = d_solver.mkParamSort("s0");
  Sort s1 = d_solver.mkParamSort("|s1\\|");

  ASSERT_THROW(n.hasSymbol(), CVC5ApiException);
  ASSERT_FALSE(b.hasSymbol());
  ASSERT_TRUE(s0.hasSymbol());
  ASSERT_TRUE(s1.hasSymbol());

  ASSERT_THROW(n.getSymbol(), CVC5ApiException);
  ASSERT_THROW(b.getSymbol(), CVC5ApiException);
  ASSERT_EQ(s0.getSymbol(), "s0");
  ASSERT_EQ(s1.getSymbol(), "|s1\\|");
}

TEST_F(TestApiBlackSort, isNull)
{
  Sort x;
  ASSERT_TRUE(x.isNull());
  x = d_solver.getBooleanSort();
  ASSERT_FALSE(x.isNull());
}

TEST_F(TestApiBlackSort, isBoolean)
{
  ASSERT_TRUE(d_solver.getBooleanSort().isBoolean());
  ASSERT_NO_THROW(Sort().isBoolean());
}

TEST_F(TestApiBlackSort, isInteger)
{
  ASSERT_TRUE(d_solver.getIntegerSort().isInteger());
  ASSERT_TRUE(!d_solver.getRealSort().isInteger());
  ASSERT_NO_THROW(Sort().isInteger());
}

TEST_F(TestApiBlackSort, isReal)
{
  ASSERT_TRUE(d_solver.getRealSort().isReal());
  ASSERT_TRUE(!d_solver.getIntegerSort().isReal());
  ASSERT_NO_THROW(Sort().isReal());
}

TEST_F(TestApiBlackSort, isString)
{
  ASSERT_TRUE(d_solver.getStringSort().isString());
  ASSERT_NO_THROW(Sort().isString());
}

TEST_F(TestApiBlackSort, isRegExp)
{
  ASSERT_TRUE(d_solver.getRegExpSort().isRegExp());
  ASSERT_NO_THROW(Sort().isRegExp());
}

TEST_F(TestApiBlackSort, isRoundingMode)
{
  ASSERT_TRUE(d_solver.getRoundingModeSort().isRoundingMode());
  ASSERT_NO_THROW(Sort().isRoundingMode());
}

TEST_F(TestApiBlackSort, isBitVector)
{
  ASSERT_TRUE(d_solver.mkBitVectorSort(8).isBitVector());
  ASSERT_NO_THROW(Sort().isBitVector());
}

TEST_F(TestApiBlackSort, isFloatingPoint)
{
  ASSERT_TRUE(d_solver.mkFloatingPointSort(8, 24).isFloatingPoint());
  ASSERT_NO_THROW(Sort().isFloatingPoint());
}

TEST_F(TestApiBlackSort, isDatatype)
{
  Sort dt_sort = create_datatype_sort();
  ASSERT_TRUE(dt_sort.isDatatype());
  ASSERT_NO_THROW(Sort().isDatatype());
}

TEST_F(TestApiBlackSort, isParametricDatatype)
{
  Sort param_dt_sort = create_param_datatype_sort();
  ASSERT_TRUE(param_dt_sort.isParametricDatatype());
  ASSERT_NO_THROW(Sort().isParametricDatatype());
}

TEST_F(TestApiBlackSort, isConstructor)
{
  Sort dt_sort = create_datatype_sort();
  Datatype dt = dt_sort.getDatatype();
  Sort cons_sort = dt[0].getConstructorTerm().getSort();
  ASSERT_TRUE(cons_sort.isConstructor());
  ASSERT_NO_THROW(Sort().isConstructor());
}

TEST_F(TestApiBlackSort, isSelector)
{
  Sort dt_sort = create_datatype_sort();
  Datatype dt = dt_sort.getDatatype();
  Sort cons_sort = dt[0][1].getSelectorTerm().getSort();
  ASSERT_TRUE(cons_sort.isSelector());
  ASSERT_NO_THROW(Sort().isSelector());
}

TEST_F(TestApiBlackSort, isTester)
{
  Sort dt_sort = create_datatype_sort();
  Datatype dt = dt_sort.getDatatype();
  Sort testerSort = dt[0].getTesterTerm().getSort();
  ASSERT_TRUE(testerSort.isTester());
  ASSERT_NO_THROW(Sort().isTester());
}

TEST_F(TestApiBlackSort, isUpdater)
{
  Sort dt_sort = create_datatype_sort();
  Datatype dt = dt_sort.getDatatype();
  Sort updaterSort = dt[0][0].getUpdaterTerm().getSort();
  ASSERT_TRUE(updaterSort.isUpdater());
  ASSERT_NO_THROW(Sort().isUpdater());
}

TEST_F(TestApiBlackSort, isFunction)
{
  Sort fun_sort = d_solver.mkFunctionSort(d_solver.getRealSort(),
                                          d_solver.getIntegerSort());
  ASSERT_TRUE(fun_sort.isFunction());
  ASSERT_NO_THROW(Sort().isFunction());
}

TEST_F(TestApiBlackSort, isPredicate)
{
  Sort pred_sort = d_solver.mkPredicateSort({d_solver.getRealSort()});
  ASSERT_TRUE(pred_sort.isPredicate());
  ASSERT_NO_THROW(Sort().isPredicate());
}

TEST_F(TestApiBlackSort, isTuple)
{
  Sort tup_sort = d_solver.mkTupleSort({d_solver.getRealSort()});
  ASSERT_TRUE(tup_sort.isTuple());
  ASSERT_NO_THROW(Sort().isTuple());
}

TEST_F(TestApiBlackSort, isRecord)
{
  Sort rec_sort =
      d_solver.mkRecordSort({std::make_pair("asdf", d_solver.getRealSort())});
  ASSERT_TRUE(rec_sort.isRecord());
  ASSERT_NO_THROW(Sort().isRecord());
}

TEST_F(TestApiBlackSort, isArray)
{
  Sort arr_sort =
      d_solver.mkArraySort(d_solver.getRealSort(), d_solver.getIntegerSort());
  ASSERT_TRUE(arr_sort.isArray());
  ASSERT_NO_THROW(Sort().isArray());
}

TEST_F(TestApiBlackSort, isSet)
{
  Sort set_sort = d_solver.mkSetSort(d_solver.getRealSort());
  ASSERT_TRUE(set_sort.isSet());
  ASSERT_NO_THROW(Sort().isSet());
}

TEST_F(TestApiBlackSort, isBag)
{
  Sort bag_sort = d_solver.mkBagSort(d_solver.getRealSort());
  ASSERT_TRUE(bag_sort.isBag());
  ASSERT_NO_THROW(Sort().isBag());
}

TEST_F(TestApiBlackSort, isSequence)
{
  Sort seq_sort = d_solver.mkSequenceSort(d_solver.getRealSort());
  ASSERT_TRUE(seq_sort.isSequence());
  ASSERT_NO_THROW(Sort().isSequence());
}

TEST_F(TestApiBlackSort, isUninterpreted)
{
  Sort un_sort = d_solver.mkUninterpretedSort("asdf");
  ASSERT_TRUE(un_sort.isUninterpretedSort());
  ASSERT_NO_THROW(Sort().isUninterpretedSort());
}

TEST_F(TestApiBlackSort, isSortConstructor)
{
  Sort sc_sort = d_solver.mkSortConstructorSort("asdf", 1);
  ASSERT_TRUE(sc_sort.isSortConstructor());
  ASSERT_NO_THROW(Sort().isSortConstructor());
}

TEST_F(TestApiBlackSort, isFirstClass)
{
  Sort fun_sort = d_solver.mkFunctionSort(d_solver.getRealSort(),
                                          d_solver.getIntegerSort());
  ASSERT_TRUE(d_solver.getIntegerSort().isFirstClass());
  ASSERT_TRUE(fun_sort.isFirstClass());
  Sort reSort = d_solver.getRegExpSort();
  ASSERT_FALSE(reSort.isFirstClass());
  ASSERT_NO_THROW(Sort().isFirstClass());
}

TEST_F(TestApiBlackSort, isFunctionLike)
{
  Sort fun_sort = d_solver.mkFunctionSort(d_solver.getRealSort(),
                                          d_solver.getIntegerSort());
  ASSERT_FALSE(d_solver.getIntegerSort().isFunctionLike());
  ASSERT_TRUE(fun_sort.isFunctionLike());

  Sort dt_sort = create_datatype_sort();
  Datatype dt = dt_sort.getDatatype();
  Sort cons_sort = dt[0][1].getSelectorTerm().getSort();
  ASSERT_TRUE(cons_sort.isFunctionLike());

  ASSERT_NO_THROW(Sort().isFunctionLike());
}

TEST_F(TestApiBlackSort, isSubsortOf)
{
  ASSERT_TRUE(d_solver.getIntegerSort().isSubsortOf(d_solver.getIntegerSort()));
  ASSERT_TRUE(d_solver.getIntegerSort().isSubsortOf(d_solver.getRealSort()));
  ASSERT_FALSE(
      d_solver.getIntegerSort().isSubsortOf(d_solver.getBooleanSort()));
  ASSERT_NO_THROW(Sort().isSubsortOf(Sort()));
}

TEST_F(TestApiBlackSort, getDatatype)
{
  Sort dtypeSort = create_datatype_sort();
  ASSERT_NO_THROW(dtypeSort.getDatatype());
  // create bv sort, check should fail
  Sort bvSort = d_solver.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getDatatype(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, datatypeSorts)
{
  Sort intSort = d_solver.getIntegerSort();
  Sort dtypeSort = create_datatype_sort();
  Datatype dt = dtypeSort.getDatatype();
  ASSERT_FALSE(dtypeSort.isConstructor());
  ASSERT_THROW(dtypeSort.getConstructorCodomainSort(), CVC5ApiException);
  ASSERT_THROW(dtypeSort.getConstructorDomainSorts(), CVC5ApiException);
  ASSERT_THROW(dtypeSort.getConstructorArity(), CVC5ApiException);

  // get constructor
  DatatypeConstructor dcons = dt[0];
  Term consTerm = dcons.getConstructorTerm();
  Sort consSort = consTerm.getSort();
  ASSERT_TRUE(consSort.isConstructor());
  ASSERT_FALSE(consSort.isTester());
  ASSERT_FALSE(consSort.isSelector());
  ASSERT_EQ(consSort.getConstructorArity(), 2);
  std::vector<Sort> consDomSorts = consSort.getConstructorDomainSorts();
  ASSERT_EQ(consDomSorts[0], intSort);
  ASSERT_EQ(consDomSorts[1], dtypeSort);
  ASSERT_EQ(consSort.getConstructorCodomainSort(), dtypeSort);

  // get tester
  Term isConsTerm = dcons.getTesterTerm();
  ASSERT_TRUE(isConsTerm.getSort().isTester());
  ASSERT_EQ(isConsTerm.getSort().getTesterDomainSort(), dtypeSort);
  Sort booleanSort = d_solver.getBooleanSort();
  ASSERT_EQ(isConsTerm.getSort().getTesterCodomainSort(), booleanSort);
  ASSERT_THROW(booleanSort.getTesterDomainSort(), CVC5ApiException);
  ASSERT_THROW(booleanSort.getTesterCodomainSort(), CVC5ApiException);

  // get selector
  DatatypeSelector dselTail = dcons[1];
  Term tailTerm = dselTail.getSelectorTerm();
  ASSERT_TRUE(tailTerm.getSort().isSelector());
  ASSERT_EQ(tailTerm.getSort().getSelectorDomainSort(), dtypeSort);
  ASSERT_EQ(tailTerm.getSort().getSelectorCodomainSort(), dtypeSort);
  ASSERT_THROW(booleanSort.getSelectorDomainSort(), CVC5ApiException);
  ASSERT_THROW(booleanSort.getSelectorCodomainSort(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, instantiate)
{
  // instantiate parametric datatype, check should not fail
  Sort paramDtypeSort = create_param_datatype_sort();
  ASSERT_NO_THROW(
      paramDtypeSort.instantiate(std::vector<Sort>{d_solver.getIntegerSort()}));
  // instantiate non-parametric datatype sort, check should fail
  DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_solver.getIntegerSort());
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
  ASSERT_THROW(
      dtypeSort.instantiate(std::vector<Sort>{d_solver.getIntegerSort()}),
      CVC5ApiException);
}

TEST_F(TestApiBlackSort, getFunctionArity)
{
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  ASSERT_NO_THROW(funSort.getFunctionArity());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getFunctionArity(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getFunctionDomainSorts)
{
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  ASSERT_NO_THROW(funSort.getFunctionDomainSorts());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getFunctionDomainSorts(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getFunctionCodomainSort)
{
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  ASSERT_NO_THROW(funSort.getFunctionCodomainSort());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getFunctionCodomainSort(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getArrayIndexSort)
{
  Sort elementSort = d_solver.mkBitVectorSort(32);
  Sort indexSort = d_solver.mkBitVectorSort(32);
  Sort arraySort = d_solver.mkArraySort(indexSort, elementSort);
  ASSERT_NO_THROW(arraySort.getArrayIndexSort());
  ASSERT_THROW(indexSort.getArrayIndexSort(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getArrayElementSort)
{
  Sort elementSort = d_solver.mkBitVectorSort(32);
  Sort indexSort = d_solver.mkBitVectorSort(32);
  Sort arraySort = d_solver.mkArraySort(indexSort, elementSort);
  ASSERT_NO_THROW(arraySort.getArrayElementSort());
  ASSERT_THROW(indexSort.getArrayElementSort(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getSetElementSort)
{
  Sort setSort = d_solver.mkSetSort(d_solver.getIntegerSort());
  ASSERT_NO_THROW(setSort.getSetElementSort());
  Sort elementSort = setSort.getSetElementSort();
  ASSERT_EQ(elementSort, d_solver.getIntegerSort());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getSetElementSort(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getBagElementSort)
{
  Sort bagSort = d_solver.mkBagSort(d_solver.getIntegerSort());
  ASSERT_NO_THROW(bagSort.getBagElementSort());
  Sort elementSort = bagSort.getBagElementSort();
  ASSERT_EQ(elementSort, d_solver.getIntegerSort());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getBagElementSort(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getSequenceElementSort)
{
  Sort seqSort = d_solver.mkSequenceSort(d_solver.getIntegerSort());
  ASSERT_TRUE(seqSort.isSequence());
  ASSERT_NO_THROW(seqSort.getSequenceElementSort());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  ASSERT_FALSE(bvSort.isSequence());
  ASSERT_THROW(bvSort.getSequenceElementSort(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getUninterpretedSortName)
{
  Sort uSort = d_solver.mkUninterpretedSort("u");
  ASSERT_NO_THROW(uSort.getUninterpretedSortName());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getUninterpretedSortName(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, isUninterpretedSortParameterized)
{
  Sort uSort = d_solver.mkUninterpretedSort("u");
  ASSERT_FALSE(uSort.isUninterpretedSortParameterized());
  Sort sSort = d_solver.mkSortConstructorSort("s", 1);
  Sort siSort = sSort.instantiate({uSort});
  ASSERT_TRUE(siSort.isUninterpretedSortParameterized());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.isUninterpretedSortParameterized(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getUninterpretedSortParamSorts)
{
  Sort uSort = d_solver.mkUninterpretedSort("u");
  ASSERT_NO_THROW(uSort.getUninterpretedSortParamSorts());
  Sort sSort = d_solver.mkSortConstructorSort("s", 2);
  Sort siSort = sSort.instantiate({uSort, uSort});
  ASSERT_EQ(siSort.getUninterpretedSortParamSorts().size(), 2);
  Sort bvSort = d_solver.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getUninterpretedSortParamSorts(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getUninterpretedSortConstructorName)
{
  Sort sSort = d_solver.mkSortConstructorSort("s", 2);
  ASSERT_NO_THROW(sSort.getSortConstructorName());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getSortConstructorName(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getUninterpretedSortConstructorArity)
{
  Sort sSort = d_solver.mkSortConstructorSort("s", 2);
  ASSERT_NO_THROW(sSort.getSortConstructorArity());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getSortConstructorArity(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getBitVectorSize)
{
  Sort bvSort = d_solver.mkBitVectorSort(32);
  ASSERT_NO_THROW(bvSort.getBitVectorSize());
  Sort setSort = d_solver.mkSetSort(d_solver.getIntegerSort());
  ASSERT_THROW(setSort.getBitVectorSize(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getFloatingPointExponentSize)
{
  Sort fpSort = d_solver.mkFloatingPointSort(4, 8);
  ASSERT_NO_THROW(fpSort.getFloatingPointExponentSize());
  Sort setSort = d_solver.mkSetSort(d_solver.getIntegerSort());
  ASSERT_THROW(setSort.getFloatingPointExponentSize(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getFloatingPointSignificandSize)
{
  Sort fpSort = d_solver.mkFloatingPointSort(4, 8);
  ASSERT_NO_THROW(fpSort.getFloatingPointSignificandSize());
  Sort setSort = d_solver.mkSetSort(d_solver.getIntegerSort());
  ASSERT_THROW(setSort.getFloatingPointSignificandSize(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getDatatypeParamSorts)
{
  // create parametric datatype, check should not fail
  Sort sort = d_solver.mkParamSort("T");
  DatatypeDecl paramDtypeSpec = d_solver.mkDatatypeDecl("paramlist", sort);
  DatatypeConstructorDecl paramCons =
      d_solver.mkDatatypeConstructorDecl("cons");
  DatatypeConstructorDecl paramNil = d_solver.mkDatatypeConstructorDecl("nil");
  paramCons.addSelector("head", sort);
  paramDtypeSpec.addConstructor(paramCons);
  paramDtypeSpec.addConstructor(paramNil);
  Sort paramDtypeSort = d_solver.mkDatatypeSort(paramDtypeSpec);
  ASSERT_NO_THROW(paramDtypeSort.getDatatypeParamSorts());
  // create non-parametric datatype sort, check should fail
  DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_solver.getIntegerSort());
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
  ASSERT_THROW(dtypeSort.getDatatypeParamSorts(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getDatatypeArity)
{
  // create datatype sort, check should not fail
  DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_solver.getIntegerSort());
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
  ASSERT_NO_THROW(dtypeSort.getDatatypeArity());
  // create bv sort, check should fail
  Sort bvSort = d_solver.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getDatatypeArity(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getTupleLength)
{
  Sort tupleSort = d_solver.mkTupleSort(
      {d_solver.getIntegerSort(), d_solver.getIntegerSort()});
  ASSERT_NO_THROW(tupleSort.getTupleLength());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getTupleLength(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getTupleSorts)
{
  Sort tupleSort = d_solver.mkTupleSort(
      {d_solver.getIntegerSort(), d_solver.getIntegerSort()});
  ASSERT_NO_THROW(tupleSort.getTupleSorts());
  Sort bvSort = d_solver.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getTupleSorts(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, sortCompare)
{
  Sort boolSort = d_solver.getBooleanSort();
  Sort intSort = d_solver.getIntegerSort();
  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort bvSort2 = d_solver.mkBitVectorSort(32);
  ASSERT_TRUE(bvSort >= bvSort2);
  ASSERT_TRUE(bvSort <= bvSort2);
  ASSERT_TRUE((intSort > boolSort) != (intSort < boolSort));
  ASSERT_TRUE((intSort > bvSort || intSort == bvSort) == (intSort >= bvSort));
}

TEST_F(TestApiBlackSort, sortSubtyping)
{
  Sort intSort = d_solver.getIntegerSort();
  Sort realSort = d_solver.getRealSort();
  ASSERT_TRUE(intSort.isSubsortOf(realSort));
  ASSERT_FALSE(realSort.isSubsortOf(intSort));

  Sort arraySortII = d_solver.mkArraySort(intSort, intSort);
  Sort arraySortIR = d_solver.mkArraySort(intSort, realSort);

  Sort setSortI = d_solver.mkSetSort(intSort);
  Sort setSortR = d_solver.mkSetSort(realSort);
  // we don't support subtyping for sets
  ASSERT_FALSE(setSortI.isSubsortOf(setSortR));
  ASSERT_FALSE(setSortR.isSubsortOf(setSortI));
}

TEST_F(TestApiBlackSort, sortScopedToString)
{
  std::string name = "uninterp-sort";
  Sort bvsort8 = d_solver.mkBitVectorSort(8);
  Sort uninterp_sort = d_solver.mkUninterpretedSort(name);
  ASSERT_EQ(bvsort8.toString(), "(_ BitVec 8)");
  ASSERT_EQ(uninterp_sort.toString(), name);
  Solver solver2;
  ASSERT_EQ(bvsort8.toString(), "(_ BitVec 8)");
  ASSERT_EQ(uninterp_sort.toString(), name);
}

TEST_F(TestApiBlackSort, toString)
{
  ASSERT_NO_THROW(Sort().toString());
}

}  // namespace test
}  // namespace cvc5
