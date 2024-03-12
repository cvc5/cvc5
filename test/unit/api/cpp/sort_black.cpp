/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the guards of the C++ API functions.
 */

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackSort : public TestApi
{
 protected:
  Sort create_datatype_sort()
  {
    DatatypeDecl dtypeSpec = d_tm.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", d_tm.getIntegerSort());
    cons.addSelectorSelf("tail");
    dtypeSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
    dtypeSpec.addConstructor(nil);
    return d_tm.mkDatatypeSort(dtypeSpec);
  }

  Sort create_param_datatype_sort()
  {
    Sort sort = d_tm.mkParamSort("T");
    DatatypeDecl paramDtypeSpec = d_tm.mkDatatypeDecl("paramlist", {sort});
    DatatypeConstructorDecl paramCons = d_tm.mkDatatypeConstructorDecl("cons");
    DatatypeConstructorDecl paramNil = d_tm.mkDatatypeConstructorDecl("nil");
    paramCons.addSelector("head", sort);
    paramDtypeSpec.addConstructor(paramCons);
    paramDtypeSpec.addConstructor(paramNil);
    return d_tm.mkDatatypeSort(paramDtypeSpec);
  }
};

TEST_F(TestApiBlackSort, hash)
{
  std::hash<cvc5::Sort> h;
  ASSERT_NO_THROW(h(d_tm.getIntegerSort()));
}

TEST_F(TestApiBlackSort, operators_comparison)
{
  ASSERT_FALSE(d_tm.getIntegerSort() == Sort());
  ASSERT_TRUE(d_tm.getIntegerSort() != Sort());
  ASSERT_FALSE(d_tm.getIntegerSort() < Sort());
  ASSERT_FALSE(d_tm.getIntegerSort() <= Sort());
  ASSERT_TRUE(d_tm.getIntegerSort() > Sort());
  ASSERT_TRUE(d_tm.getIntegerSort() >= Sort());
}

TEST_F(TestApiBlackSort, getKind)
{
  Sort b = d_tm.getBooleanSort();
  ASSERT_EQ(b.getKind(), SortKind::BOOLEAN_SORT);
  Sort dt_sort = create_datatype_sort();
  ASSERT_EQ(dt_sort.getKind(), SortKind::DATATYPE_SORT);
  Sort arr_sort = d_tm.mkArraySort(d_tm.getRealSort(), d_tm.getIntegerSort());
  ASSERT_EQ(arr_sort.getKind(), SortKind::ARRAY_SORT);
  Sort fp_sort = d_tm.mkFloatingPointSort(8, 24);
  ASSERT_EQ(fp_sort.getKind(), SortKind::FLOATINGPOINT_SORT);
  Sort bv_sort = d_tm.mkBitVectorSort(8);
  ASSERT_EQ(bv_sort.getKind(), SortKind::BITVECTOR_SORT);
  Sort abs_sort = d_tm.mkAbstractSort(SortKind::BITVECTOR_SORT);
  ASSERT_EQ(abs_sort.getKind(), SortKind::ABSTRACT_SORT);
}

TEST_F(TestApiBlackSort, hasGetSymbol)
{
  Sort n;
  Sort b = d_tm.getBooleanSort();
  Sort s0 = d_tm.mkParamSort("s0");
  Sort s1 = d_tm.mkParamSort("|s1\\|");

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
  x = d_tm.getBooleanSort();
  ASSERT_FALSE(x.isNull());
}

TEST_F(TestApiBlackSort, isBoolean)
{
  ASSERT_TRUE(d_tm.getBooleanSort().isBoolean());
  ASSERT_NO_THROW(Sort().isBoolean());
}

TEST_F(TestApiBlackSort, isInteger)
{
  ASSERT_TRUE(d_tm.getIntegerSort().isInteger());
  ASSERT_TRUE(!d_tm.getRealSort().isInteger());
  ASSERT_NO_THROW(Sort().isInteger());
}

TEST_F(TestApiBlackSort, isReal)
{
  ASSERT_TRUE(d_tm.getRealSort().isReal());
  ASSERT_TRUE(!d_tm.getIntegerSort().isReal());
  ASSERT_NO_THROW(Sort().isReal());
}

TEST_F(TestApiBlackSort, isString)
{
  ASSERT_TRUE(d_tm.getStringSort().isString());
  ASSERT_NO_THROW(Sort().isString());
}

TEST_F(TestApiBlackSort, isRegExp)
{
  ASSERT_TRUE(d_tm.getRegExpSort().isRegExp());
  ASSERT_NO_THROW(Sort().isRegExp());
}

TEST_F(TestApiBlackSort, isRoundingMode)
{
  ASSERT_TRUE(d_tm.getRoundingModeSort().isRoundingMode());
  ASSERT_NO_THROW(Sort().isRoundingMode());
}

TEST_F(TestApiBlackSort, isBitVector)
{
  ASSERT_TRUE(d_tm.mkBitVectorSort(8).isBitVector());
  ASSERT_NO_THROW(Sort().isBitVector());
}

TEST_F(TestApiBlackSort, isFiniteField)
{
  ASSERT_TRUE(d_tm.mkFiniteFieldSort("7").isFiniteField());
  ASSERT_NO_THROW(Sort().isFiniteField());
}

TEST_F(TestApiBlackSort, isFloatingPoint)
{
  ASSERT_TRUE(d_tm.mkFloatingPointSort(8, 24).isFloatingPoint());
  ASSERT_NO_THROW(Sort().isFloatingPoint());
}

TEST_F(TestApiBlackSort, isDatatype)
{
  Sort dt_sort = create_datatype_sort();
  ASSERT_TRUE(dt_sort.isDatatype());
  ASSERT_NO_THROW(Sort().isDatatype());
}

TEST_F(TestApiBlackSort, isConstructor)
{
  Sort dt_sort = create_datatype_sort();
  Datatype dt = dt_sort.getDatatype();
  Sort cons_sort = dt[0].getTerm().getSort();
  ASSERT_TRUE(cons_sort.isDatatypeConstructor());
  ASSERT_NO_THROW(Sort().isDatatypeConstructor());
}

TEST_F(TestApiBlackSort, isSelector)
{
  Sort dt_sort = create_datatype_sort();
  Datatype dt = dt_sort.getDatatype();
  Sort cons_sort = dt[0][1].getTerm().getSort();
  ASSERT_TRUE(cons_sort.isDatatypeSelector());
  ASSERT_NO_THROW(Sort().isDatatypeSelector());
}

TEST_F(TestApiBlackSort, isTester)
{
  Sort dt_sort = create_datatype_sort();
  Datatype dt = dt_sort.getDatatype();
  Sort testerSort = dt[0].getTesterTerm().getSort();
  ASSERT_TRUE(testerSort.isDatatypeTester());
  ASSERT_NO_THROW(Sort().isDatatypeTester());
}

TEST_F(TestApiBlackSort, isUpdater)
{
  Sort dt_sort = create_datatype_sort();
  Datatype dt = dt_sort.getDatatype();
  Sort updaterSort = dt[0][0].getUpdaterTerm().getSort();
  ASSERT_TRUE(updaterSort.isDatatypeUpdater());
  ASSERT_NO_THROW(Sort().isDatatypeUpdater());
}

TEST_F(TestApiBlackSort, isFunction)
{
  Sort fun_sort =
      d_tm.mkFunctionSort({d_tm.getRealSort()}, d_tm.getIntegerSort());
  ASSERT_TRUE(fun_sort.isFunction());
  ASSERT_NO_THROW(Sort().isFunction());
}

TEST_F(TestApiBlackSort, isPredicate)
{
  Sort pred_sort = d_tm.mkPredicateSort({d_tm.getRealSort()});
  ASSERT_TRUE(pred_sort.isPredicate());
  ASSERT_NO_THROW(Sort().isPredicate());
}

TEST_F(TestApiBlackSort, isTuple)
{
  Sort tup_sort = d_tm.mkTupleSort({d_tm.getRealSort()});
  ASSERT_TRUE(tup_sort.isTuple());
  ASSERT_NO_THROW(Sort().isTuple());
}

TEST_F(TestApiBlackSort, isNullable)
{
  Sort tup_sort = d_tm.mkNullableSort(d_tm.getRealSort());
  ASSERT_TRUE(tup_sort.isNullable());
  ASSERT_NO_THROW(Sort().isNullable());
}

TEST_F(TestApiBlackSort, isRecord)
{
  Sort rec_sort =
      d_tm.mkRecordSort({std::make_pair("asdf", d_tm.getRealSort())});
  ASSERT_TRUE(rec_sort.isRecord());
  ASSERT_NO_THROW(Sort().isRecord());
}

TEST_F(TestApiBlackSort, isArray)
{
  Sort arr_sort = d_tm.mkArraySort(d_tm.getRealSort(), d_tm.getIntegerSort());
  ASSERT_TRUE(arr_sort.isArray());
  ASSERT_NO_THROW(Sort().isArray());
}

TEST_F(TestApiBlackSort, isSet)
{
  Sort set_sort = d_tm.mkSetSort(d_tm.getRealSort());
  ASSERT_TRUE(set_sort.isSet());
  ASSERT_NO_THROW(Sort().isSet());
}

TEST_F(TestApiBlackSort, isBag)
{
  Sort bag_sort = d_tm.mkBagSort(d_tm.getRealSort());
  ASSERT_TRUE(bag_sort.isBag());
  ASSERT_NO_THROW(Sort().isBag());
}

TEST_F(TestApiBlackSort, isSequence)
{
  Sort seq_sort = d_tm.mkSequenceSort(d_tm.getRealSort());
  ASSERT_TRUE(seq_sort.isSequence());
  ASSERT_NO_THROW(Sort().isSequence());
}

TEST_F(TestApiBlackSort, isAbstract)
{
  ASSERT_TRUE(d_tm.mkAbstractSort(SortKind::BITVECTOR_SORT).isAbstract());
  // ?Array is syntax sugar for (Array ? ?), thus the constructed sort
  // is an Array sort, not an abstract sort.
  ASSERT_FALSE(d_tm.mkAbstractSort(SortKind::ARRAY_SORT).isAbstract());
  ASSERT_TRUE(d_tm.mkAbstractSort(SortKind::ABSTRACT_SORT).isAbstract());
  ASSERT_NO_THROW(Sort().isAbstract());
}

TEST_F(TestApiBlackSort, isUninterpreted)
{
  Sort un_sort = d_tm.mkUninterpretedSort("asdf");
  ASSERT_TRUE(un_sort.isUninterpretedSort());
  ASSERT_NO_THROW(Sort().isUninterpretedSort());
  Sort un_sort2 = d_tm.mkUninterpretedSort();
  ASSERT_TRUE(un_sort2.isUninterpretedSort());
}

TEST_F(TestApiBlackSort, isUninterpretedSortConstructor)
{
  Sort sc_sort = d_tm.mkUninterpretedSortConstructorSort(1, "asdf");
  ASSERT_TRUE(sc_sort.isUninterpretedSortConstructor());
  ASSERT_NO_THROW(Sort().isUninterpretedSortConstructor());
  Sort sc_sort2 = d_tm.mkUninterpretedSortConstructorSort(2);
  ASSERT_TRUE(sc_sort2.isUninterpretedSortConstructor());
}

TEST_F(TestApiBlackSort, getDatatype)
{
  Sort dtypeSort = create_datatype_sort();
  ASSERT_NO_THROW(dtypeSort.getDatatype());
  // create bv sort, check should fail
  Sort bvSort = d_tm.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getDatatype(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, datatypeSorts)
{
  Sort intSort = d_tm.getIntegerSort();
  Sort dtypeSort = create_datatype_sort();
  Datatype dt = dtypeSort.getDatatype();
  ASSERT_FALSE(dtypeSort.isDatatypeConstructor());
  ASSERT_THROW(dtypeSort.getDatatypeConstructorCodomainSort(),
               CVC5ApiException);
  ASSERT_THROW(dtypeSort.getDatatypeConstructorDomainSorts(), CVC5ApiException);
  ASSERT_THROW(dtypeSort.getDatatypeConstructorArity(), CVC5ApiException);

  // get constructor
  DatatypeConstructor dcons = dt[0];
  Term consTerm = dcons.getTerm();
  Sort consSort = consTerm.getSort();
  ASSERT_TRUE(consSort.isDatatypeConstructor());
  ASSERT_FALSE(consSort.isDatatypeTester());
  ASSERT_FALSE(consSort.isDatatypeSelector());
  ASSERT_EQ(consSort.getDatatypeConstructorArity(), 2);
  std::vector<Sort> consDomSorts = consSort.getDatatypeConstructorDomainSorts();
  ASSERT_EQ(consDomSorts[0], intSort);
  ASSERT_EQ(consDomSorts[1], dtypeSort);
  ASSERT_EQ(consSort.getDatatypeConstructorCodomainSort(), dtypeSort);

  // get tester
  Term isConsTerm = dcons.getTesterTerm();
  ASSERT_TRUE(isConsTerm.getSort().isDatatypeTester());
  ASSERT_EQ(isConsTerm.getSort().getDatatypeTesterDomainSort(), dtypeSort);
  Sort booleanSort = d_tm.getBooleanSort();
  ASSERT_EQ(isConsTerm.getSort().getDatatypeTesterCodomainSort(), booleanSort);
  ASSERT_THROW(booleanSort.getDatatypeTesterDomainSort(), CVC5ApiException);
  ASSERT_THROW(booleanSort.getDatatypeTesterCodomainSort(), CVC5ApiException);

  // get selector
  DatatypeSelector dselTail = dcons[1];
  Term tailTerm = dselTail.getTerm();
  ASSERT_TRUE(tailTerm.getSort().isDatatypeSelector());
  ASSERT_EQ(tailTerm.getSort().getDatatypeSelectorDomainSort(), dtypeSort);
  ASSERT_EQ(tailTerm.getSort().getDatatypeSelectorCodomainSort(), dtypeSort);
  ASSERT_THROW(booleanSort.getDatatypeSelectorDomainSort(), CVC5ApiException);
  ASSERT_THROW(booleanSort.getDatatypeSelectorCodomainSort(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, instantiate)
{
  // instantiate parametric datatype, check should not fail
  Sort paramDtypeSort = create_param_datatype_sort();
  ASSERT_NO_THROW(paramDtypeSort.instantiate({d_tm.getIntegerSort()}));
  // instantiate non-parametric datatype sort, check should fail
  DatatypeDecl dtypeSpec = d_tm.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_tm.getIntegerSort());
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  Sort dtypeSort = d_tm.mkDatatypeSort(dtypeSpec);
  ASSERT_THROW(dtypeSort.instantiate({d_tm.getIntegerSort()}),
               CVC5ApiException);
  // instantiate uninterpreted sort constructor
  Sort sortConsSort = d_tm.mkUninterpretedSortConstructorSort(1, "s");
  ASSERT_NO_THROW(sortConsSort.instantiate({d_tm.getIntegerSort()}));
}

TEST_F(TestApiBlackSort, isInstantiated)
{
  Sort paramDtypeSort = create_param_datatype_sort();
  ASSERT_FALSE(paramDtypeSort.isInstantiated());
  Sort instParamDtypeSort = paramDtypeSort.instantiate({d_tm.getIntegerSort()});
  ASSERT_TRUE(instParamDtypeSort.isInstantiated());

  Sort sortConsSort = d_tm.mkUninterpretedSortConstructorSort(1, "s");
  ASSERT_FALSE(sortConsSort.isInstantiated());
  Sort instSortConsSort = sortConsSort.instantiate({d_tm.getIntegerSort()});
  ASSERT_TRUE(instSortConsSort.isInstantiated());

  ASSERT_FALSE(d_tm.getIntegerSort().isInstantiated());
  ASSERT_FALSE(d_tm.mkBitVectorSort(32).isInstantiated());
}

TEST_F(TestApiBlackSort, getInstantiatedParameters)
{
  Sort intSort = d_tm.getIntegerSort();
  Sort realSort = d_tm.getRealSort();
  Sort boolSort = d_tm.getBooleanSort();
  Sort bvSort = d_tm.mkBitVectorSort(8);
  std::vector<Sort> instSorts;

  // parametric datatype instantiation
  Sort p1 = d_tm.mkParamSort("p1");
  Sort p2 = d_tm.mkParamSort("p2");
  DatatypeDecl pspec = d_tm.mkDatatypeDecl("pdtype", {p1, p2});
  DatatypeConstructorDecl pcons1 = d_tm.mkDatatypeConstructorDecl("cons1");
  DatatypeConstructorDecl pcons2 = d_tm.mkDatatypeConstructorDecl("cons2");
  DatatypeConstructorDecl pnil = d_tm.mkDatatypeConstructorDecl("nil");
  pcons1.addSelector("sel", p1);
  pcons2.addSelector("sel", p2);
  pspec.addConstructor(pcons1);
  pspec.addConstructor(pcons2);
  pspec.addConstructor(pnil);
  Sort paramDtypeSort = d_tm.mkDatatypeSort(pspec);

  ASSERT_THROW(paramDtypeSort.getInstantiatedParameters(), CVC5ApiException);

  Sort instParamDtypeSort = paramDtypeSort.instantiate({realSort, boolSort});

  instSorts = instParamDtypeSort.getInstantiatedParameters();
  ASSERT_EQ(instSorts[0], realSort);
  ASSERT_EQ(instSorts[1], boolSort);

  // uninterpreted sort constructor sort instantiation
  Sort sortConsSort = d_tm.mkUninterpretedSortConstructorSort(4, "s");
  ASSERT_THROW(sortConsSort.getInstantiatedParameters(), CVC5ApiException);

  Sort instSortConsSort =
      sortConsSort.instantiate({boolSort, intSort, bvSort, realSort});

  instSorts = instSortConsSort.getInstantiatedParameters();
  ASSERT_EQ(instSorts[0], boolSort);
  ASSERT_EQ(instSorts[1], intSort);
  ASSERT_EQ(instSorts[2], bvSort);
  ASSERT_EQ(instSorts[3], realSort);

  ASSERT_THROW(intSort.getInstantiatedParameters(), CVC5ApiException);
  ASSERT_THROW(bvSort.getInstantiatedParameters(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getUninterpretedSortConstructor)
{
  Sort intSort = d_tm.getIntegerSort();
  Sort realSort = d_tm.getRealSort();
  Sort boolSort = d_tm.getBooleanSort();
  Sort bvSort = d_tm.mkBitVectorSort(8);
  Sort sortConsSort = d_tm.mkUninterpretedSortConstructorSort(4, "s");
  ASSERT_THROW(sortConsSort.getUninterpretedSortConstructor(),
               CVC5ApiException);
  Sort instSortConsSort =
      sortConsSort.instantiate({boolSort, intSort, bvSort, realSort});
  ASSERT_EQ(sortConsSort, instSortConsSort.getUninterpretedSortConstructor());
}

TEST_F(TestApiBlackSort, getFunctionArity)
{
  Sort funSort = d_tm.mkFunctionSort({d_tm.mkUninterpretedSort("u")},
                                     d_tm.getIntegerSort());
  ASSERT_NO_THROW(funSort.getFunctionArity());
  Sort bvSort = d_tm.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getFunctionArity(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getFunctionDomainSorts)
{
  Sort funSort = d_tm.mkFunctionSort({d_tm.mkUninterpretedSort("u")},
                                     d_tm.getIntegerSort());
  ASSERT_NO_THROW(funSort.getFunctionDomainSorts());
  Sort bvSort = d_tm.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getFunctionDomainSorts(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getFunctionCodomainSort)
{
  Sort funSort = d_tm.mkFunctionSort({d_tm.mkUninterpretedSort("u")},
                                     d_tm.getIntegerSort());
  ASSERT_NO_THROW(funSort.getFunctionCodomainSort());
  Sort bvSort = d_tm.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getFunctionCodomainSort(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getArrayIndexSort)
{
  Sort elementSort = d_tm.mkBitVectorSort(32);
  Sort indexSort = d_tm.mkBitVectorSort(32);
  Sort arraySort = d_tm.mkArraySort(indexSort, elementSort);
  ASSERT_NO_THROW(arraySort.getArrayIndexSort());
  ASSERT_THROW(indexSort.getArrayIndexSort(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getArrayElementSort)
{
  Sort elementSort = d_tm.mkBitVectorSort(32);
  Sort indexSort = d_tm.mkBitVectorSort(32);
  Sort arraySort = d_tm.mkArraySort(indexSort, elementSort);
  ASSERT_NO_THROW(arraySort.getArrayElementSort());
  ASSERT_THROW(indexSort.getArrayElementSort(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getSetElementSort)
{
  Sort setSort = d_tm.mkSetSort(d_tm.getIntegerSort());
  ASSERT_NO_THROW(setSort.getSetElementSort());
  Sort elementSort = setSort.getSetElementSort();
  ASSERT_EQ(elementSort, d_tm.getIntegerSort());
  Sort bvSort = d_tm.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getSetElementSort(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getBagElementSort)
{
  Sort bagSort = d_tm.mkBagSort(d_tm.getIntegerSort());
  ASSERT_NO_THROW(bagSort.getBagElementSort());
  Sort elementSort = bagSort.getBagElementSort();
  ASSERT_EQ(elementSort, d_tm.getIntegerSort());
  Sort bvSort = d_tm.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getBagElementSort(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getSequenceElementSort)
{
  Sort seqSort = d_tm.mkSequenceSort(d_tm.getIntegerSort());
  ASSERT_TRUE(seqSort.isSequence());
  ASSERT_NO_THROW(seqSort.getSequenceElementSort());
  Sort bvSort = d_tm.mkBitVectorSort(32);
  ASSERT_FALSE(bvSort.isSequence());
  ASSERT_THROW(bvSort.getSequenceElementSort(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getAbstractedKind)
{
  ASSERT_EQ(d_tm.mkAbstractSort(SortKind::BITVECTOR_SORT).getAbstractedKind(),
            SortKind::BITVECTOR_SORT);
  // ?Array is syntax sugar for (Array ? ?), thus the constructed sort
  // is an Array sort, not an abstract sort and its abstract kind cannot be
  // extracted.
  ASSERT_THROW(d_tm.mkAbstractSort(SortKind::ARRAY_SORT).getAbstractedKind(),
               CVC5ApiException);
  ASSERT_EQ(d_tm.mkAbstractSort(SortKind::ABSTRACT_SORT).getAbstractedKind(),
            SortKind::ABSTRACT_SORT);
}

TEST_F(TestApiBlackSort, getSymbol)
{
  Sort uSort = d_tm.mkUninterpretedSort("u");
  ASSERT_NO_THROW(uSort.getSymbol());
  Sort bvSort = d_tm.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getSymbol(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getUninterpretedSortConstructorName)
{
  Sort sSort = d_tm.mkUninterpretedSortConstructorSort(2, "s");
  ASSERT_NO_THROW(sSort.getSymbol());
  Sort bvSort = d_tm.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getSymbol(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getUninterpretedSortConstructorArity)
{
  Sort sSort = d_tm.mkUninterpretedSortConstructorSort(2, "s");
  ASSERT_NO_THROW(sSort.getUninterpretedSortConstructorArity());
  Sort bvSort = d_tm.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getUninterpretedSortConstructorArity(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getBitVectorSize)
{
  Sort bvSort = d_tm.mkBitVectorSort(32);
  ASSERT_NO_THROW(bvSort.getBitVectorSize());
  Sort setSort = d_tm.mkSetSort(d_tm.getIntegerSort());
  ASSERT_THROW(setSort.getBitVectorSize(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getFiniteFieldSize)
{
  Sort ffSort = d_tm.mkFiniteFieldSort("31");
  ASSERT_NO_THROW(ffSort.getFiniteFieldSize());
  ASSERT_EQ(ffSort.getFiniteFieldSize(), "31");
  ASSERT_THROW(Sort().getFiniteFieldSize(), CVC5ApiException);
  Sort setSort = d_tm.mkSetSort(d_tm.getIntegerSort());
  ASSERT_THROW(setSort.getFiniteFieldSize(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getFloatingPointExponentSize)
{
  Sort fpSort = d_tm.mkFloatingPointSort(4, 8);
  ASSERT_NO_THROW(fpSort.getFloatingPointExponentSize());
  Sort setSort = d_tm.mkSetSort(d_tm.getIntegerSort());
  ASSERT_THROW(setSort.getFloatingPointExponentSize(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getFloatingPointSignificandSize)
{
  Sort fpSort = d_tm.mkFloatingPointSort(4, 8);
  ASSERT_NO_THROW(fpSort.getFloatingPointSignificandSize());
  Sort setSort = d_tm.mkSetSort(d_tm.getIntegerSort());
  ASSERT_THROW(setSort.getFloatingPointSignificandSize(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getDatatypeArity)
{
  // create datatype sort, check should not fail
  DatatypeDecl dtypeSpec = d_tm.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_tm.getIntegerSort());
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  Sort dtypeSort = d_tm.mkDatatypeSort(dtypeSpec);
  ASSERT_NO_THROW(dtypeSort.getDatatypeArity());
  // create bv sort, check should fail
  Sort bvSort = d_tm.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getDatatypeArity(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getTupleLength)
{
  Sort tupleSort =
      d_tm.mkTupleSort({d_tm.getIntegerSort(), d_tm.getIntegerSort()});
  ASSERT_NO_THROW(tupleSort.getTupleLength());
  Sort bvSort = d_tm.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getTupleLength(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getTupleSorts)
{
  Sort tupleSort =
      d_tm.mkTupleSort({d_tm.getIntegerSort(), d_tm.getIntegerSort()});
  ASSERT_NO_THROW(tupleSort.getTupleSorts());
  Sort bvSort = d_tm.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getTupleSorts(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, getNullableElementSort)
{
  Sort nullableSort = d_tm.mkNullableSort(d_tm.getIntegerSort());
  ASSERT_NO_THROW(nullableSort.getNullableElementSort());
  Sort elementSort = nullableSort.getNullableElementSort();
  ASSERT_EQ(elementSort, d_tm.getIntegerSort());
  Sort bvSort = d_tm.mkBitVectorSort(32);
  ASSERT_THROW(bvSort.getNullableElementSort(), CVC5ApiException);
}

TEST_F(TestApiBlackSort, sortCompare)
{
  Sort boolSort = d_tm.getBooleanSort();
  Sort intSort = d_tm.getIntegerSort();
  Sort bvSort = d_tm.mkBitVectorSort(32);
  Sort bvSort2 = d_tm.mkBitVectorSort(32);
  ASSERT_TRUE(bvSort >= bvSort2);
  ASSERT_TRUE(bvSort <= bvSort2);
  ASSERT_TRUE((intSort > boolSort) != (intSort < boolSort));
  ASSERT_TRUE((intSort > bvSort || intSort == bvSort) == (intSort >= bvSort));
}

TEST_F(TestApiBlackSort, sortScopedToString)
{
  std::string name = "uninterp-sort";
  Sort bvsort8 = d_tm.mkBitVectorSort(8);
  Sort uninterp_sort = d_tm.mkUninterpretedSort(name);
  ASSERT_EQ(bvsort8.toString(), "(_ BitVec 8)");
  ASSERT_EQ(uninterp_sort.toString(), name);
  ASSERT_EQ(bvsort8.toString(), "(_ BitVec 8)");
  ASSERT_EQ(uninterp_sort.toString(), name);
}

TEST_F(TestApiBlackSort, toString)
{
  ASSERT_NO_THROW(Sort().toString());
}

TEST_F(TestApiBlackSort, substitute)
{
  Sort sortVar0 = d_tm.mkParamSort("T0");
  Sort sortVar1 = d_tm.mkParamSort("T1");
  Sort intSort = d_tm.getIntegerSort();
  Sort realSort = d_tm.getRealSort();
  Sort arraySort0 = d_tm.mkArraySort(sortVar0, sortVar0);
  Sort arraySort1 = d_tm.mkArraySort(sortVar0, sortVar1);
  // Now create instantiations of the defined sorts
  ASSERT_NO_THROW(arraySort0.substitute(sortVar0, intSort));
  ASSERT_NO_THROW(
      arraySort1.substitute({sortVar0, sortVar1}, {intSort, realSort}));
}
}  // namespace test
}  // namespace cvc5::internal
