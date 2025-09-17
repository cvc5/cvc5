/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer, Amalee Wilson
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the TermManager class of the  C++ API.
 */

#include <gtest/gtest.h>

#include <cmath>

#include "test_api.h"

namespace cvc5::internal::test {

class TestApiBlackTermManager : public TestApi
{
};

TEST_F(TestApiBlackTermManager, getBooleanSort)
{
  ASSERT_NO_THROW(d_tm.getBooleanSort());
}

TEST_F(TestApiBlackTermManager, getIntegerSort)
{
  ASSERT_NO_THROW(d_tm.getIntegerSort());
}

TEST_F(TestApiBlackTermManager, getRealSort)
{
  ASSERT_NO_THROW(d_tm.getRealSort());
}

TEST_F(TestApiBlackTermManager, getRegExpSort)
{
  ASSERT_NO_THROW(d_tm.getRegExpSort());
}

TEST_F(TestApiBlackTermManager, getStringSort)
{
  ASSERT_NO_THROW(d_tm.getStringSort());
}

TEST_F(TestApiBlackTermManager, getRoundingModeSort)
{
  ASSERT_NO_THROW(d_tm.getRoundingModeSort());
}

TEST_F(TestApiBlackTermManager, mkArraySort)
{
  Sort boolSort = d_tm.getBooleanSort();
  Sort intSort = d_tm.getIntegerSort();
  Sort realSort = d_tm.getRealSort();
  Sort bvSort = d_tm.mkBitVectorSort(32);
  ASSERT_NO_THROW(d_tm.mkArraySort(boolSort, boolSort));
  ASSERT_NO_THROW(d_tm.mkArraySort(intSort, intSort));
  ASSERT_NO_THROW(d_tm.mkArraySort(realSort, realSort));
  ASSERT_NO_THROW(d_tm.mkArraySort(bvSort, bvSort));
  ASSERT_NO_THROW(d_tm.mkArraySort(boolSort, intSort));
  ASSERT_NO_THROW(d_tm.mkArraySort(realSort, bvSort));

  Sort fpSort = d_tm.mkFloatingPointSort(3, 5);
  ASSERT_NO_THROW(d_tm.mkArraySort(fpSort, fpSort));
  ASSERT_NO_THROW(d_tm.mkArraySort(bvSort, fpSort));
  ASSERT_NO_THROW(d_tm.mkArraySort(boolSort, boolSort));

  TermManager tm;
  ASSERT_THROW(d_tm.mkArraySort(tm.getBooleanSort(), tm.getIntegerSort()),
               CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkBitVectorSort)
{
  ASSERT_NO_THROW(d_tm.mkBitVectorSort(32));
  ASSERT_THROW(d_tm.mkBitVectorSort(0), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkFiniteFieldSort)
{
  ASSERT_NO_THROW(d_tm.mkFiniteFieldSort("31"));
  ASSERT_THROW(d_tm.mkFiniteFieldSort("6"), CVC5ApiException);

  ASSERT_THROW(d_tm.mkFiniteFieldSort("b"), CVC5ApiException);

  ASSERT_NO_THROW(d_tm.mkFiniteFieldSort("1100101", 2));
  ASSERT_NO_THROW(d_tm.mkFiniteFieldSort("10202", 3));
  ASSERT_NO_THROW(d_tm.mkFiniteFieldSort("401", 5));
  ASSERT_NO_THROW(d_tm.mkFiniteFieldSort("791a", 11));
  ASSERT_NO_THROW(d_tm.mkFiniteFieldSort("970f", 16));
  ASSERT_NO_THROW(d_tm.mkFiniteFieldSort("8CC5", 16));

  ASSERT_THROW(d_tm.mkFiniteFieldSort("1100100", 2), CVC5ApiException);
  ASSERT_THROW(d_tm.mkFiniteFieldSort("10201", 3), CVC5ApiException);
  ASSERT_THROW(d_tm.mkFiniteFieldSort("400", 5), CVC5ApiException);
  ASSERT_THROW(d_tm.mkFiniteFieldSort("7919", 11), CVC5ApiException);
  ASSERT_THROW(d_tm.mkFiniteFieldSort("970e", 16), CVC5ApiException);
  ASSERT_THROW(d_tm.mkFiniteFieldSort("8CC4", 16), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkFloatingPointSort)
{
  ASSERT_NO_THROW(d_tm.mkFloatingPointSort(4, 8));
  ASSERT_THROW(d_tm.mkFloatingPointSort(0, 8), CVC5ApiException);
  ASSERT_THROW(d_tm.mkFloatingPointSort(4, 0), CVC5ApiException);
  ASSERT_THROW(d_tm.mkFloatingPointSort(1, 8), CVC5ApiException);
  ASSERT_THROW(d_tm.mkFloatingPointSort(4, 1), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkDatatypeSort)
{
  {
    DatatypeDecl dtypeSpec = d_tm.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", d_tm.getIntegerSort());
    dtypeSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
    dtypeSpec.addConstructor(nil);
    ASSERT_NO_THROW(d_tm.mkDatatypeSort(dtypeSpec));

    ASSERT_THROW(d_tm.mkDatatypeSort(dtypeSpec), CVC5ApiException);
    ASSERT_THROW(d_tm.mkDatatypeSort(dtypeSpec), CVC5ApiException);
  }

  DatatypeDecl throwsDtypeSpec = d_tm.mkDatatypeDecl("list");
  ASSERT_THROW(d_tm.mkDatatypeSort(throwsDtypeSpec), CVC5ApiException);

  {
    TermManager tm;
    DatatypeDecl dtypeSpec = tm.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = tm.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", tm.getIntegerSort());
    dtypeSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = tm.mkDatatypeConstructorDecl("nil");
    dtypeSpec.addConstructor(nil);
    ASSERT_THROW(d_tm.mkDatatypeSort(dtypeSpec), CVC5ApiException);
  }
}

TEST_F(TestApiBlackTermManager, mkDatatypeSorts)
{
  {
    DatatypeDecl dtypeSpec1 = d_tm.mkDatatypeDecl("list1");
    DatatypeConstructorDecl cons1 = d_tm.mkDatatypeConstructorDecl("cons1");
    cons1.addSelector("head1", d_tm.getIntegerSort());
    dtypeSpec1.addConstructor(cons1);
    DatatypeConstructorDecl nil1 = d_tm.mkDatatypeConstructorDecl("nil1");
    dtypeSpec1.addConstructor(nil1);
    DatatypeDecl dtypeSpec2 = d_tm.mkDatatypeDecl("list2");
    DatatypeConstructorDecl cons2 = d_tm.mkDatatypeConstructorDecl("cons2");
    cons2.addSelector("head2", d_tm.getIntegerSort());
    dtypeSpec2.addConstructor(cons2);
    DatatypeConstructorDecl nil2 = d_tm.mkDatatypeConstructorDecl("nil2");
    dtypeSpec2.addConstructor(nil2);
    std::vector<DatatypeDecl> decls = {dtypeSpec1, dtypeSpec2};
    ASSERT_NO_THROW(d_tm.mkDatatypeSorts(decls));

    ASSERT_THROW(d_tm.mkDatatypeSorts(decls), CVC5ApiException);
    ASSERT_THROW(d_tm.mkDatatypeSorts(decls), CVC5ApiException);
  }

  DatatypeDecl throwsDtypeSpec = d_tm.mkDatatypeDecl("list");
  std::vector<DatatypeDecl> throwsDecls = {throwsDtypeSpec};
  ASSERT_THROW(d_tm.mkDatatypeSorts(throwsDecls), CVC5ApiException);

  /* with unresolved sorts */
  Sort unresList = d_tm.mkUnresolvedDatatypeSort("ulist");
  DatatypeDecl ulist = d_tm.mkDatatypeDecl("ulist");
  DatatypeConstructorDecl ucons = d_tm.mkDatatypeConstructorDecl("ucons");
  ucons.addSelector("car", unresList);
  ucons.addSelector("cdr", unresList);
  ulist.addConstructor(ucons);
  DatatypeConstructorDecl unil = d_tm.mkDatatypeConstructorDecl("unil");
  ulist.addConstructor(unil);
  std::vector<DatatypeDecl> udecls = {ulist};
  ASSERT_NO_THROW(d_tm.mkDatatypeSorts(udecls));

  ASSERT_THROW(d_tm.mkDatatypeSorts(udecls), CVC5ApiException);
  ASSERT_THROW(d_tm.mkDatatypeSorts(udecls), CVC5ApiException);

  /* mutually recursive with unresolved parameterized sorts */
  Sort p0 = d_tm.mkParamSort("p0");
  Sort p1 = d_tm.mkParamSort("p1");
  Sort u0 = d_tm.mkUnresolvedDatatypeSort("dt0", 1);
  Sort u1 = d_tm.mkUnresolvedDatatypeSort("dt1", 1);
  DatatypeDecl dtdecl0 = d_tm.mkDatatypeDecl("dt0", {p0});
  DatatypeDecl dtdecl1 = d_tm.mkDatatypeDecl("dt1", {p1});
  DatatypeConstructorDecl ctordecl0 = d_tm.mkDatatypeConstructorDecl("c0");
  ctordecl0.addSelector("s0", u1.instantiate({p0}));
  DatatypeConstructorDecl ctordecl1 = d_tm.mkDatatypeConstructorDecl("c1");
  ctordecl1.addSelector("s1", u0.instantiate({p1}));
  dtdecl0.addConstructor(ctordecl0);
  dtdecl1.addConstructor(ctordecl1);
  dtdecl1.addConstructor(d_tm.mkDatatypeConstructorDecl("nil"));
  std::vector<Sort> dt_sorts = d_tm.mkDatatypeSorts({dtdecl0, dtdecl1});
  Sort isort1 = dt_sorts[1].instantiate({d_tm.getBooleanSort()});
  Term t1 = d_tm.mkConst(isort1, "t");
  Term t0 =
      d_tm.mkTerm(Kind::APPLY_SELECTOR,
                  {t1.getSort().getDatatype().getSelector("s1").getTerm(), t1});
  ASSERT_EQ(dt_sorts[0].instantiate({d_tm.getBooleanSort()}), t0.getSort());

  {
    TermManager tm;
    DatatypeDecl dtypeSpec1 = tm.mkDatatypeDecl("list1");
    DatatypeConstructorDecl cons1 = tm.mkDatatypeConstructorDecl("cons1");
    cons1.addSelector("head1", tm.getIntegerSort());
    dtypeSpec1.addConstructor(cons1);
    DatatypeConstructorDecl nil1 = tm.mkDatatypeConstructorDecl("nil1");
    dtypeSpec1.addConstructor(nil1);
    DatatypeDecl dtypeSpec2 = tm.mkDatatypeDecl("list2");
    DatatypeConstructorDecl cons2 = tm.mkDatatypeConstructorDecl("cons2");
    cons2.addSelector("head2", tm.getIntegerSort());
    dtypeSpec2.addConstructor(cons2);
    DatatypeConstructorDecl nil2 = tm.mkDatatypeConstructorDecl("nil2");
    dtypeSpec2.addConstructor(nil2);
    std::vector<DatatypeDecl> decls = {dtypeSpec1, dtypeSpec2};
    ASSERT_THROW(d_tm.mkDatatypeSorts(decls), CVC5ApiException);
  }

  /* Note: More tests are in datatype_api_black. */
}

TEST_F(TestApiBlackTermManager, mkFunctionSort)
{
  ASSERT_NO_THROW(d_tm.mkFunctionSort({d_tm.mkUninterpretedSort("u")},
                                      d_tm.getIntegerSort()));
  Sort funSort = d_tm.mkFunctionSort({d_tm.mkUninterpretedSort("u")},
                                     d_tm.getIntegerSort());
  // function arguments are allowed
  ASSERT_NO_THROW(d_tm.mkFunctionSort({funSort}, d_tm.getIntegerSort()));
  ASSERT_THROW(d_tm.mkFunctionSort({d_tm.getIntegerSort()}, funSort),
               CVC5ApiException);
  ASSERT_NO_THROW(d_tm.mkFunctionSort(
      {d_tm.mkUninterpretedSort("u"), d_tm.getIntegerSort()},
      d_tm.getIntegerSort()));
  Sort funSort2 = d_tm.mkFunctionSort({d_tm.mkUninterpretedSort("u")},
                                      d_tm.getIntegerSort());
  // function arguments are allowed
  ASSERT_NO_THROW(d_tm.mkFunctionSort({funSort2, d_tm.mkUninterpretedSort("u")},
                                      d_tm.getIntegerSort()));
  ASSERT_THROW(
      d_tm.mkFunctionSort(
          {d_tm.getIntegerSort(), d_tm.mkUninterpretedSort("u")}, funSort2),
      CVC5ApiException);

  std::vector<Sort> sorts1 = {
      d_tm.getBooleanSort(), d_tm.getIntegerSort(), d_tm.getIntegerSort()};
  std::vector<Sort> sorts2 = {d_tm.getBooleanSort(), d_tm.getIntegerSort()};
  ASSERT_NO_THROW(d_tm.mkFunctionSort(sorts2, d_tm.getIntegerSort()));
  ASSERT_NO_THROW(d_tm.mkFunctionSort(sorts1, d_tm.getIntegerSort()));

  TermManager tm;
  ASSERT_THROW(tm.mkFunctionSort(sorts2, tm.getIntegerSort()),
               CVC5ApiException);
  ASSERT_THROW(tm.mkFunctionSort({tm.getBooleanSort(), tm.getIntegerSort()},
                                 d_tm.getIntegerSort()),
               CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkParamSort)
{
  ASSERT_NO_THROW(d_tm.mkParamSort("T"));
  ASSERT_NO_THROW(d_tm.mkParamSort(""));
}

TEST_F(TestApiBlackTermManager, mkPredicateSort)
{
  ASSERT_NO_THROW(d_tm.mkPredicateSort({d_tm.getIntegerSort()}));
  ASSERT_THROW(d_tm.mkPredicateSort({}), CVC5ApiException);
  Sort funSort = d_tm.mkFunctionSort({d_tm.mkUninterpretedSort("u")},
                                     d_tm.getIntegerSort());
  // functions as arguments are allowed
  ASSERT_NO_THROW(d_tm.mkPredicateSort({d_tm.getIntegerSort(), funSort}));

  ASSERT_NO_THROW(d_tm.mkPredicateSort({d_tm.getIntegerSort()}));

  TermManager tm;
  ASSERT_THROW(tm.mkPredicateSort({d_tm.getIntegerSort()}), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkRecordSort)
{
  std::vector<std::pair<std::string, Sort>> fields = {
      std::make_pair("b", d_tm.getBooleanSort()),
      std::make_pair("bv", d_tm.mkBitVectorSort(8)),
      std::make_pair("i", d_tm.getIntegerSort())};
  std::vector<std::pair<std::string, Sort>> empty;
  ASSERT_NO_THROW(d_tm.mkRecordSort(fields));
  ASSERT_NO_THROW(d_tm.mkRecordSort(empty));
  Sort recSort = d_tm.mkRecordSort(fields);
  ASSERT_NO_THROW(recSort.getDatatype());
  ASSERT_NO_THROW(d_tm.mkRecordSort(fields));

  TermManager tm;
  ASSERT_THROW(tm.mkRecordSort({{"b", tm.getBooleanSort()},
                                {"bv", d_tm.mkBitVectorSort(8)},
                                {"i", tm.getIntegerSort()}}),
               CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkSetSort)
{
  ASSERT_NO_THROW(d_tm.mkSetSort(d_tm.getBooleanSort()));
  ASSERT_NO_THROW(d_tm.mkSetSort(d_tm.getIntegerSort()));
  ASSERT_NO_THROW(d_tm.mkSetSort(d_tm.mkBitVectorSort(4)));
  ASSERT_NO_THROW(d_tm.mkSetSort(d_tm.mkBitVectorSort(4)));
  TermManager tm;
  ASSERT_THROW(d_tm.mkSetSort(tm.getBooleanSort()), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkBagSort)
{
  ASSERT_NO_THROW(d_tm.mkBagSort(d_tm.getBooleanSort()));
  ASSERT_NO_THROW(d_tm.mkBagSort(d_tm.getIntegerSort()));
  ASSERT_NO_THROW(d_tm.mkBagSort(d_tm.mkBitVectorSort(4)));
  ASSERT_NO_THROW(d_tm.mkBagSort(d_tm.mkBitVectorSort(4)));
  TermManager tm;
  ASSERT_THROW(d_tm.mkBagSort(tm.getBooleanSort()), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkSequenceSort)
{
  ASSERT_NO_THROW(d_tm.mkSequenceSort(d_tm.getBooleanSort()));
  ASSERT_NO_THROW(
      d_tm.mkSequenceSort(d_tm.mkSequenceSort(d_tm.getIntegerSort())));
  ASSERT_NO_THROW(d_tm.mkSequenceSort(d_tm.getIntegerSort()));
  TermManager tm;
  ASSERT_THROW(d_tm.mkSequenceSort(tm.getBooleanSort()), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkAbstractSort)
{
  ASSERT_NO_THROW(d_tm.mkAbstractSort(SortKind::ARRAY_SORT));
  ASSERT_NO_THROW(d_tm.mkAbstractSort(SortKind::BITVECTOR_SORT));
  ASSERT_NO_THROW(d_tm.mkAbstractSort(SortKind::TUPLE_SORT));
  ASSERT_NO_THROW(d_tm.mkAbstractSort(SortKind::SET_SORT));
  ASSERT_THROW(d_tm.mkAbstractSort(SortKind::BOOLEAN_SORT), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkUninterpretedSort)
{
  ASSERT_NO_THROW(d_tm.mkUninterpretedSort("u"));
  ASSERT_NO_THROW(d_tm.mkUninterpretedSort(""));
}

TEST_F(TestApiBlackTermManager, mkUnresolvedDatatypeSort)
{
  ASSERT_NO_THROW(d_tm.mkUnresolvedDatatypeSort("u"));
  ASSERT_NO_THROW(d_tm.mkUnresolvedDatatypeSort("u", 1));
  ASSERT_NO_THROW(d_tm.mkUnresolvedDatatypeSort(""));
  ASSERT_NO_THROW(d_tm.mkUnresolvedDatatypeSort("", 1));
}

TEST_F(TestApiBlackTermManager, mkUninterpretedSortConstructorSort)
{
  ASSERT_NO_THROW(d_tm.mkUninterpretedSortConstructorSort(2, "s"));
  ASSERT_NO_THROW(d_tm.mkUninterpretedSortConstructorSort(2, ""));
  ASSERT_THROW(d_tm.mkUninterpretedSortConstructorSort(0), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkTupleSort)
{
  ASSERT_NO_THROW(d_tm.mkTupleSort({d_tm.getIntegerSort()}));
  Sort funSort = d_tm.mkFunctionSort({d_tm.mkUninterpretedSort("u")},
                                     d_tm.getIntegerSort());
  ASSERT_NO_THROW(d_tm.mkTupleSort({d_tm.getIntegerSort(), funSort}));

  ASSERT_NO_THROW(d_tm.mkTupleSort({d_tm.getIntegerSort()}));
  TermManager tm;
  ASSERT_THROW(d_tm.mkTupleSort({tm.getBooleanSort()}), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkNullableSort)
{
  ASSERT_NO_THROW(d_tm.mkNullableSort(d_tm.getIntegerSort()));
  ASSERT_NO_THROW(d_tm.mkNullableSort(d_tm.getIntegerSort()));
  TermManager tm;
  ASSERT_THROW(d_tm.mkNullableSort(tm.getIntegerSort()), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkBitVector)
{
  ASSERT_NO_THROW(d_tm.mkBitVector(8, 2));
  ASSERT_NO_THROW(d_tm.mkBitVector(32, 2));
  ASSERT_NO_THROW(d_tm.mkBitVector(8, "-1111111", 2));
  ASSERT_NO_THROW(d_tm.mkBitVector(8, "0101", 2));
  ASSERT_NO_THROW(d_tm.mkBitVector(8, "00000101", 2));
  ASSERT_NO_THROW(d_tm.mkBitVector(8, "-127", 10));
  ASSERT_NO_THROW(d_tm.mkBitVector(8, "255", 10));
  ASSERT_NO_THROW(d_tm.mkBitVector(8, "-7f", 16));
  ASSERT_NO_THROW(d_tm.mkBitVector(8, "a0", 16));

  ASSERT_THROW(d_tm.mkBitVector(0, 2), CVC5ApiException);
  ASSERT_THROW(d_tm.mkBitVector(0, "-127", 10), CVC5ApiException);
  ASSERT_THROW(d_tm.mkBitVector(0, "a0", 16), CVC5ApiException);

  ASSERT_THROW(d_tm.mkBitVector(8, "", 2), CVC5ApiException);

  ASSERT_THROW(d_tm.mkBitVector(8, "101", 5), CVC5ApiException);
  ASSERT_THROW(d_tm.mkBitVector(8, "128", 11), CVC5ApiException);
  ASSERT_THROW(d_tm.mkBitVector(8, "a0", 21), CVC5ApiException);

  ASSERT_THROW(d_tm.mkBitVector(8, "-11111111", 2), CVC5ApiException);
  ASSERT_THROW(d_tm.mkBitVector(8, "101010101", 2), CVC5ApiException);
  ASSERT_THROW(d_tm.mkBitVector(8, "-256", 10), CVC5ApiException);
  ASSERT_THROW(d_tm.mkBitVector(8, "257", 10), CVC5ApiException);
  ASSERT_THROW(d_tm.mkBitVector(8, "-a0", 16), CVC5ApiException);
  ASSERT_THROW(d_tm.mkBitVector(8, "fffff", 16), CVC5ApiException);

  ASSERT_THROW(d_tm.mkBitVector(8, "10201010", 2), CVC5ApiException);
  ASSERT_THROW(d_tm.mkBitVector(8, "-25x", 10), CVC5ApiException);
  ASSERT_THROW(d_tm.mkBitVector(8, "2x7", 10), CVC5ApiException);
  ASSERT_THROW(d_tm.mkBitVector(8, "fzff", 16), CVC5ApiException);

  ASSERT_EQ(d_tm.mkBitVector(8, "0101", 2), d_tm.mkBitVector(8, "00000101", 2));
  ASSERT_EQ(d_tm.mkBitVector(4, "-1", 2), d_tm.mkBitVector(4, "1111", 2));
  ASSERT_EQ(d_tm.mkBitVector(4, "-1", 16), d_tm.mkBitVector(4, "1111", 2));
  ASSERT_EQ(d_tm.mkBitVector(4, "-1", 10), d_tm.mkBitVector(4, "1111", 2));
  ASSERT_EQ(d_tm.mkBitVector(8, "01010101", 2).toString(), "#b01010101");
  ASSERT_EQ(d_tm.mkBitVector(8, "F", 16).toString(), "#b00001111");
  ASSERT_EQ(d_tm.mkBitVector(8, "-1", 10), d_tm.mkBitVector(8, "FF", 16));
}

TEST_F(TestApiBlackTermManager, mkFiniteFieldElem)
{
  Sort f = d_tm.mkFiniteFieldSort("7");
  Sort bv = d_tm.mkBitVectorSort(4);

  ASSERT_NO_THROW(d_tm.mkFiniteFieldElem("0", f));
  ASSERT_NO_THROW(d_tm.mkFiniteFieldElem("1", f));
  ASSERT_NO_THROW(d_tm.mkFiniteFieldElem("6", f));
  ASSERT_NO_THROW(d_tm.mkFiniteFieldElem("8", f));
  ASSERT_NO_THROW(d_tm.mkFiniteFieldElem("-1", f));

  ASSERT_THROW(d_tm.mkFiniteFieldElem("a", f), CVC5ApiException);

  ASSERT_THROW(d_tm.mkFiniteFieldElem("-1", bv), CVC5ApiException);

  ASSERT_EQ(d_tm.mkFiniteFieldElem("-1", f), d_tm.mkFiniteFieldElem("6", f));
  ASSERT_EQ(d_tm.mkFiniteFieldElem("1", f), d_tm.mkFiniteFieldElem("8", f));

  ASSERT_NO_THROW(d_tm.mkFiniteFieldElem("0", f, 2));
  ASSERT_NO_THROW(d_tm.mkFiniteFieldElem("101", f, 3));
  ASSERT_NO_THROW(d_tm.mkFiniteFieldElem("-10", f, 7));
  ASSERT_NO_THROW(d_tm.mkFiniteFieldElem("abcde", f, 16));

  ASSERT_EQ(d_tm.mkFiniteFieldElem("0", f, 2),
            d_tm.mkFiniteFieldElem("0", f, 3));
  ASSERT_EQ(d_tm.mkFiniteFieldElem("11", f, 2),
            d_tm.mkFiniteFieldElem("10", f, 3));
  ASSERT_EQ(d_tm.mkFiniteFieldElem("1010", f, 2),
            d_tm.mkFiniteFieldElem("A", f, 16));

  ASSERT_EQ(d_tm.mkFiniteFieldElem("-22", f, 3),
            d_tm.mkFiniteFieldElem("10", f, 6));
}

TEST_F(TestApiBlackTermManager, mkConstArray)
{
  Sort intSort = d_tm.getIntegerSort();
  Sort arrSort = d_tm.mkArraySort(intSort, intSort);
  Term zero = d_tm.mkInteger(0);
  Term constArr = d_tm.mkConstArray(arrSort, zero);

  ASSERT_THROW(d_tm.mkConstArray(Sort(), zero), CVC5ApiException);
  ASSERT_THROW(d_tm.mkConstArray(arrSort, Term()), CVC5ApiException);
  ASSERT_THROW(d_tm.mkConstArray(arrSort, d_tm.mkBitVector(1, 1)),
               CVC5ApiException);
  ASSERT_THROW(d_tm.mkConstArray(intSort, zero), CVC5ApiException);
  Term zero2 = d_tm.mkInteger(0);
  Sort arrSort2 =
      d_tm.mkArraySort(d_tm.getIntegerSort(), d_tm.getIntegerSort());
  ASSERT_NO_THROW(d_tm.mkConstArray(arrSort2, zero));
  ASSERT_NO_THROW(d_tm.mkConstArray(arrSort, zero2));
  TermManager tm;
  ASSERT_THROW(tm.mkConstArray(arrSort, tm.mkInteger(0)), CVC5ApiException);
  ASSERT_THROW(
      tm.mkConstArray(tm.mkArraySort(tm.getIntegerSort(), tm.getIntegerSort()),
                      zero),
      CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkVar)
{
  Sort boolSort = d_tm.getBooleanSort();
  Sort intSort = d_tm.getIntegerSort();
  Sort funSort = d_tm.mkFunctionSort({intSort}, boolSort);
  ASSERT_NO_THROW(d_tm.mkVar(boolSort));
  ASSERT_NO_THROW(d_tm.mkVar(funSort));
  ASSERT_NO_THROW(d_tm.mkVar(boolSort, std::string("b")));
  ASSERT_NO_THROW(d_tm.mkVar(funSort, ""));
  ASSERT_THROW(d_tm.mkVar(Sort()), CVC5ApiException);
  ASSERT_THROW(d_tm.mkVar(Sort(), "a"), CVC5ApiException);
  ASSERT_NO_THROW(d_tm.mkVar(boolSort, "x"));
  TermManager tm;
  ASSERT_THROW(tm.mkVar(boolSort, "c"), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkBoolean)
{
  ASSERT_NO_THROW(d_tm.mkBoolean(true));
  ASSERT_NO_THROW(d_tm.mkBoolean(false));
}

TEST_F(TestApiBlackTermManager, mkRoundingMode)
{
  ASSERT_EQ(
      d_tm.mkRoundingMode(RoundingMode::ROUND_NEAREST_TIES_TO_EVEN).toString(),
      "roundNearestTiesToEven");
  ASSERT_EQ(d_tm.mkRoundingMode(RoundingMode::ROUND_TOWARD_POSITIVE).toString(),
            "roundTowardPositive");
  ASSERT_EQ(d_tm.mkRoundingMode(RoundingMode::ROUND_TOWARD_NEGATIVE).toString(),
            "roundTowardNegative");
  ASSERT_EQ(d_tm.mkRoundingMode(RoundingMode::ROUND_TOWARD_ZERO).toString(),
            "roundTowardZero");
  ASSERT_EQ(
      d_tm.mkRoundingMode(RoundingMode::ROUND_NEAREST_TIES_TO_AWAY).toString(),
      "roundNearestTiesToAway");
}

TEST_F(TestApiBlackTermManager, mkFloatingPoint)
{
  Term t1 = d_tm.mkBitVector(8);
  Term t2 = d_tm.mkBitVector(4);
  ASSERT_NO_THROW(d_tm.mkFloatingPoint(3, 5, t1));
  ASSERT_THROW(d_tm.mkFloatingPoint(0, 5, Term()), CVC5ApiException);
  ASSERT_THROW(d_tm.mkFloatingPoint(0, 5, t1), CVC5ApiException);
  ASSERT_THROW(d_tm.mkFloatingPoint(1, 5, t1), CVC5ApiException);
  ASSERT_THROW(d_tm.mkFloatingPoint(3, 0, t1), CVC5ApiException);
  ASSERT_THROW(d_tm.mkFloatingPoint(3, 1, t1), CVC5ApiException);
  ASSERT_THROW(d_tm.mkFloatingPoint(3, 5, t2), CVC5ApiException);

  ASSERT_EQ(d_tm.mkFloatingPoint(
                d_tm.mkBitVector(1), d_tm.mkBitVector(5), d_tm.mkBitVector(10)),
            d_tm.mkFloatingPoint(5, 11, d_tm.mkBitVector(16)));
  ASSERT_THROW(
      d_tm.mkFloatingPoint(Term(), d_tm.mkBitVector(5), d_tm.mkBitVector(10)),
      CVC5ApiException);
  ASSERT_THROW(
      d_tm.mkFloatingPoint(d_tm.mkBitVector(1), Term(), d_tm.mkBitVector(10)),
      CVC5ApiException);
  ASSERT_THROW(
      d_tm.mkFloatingPoint(d_tm.mkBitVector(1), d_tm.mkBitVector(5), Term()),
      CVC5ApiException);
  ASSERT_THROW(d_tm.mkFloatingPoint(d_tm.mkConst(d_tm.mkBitVectorSort(1)),
                                    d_tm.mkBitVector(5),
                                    d_tm.mkBitVector(10)),
               CVC5ApiException);
  ASSERT_THROW(d_tm.mkFloatingPoint(d_tm.mkBitVector(1),
                                    d_tm.mkConst(d_tm.mkBitVectorSort(5)),
                                    d_tm.mkBitVector(10)),
               CVC5ApiException);
  ASSERT_THROW(d_tm.mkFloatingPoint(d_tm.mkBitVector(1),
                                    d_tm.mkBitVector(5),
                                    d_tm.mkConst(d_tm.mkBitVectorSort(5))),
               CVC5ApiException);
  ASSERT_THROW(
      d_tm.mkFloatingPoint(
          d_tm.mkBitVector(2), d_tm.mkBitVector(5), d_tm.mkBitVector(10)),
      CVC5ApiException);

  TermManager tm;
  ASSERT_THROW(tm.mkFloatingPoint(3, 5, t1), CVC5ApiException);
  ASSERT_THROW(tm.mkFloatingPoint(
                   d_tm.mkBitVector(1), tm.mkBitVector(5), tm.mkBitVector(10)),
               CVC5ApiException);
  ASSERT_THROW(tm.mkFloatingPoint(
                   tm.mkBitVector(1), d_tm.mkBitVector(5), tm.mkBitVector(10)),
               CVC5ApiException);
  ASSERT_THROW(tm.mkFloatingPoint(
                   tm.mkBitVector(1), tm.mkBitVector(5), d_tm.mkBitVector(10)),
               CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkCardinalityConstraint)
{
  Sort su = d_tm.mkUninterpretedSort("u");
  Sort si = d_tm.getIntegerSort();
  ASSERT_NO_THROW(d_tm.mkCardinalityConstraint(su, 3));
  ASSERT_THROW(d_tm.mkCardinalityConstraint(si, 3), CVC5ApiException);
  ASSERT_THROW(d_tm.mkCardinalityConstraint(su, 0), CVC5ApiException);
  ASSERT_NO_THROW(d_tm.mkCardinalityConstraint(su, 3));
  TermManager tm;
  ASSERT_THROW(tm.mkCardinalityConstraint(su, 3), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkEmptySet)
{
  Sort s = d_tm.mkSetSort(d_tm.getBooleanSort());
  ASSERT_THROW(d_tm.mkEmptySet(Sort()), CVC5ApiException);
  ASSERT_NO_THROW(d_tm.mkEmptySet(s));
  ASSERT_THROW(d_tm.mkEmptySet(d_tm.getBooleanSort()), CVC5ApiException);
  ASSERT_NO_THROW(d_tm.mkEmptySet(s));
  TermManager tm;
  ASSERT_THROW(tm.mkEmptySet(s), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkEmptyBag)
{
  Sort s = d_tm.mkBagSort(d_tm.getBooleanSort());
  ASSERT_THROW(d_tm.mkEmptyBag(Sort()), CVC5ApiException);
  ASSERT_NO_THROW(d_tm.mkEmptyBag(s));
  ASSERT_THROW(d_tm.mkEmptyBag(d_tm.getBooleanSort()), CVC5ApiException);
  ASSERT_NO_THROW(d_tm.mkEmptyBag(s));
  TermManager tm;
  ASSERT_THROW(tm.mkEmptyBag(s), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkEmptySequence)
{
  Sort s = d_tm.mkSequenceSort(d_tm.getBooleanSort());
  ASSERT_NO_THROW(d_tm.mkEmptySequence(s));
  ASSERT_NO_THROW(d_tm.mkEmptySequence(d_tm.getBooleanSort()));
  ASSERT_NO_THROW(d_tm.mkEmptySequence(s));
  TermManager tm;
  ASSERT_THROW(tm.mkEmptySequence(s), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkFalse)
{
  ASSERT_NO_THROW(d_tm.mkFalse());
  ASSERT_NO_THROW(d_tm.mkFalse());
}

TEST_F(TestApiBlackTermManager, mkFloatingPointNaN)
{
  ASSERT_NO_THROW(d_tm.mkFloatingPointNaN(3, 5));
}

TEST_F(TestApiBlackTermManager, mkFloatingPointNegZero)
{
  ASSERT_NO_THROW(d_tm.mkFloatingPointNegZero(3, 5));
}

TEST_F(TestApiBlackTermManager, mkFloatingPointNegInf)
{
  ASSERT_NO_THROW(d_tm.mkFloatingPointNegInf(3, 5));
}

TEST_F(TestApiBlackTermManager, mkFloatingPointPosInf)
{
  ASSERT_NO_THROW(d_tm.mkFloatingPointPosInf(3, 5));
}

TEST_F(TestApiBlackTermManager, mkFloatingPointPosZero)
{
  ASSERT_NO_THROW(d_tm.mkFloatingPointPosZero(3, 5));
}

TEST_F(TestApiBlackTermManager, mkOp)
{
  // mkOp(Kind kind, const std::string& arg)
  ASSERT_NO_THROW(d_tm.mkOp(Kind::DIVISIBLE, "2147483648"));
  ASSERT_THROW(d_tm.mkOp(Kind::BITVECTOR_EXTRACT, "asdf"), CVC5ApiException);

  // mkOp(Kind kind, std::vector<uint32_t> args)
  ASSERT_NO_THROW(d_tm.mkOp(Kind::DIVISIBLE, {1}));
  ASSERT_NO_THROW(d_tm.mkOp(Kind::BITVECTOR_ROTATE_LEFT, {1}));
  ASSERT_NO_THROW(d_tm.mkOp(Kind::BITVECTOR_ROTATE_RIGHT, {1}));
  ASSERT_THROW(d_tm.mkOp(Kind::BITVECTOR_EXTRACT, {1}), CVC5ApiException);

  ASSERT_NO_THROW(d_tm.mkOp(Kind::BITVECTOR_EXTRACT, {1, 1}));
  ASSERT_THROW(d_tm.mkOp(Kind::DIVISIBLE, {1, 2}), CVC5ApiException);

  ASSERT_NO_THROW(d_tm.mkOp(Kind::TUPLE_PROJECT, {1, 2, 2}));
}

TEST_F(TestApiBlackTermManager, mkPi) { ASSERT_NO_THROW(d_tm.mkPi()); }

TEST_F(TestApiBlackTermManager, mkInteger)
{
  ASSERT_NO_THROW(d_tm.mkInteger("123"));
  ASSERT_THROW(d_tm.mkInteger("1.23"), CVC5ApiException);
  ASSERT_THROW(d_tm.mkInteger("1/23"), CVC5ApiException);
  ASSERT_THROW(d_tm.mkInteger("12/3"), CVC5ApiException);
  ASSERT_THROW(d_tm.mkInteger(".2"), CVC5ApiException);
  ASSERT_THROW(d_tm.mkInteger("2."), CVC5ApiException);
  ASSERT_THROW(d_tm.mkInteger(""), CVC5ApiException);
  ASSERT_THROW(d_tm.mkInteger("asdf"), CVC5ApiException);
  ASSERT_THROW(d_tm.mkInteger("1.2/3"), CVC5ApiException);
  ASSERT_THROW(d_tm.mkInteger("."), CVC5ApiException);
  ASSERT_THROW(d_tm.mkInteger("/"), CVC5ApiException);
  ASSERT_THROW(d_tm.mkInteger("2/"), CVC5ApiException);
  ASSERT_THROW(d_tm.mkInteger("/2"), CVC5ApiException);

  ASSERT_NO_THROW(d_tm.mkInteger(1));
  ASSERT_NO_THROW(d_tm.mkInteger(-1));
}

TEST_F(TestApiBlackTermManager, mkReal)
{
  ASSERT_NO_THROW(d_tm.mkReal("123"));
  ASSERT_NO_THROW(d_tm.mkReal("1.23"));
  ASSERT_NO_THROW(d_tm.mkReal("1/23"));
  ASSERT_NO_THROW(d_tm.mkReal("12/3"));
  ASSERT_NO_THROW(d_tm.mkReal(".2"));
  ASSERT_NO_THROW(d_tm.mkReal("2."));
  ASSERT_THROW(d_tm.mkReal(""), CVC5ApiException);
  ASSERT_THROW(d_tm.mkReal("asdf"), CVC5ApiException);
  ASSERT_THROW(d_tm.mkReal("1.2/3"), CVC5ApiException);
  ASSERT_THROW(d_tm.mkReal("."), CVC5ApiException);
  ASSERT_THROW(d_tm.mkReal("/"), CVC5ApiException);
  ASSERT_THROW(d_tm.mkReal("2/"), CVC5ApiException);
  ASSERT_THROW(d_tm.mkReal("/2"), CVC5ApiException);

  int32_t val1 = 1;
  int64_t val2 = -1;
  uint32_t val3 = 1;
  uint64_t val4 = -1;
  ASSERT_NO_THROW(d_tm.mkReal(val1));
  ASSERT_NO_THROW(d_tm.mkReal(val2));
  ASSERT_NO_THROW(d_tm.mkReal(val3));
  ASSERT_NO_THROW(d_tm.mkReal(val4));
  ASSERT_NO_THROW(d_tm.mkReal(val4));
  ASSERT_NO_THROW(d_tm.mkReal(val1, val1));
  ASSERT_NO_THROW(d_tm.mkReal(val2, val2));
  ASSERT_NO_THROW(d_tm.mkReal(val3, val3));
  ASSERT_NO_THROW(d_tm.mkReal(val4, val4));
  ASSERT_NO_THROW(d_tm.mkReal("-1/-1"));
  ASSERT_NO_THROW(d_tm.mkReal("1/-1"));
  ASSERT_NO_THROW(d_tm.mkReal("-1/1"));
  ASSERT_NO_THROW(d_tm.mkReal("1/1"));
  ASSERT_THROW(d_tm.mkReal("/-5"), CVC5ApiException);
  ASSERT_THROW(d_tm.mkReal(1, 0), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkRegexpAll)
{
  Sort strSort = d_tm.getStringSort();
  Term s = d_tm.mkConst(strSort, "s");
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::STRING_IN_REGEXP, {s, d_tm.mkRegexpAll()}));
}

TEST_F(TestApiBlackTermManager, mkRegexpAllchar)
{
  Sort strSort = d_tm.getStringSort();
  Term s = d_tm.mkConst(strSort, "s");
  ASSERT_NO_THROW(
      d_tm.mkTerm(Kind::STRING_IN_REGEXP, {s, d_tm.mkRegexpAllchar()}));
}

TEST_F(TestApiBlackTermManager, mkRegexpNone)
{
  Sort strSort = d_tm.getStringSort();
  Term s = d_tm.mkConst(strSort, "s");
  ASSERT_NO_THROW(
      d_tm.mkTerm(Kind::STRING_IN_REGEXP, {s, d_tm.mkRegexpNone()}));
}

TEST_F(TestApiBlackTermManager, mkSepEmp) { ASSERT_NO_THROW(d_tm.mkSepEmp()); }

TEST_F(TestApiBlackTermManager, mkSepNil)
{
  ASSERT_NO_THROW(d_tm.mkSepNil(d_tm.getBooleanSort()));
  ASSERT_THROW(d_tm.mkSepNil(Sort()), CVC5ApiException);
  ASSERT_NO_THROW(d_tm.mkSepNil(d_tm.getIntegerSort()));
  TermManager tm;
  ASSERT_THROW(tm.mkSepNil(d_tm.getBooleanSort()), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkString)
{
  ASSERT_NO_THROW(d_tm.mkString(""));
  ASSERT_NO_THROW(d_tm.mkString("asdfasdf"));
  ASSERT_EQ(d_tm.mkString("asdf\\nasdf").toString(), "\"asdf\\u{5c}nasdf\"");
  ASSERT_EQ(d_tm.mkString("asdf\\u{005c}nasdf", true).toString(),
            "\"asdf\\u{5c}nasdf\"");
  std::u32string s;
  ASSERT_EQ(d_tm.mkString(s).getU32StringValue(), s);
}

TEST_F(TestApiBlackTermManager, mkTerm)
{
  Sort bv32 = d_tm.mkBitVectorSort(32);
  Term a = d_tm.mkConst(bv32, "a");
  Term b = d_tm.mkConst(bv32, "b");
  std::vector<Term> v1 = {a, b};
  std::vector<Term> v2 = {a, Term()};
  std::vector<Term> v3 = {a, d_tm.mkTrue()};
  std::vector<Term> v4 = {d_tm.mkInteger(1), d_tm.mkInteger(2)};
  std::vector<Term> v5 = {d_tm.mkInteger(1), Term()};
  std::vector<Term> v6 = {};

  ASSERT_NO_THROW(d_tm.mkTerm(Kind::PI));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::PI, {v6}));
  ASSERT_NO_THROW(d_tm.mkTerm(d_tm.mkOp(Kind::PI)));
  ASSERT_NO_THROW(d_tm.mkTerm(d_tm.mkOp(Kind::PI), {v6}));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::REGEXP_NONE));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::REGEXP_NONE, {v6}));
  ASSERT_NO_THROW(d_tm.mkTerm(d_tm.mkOp(Kind::REGEXP_NONE)));
  ASSERT_NO_THROW(d_tm.mkTerm(d_tm.mkOp(Kind::REGEXP_NONE), {v6}));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::REGEXP_ALLCHAR));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::REGEXP_ALLCHAR, {v6}));
  ASSERT_NO_THROW(d_tm.mkTerm(d_tm.mkOp(Kind::REGEXP_ALLCHAR)));
  ASSERT_NO_THROW(d_tm.mkTerm(d_tm.mkOp(Kind::REGEXP_ALLCHAR), {v6}));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::SEP_EMP));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::SEP_EMP, {v6}));
  ASSERT_NO_THROW(d_tm.mkTerm(d_tm.mkOp(Kind::SEP_EMP)));
  ASSERT_NO_THROW(d_tm.mkTerm(d_tm.mkOp(Kind::SEP_EMP), {v6}));
  ASSERT_THROW(d_tm.mkTerm(Kind::CONST_BITVECTOR), CVC5ApiException);

  ASSERT_NO_THROW(d_tm.mkTerm(Kind::NOT, {d_tm.mkTrue()}));
  ASSERT_NO_THROW(
      d_tm.mkTerm(Kind::BAG_MAKE, {d_tm.mkTrue(), d_tm.mkInteger(1)}));
  ASSERT_THROW(d_tm.mkTerm(Kind::NOT, {Term()}), CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(Kind::NOT, {a}), CVC5ApiException);
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::NOT, {d_tm.mkTrue()}));

  ASSERT_NO_THROW(d_tm.mkTerm(Kind::EQUAL, {a, b}));
  ASSERT_THROW(d_tm.mkTerm(Kind::EQUAL, {Term(), b}), CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(Kind::EQUAL, {a, Term()}), CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(Kind::EQUAL, {a, d_tm.mkTrue()}), CVC5ApiException);
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::EQUAL, {a, b}));

  ASSERT_NO_THROW(
      d_tm.mkTerm(Kind::ITE, {d_tm.mkTrue(), d_tm.mkTrue(), d_tm.mkTrue()}));
  ASSERT_THROW(d_tm.mkTerm(Kind::ITE, {Term(), d_tm.mkTrue(), d_tm.mkTrue()}),
               CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(Kind::ITE, {d_tm.mkTrue(), Term(), d_tm.mkTrue()}),
               CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(Kind::ITE, {d_tm.mkTrue(), d_tm.mkTrue(), Term()}),
               CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(Kind::ITE, {d_tm.mkTrue(), d_tm.mkTrue(), b}),
               CVC5ApiException);
  ASSERT_NO_THROW(
      d_tm.mkTerm(Kind::ITE, {d_tm.mkTrue(), d_tm.mkTrue(), d_tm.mkTrue()}));

  ASSERT_NO_THROW(d_tm.mkTerm(Kind::EQUAL, {v1}));
  ASSERT_THROW(d_tm.mkTerm(Kind::EQUAL, {v2}), CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(Kind::EQUAL, {v3}), CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(Kind::DISTINCT, {v6}), CVC5ApiException);

  // Test cases that are nary via the API but have arity = 2 internally
  Sort s_bool = d_tm.getBooleanSort();
  Term t_bool = d_tm.mkConst(s_bool, "t_bool");
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::IMPLIES, {t_bool, t_bool, t_bool}));
  ASSERT_NO_THROW(
      d_tm.mkTerm(d_tm.mkOp(Kind::IMPLIES), {t_bool, t_bool, t_bool}));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::XOR, {t_bool, t_bool, t_bool}));
  ASSERT_NO_THROW(d_tm.mkTerm(d_tm.mkOp(Kind::XOR), {t_bool, t_bool, t_bool}));
  Term t_int = d_tm.mkConst(d_tm.getIntegerSort(), "t_int");
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::DIVISION, {t_int, t_int, t_int}));
  ASSERT_NO_THROW(
      d_tm.mkTerm(d_tm.mkOp(Kind::DIVISION), {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::INTS_DIVISION, {t_int, t_int, t_int}));
  ASSERT_NO_THROW(
      d_tm.mkTerm(d_tm.mkOp(Kind::INTS_DIVISION), {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::SUB, {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_tm.mkTerm(d_tm.mkOp(Kind::SUB), {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::EQUAL, {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_tm.mkTerm(d_tm.mkOp(Kind::EQUAL), {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::LT, {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_tm.mkTerm(d_tm.mkOp(Kind::LT), {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::GT, {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_tm.mkTerm(d_tm.mkOp(Kind::GT), {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::LEQ, {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_tm.mkTerm(d_tm.mkOp(Kind::LEQ), {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::GEQ, {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_tm.mkTerm(d_tm.mkOp(Kind::GEQ), {t_int, t_int, t_int}));
  Term t_reg = d_tm.mkConst(d_tm.getRegExpSort(), "t_reg");
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::REGEXP_DIFF, {t_reg, t_reg, t_reg}));
  ASSERT_NO_THROW(
      d_tm.mkTerm(d_tm.mkOp(Kind::REGEXP_DIFF), {t_reg, t_reg, t_reg}));
  Term t_fun =
      d_tm.mkConst(d_tm.mkFunctionSort({s_bool, s_bool, s_bool}, s_bool));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::HO_APPLY, {t_fun, t_bool, t_bool, t_bool}));
  ASSERT_NO_THROW(
      d_tm.mkTerm(d_tm.mkOp(Kind::HO_APPLY), {t_fun, t_bool, t_bool, t_bool}));

  TermManager tm;
  ASSERT_THROW(
      d_tm.mkTerm(Kind::ITE, {d_tm.mkTrue(), tm.mkTrue(), tm.mkTrue()}),
      CVC5ApiException);
  ASSERT_THROW(
      d_tm.mkTerm(Kind::ITE, {tm.mkTrue(), d_tm.mkTrue(), tm.mkTrue()}),
      CVC5ApiException);
  ASSERT_THROW(
      d_tm.mkTerm(Kind::ITE, {tm.mkTrue(), tm.mkTrue(), d_tm.mkTrue()}),
      CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkTermFromOp)
{
  Sort bv32 = d_tm.mkBitVectorSort(32);
  Term a = d_tm.mkConst(bv32, "a");
  Term b = d_tm.mkConst(bv32, "b");
  std::vector<Term> v1 = {d_tm.mkInteger(1), d_tm.mkInteger(2)};
  std::vector<Term> v2 = {d_tm.mkInteger(1), Term()};
  std::vector<Term> v3 = {};
  std::vector<Term> v4 = {d_tm.mkInteger(5)};

  // simple operator terms
  Op opterm1 = d_tm.mkOp(Kind::BITVECTOR_EXTRACT, {2, 1});
  Op opterm2 = d_tm.mkOp(Kind::DIVISIBLE, {1});

  // list datatype
  Sort sort = d_tm.mkParamSort("T");
  DatatypeDecl listDecl = d_tm.mkDatatypeDecl("paramlist", {sort});
  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
  cons.addSelector("head", sort);
  cons.addSelectorSelf("tail");
  listDecl.addConstructor(cons);
  listDecl.addConstructor(nil);
  Sort listSort = d_tm.mkDatatypeSort(listDecl);
  Sort intListSort =
      listSort.instantiate(std::vector<Sort>{d_tm.getIntegerSort()});
  Term c = d_tm.mkConst(intListSort, "c");
  Datatype list = listSort.getDatatype();

  // list datatype constructor and selector operator terms
  Term consTerm = list.getConstructor("cons").getTerm();
  Term nilTerm = list.getConstructor("nil").getTerm();
  Term headTerm = list["cons"].getSelector("head").getTerm();
  Term tailTerm = list["cons"]["tail"].getTerm();

  // mkTerm(Op op, const std::vector<Term>& children) const
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::APPLY_CONSTRUCTOR, {nilTerm}));
  ASSERT_THROW(d_tm.mkTerm(Kind::APPLY_SELECTOR, {nilTerm}), CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(Kind::APPLY_SELECTOR, {consTerm}), CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(Kind::APPLY_CONSTRUCTOR, {consTerm}),
               CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(opterm1), CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(Kind::APPLY_SELECTOR, {headTerm}), CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(opterm1), CVC5ApiException);
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::APPLY_CONSTRUCTOR, {nilTerm}));

  ASSERT_NO_THROW(d_tm.mkTerm(opterm1, {a}));
  ASSERT_NO_THROW(d_tm.mkTerm(opterm2, {d_tm.mkInteger(1)}));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::APPLY_SELECTOR, {headTerm, c}));
  ASSERT_NO_THROW(d_tm.mkTerm(Kind::APPLY_SELECTOR, {tailTerm, c}));
  ASSERT_THROW(d_tm.mkTerm(opterm2, {a}), CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(opterm1, {Term()}), CVC5ApiException);
  ASSERT_THROW(
      d_tm.mkTerm(Kind::APPLY_CONSTRUCTOR, {consTerm, d_tm.mkInteger(0)}),
      CVC5ApiException);
  ASSERT_NO_THROW(d_tm.mkTerm(opterm1, {a}));

  ASSERT_NO_THROW(
      d_tm.mkTerm(Kind::APPLY_CONSTRUCTOR,
                  {consTerm,
                   d_tm.mkInteger(0),
                   d_tm.mkTerm(Kind::APPLY_CONSTRUCTOR, {nilTerm})}));
  ASSERT_THROW(d_tm.mkTerm(opterm2, {d_tm.mkInteger(1), d_tm.mkInteger(2)}),
               CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(opterm1, {a, b}), CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(opterm2, {d_tm.mkInteger(1), Term()}),
               CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(opterm2, {Term(), d_tm.mkInteger(1)}),
               CVC5ApiException);
  ASSERT_NO_THROW(
      d_tm.mkTerm(Kind::APPLY_CONSTRUCTOR,
                  {consTerm,
                   d_tm.mkInteger(0),
                   d_tm.mkTerm(Kind::APPLY_CONSTRUCTOR, {nilTerm})}));

  ASSERT_THROW(d_tm.mkTerm(opterm1, {a, b, a}), CVC5ApiException);
  ASSERT_THROW(
      d_tm.mkTerm(opterm2, {d_tm.mkInteger(1), d_tm.mkInteger(1), Term()}),
      CVC5ApiException);

  ASSERT_NO_THROW(d_tm.mkTerm(opterm2, {v4}));
  ASSERT_THROW(d_tm.mkTerm(opterm2, {v1}), CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(opterm2, {v2}), CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(opterm2, {v3}), CVC5ApiException);
  ASSERT_NO_THROW(d_tm.mkTerm(opterm2, {v4}));

  TermManager tm;
  ASSERT_THROW(tm.mkTerm(opterm2, {tm.mkInteger(1)}), CVC5ApiException);
  ASSERT_THROW(tm.mkTerm(tm.mkOp(Kind::DIVISIBLE, {1}), {d_tm.mkInteger(1)}),
               CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkTrue)
{
  ASSERT_NO_THROW(d_tm.mkTrue());
  ASSERT_NO_THROW(d_tm.mkTrue());
}

TEST_F(TestApiBlackTermManager, mkTuple)
{
  ASSERT_NO_THROW(d_tm.mkTuple({d_tm.mkBitVector(3, "101", 2)}));
  ASSERT_NO_THROW(d_tm.mkTuple({d_tm.mkInteger("5")}));
  ASSERT_NO_THROW(d_tm.mkTuple({d_tm.mkReal("5.3")}));
  ASSERT_NO_THROW(d_tm.mkTuple({d_tm.mkBitVector(3, "101", 2)}));
  ASSERT_NO_THROW(d_tm.mkTuple({d_tm.mkBitVector(3, "101", 2)}));

  TermManager tm;
  ASSERT_THROW(tm.mkTuple({d_tm.mkBitVector(3, "101", 2)}), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkNullableSome)
{
  ASSERT_NO_THROW(d_tm.mkNullableSome(d_tm.mkBitVector(3, "101", 2)));
  ASSERT_NO_THROW(d_tm.mkNullableSome(d_tm.mkInteger("5")));
  ASSERT_NO_THROW(d_tm.mkNullableSome(d_tm.mkReal("5.3")));
  ASSERT_NO_THROW(d_tm.mkNullableSome(d_tm.mkBitVector(3, "101", 2)));
  ASSERT_NO_THROW(d_tm.mkNullableSome(d_tm.mkBitVector(3, "101", 2)));

  TermManager tm;
  ASSERT_THROW(tm.mkNullableSome(d_tm.mkBitVector(3, "101", 2)),
               CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkNullableVal)
{
  Term value = d_tm.mkNullableVal(d_tm.mkNullableSome(d_tm.mkInteger(5)));
  value = d_solver->simplify(value);
  ASSERT_EQ(5, value.getInt32Value());

  TermManager tm;
  ASSERT_THROW(
      tm.mkNullableVal(d_tm.mkNullableSome(d_tm.mkBitVector(3, "101", 2))),
      CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkNullableIsNull)
{
  Term value = d_tm.mkNullableIsNull(d_tm.mkNullableSome(d_tm.mkInteger(5)));
  value = d_solver->simplify(value);
  ASSERT_EQ(false, value.getBooleanValue());

  TermManager tm;
  ASSERT_THROW(tm.mkNullableIsNull(d_tm.mkNullableSome(d_tm.mkInteger(5))),
               CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkNullableIsSome)
{
  Term value = d_tm.mkNullableIsSome(d_tm.mkNullableSome(d_tm.mkInteger(5)));
  value = d_solver->simplify(value);
  ASSERT_EQ(true, value.getBooleanValue());

  TermManager tm;
  ASSERT_THROW(tm.mkNullableIsSome(d_tm.mkNullableSome(d_tm.mkInteger(5))),
               CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkNullableNull)
{
  Sort nullableSort = d_tm.mkNullableSort(d_tm.getBooleanSort());
  Term nullableNull = d_tm.mkNullableNull(nullableSort);
  Term value = d_tm.mkNullableIsNull(nullableNull);
  value = d_solver->simplify(value);
  ASSERT_EQ(true, value.getBooleanValue());

  TermManager tm;
  ASSERT_THROW(tm.mkNullableIsNull(d_tm.mkNullableNull(
                   d_tm.mkNullableSort(d_tm.getBooleanSort()))),
               CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkNullableLift)
{
  Term some1 = d_tm.mkNullableSome(d_tm.mkInteger(1));
  Term some2 = d_tm.mkNullableSome(d_tm.mkInteger(2));
  Term some3 = d_tm.mkNullableLift(Kind::ADD, {some1, some2});
  Term three = d_solver->simplify(d_tm.mkNullableVal(some3));
  ASSERT_EQ(3, three.getInt32Value());

  TermManager tm;
  ASSERT_THROW(tm.mkNullableLift(Kind::ADD,
                                 {d_tm.mkNullableSome(d_tm.mkInteger(1)),
                                  d_tm.mkNullableSome(d_tm.mkInteger(2))}),
               CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkUniverseSet)
{
  ASSERT_NO_THROW(d_tm.mkUniverseSet(d_tm.getBooleanSort()));
  ASSERT_THROW(d_tm.mkUniverseSet(Sort()), CVC5ApiException);
  ASSERT_NO_THROW(d_tm.mkUniverseSet(d_tm.getBooleanSort()));

  TermManager tm;
  ASSERT_THROW(tm.mkUniverseSet(d_tm.getBooleanSort()), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkConst)
{
  Sort boolSort = d_tm.getBooleanSort();
  Sort intSort = d_tm.getIntegerSort();
  Sort funSort = d_tm.mkFunctionSort({intSort}, boolSort);
  ASSERT_NO_THROW(d_tm.mkConst(boolSort));
  ASSERT_NO_THROW(d_tm.mkConst(funSort));
  ASSERT_NO_THROW(d_tm.mkConst(boolSort, std::string("b")));
  ASSERT_NO_THROW(d_tm.mkConst(intSort, std::string("i")));
  ASSERT_NO_THROW(d_tm.mkConst(funSort, "f"));
  ASSERT_NO_THROW(d_tm.mkConst(funSort, ""));
  ASSERT_THROW(d_tm.mkConst(Sort()), CVC5ApiException);
  ASSERT_THROW(d_tm.mkConst(Sort(), "a"), CVC5ApiException);
  ASSERT_NO_THROW(d_tm.mkConst(boolSort));

  TermManager tm;
  ASSERT_THROW(tm.mkConst(boolSort), CVC5ApiException);
}

TEST_F(TestApiBlackTermManager, mkSkolem)
{
  Sort integer = d_tm.getIntegerSort();
  Sort arraySort = d_tm.mkArraySort(integer, integer);

  Term a = d_tm.mkConst(arraySort, "a");
  Term b = d_tm.mkConst(arraySort, "b");

  Term sk = d_tm.mkSkolem(SkolemId::ARRAY_DEQ_DIFF, {a, b});
  Term sk2 = d_tm.mkSkolem(SkolemId::ARRAY_DEQ_DIFF, {b, a});

  ASSERT_THROW(d_tm.mkSkolem(SkolemId::ARRAY_DEQ_DIFF, {a}), CVC5ApiException);

  ASSERT_TRUE(sk.isSkolem());
  ASSERT_EQ(sk.getSkolemId(), SkolemId::ARRAY_DEQ_DIFF);
  ASSERT_EQ(sk.getSkolemIndices(), std::vector<Term>({a, b}));
  // ARRAY_DEQ_DIFF is commutative, so the order of the indices is sorted.
  ASSERT_EQ(sk2.getSkolemIndices(), std::vector<Term>({a, b}));
}

TEST_F(TestApiBlackTermManager, getNumIndicesForSkolemId)
{
  size_t numIndices = d_tm.getNumIndicesForSkolemId(SkolemId::BAGS_MAP_INDEX);
  ASSERT_EQ(numIndices, 5);
}

TEST_F(TestApiBlackTermManager, uFIteration)
{
  Sort intSort = d_tm.getIntegerSort();
  Sort funSort = d_tm.mkFunctionSort({intSort, intSort}, intSort);
  Term x = d_tm.mkConst(intSort, "x");
  Term y = d_tm.mkConst(intSort, "y");
  Term f = d_tm.mkConst(funSort, "f");
  Term fxy = d_tm.mkTerm(Kind::APPLY_UF, {f, x, y});

  // Expecting the uninterpreted function to be one of the children
  Term expected_children[3] = {f, x, y};
  uint32_t idx = 0;
  for (auto c : fxy)
  {
    ASSERT_LT(idx, 3);
    ASSERT_EQ(c, expected_children[idx]);
    idx++;
  }
}

TEST_F(TestApiBlackTermManager, getStatistics)
{
  ASSERT_NO_THROW(cvc5::Stat());
  // do some array reasoning to make sure we have statistics
  {
    Sort s1 = d_tm.getIntegerSort();
    Sort s2 = d_tm.mkArraySort(s1, s1);
    Term t1 = d_tm.mkConst(s1, "i");
    Term t2 = d_tm.mkConst(s2, "a");
    Term t3 = d_tm.mkTerm(Kind::SELECT, {t2, t1});
    d_solver->assertFormula(t3.eqTerm(t1));
    d_solver->checkSat();
  }
  cvc5::Statistics stats = d_tm.getStatistics();
  {
    std::stringstream ss;
    ss << stats;
  }
  for (const auto& s : stats)
  {
    ASSERT_FALSE(s.first.empty());
  }
  for (auto it = stats.begin(true, true); it != stats.end(); ++it)
  {
    {
      auto tmp1 = it, tmp2 = it;
      ++tmp1;
      tmp2++;
      ASSERT_EQ(tmp1, tmp2);
      --tmp1;
      tmp2--;
      ASSERT_EQ(tmp1, tmp2);
      ASSERT_EQ(tmp1, it);
      ASSERT_EQ(it, tmp2);
    }
    const auto& s = *it;
    // check some basic utility methods
    ASSERT_TRUE(!(it == stats.end()));
    ASSERT_EQ(s.first, it->first);
    if (s.first == "cvc5::CONSTANT")
    {
      ASSERT_FALSE(s.second.isInternal());
      ASSERT_FALSE(s.second.isDefault());
      ASSERT_TRUE(s.second.isHistogram());
      auto hist = s.second.getHistogram();
      ASSERT_FALSE(hist.empty());
      std::stringstream ss;
      ss << s.second;
      ASSERT_EQ(ss.str(), "{ UNKNOWN_TYPE_CONSTANT: 1, integer type: 1 }");
    }
    else if (s.first == "theory::arrays::avgIndexListLength")
    {
      ASSERT_TRUE(s.second.isInternal());
      ASSERT_TRUE(s.second.isDouble());
      ASSERT_TRUE(std::isnan(s.second.getDouble()));
    }
  }
}

TEST_F(TestApiBlackTermManager, printStatisticsSafe)
{
  // do some array reasoning to make sure we have statistics
  {
    Sort s1 = d_tm.getIntegerSort();
    Sort s2 = d_tm.mkArraySort(s1, s1);
    Term t1 = d_tm.mkConst(s1, "i");
    Term t2 = d_tm.mkConst(s2, "a");
    Term t3 = d_tm.mkTerm(Kind::SELECT, {t2, t1});
    d_solver->assertFormula(t3.eqTerm(t1));
    d_solver->checkSat();
  }
  testing::internal::CaptureStdout();
  d_tm.printStatisticsSafe(STDOUT_FILENO);
  std::string out = testing::internal::GetCapturedStdout();
  std::stringstream expected;
  expected << "cvc5::CONSTANT = { integer type: 1, UNKNOWN_TYPE_CONSTANT: 1 }"
           << std::endl
           << "cvc5::TERM = { <unsupported>: 1 }" << std::endl;
  ASSERT_EQ(out, expected.str());
}

}  // namespace cvc5::internal::test
