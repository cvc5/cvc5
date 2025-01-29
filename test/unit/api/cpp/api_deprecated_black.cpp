/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * These tests are purely for the purpose of covering deprecated API functions
 * for the nightly API coverage builds.
 */

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestApiDeprecated : public ::testing::Test
{
};

TEST_F(TestApiDeprecated, kindToString)
{
  for (int32_t k = static_cast<int32_t>(Kind::INTERNAL_KIND);
       k < static_cast<int32_t>(Kind::LAST_KIND);
       ++k)
  {
    ASSERT_EQ(kindToString(static_cast<Kind>(k)),
              std::to_string(static_cast<Kind>(k)));
  }
}

TEST_F(TestApiDeprecated, sortKindToString)
{
  for (int32_t k = static_cast<int32_t>(SortKind::INTERNAL_SORT_KIND);
       k < static_cast<int32_t>(SortKind::LAST_SORT_KIND);
       ++k)
  {
    ASSERT_EQ(sortKindToString(static_cast<SortKind>(k)),
              std::to_string(static_cast<SortKind>(k)));
  }
}

TEST_F(TestApiDeprecated, solver)
{
  Solver slv;
  (void)slv.getBooleanSort();
  (void)slv.getIntegerSort();
  (void)slv.getRealSort();
  (void)slv.getRegExpSort();
  (void)slv.getRoundingModeSort();
  (void)slv.getStringSort();
  (void)slv.mkArraySort(slv.getBooleanSort(), slv.getIntegerSort());
  (void)slv.mkBitVectorSort(32);
  (void)slv.mkFloatingPointSort(5, 11);
  (void)slv.mkFiniteFieldSort("37");

  {
    DatatypeDecl decl = slv.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = slv.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", slv.getIntegerSort());
    decl.addConstructor(cons);
    decl.addConstructor(slv.mkDatatypeConstructorDecl("nil"));
    (void)slv.mkDatatypeSort(decl);
  }
  {
    DatatypeDecl decl1 = slv.mkDatatypeDecl("list1");
    DatatypeConstructorDecl cons1 = slv.mkDatatypeConstructorDecl("cons1");
    cons1.addSelector("head1", slv.getIntegerSort());
    decl1.addConstructor(cons1);
    DatatypeConstructorDecl nil1 = slv.mkDatatypeConstructorDecl("nil1");
    decl1.addConstructor(nil1);
    DatatypeDecl decl2 = slv.mkDatatypeDecl("list2");
    DatatypeConstructorDecl cons2 = slv.mkDatatypeConstructorDecl("cons2");
    cons2.addSelector("head2", slv.getIntegerSort());
    decl2.addConstructor(cons2);
    DatatypeConstructorDecl nil2 = slv.mkDatatypeConstructorDecl("nil2");
    decl2.addConstructor(nil2);
    std::vector<DatatypeDecl> decls = {decl1, decl2};
    ASSERT_NO_THROW(slv.mkDatatypeSorts(decls));
  }

  (void)slv.mkFunctionSort({slv.mkUninterpretedSort("u")},
                           slv.getIntegerSort());
  (void)slv.mkParamSort("T");
  (void)slv.mkPredicateSort({slv.getIntegerSort()});

  (void)slv.mkRecordSort({std::make_pair("b", slv.getBooleanSort()),
                          std::make_pair("bv", slv.mkBitVectorSort(8)),
                          std::make_pair("i", slv.getIntegerSort())});
  (void)slv.mkSetSort(slv.getBooleanSort());
  (void)slv.mkBagSort(slv.getBooleanSort());
  (void)slv.mkSequenceSort(slv.getBooleanSort());
  (void)slv.mkAbstractSort(SortKind::ARRAY_SORT);
  (void)slv.mkUninterpretedSort("u");
  (void)slv.mkUnresolvedDatatypeSort("u");
  (void)slv.mkUninterpretedSortConstructorSort(2, "s");
  (void)slv.mkTupleSort({slv.getIntegerSort()});
  (void)slv.mkNullableSort({slv.getIntegerSort()});
  (void)slv.mkTerm(Kind::STRING_IN_REGEXP,
                   {slv.mkConst(slv.getStringSort(), "s"), slv.mkRegexpAll()});
  (void)slv.mkTerm(slv.mkOp(Kind::REGEXP_ALLCHAR));
  (void)slv.mkTuple({slv.mkBitVector(3, "101", 2)});
  (void)slv.mkNullableSome(slv.mkBitVector(3, "101", 2));
  (void)slv.mkNullableVal(slv.mkNullableSome(slv.mkInteger(5)));
  (void)slv.mkNullableNull(slv.mkNullableSort(slv.getBooleanSort()));
  (void)slv.mkNullableIsNull(slv.mkNullableSome(slv.mkInteger(5)));
  (void)slv.mkNullableIsSome(slv.mkNullableSome(slv.mkInteger(5)));
  (void)slv.mkNullableSort(slv.getBooleanSort());
  (void)slv.mkNullableLift(Kind::ADD,
                           {slv.mkNullableSome(slv.mkInteger(1)),
                            slv.mkNullableSome(slv.mkInteger(2))});
  (void)slv.mkOp(Kind::DIVISIBLE, "2147483648");
  (void)slv.mkOp(Kind::TUPLE_PROJECT, {1, 2, 2});

  (void)slv.mkTrue();
  (void)slv.mkFalse();
  (void)slv.mkBoolean(true);
  (void)slv.mkPi();
  (void)slv.mkInteger("2");
  (void)slv.mkInteger(2);
  (void)slv.mkReal("2.1");
  (void)slv.mkReal(2);
  (void)slv.mkReal(2, 3);
  (void)slv.mkRegexpAll();
  (void)slv.mkRegexpAllchar();
  (void)slv.mkRegexpNone();
  (void)slv.mkEmptySet(slv.mkSetSort(slv.getIntegerSort()));
  (void)slv.mkEmptyBag(slv.mkBagSort(slv.getIntegerSort()));
  (void)slv.mkSepEmp();
  (void)slv.mkSepNil(slv.getIntegerSort());
  (void)slv.mkString("asdfasdf");
  std::wstring s;
  (void)slv.mkString(s);
  (void)slv.mkEmptySequence(slv.getIntegerSort());
  (void)slv.mkUniverseSet(slv.getIntegerSort());
  (void)slv.mkBitVector(32, 2);
  (void)slv.mkBitVector(32, "2", 10);
  (void)slv.mkFiniteFieldElem("0", slv.mkFiniteFieldSort("7"));
  (void)slv.mkConstArray(
      slv.mkArraySort(slv.getIntegerSort(), slv.getIntegerSort()),
      slv.mkInteger(2));
  (void)slv.mkFloatingPointPosInf(5, 11);
  (void)slv.mkFloatingPointNegInf(5, 11);
  (void)slv.mkFloatingPointNaN(5, 11);
  (void)slv.mkFloatingPointPosZero(5, 11);
  (void)slv.mkFloatingPointNegZero(5, 11);
  (void)slv.mkRoundingMode(RoundingMode::ROUND_NEAREST_TIES_TO_EVEN);
  (void)slv.mkFloatingPoint(5, 11, slv.mkBitVector(16));
  (void)slv.mkFloatingPoint(
      slv.mkBitVector(1), slv.mkBitVector(5), slv.mkBitVector(10));
  (void)slv.mkCardinalityConstraint(slv.mkUninterpretedSort("u"), 3);

  (void)slv.mkVar(slv.getIntegerSort());
  (void)slv.mkDatatypeDecl("paramlist", {slv.mkParamSort("T")});
  (void)parser::SymbolManager(&slv);
}

}  // namespace cvc5::internal::test
