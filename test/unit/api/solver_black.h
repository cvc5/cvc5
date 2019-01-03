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

  void testGetBooleanSort();
  void testGetIntegerSort();
  void testGetRealSort();
  void testGetRegExpSort();
  void testGetStringSort();
  void testGetRoundingmodeSort();

  void testMkArraySort();
  void testMkBitVectorSort();
  void testMkFloatingPointSort();
  void testMkDatatypeSort();
  void testMkFunctionSort();
  void testMkOpTerm();
  void testMkParamSort();
  void testMkPredicateSort();
  void testMkRecordSort();
  void testMkSetSort();
  void testMkSortConstructorSort();
  void testMkTupleSort();
  void testMkUninterpretedSort();

  void testMkBitVector();
  void testMkBoundVar();
  void testMkBoolean();
  void testMkConst();
  void testMkEmptySet();
  void testMkFalse();
  void testMkPi();
  void testMkReal();
  void testMkRegexpEmpty();
  void testMkRegexpSigma();
  void testMkSepNil();
  void testMkString();
  void testMkUniverseSet();
  void testMkTerm();
  void testMkTrue();
  void testMkVar();

  void testDeclareFun();
  void testDefineFun();
  void testDefineFunRec();
  void testDefineFunsRec();

 private:
  Solver d_solver;
};

void SolverBlack::setUp() {}

void SolverBlack::tearDown() {}

void SolverBlack::testGetBooleanSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.getBooleanSort());
}

void SolverBlack::testGetIntegerSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.getIntegerSort());
}

void SolverBlack::testGetRealSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.getRealSort());
}

void SolverBlack::testGetRegExpSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.getRegExpSort());
}

void SolverBlack::testGetStringSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.getStringSort());
}

void SolverBlack::testGetRoundingmodeSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.getRoundingmodeSort());
}

void SolverBlack::testMkArraySort()
{
  Sort boolSort = d_solver.getBooleanSort();
  Sort intSort = d_solver.getIntegerSort();
  Sort realSort = d_solver.getRealSort();
  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort fpSort = d_solver.mkFloatingPointSort(3, 5);
  TS_ASSERT_THROWS_NOTHING(d_solver.mkArraySort(boolSort, boolSort));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkArraySort(intSort, intSort));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkArraySort(realSort, realSort));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkArraySort(bvSort, bvSort));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkArraySort(fpSort, fpSort));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkArraySort(boolSort, intSort));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkArraySort(realSort, bvSort));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkArraySort(bvSort, fpSort));
}

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

void SolverBlack::testMkParamSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkParamSort("T"));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkParamSort(""));
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

void SolverBlack::testMkRecordSort()
{
  std::vector<std::pair<std::string, Sort>> fields = {
      std::make_pair("b", d_solver.getBooleanSort()),
      std::make_pair("bv", d_solver.mkBitVectorSort(8)),
      std::make_pair("i", d_solver.getIntegerSort())};
  std::vector<std::pair<std::string, Sort>> empty;
  TS_ASSERT_THROWS_NOTHING(d_solver.mkRecordSort(fields));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkRecordSort(empty));
}

void SolverBlack::testMkSetSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkSetSort(d_solver.getBooleanSort()));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkSetSort(d_solver.getIntegerSort()));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkSetSort(d_solver.mkBitVectorSort(4)));
}

void SolverBlack::testMkUninterpretedSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkUninterpretedSort("u"));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkUninterpretedSort(""));
}

void SolverBlack::testMkSortConstructorSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkSortConstructorSort("s", 2));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkSortConstructorSort("", 2));
  TS_ASSERT_THROWS(d_solver.mkSortConstructorSort("", 0), CVC4ApiException&);
}

void SolverBlack::testMkTupleSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkTupleSort({d_solver.getIntegerSort()}));
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  TS_ASSERT_THROWS(d_solver.mkTupleSort({d_solver.getIntegerSort(), funSort}),
                   CVC4ApiException&);
}

void SolverBlack::testMkBitVector()
{
  uint32_t size0 = 0, size1 = 8, size2 = 32, val1 = 2;
  uint64_t val2 = 2;
  TS_ASSERT_THROWS(d_solver.mkBitVector(size0, val1), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkBitVector(size0, val2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkBitVector("", 2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkBitVector("10", 3), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkBitVector("20", 2), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(d_solver.mkBitVector(size1, val1));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkBitVector(size2, val2));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkBitVector("1010", 2));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkBitVector("1010", 16));
}

void SolverBlack::testMkBoundVar()
{
  Sort boolSort = d_solver.getBooleanSort();
  Sort intSort = d_solver.getIntegerSort();
  Sort funSort = d_solver.mkFunctionSort(intSort, boolSort);
  TS_ASSERT_THROWS(d_solver.mkBoundVar(Sort()), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(d_solver.mkBoundVar(boolSort));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkBoundVar(funSort));
  TS_ASSERT_THROWS(d_solver.mkBoundVar("a", Sort()), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(d_solver.mkBoundVar(std::string("b"), boolSort));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkBoundVar("", funSort));
}

void SolverBlack::testMkBoolean()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkBoolean(true));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkBoolean(false));
}

void SolverBlack::testMkConst()
{
  // mkConst(RoundingMode rm) const
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(RoundingMode::ROUND_TOWARD_ZERO));

  // mkConst(Kind kind, Sort arg) const
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(EMPTYSET, Sort()));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(UNIVERSE_SET, d_solver.mkSetSort(d_solver.getBooleanSort())));
  TS_ASSERT_THROWS(d_solver.mkConst(EMPTYSET, d_solver.getBooleanSort()),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkTerm(UNIVERSE_SET, Sort()), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(APPLY, d_solver.getBooleanSort()),
                   CVC4ApiException&);

  // mkConst(Kind kind, Sort arg1, int32_t arg2) const
  TS_ASSERT_THROWS_NOTHING(
      d_solver.mkConst(UNINTERPRETED_CONSTANT, d_solver.getBooleanSort(), 1));
  TS_ASSERT_THROWS(d_solver.mkConst(UNINTERPRETED_CONSTANT, Sort(), 1),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(EMPTYSET, d_solver.getBooleanSort(), 1),
                   CVC4ApiException&);

  // mkConst(Kind kind, bool arg) const
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(CONST_BOOLEAN, true));
  TS_ASSERT_THROWS(d_solver.mkConst(UNINTERPRETED_CONSTANT, true),
                   CVC4ApiException&);

  // mkConst(Kind kind, const char* arg) const
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(ABSTRACT_VALUE, std::string("1")));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(CONST_STRING, "asdf"));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(CONST_RATIONAL, "1"));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(CONST_RATIONAL, "1/2"));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(CONST_RATIONAL, "1.2"));
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_STRING, nullptr), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_STRING, ""), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(ABSTRACT_VALUE, std::string("1.2")),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(ABSTRACT_VALUE, "1/2"), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(ABSTRACT_VALUE, "asdf"), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_RATIONAL, "1..2"), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_RATIONAL, "asdf"), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(BITVECTOR_ULT, "asdf"), CVC4ApiException&);

  // mkConst(Kind kind, const std::string& arg) const
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(CONST_STRING, std::string("asdf")));
  TS_ASSERT_THROWS_NOTHING(
      d_solver.mkConst(CONST_RATIONAL, std::string("1/2")));
  TS_ASSERT_THROWS_NOTHING(
      d_solver.mkConst(CONST_RATIONAL, std::string("1.2")));
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_STRING, nullptr), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_STRING, std::string("")),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_RATIONAL, std::string("asdf")),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(BITVECTOR_ULT, std::string("asdf")),
                   CVC4ApiException&);

  // mkConst(Kind kind, const char* arg1, uint32_t arg2) const
  TS_ASSERT_THROWS_NOTHING(
      d_solver.mkConst(CONST_BITVECTOR, std::string("101"), 2));
  TS_ASSERT_THROWS_NOTHING(
      d_solver.mkConst(CONST_BITVECTOR, std::string("10a"), 16));
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_BITVECTOR, nullptr, 1),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_BITVECTOR, std::string("")),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_BITVECTOR, std::string("101", 6)),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_BITVECTOR, std::string("102", 16)),
                   CVC4ApiException&);

  // mkConst(Kind kind, int32_t arg) const
  // mkConst(Kind kind, uint32_t arg) const
  // mkConst(Kind kind, int64_t arg) const
  // mkConst(Kind kind, uint64_t arg) const
  int32_t val1 = 2;
  uint32_t val2 = 2;
  int64_t val3 = 2;
  uint64_t val4 = 2;
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(ABSTRACT_VALUE, val1));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(ABSTRACT_VALUE, val2));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(ABSTRACT_VALUE, val3));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(ABSTRACT_VALUE, val4));
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_BITVECTOR, val1), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_BITVECTOR, val2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_BITVECTOR, val3), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_BITVECTOR, val4), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(CONST_RATIONAL, val1));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(CONST_RATIONAL, val2));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(CONST_RATIONAL, val3));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(CONST_RATIONAL, val4));

  // mkConst(Kind kind, int32_t arg1, int32_t arg2) const
  // mkConst(Kind kind, uint32_t arg1, uint32_t arg2) const
  // mkConst(Kind kind, int64_t arg1, int64_t arg2) const
  // mkConst(Kind kind, uint64_t arg1, uint64_t arg2) const
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(CONST_RATIONAL, val1, val1));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(CONST_RATIONAL, val2, val2));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(CONST_RATIONAL, val3, val3));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(CONST_RATIONAL, val4, val4));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(CONST_BITVECTOR, val2, val2));

  // mkConst(Kind kind, uint32_t arg1, uint32_t arg2, Term arg3) const
#ifdef CVC4_USE_SYMFPU
  Term t1 = d_solver.mkBitVector(8);
  Term t2 = d_solver.mkBitVector(4);
  Term t3 = d_solver.mkReal(2);
  TS_ASSERT_THROWS_NOTHING(d_solver.mkConst(CONST_FLOATINGPOINT, 3, 5, t1));
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_FLOATINGPOINT, 0, 5, Term()),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_FLOATINGPOINT, 0, 5, t1),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_FLOATINGPOINT, 3, 0, t1),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_FLOATINGPOINT, 3, 5, t2),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_FLOATINGPOINT, 3, 5, t2),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkConst(CONST_BITVECTOR, 3, 5, t1),
                   CVC4ApiException&);
#endif
}

void SolverBlack::testMkEmptySet()
{
  TS_ASSERT_THROWS(d_solver.mkEmptySet(d_solver.getBooleanSort()),
                   CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(d_solver.mkEmptySet(Sort()));
}

void SolverBlack::testMkFalse()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkFalse());
  TS_ASSERT_THROWS_NOTHING(d_solver.mkFalse());
}

void SolverBlack::testMkOpTerm()
{
  // mkOpTerm(Kind kind, Kind k)
  TS_ASSERT_THROWS_NOTHING(d_solver.mkOpTerm(CHAIN_OP, EQUAL));
  TS_ASSERT_THROWS(d_solver.mkOpTerm(BITVECTOR_EXTRACT_OP, EQUAL),
                   CVC4ApiException&);

  // mkOpTerm(Kind kind, const std::string& arg)
  TS_ASSERT_THROWS_NOTHING(d_solver.mkOpTerm(RECORD_UPDATE_OP, "asdf"));
  TS_ASSERT_THROWS(d_solver.mkOpTerm(BITVECTOR_EXTRACT_OP, "asdf"),
                   CVC4ApiException&);

  // mkOpTerm(Kind kind, uint32_t arg)
  TS_ASSERT_THROWS_NOTHING(d_solver.mkOpTerm(DIVISIBLE_OP, 1));
  TS_ASSERT_THROWS(d_solver.mkOpTerm(BITVECTOR_EXTRACT_OP, 1),
                   CVC4ApiException&);

  // mkOpTerm(Kind kind, uint32_t arg1, uint32_t arg2)
  TS_ASSERT_THROWS_NOTHING(d_solver.mkOpTerm(BITVECTOR_EXTRACT_OP, 1, 1));
  TS_ASSERT_THROWS(d_solver.mkOpTerm(DIVISIBLE_OP, 1, 2), CVC4ApiException&);
}

void SolverBlack::testMkPi() { TS_ASSERT_THROWS_NOTHING(d_solver.mkPi()); }

void SolverBlack::testMkReal()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal("123"));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal("1.23"));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal("1/23"));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal("12/3"));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal(".2"));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal("2."));
  TS_ASSERT_THROWS(d_solver.mkReal(nullptr), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkReal(""), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkReal("asdf"), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkReal("1.2/3"), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkReal("."), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkReal("/"), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkReal("2/"), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkReal("/2"), CVC4ApiException&);

  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal(std::string("123")));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal(std::string("1.23")));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal(std::string("1/23")));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal(std::string("12/3")));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal(std::string(".2")));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal(std::string("2.")));
  TS_ASSERT_THROWS(d_solver.mkReal(std::string("")), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkReal(std::string("asdf")), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkReal(std::string("1.2/3")), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkReal(std::string(".")), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkReal(std::string("/")), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkReal(std::string("2/")), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkReal(std::string("/2")), CVC4ApiException&);

  int32_t val1 = 1;
  int64_t val2 = -1;
  uint32_t val3 = 1;
  uint64_t val4 = -1;
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal(val1));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal(val2));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal(val3));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal(val4));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal(val4));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal(val1, val1));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal(val2, val2));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal(val3, val3));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkReal(val4, val4));
}

void SolverBlack::testMkRegexpEmpty()
{
  Sort strSort = d_solver.getStringSort();
  Term s = d_solver.mkVar("s", strSort);
  TS_ASSERT_THROWS_NOTHING(
      d_solver.mkTerm(STRING_IN_REGEXP, s, d_solver.mkRegexpEmpty()));
}

void SolverBlack::testMkRegexpSigma()
{
  Sort strSort = d_solver.getStringSort();
  Term s = d_solver.mkVar("s", strSort);
  TS_ASSERT_THROWS_NOTHING(
      d_solver.mkTerm(STRING_IN_REGEXP, s, d_solver.mkRegexpSigma()));
}

void SolverBlack::testMkSepNil()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkSepNil(d_solver.getBooleanSort()));
  TS_ASSERT_THROWS(d_solver.mkSepNil(Sort()), CVC4ApiException&);
}

void SolverBlack::testMkString()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkString(""));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkString("asdfasdf"));
}

void SolverBlack::testMkTerm()
{
  Sort bv32 = d_solver.mkBitVectorSort(32);
  Term a = d_solver.mkVar("a", bv32);
  Term b = d_solver.mkVar("b", bv32);
  std::vector<Term> v1 = {a, b};
  std::vector<Term> v2 = {a, Term()};
  std::vector<Term> v3 = {a, d_solver.mkTrue()};
  std::vector<Term> v4 = {d_solver.mkReal(1), d_solver.mkReal(2)};
  std::vector<Term> v5 = {d_solver.mkReal(1), Term()};
  OpTerm opterm1 = d_solver.mkOpTerm(BITVECTOR_EXTRACT_OP, 2, 1);
  OpTerm opterm2 = d_solver.mkOpTerm(DIVISIBLE_OP, 1);
  OpTerm opterm3 = d_solver.mkOpTerm(CHAIN_OP, EQUAL);

  // mkTerm(Kind kind) const
  TS_ASSERT_THROWS_NOTHING(d_solver.mkTerm(PI));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkTerm(REGEXP_EMPTY));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkTerm(REGEXP_SIGMA));
  TS_ASSERT_THROWS(d_solver.mkTerm(CONST_BITVECTOR), CVC4ApiException&);

  // mkTerm(Kind kind, Sort sort) const
  TS_ASSERT_THROWS_NOTHING(d_solver.mkTerm(SEP_NIL, d_solver.getBooleanSort()));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkTerm(SEP_NIL, Sort()));

  // mkTerm(Kind kind, Term child) const
  TS_ASSERT_THROWS_NOTHING(d_solver.mkTerm(NOT, d_solver.mkTrue()));
  TS_ASSERT_THROWS(d_solver.mkTerm(NOT, Term()), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkTerm(NOT, a), CVC4ApiException&);

  // mkTerm(Kind kind, Term child1, Term child2) const
  TS_ASSERT_THROWS_NOTHING(d_solver.mkTerm(EQUAL, a, b));
  TS_ASSERT_THROWS(d_solver.mkTerm(EQUAL, Term(), b), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkTerm(EQUAL, a, Term()), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkTerm(EQUAL, a, d_solver.mkTrue()),
                   CVC4ApiException&);

  // mkTerm(Kind kind, Term child1, Term child2, Term child3) const
  TS_ASSERT_THROWS_NOTHING(d_solver.mkTerm(
      ITE, d_solver.mkTrue(), d_solver.mkTrue(), d_solver.mkTrue()));
  TS_ASSERT_THROWS(
      d_solver.mkTerm(ITE, Term(), d_solver.mkTrue(), d_solver.mkTrue()),
      CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver.mkTerm(ITE, d_solver.mkTrue(), Term(), d_solver.mkTrue()),
      CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver.mkTerm(ITE, d_solver.mkTrue(), d_solver.mkTrue(), Term()),
      CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver.mkTerm(ITE, d_solver.mkTrue(), d_solver.mkTrue(), b),
      CVC4ApiException&);

  // mkTerm(Kind kind, const std::vector<Term>& children) const
  TS_ASSERT_THROWS_NOTHING(d_solver.mkTerm(EQUAL, v1));
  TS_ASSERT_THROWS(d_solver.mkTerm(EQUAL, v2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkTerm(EQUAL, v3), CVC4ApiException&);

  // mkTerm(OpTerm opTerm, Term child) const
  TS_ASSERT_THROWS_NOTHING(d_solver.mkTerm(opterm1, a));
  TS_ASSERT_THROWS(d_solver.mkTerm(opterm2, a), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkTerm(opterm1, Term()), CVC4ApiException&);

  // mkTerm(OpTerm opTerm, Term child1, Term child2) const
  TS_ASSERT_THROWS_NOTHING(
      d_solver.mkTerm(opterm3, d_solver.mkReal(1), d_solver.mkReal(2)));
  TS_ASSERT_THROWS(d_solver.mkTerm(opterm1, a, b), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkTerm(opterm3, d_solver.mkReal(1), Term()),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkTerm(opterm3, Term(), d_solver.mkReal(1)),
                   CVC4ApiException&);

  // mkTerm(OpTerm opTerm, Term child1, Term child2, Term child3) const
  TS_ASSERT_THROWS_NOTHING(d_solver.mkTerm(
      opterm3, d_solver.mkReal(1), d_solver.mkReal(1), d_solver.mkReal(2)));
  TS_ASSERT_THROWS(d_solver.mkTerm(opterm1, a, b, a), CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver.mkTerm(opterm3, d_solver.mkReal(1), d_solver.mkReal(1), Term()),
      CVC4ApiException&);

  // mkTerm(OpTerm opTerm, const std::vector<Term>& children) const
  TS_ASSERT_THROWS_NOTHING(d_solver.mkTerm(opterm3, v4));
  TS_ASSERT_THROWS(d_solver.mkTerm(opterm3, v5), CVC4ApiException&);
}

void SolverBlack::testMkTrue()
{
  TS_ASSERT_THROWS_NOTHING(d_solver.mkTrue());
  TS_ASSERT_THROWS_NOTHING(d_solver.mkTrue());
}

void SolverBlack::testMkUniverseSet()
{
  TS_ASSERT_THROWS(d_solver.mkUniverseSet(Sort()), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver.mkUniverseSet(d_solver.getBooleanSort()), CVC4ApiException&);
}

void SolverBlack::testMkVar()
{
  Sort boolSort = d_solver.getBooleanSort();
  Sort intSort = d_solver.getIntegerSort();
  Sort funSort = d_solver.mkFunctionSort(intSort, boolSort);
  TS_ASSERT_THROWS(d_solver.mkVar(Sort()), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(d_solver.mkVar(boolSort));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkVar(funSort));
  TS_ASSERT_THROWS(d_solver.mkVar("a", Sort()), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(d_solver.mkVar(std::string("b"), boolSort));
  TS_ASSERT_THROWS_NOTHING(d_solver.mkVar("", funSort));
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
