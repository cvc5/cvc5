/*********************                                                        */
/*! \file solver_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the Solver class of the  C++ API.
 **
 ** Black box testing of the Solver class of the  C++ API.
 **/

#include <cxxtest/TestSuite.h>

#include "api/cvc4cpp.h"
#include "base/configuration.h"

using namespace CVC4::api;

class SolverBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override;
  void tearDown() override;

  void testGetBooleanSort();
  void testGetIntegerSort();
  void testGetNullSort();
  void testGetRealSort();
  void testGetRegExpSort();
  void testGetRoundingmodeSort();
  void testGetStringSort();

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

  void testMkAbstractValue();
  void testMkBitVector();
  void testMkBoolean();
  void testMkBoundVar();
  void testMkEmptySet();
  void testMkFalse();
  void testMkFloatingPoint();
  void testMkNaN();
  void testMkNegInf();
  void testMkNegZero();
  void testMkPi();
  void testMkPosInf();
  void testMkPosZero();
  void testMkReal();
  void testMkRegexpEmpty();
  void testMkRegexpSigma();
  void testMkRoundingMode();
  void testMkSepNil();
  void testMkString();
  void testMkTerm();
  void testMkTermFromOpTerm();
  void testMkTrue();
  void testMkTuple();
  void testMkUninterpretedConst();
  void testMkUniverseSet();
  void testMkVar();

  void testDeclareDatatype();
  void testDeclareFun();
  void testDeclareSort();

  void testDefineFun();
  void testDefineFunRec();
  void testDefineFunsRec();

  void testSetInfo();
  void testSetLogic();
  void testSetOption();

 private:
  std::unique_ptr<Solver> d_solver;
};

void SolverBlack::setUp() { d_solver.reset(new Solver()); }

void SolverBlack::tearDown() {}

void SolverBlack::testGetBooleanSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->getBooleanSort());
}

void SolverBlack::testGetIntegerSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->getIntegerSort());
}

void SolverBlack::testGetNullSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->getNullSort());
}

void SolverBlack::testGetRealSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->getRealSort());
}

void SolverBlack::testGetRegExpSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->getRegExpSort());
}

void SolverBlack::testGetStringSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->getStringSort());
}

void SolverBlack::testGetRoundingmodeSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->getRoundingmodeSort());
}

void SolverBlack::testMkArraySort()
{
  Sort boolSort = d_solver->getBooleanSort();
  Sort intSort = d_solver->getIntegerSort();
  Sort realSort = d_solver->getRealSort();
  Sort bvSort = d_solver->mkBitVectorSort(32);
  Sort fpSort = d_solver->mkFloatingPointSort(3, 5);
  TS_ASSERT_THROWS_NOTHING(d_solver->mkArraySort(boolSort, boolSort));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkArraySort(intSort, intSort));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkArraySort(realSort, realSort));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkArraySort(bvSort, bvSort));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkArraySort(fpSort, fpSort));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkArraySort(boolSort, intSort));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkArraySort(realSort, bvSort));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkArraySort(bvSort, fpSort));
}

void SolverBlack::testMkBitVectorSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->mkBitVectorSort(32));
  TS_ASSERT_THROWS(d_solver->mkBitVectorSort(0), CVC4ApiException&);
}

void SolverBlack::testMkFloatingPointSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->mkFloatingPointSort(4, 8));
  TS_ASSERT_THROWS(d_solver->mkFloatingPointSort(0, 8), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkFloatingPointSort(4, 0), CVC4ApiException&);
}

void SolverBlack::testMkDatatypeSort()
{
  DatatypeDecl dtypeSpec("list");
  DatatypeConstructorDecl cons("cons");
  DatatypeSelectorDecl head("head", d_solver->getIntegerSort());
  cons.addSelector(head);
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil("nil");
  dtypeSpec.addConstructor(nil);
  TS_ASSERT_THROWS_NOTHING(d_solver->mkDatatypeSort(dtypeSpec));
  DatatypeDecl throwsDtypeSpec("list");
  TS_ASSERT_THROWS(d_solver->mkDatatypeSort(throwsDtypeSpec),
                   CVC4ApiException&);
}

void SolverBlack::testMkFunctionSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->mkFunctionSort(
      d_solver->mkUninterpretedSort("u"), d_solver->getIntegerSort()));
  Sort funSort = d_solver->mkFunctionSort(d_solver->mkUninterpretedSort("u"),
                                          d_solver->getIntegerSort());
  TS_ASSERT_THROWS(
      d_solver->mkFunctionSort(funSort, d_solver->getIntegerSort()),
      CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver->mkFunctionSort(d_solver->getIntegerSort(), funSort),
      CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(d_solver->mkFunctionSort(
      {d_solver->mkUninterpretedSort("u"), d_solver->getIntegerSort()},
      d_solver->getIntegerSort()));
  Sort funSort2 = d_solver->mkFunctionSort(d_solver->mkUninterpretedSort("u"),
                                           d_solver->getIntegerSort());
  TS_ASSERT_THROWS(
      d_solver->mkFunctionSort({funSort2, d_solver->mkUninterpretedSort("u")},
                               d_solver->getIntegerSort()),
      CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver->mkFunctionSort(
          {d_solver->getIntegerSort(), d_solver->mkUninterpretedSort("u")},
          funSort2),
      CVC4ApiException&);
}

void SolverBlack::testMkParamSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->mkParamSort("T"));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkParamSort(""));
}

void SolverBlack::testMkPredicateSort()
{
  TS_ASSERT_THROWS_NOTHING(
      d_solver->mkPredicateSort({d_solver->getIntegerSort()}));
  TS_ASSERT_THROWS(d_solver->mkPredicateSort({}), CVC4ApiException&);
  Sort funSort = d_solver->mkFunctionSort(d_solver->mkUninterpretedSort("u"),
                                          d_solver->getIntegerSort());
  TS_ASSERT_THROWS(
      d_solver->mkPredicateSort({d_solver->getIntegerSort(), funSort}),
      CVC4ApiException&);
}

void SolverBlack::testMkRecordSort()
{
  std::vector<std::pair<std::string, Sort>> fields = {
      std::make_pair("b", d_solver->getBooleanSort()),
      std::make_pair("bv", d_solver->mkBitVectorSort(8)),
      std::make_pair("i", d_solver->getIntegerSort())};
  std::vector<std::pair<std::string, Sort>> empty;
  TS_ASSERT_THROWS_NOTHING(d_solver->mkRecordSort(fields));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkRecordSort(empty));
}

void SolverBlack::testMkSetSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->mkSetSort(d_solver->getBooleanSort()));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkSetSort(d_solver->getIntegerSort()));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkSetSort(d_solver->mkBitVectorSort(4)));
}

void SolverBlack::testMkUninterpretedSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->mkUninterpretedSort("u"));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkUninterpretedSort(""));
}

void SolverBlack::testMkSortConstructorSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->mkSortConstructorSort("s", 2));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkSortConstructorSort("", 2));
  TS_ASSERT_THROWS(d_solver->mkSortConstructorSort("", 0), CVC4ApiException&);
}

void SolverBlack::testMkTupleSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTupleSort({d_solver->getIntegerSort()}));
  Sort funSort = d_solver->mkFunctionSort(d_solver->mkUninterpretedSort("u"),
                                          d_solver->getIntegerSort());
  TS_ASSERT_THROWS(d_solver->mkTupleSort({d_solver->getIntegerSort(), funSort}),
                   CVC4ApiException&);
}

void SolverBlack::testMkBitVector()
{
  uint32_t size0 = 0, size1 = 8, size2 = 32, val1 = 2;
  uint64_t val2 = 2;
  TS_ASSERT_THROWS_NOTHING(d_solver->mkBitVector(size1, val1));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkBitVector(size2, val2));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkBitVector("1010", 2));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkBitVector("1010", 10));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkBitVector("1234", 10));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkBitVector("1010", 16));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkBitVector("a09f", 16));
  TS_ASSERT_THROWS(d_solver->mkBitVector(size0, val1), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkBitVector(size0, val2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkBitVector("", 2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkBitVector("10", 3), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkBitVector("20", 2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkBitVector(8, "101010101", 2), CVC4ApiException&);
  TS_ASSERT_EQUALS(d_solver->mkBitVector("1010", 2),
                   d_solver->mkBitVector("10", 10));
  TS_ASSERT_EQUALS(d_solver->mkBitVector("1010", 2),
                   d_solver->mkBitVector("a", 16));
  TS_ASSERT_EQUALS(d_solver->mkBitVector(8, "01010101", 2).toString(),
                   "0bin01010101");
  TS_ASSERT_EQUALS(d_solver->mkBitVector(8, "F", 16).toString(),
                   "0bin00001111");
}

void SolverBlack::testMkBoundVar()
{
  Sort boolSort = d_solver->getBooleanSort();
  Sort intSort = d_solver->getIntegerSort();
  Sort funSort = d_solver->mkFunctionSort(intSort, boolSort);
  TS_ASSERT_THROWS_NOTHING(d_solver->mkVar(boolSort));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkVar(funSort));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkVar(boolSort, std::string("b")));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkVar(funSort, ""));
  TS_ASSERT_THROWS(d_solver->mkVar(Sort()), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkVar(Sort(), "a"), CVC4ApiException&);
}

void SolverBlack::testMkBoolean()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->mkBoolean(true));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkBoolean(false));
}

void SolverBlack::testMkRoundingMode()
{
  TS_ASSERT_THROWS_NOTHING(
      d_solver->mkRoundingMode(RoundingMode::ROUND_TOWARD_ZERO));
}

void SolverBlack::testMkUninterpretedConst()
{
  TS_ASSERT_THROWS_NOTHING(
      d_solver->mkUninterpretedConst(d_solver->getBooleanSort(), 1));
  TS_ASSERT_THROWS(d_solver->mkUninterpretedConst(Sort(), 1),
                   CVC4ApiException&);
}

void SolverBlack::testMkAbstractValue()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->mkAbstractValue(std::string("1")));
  TS_ASSERT_THROWS(d_solver->mkAbstractValue(std::string("0")),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkAbstractValue(std::string("-1")),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkAbstractValue(std::string("1.2")),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkAbstractValue("1/2"), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkAbstractValue("asdf"), CVC4ApiException&);

  TS_ASSERT_THROWS_NOTHING(d_solver->mkAbstractValue((uint32_t)1));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkAbstractValue((int32_t)1));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkAbstractValue((uint64_t)1));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkAbstractValue((int64_t)1));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkAbstractValue((int32_t)-1));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkAbstractValue((int64_t)-1));
  TS_ASSERT_THROWS(d_solver->mkAbstractValue(0), CVC4ApiException&);
}

void SolverBlack::testMkFloatingPoint()
{
  Term t1 = d_solver->mkBitVector(8);
  Term t2 = d_solver->mkBitVector(4);
  Term t3 = d_solver->mkReal(2);
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    TS_ASSERT_THROWS_NOTHING(d_solver->mkFloatingPoint(3, 5, t1));
  }
  else
  {
    TS_ASSERT_THROWS(d_solver->mkFloatingPoint(3, 5, t1), CVC4ApiException&);
  }
  TS_ASSERT_THROWS(d_solver->mkFloatingPoint(0, 5, Term()), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkFloatingPoint(0, 5, t1), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkFloatingPoint(3, 0, t1), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkFloatingPoint(3, 5, t2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkFloatingPoint(3, 5, t2), CVC4ApiException&);
}

void SolverBlack::testMkEmptySet()
{
  TS_ASSERT_THROWS(d_solver->mkEmptySet(d_solver->getBooleanSort()),
                   CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(d_solver->mkEmptySet(Sort()));
}

void SolverBlack::testMkFalse()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->mkFalse());
  TS_ASSERT_THROWS_NOTHING(d_solver->mkFalse());
}

void SolverBlack::testMkNaN()
{
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    TS_ASSERT_THROWS_NOTHING(d_solver->mkNaN(3, 5));
  }
  else
  {
    TS_ASSERT_THROWS(d_solver->mkNaN(3, 5), CVC4ApiException&);
  }
}

void SolverBlack::testMkNegZero()
{
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    TS_ASSERT_THROWS_NOTHING(d_solver->mkNegZero(3, 5));
  }
  else
  {
    TS_ASSERT_THROWS(d_solver->mkNegZero(3, 5), CVC4ApiException&);
  }
}

void SolverBlack::testMkNegInf()
{
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    TS_ASSERT_THROWS_NOTHING(d_solver->mkNegInf(3, 5));
  }
  else
  {
    TS_ASSERT_THROWS(d_solver->mkNegInf(3, 5), CVC4ApiException&);
  }
}

void SolverBlack::testMkPosInf()
{
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    TS_ASSERT_THROWS_NOTHING(d_solver->mkPosInf(3, 5));
  }
  else
  {
    TS_ASSERT_THROWS(d_solver->mkPosInf(3, 5), CVC4ApiException&);
  }
}

void SolverBlack::testMkPosZero()
{
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    TS_ASSERT_THROWS_NOTHING(d_solver->mkPosZero(3, 5));
  }
  else
  {
    TS_ASSERT_THROWS(d_solver->mkPosZero(3, 5), CVC4ApiException&);
  }
}

void SolverBlack::testMkOpTerm()
{
  // mkOpTerm(Kind kind, Kind k)
  TS_ASSERT_THROWS_NOTHING(d_solver->mkOpTerm(CHAIN_OP, EQUAL));
  TS_ASSERT_THROWS(d_solver->mkOpTerm(BITVECTOR_EXTRACT_OP, EQUAL),
                   CVC4ApiException&);

  // mkOpTerm(Kind kind, const std::string& arg)
  TS_ASSERT_THROWS_NOTHING(d_solver->mkOpTerm(RECORD_UPDATE_OP, "asdf"));
  TS_ASSERT_THROWS(d_solver->mkOpTerm(BITVECTOR_EXTRACT_OP, "asdf"),
                   CVC4ApiException&);

  // mkOpTerm(Kind kind, uint32_t arg)
  TS_ASSERT_THROWS_NOTHING(d_solver->mkOpTerm(DIVISIBLE_OP, 1));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkOpTerm(BITVECTOR_ROTATE_LEFT_OP, 1));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkOpTerm(BITVECTOR_ROTATE_RIGHT_OP, 1));
  TS_ASSERT_THROWS(d_solver->mkOpTerm(BITVECTOR_EXTRACT_OP, 1),
                   CVC4ApiException&);

  // mkOpTerm(Kind kind, uint32_t arg1, uint32_t arg2)
  TS_ASSERT_THROWS_NOTHING(d_solver->mkOpTerm(BITVECTOR_EXTRACT_OP, 1, 1));
  TS_ASSERT_THROWS(d_solver->mkOpTerm(DIVISIBLE_OP, 1, 2), CVC4ApiException&);
}

void SolverBlack::testMkPi() { TS_ASSERT_THROWS_NOTHING(d_solver->mkPi()); }

void SolverBlack::testMkReal()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal("123"));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal("1.23"));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal("1/23"));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal("12/3"));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal(".2"));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal("2."));
  TS_ASSERT_THROWS(d_solver->mkReal(nullptr), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkReal(""), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkReal("asdf"), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkReal("1.2/3"), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkReal("."), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkReal("/"), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkReal("2/"), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkReal("/2"), CVC4ApiException&);

  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal(std::string("123")));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal(std::string("1.23")));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal(std::string("1/23")));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal(std::string("12/3")));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal(std::string(".2")));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal(std::string("2.")));
  TS_ASSERT_THROWS(d_solver->mkReal(std::string("")), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkReal(std::string("asdf")), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkReal(std::string("1.2/3")), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkReal(std::string(".")), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkReal(std::string("/")), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkReal(std::string("2/")), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkReal(std::string("/2")), CVC4ApiException&);

  int32_t val1 = 1;
  int64_t val2 = -1;
  uint32_t val3 = 1;
  uint64_t val4 = -1;
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal(val1));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal(val2));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal(val3));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal(val4));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal(val4));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal(val1, val1));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal(val2, val2));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal(val3, val3));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkReal(val4, val4));
}

void SolverBlack::testMkRegexpEmpty()
{
  Sort strSort = d_solver->getStringSort();
  Term s = d_solver->mkConst(strSort, "s");
  TS_ASSERT_THROWS_NOTHING(
      d_solver->mkTerm(STRING_IN_REGEXP, s, d_solver->mkRegexpEmpty()));
}

void SolverBlack::testMkRegexpSigma()
{
  Sort strSort = d_solver->getStringSort();
  Term s = d_solver->mkConst(strSort, "s");
  TS_ASSERT_THROWS_NOTHING(
      d_solver->mkTerm(STRING_IN_REGEXP, s, d_solver->mkRegexpSigma()));
}

void SolverBlack::testMkSepNil()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->mkSepNil(d_solver->getBooleanSort()));
  TS_ASSERT_THROWS(d_solver->mkSepNil(Sort()), CVC4ApiException&);
}

void SolverBlack::testMkString()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->mkString(""));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkString("asdfasdf"));
  TS_ASSERT_EQUALS(d_solver->mkString("asdf\\nasdf").toString(),
                   "\"asdf\\\\nasdf\"");
  TS_ASSERT_EQUALS(d_solver->mkString("asdf\\nasdf", true).toString(),
                   "\"asdf\\nasdf\"");
}

void SolverBlack::testMkTerm()
{
  Sort bv32 = d_solver->mkBitVectorSort(32);
  Term a = d_solver->mkConst(bv32, "a");
  Term b = d_solver->mkConst(bv32, "b");
  std::vector<Term> v1 = {a, b};
  std::vector<Term> v2 = {a, Term()};
  std::vector<Term> v3 = {a, d_solver->mkTrue()};
  std::vector<Term> v4 = {d_solver->mkReal(1), d_solver->mkReal(2)};
  std::vector<Term> v5 = {d_solver->mkReal(1), Term()};
  std::vector<Term> v6 = {};

  // mkTerm(Kind kind) const
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(PI));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(REGEXP_EMPTY));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(REGEXP_SIGMA));
  TS_ASSERT_THROWS(d_solver->mkTerm(CONST_BITVECTOR), CVC4ApiException&);

  // mkTerm(Kind kind, Term child) const
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(NOT, d_solver->mkTrue()));
  TS_ASSERT_THROWS(d_solver->mkTerm(NOT, Term()), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(NOT, a), CVC4ApiException&);

  // mkTerm(Kind kind, Term child1, Term child2) const
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(EQUAL, a, b));
  TS_ASSERT_THROWS(d_solver->mkTerm(EQUAL, Term(), b), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(EQUAL, a, Term()), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(EQUAL, a, d_solver->mkTrue()),
                   CVC4ApiException&);

  // mkTerm(Kind kind, Term child1, Term child2, Term child3) const
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(
      ITE, d_solver->mkTrue(), d_solver->mkTrue(), d_solver->mkTrue()));
  TS_ASSERT_THROWS(
      d_solver->mkTerm(ITE, Term(), d_solver->mkTrue(), d_solver->mkTrue()),
      CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver->mkTerm(ITE, d_solver->mkTrue(), Term(), d_solver->mkTrue()),
      CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver->mkTerm(ITE, d_solver->mkTrue(), d_solver->mkTrue(), Term()),
      CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver->mkTerm(ITE, d_solver->mkTrue(), d_solver->mkTrue(), b),
      CVC4ApiException&);

  // mkTerm(Kind kind, const std::vector<Term>& children) const
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(EQUAL, v1));
  TS_ASSERT_THROWS(d_solver->mkTerm(EQUAL, v2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(EQUAL, v3), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(DISTINCT, v6), CVC4ApiException&);
}

void SolverBlack::testMkTermFromOpTerm()
{
  Sort bv32 = d_solver->mkBitVectorSort(32);
  Term a = d_solver->mkConst(bv32, "a");
  Term b = d_solver->mkConst(bv32, "b");
  std::vector<Term> v1 = {d_solver->mkReal(1), d_solver->mkReal(2)};
  std::vector<Term> v2 = {d_solver->mkReal(1), Term()};
  std::vector<Term> v3 = {};
  // simple operator terms
  OpTerm opterm1 = d_solver->mkOpTerm(BITVECTOR_EXTRACT_OP, 2, 1);
  OpTerm opterm2 = d_solver->mkOpTerm(DIVISIBLE_OP, 1);
  OpTerm opterm3 = d_solver->mkOpTerm(CHAIN_OP, EQUAL);
  // list datatype
  Sort sort = d_solver->mkParamSort("T");
  DatatypeDecl listDecl("paramlist", sort);
  DatatypeConstructorDecl cons("cons");
  DatatypeConstructorDecl nil("nil");
  DatatypeSelectorDecl head("head", sort);
  DatatypeSelectorDecl tail("tail", DatatypeDeclSelfSort());
  cons.addSelector(head);
  cons.addSelector(tail);
  listDecl.addConstructor(cons);
  listDecl.addConstructor(nil);
  Sort listSort = d_solver->mkDatatypeSort(listDecl);
  Sort intListSort =
      listSort.instantiate(std::vector<Sort>{d_solver->getIntegerSort()});
  Term c = d_solver->mkConst(intListSort, "c");
  Datatype list = listSort.getDatatype();
  // list datatype constructor and selector operator terms
  OpTerm consTerm1 = list.getConstructorTerm("cons");
  OpTerm consTerm2 = list.getConstructor("cons").getConstructorTerm();
  OpTerm nilTerm1 = list.getConstructorTerm("nil");
  OpTerm nilTerm2 = list.getConstructor("nil").getConstructorTerm();
  OpTerm headTerm1 = list["cons"].getSelectorTerm("head");
  OpTerm headTerm2 = list["cons"].getSelector("head").getSelectorTerm();
  OpTerm tailTerm1 = list["cons"].getSelectorTerm("tail");
  OpTerm tailTerm2 = list["cons"]["tail"].getSelectorTerm();

  // mkTerm(Kind kind, OpTerm opTerm) const
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(APPLY_CONSTRUCTOR, nilTerm1));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(APPLY_CONSTRUCTOR, nilTerm2));
  TS_ASSERT_THROWS(d_solver->mkTerm(APPLY_CONSTRUCTOR, consTerm1),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(APPLY_CONSTRUCTOR, consTerm2),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(APPLY_CONSTRUCTOR, opterm1),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(APPLY_SELECTOR, headTerm1),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(APPLY_SELECTOR, tailTerm2),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(BITVECTOR_EXTRACT, opterm1),
                   CVC4ApiException&);

  // mkTerm(Kind kind, OpTerm opTerm, Term child) const
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(BITVECTOR_EXTRACT, opterm1, a));
  TS_ASSERT_THROWS_NOTHING(
      d_solver->mkTerm(DIVISIBLE, opterm2, d_solver->mkReal(1)));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(APPLY_SELECTOR, headTerm1, c));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(APPLY_SELECTOR, tailTerm2, c));
  TS_ASSERT_THROWS(d_solver->mkTerm(DIVISIBLE, opterm1, a), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(DIVISIBLE, opterm2, a), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(BITVECTOR_EXTRACT, opterm1, Term()),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver->mkTerm(APPLY_CONSTRUCTOR, consTerm1, d_solver->mkReal(0)),
      CVC4ApiException&);

  // mkTerm(Kind kind, OpTerm opTerm, Term child1, Term child2) const
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(
      CHAIN, opterm3, d_solver->mkReal(1), d_solver->mkReal(2)));
  TS_ASSERT_THROWS_NOTHING(
      d_solver->mkTerm(APPLY_CONSTRUCTOR,
                       consTerm1,
                       d_solver->mkReal(0),
                       d_solver->mkTerm(APPLY_CONSTRUCTOR, nilTerm1)));
  TS_ASSERT_THROWS(d_solver->mkTerm(BITVECTOR_EXTRACT, opterm1, a, b),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver->mkTerm(CHAIN, opterm3, d_solver->mkReal(1), Term()),
      CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver->mkTerm(CHAIN, opterm3, Term(), d_solver->mkReal(1)),
      CVC4ApiException&);

  // mkTerm(Kind kind, OpTerm opTerm, Term child1, Term child2, Term child3)
  // const
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(CHAIN,
                                            opterm3,
                                            d_solver->mkReal(1),
                                            d_solver->mkReal(1),
                                            d_solver->mkReal(2)));
  TS_ASSERT_THROWS(d_solver->mkTerm(BITVECTOR_EXTRACT, opterm1, a, b, a),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver->mkTerm(
          CHAIN, opterm3, d_solver->mkReal(1), d_solver->mkReal(1), Term()),
      CVC4ApiException&);

  // mkTerm(OpTerm opTerm, const std::vector<Term>& children) const
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(CHAIN, opterm3, v1));
  TS_ASSERT_THROWS(d_solver->mkTerm(CHAIN, opterm3, v2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(CHAIN, opterm3, v3), CVC4ApiException&);
}

void SolverBlack::testMkTrue()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTrue());
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTrue());
}

void SolverBlack::testMkTuple()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTuple(
      {d_solver->mkBitVectorSort(3)}, {d_solver->mkBitVector("101", 2)}));
  TS_ASSERT_THROWS_NOTHING(
      d_solver->mkTuple({d_solver->getRealSort()}, {d_solver->mkReal("5")}));

  TS_ASSERT_THROWS(d_solver->mkTuple({}, {d_solver->mkBitVector("101", 2)}),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTuple({d_solver->mkBitVectorSort(4)},
                                     {d_solver->mkBitVector("101", 2)}),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTuple({d_solver->getIntegerSort()},
                                     {d_solver->mkReal("5.3")}),
                   CVC4ApiException&);
}

void SolverBlack::testMkUniverseSet()
{
  TS_ASSERT_THROWS(d_solver->mkUniverseSet(Sort()), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(d_solver->mkUniverseSet(d_solver->getBooleanSort()));
}

void SolverBlack::testMkVar()
{
  Sort boolSort = d_solver->getBooleanSort();
  Sort intSort = d_solver->getIntegerSort();
  Sort funSort = d_solver->mkFunctionSort(intSort, boolSort);
  TS_ASSERT_THROWS_NOTHING(d_solver->mkConst(boolSort));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkConst(funSort));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkConst(boolSort, std::string("b")));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkConst(intSort, std::string("i")));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkConst(funSort, "f"));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkConst(funSort, ""));
  TS_ASSERT_THROWS(d_solver->mkConst(Sort()), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkConst(Sort(), "a"), CVC4ApiException&);
}

void SolverBlack::testDeclareDatatype()
{
  DatatypeConstructorDecl cons("cons");
  DatatypeConstructorDecl nil("nil");
  std::vector<DatatypeConstructorDecl> ctors1 = {nil};
  std::vector<DatatypeConstructorDecl> ctors2 = {cons, nil};
  std::vector<DatatypeConstructorDecl> ctors3;
  TS_ASSERT_THROWS_NOTHING(d_solver->declareDatatype(std::string("a"), ctors1));
  TS_ASSERT_THROWS_NOTHING(d_solver->declareDatatype(std::string("b"), ctors2));
  TS_ASSERT_THROWS_NOTHING(d_solver->declareDatatype(std::string(""), ctors2));
  TS_ASSERT_THROWS(d_solver->declareDatatype(std::string("c"), ctors3),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->declareDatatype(std::string(""), ctors3),
                   CVC4ApiException&);
}

void SolverBlack::testDeclareFun()
{
  Sort bvSort = d_solver->mkBitVectorSort(32);
  Sort funSort = d_solver->mkFunctionSort(d_solver->mkUninterpretedSort("u"),
                                          d_solver->getIntegerSort());
  TS_ASSERT_THROWS_NOTHING(d_solver->declareFun("f1", {}, bvSort));
  TS_ASSERT_THROWS_NOTHING(
      d_solver->declareFun("f3", {bvSort, d_solver->getIntegerSort()}, bvSort));
  TS_ASSERT_THROWS(d_solver->declareFun("f2", {}, funSort), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->declareFun("f4", {bvSort, funSort}, bvSort),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->declareFun("f5", {bvSort, bvSort}, funSort),
                   CVC4ApiException&);
}

void SolverBlack::testDeclareSort()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->declareSort("s", 0));
  TS_ASSERT_THROWS_NOTHING(d_solver->declareSort("s", 2));
  TS_ASSERT_THROWS_NOTHING(d_solver->declareSort("", 2));
}

void SolverBlack::testDefineFun()
{
  Sort bvSort = d_solver->mkBitVectorSort(32);
  Sort funSort1 = d_solver->mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_solver->mkFunctionSort(d_solver->mkUninterpretedSort("u"),
                                           d_solver->getIntegerSort());
  Term b1 = d_solver->mkVar(bvSort, "b1");
  Term b11 = d_solver->mkVar(bvSort, "b1");
  Term b2 = d_solver->mkVar(d_solver->getIntegerSort(), "b2");
  Term b3 = d_solver->mkVar(funSort2, "b3");
  Term v1 = d_solver->mkVar(bvSort, "v1");
  Term v2 = d_solver->mkVar(d_solver->getIntegerSort(), "v2");
  Term v3 = d_solver->mkConst(funSort2, "v3");
  Term f1 = d_solver->mkConst(funSort1, "f1");
  Term f2 = d_solver->mkConst(funSort2, "f2");
  Term f3 = d_solver->mkConst(bvSort, "f3");
  TS_ASSERT_THROWS_NOTHING(d_solver->defineFun("f", {}, bvSort, v1));
  TS_ASSERT_THROWS_NOTHING(d_solver->defineFun("ff", {b1, b2}, bvSort, v1));
  TS_ASSERT_THROWS_NOTHING(d_solver->defineFun(f1, {b1, b11}, v1));
  TS_ASSERT_THROWS(d_solver->defineFun("fff", {b1}, bvSort, v3),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->defineFun("ffff", {b1}, funSort2, v3),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->defineFun("fffff", {b1, b3}, bvSort, v1),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->defineFun(f1, {b1}, v1), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->defineFun(f1, {b1, b11}, v2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->defineFun(f1, {b1, b11}, v3), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->defineFun(f2, {b1}, v2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->defineFun(f3, {b1}, v1), CVC4ApiException&);
}

void SolverBlack::testDefineFunRec()
{
  Sort bvSort = d_solver->mkBitVectorSort(32);
  Sort funSort1 = d_solver->mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_solver->mkFunctionSort(d_solver->mkUninterpretedSort("u"),
                                           d_solver->getIntegerSort());
  Term b1 = d_solver->mkVar(bvSort, "b1");
  Term b11 = d_solver->mkVar(bvSort, "b1");
  Term b2 = d_solver->mkVar(d_solver->getIntegerSort(), "b2");
  Term b3 = d_solver->mkVar(funSort2, "b3");
  Term v1 = d_solver->mkVar(bvSort, "v1");
  Term v2 = d_solver->mkVar(d_solver->getIntegerSort(), "v2");
  Term v3 = d_solver->mkConst(funSort2, "v3");
  Term f1 = d_solver->mkConst(funSort1, "f1");
  Term f2 = d_solver->mkConst(funSort2, "f2");
  Term f3 = d_solver->mkConst(bvSort, "f3");
  TS_ASSERT_THROWS_NOTHING(d_solver->defineFunRec("f", {}, bvSort, v1));
  TS_ASSERT_THROWS_NOTHING(d_solver->defineFunRec("ff", {b1, b2}, bvSort, v1));
  TS_ASSERT_THROWS_NOTHING(d_solver->defineFunRec(f1, {b1, b11}, v1));
  TS_ASSERT_THROWS(d_solver->defineFunRec("fff", {b1}, bvSort, v3),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->defineFunRec("ffff", {b1}, funSort2, v3),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->defineFunRec("fffff", {b1, b3}, bvSort, v1),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->defineFunRec(f1, {b1}, v1), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->defineFunRec(f1, {b1, b11}, v2),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->defineFunRec(f1, {b1, b11}, v3),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->defineFunRec(f2, {b1}, v2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->defineFunRec(f3, {b1}, v1), CVC4ApiException&);
}

void SolverBlack::testDefineFunsRec()
{
  Sort uSort = d_solver->mkUninterpretedSort("u");
  Sort bvSort = d_solver->mkBitVectorSort(32);
  Sort funSort1 = d_solver->mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_solver->mkFunctionSort(uSort, d_solver->getIntegerSort());
  Term b1 = d_solver->mkVar(bvSort, "b1");
  Term b11 = d_solver->mkVar(bvSort, "b1");
  Term b2 = d_solver->mkVar(d_solver->getIntegerSort(), "b2");
  Term b3 = d_solver->mkVar(funSort2, "b3");
  Term b4 = d_solver->mkVar(uSort, "b4");
  Term v1 = d_solver->mkVar(bvSort, "v1");
  Term v2 = d_solver->mkVar(d_solver->getIntegerSort(), "v2");
  Term v3 = d_solver->mkConst(funSort2, "v3");
  Term v4 = d_solver->mkConst(uSort, "v4");
  Term f1 = d_solver->mkConst(funSort1, "f1");
  Term f2 = d_solver->mkConst(funSort2, "f2");
  Term f3 = d_solver->mkConst(bvSort, "f3");
  TS_ASSERT_THROWS_NOTHING(
      d_solver->defineFunsRec({f1, f2}, {{b1, b11}, {b4}}, {v1, v2}));
  TS_ASSERT_THROWS(
      d_solver->defineFunsRec({f1, f3}, {{b1, b11}, {b4}}, {v1, v2}),
      CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->defineFunsRec({f1, f2}, {{b1}, {b4}}, {v1, v2}),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver->defineFunsRec({f1, f2}, {{b1, b2}, {b4}}, {v1, v2}),
      CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver->defineFunsRec({f1, f2}, {{b1, b11}, {b4}}, {v1, v4}),
      CVC4ApiException&);
}

void SolverBlack::testSetInfo()
{
  TS_ASSERT_THROWS(d_solver->setInfo("cvc4-lagic", "QF_BV"), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->setInfo("cvc2-logic", "QF_BV"), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->setInfo("cvc4-logic", "asdf"), CVC4ApiException&);

  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("source", "asdf"));
  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("category", "asdf"));
  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("difficulty", "asdf"));
  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("filename", "asdf"));
  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("license", "asdf"));
  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("name", "asdf"));
  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("notes", "asdf"));

  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("smt-lib-version", "2"));
  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("smt-lib-version", "2.0"));
  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("smt-lib-version", "2.5"));
  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("smt-lib-version", "2.6"));
  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("smt-lib-version", "2.6.1"));
  TS_ASSERT_THROWS(d_solver->setInfo("smt-lib-version", ".0"),
                   CVC4ApiException&);

  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("status", "sat"));
  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("status", "unsat"));
  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("status", "unknown"));
  TS_ASSERT_THROWS(d_solver->setInfo("status", "asdf"), CVC4ApiException&);
}

void SolverBlack::testSetLogic()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->setLogic("AUFLIRA"));
  TS_ASSERT_THROWS(d_solver->setLogic("AF_BV"), CVC4ApiException&);
  d_solver->assertFormula(d_solver->mkTrue());
  TS_ASSERT_THROWS(d_solver->setLogic("AUFLIRA"), CVC4ApiException&);
}

void SolverBlack::testSetOption()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->setOption("bv-sat-solver", "minisat"));
  TS_ASSERT_THROWS(d_solver->setOption("bv-sat-solver", "1"),
                   CVC4ApiException&);
  d_solver->assertFormula(d_solver->mkTrue());
  TS_ASSERT_THROWS(d_solver->setOption("bv-sat-solver", "minisat"),
                   CVC4ApiException&);
}
