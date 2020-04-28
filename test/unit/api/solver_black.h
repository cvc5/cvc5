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
  void testMkOp();
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
  void testMkConst();
  void testMkConstArray();
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
  void testMkChar();
  void testMkTerm();
  void testMkTermFromOp();
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

  void testUFIteration();
  void testGetOp();

  void testPush1();
  void testPush2();
  void testPop1();
  void testPop2();
  void testPop3();

  void testSimplify();
  void testCheckEntailed();
  void testCheckEntailed1();
  void testCheckEntailed2();

  void testSetInfo();
  void testSetLogic();
  void testSetOption();

  void testResetAssertions();

  void testMkSygusVar();
  void testMkSygusGrammar();
  void testSynthFun();
  void testSynthInv();
  void testAddSygusConstraint();
  void testAddSygusInvConstraint();
  void testGetSynthSolution();
  void testGetSynthSolutions();

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
  DatatypeDecl dtypeSpec = d_solver->mkDatatypeDecl("list");
  DatatypeConstructorDecl cons("cons");
  cons.addSelector("head", d_solver->getIntegerSort());
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil("nil");
  dtypeSpec.addConstructor(nil);
  TS_ASSERT_THROWS_NOTHING(d_solver->mkDatatypeSort(dtypeSpec));
  DatatypeDecl throwsDtypeSpec = d_solver->mkDatatypeDecl("list");
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
  Sort recSort = d_solver->mkRecordSort(fields);
  TS_ASSERT_THROWS_NOTHING(recSort.getDatatype());
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
  TS_ASSERT_THROWS_NOTHING(d_solver->mkBitVector(8, "-127", 10));
  TS_ASSERT_THROWS(d_solver->mkBitVector(size0, val1), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkBitVector(size0, val2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkBitVector("", 2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkBitVector("10", 3), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkBitVector("20", 2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkBitVector(8, "101010101", 2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkBitVector(8, "-256", 10), CVC4ApiException&);
  TS_ASSERT_EQUALS(d_solver->mkBitVector("1010", 2),
                   d_solver->mkBitVector("10", 10));
  TS_ASSERT_EQUALS(d_solver->mkBitVector("1010", 2),
                   d_solver->mkBitVector("a", 16));
  TS_ASSERT_EQUALS(d_solver->mkBitVector(8, "01010101", 2).toString(),
                   "0bin01010101");
  TS_ASSERT_EQUALS(d_solver->mkBitVector(8, "F", 16).toString(),
                   "0bin00001111");
  TS_ASSERT_EQUALS(d_solver->mkBitVector(8, "-1", 10),
                   d_solver->mkBitVector(8, "FF", 16));
}

void SolverBlack::testMkVar()
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

void SolverBlack::testMkOp()
{
  // mkOp(Kind kind, Kind k)
  TS_ASSERT_THROWS(d_solver->mkOp(BITVECTOR_EXTRACT, EQUAL), CVC4ApiException&);

  // mkOp(Kind kind, const std::string& arg)
  TS_ASSERT_THROWS_NOTHING(d_solver->mkOp(RECORD_UPDATE, "asdf"));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkOp(DIVISIBLE, "2147483648"));
  TS_ASSERT_THROWS(d_solver->mkOp(BITVECTOR_EXTRACT, "asdf"),
                   CVC4ApiException&);

  // mkOp(Kind kind, uint32_t arg)
  TS_ASSERT_THROWS_NOTHING(d_solver->mkOp(DIVISIBLE, 1));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkOp(BITVECTOR_ROTATE_LEFT, 1));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkOp(BITVECTOR_ROTATE_RIGHT, 1));
  TS_ASSERT_THROWS(d_solver->mkOp(BITVECTOR_EXTRACT, 1), CVC4ApiException&);

  // mkOp(Kind kind, uint32_t arg1, uint32_t arg2)
  TS_ASSERT_THROWS_NOTHING(d_solver->mkOp(BITVECTOR_EXTRACT, 1, 1));
  TS_ASSERT_THROWS(d_solver->mkOp(DIVISIBLE, 1, 2), CVC4ApiException&);
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
                   "\"asdf\\u{5c}nasdf\"");
  TS_ASSERT_EQUALS(d_solver->mkString("asdf\\u{005c}nasdf", true).toString(),
                   "\"asdf\\u{5c}nasdf\"");
}

void SolverBlack::testMkChar()
{
  TS_ASSERT_THROWS_NOTHING(d_solver->mkChar(std::string("0123")));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkChar("aA"));
  TS_ASSERT_THROWS(d_solver->mkChar(nullptr), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkChar(""), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkChar("0g0"), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkChar("100000"), CVC4ApiException&);
  TS_ASSERT_EQUALS(d_solver->mkChar("abc"), d_solver->mkChar("ABC"));
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

void SolverBlack::testMkTermFromOp()
{
  Sort bv32 = d_solver->mkBitVectorSort(32);
  Term a = d_solver->mkConst(bv32, "a");
  Term b = d_solver->mkConst(bv32, "b");
  std::vector<Term> v1 = {d_solver->mkReal(1), d_solver->mkReal(2)};
  std::vector<Term> v2 = {d_solver->mkReal(1), Term()};
  std::vector<Term> v3 = {};
  std::vector<Term> v4 = {d_solver->mkReal(5)};
  // simple operator terms
  Op opterm1 = d_solver->mkOp(BITVECTOR_EXTRACT, 2, 1);
  Op opterm2 = d_solver->mkOp(DIVISIBLE, 1);
  // list datatype

  Sort sort = d_solver->mkParamSort("T");
  DatatypeDecl listDecl = d_solver->mkDatatypeDecl("paramlist", sort);
  DatatypeConstructorDecl cons("cons");
  DatatypeConstructorDecl nil("nil");
  cons.addSelector("head", sort);
  cons.addSelectorSelf("tail");
  listDecl.addConstructor(cons);
  listDecl.addConstructor(nil);
  Sort listSort = d_solver->mkDatatypeSort(listDecl);
  Sort intListSort =
      listSort.instantiate(std::vector<Sort>{d_solver->getIntegerSort()});
  Term c = d_solver->mkConst(intListSort, "c");
  Datatype list = listSort.getDatatype();
  // list datatype constructor and selector operator terms
  Term consTerm1 = list.getConstructorTerm("cons");
  Term consTerm2 = list.getConstructor("cons").getConstructorTerm();
  Term nilTerm1 = list.getConstructorTerm("nil");
  Term nilTerm2 = list.getConstructor("nil").getConstructorTerm();
  Term headTerm1 = list["cons"].getSelectorTerm("head");
  Term headTerm2 = list["cons"].getSelector("head").getSelectorTerm();
  Term tailTerm1 = list["cons"].getSelectorTerm("tail");
  Term tailTerm2 = list["cons"]["tail"].getSelectorTerm();

  // mkTerm(Op op, Term term) const
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(APPLY_CONSTRUCTOR, nilTerm1));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(APPLY_CONSTRUCTOR, nilTerm2));
  TS_ASSERT_THROWS(d_solver->mkTerm(APPLY_SELECTOR, nilTerm1),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(APPLY_SELECTOR, consTerm1),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(APPLY_CONSTRUCTOR, consTerm2),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(opterm1), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(APPLY_SELECTOR, headTerm1),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(opterm1), CVC4ApiException&);

  // mkTerm(Op op, Term child) const
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(opterm1, a));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(opterm2, d_solver->mkReal(1)));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(APPLY_SELECTOR, headTerm1, c));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(APPLY_SELECTOR, tailTerm2, c));
  TS_ASSERT_THROWS(d_solver->mkTerm(opterm2, a), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(opterm1, Term()), CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver->mkTerm(APPLY_CONSTRUCTOR, consTerm1, d_solver->mkReal(0)),
      CVC4ApiException&);

  // mkTerm(Op op, Term child1, Term child2) const
  TS_ASSERT_THROWS(
      d_solver->mkTerm(opterm2, d_solver->mkReal(1), d_solver->mkReal(2)),
      CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(
      d_solver->mkTerm(APPLY_CONSTRUCTOR,
                       consTerm1,
                       d_solver->mkReal(0),
                       d_solver->mkTerm(APPLY_CONSTRUCTOR, nilTerm1)));
  TS_ASSERT_THROWS(d_solver->mkTerm(opterm1, a, b), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(opterm2, d_solver->mkReal(1), Term()),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(opterm2, Term(), d_solver->mkReal(1)),
                   CVC4ApiException&);

  // mkTerm(Op op, Term child1, Term child2, Term child3)
  // const
  TS_ASSERT_THROWS(d_solver->mkTerm(opterm1, a, b, a), CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver->mkTerm(
          opterm2, d_solver->mkReal(1), d_solver->mkReal(1), Term()),
      CVC4ApiException&);

  // mkTerm(Op op, const std::vector<Term>& children) const
  TS_ASSERT_THROWS_NOTHING(d_solver->mkTerm(opterm2, v4));
  TS_ASSERT_THROWS(d_solver->mkTerm(opterm2, v1), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(opterm2, v2), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkTerm(opterm2, v3), CVC4ApiException&);
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

void SolverBlack::testMkConst()
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

void SolverBlack::testMkConstArray()
{
  Sort intSort = d_solver->getIntegerSort();
  Sort arrSort = d_solver->mkArraySort(intSort, intSort);
  Term zero = d_solver->mkReal(0);
  Term constArr = d_solver->mkConstArray(arrSort, zero);

  TS_ASSERT_THROWS_NOTHING(d_solver->mkConstArray(arrSort, zero));
  TS_ASSERT_THROWS(d_solver->mkConstArray(arrSort, Term()), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkConstArray(arrSort, d_solver->mkBitVector(1, 1)),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkConstArray(intSort, zero), CVC4ApiException&);
}

void SolverBlack::testDeclareDatatype()
{
  DatatypeConstructorDecl nil("nil");
  std::vector<DatatypeConstructorDecl> ctors1 = {nil};
  TS_ASSERT_THROWS_NOTHING(d_solver->declareDatatype(std::string("a"), ctors1));
  DatatypeConstructorDecl cons("cons");
  DatatypeConstructorDecl nil2("nil");
  std::vector<DatatypeConstructorDecl> ctors2 = {cons, nil2};
  TS_ASSERT_THROWS_NOTHING(d_solver->declareDatatype(std::string("b"), ctors2));
  DatatypeConstructorDecl cons2("cons");
  DatatypeConstructorDecl nil3("nil");
  std::vector<DatatypeConstructorDecl> ctors3 = {cons2, nil3};
  TS_ASSERT_THROWS_NOTHING(d_solver->declareDatatype(std::string(""), ctors3));
  std::vector<DatatypeConstructorDecl> ctors4;
  TS_ASSERT_THROWS(d_solver->declareDatatype(std::string("c"), ctors4),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->declareDatatype(std::string(""), ctors4),
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
  Term v1 = d_solver->mkConst(bvSort, "v1");
  Term v2 = d_solver->mkConst(d_solver->getIntegerSort(), "v2");
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
  Term v1 = d_solver->mkConst(bvSort, "v1");
  Term v2 = d_solver->mkConst(d_solver->getIntegerSort(), "v2");
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
  Term v1 = d_solver->mkConst(bvSort, "v1");
  Term v2 = d_solver->mkConst(d_solver->getIntegerSort(), "v2");
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

void SolverBlack::testUFIteration()
{
  Sort intSort = d_solver->getIntegerSort();
  Sort funSort = d_solver->mkFunctionSort({intSort, intSort}, intSort);
  Term x = d_solver->mkConst(intSort, "x");
  Term y = d_solver->mkConst(intSort, "y");
  Term f = d_solver->mkConst(funSort, "f");
  Term fxy = d_solver->mkTerm(APPLY_UF, f, x, y);

  // Expecting the uninterpreted function to be one of the children
  Term expected_children[3] = {f, x, y};
  uint32_t idx = 0;
  for (auto c : fxy)
  {
    TS_ASSERT(idx < 3);
    TS_ASSERT(c == expected_children[idx]);
    idx++;
  }
}

void SolverBlack::testGetOp()
{
  Sort bv32 = d_solver->mkBitVectorSort(32);
  Term a = d_solver->mkConst(bv32, "a");
  Op ext = d_solver->mkOp(BITVECTOR_EXTRACT, 2, 1);
  Term exta = d_solver->mkTerm(ext, a);

  TS_ASSERT(!a.hasOp());
  TS_ASSERT_THROWS(a.getOp(), CVC4ApiException&);
  TS_ASSERT(exta.hasOp());
  TS_ASSERT_EQUALS(exta.getOp(), ext);

  // Test Datatypes -- more complicated
  DatatypeDecl consListSpec = d_solver->mkDatatypeDecl("list");
  DatatypeConstructorDecl cons("cons");
  cons.addSelector("head", d_solver->getIntegerSort());
  cons.addSelectorSelf("tail");
  consListSpec.addConstructor(cons);
  DatatypeConstructorDecl nil("nil");
  consListSpec.addConstructor(nil);
  Sort consListSort = d_solver->mkDatatypeSort(consListSpec);
  Datatype consList = consListSort.getDatatype();

  Term consTerm = consList.getConstructorTerm("cons");
  Term nilTerm = consList.getConstructorTerm("nil");
  Term headTerm = consList["cons"].getSelectorTerm("head");

  Term listnil = d_solver->mkTerm(APPLY_CONSTRUCTOR, nilTerm);
  Term listcons1 = d_solver->mkTerm(
      APPLY_CONSTRUCTOR, consTerm, d_solver->mkReal(1), listnil);
  Term listhead = d_solver->mkTerm(APPLY_SELECTOR, headTerm, listcons1);

  TS_ASSERT(listnil.hasOp());
  TS_ASSERT_EQUALS(listnil.getOp(), APPLY_CONSTRUCTOR);

  TS_ASSERT(listcons1.hasOp());
  TS_ASSERT_EQUALS(listcons1.getOp(), APPLY_CONSTRUCTOR);

  TS_ASSERT(listhead.hasOp());
  TS_ASSERT_EQUALS(listhead.getOp(), APPLY_SELECTOR);
}

void SolverBlack::testPush1()
{
  d_solver->setOption("incremental", "true");
  TS_ASSERT_THROWS_NOTHING(d_solver->push(1));
  TS_ASSERT_THROWS(d_solver->setOption("incremental", "false"),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->setOption("incremental", "true"),
                   CVC4ApiException&);
}

void SolverBlack::testPush2()
{
  d_solver->setOption("incremental", "false");
  TS_ASSERT_THROWS(d_solver->push(1), CVC4ApiException&);
}

void SolverBlack::testPop1()
{
  d_solver->setOption("incremental", "false");
  TS_ASSERT_THROWS(d_solver->pop(1), CVC4ApiException&);
}

void SolverBlack::testPop2()
{
  d_solver->setOption("incremental", "true");
  TS_ASSERT_THROWS(d_solver->pop(1), CVC4ApiException&);
}

void SolverBlack::testPop3()
{
  d_solver->setOption("incremental", "true");
  TS_ASSERT_THROWS_NOTHING(d_solver->push(1));
  TS_ASSERT_THROWS_NOTHING(d_solver->pop(1));
  TS_ASSERT_THROWS(d_solver->pop(1), CVC4ApiException&);
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
  TS_ASSERT_THROWS(d_solver->setInfo("smt-lib-version", ".0"),
                   CVC4ApiException&);

  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("status", "sat"));
  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("status", "unsat"));
  TS_ASSERT_THROWS_NOTHING(d_solver->setInfo("status", "unknown"));
  TS_ASSERT_THROWS(d_solver->setInfo("status", "asdf"), CVC4ApiException&);
}

void SolverBlack::testSimplify()
{
  TS_ASSERT_THROWS(d_solver->simplify(Term()), CVC4ApiException&);

  Sort bvSort = d_solver->mkBitVectorSort(32);
  Sort uSort = d_solver->mkUninterpretedSort("u");
  Sort funSort1 = d_solver->mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_solver->mkFunctionSort(uSort, d_solver->getIntegerSort());
  DatatypeDecl consListSpec = d_solver->mkDatatypeDecl("list");
  DatatypeConstructorDecl cons("cons");
  cons.addSelector("head", d_solver->getIntegerSort());
  cons.addSelectorSelf("tail");
  consListSpec.addConstructor(cons);
  DatatypeConstructorDecl nil("nil");
  consListSpec.addConstructor(nil);
  Sort consListSort = d_solver->mkDatatypeSort(consListSpec);

  Term x = d_solver->mkConst(bvSort, "x");
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(x));
  Term a = d_solver->mkConst(bvSort, "a");
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(a));
  Term b = d_solver->mkConst(bvSort, "b");
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(b));
  Term x_eq_x = d_solver->mkTerm(EQUAL, x, x);
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(x_eq_x));
  TS_ASSERT(d_solver->mkTrue() != x_eq_x);
  TS_ASSERT(d_solver->mkTrue() == d_solver->simplify(x_eq_x));
  Term x_eq_b = d_solver->mkTerm(EQUAL, x, b);
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(x_eq_b));
  TS_ASSERT(d_solver->mkTrue() != x_eq_b);
  TS_ASSERT(d_solver->mkTrue() != d_solver->simplify(x_eq_b));

  Term i1 = d_solver->mkConst(d_solver->getIntegerSort(), "i1");
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(i1));
  Term i2 = d_solver->mkTerm(MULT, i1, d_solver->mkReal("23"));
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(i2));
  TS_ASSERT(i1 != i2);
  TS_ASSERT(i1 != d_solver->simplify(i2));
  Term i3 = d_solver->mkTerm(PLUS, i1, d_solver->mkReal(0));
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(i3));
  TS_ASSERT(i1 != i3);
  TS_ASSERT(i1 == d_solver->simplify(i3));

  Datatype consList = consListSort.getDatatype();
  Term dt1 = d_solver->mkTerm(
      APPLY_CONSTRUCTOR,
      consList.getConstructorTerm("cons"),
      d_solver->mkReal(0),
      d_solver->mkTerm(APPLY_CONSTRUCTOR, consList.getConstructorTerm("nil")));
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(dt1));
  Term dt2 = d_solver->mkTerm(
      APPLY_SELECTOR, consList["cons"].getSelectorTerm("head"), dt1);
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(dt2));

  Term b1 = d_solver->mkVar(bvSort, "b1");
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(b1));
  Term b2 = d_solver->mkVar(bvSort, "b1");
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(b2));
  Term b3 = d_solver->mkVar(uSort, "b3");
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(b3));
  Term v1 = d_solver->mkConst(bvSort, "v1");
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(v1));
  Term v2 = d_solver->mkConst(d_solver->getIntegerSort(), "v2");
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(v2));
  Term f1 = d_solver->mkConst(funSort1, "f1");
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(f1));
  Term f2 = d_solver->mkConst(funSort2, "f2");
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(f2));
  d_solver->defineFunsRec({f1, f2}, {{b1, b2}, {b3}}, {v1, v2});
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(f1));
  TS_ASSERT_THROWS_NOTHING(d_solver->simplify(f2));
}

void SolverBlack::testCheckEntailed()
{
  d_solver->setOption("incremental", "false");
  TS_ASSERT_THROWS_NOTHING(d_solver->checkEntailed(d_solver->mkTrue()));
  TS_ASSERT_THROWS(d_solver->checkEntailed(d_solver->mkTrue()),
                   CVC4ApiException&);
}

void SolverBlack::testCheckEntailed1()
{
  Sort boolSort = d_solver->getBooleanSort();
  Term x = d_solver->mkConst(boolSort, "x");
  Term y = d_solver->mkConst(boolSort, "y");
  Term z = d_solver->mkTerm(AND, x, y);
  d_solver->setOption("incremental", "true");
  TS_ASSERT_THROWS_NOTHING(d_solver->checkEntailed(d_solver->mkTrue()));
  TS_ASSERT_THROWS(d_solver->checkEntailed(Term()), CVC4ApiException&);
  TS_ASSERT_THROWS_NOTHING(d_solver->checkEntailed(d_solver->mkTrue()));
  TS_ASSERT_THROWS_NOTHING(d_solver->checkEntailed(z));
}

void SolverBlack::testCheckEntailed2()
{
  d_solver->setOption("incremental", "true");

  Sort uSort = d_solver->mkUninterpretedSort("u");
  Sort intSort = d_solver->getIntegerSort();
  Sort boolSort = d_solver->getBooleanSort();
  Sort uToIntSort = d_solver->mkFunctionSort(uSort, intSort);
  Sort intPredSort = d_solver->mkFunctionSort(intSort, boolSort);

  Term n = Term();
  // Constants
  Term x = d_solver->mkConst(uSort, "x");
  Term y = d_solver->mkConst(uSort, "y");
  // Functions
  Term f = d_solver->mkConst(uToIntSort, "f");
  Term p = d_solver->mkConst(intPredSort, "p");
  // Values
  Term zero = d_solver->mkReal(0);
  Term one = d_solver->mkReal(1);
  // Terms
  Term f_x = d_solver->mkTerm(APPLY_UF, f, x);
  Term f_y = d_solver->mkTerm(APPLY_UF, f, y);
  Term sum = d_solver->mkTerm(PLUS, f_x, f_y);
  Term p_0 = d_solver->mkTerm(APPLY_UF, p, zero);
  Term p_f_y = d_solver->mkTerm(APPLY_UF, p, f_y);
  // Assertions
  Term assertions =
      d_solver->mkTerm(AND,
                       std::vector<Term>{
                           d_solver->mkTerm(LEQ, zero, f_x),  // 0 <= f(x)
                           d_solver->mkTerm(LEQ, zero, f_y),  // 0 <= f(y)
                           d_solver->mkTerm(LEQ, sum, one),  // f(x) + f(y) <= 1
                           p_0.notTerm(),                    // not p(0)
                           p_f_y                             // p(f(y))
                       });

  TS_ASSERT_THROWS_NOTHING(d_solver->checkEntailed(d_solver->mkTrue()));
  d_solver->assertFormula(assertions);
  TS_ASSERT_THROWS_NOTHING(
      d_solver->checkEntailed(d_solver->mkTerm(DISTINCT, x, y)));
  TS_ASSERT_THROWS_NOTHING(d_solver->checkEntailed(
      {d_solver->mkFalse(), d_solver->mkTerm(DISTINCT, x, y)}));
  TS_ASSERT_THROWS(d_solver->checkEntailed(n), CVC4ApiException&);
  TS_ASSERT_THROWS(
      d_solver->checkEntailed({n, d_solver->mkTerm(DISTINCT, x, y)}),
      CVC4ApiException&);
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

void SolverBlack::testResetAssertions()
{
  d_solver->setOption("incremental", "true");

  Sort bvSort = d_solver->mkBitVectorSort(4);
  Term one = d_solver->mkBitVector(4, 1);
  Term x = d_solver->mkConst(bvSort, "x");
  Term ule = d_solver->mkTerm(BITVECTOR_ULE, x, one);
  Term srem = d_solver->mkTerm(BITVECTOR_SREM, one, x);
  d_solver->push(4);
  Term slt = d_solver->mkTerm(BITVECTOR_SLT, srem, one);
  d_solver->resetAssertions();
  d_solver->checkSatAssuming({slt, ule});
}

void SolverBlack::testMkSygusVar()
{
  Sort boolSort = d_solver->getBooleanSort();
  Sort intSort = d_solver->getIntegerSort();
  Sort funSort = d_solver->mkFunctionSort(intSort, boolSort);

  TS_ASSERT_THROWS_NOTHING(d_solver->mkSygusVar(boolSort));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkSygusVar(funSort));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkSygusVar(boolSort, std::string("b")));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkSygusVar(funSort, ""));
  TS_ASSERT_THROWS(d_solver->mkSygusVar(Sort()), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkSygusVar(d_solver->getNullSort(), "a"),
                   CVC4ApiException&);
}

void SolverBlack::testMkSygusGrammar()
{
  Term nullTerm;
  Term boolTerm = d_solver->mkBoolean(true);
  Term intTerm = d_solver->mkReal(1);

  TS_ASSERT_THROWS_NOTHING(d_solver->mkSygusGrammar({}, {intTerm}));
  TS_ASSERT_THROWS_NOTHING(d_solver->mkSygusGrammar({boolTerm}, {intTerm}));
  TS_ASSERT_THROWS(d_solver->mkSygusGrammar({}, {}), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkSygusGrammar({}, {nullTerm}), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->mkSygusGrammar({nullTerm}, {intTerm}),
                   CVC4ApiException&);
}

void SolverBlack::testSynthFun()
{
  Sort null = d_solver->getNullSort();
  Sort boolean = d_solver->getBooleanSort();
  Sort integer = d_solver->getIntegerSort();
  Sort boolToBool = d_solver->mkFunctionSort(boolean, boolean);

  Term nullTerm;
  Term x = d_solver->mkVar(boolean);

  Term start1 = d_solver->mkVar(boolean);
  Term start2 = d_solver->mkVar(integer);

  Grammar g1 = d_solver->mkSygusGrammar({x}, {start1});
  g1.addRule(start1, d_solver->mkBoolean(false));

  Grammar g2 = d_solver->mkSygusGrammar({x}, {start2});
  g2.addRule(start2, d_solver->mkReal(0));

  TS_ASSERT_THROWS_NOTHING(d_solver->synthFun("", {}, boolean));
  TS_ASSERT_THROWS_NOTHING(d_solver->synthFun("f1", {x}, boolean));
  TS_ASSERT_THROWS_NOTHING(d_solver->synthFun("f2", {x}, boolean, g1));

  TS_ASSERT_THROWS(d_solver->synthFun("f3", {nullTerm}, boolean),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->synthFun("f4", {}, null), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->synthFun("f5", {}, boolToBool), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->synthFun("f6", {x}, boolean, g2),
                   CVC4ApiException&);
}

void SolverBlack::testSynthInv()
{
  Sort boolean = d_solver->getBooleanSort();
  Sort integer = d_solver->getIntegerSort();

  Term nullTerm;
  Term x = d_solver->mkVar(boolean);

  Term start1 = d_solver->mkVar(boolean);
  Term start2 = d_solver->mkVar(integer);

  Grammar g1 = d_solver->mkSygusGrammar({x}, {start1});
  g1.addRule(start1, d_solver->mkBoolean(false));

  Grammar g2 = d_solver->mkSygusGrammar({x}, {start2});
  g2.addRule(start2, d_solver->mkReal(0));

  TS_ASSERT_THROWS_NOTHING(d_solver->synthInv("", {}));
  TS_ASSERT_THROWS_NOTHING(d_solver->synthInv("i1", {x}));
  TS_ASSERT_THROWS_NOTHING(d_solver->synthInv("i2", {x}, g1));

  TS_ASSERT_THROWS(d_solver->synthInv("i3", {nullTerm}), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->synthInv("i4", {x}, g2), CVC4ApiException&);
}

void SolverBlack::testAddSygusConstraint()
{
  Term nullTerm;
  Term boolTerm = d_solver->mkBoolean(true);
  Term intTerm = d_solver->mkReal(1);

  TS_ASSERT_THROWS_NOTHING(d_solver->addSygusConstraint(boolTerm));
  TS_ASSERT_THROWS(d_solver->addSygusConstraint(nullTerm), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->addSygusConstraint(intTerm), CVC4ApiException&);
}

void SolverBlack::testAddSygusInvConstraint()
{
  Sort boolean = d_solver->getBooleanSort();
  Sort real = d_solver->getRealSort();

  Term nullTerm;
  Term intTerm = d_solver->mkReal(1);

  Term inv = d_solver->declareFun("inv", {real}, boolean);
  Term pre = d_solver->declareFun("pre", {real}, boolean);
  Term trans = d_solver->declareFun("trans", {real, real}, boolean);
  Term post = d_solver->declareFun("post", {real}, boolean);

  Term inv1 = d_solver->declareFun("inv1", {real}, real);

  Term trans1 = d_solver->declareFun("trans1", {boolean, real}, boolean);
  Term trans2 = d_solver->declareFun("trans2", {real, boolean}, boolean);
  Term trans3 = d_solver->declareFun("trans3", {real, real}, real);

  TS_ASSERT_THROWS_NOTHING(
      d_solver->addSygusInvConstraint(inv, pre, trans, post));

  TS_ASSERT_THROWS(d_solver->addSygusInvConstraint(nullTerm, pre, trans, post),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->addSygusInvConstraint(inv, nullTerm, trans, post),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->addSygusInvConstraint(inv, pre, nullTerm, post),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->addSygusInvConstraint(inv, pre, trans, nullTerm),
                   CVC4ApiException&);

  TS_ASSERT_THROWS(d_solver->addSygusInvConstraint(intTerm, pre, trans, post),
                   CVC4ApiException&);

  TS_ASSERT_THROWS(d_solver->addSygusInvConstraint(inv1, pre, trans, post),
                   CVC4ApiException&);

  TS_ASSERT_THROWS(d_solver->addSygusInvConstraint(inv, trans, trans, post),
                   CVC4ApiException&);

  TS_ASSERT_THROWS(d_solver->addSygusInvConstraint(inv, pre, intTerm, post),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->addSygusInvConstraint(inv, pre, pre, post),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->addSygusInvConstraint(inv, pre, trans1, post),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->addSygusInvConstraint(inv, pre, trans2, post),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->addSygusInvConstraint(inv, pre, trans3, post),
                   CVC4ApiException&);

  TS_ASSERT_THROWS(d_solver->addSygusInvConstraint(inv, pre, trans, trans),
                   CVC4ApiException&);
}

void SolverBlack::testGetSynthSolution()
{
  d_solver->setOption("lang", "sygus2");
  d_solver->setOption("incremental", "false");

  Term nullTerm;
  Term x = d_solver->mkBoolean(false);
  Term f = d_solver->synthFun("f", {}, d_solver->getBooleanSort());

  TS_ASSERT_THROWS(d_solver->getSynthSolution(f), CVC4ApiException&);

  d_solver->checkSynth();

  TS_ASSERT_THROWS_NOTHING(d_solver->getSynthSolution(f));
  TS_ASSERT_THROWS_NOTHING(d_solver->getSynthSolution(f));

  TS_ASSERT_THROWS(d_solver->getSynthSolution(nullTerm), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->getSynthSolution(x), CVC4ApiException&);
}

void SolverBlack::testGetSynthSolutions()
{
  d_solver->setOption("lang", "sygus2");
  d_solver->setOption("incremental", "false");

  Term nullTerm;
  Term x = d_solver->mkBoolean(false);
  Term f = d_solver->synthFun("f", {}, d_solver->getBooleanSort());

  TS_ASSERT_THROWS(d_solver->getSynthSolutions({}), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->getSynthSolutions({f}), CVC4ApiException&);

  d_solver->checkSynth();

  TS_ASSERT_THROWS_NOTHING(d_solver->getSynthSolutions({f}));
  TS_ASSERT_THROWS_NOTHING(d_solver->getSynthSolutions({f, f}));

  TS_ASSERT_THROWS(d_solver->getSynthSolutions({}), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->getSynthSolutions({nullTerm}), CVC4ApiException&);
  TS_ASSERT_THROWS(d_solver->getSynthSolutions({x}), CVC4ApiException&);
}
