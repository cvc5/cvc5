/*********************                                                        */
/*! \file solver_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Andres Noetzli, Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the Solver class of the  C++ API.
 **
 ** Black box testing of the Solver class of the  C++ API.
 **/

#include "base/configuration.h"
#include "test_api.h"

namespace CVC4 {

using namespace api;

namespace test {

class TestApiSolverBlack : public TestApi
{
};

TEST_F(TestApiSolverBlack, recoverableException)
{
  d_solver.setOption("produce-models", "true");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x).notTerm());
  ASSERT_THROW(d_solver.getValue(x), CVC4ApiRecoverableException);
}

TEST_F(TestApiSolverBlack, supportsFloatingPoint)
{
  if (d_solver.supportsFloatingPoint())
  {
    ASSERT_NO_THROW(d_solver.mkRoundingMode(ROUND_NEAREST_TIES_TO_EVEN));
  }
  else
  {
    ASSERT_THROW(d_solver.mkRoundingMode(ROUND_NEAREST_TIES_TO_EVEN),
                 CVC4ApiException);
  }
}

TEST_F(TestApiSolverBlack, getBooleanSort)
{
  ASSERT_NO_THROW(d_solver.getBooleanSort());
}

TEST_F(TestApiSolverBlack, getIntegerSort)
{
  ASSERT_NO_THROW(d_solver.getIntegerSort());
}

TEST_F(TestApiSolverBlack, getNullSort)
{
  ASSERT_NO_THROW(d_solver.getNullSort());
}

TEST_F(TestApiSolverBlack, getRealSort)
{
  ASSERT_NO_THROW(d_solver.getRealSort());
}

TEST_F(TestApiSolverBlack, getRegExpSort)
{
  ASSERT_NO_THROW(d_solver.getRegExpSort());
}

TEST_F(TestApiSolverBlack, getStringSort)
{
  ASSERT_NO_THROW(d_solver.getStringSort());
}

TEST_F(TestApiSolverBlack, getRoundingModeSort)
{
  if (d_solver.supportsFloatingPoint())
  {
    ASSERT_NO_THROW(d_solver.getRoundingModeSort());
  }
  else
  {
    ASSERT_THROW(d_solver.getRoundingModeSort(), CVC4ApiException);
  }
}

TEST_F(TestApiSolverBlack, mkArraySort)
{
  Sort boolSort = d_solver.getBooleanSort();
  Sort intSort = d_solver.getIntegerSort();
  Sort realSort = d_solver.getRealSort();
  Sort bvSort = d_solver.mkBitVectorSort(32);
  ASSERT_NO_THROW(d_solver.mkArraySort(boolSort, boolSort));
  ASSERT_NO_THROW(d_solver.mkArraySort(intSort, intSort));
  ASSERT_NO_THROW(d_solver.mkArraySort(realSort, realSort));
  ASSERT_NO_THROW(d_solver.mkArraySort(bvSort, bvSort));
  ASSERT_NO_THROW(d_solver.mkArraySort(boolSort, intSort));
  ASSERT_NO_THROW(d_solver.mkArraySort(realSort, bvSort));

  if (d_solver.supportsFloatingPoint())
  {
    Sort fpSort = d_solver.mkFloatingPointSort(3, 5);
    ASSERT_NO_THROW(d_solver.mkArraySort(fpSort, fpSort));
    ASSERT_NO_THROW(d_solver.mkArraySort(bvSort, fpSort));
  }

  Solver slv;
  ASSERT_THROW(slv.mkArraySort(boolSort, boolSort), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkBitVectorSort)
{
  ASSERT_NO_THROW(d_solver.mkBitVectorSort(32));
  ASSERT_THROW(d_solver.mkBitVectorSort(0), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkFloatingPointSort)
{
  if (d_solver.supportsFloatingPoint())
  {
    ASSERT_NO_THROW(d_solver.mkFloatingPointSort(4, 8));
    ASSERT_THROW(d_solver.mkFloatingPointSort(0, 8), CVC4ApiException);
    ASSERT_THROW(d_solver.mkFloatingPointSort(4, 0), CVC4ApiException);
  }
  else
  {
    ASSERT_THROW(d_solver.mkFloatingPointSort(4, 8), CVC4ApiException);
  }
}

TEST_F(TestApiSolverBlack, mkDatatypeSort)
{
  DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_solver.getIntegerSort());
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  ASSERT_NO_THROW(d_solver.mkDatatypeSort(dtypeSpec));

  Solver slv;
  ASSERT_THROW(slv.mkDatatypeSort(dtypeSpec), CVC4ApiException);

  DatatypeDecl throwsDtypeSpec = d_solver.mkDatatypeDecl("list");
  ASSERT_THROW(d_solver.mkDatatypeSort(throwsDtypeSpec), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkDatatypeSorts)
{
  Solver slv;

  DatatypeDecl dtypeSpec1 = d_solver.mkDatatypeDecl("list1");
  DatatypeConstructorDecl cons1 = d_solver.mkDatatypeConstructorDecl("cons1");
  cons1.addSelector("head1", d_solver.getIntegerSort());
  dtypeSpec1.addConstructor(cons1);
  DatatypeConstructorDecl nil1 = d_solver.mkDatatypeConstructorDecl("nil1");
  dtypeSpec1.addConstructor(nil1);
  DatatypeDecl dtypeSpec2 = d_solver.mkDatatypeDecl("list2");
  DatatypeConstructorDecl cons2 = d_solver.mkDatatypeConstructorDecl("cons2");
  cons2.addSelector("head2", d_solver.getIntegerSort());
  dtypeSpec2.addConstructor(cons2);
  DatatypeConstructorDecl nil2 = d_solver.mkDatatypeConstructorDecl("nil2");
  dtypeSpec2.addConstructor(nil2);
  std::vector<DatatypeDecl> decls = {dtypeSpec1, dtypeSpec2};
  ASSERT_NO_THROW(d_solver.mkDatatypeSorts(decls));

  ASSERT_THROW(slv.mkDatatypeSorts(decls), CVC4ApiException);

  DatatypeDecl throwsDtypeSpec = d_solver.mkDatatypeDecl("list");
  std::vector<DatatypeDecl> throwsDecls = {throwsDtypeSpec};
  ASSERT_THROW(d_solver.mkDatatypeSorts(throwsDecls), CVC4ApiException);

  /* with unresolved sorts */
  Sort unresList = d_solver.mkUninterpretedSort("ulist");
  std::set<Sort> unresSorts = {unresList};
  DatatypeDecl ulist = d_solver.mkDatatypeDecl("ulist");
  DatatypeConstructorDecl ucons = d_solver.mkDatatypeConstructorDecl("ucons");
  ucons.addSelector("car", unresList);
  ucons.addSelector("cdr", unresList);
  ulist.addConstructor(ucons);
  DatatypeConstructorDecl unil = d_solver.mkDatatypeConstructorDecl("unil");
  ulist.addConstructor(unil);
  std::vector<DatatypeDecl> udecls = {ulist};
  ASSERT_NO_THROW(d_solver.mkDatatypeSorts(udecls, unresSorts));

  ASSERT_THROW(slv.mkDatatypeSorts(udecls, unresSorts), CVC4ApiException);

  /* Note: More tests are in datatype_api_black. */
}

TEST_F(TestApiSolverBlack, mkFunctionSort)
{
  ASSERT_NO_THROW(d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                          d_solver.getIntegerSort()));
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  ASSERT_THROW(d_solver.mkFunctionSort(funSort, d_solver.getIntegerSort()),
               CVC4ApiException);
  ASSERT_THROW(d_solver.mkFunctionSort(d_solver.getIntegerSort(), funSort),
               CVC4ApiException);
  ASSERT_NO_THROW(d_solver.mkFunctionSort(
      {d_solver.mkUninterpretedSort("u"), d_solver.getIntegerSort()},
      d_solver.getIntegerSort()));
  Sort funSort2 = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                          d_solver.getIntegerSort());
  ASSERT_THROW(
      d_solver.mkFunctionSort({funSort2, d_solver.mkUninterpretedSort("u")},
                              d_solver.getIntegerSort()),
      CVC4ApiException);
  ASSERT_THROW(d_solver.mkFunctionSort({d_solver.getIntegerSort(),
                                        d_solver.mkUninterpretedSort("u")},
                                       funSort2),
               CVC4ApiException);

  Solver slv;
  ASSERT_THROW(slv.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                  d_solver.getIntegerSort()),
               CVC4ApiException);
  ASSERT_THROW(slv.mkFunctionSort(slv.mkUninterpretedSort("u"),
                                  d_solver.getIntegerSort()),
               CVC4ApiException);
  std::vector<Sort> sorts1 = {d_solver.getBooleanSort(),
                              slv.getIntegerSort(),
                              d_solver.getIntegerSort()};
  std::vector<Sort> sorts2 = {slv.getBooleanSort(), slv.getIntegerSort()};
  ASSERT_NO_THROW(slv.mkFunctionSort(sorts2, slv.getIntegerSort()));
  ASSERT_THROW(slv.mkFunctionSort(sorts1, slv.getIntegerSort()),
               CVC4ApiException);
  ASSERT_THROW(slv.mkFunctionSort(sorts2, d_solver.getIntegerSort()),
               CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkParamSort)
{
  ASSERT_NO_THROW(d_solver.mkParamSort("T"));
  ASSERT_NO_THROW(d_solver.mkParamSort(""));
}

TEST_F(TestApiSolverBlack, mkPredicateSort)
{
  ASSERT_NO_THROW(d_solver.mkPredicateSort({d_solver.getIntegerSort()}));
  ASSERT_THROW(d_solver.mkPredicateSort({}), CVC4ApiException);
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  ASSERT_THROW(d_solver.mkPredicateSort({d_solver.getIntegerSort(), funSort}),
               CVC4ApiException);

  Solver slv;
  ASSERT_THROW(slv.mkPredicateSort({d_solver.getIntegerSort()}),
               CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkRecordSort)
{
  std::vector<std::pair<std::string, Sort>> fields = {
      std::make_pair("b", d_solver.getBooleanSort()),
      std::make_pair("bv", d_solver.mkBitVectorSort(8)),
      std::make_pair("i", d_solver.getIntegerSort())};
  std::vector<std::pair<std::string, Sort>> empty;
  ASSERT_NO_THROW(d_solver.mkRecordSort(fields));
  ASSERT_NO_THROW(d_solver.mkRecordSort(empty));
  Sort recSort = d_solver.mkRecordSort(fields);
  ASSERT_NO_THROW(recSort.getDatatype());

  Solver slv;
  ASSERT_THROW(slv.mkRecordSort(fields), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkSetSort)
{
  ASSERT_NO_THROW(d_solver.mkSetSort(d_solver.getBooleanSort()));
  ASSERT_NO_THROW(d_solver.mkSetSort(d_solver.getIntegerSort()));
  ASSERT_NO_THROW(d_solver.mkSetSort(d_solver.mkBitVectorSort(4)));
  Solver slv;
  ASSERT_THROW(slv.mkSetSort(d_solver.mkBitVectorSort(4)), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkBagSort)
{
  ASSERT_NO_THROW(d_solver.mkBagSort(d_solver.getBooleanSort()));
  ASSERT_NO_THROW(d_solver.mkBagSort(d_solver.getIntegerSort()));
  ASSERT_NO_THROW(d_solver.mkBagSort(d_solver.mkBitVectorSort(4)));
  Solver slv;
  ASSERT_THROW(slv.mkBagSort(d_solver.mkBitVectorSort(4)), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkSequenceSort)
{
  ASSERT_NO_THROW(d_solver.mkSequenceSort(d_solver.getBooleanSort()));
  ASSERT_NO_THROW(d_solver.mkSequenceSort(
      d_solver.mkSequenceSort(d_solver.getIntegerSort())));
  Solver slv;
  ASSERT_THROW(slv.mkSequenceSort(d_solver.getIntegerSort()), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkUninterpretedSort)
{
  ASSERT_NO_THROW(d_solver.mkUninterpretedSort("u"));
  ASSERT_NO_THROW(d_solver.mkUninterpretedSort(""));
}

TEST_F(TestApiSolverBlack, mkSortConstructorSort)
{
  ASSERT_NO_THROW(d_solver.mkSortConstructorSort("s", 2));
  ASSERT_NO_THROW(d_solver.mkSortConstructorSort("", 2));
  ASSERT_THROW(d_solver.mkSortConstructorSort("", 0), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkTupleSort)
{
  ASSERT_NO_THROW(d_solver.mkTupleSort({d_solver.getIntegerSort()}));
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  ASSERT_THROW(d_solver.mkTupleSort({d_solver.getIntegerSort(), funSort}),
               CVC4ApiException);

  Solver slv;
  ASSERT_THROW(slv.mkTupleSort({d_solver.getIntegerSort()}), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkBitVector)
{
  uint32_t size0 = 0, size1 = 8, size2 = 32, val1 = 2;
  uint64_t val2 = 2;
  ASSERT_NO_THROW(d_solver.mkBitVector(size1, val1));
  ASSERT_NO_THROW(d_solver.mkBitVector(size2, val2));
  ASSERT_NO_THROW(d_solver.mkBitVector("1010", 2));
  ASSERT_NO_THROW(d_solver.mkBitVector("1010", 10));
  ASSERT_NO_THROW(d_solver.mkBitVector("1234", 10));
  ASSERT_NO_THROW(d_solver.mkBitVector("1010", 16));
  ASSERT_NO_THROW(d_solver.mkBitVector("a09f", 16));
  ASSERT_NO_THROW(d_solver.mkBitVector(8, "-127", 10));
  ASSERT_THROW(d_solver.mkBitVector(size0, val1), CVC4ApiException);
  ASSERT_THROW(d_solver.mkBitVector(size0, val2), CVC4ApiException);
  ASSERT_THROW(d_solver.mkBitVector("", 2), CVC4ApiException);
  ASSERT_THROW(d_solver.mkBitVector("10", 3), CVC4ApiException);
  ASSERT_THROW(d_solver.mkBitVector("20", 2), CVC4ApiException);
  ASSERT_THROW(d_solver.mkBitVector(8, "101010101", 2), CVC4ApiException);
  ASSERT_THROW(d_solver.mkBitVector(8, "-256", 10), CVC4ApiException);
  EXPECT_EQ(d_solver.mkBitVector("1010", 2), d_solver.mkBitVector("10", 10));
  EXPECT_EQ(d_solver.mkBitVector("1010", 2), d_solver.mkBitVector("a", 16));
  EXPECT_EQ(d_solver.mkBitVector(8, "01010101", 2).toString(), "#b01010101");
  EXPECT_EQ(d_solver.mkBitVector(8, "F", 16).toString(), "#b00001111");
  EXPECT_EQ(d_solver.mkBitVector(8, "-1", 10),
            d_solver.mkBitVector(8, "FF", 16));
}

TEST_F(TestApiSolverBlack, mkVar)
{
  Sort boolSort = d_solver.getBooleanSort();
  Sort intSort = d_solver.getIntegerSort();
  Sort funSort = d_solver.mkFunctionSort(intSort, boolSort);
  ASSERT_NO_THROW(d_solver.mkVar(boolSort));
  ASSERT_NO_THROW(d_solver.mkVar(funSort));
  ASSERT_NO_THROW(d_solver.mkVar(boolSort, std::string("b")));
  ASSERT_NO_THROW(d_solver.mkVar(funSort, ""));
  ASSERT_THROW(d_solver.mkVar(Sort()), CVC4ApiException);
  ASSERT_THROW(d_solver.mkVar(Sort(), "a"), CVC4ApiException);
  Solver slv;
  ASSERT_THROW(slv.mkVar(boolSort, "x"), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkBoolean)
{
  ASSERT_NO_THROW(d_solver.mkBoolean(true));
  ASSERT_NO_THROW(d_solver.mkBoolean(false));
}

TEST_F(TestApiSolverBlack, mkRoundingMode)
{
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    ASSERT_NO_THROW(d_solver.mkRoundingMode(RoundingMode::ROUND_TOWARD_ZERO));
  }
  else
  {
    ASSERT_THROW(d_solver.mkRoundingMode(RoundingMode::ROUND_TOWARD_ZERO),
                 CVC4ApiException);
  }
}

TEST_F(TestApiSolverBlack, mkUninterpretedConst)
{
  ASSERT_NO_THROW(d_solver.mkUninterpretedConst(d_solver.getBooleanSort(), 1));
  ASSERT_THROW(d_solver.mkUninterpretedConst(Sort(), 1), CVC4ApiException);
  Solver slv;
  ASSERT_THROW(slv.mkUninterpretedConst(d_solver.getBooleanSort(), 1),
               CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkAbstractValue)
{
  ASSERT_NO_THROW(d_solver.mkAbstractValue(std::string("1")));
  ASSERT_THROW(d_solver.mkAbstractValue(std::string("0")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkAbstractValue(std::string("-1")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkAbstractValue(std::string("1.2")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkAbstractValue("1/2"), CVC4ApiException);
  ASSERT_THROW(d_solver.mkAbstractValue("asdf"), CVC4ApiException);

  ASSERT_NO_THROW(d_solver.mkAbstractValue((uint32_t)1));
  ASSERT_NO_THROW(d_solver.mkAbstractValue((int32_t)1));
  ASSERT_NO_THROW(d_solver.mkAbstractValue((uint64_t)1));
  ASSERT_NO_THROW(d_solver.mkAbstractValue((int64_t)1));
  ASSERT_NO_THROW(d_solver.mkAbstractValue((int32_t)-1));
  ASSERT_NO_THROW(d_solver.mkAbstractValue((int64_t)-1));
  ASSERT_THROW(d_solver.mkAbstractValue(0), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkFloatingPoint)
{
  Term t1 = d_solver.mkBitVector(8);
  Term t2 = d_solver.mkBitVector(4);
  Term t3 = d_solver.mkInteger(2);
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    ASSERT_NO_THROW(d_solver.mkFloatingPoint(3, 5, t1));
  }
  else
  {
    ASSERT_THROW(d_solver.mkFloatingPoint(3, 5, t1), CVC4ApiException);
  }
  ASSERT_THROW(d_solver.mkFloatingPoint(0, 5, Term()), CVC4ApiException);
  ASSERT_THROW(d_solver.mkFloatingPoint(0, 5, t1), CVC4ApiException);
  ASSERT_THROW(d_solver.mkFloatingPoint(3, 0, t1), CVC4ApiException);
  ASSERT_THROW(d_solver.mkFloatingPoint(3, 5, t2), CVC4ApiException);
  ASSERT_THROW(d_solver.mkFloatingPoint(3, 5, t2), CVC4ApiException);

  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    Solver slv;
    ASSERT_THROW(slv.mkFloatingPoint(3, 5, t1), CVC4ApiException);
  }
}

TEST_F(TestApiSolverBlack, mkEmptySet)
{
  Solver slv;
  Sort s = d_solver.mkSetSort(d_solver.getBooleanSort());
  ASSERT_NO_THROW(d_solver.mkEmptySet(Sort()));
  ASSERT_NO_THROW(d_solver.mkEmptySet(s));
  ASSERT_THROW(d_solver.mkEmptySet(d_solver.getBooleanSort()),
               CVC4ApiException);
  ASSERT_THROW(slv.mkEmptySet(s), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkEmptyBag)
{
  Solver slv;
  Sort s = d_solver.mkBagSort(d_solver.getBooleanSort());
  ASSERT_NO_THROW(d_solver.mkEmptyBag(Sort()));
  ASSERT_NO_THROW(d_solver.mkEmptyBag(s));
  ASSERT_THROW(d_solver.mkEmptyBag(d_solver.getBooleanSort()),
               CVC4ApiException);
  ASSERT_THROW(slv.mkEmptyBag(s), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkEmptySequence)
{
  Solver slv;
  Sort s = d_solver.mkSequenceSort(d_solver.getBooleanSort());
  ASSERT_NO_THROW(d_solver.mkEmptySequence(s));
  ASSERT_NO_THROW(d_solver.mkEmptySequence(d_solver.getBooleanSort()));
  ASSERT_THROW(slv.mkEmptySequence(s), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkFalse)
{
  ASSERT_NO_THROW(d_solver.mkFalse());
  ASSERT_NO_THROW(d_solver.mkFalse());
}

TEST_F(TestApiSolverBlack, mkNaN)
{
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    ASSERT_NO_THROW(d_solver.mkNaN(3, 5));
  }
  else
  {
    ASSERT_THROW(d_solver.mkNaN(3, 5), CVC4ApiException);
  }
}

TEST_F(TestApiSolverBlack, mkNegZero)
{
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    ASSERT_NO_THROW(d_solver.mkNegZero(3, 5));
  }
  else
  {
    ASSERT_THROW(d_solver.mkNegZero(3, 5), CVC4ApiException);
  }
}

TEST_F(TestApiSolverBlack, mkNegInf)
{
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    ASSERT_NO_THROW(d_solver.mkNegInf(3, 5));
  }
  else
  {
    ASSERT_THROW(d_solver.mkNegInf(3, 5), CVC4ApiException);
  }
}

TEST_F(TestApiSolverBlack, mkPosInf)
{
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    ASSERT_NO_THROW(d_solver.mkPosInf(3, 5));
  }
  else
  {
    ASSERT_THROW(d_solver.mkPosInf(3, 5), CVC4ApiException);
  }
}

TEST_F(TestApiSolverBlack, mkPosZero)
{
  if (CVC4::Configuration::isBuiltWithSymFPU())
  {
    ASSERT_NO_THROW(d_solver.mkPosZero(3, 5));
  }
  else
  {
    ASSERT_THROW(d_solver.mkPosZero(3, 5), CVC4ApiException);
  }
}

TEST_F(TestApiSolverBlack, mkOp)
{
  // mkOp(Kind kind, Kind k)
  ASSERT_THROW(d_solver.mkOp(BITVECTOR_EXTRACT, EQUAL), CVC4ApiException);

  // mkOp(Kind kind, const std::string& arg)
  ASSERT_NO_THROW(d_solver.mkOp(RECORD_UPDATE, "asdf"));
  ASSERT_NO_THROW(d_solver.mkOp(DIVISIBLE, "2147483648"));
  ASSERT_THROW(d_solver.mkOp(BITVECTOR_EXTRACT, "asdf"), CVC4ApiException);

  // mkOp(Kind kind, uint32_t arg)
  ASSERT_NO_THROW(d_solver.mkOp(DIVISIBLE, 1));
  ASSERT_NO_THROW(d_solver.mkOp(BITVECTOR_ROTATE_LEFT, 1));
  ASSERT_NO_THROW(d_solver.mkOp(BITVECTOR_ROTATE_RIGHT, 1));
  ASSERT_THROW(d_solver.mkOp(BITVECTOR_EXTRACT, 1), CVC4ApiException);

  // mkOp(Kind kind, uint32_t arg1, uint32_t arg2)
  ASSERT_NO_THROW(d_solver.mkOp(BITVECTOR_EXTRACT, 1, 1));
  ASSERT_THROW(d_solver.mkOp(DIVISIBLE, 1, 2), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkPi) { ASSERT_NO_THROW(d_solver.mkPi()); }

TEST_F(TestApiSolverBlack, mkInteger)
{
  ASSERT_NO_THROW(d_solver.mkInteger("123"));
  ASSERT_THROW(d_solver.mkInteger("1.23"), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger("1/23"), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger("12/3"), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger(".2"), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger("2."), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger(""), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger("asdf"), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger("1.2/3"), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger("."), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger("/"), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger("2/"), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger("/2"), CVC4ApiException);

  ASSERT_NO_THROW(d_solver.mkReal(std::string("123")));
  ASSERT_THROW(d_solver.mkInteger(std::string("1.23")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("1/23")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("12/3")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string(".2")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("2.")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("asdf")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("1.2/3")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string(".")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("/")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("2/")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("/2")), CVC4ApiException);

  int32_t val1 = 1;
  int64_t val2 = -1;
  uint32_t val3 = 1;
  uint64_t val4 = -1;
  ASSERT_NO_THROW(d_solver.mkInteger(val1));
  ASSERT_NO_THROW(d_solver.mkInteger(val2));
  ASSERT_NO_THROW(d_solver.mkInteger(val3));
  ASSERT_NO_THROW(d_solver.mkInteger(val4));
  ASSERT_NO_THROW(d_solver.mkInteger(val4));
}

TEST_F(TestApiSolverBlack, mkReal)
{
  ASSERT_NO_THROW(d_solver.mkReal("123"));
  ASSERT_NO_THROW(d_solver.mkReal("1.23"));
  ASSERT_NO_THROW(d_solver.mkReal("1/23"));
  ASSERT_NO_THROW(d_solver.mkReal("12/3"));
  ASSERT_NO_THROW(d_solver.mkReal(".2"));
  ASSERT_NO_THROW(d_solver.mkReal("2."));
  ASSERT_THROW(d_solver.mkReal(""), CVC4ApiException);
  ASSERT_THROW(d_solver.mkReal("asdf"), CVC4ApiException);
  ASSERT_THROW(d_solver.mkReal("1.2/3"), CVC4ApiException);
  ASSERT_THROW(d_solver.mkReal("."), CVC4ApiException);
  ASSERT_THROW(d_solver.mkReal("/"), CVC4ApiException);
  ASSERT_THROW(d_solver.mkReal("2/"), CVC4ApiException);
  ASSERT_THROW(d_solver.mkReal("/2"), CVC4ApiException);

  ASSERT_NO_THROW(d_solver.mkReal(std::string("123")));
  ASSERT_NO_THROW(d_solver.mkReal(std::string("1.23")));
  ASSERT_NO_THROW(d_solver.mkReal(std::string("1/23")));
  ASSERT_NO_THROW(d_solver.mkReal(std::string("12/3")));
  ASSERT_NO_THROW(d_solver.mkReal(std::string(".2")));
  ASSERT_NO_THROW(d_solver.mkReal(std::string("2.")));
  ASSERT_THROW(d_solver.mkReal(std::string("")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkReal(std::string("asdf")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkReal(std::string("1.2/3")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkReal(std::string(".")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkReal(std::string("/")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkReal(std::string("2/")), CVC4ApiException);
  ASSERT_THROW(d_solver.mkReal(std::string("/2")), CVC4ApiException);

  int32_t val1 = 1;
  int64_t val2 = -1;
  uint32_t val3 = 1;
  uint64_t val4 = -1;
  ASSERT_NO_THROW(d_solver.mkReal(val1));
  ASSERT_NO_THROW(d_solver.mkReal(val2));
  ASSERT_NO_THROW(d_solver.mkReal(val3));
  ASSERT_NO_THROW(d_solver.mkReal(val4));
  ASSERT_NO_THROW(d_solver.mkReal(val4));
  ASSERT_NO_THROW(d_solver.mkReal(val1, val1));
  ASSERT_NO_THROW(d_solver.mkReal(val2, val2));
  ASSERT_NO_THROW(d_solver.mkReal(val3, val3));
  ASSERT_NO_THROW(d_solver.mkReal(val4, val4));
}

TEST_F(TestApiSolverBlack, mkRegexpEmpty)
{
  Sort strSort = d_solver.getStringSort();
  Term s = d_solver.mkConst(strSort, "s");
  ASSERT_NO_THROW(
      d_solver.mkTerm(STRING_IN_REGEXP, s, d_solver.mkRegexpEmpty()));
}

TEST_F(TestApiSolverBlack, mkRegexpSigma)
{
  Sort strSort = d_solver.getStringSort();
  Term s = d_solver.mkConst(strSort, "s");
  ASSERT_NO_THROW(
      d_solver.mkTerm(STRING_IN_REGEXP, s, d_solver.mkRegexpSigma()));
}

TEST_F(TestApiSolverBlack, mkSepNil)
{
  ASSERT_NO_THROW(d_solver.mkSepNil(d_solver.getBooleanSort()));
  ASSERT_THROW(d_solver.mkSepNil(Sort()), CVC4ApiException);
  Solver slv;
  ASSERT_THROW(slv.mkSepNil(d_solver.getIntegerSort()), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkString)
{
  ASSERT_NO_THROW(d_solver.mkString(""));
  ASSERT_NO_THROW(d_solver.mkString("asdfasdf"));
  EXPECT_EQ(d_solver.mkString("asdf\\nasdf").toString(),
            "\"asdf\\u{5c}nasdf\"");
  EXPECT_EQ(d_solver.mkString("asdf\\u{005c}nasdf", true).toString(),
            "\"asdf\\u{5c}nasdf\"");
}

TEST_F(TestApiSolverBlack, mkChar)
{
  ASSERT_NO_THROW(d_solver.mkChar(std::string("0123")));
  ASSERT_NO_THROW(d_solver.mkChar("aA"));
  ASSERT_THROW(d_solver.mkChar(""), CVC4ApiException);
  ASSERT_THROW(d_solver.mkChar("0g0"), CVC4ApiException);
  ASSERT_THROW(d_solver.mkChar("100000"), CVC4ApiException);
  EXPECT_EQ(d_solver.mkChar("abc"), d_solver.mkChar("ABC"));
}

TEST_F(TestApiSolverBlack, mkTerm)
{
  Sort bv32 = d_solver.mkBitVectorSort(32);
  Term a = d_solver.mkConst(bv32, "a");
  Term b = d_solver.mkConst(bv32, "b");
  std::vector<Term> v1 = {a, b};
  std::vector<Term> v2 = {a, Term()};
  std::vector<Term> v3 = {a, d_solver.mkTrue()};
  std::vector<Term> v4 = {d_solver.mkInteger(1), d_solver.mkInteger(2)};
  std::vector<Term> v5 = {d_solver.mkInteger(1), Term()};
  std::vector<Term> v6 = {};
  Solver slv;

  // mkTerm(Kind kind) const
  ASSERT_NO_THROW(d_solver.mkTerm(PI));
  ASSERT_NO_THROW(d_solver.mkTerm(REGEXP_EMPTY));
  ASSERT_NO_THROW(d_solver.mkTerm(REGEXP_SIGMA));
  ASSERT_THROW(d_solver.mkTerm(CONST_BITVECTOR), CVC4ApiException);

  // mkTerm(Kind kind, Term child) const
  ASSERT_NO_THROW(d_solver.mkTerm(NOT, d_solver.mkTrue()));
  ASSERT_THROW(d_solver.mkTerm(NOT, Term()), CVC4ApiException);
  ASSERT_THROW(d_solver.mkTerm(NOT, a), CVC4ApiException);
  ASSERT_THROW(slv.mkTerm(NOT, d_solver.mkTrue()), CVC4ApiException);

  // mkTerm(Kind kind, Term child1, Term child2) const
  ASSERT_NO_THROW(d_solver.mkTerm(EQUAL, a, b));
  ASSERT_THROW(d_solver.mkTerm(EQUAL, Term(), b), CVC4ApiException);
  ASSERT_THROW(d_solver.mkTerm(EQUAL, a, Term()), CVC4ApiException);
  ASSERT_THROW(d_solver.mkTerm(EQUAL, a, d_solver.mkTrue()), CVC4ApiException);
  ASSERT_THROW(slv.mkTerm(EQUAL, a, b), CVC4ApiException);

  // mkTerm(Kind kind, Term child1, Term child2, Term child3) const
  ASSERT_NO_THROW(d_solver.mkTerm(
      ITE, d_solver.mkTrue(), d_solver.mkTrue(), d_solver.mkTrue()));
  ASSERT_THROW(
      d_solver.mkTerm(ITE, Term(), d_solver.mkTrue(), d_solver.mkTrue()),
      CVC4ApiException);
  ASSERT_THROW(
      d_solver.mkTerm(ITE, d_solver.mkTrue(), Term(), d_solver.mkTrue()),
      CVC4ApiException);
  ASSERT_THROW(
      d_solver.mkTerm(ITE, d_solver.mkTrue(), d_solver.mkTrue(), Term()),
      CVC4ApiException);
  ASSERT_THROW(d_solver.mkTerm(ITE, d_solver.mkTrue(), d_solver.mkTrue(), b),
               CVC4ApiException);
  ASSERT_THROW(
      slv.mkTerm(ITE, d_solver.mkTrue(), d_solver.mkTrue(), d_solver.mkTrue()),
      CVC4ApiException);

  // mkTerm(Kind kind, const std::vector<Term>& children) const
  ASSERT_NO_THROW(d_solver.mkTerm(EQUAL, v1));
  ASSERT_THROW(d_solver.mkTerm(EQUAL, v2), CVC4ApiException);
  ASSERT_THROW(d_solver.mkTerm(EQUAL, v3), CVC4ApiException);
  ASSERT_THROW(d_solver.mkTerm(DISTINCT, v6), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkTermFromOp)
{
  Sort bv32 = d_solver.mkBitVectorSort(32);
  Term a = d_solver.mkConst(bv32, "a");
  Term b = d_solver.mkConst(bv32, "b");
  std::vector<Term> v1 = {d_solver.mkInteger(1), d_solver.mkInteger(2)};
  std::vector<Term> v2 = {d_solver.mkInteger(1), Term()};
  std::vector<Term> v3 = {};
  std::vector<Term> v4 = {d_solver.mkInteger(5)};
  Solver slv;

  // simple operator terms
  Op opterm1 = d_solver.mkOp(BITVECTOR_EXTRACT, 2, 1);
  Op opterm2 = d_solver.mkOp(DIVISIBLE, 1);

  // list datatype
  Sort sort = d_solver.mkParamSort("T");
  DatatypeDecl listDecl = d_solver.mkDatatypeDecl("paramlist", sort);
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  cons.addSelector("head", sort);
  cons.addSelectorSelf("tail");
  listDecl.addConstructor(cons);
  listDecl.addConstructor(nil);
  Sort listSort = d_solver.mkDatatypeSort(listDecl);
  Sort intListSort =
      listSort.instantiate(std::vector<Sort>{d_solver.getIntegerSort()});
  Term c = d_solver.mkConst(intListSort, "c");
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
  ASSERT_NO_THROW(d_solver.mkTerm(APPLY_CONSTRUCTOR, nilTerm1));
  ASSERT_NO_THROW(d_solver.mkTerm(APPLY_CONSTRUCTOR, nilTerm2));
  ASSERT_THROW(d_solver.mkTerm(APPLY_SELECTOR, nilTerm1), CVC4ApiException);
  ASSERT_THROW(d_solver.mkTerm(APPLY_SELECTOR, consTerm1), CVC4ApiException);
  ASSERT_THROW(d_solver.mkTerm(APPLY_CONSTRUCTOR, consTerm2), CVC4ApiException);
  ASSERT_THROW(d_solver.mkTerm(opterm1), CVC4ApiException);
  ASSERT_THROW(d_solver.mkTerm(APPLY_SELECTOR, headTerm1), CVC4ApiException);
  ASSERT_THROW(d_solver.mkTerm(opterm1), CVC4ApiException);
  ASSERT_THROW(slv.mkTerm(APPLY_CONSTRUCTOR, nilTerm1), CVC4ApiException);

  // mkTerm(Op op, Term child) const
  ASSERT_NO_THROW(d_solver.mkTerm(opterm1, a));
  ASSERT_NO_THROW(d_solver.mkTerm(opterm2, d_solver.mkInteger(1)));
  ASSERT_NO_THROW(d_solver.mkTerm(APPLY_SELECTOR, headTerm1, c));
  ASSERT_NO_THROW(d_solver.mkTerm(APPLY_SELECTOR, tailTerm2, c));
  ASSERT_THROW(d_solver.mkTerm(opterm2, a), CVC4ApiException);
  ASSERT_THROW(d_solver.mkTerm(opterm1, Term()), CVC4ApiException);
  ASSERT_THROW(
      d_solver.mkTerm(APPLY_CONSTRUCTOR, consTerm1, d_solver.mkInteger(0)),
      CVC4ApiException);
  ASSERT_THROW(slv.mkTerm(opterm1, a), CVC4ApiException);

  // mkTerm(Op op, Term child1, Term child2) const
  ASSERT_NO_THROW(
      d_solver.mkTerm(APPLY_CONSTRUCTOR,
                      consTerm1,
                      d_solver.mkInteger(0),
                      d_solver.mkTerm(APPLY_CONSTRUCTOR, nilTerm1)));
  ASSERT_THROW(
      d_solver.mkTerm(opterm2, d_solver.mkInteger(1), d_solver.mkInteger(2)),
      CVC4ApiException);
  ASSERT_THROW(d_solver.mkTerm(opterm1, a, b), CVC4ApiException);
  ASSERT_THROW(d_solver.mkTerm(opterm2, d_solver.mkInteger(1), Term()),
               CVC4ApiException);
  ASSERT_THROW(d_solver.mkTerm(opterm2, Term(), d_solver.mkInteger(1)),
               CVC4ApiException);
  ASSERT_THROW(slv.mkTerm(APPLY_CONSTRUCTOR,
                          consTerm1,
                          d_solver.mkInteger(0),
                          d_solver.mkTerm(APPLY_CONSTRUCTOR, nilTerm1)),
               CVC4ApiException);

  // mkTerm(Op op, Term child1, Term child2, Term child3) const
  ASSERT_THROW(d_solver.mkTerm(opterm1, a, b, a), CVC4ApiException);
  ASSERT_THROW(
      d_solver.mkTerm(
          opterm2, d_solver.mkInteger(1), d_solver.mkInteger(1), Term()),
      CVC4ApiException);

  // mkTerm(Op op, const std::vector<Term>& children) const
  ASSERT_NO_THROW(d_solver.mkTerm(opterm2, v4));
  ASSERT_THROW(d_solver.mkTerm(opterm2, v1), CVC4ApiException);
  ASSERT_THROW(d_solver.mkTerm(opterm2, v2), CVC4ApiException);
  ASSERT_THROW(d_solver.mkTerm(opterm2, v3), CVC4ApiException);
  ASSERT_THROW(slv.mkTerm(opterm2, v4), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkTrue)
{
  ASSERT_NO_THROW(d_solver.mkTrue());
  ASSERT_NO_THROW(d_solver.mkTrue());
}

TEST_F(TestApiSolverBlack, mkTuple)
{
  ASSERT_NO_THROW(d_solver.mkTuple({d_solver.mkBitVectorSort(3)},
                                   {d_solver.mkBitVector("101", 2)}));
  ASSERT_NO_THROW(
      d_solver.mkTuple({d_solver.getRealSort()}, {d_solver.mkInteger("5")}));

  ASSERT_THROW(d_solver.mkTuple({}, {d_solver.mkBitVector("101", 2)}),
               CVC4ApiException);
  ASSERT_THROW(d_solver.mkTuple({d_solver.mkBitVectorSort(4)},
                                {d_solver.mkBitVector("101", 2)}),
               CVC4ApiException);
  ASSERT_THROW(
      d_solver.mkTuple({d_solver.getIntegerSort()}, {d_solver.mkReal("5.3")}),
      CVC4ApiException);
  Solver slv;
  ASSERT_THROW(
      slv.mkTuple({d_solver.mkBitVectorSort(3)}, {slv.mkBitVector("101", 2)}),
      CVC4ApiException);
  ASSERT_THROW(
      slv.mkTuple({slv.mkBitVectorSort(3)}, {d_solver.mkBitVector("101", 2)}),
      CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkUniverseSet)
{
  ASSERT_NO_THROW(d_solver.mkUniverseSet(d_solver.getBooleanSort()));
  ASSERT_THROW(d_solver.mkUniverseSet(Sort()), CVC4ApiException);
  Solver slv;
  ASSERT_THROW(slv.mkUniverseSet(d_solver.getBooleanSort()), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkConst)
{
  Sort boolSort = d_solver.getBooleanSort();
  Sort intSort = d_solver.getIntegerSort();
  Sort funSort = d_solver.mkFunctionSort(intSort, boolSort);
  ASSERT_NO_THROW(d_solver.mkConst(boolSort));
  ASSERT_NO_THROW(d_solver.mkConst(funSort));
  ASSERT_NO_THROW(d_solver.mkConst(boolSort, std::string("b")));
  ASSERT_NO_THROW(d_solver.mkConst(intSort, std::string("i")));
  ASSERT_NO_THROW(d_solver.mkConst(funSort, "f"));
  ASSERT_NO_THROW(d_solver.mkConst(funSort, ""));
  ASSERT_THROW(d_solver.mkConst(Sort()), CVC4ApiException);
  ASSERT_THROW(d_solver.mkConst(Sort(), "a"), CVC4ApiException);

  Solver slv;
  ASSERT_THROW(slv.mkConst(boolSort), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkConstArray)
{
  Sort intSort = d_solver.getIntegerSort();
  Sort arrSort = d_solver.mkArraySort(intSort, intSort);
  Term zero = d_solver.mkInteger(0);
  Term constArr = d_solver.mkConstArray(arrSort, zero);

  ASSERT_NO_THROW(d_solver.mkConstArray(arrSort, zero));
  ASSERT_THROW(d_solver.mkConstArray(Sort(), zero), CVC4ApiException);
  ASSERT_THROW(d_solver.mkConstArray(arrSort, Term()), CVC4ApiException);
  ASSERT_THROW(d_solver.mkConstArray(arrSort, d_solver.mkBitVector(1, 1)),
               CVC4ApiException);
  ASSERT_THROW(d_solver.mkConstArray(intSort, zero), CVC4ApiException);
  Solver slv;
  Term zero2 = slv.mkInteger(0);
  Sort arrSort2 = slv.mkArraySort(slv.getIntegerSort(), slv.getIntegerSort());
  ASSERT_THROW(slv.mkConstArray(arrSort2, zero), CVC4ApiException);
  ASSERT_THROW(slv.mkConstArray(arrSort, zero2), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, declareDatatype)
{
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  std::vector<DatatypeConstructorDecl> ctors1 = {nil};
  ASSERT_NO_THROW(d_solver.declareDatatype(std::string("a"), ctors1));
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  DatatypeConstructorDecl nil2 = d_solver.mkDatatypeConstructorDecl("nil");
  std::vector<DatatypeConstructorDecl> ctors2 = {cons, nil2};
  ASSERT_NO_THROW(d_solver.declareDatatype(std::string("b"), ctors2));
  DatatypeConstructorDecl cons2 = d_solver.mkDatatypeConstructorDecl("cons");
  DatatypeConstructorDecl nil3 = d_solver.mkDatatypeConstructorDecl("nil");
  std::vector<DatatypeConstructorDecl> ctors3 = {cons2, nil3};
  ASSERT_NO_THROW(d_solver.declareDatatype(std::string(""), ctors3));
  std::vector<DatatypeConstructorDecl> ctors4;
  ASSERT_THROW(d_solver.declareDatatype(std::string("c"), ctors4),
               CVC4ApiException);
  ASSERT_THROW(d_solver.declareDatatype(std::string(""), ctors4),
               CVC4ApiException);
  Solver slv;
  ASSERT_THROW(slv.declareDatatype(std::string("a"), ctors1), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, declareFun)
{
  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  ASSERT_NO_THROW(d_solver.declareFun("f1", {}, bvSort));
  ASSERT_NO_THROW(
      d_solver.declareFun("f3", {bvSort, d_solver.getIntegerSort()}, bvSort));
  ASSERT_THROW(d_solver.declareFun("f2", {}, funSort), CVC4ApiException);
  ASSERT_THROW(d_solver.declareFun("f4", {bvSort, funSort}, bvSort),
               CVC4ApiException);
  ASSERT_THROW(d_solver.declareFun("f5", {bvSort, bvSort}, funSort),
               CVC4ApiException);
  Solver slv;
  ASSERT_THROW(slv.declareFun("f1", {}, bvSort), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, declareSort)
{
  ASSERT_NO_THROW(d_solver.declareSort("s", 0));
  ASSERT_NO_THROW(d_solver.declareSort("s", 2));
  ASSERT_NO_THROW(d_solver.declareSort("", 2));
}

TEST_F(TestApiSolverBlack, defineFun)
{
  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort funSort1 = d_solver.mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                          d_solver.getIntegerSort());
  Term b1 = d_solver.mkVar(bvSort, "b1");
  Term b11 = d_solver.mkVar(bvSort, "b1");
  Term b2 = d_solver.mkVar(d_solver.getIntegerSort(), "b2");
  Term b3 = d_solver.mkVar(funSort2, "b3");
  Term v1 = d_solver.mkConst(bvSort, "v1");
  Term v2 = d_solver.mkConst(d_solver.getIntegerSort(), "v2");
  Term v3 = d_solver.mkConst(funSort2, "v3");
  Term f1 = d_solver.mkConst(funSort1, "f1");
  Term f2 = d_solver.mkConst(funSort2, "f2");
  Term f3 = d_solver.mkConst(bvSort, "f3");
  ASSERT_NO_THROW(d_solver.defineFun("f", {}, bvSort, v1));
  ASSERT_NO_THROW(d_solver.defineFun("ff", {b1, b2}, bvSort, v1));
  ASSERT_NO_THROW(d_solver.defineFun(f1, {b1, b11}, v1));
  ASSERT_THROW(d_solver.defineFun("ff", {v1, b2}, bvSort, v1),
               CVC4ApiException);
  ASSERT_THROW(d_solver.defineFun("fff", {b1}, bvSort, v3), CVC4ApiException);
  ASSERT_THROW(d_solver.defineFun("ffff", {b1}, funSort2, v3),
               CVC4ApiException);
  ASSERT_THROW(d_solver.defineFun("fffff", {b1, b3}, bvSort, v1),
               CVC4ApiException);
  ASSERT_THROW(d_solver.defineFun(f1, {v1, b11}, v1), CVC4ApiException);
  ASSERT_THROW(d_solver.defineFun(f1, {b1}, v1), CVC4ApiException);
  ASSERT_THROW(d_solver.defineFun(f1, {b1, b11}, v2), CVC4ApiException);
  ASSERT_THROW(d_solver.defineFun(f1, {b1, b11}, v3), CVC4ApiException);
  ASSERT_THROW(d_solver.defineFun(f2, {b1}, v2), CVC4ApiException);
  ASSERT_THROW(d_solver.defineFun(f3, {b1}, v1), CVC4ApiException);

  Solver slv;
  Sort bvSort2 = slv.mkBitVectorSort(32);
  Term v12 = slv.mkConst(bvSort2, "v1");
  Term b12 = slv.mkVar(bvSort2, "b1");
  Term b22 = slv.mkVar(slv.getIntegerSort(), "b2");
  ASSERT_THROW(slv.defineFun("f", {}, bvSort, v12), CVC4ApiException);
  ASSERT_THROW(slv.defineFun("f", {}, bvSort2, v1), CVC4ApiException);
  ASSERT_THROW(slv.defineFun("ff", {b1, b22}, bvSort2, v12), CVC4ApiException);
  ASSERT_THROW(slv.defineFun("ff", {b12, b2}, bvSort2, v12), CVC4ApiException);
  ASSERT_THROW(slv.defineFun("ff", {b12, b22}, bvSort, v12), CVC4ApiException);
  ASSERT_THROW(slv.defineFun("ff", {b12, b22}, bvSort2, v1), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, defineFunGlobal)
{
  Sort bSort = d_solver.getBooleanSort();
  Sort fSort = d_solver.mkFunctionSort(bSort, bSort);

  Term bTrue = d_solver.mkBoolean(true);
  // (define-fun f () Bool true)
  Term f = d_solver.defineFun("f", {}, bSort, bTrue, true);
  Term b = d_solver.mkVar(bSort, "b");
  Term gSym = d_solver.mkConst(fSort, "g");
  // (define-fun g (b Bool) Bool b)
  Term g = d_solver.defineFun(gSym, {b}, b, true);

  // (assert (or (not f) (not (g true))))
  d_solver.assertFormula(d_solver.mkTerm(
      OR, f.notTerm(), d_solver.mkTerm(APPLY_UF, g, bTrue).notTerm()));
  ASSERT_TRUE(d_solver.checkSat().isUnsat());
  d_solver.resetAssertions();
  // (assert (or (not f) (not (g true))))
  d_solver.assertFormula(d_solver.mkTerm(
      OR, f.notTerm(), d_solver.mkTerm(APPLY_UF, g, bTrue).notTerm()));
  ASSERT_TRUE(d_solver.checkSat().isUnsat());
}

TEST_F(TestApiSolverBlack, defineFunRec)
{
  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort funSort1 = d_solver.mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                          d_solver.getIntegerSort());
  Term b1 = d_solver.mkVar(bvSort, "b1");
  Term b11 = d_solver.mkVar(bvSort, "b1");
  Term b2 = d_solver.mkVar(d_solver.getIntegerSort(), "b2");
  Term b3 = d_solver.mkVar(funSort2, "b3");
  Term v1 = d_solver.mkConst(bvSort, "v1");
  Term v2 = d_solver.mkConst(d_solver.getIntegerSort(), "v2");
  Term v3 = d_solver.mkConst(funSort2, "v3");
  Term f1 = d_solver.mkConst(funSort1, "f1");
  Term f2 = d_solver.mkConst(funSort2, "f2");
  Term f3 = d_solver.mkConst(bvSort, "f3");
  ASSERT_NO_THROW(d_solver.defineFunRec("f", {}, bvSort, v1));
  ASSERT_NO_THROW(d_solver.defineFunRec("ff", {b1, b2}, bvSort, v1));
  ASSERT_NO_THROW(d_solver.defineFunRec(f1, {b1, b11}, v1));
  ASSERT_THROW(d_solver.defineFunRec("fff", {b1}, bvSort, v3),
               CVC4ApiException);
  ASSERT_THROW(d_solver.defineFunRec("ff", {b1, v2}, bvSort, v1),
               CVC4ApiException);
  ASSERT_THROW(d_solver.defineFunRec("ffff", {b1}, funSort2, v3),
               CVC4ApiException);
  ASSERT_THROW(d_solver.defineFunRec("fffff", {b1, b3}, bvSort, v1),
               CVC4ApiException);
  ASSERT_THROW(d_solver.defineFunRec(f1, {b1}, v1), CVC4ApiException);
  ASSERT_THROW(d_solver.defineFunRec(f1, {b1, b11}, v2), CVC4ApiException);
  ASSERT_THROW(d_solver.defineFunRec(f1, {b1, b11}, v3), CVC4ApiException);
  ASSERT_THROW(d_solver.defineFunRec(f2, {b1}, v2), CVC4ApiException);
  ASSERT_THROW(d_solver.defineFunRec(f3, {b1}, v1), CVC4ApiException);

  Solver slv;
  Sort bvSort2 = slv.mkBitVectorSort(32);
  Term v12 = slv.mkConst(bvSort2, "v1");
  Term b12 = slv.mkVar(bvSort2, "b1");
  Term b22 = slv.mkVar(slv.getIntegerSort(), "b2");
  ASSERT_NO_THROW(slv.defineFunRec("f", {}, bvSort2, v12));
  ASSERT_NO_THROW(slv.defineFunRec("ff", {b12, b22}, bvSort2, v12));
  ASSERT_THROW(slv.defineFunRec("f", {}, bvSort, v12), CVC4ApiException);
  ASSERT_THROW(slv.defineFunRec("f", {}, bvSort2, v1), CVC4ApiException);
  ASSERT_THROW(slv.defineFunRec("ff", {b1, b22}, bvSort2, v12),
               CVC4ApiException);
  ASSERT_THROW(slv.defineFunRec("ff", {b12, b2}, bvSort2, v12),
               CVC4ApiException);
  ASSERT_THROW(slv.defineFunRec("ff", {b12, b22}, bvSort, v12),
               CVC4ApiException);
  ASSERT_THROW(slv.defineFunRec("ff", {b12, b22}, bvSort2, v1),
               CVC4ApiException);
}

TEST_F(TestApiSolverBlack, defineFunRecWrongLogic)
{
  d_solver.setLogic("QF_BV");
  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort funSort = d_solver.mkFunctionSort({bvSort, bvSort}, bvSort);
  Term b = d_solver.mkVar(bvSort, "b");
  Term v = d_solver.mkConst(bvSort, "v");
  Term f = d_solver.mkConst(funSort, "f");
  ASSERT_THROW(d_solver.defineFunRec("f", {}, bvSort, v), CVC4ApiException);
  ASSERT_THROW(d_solver.defineFunRec(f, {b, b}, v), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, defineFunRecGlobal)
{
  Sort bSort = d_solver.getBooleanSort();
  Sort fSort = d_solver.mkFunctionSort(bSort, bSort);

  d_solver.push();
  Term bTrue = d_solver.mkBoolean(true);
  // (define-fun f () Bool true)
  Term f = d_solver.defineFunRec("f", {}, bSort, bTrue, true);
  Term b = d_solver.mkVar(bSort, "b");
  Term gSym = d_solver.mkConst(fSort, "g");
  // (define-fun g (b Bool) Bool b)
  Term g = d_solver.defineFunRec(gSym, {b}, b, true);

  // (assert (or (not f) (not (g true))))
  d_solver.assertFormula(d_solver.mkTerm(
      OR, f.notTerm(), d_solver.mkTerm(APPLY_UF, g, bTrue).notTerm()));
  ASSERT_TRUE(d_solver.checkSat().isUnsat());
  d_solver.pop();
  // (assert (or (not f) (not (g true))))
  d_solver.assertFormula(d_solver.mkTerm(
      OR, f.notTerm(), d_solver.mkTerm(APPLY_UF, g, bTrue).notTerm()));
  ASSERT_TRUE(d_solver.checkSat().isUnsat());
}

TEST_F(TestApiSolverBlack, defineFunsRec)
{
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort funSort1 = d_solver.mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_solver.mkFunctionSort(uSort, d_solver.getIntegerSort());
  Term b1 = d_solver.mkVar(bvSort, "b1");
  Term b11 = d_solver.mkVar(bvSort, "b1");
  Term b2 = d_solver.mkVar(d_solver.getIntegerSort(), "b2");
  Term b3 = d_solver.mkVar(funSort2, "b3");
  Term b4 = d_solver.mkVar(uSort, "b4");
  Term v1 = d_solver.mkConst(bvSort, "v1");
  Term v2 = d_solver.mkConst(d_solver.getIntegerSort(), "v2");
  Term v3 = d_solver.mkConst(funSort2, "v3");
  Term v4 = d_solver.mkConst(uSort, "v4");
  Term f1 = d_solver.mkConst(funSort1, "f1");
  Term f2 = d_solver.mkConst(funSort2, "f2");
  Term f3 = d_solver.mkConst(bvSort, "f3");
  ASSERT_NO_THROW(
      d_solver.defineFunsRec({f1, f2}, {{b1, b11}, {b4}}, {v1, v2}));
  ASSERT_THROW(d_solver.defineFunsRec({f1, f2}, {{v1, b11}, {b4}}, {v1, v2}),
               CVC4ApiException);
  ASSERT_THROW(d_solver.defineFunsRec({f1, f3}, {{b1, b11}, {b4}}, {v1, v2}),
               CVC4ApiException);
  ASSERT_THROW(d_solver.defineFunsRec({f1, f2}, {{b1}, {b4}}, {v1, v2}),
               CVC4ApiException);
  ASSERT_THROW(d_solver.defineFunsRec({f1, f2}, {{b1, b2}, {b4}}, {v1, v2}),
               CVC4ApiException);
  ASSERT_THROW(d_solver.defineFunsRec({f1, f2}, {{b1, b11}, {b4}}, {v1, v4}),
               CVC4ApiException);

  Solver slv;
  Sort uSort2 = slv.mkUninterpretedSort("u");
  Sort bvSort2 = slv.mkBitVectorSort(32);
  Sort funSort12 = slv.mkFunctionSort({bvSort2, bvSort2}, bvSort2);
  Sort funSort22 = slv.mkFunctionSort(uSort2, slv.getIntegerSort());
  Term b12 = slv.mkVar(bvSort2, "b1");
  Term b112 = slv.mkVar(bvSort2, "b1");
  Term b42 = slv.mkVar(uSort2, "b4");
  Term v12 = slv.mkConst(bvSort2, "v1");
  Term v22 = slv.mkConst(slv.getIntegerSort(), "v2");
  Term f12 = slv.mkConst(funSort12, "f1");
  Term f22 = slv.mkConst(funSort22, "f2");
  ASSERT_NO_THROW(
      slv.defineFunsRec({f12, f22}, {{b12, b112}, {b42}}, {v12, v22}));
  ASSERT_THROW(slv.defineFunsRec({f1, f22}, {{b12, b112}, {b42}}, {v12, v22}),
               CVC4ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f2}, {{b12, b112}, {b42}}, {v12, v22}),
               CVC4ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f22}, {{b1, b112}, {b42}}, {v12, v22}),
               CVC4ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f22}, {{b12, b11}, {b42}}, {v12, v22}),
               CVC4ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f22}, {{b12, b112}, {b4}}, {v12, v22}),
               CVC4ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f22}, {{b12, b112}, {b42}}, {v1, v22}),
               CVC4ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f22}, {{b12, b112}, {b42}}, {v12, v2}),
               CVC4ApiException);
}

TEST_F(TestApiSolverBlack, defineFunsRecWrongLogic)
{
  d_solver.setLogic("QF_BV");
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort funSort1 = d_solver.mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_solver.mkFunctionSort(uSort, d_solver.getIntegerSort());
  Term b = d_solver.mkVar(bvSort, "b");
  Term u = d_solver.mkVar(uSort, "u");
  Term v1 = d_solver.mkConst(bvSort, "v1");
  Term v2 = d_solver.mkConst(d_solver.getIntegerSort(), "v2");
  Term f1 = d_solver.mkConst(funSort1, "f1");
  Term f2 = d_solver.mkConst(funSort2, "f2");
  ASSERT_THROW(d_solver.defineFunsRec({f1, f2}, {{b, b}, {u}}, {v1, v2}),
               CVC4ApiException);
}

TEST_F(TestApiSolverBlack, defineFunsRecGlobal)
{
  Sort bSort = d_solver.getBooleanSort();
  Sort fSort = d_solver.mkFunctionSort(bSort, bSort);

  d_solver.push();
  Term bTrue = d_solver.mkBoolean(true);
  Term b = d_solver.mkVar(bSort, "b");
  Term gSym = d_solver.mkConst(fSort, "g");
  // (define-funs-rec ((g ((b Bool)) Bool)) (b))
  d_solver.defineFunsRec({gSym}, {{b}}, {b}, true);

  // (assert (not (g true)))
  d_solver.assertFormula(d_solver.mkTerm(APPLY_UF, gSym, bTrue).notTerm());
  ASSERT_TRUE(d_solver.checkSat().isUnsat());
  d_solver.pop();
  // (assert (not (g true)))
  d_solver.assertFormula(d_solver.mkTerm(APPLY_UF, gSym, bTrue).notTerm());
  ASSERT_TRUE(d_solver.checkSat().isUnsat());
}

TEST_F(TestApiSolverBlack, uFIteration)
{
  Sort intSort = d_solver.getIntegerSort();
  Sort funSort = d_solver.mkFunctionSort({intSort, intSort}, intSort);
  Term x = d_solver.mkConst(intSort, "x");
  Term y = d_solver.mkConst(intSort, "y");
  Term f = d_solver.mkConst(funSort, "f");
  Term fxy = d_solver.mkTerm(APPLY_UF, f, x, y);

  // Expecting the uninterpreted function to be one of the children
  Term expected_children[3] = {f, x, y};
  uint32_t idx = 0;
  for (auto c : fxy)
  {
    EXPECT_LT(idx, 3);
    EXPECT_EQ(c, expected_children[idx]);
    idx++;
  }
}

TEST_F(TestApiSolverBlack, getInfo)
{
  ASSERT_NO_THROW(d_solver.getInfo("name"));
  ASSERT_THROW(d_solver.getInfo("asdf"), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, getInterpolant)
{
  // TODO issue #5593
}

TEST_F(TestApiSolverBlack, getOp)
{
  Sort bv32 = d_solver.mkBitVectorSort(32);
  Term a = d_solver.mkConst(bv32, "a");
  Op ext = d_solver.mkOp(BITVECTOR_EXTRACT, 2, 1);
  Term exta = d_solver.mkTerm(ext, a);

  ASSERT_FALSE(a.hasOp());
  ASSERT_THROW(a.getOp(), CVC4ApiException);
  ASSERT_TRUE(exta.hasOp());
  EXPECT_EQ(exta.getOp(), ext);

  // Test Datatypes -- more complicated
  DatatypeDecl consListSpec = d_solver.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_solver.getIntegerSort());
  cons.addSelectorSelf("tail");
  consListSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  consListSpec.addConstructor(nil);
  Sort consListSort = d_solver.mkDatatypeSort(consListSpec);
  Datatype consList = consListSort.getDatatype();

  Term consTerm = consList.getConstructorTerm("cons");
  Term nilTerm = consList.getConstructorTerm("nil");
  Term headTerm = consList["cons"].getSelectorTerm("head");

  Term listnil = d_solver.mkTerm(APPLY_CONSTRUCTOR, nilTerm);
  Term listcons1 = d_solver.mkTerm(
      APPLY_CONSTRUCTOR, consTerm, d_solver.mkInteger(1), listnil);
  Term listhead = d_solver.mkTerm(APPLY_SELECTOR, headTerm, listcons1);

  ASSERT_TRUE(listnil.hasOp());
  EXPECT_EQ(listnil.getOp(), Op(&d_solver, APPLY_CONSTRUCTOR));

  ASSERT_TRUE(listcons1.hasOp());
  EXPECT_EQ(listcons1.getOp(), Op(&d_solver, APPLY_CONSTRUCTOR));

  ASSERT_TRUE(listhead.hasOp());
  EXPECT_EQ(listhead.getOp(), Op(&d_solver, APPLY_SELECTOR));
}

TEST_F(TestApiSolverBlack, getOption)
{
  ASSERT_NO_THROW(d_solver.getOption("incremental"));
  ASSERT_THROW(d_solver.getOption("asdf"), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, getUnsatAssumptions1)
{
#if IS_PROOFS_BUILD
  d_solver.setOption("incremental", "false");
  d_solver.checkSatAssuming(d_solver.mkFalse());
  ASSERT_THROW(d_solver.getUnsatAssumptions(), CVC4ApiException);
#endif
}

TEST_F(TestApiSolverBlack, getUnsatAssumptions2)
{
#if IS_PROOFS_BUILD
  d_solver.setOption("incremental", "true");
  d_solver.setOption("produce-unsat-assumptions", "false");
  d_solver.checkSatAssuming(d_solver.mkFalse());
  ASSERT_THROW(d_solver.getUnsatAssumptions(), CVC4ApiException);
#endif
}

TEST_F(TestApiSolverBlack, getUnsatAssumptions3)
{
#if IS_PROOFS_BUILD
  d_solver.setOption("incremental", "true");
  d_solver.setOption("produce-unsat-assumptions", "true");
  d_solver.checkSatAssuming(d_solver.mkFalse());
  ASSERT_NO_THROW(d_solver.getUnsatAssumptions());
  d_solver.checkSatAssuming(d_solver.mkTrue());
  ASSERT_THROW(d_solver.getUnsatAssumptions(), CVC4ApiException);
#endif
}

TEST_F(TestApiSolverBlack, getUnsatCore1)
{
#if IS_PROOFS_BUILD
  d_solver.setOption("incremental", "false");
  d_solver.assertFormula(d_solver.mkFalse());
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getUnsatCore(), CVC4ApiException);
#endif
}

TEST_F(TestApiSolverBlack, getUnsatCore2)
{
#if IS_PROOFS_BUILD
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-unsat-cores", "false");
  d_solver.assertFormula(d_solver.mkFalse());
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getUnsatCore(), CVC4ApiException);
#endif
}

TEST_F(TestApiSolverBlack, getUnsatCore3)
{
#if IS_PROOFS_BUILD
  d_solver.setOption("incremental", "true");
  d_solver.setOption("produce-unsat-cores", "true");

  Sort uSort = d_solver.mkUninterpretedSort("u");
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort uToIntSort = d_solver.mkFunctionSort(uSort, intSort);
  Sort intPredSort = d_solver.mkFunctionSort(intSort, boolSort);
  std::vector<Term> unsat_core;

  Term x = d_solver.mkConst(uSort, "x");
  Term y = d_solver.mkConst(uSort, "y");
  Term f = d_solver.mkConst(uToIntSort, "f");
  Term p = d_solver.mkConst(intPredSort, "p");
  Term zero = d_solver.mkInteger(0);
  Term one = d_solver.mkInteger(1);
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  Term f_y = d_solver.mkTerm(APPLY_UF, f, y);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_y);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);
  d_solver.assertFormula(d_solver.mkTerm(GT, zero, f_x));
  d_solver.assertFormula(d_solver.mkTerm(GT, zero, f_y));
  d_solver.assertFormula(d_solver.mkTerm(GT, sum, one));
  d_solver.assertFormula(p_0);
  d_solver.assertFormula(p_f_y.notTerm());
  ASSERT_TRUE(d_solver.checkSat().isUnsat());

  ASSERT_NO_THROW(unsat_core = d_solver.getUnsatCore());

  d_solver.resetAssertions();
  for (const auto& t : unsat_core)
  {
    d_solver.assertFormula(t);
  }
  Result res = d_solver.checkSat();
  ASSERT_TRUE(res.isUnsat());
#endif
}

TEST_F(TestApiSolverBlack, getValue1)
{
  d_solver.setOption("produce-models", "false");
  Term t = d_solver.mkTrue();
  d_solver.assertFormula(t);
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getValue(t), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, getValue2)
{
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkFalse();
  d_solver.assertFormula(t);
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getValue(t), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, getValue3)
{
  d_solver.setOption("produce-models", "true");
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort uToIntSort = d_solver.mkFunctionSort(uSort, intSort);
  Sort intPredSort = d_solver.mkFunctionSort(intSort, boolSort);
  std::vector<Term> unsat_core;

  Term x = d_solver.mkConst(uSort, "x");
  Term y = d_solver.mkConst(uSort, "y");
  Term z = d_solver.mkConst(uSort, "z");
  Term f = d_solver.mkConst(uToIntSort, "f");
  Term p = d_solver.mkConst(intPredSort, "p");
  Term zero = d_solver.mkInteger(0);
  Term one = d_solver.mkInteger(1);
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  Term f_y = d_solver.mkTerm(APPLY_UF, f, y);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_y);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);

  d_solver.assertFormula(d_solver.mkTerm(LEQ, zero, f_x));
  d_solver.assertFormula(d_solver.mkTerm(LEQ, zero, f_y));
  d_solver.assertFormula(d_solver.mkTerm(LEQ, sum, one));
  d_solver.assertFormula(p_0.notTerm());
  d_solver.assertFormula(p_f_y);
  ASSERT_TRUE(d_solver.checkSat().isSat());
  ASSERT_NO_THROW(d_solver.getValue(x));
  ASSERT_NO_THROW(d_solver.getValue(y));
  ASSERT_NO_THROW(d_solver.getValue(z));
  ASSERT_NO_THROW(d_solver.getValue(sum));
  ASSERT_NO_THROW(d_solver.getValue(p_f_y));

  Solver slv;
  ASSERT_THROW(slv.getValue(x), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, getQuantifierElimination)
{
  Term x = d_solver.mkVar(d_solver.getBooleanSort(), "x");
  Term forall =
      d_solver.mkTerm(FORALL,
                      d_solver.mkTerm(BOUND_VAR_LIST, x),
                      d_solver.mkTerm(OR, x, d_solver.mkTerm(NOT, x)));
  ASSERT_THROW(d_solver.getQuantifierElimination(Term()), CVC4ApiException);
  ASSERT_THROW(d_solver.getQuantifierElimination(Solver().mkBoolean(false)),
               CVC4ApiException);
  ASSERT_NO_THROW(d_solver.getQuantifierElimination(forall));
}

TEST_F(TestApiSolverBlack, getQuantifierEliminationDisjunct)
{
  Term x = d_solver.mkVar(d_solver.getBooleanSort(), "x");
  Term forall =
      d_solver.mkTerm(FORALL,
                      d_solver.mkTerm(BOUND_VAR_LIST, x),
                      d_solver.mkTerm(OR, x, d_solver.mkTerm(NOT, x)));
  ASSERT_THROW(d_solver.getQuantifierEliminationDisjunct(Term()),
               CVC4ApiException);
  ASSERT_THROW(
      d_solver.getQuantifierEliminationDisjunct(Solver().mkBoolean(false)),
      CVC4ApiException);
  ASSERT_NO_THROW(d_solver.getQuantifierEliminationDisjunct(forall));
}

TEST_F(TestApiSolverBlack, declareSeparationHeap)
{
  d_solver.setLogic("ALL_SUPPORTED");
  Sort integer = d_solver.getIntegerSort();
  ASSERT_NO_THROW(d_solver.declareSeparationHeap(integer, integer));
  // cannot declare separation logic heap more than once
  ASSERT_THROW(d_solver.declareSeparationHeap(integer, integer),
               CVC4ApiException);
}

namespace {
/**
 * Helper function for testGetSeparation{Heap,Nil}TermX. Asserts and checks
 * some simple separation logic constraints.
 */
void checkSimpleSeparationConstraints(Solver* solver)
{
  Sort integer = solver->getIntegerSort();
  // declare the separation heap
  solver->declareSeparationHeap(integer, integer);
  Term x = solver->mkConst(integer, "x");
  Term p = solver->mkConst(integer, "p");
  Term heap = solver->mkTerm(CVC4::api::Kind::SEP_PTO, p, x);
  solver->assertFormula(heap);
  Term nil = solver->mkSepNil(integer);
  solver->assertFormula(nil.eqTerm(solver->mkReal(5)));
  solver->checkSat();
}
}  // namespace

TEST_F(TestApiSolverBlack, getSeparationHeapTerm1)
{
  d_solver.setLogic("QF_BV");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkTrue();
  d_solver.assertFormula(t);
  ASSERT_THROW(d_solver.getSeparationHeap(), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, getSeparationHeapTerm2)
{
  d_solver.setLogic("ALL_SUPPORTED");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "false");
  checkSimpleSeparationConstraints(&d_solver);
  ASSERT_THROW(d_solver.getSeparationHeap(), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, getSeparationHeapTerm3)
{
  d_solver.setLogic("ALL_SUPPORTED");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkFalse();
  d_solver.assertFormula(t);
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getSeparationHeap(), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, getSeparationHeapTerm4)
{
  d_solver.setLogic("ALL_SUPPORTED");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkTrue();
  d_solver.assertFormula(t);
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getSeparationHeap(), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, getSeparationHeapTerm5)
{
  d_solver.setLogic("ALL_SUPPORTED");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  checkSimpleSeparationConstraints(&d_solver);
  ASSERT_NO_THROW(d_solver.getSeparationHeap());
}

TEST_F(TestApiSolverBlack, getSeparationNilTerm1)
{
  d_solver.setLogic("QF_BV");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkTrue();
  d_solver.assertFormula(t);
  ASSERT_THROW(d_solver.getSeparationNilTerm(), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, getSeparationNilTerm2)
{
  d_solver.setLogic("ALL_SUPPORTED");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "false");
  checkSimpleSeparationConstraints(&d_solver);
  ASSERT_THROW(d_solver.getSeparationNilTerm(), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, getSeparationNilTerm3)
{
  d_solver.setLogic("ALL_SUPPORTED");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkFalse();
  d_solver.assertFormula(t);
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getSeparationNilTerm(), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, getSeparationNilTerm4)
{
  d_solver.setLogic("ALL_SUPPORTED");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkTrue();
  d_solver.assertFormula(t);
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getSeparationNilTerm(), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, getSeparationNilTerm5)
{
  d_solver.setLogic("ALL_SUPPORTED");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  checkSimpleSeparationConstraints(&d_solver);
  ASSERT_NO_THROW(d_solver.getSeparationNilTerm());
}

TEST_F(TestApiSolverBlack, push1)
{
  d_solver.setOption("incremental", "true");
  ASSERT_NO_THROW(d_solver.push(1));
  ASSERT_THROW(d_solver.setOption("incremental", "false"), CVC4ApiException);
  ASSERT_THROW(d_solver.setOption("incremental", "true"), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, push2)
{
  d_solver.setOption("incremental", "false");
  ASSERT_THROW(d_solver.push(1), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, pop1)
{
  d_solver.setOption("incremental", "false");
  ASSERT_THROW(d_solver.pop(1), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, pop2)
{
  d_solver.setOption("incremental", "true");
  ASSERT_THROW(d_solver.pop(1), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, pop3)
{
  d_solver.setOption("incremental", "true");
  ASSERT_NO_THROW(d_solver.push(1));
  ASSERT_NO_THROW(d_solver.pop(1));
  ASSERT_THROW(d_solver.pop(1), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, blockModel1)
{
  d_solver.setOption("produce-models", "true");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_THROW(d_solver.blockModel(), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, blockModel2)
{
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_THROW(d_solver.blockModel(), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, blockModel3)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  ASSERT_THROW(d_solver.blockModel(), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, blockModel4)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.blockModel());
}

TEST_F(TestApiSolverBlack, blockModelValues1)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_THROW(d_solver.blockModelValues({}), CVC4ApiException);
  ASSERT_THROW(d_solver.blockModelValues({Term()}), CVC4ApiException);
  ASSERT_THROW(d_solver.blockModelValues({Solver().mkBoolean(false)}),
               CVC4ApiException);
}

TEST_F(TestApiSolverBlack, blockModelValues3)
{
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_THROW(d_solver.blockModelValues({x}), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, blockModelValues4)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  ASSERT_THROW(d_solver.blockModelValues({x}), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, blockModelValues5)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.blockModelValues({x}));
}

TEST_F(TestApiSolverBlack, setInfo)
{
  ASSERT_THROW(d_solver.setInfo("cvc4-lagic", "QF_BV"), CVC4ApiException);
  ASSERT_THROW(d_solver.setInfo("cvc2-logic", "QF_BV"), CVC4ApiException);
  ASSERT_THROW(d_solver.setInfo("cvc4-logic", "asdf"), CVC4ApiException);

  ASSERT_NO_THROW(d_solver.setInfo("source", "asdf"));
  ASSERT_NO_THROW(d_solver.setInfo("category", "asdf"));
  ASSERT_NO_THROW(d_solver.setInfo("difficulty", "asdf"));
  ASSERT_NO_THROW(d_solver.setInfo("filename", "asdf"));
  ASSERT_NO_THROW(d_solver.setInfo("license", "asdf"));
  ASSERT_NO_THROW(d_solver.setInfo("name", "asdf"));
  ASSERT_NO_THROW(d_solver.setInfo("notes", "asdf"));

  ASSERT_NO_THROW(d_solver.setInfo("smt-lib-version", "2"));
  ASSERT_NO_THROW(d_solver.setInfo("smt-lib-version", "2.0"));
  ASSERT_NO_THROW(d_solver.setInfo("smt-lib-version", "2.5"));
  ASSERT_NO_THROW(d_solver.setInfo("smt-lib-version", "2.6"));
  ASSERT_THROW(d_solver.setInfo("smt-lib-version", ".0"), CVC4ApiException);

  ASSERT_NO_THROW(d_solver.setInfo("status", "sat"));
  ASSERT_NO_THROW(d_solver.setInfo("status", "unsat"));
  ASSERT_NO_THROW(d_solver.setInfo("status", "unknown"));
  ASSERT_THROW(d_solver.setInfo("status", "asdf"), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, simplify)
{
  ASSERT_THROW(d_solver.simplify(Term()), CVC4ApiException);

  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Sort funSort1 = d_solver.mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_solver.mkFunctionSort(uSort, d_solver.getIntegerSort());
  DatatypeDecl consListSpec = d_solver.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_solver.getIntegerSort());
  cons.addSelectorSelf("tail");
  consListSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  consListSpec.addConstructor(nil);
  Sort consListSort = d_solver.mkDatatypeSort(consListSpec);

  Term x = d_solver.mkConst(bvSort, "x");
  ASSERT_NO_THROW(d_solver.simplify(x));
  Term a = d_solver.mkConst(bvSort, "a");
  ASSERT_NO_THROW(d_solver.simplify(a));
  Term b = d_solver.mkConst(bvSort, "b");
  ASSERT_NO_THROW(d_solver.simplify(b));
  Term x_eq_x = d_solver.mkTerm(EQUAL, x, x);
  ASSERT_NO_THROW(d_solver.simplify(x_eq_x));
  EXPECT_NE(d_solver.mkTrue(), x_eq_x);
  EXPECT_EQ(d_solver.mkTrue(), d_solver.simplify(x_eq_x));
  Term x_eq_b = d_solver.mkTerm(EQUAL, x, b);
  ASSERT_NO_THROW(d_solver.simplify(x_eq_b));
  EXPECT_NE(d_solver.mkTrue(), x_eq_b);
  EXPECT_NE(d_solver.mkTrue(), d_solver.simplify(x_eq_b));
  Solver slv;
  ASSERT_THROW(slv.simplify(x), CVC4ApiException);

  Term i1 = d_solver.mkConst(d_solver.getIntegerSort(), "i1");
  ASSERT_NO_THROW(d_solver.simplify(i1));
  Term i2 = d_solver.mkTerm(MULT, i1, d_solver.mkInteger("23"));
  ASSERT_NO_THROW(d_solver.simplify(i2));
  EXPECT_NE(i1, i2);
  EXPECT_NE(i1, d_solver.simplify(i2));
  Term i3 = d_solver.mkTerm(PLUS, i1, d_solver.mkInteger(0));
  ASSERT_NO_THROW(d_solver.simplify(i3));
  EXPECT_NE(i1, i3);
  EXPECT_EQ(i1, d_solver.simplify(i3));

  Datatype consList = consListSort.getDatatype();
  Term dt1 = d_solver.mkTerm(
      APPLY_CONSTRUCTOR,
      consList.getConstructorTerm("cons"),
      d_solver.mkInteger(0),
      d_solver.mkTerm(APPLY_CONSTRUCTOR, consList.getConstructorTerm("nil")));
  ASSERT_NO_THROW(d_solver.simplify(dt1));
  Term dt2 = d_solver.mkTerm(
      APPLY_SELECTOR, consList["cons"].getSelectorTerm("head"), dt1);
  ASSERT_NO_THROW(d_solver.simplify(dt2));

  Term b1 = d_solver.mkVar(bvSort, "b1");
  ASSERT_NO_THROW(d_solver.simplify(b1));
  Term b2 = d_solver.mkVar(bvSort, "b1");
  ASSERT_NO_THROW(d_solver.simplify(b2));
  Term b3 = d_solver.mkVar(uSort, "b3");
  ASSERT_NO_THROW(d_solver.simplify(b3));
  Term v1 = d_solver.mkConst(bvSort, "v1");
  ASSERT_NO_THROW(d_solver.simplify(v1));
  Term v2 = d_solver.mkConst(d_solver.getIntegerSort(), "v2");
  ASSERT_NO_THROW(d_solver.simplify(v2));
  Term f1 = d_solver.mkConst(funSort1, "f1");
  ASSERT_NO_THROW(d_solver.simplify(f1));
  Term f2 = d_solver.mkConst(funSort2, "f2");
  ASSERT_NO_THROW(d_solver.simplify(f2));
  d_solver.defineFunsRec({f1, f2}, {{b1, b2}, {b3}}, {v1, v2});
  ASSERT_NO_THROW(d_solver.simplify(f1));
  ASSERT_NO_THROW(d_solver.simplify(f2));
}

TEST_F(TestApiSolverBlack, assertFormula)
{
  ASSERT_NO_THROW(d_solver.assertFormula(d_solver.mkTrue()));
  ASSERT_THROW(d_solver.assertFormula(Term()), CVC4ApiException);
  Solver slv;
  ASSERT_THROW(slv.assertFormula(d_solver.mkTrue()), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, checkEntailed)
{
  d_solver.setOption("incremental", "false");
  ASSERT_NO_THROW(d_solver.checkEntailed(d_solver.mkTrue()));
  ASSERT_THROW(d_solver.checkEntailed(d_solver.mkTrue()), CVC4ApiException);
  Solver slv;
  ASSERT_THROW(slv.checkEntailed(d_solver.mkTrue()), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, checkEntailed1)
{
  Sort boolSort = d_solver.getBooleanSort();
  Term x = d_solver.mkConst(boolSort, "x");
  Term y = d_solver.mkConst(boolSort, "y");
  Term z = d_solver.mkTerm(AND, x, y);
  d_solver.setOption("incremental", "true");
  ASSERT_NO_THROW(d_solver.checkEntailed(d_solver.mkTrue()));
  ASSERT_THROW(d_solver.checkEntailed(Term()), CVC4ApiException);
  ASSERT_NO_THROW(d_solver.checkEntailed(d_solver.mkTrue()));
  ASSERT_NO_THROW(d_solver.checkEntailed(z));
  Solver slv;
  ASSERT_THROW(slv.checkEntailed(d_solver.mkTrue()), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, checkEntailed2)
{
  d_solver.setOption("incremental", "true");

  Sort uSort = d_solver.mkUninterpretedSort("u");
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort uToIntSort = d_solver.mkFunctionSort(uSort, intSort);
  Sort intPredSort = d_solver.mkFunctionSort(intSort, boolSort);

  Term n = Term();
  // Constants
  Term x = d_solver.mkConst(uSort, "x");
  Term y = d_solver.mkConst(uSort, "y");
  // Functions
  Term f = d_solver.mkConst(uToIntSort, "f");
  Term p = d_solver.mkConst(intPredSort, "p");
  // Values
  Term zero = d_solver.mkInteger(0);
  Term one = d_solver.mkInteger(1);
  // Terms
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  Term f_y = d_solver.mkTerm(APPLY_UF, f, y);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_y);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);
  // Assertions
  Term assertions =
      d_solver.mkTerm(AND,
                      std::vector<Term>{
                          d_solver.mkTerm(LEQ, zero, f_x),  // 0 <= f(x)
                          d_solver.mkTerm(LEQ, zero, f_y),  // 0 <= f(y)
                          d_solver.mkTerm(LEQ, sum, one),   // f(x) + f(y) <= 1
                          p_0.notTerm(),                    // not p(0)
                          p_f_y                             // p(f(y))
                      });

  ASSERT_NO_THROW(d_solver.checkEntailed(d_solver.mkTrue()));
  d_solver.assertFormula(assertions);
  ASSERT_NO_THROW(d_solver.checkEntailed(d_solver.mkTerm(DISTINCT, x, y)));
  ASSERT_NO_THROW(d_solver.checkEntailed(
      {d_solver.mkFalse(), d_solver.mkTerm(DISTINCT, x, y)}));
  ASSERT_THROW(d_solver.checkEntailed(n), CVC4ApiException);
  ASSERT_THROW(d_solver.checkEntailed({n, d_solver.mkTerm(DISTINCT, x, y)}),
               CVC4ApiException);
  Solver slv;
  ASSERT_THROW(slv.checkEntailed(d_solver.mkTrue()), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, checkSat)
{
  d_solver.setOption("incremental", "false");
  ASSERT_NO_THROW(d_solver.checkSat());
  ASSERT_THROW(d_solver.checkSat(), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, checkSatAssuming)
{
  d_solver.setOption("incremental", "false");
  ASSERT_NO_THROW(d_solver.checkSatAssuming(d_solver.mkTrue()));
  ASSERT_THROW(d_solver.checkSatAssuming(d_solver.mkTrue()), CVC4ApiException);
  Solver slv;
  ASSERT_THROW(slv.checkSatAssuming(d_solver.mkTrue()), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, checkSatAssuming1)
{
  Sort boolSort = d_solver.getBooleanSort();
  Term x = d_solver.mkConst(boolSort, "x");
  Term y = d_solver.mkConst(boolSort, "y");
  Term z = d_solver.mkTerm(AND, x, y);
  d_solver.setOption("incremental", "true");
  ASSERT_NO_THROW(d_solver.checkSatAssuming(d_solver.mkTrue()));
  ASSERT_THROW(d_solver.checkSatAssuming(Term()), CVC4ApiException);
  ASSERT_NO_THROW(d_solver.checkSatAssuming(d_solver.mkTrue()));
  ASSERT_NO_THROW(d_solver.checkSatAssuming(z));
  Solver slv;
  ASSERT_THROW(slv.checkSatAssuming(d_solver.mkTrue()), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, checkSatAssuming2)
{
  d_solver.setOption("incremental", "true");

  Sort uSort = d_solver.mkUninterpretedSort("u");
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort uToIntSort = d_solver.mkFunctionSort(uSort, intSort);
  Sort intPredSort = d_solver.mkFunctionSort(intSort, boolSort);

  Term n = Term();
  // Constants
  Term x = d_solver.mkConst(uSort, "x");
  Term y = d_solver.mkConst(uSort, "y");
  // Functions
  Term f = d_solver.mkConst(uToIntSort, "f");
  Term p = d_solver.mkConst(intPredSort, "p");
  // Values
  Term zero = d_solver.mkInteger(0);
  Term one = d_solver.mkInteger(1);
  // Terms
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  Term f_y = d_solver.mkTerm(APPLY_UF, f, y);
  Term sum = d_solver.mkTerm(PLUS, f_x, f_y);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);
  // Assertions
  Term assertions =
      d_solver.mkTerm(AND,
                      std::vector<Term>{
                          d_solver.mkTerm(LEQ, zero, f_x),  // 0 <= f(x)
                          d_solver.mkTerm(LEQ, zero, f_y),  // 0 <= f(y)
                          d_solver.mkTerm(LEQ, sum, one),   // f(x) + f(y) <= 1
                          p_0.notTerm(),                    // not p(0)
                          p_f_y                             // p(f(y))
                      });

  ASSERT_NO_THROW(d_solver.checkSatAssuming(d_solver.mkTrue()));
  d_solver.assertFormula(assertions);
  ASSERT_NO_THROW(d_solver.checkSatAssuming(d_solver.mkTerm(DISTINCT, x, y)));
  ASSERT_NO_THROW(d_solver.checkSatAssuming(
      {d_solver.mkFalse(), d_solver.mkTerm(DISTINCT, x, y)}));
  ASSERT_THROW(d_solver.checkSatAssuming(n), CVC4ApiException);
  ASSERT_THROW(d_solver.checkSatAssuming({n, d_solver.mkTerm(DISTINCT, x, y)}),
               CVC4ApiException);
  Solver slv;
  ASSERT_THROW(slv.checkSatAssuming(d_solver.mkTrue()), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, setLogic)
{
  ASSERT_NO_THROW(d_solver.setLogic("AUFLIRA"));
  ASSERT_THROW(d_solver.setLogic("AF_BV"), CVC4ApiException);
  d_solver.assertFormula(d_solver.mkTrue());
  ASSERT_THROW(d_solver.setLogic("AUFLIRA"), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, setOption)
{
  ASSERT_NO_THROW(d_solver.setOption("bv-sat-solver", "minisat"));
  ASSERT_THROW(d_solver.setOption("bv-sat-solver", "1"), CVC4ApiException);
  d_solver.assertFormula(d_solver.mkTrue());
  ASSERT_THROW(d_solver.setOption("bv-sat-solver", "minisat"),
               CVC4ApiException);
}

TEST_F(TestApiSolverBlack, resetAssertions)
{
  d_solver.setOption("incremental", "true");

  Sort bvSort = d_solver.mkBitVectorSort(4);
  Term one = d_solver.mkBitVector(4, 1);
  Term x = d_solver.mkConst(bvSort, "x");
  Term ule = d_solver.mkTerm(BITVECTOR_ULE, x, one);
  Term srem = d_solver.mkTerm(BITVECTOR_SREM, one, x);
  d_solver.push(4);
  Term slt = d_solver.mkTerm(BITVECTOR_SLT, srem, one);
  d_solver.resetAssertions();
  d_solver.checkSatAssuming({slt, ule});
}

TEST_F(TestApiSolverBlack, mkSygusVar)
{
  Sort boolSort = d_solver.getBooleanSort();
  Sort intSort = d_solver.getIntegerSort();
  Sort funSort = d_solver.mkFunctionSort(intSort, boolSort);

  ASSERT_NO_THROW(d_solver.mkSygusVar(boolSort));
  ASSERT_NO_THROW(d_solver.mkSygusVar(funSort));
  ASSERT_NO_THROW(d_solver.mkSygusVar(boolSort, std::string("b")));
  ASSERT_NO_THROW(d_solver.mkSygusVar(funSort, ""));
  ASSERT_THROW(d_solver.mkSygusVar(Sort()), CVC4ApiException);
  ASSERT_THROW(d_solver.mkSygusVar(d_solver.getNullSort(), "a"),
               CVC4ApiException);
  Solver slv;
  ASSERT_THROW(slv.mkSygusVar(boolSort), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, mkSygusGrammar)
{
  Term nullTerm;
  Term boolTerm = d_solver.mkBoolean(true);
  Term boolVar = d_solver.mkVar(d_solver.getBooleanSort());
  Term intVar = d_solver.mkVar(d_solver.getIntegerSort());

  ASSERT_NO_THROW(d_solver.mkSygusGrammar({}, {intVar}));
  ASSERT_NO_THROW(d_solver.mkSygusGrammar({boolVar}, {intVar}));
  ASSERT_THROW(d_solver.mkSygusGrammar({}, {}), CVC4ApiException);
  ASSERT_THROW(d_solver.mkSygusGrammar({}, {nullTerm}), CVC4ApiException);
  ASSERT_THROW(d_solver.mkSygusGrammar({}, {boolTerm}), CVC4ApiException);
  ASSERT_THROW(d_solver.mkSygusGrammar({boolTerm}, {intVar}), CVC4ApiException);
  Solver slv;
  Term boolVar2 = slv.mkVar(slv.getBooleanSort());
  Term intVar2 = slv.mkVar(slv.getIntegerSort());
  ASSERT_NO_THROW(slv.mkSygusGrammar({boolVar2}, {intVar2}));
  ASSERT_THROW(slv.mkSygusGrammar({boolVar}, {intVar2}), CVC4ApiException);
  ASSERT_THROW(slv.mkSygusGrammar({boolVar2}, {intVar}), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, synthFun)
{
  Sort null = d_solver.getNullSort();
  Sort boolean = d_solver.getBooleanSort();
  Sort integer = d_solver.getIntegerSort();

  Term nullTerm;
  Term x = d_solver.mkVar(boolean);

  Term start1 = d_solver.mkVar(boolean);
  Term start2 = d_solver.mkVar(integer);

  Grammar g1 = d_solver.mkSygusGrammar({x}, {start1});
  g1.addRule(start1, d_solver.mkBoolean(false));

  Grammar g2 = d_solver.mkSygusGrammar({x}, {start2});
  g2.addRule(start2, d_solver.mkInteger(0));

  ASSERT_NO_THROW(d_solver.synthFun("", {}, boolean));
  ASSERT_NO_THROW(d_solver.synthFun("f1", {x}, boolean));
  ASSERT_NO_THROW(d_solver.synthFun("f2", {x}, boolean, g1));

  ASSERT_THROW(d_solver.synthFun("f3", {nullTerm}, boolean), CVC4ApiException);
  ASSERT_THROW(d_solver.synthFun("f4", {}, null), CVC4ApiException);
  ASSERT_THROW(d_solver.synthFun("f6", {x}, boolean, g2), CVC4ApiException);
  Solver slv;
  Term x2 = slv.mkVar(slv.getBooleanSort());
  ASSERT_NO_THROW(slv.synthFun("f1", {x2}, slv.getBooleanSort()));
  ASSERT_THROW(slv.synthFun("", {}, d_solver.getBooleanSort()),
               CVC4ApiException);
  ASSERT_THROW(slv.synthFun("f1", {x}, d_solver.getBooleanSort()),
               CVC4ApiException);
}

TEST_F(TestApiSolverBlack, synthInv)
{
  Sort boolean = d_solver.getBooleanSort();
  Sort integer = d_solver.getIntegerSort();

  Term nullTerm;
  Term x = d_solver.mkVar(boolean);

  Term start1 = d_solver.mkVar(boolean);
  Term start2 = d_solver.mkVar(integer);

  Grammar g1 = d_solver.mkSygusGrammar({x}, {start1});
  g1.addRule(start1, d_solver.mkBoolean(false));

  Grammar g2 = d_solver.mkSygusGrammar({x}, {start2});
  g2.addRule(start2, d_solver.mkInteger(0));

  ASSERT_NO_THROW(d_solver.synthInv("", {}));
  ASSERT_NO_THROW(d_solver.synthInv("i1", {x}));
  ASSERT_NO_THROW(d_solver.synthInv("i2", {x}, g1));

  ASSERT_THROW(d_solver.synthInv("i3", {nullTerm}), CVC4ApiException);
  ASSERT_THROW(d_solver.synthInv("i4", {x}, g2), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, addSygusConstraint)
{
  Term nullTerm;
  Term boolTerm = d_solver.mkBoolean(true);
  Term intTerm = d_solver.mkInteger(1);

  ASSERT_NO_THROW(d_solver.addSygusConstraint(boolTerm));
  ASSERT_THROW(d_solver.addSygusConstraint(nullTerm), CVC4ApiException);
  ASSERT_THROW(d_solver.addSygusConstraint(intTerm), CVC4ApiException);

  Solver slv;
  ASSERT_THROW(slv.addSygusConstraint(boolTerm), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, addSygusInvConstraint)
{
  Sort boolean = d_solver.getBooleanSort();
  Sort real = d_solver.getRealSort();

  Term nullTerm;
  Term intTerm = d_solver.mkInteger(1);

  Term inv = d_solver.declareFun("inv", {real}, boolean);
  Term pre = d_solver.declareFun("pre", {real}, boolean);
  Term trans = d_solver.declareFun("trans", {real, real}, boolean);
  Term post = d_solver.declareFun("post", {real}, boolean);

  Term inv1 = d_solver.declareFun("inv1", {real}, real);

  Term trans1 = d_solver.declareFun("trans1", {boolean, real}, boolean);
  Term trans2 = d_solver.declareFun("trans2", {real, boolean}, boolean);
  Term trans3 = d_solver.declareFun("trans3", {real, real}, real);

  ASSERT_NO_THROW(d_solver.addSygusInvConstraint(inv, pre, trans, post));

  ASSERT_THROW(d_solver.addSygusInvConstraint(nullTerm, pre, trans, post),
               CVC4ApiException);
  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, nullTerm, trans, post),
               CVC4ApiException);
  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, pre, nullTerm, post),
               CVC4ApiException);
  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, pre, trans, nullTerm),
               CVC4ApiException);

  ASSERT_THROW(d_solver.addSygusInvConstraint(intTerm, pre, trans, post),
               CVC4ApiException);

  ASSERT_THROW(d_solver.addSygusInvConstraint(inv1, pre, trans, post),
               CVC4ApiException);

  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, trans, trans, post),
               CVC4ApiException);

  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, pre, intTerm, post),
               CVC4ApiException);
  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, pre, pre, post),
               CVC4ApiException);
  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, pre, trans1, post),
               CVC4ApiException);
  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, pre, trans2, post),
               CVC4ApiException);
  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, pre, trans3, post),
               CVC4ApiException);

  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, pre, trans, trans),
               CVC4ApiException);
  Solver slv;
  Sort boolean2 = slv.getBooleanSort();
  Sort real2 = slv.getRealSort();
  Term inv22 = slv.declareFun("inv", {real2}, boolean2);
  Term pre22 = slv.declareFun("pre", {real2}, boolean2);
  Term trans22 = slv.declareFun("trans", {real2, real2}, boolean2);
  Term post22 = slv.declareFun("post", {real2}, boolean2);
  ASSERT_NO_THROW(slv.addSygusInvConstraint(inv22, pre22, trans22, post22));
  ASSERT_THROW(slv.addSygusInvConstraint(inv, pre22, trans22, post22),
               CVC4ApiException);
  ASSERT_THROW(slv.addSygusInvConstraint(inv22, pre, trans22, post22),
               CVC4ApiException);
  ASSERT_THROW(slv.addSygusInvConstraint(inv22, pre22, trans, post22),
               CVC4ApiException);
  ASSERT_THROW(slv.addSygusInvConstraint(inv22, pre22, trans22, post),
               CVC4ApiException);
}

TEST_F(TestApiSolverBlack, getSynthSolution)
{
  d_solver.setOption("lang", "sygus2");
  d_solver.setOption("incremental", "false");

  Term nullTerm;
  Term x = d_solver.mkBoolean(false);
  Term f = d_solver.synthFun("f", {}, d_solver.getBooleanSort());

  ASSERT_THROW(d_solver.getSynthSolution(f), CVC4ApiException);

  d_solver.checkSynth();

  ASSERT_NO_THROW(d_solver.getSynthSolution(f));
  ASSERT_NO_THROW(d_solver.getSynthSolution(f));

  ASSERT_THROW(d_solver.getSynthSolution(nullTerm), CVC4ApiException);
  ASSERT_THROW(d_solver.getSynthSolution(x), CVC4ApiException);

  Solver slv;
  ASSERT_THROW(slv.getSynthSolution(f), CVC4ApiException);
}

TEST_F(TestApiSolverBlack, getSynthSolutions)
{
  d_solver.setOption("lang", "sygus2");
  d_solver.setOption("incremental", "false");

  Term nullTerm;
  Term x = d_solver.mkBoolean(false);
  Term f = d_solver.synthFun("f", {}, d_solver.getBooleanSort());

  ASSERT_THROW(d_solver.getSynthSolutions({}), CVC4ApiException);
  ASSERT_THROW(d_solver.getSynthSolutions({f}), CVC4ApiException);

  d_solver.checkSynth();

  ASSERT_NO_THROW(d_solver.getSynthSolutions({f}));
  ASSERT_NO_THROW(d_solver.getSynthSolutions({f, f}));

  ASSERT_THROW(d_solver.getSynthSolutions({}), CVC4ApiException);
  ASSERT_THROW(d_solver.getSynthSolutions({nullTerm}), CVC4ApiException);
  ASSERT_THROW(d_solver.getSynthSolutions({x}), CVC4ApiException);

  Solver slv;
  ASSERT_THROW(slv.getSynthSolutions({x}), CVC4ApiException);
}

}  // namespace test
}  // namespace CVC4
