/*********************                                                        */
/*! \file result_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the Result class
 **/

#include <cxxtest/TestSuite.h>

#include "api/cvc4cpp.h"

using namespace CVC4::api;

class ResultBlack : public CxxTest::TestSuite
{
 public:
  void setUp() { d_solver.reset(new Solver()); }
  void tearDown() override {}

  void testIsNull();
  void testEq();
  void testIsSat();
  void testIsUnsat();
  void testIsSatUnknown();
  void testIsValid();
  void testIsInvalid();
  void testIsValidUnknown();

 private:
  std::unique_ptr<Solver> d_solver;
};

void ResultBlack::testIsNull()
{
  Result res_null;
  TS_ASSERT(res_null.isNull());
  TS_ASSERT(!res_null.isSat());
  TS_ASSERT(!res_null.isUnsat());
  TS_ASSERT(!res_null.isSatUnknown());
  TS_ASSERT(!res_null.isValid());
  TS_ASSERT(!res_null.isInvalid());
  TS_ASSERT(!res_null.isValidUnknown());
  Sort u_sort = d_solver->mkUninterpretedSort("u");
  Term x = d_solver->mkVar(u_sort, "x");
  d_solver->assertFormula(x.eqTerm(x));
  Result res = d_solver->checkSat();
  TS_ASSERT(!res.isNull());
}

void ResultBlack::testEq()
{
  Sort u_sort = d_solver->mkUninterpretedSort("u");
  Term x = d_solver->mkVar(u_sort, "x");
  d_solver->assertFormula(x.eqTerm(x));
  Result res;
  Result res2 = d_solver->checkSat();
  Result res3 = d_solver->checkSat();
  res = res2;
  TS_ASSERT_EQUALS(res, res2);
  TS_ASSERT_EQUALS(res3, res2);
}

void ResultBlack::testIsSat()
{
  Sort u_sort = d_solver->mkUninterpretedSort("u");
  Term x = d_solver->mkVar(u_sort, "x");
  d_solver->assertFormula(x.eqTerm(x));
  Result res = d_solver->checkSat();
  TS_ASSERT(res.isSat());
  TS_ASSERT(!res.isSatUnknown());
}

void ResultBlack::testIsUnsat()
{
  Sort u_sort = d_solver->mkUninterpretedSort("u");
  Term x = d_solver->mkVar(u_sort, "x");
  d_solver->assertFormula(x.eqTerm(x).notTerm());
  Result res = d_solver->checkSat();
  TS_ASSERT(res.isUnsat());
  TS_ASSERT(!res.isSatUnknown());
}

void ResultBlack::testIsSatUnknown()
{
  d_solver->setLogic("QF_NIA");
  d_solver->setOption("incremental", "false");
  d_solver->setOption("solve-int-as-bv", "32");
  Sort int_sort = d_solver->getIntegerSort();
  Term x = d_solver->mkVar(int_sort, "x");
  d_solver->assertFormula(x.eqTerm(x).notTerm());
  Result res = d_solver->checkSat();
  TS_ASSERT(!res.isSat());
  TS_ASSERT(res.isSatUnknown());
}

void ResultBlack::testIsValid()
{
  Sort u_sort = d_solver->mkUninterpretedSort("u");
  Term x = d_solver->mkVar(u_sort, "x");
  d_solver->assertFormula(x.eqTerm(x).notTerm());
  Result res = d_solver->checkValid();
  TS_ASSERT(res.isValid());
  TS_ASSERT(!res.isValidUnknown());
}

void ResultBlack::testIsInvalid()
{
  Sort u_sort = d_solver->mkUninterpretedSort("u");
  Term x = d_solver->mkVar(u_sort, "x");
  d_solver->assertFormula(x.eqTerm(x));
  Result res = d_solver->checkValid();
  TS_ASSERT(res.isInvalid());
  TS_ASSERT(!res.isValidUnknown());
}

void ResultBlack::testIsValidUnknown()
{
  d_solver->setLogic("QF_NIA");
  d_solver->setOption("incremental", "false");
  d_solver->setOption("solve-int-as-bv", "32");
  Sort int_sort = d_solver->getIntegerSort();
  Term x = d_solver->mkVar(int_sort, "x");
  d_solver->assertFormula(x.eqTerm(x).notTerm());
  Result res = d_solver->checkValid();
  TS_ASSERT(!res.isValid());
  TS_ASSERT(res.isValidUnknown());
  TS_ASSERT_EQUALS(res.getUnknownExplanation(), "UNKNOWN_REASON");
}

