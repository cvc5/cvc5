/*********************                                                        */
/*! \file opterm_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the Term class
 **/

#include <cxxtest/TestSuite.h>

#include "api/cvc4cpp.h"

using namespace CVC4::api;

class OpTermBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override {}
  void tearDown() override {}

  void testGetKind();
  void testGetSort();
  void testIsNull();

 private:
  Solver d_solver;
};

void OpTermBlack::testGetKind()
{
  OpTerm x;
  TS_ASSERT_THROWS(x.getSort(), CVC4ApiException&);
  x = d_solver.mkOpTerm(BITVECTOR_EXTRACT_OP, 31, 1);
  TS_ASSERT_THROWS_NOTHING(x.getKind());
}

void OpTermBlack::testGetSort()
{
  OpTerm x;
  TS_ASSERT_THROWS(x.getSort(), CVC4ApiException&);
  x = d_solver.mkOpTerm(BITVECTOR_EXTRACT_OP, 31, 1);
  TS_ASSERT_THROWS_NOTHING(x.getSort());
}

void OpTermBlack::testIsNull()
{
  OpTerm x;
  TS_ASSERT(x.isNull());
  x = d_solver.mkOpTerm(BITVECTOR_EXTRACT_OP, 31, 1);
  TS_ASSERT(!x.isNull());
}
