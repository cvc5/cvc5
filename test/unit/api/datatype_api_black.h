/*********************                                                        */
/*! \file datatype_api_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the datatype classes of the C++ API.
 **
 ** Black box testing of the datatype classes of the C++ API.
 **/

#include <cxxtest/TestSuite.h>

#include "api/cvc4cpp.h"

using namespace CVC4::api;

class DatatypeBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override;
  void tearDown() override;

  void testMkDatatypeSort();

 private:
  Solver d_solver;
};

void DatatypeBlack::setUp() {}

void DatatypeBlack::tearDown() {}

void DatatypeBlack::testMkDatatypeSort()
{
  DatatypeDecl dtypeSpec("list");
  DatatypeConstructorDecl cons("cons");
  DatatypeSelectorDecl head("head", d_solver.getIntegerSort());
  cons.addSelector(head);
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil("nil");
  dtypeSpec.addConstructor(nil);
  Sort listSort = d_solver.mkDatatypeSort(dtypeSpec);
  Datatype d = listSort.getDatatype();
  DatatypeConstructor consConstr = d[0];
  DatatypeConstructor nilConstr = d[1];
  TS_ASSERT_THROWS(d[2], CVC4ApiException&);
  TS_ASSERT(consConstr.isResolved());
  TS_ASSERT(nilConstr.isResolved());
  TS_ASSERT_THROWS_NOTHING(consConstr.getConstructorTerm());
  TS_ASSERT_THROWS_NOTHING(nilConstr.getConstructorTerm());
}
