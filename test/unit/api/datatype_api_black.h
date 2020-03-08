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

  void testDatatypeStructs();
  void testDatatypeNames();

 private:
  Solver d_solver;
};

void DatatypeBlack::setUp() {}

void DatatypeBlack::tearDown() {}

void DatatypeBlack::testMkDatatypeSort()
{
  DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
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
  TS_ASSERT_THROWS_NOTHING(consConstr.getConstructorTerm());
  TS_ASSERT_THROWS_NOTHING(nilConstr.getConstructorTerm());
}

void DatatypeBlack::testDatatypeStructs()
{
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();

  // create datatype sort to test
  DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons("cons");
  DatatypeSelectorDecl head("head", intSort);
  cons.addSelector(head);
  DatatypeSelectorDecl tail("tail", DatatypeDeclSelfSort());
  cons.addSelector(tail);
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil("nil");
  dtypeSpec.addConstructor(nil);
  Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
  Datatype dt = dtypeSort.getDatatype();
  TS_ASSERT(!dt.isCodatatype());
  TS_ASSERT(!dt.isTuple());
  TS_ASSERT(!dt.isRecord());
  TS_ASSERT(!dt.isFinite());
  TS_ASSERT(dt.isWellFounded());
  // get constructor
  DatatypeConstructor dcons = dt[0];
  Term consTerm = dcons.getConstructorTerm();
  TS_ASSERT(dcons.getNumSelectors() == 2);

  // create datatype sort to test
  DatatypeDecl dtypeSpecEnum = d_solver.mkDatatypeDecl("enum");
  DatatypeConstructorDecl ca("A");
  dtypeSpecEnum.addConstructor(ca);
  DatatypeConstructorDecl cb("B");
  dtypeSpecEnum.addConstructor(cb);
  DatatypeConstructorDecl cc("C");
  dtypeSpecEnum.addConstructor(cc);
  Sort dtypeSortEnum = d_solver.mkDatatypeSort(dtypeSpecEnum);
  Datatype dtEnum = dtypeSortEnum.getDatatype();
  TS_ASSERT(!dtEnum.isTuple());
  TS_ASSERT(dtEnum.isFinite());

  // create codatatype
  DatatypeDecl dtypeSpecStream = d_solver.mkDatatypeDecl("stream", true);
  DatatypeConstructorDecl consStream("cons");
  DatatypeSelectorDecl headStream("head", intSort);
  consStream.addSelector(headStream);
  DatatypeSelectorDecl tailStream("tail", DatatypeDeclSelfSort());
  consStream.addSelector(tailStream);
  dtypeSpecStream.addConstructor(consStream);
  Sort dtypeSortStream = d_solver.mkDatatypeSort(dtypeSpecStream);
  Datatype dtStream = dtypeSortStream.getDatatype();
  TS_ASSERT(dtStream.isCodatatype());
  TS_ASSERT(!dtStream.isFinite());
  // codatatypes may be well-founded
  TS_ASSERT(dtStream.isWellFounded());

  // create tuple
  Sort tupSort = d_solver.mkTupleSort({boolSort});
  Datatype dtTuple = tupSort.getDatatype();
  TS_ASSERT(dtTuple.isTuple());
  TS_ASSERT(!dtTuple.isRecord());
  TS_ASSERT(dtTuple.isFinite());
  TS_ASSERT(dtTuple.isWellFounded());

  // create record
  std::vector<std::pair<std::string, Sort>> fields = {
      std::make_pair("b", boolSort), std::make_pair("i", intSort)};
  Sort recSort = d_solver.mkRecordSort(fields);
  TS_ASSERT(recSort.isDatatype());
  Datatype dtRecord = recSort.getDatatype();
  TS_ASSERT(!dtRecord.isTuple());
  TS_ASSERT(dtRecord.isRecord());
  TS_ASSERT(!dtRecord.isFinite());
  TS_ASSERT(dtRecord.isWellFounded());
}

void DatatypeBlack::testDatatypeNames()
{
  Sort intSort = d_solver.getIntegerSort();

  // create datatype sort to test
  DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons("cons");
  DatatypeSelectorDecl head("head", intSort);
  cons.addSelector(head);
  DatatypeSelectorDecl tail("tail", DatatypeDeclSelfSort());
  cons.addSelector(tail);
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil("nil");
  dtypeSpec.addConstructor(nil);
  Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
  Datatype dt = dtypeSort.getDatatype();
  TS_ASSERT(dt.getName() == std::string("list"));
  TS_ASSERT_THROWS_NOTHING(dt.getConstructor("nil"));
  TS_ASSERT_THROWS_NOTHING(dt["cons"]);
  TS_ASSERT_THROWS(dt.getConstructor("head"), CVC4ApiException&);
  TS_ASSERT_THROWS(dt.getConstructor(""), CVC4ApiException&);

  DatatypeConstructor dcons = dt[0];
  TS_ASSERT(dcons.getName() == std::string("cons"));
  TS_ASSERT_THROWS_NOTHING(dcons.getSelector("head"));
  TS_ASSERT_THROWS_NOTHING(dcons["tail"]);
  TS_ASSERT_THROWS(dcons.getSelector("cons"), CVC4ApiException&);

  // get selector
  DatatypeSelector dselTail = dcons[1];
  TS_ASSERT(dselTail.getName() == std::string("tail"));
}
