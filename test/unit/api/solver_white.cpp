/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Makai Mann, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Solver class of the  C++ API.
 */

#include "base/configuration.h"
#include "test_api.h"

namespace cvc5 {

using namespace api;

namespace test {

class TestApiWhiteSolver : public TestApi
{
};

TEST_F(TestApiWhiteSolver, getOp)
{
  DatatypeDecl consListSpec = d_solver.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_solver.getIntegerSort());
  cons.addSelectorSelf("tail");
  consListSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  consListSpec.addConstructor(nil);
  Sort consListSort = d_solver.mkDatatypeSort(consListSpec);
  Datatype consList = consListSort.getDatatype();

  Term nilTerm = consList.getConstructorTerm("nil");
  Term consTerm = consList.getConstructorTerm("cons");
  Term headTerm = consList["cons"].getSelectorTerm("head");

  Term listnil = d_solver.mkTerm(APPLY_CONSTRUCTOR, nilTerm);
  Term listcons1 = d_solver.mkTerm(
      APPLY_CONSTRUCTOR, consTerm, d_solver.mkInteger(1), listnil);
  Term listhead = d_solver.mkTerm(APPLY_SELECTOR, headTerm, listcons1);

  ASSERT_EQ(listnil.getOp(), Op(&d_solver, APPLY_CONSTRUCTOR));
  ASSERT_EQ(listcons1.getOp(), Op(&d_solver, APPLY_CONSTRUCTOR));
  ASSERT_EQ(listhead.getOp(), Op(&d_solver, APPLY_SELECTOR));
}

}  // namespace test
}  // namespace cvc5
