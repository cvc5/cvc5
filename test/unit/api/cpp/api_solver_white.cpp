/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Solver class of the  C++ API.
 */

#include "base/configuration.h"
#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiWhiteSolver : public TestApi
{
};

TEST_F(TestApiWhiteSolver, getOp)
{
  DatatypeDecl consListSpec = d_tm.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_tm.getIntegerSort());
  cons.addSelectorSelf("tail");
  consListSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
  consListSpec.addConstructor(nil);
  Sort consListSort = d_tm.mkDatatypeSort(consListSpec);
  Datatype consList = consListSort.getDatatype();

  Term nilTerm = consList.getConstructor("nil").getTerm();
  Term consTerm = consList.getConstructor("cons").getTerm();
  Term headTerm = consList["cons"].getSelector("head").getTerm();

  Term listnil = d_tm.mkTerm(Kind::APPLY_CONSTRUCTOR, {nilTerm});
  Term listcons1 = d_tm.mkTerm(Kind::APPLY_CONSTRUCTOR,
                               {consTerm, d_tm.mkInteger(1), listnil});
  Term listhead = d_tm.mkTerm(Kind::APPLY_SELECTOR, {headTerm, listcons1});

  ASSERT_EQ(listnil.getOp(),
            Op(&d_solver->getTermManager(), Kind::APPLY_CONSTRUCTOR));
  ASSERT_EQ(listcons1.getOp(),
            Op(&d_solver->getTermManager(), Kind::APPLY_CONSTRUCTOR));
  ASSERT_EQ(listhead.getOp(),
            Op(&d_solver->getTermManager(), Kind::APPLY_SELECTOR));
}

}  // namespace test
}  // namespace cvc5::internal
