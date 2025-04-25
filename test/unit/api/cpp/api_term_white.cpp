/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Makai Mann
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of the Term class.
 */

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiWhiteTerm : public TestApi
{
};

TEST_F(TestApiWhiteTerm, getOp)
{
  Sort intsort = d_tm.getIntegerSort();
  Sort bvsort = d_tm.mkBitVectorSort(8);
  Sort arrsort = d_tm.mkArraySort(bvsort, intsort);
  Sort funsort = d_tm.mkFunctionSort({intsort}, bvsort);

  Term x = d_tm.mkConst(intsort, "x");
  Term a = d_tm.mkConst(arrsort, "a");
  Term b = d_tm.mkConst(bvsort, "b");

  Term ab = d_tm.mkTerm(Kind::SELECT, {a, b});
  Op ext = d_tm.mkOp(Kind::BITVECTOR_EXTRACT, {4, 0});
  Term extb = d_tm.mkTerm(ext, {b});

  ASSERT_EQ(ab.getOp(), Op(&d_solver->getTermManager(), Kind::SELECT));
  // can compare directly to a Kind (will invoke Op constructor)
  ASSERT_EQ(ab.getOp(), Op(&d_solver->getTermManager(), Kind::SELECT));

  Term f = d_tm.mkConst(funsort, "f");
  Term fx = d_tm.mkTerm(Kind::APPLY_UF, {f, x});

  ASSERT_EQ(fx.getOp(), Op(&d_solver->getTermManager(), Kind::APPLY_UF));
  // testing rebuild from op and children

  // Test Datatypes Ops
  Sort sort = d_tm.mkParamSort("T");
  DatatypeDecl listDecl = d_tm.mkDatatypeDecl("paramlist", {sort});
  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
  cons.addSelector("head", sort);
  cons.addSelectorSelf("tail");
  listDecl.addConstructor(cons);
  listDecl.addConstructor(nil);
  Sort listSort = d_tm.mkDatatypeSort(listDecl);
  Sort intListSort =
      listSort.instantiate(std::vector<Sort>{d_tm.getIntegerSort()});
  Term c = d_tm.mkConst(intListSort, "c");
  Datatype list = listSort.getDatatype();
  // list datatype constructor and selector operator terms
  Term consOpTerm = list.getConstructor("cons").getTerm();
  Term nilOpTerm = list.getConstructor("nil").getTerm();
  Term headOpTerm = list["cons"].getSelector("head").getTerm();
  Term tailOpTerm = list["cons"].getSelector("tail").getTerm();

  Term nilTerm = d_tm.mkTerm(Kind::APPLY_CONSTRUCTOR, {nilOpTerm});
  Term consTerm = d_tm.mkTerm(Kind::APPLY_CONSTRUCTOR,
                              {consOpTerm, d_tm.mkInteger(0), nilTerm});
  Term headTerm = d_tm.mkTerm(Kind::APPLY_SELECTOR, {headOpTerm, consTerm});
  Term tailTerm = d_tm.mkTerm(Kind::APPLY_SELECTOR, {tailOpTerm, consTerm});

  ASSERT_EQ(nilTerm.getOp(),
            Op(&d_solver->getTermManager(), Kind::APPLY_CONSTRUCTOR));
  ASSERT_EQ(consTerm.getOp(),
            Op(&d_solver->getTermManager(), Kind::APPLY_CONSTRUCTOR));
  ASSERT_EQ(headTerm.getOp(),
            Op(&d_solver->getTermManager(), Kind::APPLY_SELECTOR));
  ASSERT_EQ(tailTerm.getOp(),
            Op(&d_solver->getTermManager(), Kind::APPLY_SELECTOR));
}
}  // namespace test
}  // namespace cvc5::internal
