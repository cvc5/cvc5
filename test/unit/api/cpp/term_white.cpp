/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Makai Mann, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  Sort intsort = d_solver.getIntegerSort();
  Sort bvsort = d_solver.mkBitVectorSort(8);
  Sort arrsort = d_solver.mkArraySort(bvsort, intsort);
  Sort funsort = d_solver.mkFunctionSort({intsort}, bvsort);

  Term x = d_solver.mkConst(intsort, "x");
  Term a = d_solver.mkConst(arrsort, "a");
  Term b = d_solver.mkConst(bvsort, "b");

  Term ab = d_solver.mkTerm(SELECT, {a, b});
  Op ext = d_solver.mkOp(BITVECTOR_EXTRACT, {4, 0});
  Term extb = d_solver.mkTerm(ext, {b});

  ASSERT_EQ(ab.getOp(), Op(d_solver.getNodeManager(), SELECT));
  // can compare directly to a Kind (will invoke Op constructor)
  ASSERT_EQ(ab.getOp(), Op(d_solver.getNodeManager(), SELECT));

  Term f = d_solver.mkConst(funsort, "f");
  Term fx = d_solver.mkTerm(APPLY_UF, {f, x});

  ASSERT_EQ(fx.getOp(), Op(d_solver.getNodeManager(), APPLY_UF));
  // testing rebuild from op and children

  // Test Datatypes Ops
  Sort sort = d_solver.mkParamSort("T");
  DatatypeDecl listDecl = d_solver.mkDatatypeDecl("paramlist", {sort});
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
  Term consOpTerm = list.getConstructor("cons").getTerm();
  Term nilOpTerm = list.getConstructor("nil").getTerm();
  Term headOpTerm = list["cons"].getSelector("head").getTerm();
  Term tailOpTerm = list["cons"].getSelector("tail").getTerm();

  Term nilTerm = d_solver.mkTerm(APPLY_CONSTRUCTOR, {nilOpTerm});
  Term consTerm = d_solver.mkTerm(APPLY_CONSTRUCTOR,
                                  {consOpTerm, d_solver.mkInteger(0), nilTerm});
  Term headTerm = d_solver.mkTerm(APPLY_SELECTOR, {headOpTerm, consTerm});
  Term tailTerm = d_solver.mkTerm(APPLY_SELECTOR, {tailOpTerm, consTerm});

  ASSERT_EQ(nilTerm.getOp(), Op(d_solver.getNodeManager(), APPLY_CONSTRUCTOR));
  ASSERT_EQ(consTerm.getOp(), Op(d_solver.getNodeManager(), APPLY_CONSTRUCTOR));
  ASSERT_EQ(headTerm.getOp(), Op(d_solver.getNodeManager(), APPLY_SELECTOR));
  ASSERT_EQ(tailTerm.getOp(), Op(d_solver.getNodeManager(), APPLY_SELECTOR));
}
}  // namespace test
}  // namespace cvc5::internal
