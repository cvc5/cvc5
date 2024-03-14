/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Gereon Kremer
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

#include <gtest/gtest.h>

#include <algorithm>
#include <cmath>

#include "base/output.h"
#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackSolver : public TestApi
{
};

TEST_F(TestApiBlackSolver, proj_issue416)
{
  d_solver->setOption("solve-bv-as-int", "sum");
  d_solver->setOption("strings-exp", "true");
  Sort s1 = d_tm.getStringSort();
  Term t27 = d_tm.mkConst(s1, "_x50");
  Term t333 = d_tm.mkRegexpAll();
  Term t1243 = d_tm.mkTerm(Kind::STRING_REPLACE_RE_ALL, {t27, t333, t27});
  Term t1291 = d_tm.mkTerm(Kind::EQUAL, {t1243, t27});
  d_solver->assertFormula(t1291);
  d_solver->checkSat();
}

TEST_F(TestApiBlackSolver, proj_issue435)
{
  d_solver->setOption("strings-exp", "true");
  Sort s1 = d_tm.mkUninterpretedSort("_u0");
  Sort s3 = d_tm.getBooleanSort();
  Sort _p7 = d_tm.mkParamSort("_p7");
  DatatypeDecl _dt5 = d_tm.mkDatatypeDecl("_dt5", {_p7});
  DatatypeConstructorDecl _cons33 = d_tm.mkDatatypeConstructorDecl("_cons33");
  _cons33.addSelector("_sel31", s1);
  _cons33.addSelector("_sel32", _p7);
  _dt5.addConstructor(_cons33);
  std::vector<Sort> _s6 = d_tm.mkDatatypeSorts({_dt5});
  Sort s6 = _s6[0];
  Sort s21 = s6.instantiate({s3});
  Sort s42 = d_tm.mkSequenceSort(s21);
  Term t40 = d_tm.mkConst(s42, "_x64");
  Term t75 = d_tm.mkTerm(Kind::SEQ_REV, {t40});
  Term t91 = d_tm.mkTerm(Kind::SEQ_PREFIX, {t75, t40});
  d_solver->checkSatAssuming({t91});
}

TEST_F(TestApiBlackSolver, pow2Large1)
{
  // Based on https://github.com/cvc5/cvc5-projects/issues/371
  Sort s1 = d_tm.getStringSort();
  Sort s2 = d_tm.getIntegerSort();
  Sort s4 = d_tm.mkArraySort(s1, s2);
  Sort s7 = d_tm.mkArraySort(s2, s1);
  Term t10 = d_tm.mkInteger("68038927088685865242724985643");
  Term t74 = d_tm.mkInteger("8416288636405");
  std::vector<DatatypeConstructorDecl> ctors;
  ctors.push_back(d_tm.mkDatatypeConstructorDecl("_x109"));
  ctors.back().addSelector("_x108", s7);
  ctors.push_back(d_tm.mkDatatypeConstructorDecl("_x113"));
  ctors.back().addSelector("_x110", s4);
  ctors.back().addSelector("_x111", s2);
  ctors.back().addSelector("_x112", s7);
  Sort s11 = d_solver->declareDatatype("_x107", ctors);
  Term t82 = d_tm.mkConst(s11, "_x114");
  Term t180 = d_tm.mkTerm(Kind::POW2, {t10});
  Term t258 = d_tm.mkTerm(Kind::GEQ, {t74, t180});
  d_solver->assertFormula(t258);
  ASSERT_THROW(d_solver->simplify(t82), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, pow2Large2)
{
  // Based on https://github.com/cvc5/cvc5-projects/issues/333
  Term t1 = d_tm.mkBitVector(63, ~(((uint64_t)1) << 62));
  Term t2 = d_tm.mkTerm(Kind::BITVECTOR_TO_NAT, {t1});
  Term t3 = d_tm.mkTerm(Kind::POW2, {t2});
  Term t4 = d_tm.mkTerm(Kind::DISTINCT, {t3, t2});
  ASSERT_THROW(d_solver->checkSatAssuming({t4}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, pow2Large3)
{
  // Based on https://github.com/cvc5/cvc5-projects/issues/339
  Sort s4 = d_tm.getIntegerSort();
  Term t203 = d_tm.mkInteger("6135470354240554220207");
  Term t262 = d_tm.mkTerm(Kind::POW2, {t203});
  Term t536 = d_tm.mkTerm(d_tm.mkOp(Kind::INT_TO_BITVECTOR, {49}), {t262});
  // should not throw an exception, will not simplify.
  ASSERT_NO_THROW(d_solver->simplify(t536));
}

TEST_F(TestApiBlackSolver, recoverableException)
{
  d_solver->setOption("produce-models", "true");
  Term x = d_tm.mkConst(d_tm.getBooleanSort(), "x");
  d_solver->assertFormula(x.eqTerm(x).notTerm());
  ASSERT_THROW(d_solver->getValue(x), CVC5ApiRecoverableException);

  try
  {
    d_solver->getValue(x);
  }
  catch (const CVC5ApiRecoverableException& e)
  {
    ASSERT_NO_THROW(e.what());
    ASSERT_NO_THROW(e.getMessage());
  }
}

TEST_F(TestApiBlackSolver, declareFunFresh)
{
  Sort boolSort = d_tm.getBooleanSort();
  Sort intSort = d_tm.getIntegerSort();
  Term t1 = d_solver->declareFun(std::string("b"), {}, boolSort, true);
  Term t2 = d_solver->declareFun(std::string("b"), {}, boolSort, false);
  Term t3 = d_solver->declareFun(std::string("b"), {}, boolSort, false);
  ASSERT_FALSE(t1 == t2);
  ASSERT_FALSE(t1 == t3);
  ASSERT_TRUE(t2 == t3);
  Term t4 = d_solver->declareFun(std::string("c"), {}, boolSort, false);
  ASSERT_FALSE(t2 == t4);
  Term t5 = d_solver->declareFun(std::string("b"), {}, intSort, false);
  ASSERT_FALSE(t2 == t5);
}

TEST_F(TestApiBlackSolver, declareDatatype)
{
  DatatypeConstructorDecl lin = d_tm.mkDatatypeConstructorDecl("lin");
  std::vector<DatatypeConstructorDecl> ctors0 = {lin};
  ASSERT_NO_THROW(d_solver->declareDatatype(std::string(""), ctors0));

  DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
  std::vector<DatatypeConstructorDecl> ctors1 = {nil};
  ASSERT_NO_THROW(d_solver->declareDatatype(std::string("a"), ctors1));

  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  DatatypeConstructorDecl nil2 = d_tm.mkDatatypeConstructorDecl("nil");
  std::vector<DatatypeConstructorDecl> ctors2 = {cons, nil2};
  ASSERT_NO_THROW(d_solver->declareDatatype(std::string("b"), ctors2));

  DatatypeConstructorDecl cons2 = d_tm.mkDatatypeConstructorDecl("cons");
  DatatypeConstructorDecl nil3 = d_tm.mkDatatypeConstructorDecl("nil");
  std::vector<DatatypeConstructorDecl> ctors3 = {cons2, nil3};
  ASSERT_NO_THROW(d_solver->declareDatatype(std::string(""), ctors3));

  // must have at least one constructor
  std::vector<DatatypeConstructorDecl> ctors4;
  ASSERT_THROW(d_solver->declareDatatype(std::string("c"), ctors4),
               CVC5ApiException);
  // constructors may not be reused
  DatatypeConstructorDecl ctor1 = d_tm.mkDatatypeConstructorDecl("_x21");
  DatatypeConstructorDecl ctor2 = d_tm.mkDatatypeConstructorDecl("_x31");
  Sort s3 = d_solver->declareDatatype(std::string("_x17"), {ctor1, ctor2});
  ASSERT_THROW(d_solver->declareDatatype(std::string("_x86"), {ctor1, ctor2}),
               CVC5ApiException);
  Solver slv(d_tm);
  ASSERT_THROW(slv.declareDatatype(std::string("a"), ctors1), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, declareFun)
{
  Sort bvSort = d_tm.mkBitVectorSort(32);
  Sort funSort = d_tm.mkFunctionSort({d_tm.mkUninterpretedSort("u")},
                                     d_tm.getIntegerSort());
  ASSERT_NO_THROW(d_solver->declareFun("f1", {}, bvSort));
  ASSERT_NO_THROW(
      d_solver->declareFun("f3", {bvSort, d_tm.getIntegerSort()}, bvSort));
  ASSERT_THROW(d_solver->declareFun("f2", {}, funSort), CVC5ApiException);
  // functions as arguments is allowed
  ASSERT_NO_THROW(d_solver->declareFun("f4", {bvSort, funSort}, bvSort));
  ASSERT_THROW(d_solver->declareFun("f5", {bvSort, bvSort}, funSort),
               CVC5ApiException);
  Solver slv(d_tm);
  ASSERT_NO_THROW(slv.declareFun("f1", {}, bvSort));
}

TEST_F(TestApiBlackSolver, declareSort)
{
  ASSERT_NO_THROW(d_solver->declareSort("s", 0));
  ASSERT_NO_THROW(d_solver->declareSort("s", 2));
  ASSERT_NO_THROW(d_solver->declareSort("", 2));
}

TEST_F(TestApiBlackSolver, declareSortFresh)
{
  Sort t1 = d_solver->declareSort(std::string("b"), 0, true);
  Sort t2 = d_solver->declareSort(std::string("b"), 0, false);
  Sort t3 = d_solver->declareSort(std::string("b"), 0, false);
  ASSERT_FALSE(t1 == t2);
  ASSERT_FALSE(t1 == t3);
  ASSERT_TRUE(t2 == t3);
  Sort t4 = d_solver->declareSort(std::string("c"), 0, false);
  ASSERT_FALSE(t2 == t4);
  Sort t5 = d_solver->declareSort(std::string("b"), 1, false);
  ASSERT_FALSE(t2 == t5);
}

TEST_F(TestApiBlackSolver, defineFun)
{
  Sort bvSort = d_tm.mkBitVectorSort(32);
  Sort funSort = d_tm.mkFunctionSort({d_tm.mkUninterpretedSort("u")},
                                     d_tm.getIntegerSort());
  Term b1 = d_tm.mkVar(bvSort, "b1");
  Term b2 = d_tm.mkVar(d_tm.getIntegerSort(), "b2");
  Term b3 = d_tm.mkVar(funSort, "b3");
  Term v1 = d_tm.mkConst(bvSort, "v1");
  Term v2 = d_tm.mkConst(funSort, "v2");
  ASSERT_NO_THROW(d_solver->defineFun("f", {}, bvSort, v1));
  ASSERT_NO_THROW(d_solver->defineFun("ff", {b1, b2}, bvSort, v1));
  ASSERT_THROW(d_solver->defineFun("ff", {v1, b2}, bvSort, v1),
               CVC5ApiException);
  ASSERT_THROW(d_solver->defineFun("fff", {b1}, bvSort, v2), CVC5ApiException);
  ASSERT_THROW(d_solver->defineFun("ffff", {b1}, funSort, v2),
               CVC5ApiException);
  // b3 has function sort, which is allowed as an argument
  ASSERT_NO_THROW(d_solver->defineFun("fffff", {b1, b3}, bvSort, v1));

  Solver slv(d_tm);
  Sort bvSort2 = d_tm.mkBitVectorSort(32);
  Term v12 = d_tm.mkConst(bvSort2, "v1");
  Term b12 = d_tm.mkVar(bvSort2, "b1");
  Term b22 = d_tm.mkVar(d_tm.getIntegerSort(), "b2");
  ASSERT_NO_THROW(slv.defineFun("f", {}, bvSort, v12));
  ASSERT_NO_THROW(slv.defineFun("f", {}, bvSort2, v1));
  ASSERT_NO_THROW(slv.defineFun("ff", {b1, b22}, bvSort2, v12));
  ASSERT_NO_THROW(slv.defineFun("ff", {b12, b2}, bvSort2, v12));
  ASSERT_NO_THROW(slv.defineFun("ff", {b12, b22}, bvSort, v12));
  ASSERT_NO_THROW(slv.defineFun("ff", {b12, b22}, bvSort2, v1));
}

TEST_F(TestApiBlackSolver, defineFunGlobal)
{
  Sort bSort = d_tm.getBooleanSort();

  Term bTrue = d_tm.mkBoolean(true);
  // (define-fun f () Bool true)
  Term f = d_solver->defineFun("f", {}, bSort, bTrue, true);
  Term b = d_tm.mkVar(bSort, "b");
  // (define-fun g (b Bool) Bool b)
  Term g = d_solver->defineFun("g", {b}, bSort, b, true);

  // (assert (or (not f) (not (g true))))
  d_solver->assertFormula(d_tm.mkTerm(
      Kind::OR,
      {f.notTerm(), d_tm.mkTerm(Kind::APPLY_UF, {g, bTrue}).notTerm()}));
  ASSERT_TRUE(d_solver->checkSat().isUnsat());
  d_solver->resetAssertions();
  // (assert (or (not f) (not (g true))))
  d_solver->assertFormula(d_tm.mkTerm(
      Kind::OR,
      {f.notTerm(), d_tm.mkTerm(Kind::APPLY_UF, {g, bTrue}).notTerm()}));
  ASSERT_TRUE(d_solver->checkSat().isUnsat());
}

TEST_F(TestApiBlackSolver, defineFunRec)
{
  Sort bvSort = d_tm.mkBitVectorSort(32);
  Sort funSort1 = d_tm.mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_tm.mkFunctionSort({d_tm.mkUninterpretedSort("u")},
                                      d_tm.getIntegerSort());
  Term b1 = d_tm.mkVar(bvSort, "b1");
  Term b11 = d_tm.mkVar(bvSort, "b1");
  Term b2 = d_tm.mkVar(d_tm.getIntegerSort(), "b2");
  Term b3 = d_tm.mkVar(funSort2, "b3");
  Term v1 = d_tm.mkConst(bvSort, "v1");
  Term v2 = d_tm.mkConst(d_tm.getIntegerSort(), "v2");
  Term v3 = d_tm.mkConst(funSort2, "v3");
  Term f1 = d_tm.mkConst(funSort1, "f1");
  Term f2 = d_tm.mkConst(funSort2, "f2");
  Term f3 = d_tm.mkConst(bvSort, "f3");
  ASSERT_NO_THROW(d_solver->defineFunRec("f", {}, bvSort, v1));
  ASSERT_NO_THROW(d_solver->defineFunRec("ff", {b1, b2}, bvSort, v1));
  ASSERT_NO_THROW(d_solver->defineFunRec(f1, {b1, b11}, v1));
  ASSERT_THROW(d_solver->defineFunRec("fff", {b1}, bvSort, v3),
               CVC5ApiException);
  ASSERT_THROW(d_solver->defineFunRec("ff", {b1, v2}, bvSort, v1),
               CVC5ApiException);
  ASSERT_THROW(d_solver->defineFunRec("ffff", {b1}, funSort2, v3),
               CVC5ApiException);
  // b3 has function sort, which is allowed as an argument
  ASSERT_NO_THROW(d_solver->defineFunRec("fffff", {b1, b3}, bvSort, v1));
  ASSERT_THROW(d_solver->defineFunRec(f1, {b1}, v1), CVC5ApiException);
  ASSERT_THROW(d_solver->defineFunRec(f1, {b1, b11}, v2), CVC5ApiException);
  ASSERT_THROW(d_solver->defineFunRec(f1, {b1, b11}, v3), CVC5ApiException);
  ASSERT_THROW(d_solver->defineFunRec(f2, {b1}, v2), CVC5ApiException);
  ASSERT_THROW(d_solver->defineFunRec(f3, {b1}, v1), CVC5ApiException);

  Solver slv(d_tm);
  Sort bvSort2 = d_tm.mkBitVectorSort(32);
  Term v12 = d_tm.mkConst(bvSort2, "v1");
  Term b12 = d_tm.mkVar(bvSort2, "b1");
  Term b22 = d_tm.mkVar(d_tm.getIntegerSort(), "b2");
  ASSERT_NO_THROW(slv.defineFunRec("f", {}, bvSort2, v12));
  ASSERT_NO_THROW(slv.defineFunRec("ff", {b12, b22}, bvSort2, v12));
  ASSERT_NO_THROW(slv.defineFunRec("f", {}, bvSort, v12));
  ASSERT_NO_THROW(slv.defineFunRec("f", {}, bvSort2, v1));
  ASSERT_NO_THROW(slv.defineFunRec("ff", {b1, b22}, bvSort2, v12));
  ASSERT_NO_THROW(slv.defineFunRec("ff", {b12, b2}, bvSort2, v12));
  ASSERT_NO_THROW(slv.defineFunRec("ff", {b12, b22}, bvSort, v12));
  ASSERT_NO_THROW(slv.defineFunRec("ff", {b12, b22}, bvSort2, v1));
}

TEST_F(TestApiBlackSolver, defineFunRecWrongLogic)
{
  d_solver->setLogic("QF_BV");
  Sort bvSort = d_tm.mkBitVectorSort(32);
  Sort funSort = d_tm.mkFunctionSort({bvSort, bvSort}, bvSort);
  Term b = d_tm.mkVar(bvSort, "b");
  Term v = d_tm.mkConst(bvSort, "v");
  Term f = d_tm.mkConst(funSort, "f");
  ASSERT_THROW(d_solver->defineFunRec("f", {}, bvSort, v), CVC5ApiException);
  ASSERT_THROW(d_solver->defineFunRec(f, {b, b}, v), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, defineFunRecGlobal)
{
  Sort bSort = d_tm.getBooleanSort();
  Sort fSort = d_tm.mkFunctionSort({bSort}, bSort);

  d_solver->push();
  Term bTrue = d_tm.mkBoolean(true);
  // (define-fun f () Bool true)
  Term f = d_solver->defineFunRec("f", {}, bSort, bTrue, true);
  Term b = d_tm.mkVar(bSort, "b");
  Term gSym = d_tm.mkConst(fSort, "g");
  // (define-fun g (b Bool) Bool b)
  Term g = d_solver->defineFunRec(gSym, {b}, b, true);

  // (assert (or (not f) (not (g true))))
  d_solver->assertFormula(d_tm.mkTerm(
      Kind::OR,
      {f.notTerm(), d_tm.mkTerm(Kind::APPLY_UF, {g, bTrue}).notTerm()}));
  ASSERT_TRUE(d_solver->checkSat().isUnsat());
  d_solver->pop();
  // (assert (or (not f) (not (g true))))
  d_solver->assertFormula(d_tm.mkTerm(
      Kind::OR,
      {f.notTerm(), d_tm.mkTerm(Kind::APPLY_UF, {g, bTrue}).notTerm()}));
  ASSERT_TRUE(d_solver->checkSat().isUnsat());
}

TEST_F(TestApiBlackSolver, defineFunsRec)
{
  Sort uSort = d_tm.mkUninterpretedSort("u");
  Sort bvSort = d_tm.mkBitVectorSort(32);
  Sort funSort1 = d_tm.mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_tm.mkFunctionSort({uSort}, d_tm.getIntegerSort());
  Term b1 = d_tm.mkVar(bvSort, "b1");
  Term b11 = d_tm.mkVar(bvSort, "b1");
  Term b2 = d_tm.mkVar(d_tm.getIntegerSort(), "b2");
  Term b3 = d_tm.mkVar(funSort2, "b3");
  Term b4 = d_tm.mkVar(uSort, "b4");
  Term v1 = d_tm.mkConst(bvSort, "v1");
  Term v2 = d_tm.mkConst(d_tm.getIntegerSort(), "v2");
  Term v3 = d_tm.mkConst(funSort2, "v3");
  Term v4 = d_tm.mkConst(uSort, "v4");
  Term f1 = d_tm.mkConst(funSort1, "f1");
  Term f2 = d_tm.mkConst(funSort2, "f2");
  Term f3 = d_tm.mkConst(bvSort, "f3");
  ASSERT_NO_THROW(
      d_solver->defineFunsRec({f1, f2}, {{b1, b11}, {b4}}, {v1, v2}));
  ASSERT_THROW(d_solver->defineFunsRec({f1, f2}, {{v1, b11}, {b4}}, {v1, v2}),
               CVC5ApiException);
  ASSERT_THROW(d_solver->defineFunsRec({f1, f3}, {{b1, b11}, {b4}}, {v1, v2}),
               CVC5ApiException);
  ASSERT_THROW(d_solver->defineFunsRec({f1, f2}, {{b1}, {b4}}, {v1, v2}),
               CVC5ApiException);
  ASSERT_THROW(d_solver->defineFunsRec({f1, f2}, {{b1, b2}, {b4}}, {v1, v2}),
               CVC5ApiException);
  ASSERT_THROW(d_solver->defineFunsRec({f1, f2}, {{b1, b11}, {b4}}, {v1, v4}),
               CVC5ApiException);

  Solver slv(d_tm);
  Sort uSort2 = d_tm.mkUninterpretedSort("u");
  Sort bvSort2 = d_tm.mkBitVectorSort(32);
  Sort funSort12 = d_tm.mkFunctionSort({bvSort2, bvSort2}, bvSort2);
  Sort funSort22 = d_tm.mkFunctionSort({uSort2}, d_tm.getIntegerSort());
  Term b12 = d_tm.mkVar(bvSort2, "b1");
  Term b112 = d_tm.mkVar(bvSort2, "b1");
  Term b42 = d_tm.mkVar(uSort2, "b4");
  Term v12 = d_tm.mkConst(bvSort2, "v1");
  Term v22 = d_tm.mkConst(d_tm.getIntegerSort(), "v2");
  Term f12 = d_tm.mkConst(funSort12, "f1");
  Term f22 = d_tm.mkConst(funSort22, "f2");
  ASSERT_NO_THROW(
      slv.defineFunsRec({f12, f22}, {{b12, b112}, {b42}}, {v12, v22}));
  ASSERT_NO_THROW(
      slv.defineFunsRec({f1, f22}, {{b12, b112}, {b42}}, {v12, v22}));
  ASSERT_THROW(slv.defineFunsRec({f12, f2}, {{b12, b112}, {b42}}, {v12, v22}),
               CVC5ApiException);
  ASSERT_NO_THROW(
      slv.defineFunsRec({f12, f22}, {{b1, b112}, {b42}}, {v12, v22}));
  ASSERT_NO_THROW(
      slv.defineFunsRec({f12, f22}, {{b12, b11}, {b42}}, {v12, v22}));
  ASSERT_THROW(slv.defineFunsRec({f12, f22}, {{b12, b112}, {b4}}, {v12, v22}),
               CVC5ApiException);
  ASSERT_NO_THROW(
      slv.defineFunsRec({f12, f22}, {{b12, b112}, {b42}}, {v1, v22}));
  ASSERT_NO_THROW(
      slv.defineFunsRec({f12, f22}, {{b12, b112}, {b42}}, {v12, v2}));
}

TEST_F(TestApiBlackSolver, defineFunsRecWrongLogic)
{
  d_solver->setLogic("QF_BV");
  Sort uSort = d_tm.mkUninterpretedSort("u");
  Sort bvSort = d_tm.mkBitVectorSort(32);
  Sort funSort1 = d_tm.mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_tm.mkFunctionSort({uSort}, d_tm.getIntegerSort());
  Term b = d_tm.mkVar(bvSort, "b");
  Term u = d_tm.mkVar(uSort, "u");
  Term v1 = d_tm.mkConst(bvSort, "v1");
  Term v2 = d_tm.mkConst(d_tm.getIntegerSort(), "v2");
  Term f1 = d_tm.mkConst(funSort1, "f1");
  Term f2 = d_tm.mkConst(funSort2, "f2");
  ASSERT_THROW(d_solver->defineFunsRec({f1, f2}, {{b, b}, {u}}, {v1, v2}),
               CVC5ApiException);
}

TEST_F(TestApiBlackSolver, defineFunsRecGlobal)
{
  Sort bSort = d_tm.getBooleanSort();
  Sort fSort = d_tm.mkFunctionSort({bSort}, bSort);

  d_solver->push();
  Term bTrue = d_tm.mkBoolean(true);
  Term b = d_tm.mkVar(bSort, "b");
  Term gSym = d_tm.mkConst(fSort, "g");
  // (define-funs-rec ((g ((b Bool)) Bool)) (b))
  d_solver->defineFunsRec({gSym}, {{b}}, {b}, true);

  // (assert (not (g true)))
  d_solver->assertFormula(d_tm.mkTerm(Kind::APPLY_UF, {gSym, bTrue}).notTerm());
  ASSERT_TRUE(d_solver->checkSat().isUnsat());
  d_solver->pop();
  // (assert (not (g true)))
  d_solver->assertFormula(d_tm.mkTerm(Kind::APPLY_UF, {gSym, bTrue}).notTerm());
  ASSERT_TRUE(d_solver->checkSat().isUnsat());
}

TEST_F(TestApiBlackSolver, uFIteration)
{
  Sort intSort = d_tm.getIntegerSort();
  Sort funSort = d_tm.mkFunctionSort({intSort, intSort}, intSort);
  Term x = d_tm.mkConst(intSort, "x");
  Term y = d_tm.mkConst(intSort, "y");
  Term f = d_tm.mkConst(funSort, "f");
  Term fxy = d_tm.mkTerm(Kind::APPLY_UF, {f, x, y});

  // Expecting the uninterpreted function to be one of the children
  Term expected_children[3] = {f, x, y};
  uint32_t idx = 0;
  for (auto c : fxy)
  {
    ASSERT_LT(idx, 3);
    ASSERT_EQ(c, expected_children[idx]);
    idx++;
  }
}

TEST_F(TestApiBlackSolver, getAssertions)
{
  Term a = d_tm.mkConst(d_tm.getBooleanSort(), "a");
  Term b = d_tm.mkConst(d_tm.getBooleanSort(), "b");
  d_solver->assertFormula(a);
  d_solver->assertFormula(b);
  std::vector<Term> asserts{a, b};
  ASSERT_EQ(d_solver->getAssertions(), asserts);
}

TEST_F(TestApiBlackSolver, getInfo)
{
  ASSERT_NO_THROW(d_solver->getInfo("name"));
  ASSERT_THROW(d_solver->getInfo("asdf"), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getAbduct)
{
  d_solver->setLogic("QF_LIA");
  d_solver->setOption("produce-abducts", "true");
  d_solver->setOption("incremental", "false");

  Sort intSort = d_tm.getIntegerSort();
  Term zero = d_tm.mkInteger(0);
  Term x = d_tm.mkConst(intSort, "x");
  Term y = d_tm.mkConst(intSort, "y");

  // Assumptions for abduction: x > 0
  d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {x, zero}));
  // Conjecture for abduction: y > 0
  Term conj = d_tm.mkTerm(Kind::GT, {y, zero});
  // Call the abduction api, while the resulting abduct is the output
  Term output = d_solver->getAbduct(conj);
  // We expect the resulting output to be a boolean formula
  ASSERT_TRUE(!output.isNull() && output.getSort().isBoolean());

  // try with a grammar, a simple grammar admitting true
  Sort boolean = d_tm.getBooleanSort();
  Term truen = d_tm.mkBoolean(true);
  Term start = d_tm.mkVar(boolean);
  Term output2;
  Grammar g = d_solver->mkGrammar({}, {start});
  Term conj2 = d_tm.mkTerm(Kind::GT, {x, zero});
  ASSERT_NO_THROW(g.addRule(start, truen));
  // Call the abduction api, while the resulting abduct is the output
  output2 = d_solver->getAbduct(conj2, g);
  // abduct must be true
  ASSERT_EQ(output2, truen);
}

TEST_F(TestApiBlackSolver, getAbduct2)
{
  d_solver->setLogic("QF_LIA");
  d_solver->setOption("incremental", "false");
  Sort intSort = d_tm.getIntegerSort();
  Term zero = d_tm.mkInteger(0);
  Term x = d_tm.mkConst(intSort, "x");
  Term y = d_tm.mkConst(intSort, "y");
  // Assumptions for abduction: x > 0
  d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {x, zero}));
  // Conjecture for abduction: y > 0
  Term conj = d_tm.mkTerm(Kind::GT, {y, zero});
  // Fails due to option not set
  ASSERT_THROW(d_solver->getAbduct(conj), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getAbductNext)
{
  d_solver->setLogic("QF_LIA");
  d_solver->setOption("produce-abducts", "true");
  d_solver->setOption("incremental", "true");

  Sort intSort = d_tm.getIntegerSort();
  Term zero = d_tm.mkInteger(0);
  Term x = d_tm.mkConst(intSort, "x");
  Term y = d_tm.mkConst(intSort, "y");

  // Assumptions for abduction: x > 0
  d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {x, zero}));
  // Conjecture for abduction: y > 0
  Term conj = d_tm.mkTerm(Kind::GT, {y, zero});
  // Call the abduction api, while the resulting abduct is the output
  Term output = d_solver->getAbduct(conj);
  Term output2 = d_solver->getAbductNext();
  // should produce a different output
  ASSERT_TRUE(output != output2);
}

TEST_F(TestApiBlackSolver, getInterpolant)
{
  d_solver->setLogic("QF_LIA");
  d_solver->setOption("produce-interpolants", "true");
  d_solver->setOption("incremental", "false");

  Sort intSort = d_tm.getIntegerSort();
  Term zero = d_tm.mkInteger(0);
  Term x = d_tm.mkConst(intSort, "x");
  Term y = d_tm.mkConst(intSort, "y");
  Term z = d_tm.mkConst(intSort, "z");

  // Assumptions for interpolation: x + y > 0 /\ x < 0
  d_solver->assertFormula(
      d_tm.mkTerm(Kind::GT, {d_tm.mkTerm(Kind::ADD, {x, y}), zero}));
  d_solver->assertFormula(d_tm.mkTerm(Kind::LT, {x, zero}));
  // Conjecture for interpolation: y + z > 0 \/ z < 0
  Term conj = d_tm.mkTerm(
      Kind::OR,
      {d_tm.mkTerm(Kind::GT, {d_tm.mkTerm(Kind::ADD, {y, z}), zero}),
       d_tm.mkTerm(Kind::LT, {z, zero})});
  // Call the interpolation api, while the resulting interpolant is the output
  Term output = d_solver->getInterpolant(conj);
  // We expect the resulting output to be a boolean formula
  ASSERT_TRUE(output.getSort().isBoolean());

  // try with a grammar, a simple grammar admitting true
  Sort boolean = d_tm.getBooleanSort();
  Term truen = d_tm.mkBoolean(true);
  Term start = d_tm.mkVar(boolean);
  Grammar g = d_solver->mkGrammar({}, {start});
  Term conj2 = d_tm.mkTerm(Kind::EQUAL, {zero, zero});
  ASSERT_NO_THROW(g.addRule(start, truen));
  // Call the interpolation api, while the resulting interpolant is the output
  Term output2 = d_solver->getInterpolant(conj2, g);
  // interpolant must be true
  ASSERT_EQ(output2, truen);
}

TEST_F(TestApiBlackSolver, getInterpolantNext)
{
  d_solver->setLogic("QF_LIA");
  d_solver->setOption("produce-interpolants", "true");
  d_solver->setOption("incremental", "true");

  Sort intSort = d_tm.getIntegerSort();
  Term zero = d_tm.mkInteger(0);
  Term x = d_tm.mkConst(intSort, "x");
  Term y = d_tm.mkConst(intSort, "y");
  Term z = d_tm.mkConst(intSort, "z");
  // Assumptions for interpolation: x + y > 0 /\ x < 0
  d_solver->assertFormula(
      d_tm.mkTerm(Kind::GT, {d_tm.mkTerm(Kind::ADD, {x, y}), zero}));
  d_solver->assertFormula(d_tm.mkTerm(Kind::LT, {x, zero}));
  // Conjecture for interpolation: y + z > 0 \/ z < 0
  Term conj = d_tm.mkTerm(
      Kind::OR,
      {d_tm.mkTerm(Kind::GT, {d_tm.mkTerm(Kind::ADD, {y, z}), zero}),
       d_tm.mkTerm(Kind::LT, {z, zero})});
  Term output = d_solver->getInterpolant(conj);
  Term output2 = d_solver->getInterpolantNext();

  // We expect the next output to be distinct
  ASSERT_TRUE(output != output2);
}

TEST_F(TestApiBlackSolver, declarePool)
{
  Sort intSort = d_tm.getIntegerSort();
  Sort setSort = d_tm.mkSetSort(intSort);
  Term zero = d_tm.mkInteger(0);
  Term x = d_tm.mkConst(intSort, "x");
  Term y = d_tm.mkConst(intSort, "y");
  // declare a pool with initial value { 0, x, y }
  Term p = d_solver->declarePool("p", intSort, {zero, x, y});
  // pool should have the same sort
  ASSERT_TRUE(p.getSort() == setSort);
  // cannot pass null sort
  Sort nullSort;
  ASSERT_THROW(d_solver->declarePool("i", nullSort, {}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getOption)
{
  ASSERT_NO_THROW(d_solver->getOption("incremental"));
  ASSERT_THROW(d_solver->getOption("asdf"), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getOptionNames)
{
  std::vector<std::string> names = d_solver->getOptionNames();
  ASSERT_TRUE(names.size() > 100);
  ASSERT_NE(std::find(names.begin(), names.end(), "verbose"), names.end());
  ASSERT_EQ(std::find(names.begin(), names.end(), "foobar"), names.end());
}

TEST_F(TestApiBlackSolver, getOptionInfo)
{
  {
    ASSERT_THROW(d_solver->getOptionInfo("asdf-invalid"), CVC5ApiException);
  }
  {
    cvc5::OptionInfo info = d_solver->getOptionInfo("verbose");
    ASSERT_EQ("verbose", info.name);
    ASSERT_EQ(std::vector<std::string>{}, info.aliases);
    ASSERT_TRUE(std::holds_alternative<OptionInfo::VoidInfo>(info.valueInfo));
    std::stringstream ss;
    ss << info;
    ASSERT_EQ(ss.str(), "OptionInfo{ verbose | void }");
  }
  {
    // bool type with default
    cvc5::OptionInfo info = d_solver->getOptionInfo("print-success");
    ASSERT_EQ("print-success", info.name);
    ASSERT_EQ(std::vector<std::string>{}, info.aliases);
    ASSERT_TRUE(
        std::holds_alternative<OptionInfo::ValueInfo<bool>>(info.valueInfo));
    auto valInfo = std::get<OptionInfo::ValueInfo<bool>>(info.valueInfo);
    ASSERT_EQ(false, valInfo.defaultValue);
    ASSERT_EQ(false, valInfo.currentValue);
    ASSERT_EQ(info.boolValue(), false);
    std::stringstream ss;
    ss << info;
    ASSERT_EQ(ss.str(),
              "OptionInfo{ print-success | bool | false | default false }");
  }
  {
    // int64 type with default
    cvc5::OptionInfo info = d_solver->getOptionInfo("verbosity");
    ASSERT_EQ("verbosity", info.name);
    ASSERT_EQ(std::vector<std::string>{}, info.aliases);
    ASSERT_TRUE(std::holds_alternative<OptionInfo::NumberInfo<int64_t>>(
        info.valueInfo));
    auto numInfo = std::get<OptionInfo::NumberInfo<int64_t>>(info.valueInfo);
    ASSERT_EQ(0, numInfo.defaultValue);
    ASSERT_EQ(0, numInfo.currentValue);
    ASSERT_FALSE(numInfo.minimum || numInfo.maximum);
    ASSERT_EQ(info.intValue(), 0);
    std::stringstream ss;
    ss << info;
    ASSERT_EQ(ss.str(), "OptionInfo{ verbosity | int64_t | 0 | default 0 }");
  }
  {
    // uint64 type with default
    cvc5::OptionInfo info = d_solver->getOptionInfo("rlimit");
    ASSERT_EQ("rlimit", info.name);
    ASSERT_EQ(std::vector<std::string>{}, info.aliases);
    ASSERT_TRUE(std::holds_alternative<OptionInfo::NumberInfo<uint64_t>>(
        info.valueInfo));
    auto numInfo = std::get<OptionInfo::NumberInfo<uint64_t>>(info.valueInfo);
    ASSERT_EQ(0, numInfo.defaultValue);
    ASSERT_EQ(0, numInfo.currentValue);
    ASSERT_FALSE(numInfo.minimum || numInfo.maximum);
    ASSERT_EQ(info.uintValue(), 0);
    std::stringstream ss;
    ss << info;
    ASSERT_EQ(ss.str(), "OptionInfo{ rlimit | uint64_t | 0 | default 0 }");
  }
  {
    auto info = d_solver->getOptionInfo("random-freq");
    ASSERT_EQ(info.name, "random-freq");
    ASSERT_EQ(info.aliases, std::vector<std::string>{"random-frequency"});
    ASSERT_TRUE(std::holds_alternative<cvc5::OptionInfo::NumberInfo<double>>(
        info.valueInfo));
    auto ni = std::get<cvc5::OptionInfo::NumberInfo<double>>(info.valueInfo);
    ASSERT_EQ(ni.currentValue, 0.0);
    ASSERT_EQ(ni.defaultValue, 0.0);
    ASSERT_TRUE(ni.minimum && ni.maximum);
    ASSERT_EQ(*ni.minimum, 0.0);
    ASSERT_EQ(*ni.maximum, 1.0);
    ASSERT_EQ(info.doubleValue(), 0.0);
    std::stringstream ss;
    ss << info;
    ASSERT_EQ(ss.str(),
              "OptionInfo{ random-freq, random-frequency | double | 0 | "
              "default 0 | 0 <= x <= 1 }");
  }
  {
    // string type with default
    cvc5::OptionInfo info = d_solver->getOptionInfo("force-logic");
    ASSERT_EQ("force-logic", info.name);
    ASSERT_EQ(std::vector<std::string>{}, info.aliases);
    ASSERT_TRUE(std::holds_alternative<OptionInfo::ValueInfo<std::string>>(
        info.valueInfo));
    auto valInfo = std::get<OptionInfo::ValueInfo<std::string>>(info.valueInfo);
    ASSERT_EQ("", valInfo.defaultValue);
    ASSERT_EQ("", valInfo.currentValue);
    ASSERT_EQ(info.stringValue(), "");
    std::stringstream ss;
    ss << info;
    ASSERT_EQ(ss.str(),
              "OptionInfo{ force-logic | string | \"\" | default \"\" }");
  }
  {
    // mode option
    cvc5::OptionInfo info = d_solver->getOptionInfo("simplification");
    ASSERT_EQ("simplification", info.name);
    ASSERT_EQ(std::vector<std::string>{"simplification-mode"}, info.aliases);
    ASSERT_TRUE(std::holds_alternative<OptionInfo::ModeInfo>(info.valueInfo));
    auto modeInfo = std::get<OptionInfo::ModeInfo>(info.valueInfo);
    ASSERT_EQ("batch", modeInfo.defaultValue);
    ASSERT_EQ("batch", modeInfo.currentValue);
    ASSERT_EQ(2, modeInfo.modes.size());
    ASSERT_TRUE(std::find(modeInfo.modes.begin(), modeInfo.modes.end(), "batch")
                != modeInfo.modes.end());
    ASSERT_TRUE(std::find(modeInfo.modes.begin(), modeInfo.modes.end(), "none")
                != modeInfo.modes.end());
    std::stringstream ss;
    ss << info;
    ASSERT_EQ(ss.str(),
              "OptionInfo{ simplification, simplification-mode | mode | batch "
              "| default batch | modes: batch, none }");
  }
}

TEST_F(TestApiBlackSolver, getDriverOptions)
{
  auto dopts = d_solver->getDriverOptions();
  ASSERT_EQ(dopts.err().rdbuf(), std::cerr.rdbuf());
  ASSERT_EQ(dopts.in().rdbuf(), std::cin.rdbuf());
  ASSERT_EQ(dopts.out().rdbuf(), std::cout.rdbuf());
}

TEST_F(TestApiBlackSolver, getStatistics)
{
  ASSERT_NO_THROW(cvc5::Stat());
  // do some array reasoning to make sure we have a double statistics
  {
    Sort s1 = d_solver->getIntegerSort();
    Sort s2 = d_solver->mkArraySort(s1, s1);
    Term t1 = d_solver->mkConst(s1, "i");
    Term t2 = d_solver->mkVar(s2, "a");
    Term t3 = d_solver->mkTerm(Kind::SELECT, {t2, t1});
    d_solver->checkSat();
  }
  cvc5::Statistics stats = d_solver->getStatistics();
  {
    std::stringstream ss;
    ss << stats;
  }
  {
    auto s = stats.get("global::totalTime");
    ASSERT_FALSE(s.isInternal());
    ASSERT_FALSE(s.isDefault());
    ASSERT_TRUE(s.isString());
    std::string time = s.getString();
    ASSERT_TRUE(time.rfind("ms") == time.size() - 2);  // ends with "ms"
    ASSERT_FALSE(s.isDouble());
    s = stats.get("resource::resourceUnitsUsed");
    ASSERT_TRUE(s.isInternal());
    ASSERT_FALSE(s.isDefault());
    ASSERT_TRUE(s.isInt());
    ASSERT_TRUE(s.getInt() >= 0);
  }
  for (const auto& s: stats)
  {
    ASSERT_FALSE(s.first.empty());
  }
  for (auto it = stats.begin(true, true); it != stats.end(); ++it)
  {
    {
      auto tmp1 = it, tmp2 = it;
      ++tmp1;
      tmp2++;
      ASSERT_EQ(tmp1, tmp2);
      --tmp1;
      tmp2--;
      ASSERT_EQ(tmp1, tmp2);
      ASSERT_EQ(tmp1, it);
      ASSERT_EQ(it, tmp2);
    }
    const auto& s = *it;
    // check some basic utility methods
    ASSERT_TRUE(!(it == stats.end()));
    ASSERT_EQ(s.first, it->first);
    if (s.first == "cvc5::CONSTANT")
    {
      ASSERT_FALSE(s.second.isInternal());
      ASSERT_FALSE(s.second.isDefault());
      ASSERT_TRUE(s.second.isHistogram());
      auto hist = s.second.getHistogram();
      ASSERT_FALSE(hist.empty());
      std::stringstream ss;
      ss << s.second;
      ASSERT_EQ(ss.str(), "{ integer type: 1 }");
    }
    else if (s.first == "theory::arrays::avgIndexListLength")
    {
      ASSERT_TRUE(s.second.isInternal());
      ASSERT_TRUE(s.second.isDouble());
      ASSERT_TRUE(std::isnan(s.second.getDouble()));
    }
  }
}

TEST_F(TestApiBlackSolver, printStatisticsSafe)
{
  testing::internal::CaptureStdout();
  d_solver->printStatisticsSafe(STDOUT_FILENO);
  testing::internal::GetCapturedStdout();
}

TEST_F(TestApiBlackSolver, getUnsatAssumptions1)
{
  d_solver->setOption("incremental", "false");
  d_solver->checkSatAssuming(d_tm.mkFalse());
  ASSERT_THROW(d_solver->getUnsatAssumptions(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getUnsatAssumptions2)
{
  d_solver->setOption("incremental", "true");
  d_solver->setOption("produce-unsat-assumptions", "false");
  d_solver->checkSatAssuming(d_tm.mkFalse());
  ASSERT_THROW(d_solver->getUnsatAssumptions(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getUnsatAssumptions3)
{
  d_solver->setOption("incremental", "true");
  d_solver->setOption("produce-unsat-assumptions", "true");
  d_solver->checkSatAssuming(d_tm.mkFalse());
  ASSERT_NO_THROW(d_solver->getUnsatAssumptions());
  d_solver->checkSatAssuming(d_tm.mkTrue());
  ASSERT_THROW(d_solver->getUnsatAssumptions(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getUnsatCore1)
{
  d_solver->setOption("incremental", "false");
  d_solver->assertFormula(d_tm.mkFalse());
  d_solver->checkSat();
  ASSERT_THROW(d_solver->getUnsatCore(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getUnsatCore2)
{
  d_solver->setOption("incremental", "false");
  d_solver->setOption("produce-unsat-cores", "false");
  d_solver->assertFormula(d_tm.mkFalse());
  d_solver->checkSat();
  ASSERT_THROW(d_solver->getUnsatCore(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getUnsatCoreAndProof)
{
  d_solver->setOption("incremental", "true");
  d_solver->setOption("produce-unsat-cores", "true");
  d_solver->setOption("produce-proofs", "true");

  Sort uSort = d_tm.mkUninterpretedSort("u");
  Sort intSort = d_tm.getIntegerSort();
  Sort boolSort = d_tm.getBooleanSort();
  Sort uToIntSort = d_tm.mkFunctionSort({uSort}, intSort);
  Sort intPredSort = d_tm.mkFunctionSort({intSort}, boolSort);
  std::vector<Term> uc;

  Term x = d_tm.mkConst(uSort, "x");
  Term y = d_tm.mkConst(uSort, "y");
  Term f = d_tm.mkConst(uToIntSort, "f");
  Term p = d_tm.mkConst(intPredSort, "p");
  Term zero = d_tm.mkInteger(0);
  Term one = d_tm.mkInteger(1);
  Term f_x = d_tm.mkTerm(Kind::APPLY_UF, {f, x});
  Term f_y = d_tm.mkTerm(Kind::APPLY_UF, {f, y});
  Term sum = d_tm.mkTerm(Kind::ADD, {f_x, f_y});
  Term p_0 = d_tm.mkTerm(Kind::APPLY_UF, {p, zero});
  Term p_f_y = d_tm.mkTerm(Kind::APPLY_UF, {p, f_y});
  d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {zero, f_x}));
  d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {zero, f_y}));
  d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {sum, one}));
  d_solver->assertFormula(p_0);
  d_solver->assertFormula(p_f_y.notTerm());
  ASSERT_TRUE(d_solver->checkSat().isUnsat());

  ASSERT_NO_THROW(uc = d_solver->getUnsatCore());
  ASSERT_FALSE(uc.empty());

  ASSERT_NO_THROW(d_solver->getProof());
  ASSERT_NO_THROW(d_solver->getProof(modes::ProofComponent::SAT));

  d_solver->resetAssertions();
  for (const auto& t : uc)
  {
    d_solver->assertFormula(t);
  }
  cvc5::Result res = d_solver->checkSat();
  ASSERT_TRUE(res.isUnsat());
  ASSERT_NO_THROW(d_solver->getProof());
}

TEST_F(TestApiBlackSolver, getUnsatCoreLemmas1)
{
  d_solver->setOption("produce-unsat-cores", "true");
  d_solver->setOption("unsat-cores-mode", "sat-proof");
  // cannot ask before a check sat
  ASSERT_THROW(d_solver->getUnsatCoreLemmas(), CVC5ApiException);

  d_solver->assertFormula(d_tm.mkFalse());
  d_solver->checkSat();
  ASSERT_TRUE(d_solver->checkSat().isUnsat());
  ASSERT_NO_THROW(d_solver->getUnsatCoreLemmas());
}

TEST_F(TestApiBlackSolver, getUnsatCoreLemmas2)
{
  d_solver->setOption("incremental", "true");
  d_solver->setOption("produce-unsat-cores", "true");
  d_solver->setOption("produce-proofs", "true");

  Sort uSort = d_tm.mkUninterpretedSort("u");
  Sort intSort = d_tm.getIntegerSort();
  Sort boolSort = d_tm.getBooleanSort();
  Sort uToIntSort = d_tm.mkFunctionSort({uSort}, intSort);
  Sort intPredSort = d_tm.mkFunctionSort({intSort}, boolSort);

  Term x = d_tm.mkConst(uSort, "x");
  Term y = d_tm.mkConst(uSort, "y");
  Term f = d_tm.mkConst(uToIntSort, "f");
  Term p = d_tm.mkConst(intPredSort, "p");
  Term zero = d_tm.mkInteger(0);
  Term one = d_tm.mkInteger(1);
  Term f_x = d_tm.mkTerm(Kind::APPLY_UF, {f, x});
  Term f_y = d_tm.mkTerm(Kind::APPLY_UF, {f, y});
  Term sum = d_tm.mkTerm(Kind::ADD, {f_x, f_y});
  Term p_0 = d_tm.mkTerm(Kind::APPLY_UF, {p, zero});
  Term p_f_y = d_tm.mkTerm(Kind::APPLY_UF, {p, f_y});
  d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {zero, f_x}));
  d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {zero, f_y}));
  d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {sum, one}));
  d_solver->assertFormula(p_0);
  d_solver->assertFormula(p_f_y.notTerm());
  ASSERT_TRUE(d_solver->checkSat().isUnsat());

  ASSERT_NO_THROW(d_solver->getUnsatCoreLemmas());
}
  
TEST_F(TestApiBlackSolver, getProofAndProofToString)
{
  d_solver->setOption("produce-proofs", "true");

  Sort uSort = d_tm.mkUninterpretedSort("u");
  Sort intSort = d_tm.getIntegerSort();
  Sort boolSort = d_tm.getBooleanSort();
  Sort uToIntSort = d_tm.mkFunctionSort({uSort}, intSort);
  Sort intPredSort = d_tm.mkFunctionSort({intSort}, boolSort);
  std::vector<Proof> proofs;

  Term x = d_tm.mkConst(uSort, "x");
  Term y = d_tm.mkConst(uSort, "y");
  Term f = d_tm.mkConst(uToIntSort, "f");
  Term p = d_tm.mkConst(intPredSort, "p");
  Term zero = d_tm.mkInteger(0);
  Term one = d_tm.mkInteger(1);
  Term f_x = d_tm.mkTerm(Kind::APPLY_UF, {f, x});
  Term f_y = d_tm.mkTerm(Kind::APPLY_UF, {f, y});
  Term sum = d_tm.mkTerm(Kind::ADD, {f_x, f_y});
  Term p_0 = d_tm.mkTerm(Kind::APPLY_UF, {p, zero});
  Term p_f_y = d_tm.mkTerm(Kind::APPLY_UF, {p, f_y});
  d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {zero, f_x}));
  d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {zero, f_y}));
  d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {sum, one}));
  d_solver->assertFormula(p_0);
  d_solver->assertFormula(p_f_y.notTerm());
  ASSERT_TRUE(d_solver->checkSat().isUnsat());

  std::string printedProof;
  ASSERT_NO_THROW(proofs = d_solver->getProof());
  ASSERT_FALSE(proofs.empty());
  ASSERT_NO_THROW(printedProof = d_solver->proofToString(proofs[0]));
  ASSERT_FALSE(printedProof.empty());
  ASSERT_NO_THROW(printedProof = d_solver->proofToString(
                      proofs[0], modes::ProofFormat::ALETHE));
  ASSERT_NO_THROW(proofs = d_solver->getProof(modes::ProofComponent::SAT));
  ASSERT_NO_THROW(printedProof = d_solver->proofToString(
                      proofs[0], modes::ProofFormat::NONE));
  ASSERT_FALSE(printedProof.empty());
}

TEST_F(TestApiBlackSolver, getDifficulty)
{
  d_solver->setOption("produce-difficulty", "true");
  // cannot ask before a check sat
  ASSERT_THROW(d_solver->getDifficulty(), CVC5ApiException);
  d_solver->checkSat();
  ASSERT_NO_THROW(d_solver->getDifficulty());
}

TEST_F(TestApiBlackSolver, getDifficulty2)
{
  d_solver->checkSat();
  // option is not set
  ASSERT_THROW(d_solver->getDifficulty(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getDifficulty3)
{
  d_solver->setOption("produce-difficulty", "true");
  Sort intSort = d_tm.getIntegerSort();
  Term x = d_tm.mkConst(intSort, "x");
  Term zero = d_tm.mkInteger(0);
  Term ten = d_tm.mkInteger(10);
  Term f0 = d_tm.mkTerm(Kind::GEQ, {x, ten});
  Term f1 = d_tm.mkTerm(Kind::GEQ, {zero, x});
  d_solver->assertFormula(f0);
  d_solver->assertFormula(f1);
  d_solver->checkSat();
  std::map<Term, Term> dmap;
  ASSERT_NO_THROW(dmap = d_solver->getDifficulty());
  // difficulty should map assertions to integer values
  for (const std::pair<const Term, Term>& t : dmap)
  {
    ASSERT_TRUE(t.first == f0 || t.first == f1);
    ASSERT_TRUE(t.second.getKind() == Kind::CONST_INTEGER);
  }
}

TEST_F(TestApiBlackSolver, getLearnedLiterals)
{
  d_solver->setOption("produce-learned-literals", "true");
  // cannot ask before a check sat
  ASSERT_THROW(d_solver->getLearnedLiterals(), CVC5ApiException);
  d_solver->checkSat();
  ASSERT_NO_THROW(d_solver->getLearnedLiterals());
  ASSERT_NO_THROW(
      d_solver->getLearnedLiterals(modes::LearnedLitType::PREPROCESS));
}

TEST_F(TestApiBlackSolver, getLearnedLiterals2)
{
  d_solver->setOption("produce-learned-literals", "true");
  Sort intSort = d_tm.getIntegerSort();
  Term x = d_tm.mkConst(intSort, "x");
  Term y = d_tm.mkConst(intSort, "y");
  Term zero = d_tm.mkInteger(0);
  Term ten = d_tm.mkInteger(10);
  Term f0 = d_tm.mkTerm(Kind::GEQ, {x, ten});
  Term f1 = d_tm.mkTerm(
      Kind::OR,
      {d_tm.mkTerm(Kind::GEQ, {zero, x}), d_tm.mkTerm(Kind::GEQ, {y, zero})});
  d_solver->assertFormula(f0);
  d_solver->assertFormula(f1);
  d_solver->checkSat();
  ASSERT_NO_THROW(d_solver->getLearnedLiterals());
}

TEST_F(TestApiBlackSolver, getTimeoutCoreUnsat)
{
  d_solver->setOption("timeout-core-timeout", "100");
  d_solver->setOption("produce-unsat-cores", "true");
  Sort intSort = d_tm.getIntegerSort();
  Term x = d_tm.mkConst(intSort, "x");
  Term tt = d_tm.mkBoolean(true);
  Term hard =
      d_tm.mkTerm(Kind::EQUAL,
                  {d_tm.mkTerm(Kind::MULT, {x, x}),
                   d_tm.mkInteger("501240912901901249014210220059591")});
  d_solver->assertFormula(tt);
  d_solver->assertFormula(hard);
  std::pair<cvc5::Result, std::vector<Term>> res = d_solver->getTimeoutCore();
  ASSERT_TRUE(res.first.isUnknown());
  ASSERT_TRUE(res.second.size() == 1);
  ASSERT_EQ(res.second[0], hard);
}

TEST_F(TestApiBlackSolver, getTimeoutCore)
{
  d_solver->setOption("produce-unsat-cores", "true");
  Term ff = d_tm.mkBoolean(false);
  Term tt = d_tm.mkBoolean(true);
  d_solver->assertFormula(tt);
  d_solver->assertFormula(ff);
  d_solver->assertFormula(tt);
  std::pair<cvc5::Result, std::vector<Term>> res = d_solver->getTimeoutCore();
  ASSERT_TRUE(res.first.isUnsat());
  ASSERT_TRUE(res.second.size() == 1);
  ASSERT_EQ(res.second[0], ff);
}

TEST_F(TestApiBlackSolver, getTimeoutCoreAssuming)
{
  d_solver->setOption("produce-unsat-cores", "true");
  Term ff = d_tm.mkBoolean(false);
  Term tt = d_tm.mkBoolean(true);
  d_solver->assertFormula(tt);
  std::pair<cvc5::Result, std::vector<Term>> res =
      d_solver->getTimeoutCoreAssuming({ff, tt});
  ASSERT_TRUE(res.first.isUnsat());
  ASSERT_TRUE(res.second.size() == 1);
  ASSERT_EQ(res.second[0], ff);
}

TEST_F(TestApiBlackSolver, getTimeoutCoreAssumingEmpty)
{
  d_solver->setOption("produce-unsat-cores", "true");
  ASSERT_THROW(d_solver->getTimeoutCoreAssuming({}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValue1)
{
  d_solver->setOption("produce-models", "false");
  Term t = d_tm.mkTrue();
  d_solver->assertFormula(t);
  d_solver->checkSat();
  ASSERT_THROW(d_solver->getValue(t), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValue2)
{
  d_solver->setOption("produce-models", "true");
  Term t = d_tm.mkFalse();
  d_solver->assertFormula(t);
  d_solver->checkSat();
  ASSERT_THROW(d_solver->getValue(t), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValue3)
{
  d_solver->setOption("produce-models", "true");
  Sort uSort = d_tm.mkUninterpretedSort("u");
  Sort intSort = d_tm.getIntegerSort();
  Sort boolSort = d_tm.getBooleanSort();
  Sort uToIntSort = d_tm.mkFunctionSort({uSort}, intSort);
  Sort intPredSort = d_tm.mkFunctionSort({intSort}, boolSort);
  std::vector<Term> unsat_core;

  Term x = d_tm.mkConst(uSort, "x");
  Term y = d_tm.mkConst(uSort, "y");
  Term z = d_tm.mkConst(uSort, "z");
  Term f = d_tm.mkConst(uToIntSort, "f");
  Term p = d_tm.mkConst(intPredSort, "p");
  Term zero = d_tm.mkInteger(0);
  Term one = d_tm.mkInteger(1);
  Term f_x = d_tm.mkTerm(Kind::APPLY_UF, {f, x});
  Term f_y = d_tm.mkTerm(Kind::APPLY_UF, {f, y});
  Term sum = d_tm.mkTerm(Kind::ADD, {f_x, f_y});
  Term p_0 = d_tm.mkTerm(Kind::APPLY_UF, {p, zero});
  Term p_f_y = d_tm.mkTerm(Kind::APPLY_UF, {p, f_y});

  d_solver->assertFormula(d_tm.mkTerm(Kind::LEQ, {zero, f_x}));
  d_solver->assertFormula(d_tm.mkTerm(Kind::LEQ, {zero, f_y}));
  d_solver->assertFormula(d_tm.mkTerm(Kind::LEQ, {sum, one}));
  d_solver->assertFormula(p_0.notTerm());
  d_solver->assertFormula(p_f_y);
  ASSERT_TRUE(d_solver->checkSat().isSat());
  ASSERT_NO_THROW(d_solver->getValue(x));
  ASSERT_NO_THROW(d_solver->getValue(y));
  ASSERT_NO_THROW(d_solver->getValue(z));
  ASSERT_NO_THROW(d_solver->getValue(sum));
  ASSERT_NO_THROW(d_solver->getValue(p_f_y));

  std::vector<Term> a;
  ASSERT_NO_THROW(a.emplace_back(d_solver->getValue(x)));
  ASSERT_NO_THROW(a.emplace_back(d_solver->getValue(y)));
  ASSERT_NO_THROW(a.emplace_back(d_solver->getValue(z)));
  std::vector<Term> b;
  ASSERT_NO_THROW(b = d_solver->getValue({x, y, z}));
  ASSERT_EQ(a,b);

  Solver slv(d_tm);
  ASSERT_THROW(slv.getValue(x), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getModelDomainElements)
{
  d_solver->setOption("produce-models", "true");
  Sort uSort = d_tm.mkUninterpretedSort("u");
  Sort intSort = d_tm.getIntegerSort();
  Term x = d_tm.mkConst(uSort, "x");
  Term y = d_tm.mkConst(uSort, "y");
  Term z = d_tm.mkConst(uSort, "z");
  Term f = d_tm.mkTerm(Kind::DISTINCT, {x, y, z});
  d_solver->assertFormula(f);
  d_solver->checkSat();
  ASSERT_NO_THROW(d_solver->getModelDomainElements(uSort));
  ASSERT_TRUE(d_solver->getModelDomainElements(uSort).size() >= 3);
  ASSERT_THROW(d_solver->getModelDomainElements(intSort), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getModelDomainElements2)
{
  d_solver->setOption("produce-models", "true");
  d_solver->setOption("finite-model-find", "true");
  Sort uSort = d_tm.mkUninterpretedSort("u");
  Term x = d_tm.mkVar(uSort, "x");
  Term y = d_tm.mkVar(uSort, "y");
  Term eq = d_tm.mkTerm(Kind::EQUAL, {x, y});
  Term bvl = d_tm.mkTerm(Kind::VARIABLE_LIST, {x, y});
  Term f = d_tm.mkTerm(Kind::FORALL, {bvl, eq});
  d_solver->assertFormula(f);
  d_solver->checkSat();
  ASSERT_NO_THROW(d_solver->getModelDomainElements(uSort));
  // a model for the above must interpret u as size 1
  ASSERT_TRUE(d_solver->getModelDomainElements(uSort).size() == 1);
}

TEST_F(TestApiBlackSolver, isModelCoreSymbol)
{
  d_solver->setOption("produce-models", "true");
  d_solver->setOption("model-cores", "simple");
  Sort uSort = d_tm.mkUninterpretedSort("u");
  Term x = d_tm.mkConst(uSort, "x");
  Term y = d_tm.mkConst(uSort, "y");
  Term z = d_tm.mkConst(uSort, "z");
  Term zero = d_tm.mkInteger(0);
  Term f = d_tm.mkTerm(Kind::NOT, {d_tm.mkTerm(Kind::EQUAL, {x, y})});
  d_solver->assertFormula(f);
  d_solver->checkSat();
  ASSERT_TRUE(d_solver->isModelCoreSymbol(x));
  ASSERT_TRUE(d_solver->isModelCoreSymbol(y));
  ASSERT_FALSE(d_solver->isModelCoreSymbol(z));
  ASSERT_THROW(d_solver->isModelCoreSymbol(zero), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getModel)
{
  d_solver->setOption("produce-models", "true");
  Sort uSort = d_tm.mkUninterpretedSort("u");
  Term x = d_tm.mkConst(uSort, "x");
  Term y = d_tm.mkConst(uSort, "y");
  Term z = d_tm.mkConst(uSort, "z");
  Term f = d_tm.mkTerm(Kind::NOT, {d_tm.mkTerm(Kind::EQUAL, {x, y})});
  d_solver->assertFormula(f);
  d_solver->checkSat();
  std::vector<Sort> sorts;
  sorts.push_back(uSort);
  std::vector<Term> terms;
  terms.push_back(x);
  terms.push_back(y);
  ASSERT_NO_THROW(d_solver->getModel(sorts, terms));
  Term null;
  terms.push_back(null);
  ASSERT_THROW(d_solver->getModel(sorts, terms), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getModel2)
{
  d_solver->setOption("produce-models", "true");
  std::vector<Sort> sorts;
  std::vector<Term> terms;
  ASSERT_THROW(d_solver->getModel(sorts, terms), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getModel3)
{
  d_solver->setOption("produce-models", "true");
  std::vector<Sort> sorts;
  std::vector<Term> terms;
  d_solver->checkSat();
  ASSERT_NO_THROW(d_solver->getModel(sorts, terms));
  Sort integer = d_tm.getIntegerSort();
  sorts.push_back(integer);
  ASSERT_THROW(d_solver->getModel(sorts, terms), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getQuantifierElimination)
{
  Term x = d_tm.mkVar(d_tm.getBooleanSort(), "x");
  Term forall =
      d_tm.mkTerm(Kind::FORALL,
                  {d_tm.mkTerm(Kind::VARIABLE_LIST, {x}),
                   d_tm.mkTerm(Kind::OR, {x, d_tm.mkTerm(Kind::NOT, {x})})});
  ASSERT_THROW(d_solver->getQuantifierElimination(Term()), CVC5ApiException);
  ASSERT_THROW(d_solver->getQuantifierElimination(d_tm.mkBoolean(false)),
               CVC5ApiException);
  ASSERT_NO_THROW(d_solver->getQuantifierElimination(forall));
}

TEST_F(TestApiBlackSolver, getQuantifierEliminationDisjunct)
{
  Term x = d_tm.mkVar(d_tm.getBooleanSort(), "x");
  Term forall =
      d_tm.mkTerm(Kind::FORALL,
                  {d_tm.mkTerm(Kind::VARIABLE_LIST, {x}),
                   d_tm.mkTerm(Kind::OR, {x, d_tm.mkTerm(Kind::NOT, {x})})});
  ASSERT_THROW(d_solver->getQuantifierEliminationDisjunct(Term()),
               CVC5ApiException);
  ASSERT_THROW(
      d_solver->getQuantifierEliminationDisjunct(d_tm.mkBoolean(false)),
      CVC5ApiException);
  ASSERT_NO_THROW(d_solver->getQuantifierEliminationDisjunct(forall));
}

TEST_F(TestApiBlackSolver, declareSepHeap)
{
  d_solver->setLogic("ALL");
  d_solver->setOption("incremental", "false");
  Sort integer = d_tm.getIntegerSort();
  ASSERT_NO_THROW(d_solver->declareSepHeap(integer, integer));
  // cannot declare separation logic heap more than once
  ASSERT_THROW(d_solver->declareSepHeap(integer, integer), CVC5ApiException);
}

namespace {
/**
 * Helper function for testGetSeparation{Heap,Nil}TermX. Asserts and checks
 * some simple separation logic constraints.
 */
void checkSimpleSeparationConstraints(Solver* solver)
{
  TermManager& tm = solver->getTermManager();
  Sort integer = tm.getIntegerSort();
  // declare the separation heap
  solver->declareSepHeap(integer, integer);
  Term x = tm.mkConst(integer, "x");
  Term p = tm.mkConst(integer, "p");
  Term heap = tm.mkTerm(cvc5::Kind::SEP_PTO, {p, x});
  solver->assertFormula(heap);
  Term nil = tm.mkSepNil(integer);
  solver->assertFormula(nil.eqTerm(tm.mkInteger(5)));
  solver->checkSat();
}
}  // namespace

TEST_F(TestApiBlackSolver, getValueSepHeap1)
{
  d_solver->setLogic("QF_BV");
  d_solver->setOption("incremental", "false");
  d_solver->setOption("produce-models", "true");
  Term t = d_tm.mkTrue();
  d_solver->assertFormula(t);
  ASSERT_THROW(d_solver->getValueSepHeap(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValueSepHeap2)
{
  d_solver->setLogic("ALL");
  d_solver->setOption("incremental", "false");
  d_solver->setOption("produce-models", "false");
  checkSimpleSeparationConstraints(d_solver.get());
  ASSERT_THROW(d_solver->getValueSepHeap(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValueSepHeap3)
{
  d_solver->setLogic("ALL");
  d_solver->setOption("incremental", "false");
  d_solver->setOption("produce-models", "true");
  Term t = d_tm.mkFalse();
  d_solver->assertFormula(t);
  d_solver->checkSat();
  ASSERT_THROW(d_solver->getValueSepHeap(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValueSepHeap4)
{
  d_solver->setLogic("ALL");
  d_solver->setOption("incremental", "false");
  d_solver->setOption("produce-models", "true");
  Term t = d_tm.mkTrue();
  d_solver->assertFormula(t);
  d_solver->checkSat();
  ASSERT_THROW(d_solver->getValueSepHeap(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValueSepHeap5)
{
  d_solver->setLogic("ALL");
  d_solver->setOption("incremental", "false");
  d_solver->setOption("produce-models", "true");
  checkSimpleSeparationConstraints(d_solver.get());
  ASSERT_NO_THROW(d_solver->getValueSepHeap());
}

TEST_F(TestApiBlackSolver, getValueSepNil1)
{
  d_solver->setLogic("QF_BV");
  d_solver->setOption("incremental", "false");
  d_solver->setOption("produce-models", "true");
  Term t = d_tm.mkTrue();
  d_solver->assertFormula(t);
  ASSERT_THROW(d_solver->getValueSepNil(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValueSepNil2)
{
  d_solver->setLogic("ALL");
  d_solver->setOption("incremental", "false");
  d_solver->setOption("produce-models", "false");
  checkSimpleSeparationConstraints(d_solver.get());
  ASSERT_THROW(d_solver->getValueSepNil(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValueSepNil3)
{
  d_solver->setLogic("ALL");
  d_solver->setOption("incremental", "false");
  d_solver->setOption("produce-models", "true");
  Term t = d_tm.mkFalse();
  d_solver->assertFormula(t);
  d_solver->checkSat();
  ASSERT_THROW(d_solver->getValueSepNil(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValueSepNil4)
{
  d_solver->setLogic("ALL");
  d_solver->setOption("incremental", "false");
  d_solver->setOption("produce-models", "true");
  Term t = d_tm.mkTrue();
  d_solver->assertFormula(t);
  d_solver->checkSat();
  ASSERT_THROW(d_solver->getValueSepNil(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValueSepNil5)
{
  d_solver->setLogic("ALL");
  d_solver->setOption("incremental", "false");
  d_solver->setOption("produce-models", "true");
  checkSimpleSeparationConstraints(d_solver.get());
  ASSERT_NO_THROW(d_solver->getValueSepNil());
}

TEST_F(TestApiBlackSolver, push1)
{
  d_solver->setOption("incremental", "true");
  ASSERT_NO_THROW(d_solver->push(1));
  ASSERT_THROW(d_solver->setOption("incremental", "false"), CVC5ApiException);
  ASSERT_THROW(d_solver->setOption("incremental", "true"), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, push2)
{
  d_solver->setOption("incremental", "false");
  ASSERT_THROW(d_solver->push(1), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, pop1)
{
  d_solver->setOption("incremental", "false");
  ASSERT_THROW(d_solver->pop(1), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, pop2)
{
  d_solver->setOption("incremental", "true");
  ASSERT_THROW(d_solver->pop(1), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, pop3)
{
  d_solver->setOption("incremental", "true");
  ASSERT_NO_THROW(d_solver->push(1));
  ASSERT_NO_THROW(d_solver->pop(1));
  ASSERT_THROW(d_solver->pop(1), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, blockModel1)
{
  Term x = d_tm.mkConst(d_tm.getBooleanSort(), "x");
  d_solver->assertFormula(x.eqTerm(x));
  d_solver->checkSat();
  ASSERT_THROW(d_solver->blockModel(modes::BlockModelsMode::LITERALS),
               CVC5ApiException);
}

TEST_F(TestApiBlackSolver, blockModel2)
{
  d_solver->setOption("produce-models", "true");
  Term x = d_tm.mkConst(d_tm.getBooleanSort(), "x");
  d_solver->assertFormula(x.eqTerm(x));
  ASSERT_THROW(d_solver->blockModel(modes::BlockModelsMode::LITERALS),
               CVC5ApiException);
}

TEST_F(TestApiBlackSolver, blockModel3)
{
  d_solver->setOption("produce-models", "true");
  Term x = d_tm.mkConst(d_tm.getBooleanSort(), "x");
  d_solver->assertFormula(x.eqTerm(x));
  d_solver->checkSat();
  ASSERT_NO_THROW(d_solver->blockModel(modes::BlockModelsMode::LITERALS));
}

TEST_F(TestApiBlackSolver, blockModelValues1)
{
  d_solver->setOption("produce-models", "true");
  Term x = d_tm.mkConst(d_tm.getBooleanSort(), "x");
  d_solver->assertFormula(x.eqTerm(x));
  d_solver->checkSat();
  ASSERT_THROW(d_solver->blockModelValues({}), CVC5ApiException);
  ASSERT_THROW(d_solver->blockModelValues({Term()}), CVC5ApiException);
  ASSERT_NO_THROW(d_solver->blockModelValues({d_tm.mkBoolean(false)}));
}

TEST_F(TestApiBlackSolver, blockModelValues2)
{
  d_solver->setOption("produce-models", "true");
  Term x = d_tm.mkConst(d_tm.getBooleanSort(), "x");
  d_solver->assertFormula(x.eqTerm(x));
  d_solver->checkSat();
  ASSERT_NO_THROW(d_solver->blockModelValues({x}));
}

TEST_F(TestApiBlackSolver, blockModelValues3)
{
  Term x = d_tm.mkConst(d_tm.getBooleanSort(), "x");
  d_solver->assertFormula(x.eqTerm(x));
  d_solver->checkSat();
  ASSERT_THROW(d_solver->blockModelValues({x}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, blockModelValues4)
{
  d_solver->setOption("produce-models", "true");
  Term x = d_tm.mkConst(d_tm.getBooleanSort(), "x");
  d_solver->assertFormula(x.eqTerm(x));
  ASSERT_THROW(d_solver->blockModelValues({x}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, blockModelValues5)
{
  d_solver->setOption("produce-models", "true");
  Term x = d_tm.mkConst(d_tm.getBooleanSort(), "x");
  d_solver->assertFormula(x.eqTerm(x));
  d_solver->checkSat();
  ASSERT_NO_THROW(d_solver->blockModelValues({x}));
}

TEST_F(TestApiBlackSolver, getInstantiations)
{
  Sort iSort = d_tm.getIntegerSort();
  Sort boolSort = d_tm.getBooleanSort();
  Term p = d_solver->declareFun("p", {iSort}, boolSort);
  Term x = d_tm.mkVar(iSort, "x");
  Term bvl = d_tm.mkTerm(Kind::VARIABLE_LIST, {x});
  Term app = d_tm.mkTerm(Kind::APPLY_UF, {p, x});
  Term q = d_tm.mkTerm(Kind::FORALL, {bvl, app});
  d_solver->assertFormula(q);
  Term five = d_tm.mkInteger(5);
  Term app2 = d_tm.mkTerm(Kind::NOT, {d_tm.mkTerm(Kind::APPLY_UF, {p, five})});
  d_solver->assertFormula(app2);
  ASSERT_THROW(d_solver->getInstantiations(), CVC5ApiException);
  d_solver->checkSat();
  ASSERT_NO_THROW(d_solver->getInstantiations());
}

TEST_F(TestApiBlackSolver, setInfo)
{
  ASSERT_THROW(d_solver->setInfo("cvc5-lagic", "QF_BV"), CVC5ApiException);
  ASSERT_THROW(d_solver->setInfo("cvc2-logic", "QF_BV"), CVC5ApiException);
  ASSERT_THROW(d_solver->setInfo("cvc5-logic", "asdf"), CVC5ApiException);

  ASSERT_NO_THROW(d_solver->setInfo("source", "asdf"));
  ASSERT_NO_THROW(d_solver->setInfo("category", "asdf"));
  ASSERT_NO_THROW(d_solver->setInfo("difficulty", "asdf"));
  ASSERT_NO_THROW(d_solver->setInfo("filename", "asdf"));
  ASSERT_NO_THROW(d_solver->setInfo("license", "asdf"));
  ASSERT_NO_THROW(d_solver->setInfo("name", "asdf"));
  ASSERT_NO_THROW(d_solver->setInfo("notes", "asdf"));

  ASSERT_NO_THROW(d_solver->setInfo("smt-lib-version", "2"));
  ASSERT_NO_THROW(d_solver->setInfo("smt-lib-version", "2.0"));
  ASSERT_NO_THROW(d_solver->setInfo("smt-lib-version", "2.5"));
  ASSERT_NO_THROW(d_solver->setInfo("smt-lib-version", "2.6"));
  ASSERT_THROW(d_solver->setInfo("smt-lib-version", ".0"), CVC5ApiException);

  ASSERT_NO_THROW(d_solver->setInfo("status", "sat"));
  ASSERT_NO_THROW(d_solver->setInfo("status", "unsat"));
  ASSERT_NO_THROW(d_solver->setInfo("status", "unknown"));
  ASSERT_THROW(d_solver->setInfo("status", "asdf"), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, simplify)
{
  ASSERT_THROW(d_solver->simplify(Term()), CVC5ApiException);

  Sort bvSort = d_tm.mkBitVectorSort(32);
  Sort uSort = d_tm.mkUninterpretedSort("u");
  Sort funSort1 = d_tm.mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_tm.mkFunctionSort({uSort}, d_tm.getIntegerSort());
  DatatypeDecl consListSpec = d_tm.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_tm.getIntegerSort());
  cons.addSelectorSelf("tail");
  consListSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
  consListSpec.addConstructor(nil);
  Sort consListSort = d_tm.mkDatatypeSort(consListSpec);

  Term x = d_tm.mkConst(bvSort, "x");
  ASSERT_NO_THROW(d_solver->simplify(x));
  Term a = d_tm.mkConst(bvSort, "a");
  ASSERT_NO_THROW(d_solver->simplify(a));
  Term b = d_tm.mkConst(bvSort, "b");
  ASSERT_NO_THROW(d_solver->simplify(b));
  Term x_eq_x = d_tm.mkTerm(Kind::EQUAL, {x, x});
  ASSERT_NO_THROW(d_solver->simplify(x_eq_x));
  ASSERT_NE(d_tm.mkTrue(), x_eq_x);
  ASSERT_EQ(d_tm.mkTrue(), d_solver->simplify(x_eq_x));
  Term x_eq_b = d_tm.mkTerm(Kind::EQUAL, {x, b});
  ASSERT_NO_THROW(d_solver->simplify(x_eq_b));
  ASSERT_NE(d_tm.mkTrue(), x_eq_b);
  ASSERT_NE(d_tm.mkTrue(), d_solver->simplify(x_eq_b));
  Solver slv(d_tm);
  ASSERT_NO_THROW(slv.simplify(x));

  Term i1 = d_tm.mkConst(d_tm.getIntegerSort(), "i1");
  ASSERT_NO_THROW(d_solver->simplify(i1));
  Term i2 = d_tm.mkTerm(Kind::MULT, {i1, d_tm.mkInteger("23")});
  ASSERT_NO_THROW(d_solver->simplify(i2));
  ASSERT_NE(i1, i2);
  ASSERT_NE(i1, d_solver->simplify(i2));
  Term i3 = d_tm.mkTerm(Kind::ADD, {i1, d_tm.mkInteger(0)});
  ASSERT_NO_THROW(d_solver->simplify(i3));
  ASSERT_NE(i1, i3);
  ASSERT_EQ(i1, d_solver->simplify(i3));

  Datatype consList = consListSort.getDatatype();
  Term dt1 =
      d_tm.mkTerm(Kind::APPLY_CONSTRUCTOR,
                  {consList.getConstructor("cons").getTerm(),
                   d_tm.mkInteger(0),
                   d_tm.mkTerm(Kind::APPLY_CONSTRUCTOR,
                               {consList.getConstructor("nil").getTerm()})});
  ASSERT_NO_THROW(d_solver->simplify(dt1));
  Term dt2 = d_tm.mkTerm(Kind::APPLY_SELECTOR,
                         {consList["cons"].getSelector("head").getTerm(), dt1});
  ASSERT_NO_THROW(d_solver->simplify(dt2));

  Term b1 = d_tm.mkVar(bvSort, "b1");
  ASSERT_NO_THROW(d_solver->simplify(b1));
  Term b2 = d_tm.mkVar(bvSort, "b1");
  ASSERT_NO_THROW(d_solver->simplify(b2));
  Term b3 = d_tm.mkVar(uSort, "b3");
  ASSERT_NO_THROW(d_solver->simplify(b3));
  Term v1 = d_tm.mkConst(bvSort, "v1");
  ASSERT_NO_THROW(d_solver->simplify(v1));
  Term v2 = d_tm.mkConst(d_tm.getIntegerSort(), "v2");
  ASSERT_NO_THROW(d_solver->simplify(v2));
  Term f1 = d_tm.mkConst(funSort1, "f1");
  ASSERT_NO_THROW(d_solver->simplify(f1));
  Term f2 = d_tm.mkConst(funSort2, "f2");
  ASSERT_NO_THROW(d_solver->simplify(f2));
  d_solver->defineFunsRec({f1, f2}, {{b1, b2}, {b3}}, {v1, v2});
  ASSERT_NO_THROW(d_solver->simplify(f1));
  ASSERT_NO_THROW(d_solver->simplify(f2));
}

TEST_F(TestApiBlackSolver, assertFormula)
{
  ASSERT_NO_THROW(d_solver->assertFormula(d_tm.mkTrue()));
  ASSERT_THROW(d_solver->assertFormula(Term()), CVC5ApiException);
  Solver slv(d_tm);
  ASSERT_NO_THROW(slv.assertFormula(d_tm.mkTrue()));
}

TEST_F(TestApiBlackSolver, checkSat)
{
  d_solver->setOption("incremental", "false");
  ASSERT_NO_THROW(d_solver->checkSat());
  ASSERT_THROW(d_solver->checkSat(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, checkSatAssuming)
{
  d_solver->setOption("incremental", "false");
  ASSERT_NO_THROW(d_solver->checkSatAssuming(d_tm.mkTrue()));
  ASSERT_THROW(d_solver->checkSatAssuming(d_tm.mkTrue()), CVC5ApiException);
  Solver slv(d_tm);
  ASSERT_NO_THROW(slv.checkSatAssuming(d_tm.mkTrue()));
}

TEST_F(TestApiBlackSolver, checkSatAssuming1)
{
  Sort boolSort = d_tm.getBooleanSort();
  Term x = d_tm.mkConst(boolSort, "x");
  Term y = d_tm.mkConst(boolSort, "y");
  Term z = d_tm.mkTerm(Kind::AND, {x, y});
  d_solver->setOption("incremental", "true");
  ASSERT_NO_THROW(d_solver->checkSatAssuming(d_tm.mkTrue()));
  ASSERT_THROW(d_solver->checkSatAssuming(Term()), CVC5ApiException);
  ASSERT_NO_THROW(d_solver->checkSatAssuming(d_tm.mkTrue()));
  ASSERT_NO_THROW(d_solver->checkSatAssuming(z));
  Solver slv(d_tm);
  ASSERT_NO_THROW(slv.checkSatAssuming(d_tm.mkTrue()));
}

TEST_F(TestApiBlackSolver, checkSatAssuming2)
{
  d_solver->setOption("incremental", "true");

  Sort uSort = d_tm.mkUninterpretedSort("u");
  Sort intSort = d_tm.getIntegerSort();
  Sort boolSort = d_tm.getBooleanSort();
  Sort uToIntSort = d_tm.mkFunctionSort({uSort}, intSort);
  Sort intPredSort = d_tm.mkFunctionSort({intSort}, boolSort);

  Term n = Term();
  // Constants
  Term x = d_tm.mkConst(uSort, "x");
  Term y = d_tm.mkConst(uSort, "y");
  // Functions
  Term f = d_tm.mkConst(uToIntSort, "f");
  Term p = d_tm.mkConst(intPredSort, "p");
  // Values
  Term zero = d_tm.mkInteger(0);
  Term one = d_tm.mkInteger(1);
  // Terms
  Term f_x = d_tm.mkTerm(Kind::APPLY_UF, {f, x});
  Term f_y = d_tm.mkTerm(Kind::APPLY_UF, {f, y});
  Term sum = d_tm.mkTerm(Kind::ADD, {f_x, f_y});
  Term p_0 = d_tm.mkTerm(Kind::APPLY_UF, {p, zero});
  Term p_f_y = d_tm.mkTerm(Kind::APPLY_UF, {p, f_y});
  // Assertions
  Term assertions =
      d_tm.mkTerm(Kind::AND,
                  {
                      d_tm.mkTerm(Kind::LEQ, {zero, f_x}),  // 0 <= f(x)
                      d_tm.mkTerm(Kind::LEQ, {zero, f_y}),  // 0 <= f(y)
                      d_tm.mkTerm(Kind::LEQ, {sum, one}),   // f(x) + f(y) <= 1
                      p_0.notTerm(),                        // not p(0)
                      p_f_y                                 // p(f(y))
                  });

  ASSERT_NO_THROW(d_solver->checkSatAssuming(d_tm.mkTrue()));
  d_solver->assertFormula(assertions);
  ASSERT_NO_THROW(
      d_solver->checkSatAssuming(d_tm.mkTerm(Kind::DISTINCT, {x, y})));
  ASSERT_NO_THROW(d_solver->checkSatAssuming(
      {d_tm.mkFalse(), d_tm.mkTerm(Kind::DISTINCT, {x, y})}));
  ASSERT_THROW(d_solver->checkSatAssuming(n), CVC5ApiException);
  ASSERT_THROW(
      d_solver->checkSatAssuming({n, d_tm.mkTerm(Kind::DISTINCT, {x, y})}),
      CVC5ApiException);
  Solver slv(d_tm);
  ASSERT_NO_THROW(slv.checkSatAssuming(d_tm.mkTrue()));
}

TEST_F(TestApiBlackSolver, setLogic)
{
  ASSERT_NO_THROW(d_solver->setLogic("AUFLIRA"));
  ASSERT_THROW(d_solver->setLogic("AF_BV"), CVC5ApiException);
  d_solver->assertFormula(d_tm.mkTrue());
  ASSERT_THROW(d_solver->setLogic("AUFLIRA"), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, isLogicSet)
{
  ASSERT_FALSE(d_solver->isLogicSet());
  ASSERT_NO_THROW(d_solver->setLogic("QF_BV"));
  ASSERT_TRUE(d_solver->isLogicSet());
}

TEST_F(TestApiBlackSolver, getLogic)
{
  ASSERT_THROW(d_solver->getLogic(), CVC5ApiException);
  ASSERT_NO_THROW(d_solver->setLogic("QF_BV"));
  ASSERT_EQ(d_solver->getLogic(), "QF_BV");
}

TEST_F(TestApiBlackSolver, setOption)
{
  ASSERT_NO_THROW(d_solver->setOption("bv-sat-solver", "minisat"));
  ASSERT_THROW(d_solver->setOption("bv-sat-solver", "1"), CVC5ApiException);
  d_solver->assertFormula(d_tm.mkTrue());
  ASSERT_THROW(d_solver->setOption("bv-sat-solver", "minisat"),
               CVC5ApiException);
}

TEST_F(TestApiBlackSolver, resetAssertions)
{
  d_solver->setOption("incremental", "true");

  Sort bvSort = d_tm.mkBitVectorSort(4);
  Term one = d_tm.mkBitVector(4, 1);
  Term x = d_tm.mkConst(bvSort, "x");
  Term ule = d_tm.mkTerm(Kind::BITVECTOR_ULE, {x, one});
  Term srem = d_tm.mkTerm(Kind::BITVECTOR_SREM, {one, x});
  d_solver->push(4);
  Term slt = d_tm.mkTerm(Kind::BITVECTOR_SLT, {srem, one});
  d_solver->resetAssertions();
  d_solver->checkSatAssuming({slt, ule});
}

TEST_F(TestApiBlackSolver, declareSygusVar)
{
  d_solver->setOption("sygus", "true");
  Sort boolSort = d_tm.getBooleanSort();
  Sort intSort = d_tm.getIntegerSort();
  Sort funSort = d_tm.mkFunctionSort({intSort}, boolSort);

  ASSERT_NO_THROW(d_solver->declareSygusVar("", boolSort));
  ASSERT_NO_THROW(d_solver->declareSygusVar("", funSort));
  ASSERT_NO_THROW(d_solver->declareSygusVar(std::string("b"), boolSort));
  ASSERT_THROW(d_solver->declareSygusVar("", Sort()), CVC5ApiException);
  ASSERT_THROW(d_solver->declareSygusVar("a", Sort()), CVC5ApiException);
  Solver slv(d_tm);
  ASSERT_THROW(slv.declareSygusVar("", boolSort), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkGrammar)
{
  Term nullTerm;
  Term boolTerm = d_tm.mkBoolean(true);
  Term boolVar = d_tm.mkVar(d_tm.getBooleanSort());
  Term intVar = d_tm.mkVar(d_tm.getIntegerSort());

  ASSERT_NO_THROW(d_solver->mkGrammar({}, {intVar}));
  ASSERT_NO_THROW(d_solver->mkGrammar({boolVar}, {intVar}));
  ASSERT_THROW(d_solver->mkGrammar({}, {}), CVC5ApiException);
  ASSERT_THROW(d_solver->mkGrammar({}, {nullTerm}), CVC5ApiException);
  ASSERT_THROW(d_solver->mkGrammar({}, {boolTerm}), CVC5ApiException);
  ASSERT_THROW(d_solver->mkGrammar({boolTerm}, {intVar}), CVC5ApiException);
  Solver slv(d_tm);
  Term boolVar2 = d_tm.mkVar(d_tm.getBooleanSort());
  Term intVar2 = d_tm.mkVar(d_tm.getIntegerSort());
  ASSERT_NO_THROW(slv.mkGrammar({boolVar2}, {intVar2}));
  ASSERT_NO_THROW(slv.mkGrammar({boolVar}, {intVar2}));
  ASSERT_NO_THROW(slv.mkGrammar({boolVar2}, {intVar}));
}

TEST_F(TestApiBlackSolver, synthFun)
{
  d_solver->setOption("sygus", "true");
  Sort null;
  Sort boolean = d_tm.getBooleanSort();
  Sort integer = d_tm.getIntegerSort();

  Term nullTerm;
  Term x = d_tm.mkVar(boolean);

  Term start1 = d_tm.mkVar(boolean);
  Term start2 = d_tm.mkVar(integer);

  Grammar g1 = d_solver->mkGrammar({x}, {start1});
  g1.addRule(start1, d_tm.mkBoolean(false));

  Grammar g2 = d_solver->mkGrammar({x}, {start2});
  g2.addRule(start2, d_tm.mkInteger(0));

  ASSERT_NO_THROW(d_solver->synthFun("", {}, boolean));
  ASSERT_NO_THROW(d_solver->synthFun("f1", {x}, boolean));
  ASSERT_NO_THROW(d_solver->synthFun("f2", {x}, boolean, g1));

  ASSERT_THROW(d_solver->synthFun("f3", {nullTerm}, boolean), CVC5ApiException);
  ASSERT_THROW(d_solver->synthFun("f4", {}, null), CVC5ApiException);
  ASSERT_THROW(d_solver->synthFun("f6", {x}, boolean, g2), CVC5ApiException);
  Solver slv(d_tm);
  slv.setOption("sygus", "true");
  Term x2 = d_tm.mkVar(d_tm.getBooleanSort());
  ASSERT_NO_THROW(slv.synthFun("f1", {x2}, d_tm.getBooleanSort()));
  ASSERT_NO_THROW(slv.synthFun("", {}, d_tm.getBooleanSort()));
  ASSERT_NO_THROW(slv.synthFun("f1", {x}, d_tm.getBooleanSort()));
}

TEST_F(TestApiBlackSolver, addSygusConstraint)
{
  d_solver->setOption("sygus", "true");
  Term nullTerm;
  Term boolTerm = d_tm.mkBoolean(true);
  Term intTerm = d_tm.mkInteger(1);

  ASSERT_NO_THROW(d_solver->addSygusConstraint(boolTerm));
  ASSERT_THROW(d_solver->addSygusConstraint(nullTerm), CVC5ApiException);
  ASSERT_THROW(d_solver->addSygusConstraint(intTerm), CVC5ApiException);

  Solver slv(d_tm);
  slv.setOption("sygus", "true");
  ASSERT_NO_THROW(slv.addSygusConstraint(boolTerm));
}

TEST_F(TestApiBlackSolver, getSygusConstraints)
{
  d_solver->setOption("sygus", "true");
  Term trueTerm = d_tm.mkBoolean(true);
  Term falseTerm = d_tm.mkBoolean(false);
  d_solver->addSygusConstraint(trueTerm);
  d_solver->addSygusConstraint(falseTerm);
  std::vector<Term> constraints{trueTerm, falseTerm};
  ASSERT_EQ(d_solver->getSygusConstraints(), constraints);
}

TEST_F(TestApiBlackSolver, addSygusAssume)
{
  d_solver->setOption("sygus", "true");
  Term nullTerm;
  Term boolTerm = d_tm.mkBoolean(false);
  Term intTerm = d_tm.mkInteger(1);

  ASSERT_NO_THROW(d_solver->addSygusAssume(boolTerm));
  ASSERT_THROW(d_solver->addSygusAssume(nullTerm), CVC5ApiException);
  ASSERT_THROW(d_solver->addSygusAssume(intTerm), CVC5ApiException);

  Solver slv(d_tm);
  slv.setOption("sygus", "true");
  ASSERT_NO_THROW(slv.addSygusAssume(boolTerm));
}

TEST_F(TestApiBlackSolver, getSygusAssumptions)
{
  d_solver->setOption("sygus", "true");
  Term trueTerm = d_tm.mkBoolean(true);
  Term falseTerm = d_tm.mkBoolean(false);
  d_solver->addSygusAssume(trueTerm);
  d_solver->addSygusAssume(falseTerm);
  std::vector<Term> assumptions{trueTerm, falseTerm};
  ASSERT_EQ(d_solver->getSygusAssumptions(), assumptions);
}

TEST_F(TestApiBlackSolver, addSygusInvConstraint)
{
  d_solver->setOption("sygus", "true");
  Sort boolean = d_tm.getBooleanSort();
  Sort real = d_tm.getRealSort();

  Term nullTerm;
  Term intTerm = d_tm.mkInteger(1);

  Term inv = d_solver->declareFun("inv", {real}, boolean);
  Term pre = d_solver->declareFun("pre", {real}, boolean);
  Term trans = d_solver->declareFun("trans", {real, real}, boolean);
  Term post = d_solver->declareFun("post", {real}, boolean);

  Term inv1 = d_solver->declareFun("inv1", {real}, real);

  Term trans1 = d_solver->declareFun("trans1", {boolean, real}, boolean);
  Term trans2 = d_solver->declareFun("trans2", {real, boolean}, boolean);
  Term trans3 = d_solver->declareFun("trans3", {real, real}, real);

  ASSERT_NO_THROW(d_solver->addSygusInvConstraint(inv, pre, trans, post));

  ASSERT_THROW(d_solver->addSygusInvConstraint(nullTerm, pre, trans, post),
               CVC5ApiException);
  ASSERT_THROW(d_solver->addSygusInvConstraint(inv, nullTerm, trans, post),
               CVC5ApiException);
  ASSERT_THROW(d_solver->addSygusInvConstraint(inv, pre, nullTerm, post),
               CVC5ApiException);
  ASSERT_THROW(d_solver->addSygusInvConstraint(inv, pre, trans, nullTerm),
               CVC5ApiException);

  ASSERT_THROW(d_solver->addSygusInvConstraint(intTerm, pre, trans, post),
               CVC5ApiException);

  ASSERT_THROW(d_solver->addSygusInvConstraint(inv1, pre, trans, post),
               CVC5ApiException);

  ASSERT_THROW(d_solver->addSygusInvConstraint(inv, trans, trans, post),
               CVC5ApiException);

  ASSERT_THROW(d_solver->addSygusInvConstraint(inv, pre, intTerm, post),
               CVC5ApiException);
  ASSERT_THROW(d_solver->addSygusInvConstraint(inv, pre, pre, post),
               CVC5ApiException);
  ASSERT_THROW(d_solver->addSygusInvConstraint(inv, pre, trans1, post),
               CVC5ApiException);
  ASSERT_THROW(d_solver->addSygusInvConstraint(inv, pre, trans2, post),
               CVC5ApiException);
  ASSERT_THROW(d_solver->addSygusInvConstraint(inv, pre, trans3, post),
               CVC5ApiException);

  ASSERT_THROW(d_solver->addSygusInvConstraint(inv, pre, trans, trans),
               CVC5ApiException);
  Solver slv(d_tm);
  slv.setOption("sygus", "true");
  Sort boolean2 = d_tm.getBooleanSort();
  Sort real2 = d_tm.getRealSort();
  Term inv22 = slv.declareFun("inv", {real2}, boolean2);
  Term pre22 = slv.declareFun("pre", {real2}, boolean2);
  Term trans22 = slv.declareFun("trans", {real2, real2}, boolean2);
  Term post22 = slv.declareFun("post", {real2}, boolean2);
  ASSERT_NO_THROW(slv.addSygusInvConstraint(inv22, pre22, trans22, post22));
  ASSERT_NO_THROW(slv.addSygusInvConstraint(inv, pre22, trans22, post22));
  ASSERT_NO_THROW(slv.addSygusInvConstraint(inv22, pre, trans22, post22));
  ASSERT_NO_THROW(slv.addSygusInvConstraint(inv22, pre22, trans, post22));
  ASSERT_NO_THROW(slv.addSygusInvConstraint(inv22, pre22, trans22, post));
}

TEST_F(TestApiBlackSolver, checkSynth)
{
  // requires option to be set
  ASSERT_THROW(d_solver->checkSynth(), CVC5ApiException);
  d_solver->setOption("sygus", "true");
  ASSERT_NO_THROW(d_solver->checkSynth());
}

TEST_F(TestApiBlackSolver, getSynthSolution)
{
  d_solver->setOption("sygus", "true");
  d_solver->setOption("incremental", "false");

  Term nullTerm;
  Term x = d_tm.mkBoolean(false);
  Term f = d_solver->synthFun("f", {}, d_tm.getBooleanSort());

  ASSERT_THROW(d_solver->getSynthSolution(f), CVC5ApiException);

  cvc5::SynthResult sr = d_solver->checkSynth();
  ASSERT_EQ(sr.hasSolution(), true);

  ASSERT_NO_THROW(d_solver->getSynthSolution(f));
  ASSERT_NO_THROW(d_solver->getSynthSolution(f));

  ASSERT_THROW(d_solver->getSynthSolution(nullTerm), CVC5ApiException);
  ASSERT_THROW(d_solver->getSynthSolution(x), CVC5ApiException);

  Solver slv(d_tm);
  ASSERT_THROW(slv.getSynthSolution(f), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getSynthSolutions)
{
  d_solver->setOption("sygus", "true");
  d_solver->setOption("incremental", "false");

  Term nullTerm;
  Term x = d_tm.mkBoolean(false);
  Term f = d_solver->synthFun("f", {}, d_tm.getBooleanSort());

  ASSERT_THROW(d_solver->getSynthSolutions({}), CVC5ApiException);
  ASSERT_THROW(d_solver->getSynthSolutions({f}), CVC5ApiException);

  d_solver->checkSynth();

  ASSERT_NO_THROW(d_solver->getSynthSolutions({f}));
  ASSERT_NO_THROW(d_solver->getSynthSolutions({f, f}));

  ASSERT_THROW(d_solver->getSynthSolutions({}), CVC5ApiException);
  ASSERT_THROW(d_solver->getSynthSolutions({nullTerm}), CVC5ApiException);
  ASSERT_THROW(d_solver->getSynthSolutions({x}), CVC5ApiException);

  Solver slv(d_tm);
  ASSERT_THROW(slv.getSynthSolutions({x}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, checkSynthNext)
{
  d_solver->setOption("sygus", "true");
  d_solver->setOption("incremental", "true");
  Term f = d_solver->synthFun("f", {}, d_tm.getBooleanSort());

  cvc5::SynthResult sr = d_solver->checkSynth();
  ASSERT_EQ(sr.hasSolution(), true);
  ASSERT_NO_THROW(d_solver->getSynthSolutions({f}));
  sr = d_solver->checkSynthNext();
  ASSERT_EQ(sr.hasSolution(), true);
  ASSERT_NO_THROW(d_solver->getSynthSolutions({f}));
}

TEST_F(TestApiBlackSolver, checkSynthNext2)
{
  d_solver->setOption("sygus", "true");
  d_solver->setOption("incremental", "false");
  Term f = d_solver->synthFun("f", {}, d_tm.getBooleanSort());

  d_solver->checkSynth();
  ASSERT_THROW(d_solver->checkSynthNext(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, checkSynthNext3)
{
  d_solver->setOption("sygus", "true");
  d_solver->setOption("incremental", "true");
  Term f = d_solver->synthFun("f", {}, d_tm.getBooleanSort());

  ASSERT_THROW(d_solver->checkSynthNext(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, findSynth)
{
  d_solver->setOption("sygus", "true");
  Sort boolean = d_tm.getBooleanSort();
  Term start = d_tm.mkVar(boolean);
  Grammar g = d_solver->mkGrammar({}, {start});
  Term truen = d_tm.mkBoolean(true);
  Term falsen = d_tm.mkBoolean(false);
  g.addRule(start, truen);
  g.addRule(start, falsen);
  Term f = d_solver->synthFun("f", {}, d_tm.getBooleanSort(), g);

  // should enumerate based on the grammar of the function to synthesize above
  cvc5::Term t = d_solver->findSynth(modes::FindSynthTarget::ENUM);
  ASSERT_TRUE(!t.isNull() && t.getSort().isBoolean());
}

TEST_F(TestApiBlackSolver, findSynth2)
{
  d_solver->setOption("sygus", "true");
  d_solver->setOption("incremental", "true");
  Sort boolean = d_tm.getBooleanSort();
  Term start = d_tm.mkVar(boolean);
  Grammar g = d_solver->mkGrammar({}, {start});
  Term truen = d_tm.mkBoolean(true);
  Term falsen = d_tm.mkBoolean(false);
  g.addRule(start, truen);
  g.addRule(start, falsen);

  // should enumerate true/false
  cvc5::Term t = d_solver->findSynth(modes::FindSynthTarget::ENUM, g);
  ASSERT_TRUE(!t.isNull() && t.getSort().isBoolean());
  t = d_solver->findSynthNext();
  ASSERT_TRUE(!t.isNull() && t.getSort().isBoolean());
}

TEST_F(TestApiBlackSolver, tupleProject)
{
  std::vector<Term> elements = {
      d_tm.mkBoolean(true),
      d_tm.mkInteger(3),
      d_tm.mkString("C"),
      d_tm.mkTerm(Kind::SET_SINGLETON, {d_tm.mkString("Z")})};

  Term tuple = d_tm.mkTuple(elements);

  std::vector<uint32_t> indices1 = {};
  std::vector<uint32_t> indices2 = {0};
  std::vector<uint32_t> indices3 = {0, 1};
  std::vector<uint32_t> indices4 = {0, 0, 2, 2, 3, 3, 0};
  std::vector<uint32_t> indices5 = {4};
  std::vector<uint32_t> indices6 = {0, 4};

  ASSERT_NO_THROW(
      d_tm.mkTerm(d_tm.mkOp(Kind::TUPLE_PROJECT, indices1), {tuple}));
  ASSERT_NO_THROW(
      d_tm.mkTerm(d_tm.mkOp(Kind::TUPLE_PROJECT, indices2), {tuple}));
  ASSERT_NO_THROW(
      d_tm.mkTerm(d_tm.mkOp(Kind::TUPLE_PROJECT, indices3), {tuple}));
  ASSERT_NO_THROW(
      d_tm.mkTerm(d_tm.mkOp(Kind::TUPLE_PROJECT, indices4), {tuple}));

  ASSERT_THROW(d_tm.mkTerm(d_tm.mkOp(Kind::TUPLE_PROJECT, indices5), {tuple}),
               CVC5ApiException);
  ASSERT_THROW(d_tm.mkTerm(d_tm.mkOp(Kind::TUPLE_PROJECT, indices6), {tuple}),
               CVC5ApiException);

  std::vector<uint32_t> indices = {0, 3, 2, 0, 1, 2};

  Op op = d_tm.mkOp(Kind::TUPLE_PROJECT, indices);
  Term projection = d_tm.mkTerm(op, {tuple});

  Datatype datatype = tuple.getSort().getDatatype();
  DatatypeConstructor constructor = datatype[0];

  for (size_t i = 0; i < indices.size(); i++)
  {
    Term selectorTerm = constructor[indices[i]].getTerm();
    Term selectedTerm =
        d_tm.mkTerm(Kind::APPLY_SELECTOR, {selectorTerm, tuple});
    Term simplifiedTerm = d_solver->simplify(selectedTerm);
    ASSERT_EQ(elements[indices[i]], simplifiedTerm);
  }

  ASSERT_EQ(
      "((_ tuple.project 0 3 2 0 1 2) (tuple true 3 \"C\" (set.singleton "
      "\"Z\")))",
      projection.toString());
}

TEST_F(TestApiBlackSolver, Output)
{
  ASSERT_THROW(d_solver->isOutputOn("foo-invalid"), CVC5ApiException);
  ASSERT_THROW(d_solver->getOutput("foo-invalid"), CVC5ApiException);
  ASSERT_FALSE(d_solver->isOutputOn("inst"));
  ASSERT_EQ(null_os.rdbuf(), d_solver->getOutput("inst").rdbuf());
  d_solver->setOption("output", "inst");
  ASSERT_TRUE(d_solver->isOutputOn("inst"));
  ASSERT_NE(null_os.rdbuf(), d_solver->getOutput("inst").rdbuf());
}

TEST_F(TestApiBlackSolver, issue7000)
{
  Sort s1 = d_tm.getIntegerSort();
  Sort s2 = d_tm.mkFunctionSort({s1}, s1);
  Sort s3 = d_tm.getRealSort();
  Term t4 = d_tm.mkPi();
  Term t7 = d_tm.mkConst(s3, "_x5");
  Term t37 = d_tm.mkConst(s2, "_x32");
  Term t59 = d_tm.mkConst(s2, "_x51");
  Term t72 = d_tm.mkTerm(Kind::EQUAL, {t37, t59});
  Term t74 = d_tm.mkTerm(Kind::GT, {t4, t7});
  Term query = d_tm.mkTerm(Kind::AND, {t72, t74, t72, t72});
  // throws logic exception since logic is not higher order by default
  ASSERT_THROW(d_solver->checkSatAssuming(query.notTerm()), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, issue5893)
{
  Sort bvsort4 = d_tm.mkBitVectorSort(4);
  Sort bvsort8 = d_tm.mkBitVectorSort(8);
  Sort arrsort = d_tm.mkArraySort(bvsort4, bvsort8);
  Term arr = d_tm.mkConst(arrsort, "arr");
  Term idx = d_tm.mkConst(bvsort4, "idx");
  Term ten = d_tm.mkBitVector(8, "10", 10);
  Term sel = d_tm.mkTerm(Kind::SELECT, {arr, idx});
  Term distinct = d_tm.mkTerm(Kind::DISTINCT, {sel, ten});
  ASSERT_NO_FATAL_FAILURE(distinct.getOp());
}

TEST_F(TestApiBlackSolver, proj_issue308)
{
  d_solver->setOption("check-proofs", "true");
  Sort s1 = d_tm.getBooleanSort();
  Term t1 = d_tm.mkConst(s1, "_x0");
  Term t2 = d_tm.mkTerm(Kind::XOR, {t1, t1});
  d_solver->checkSatAssuming({t2});
  auto unsat_core = d_solver->getUnsatCore();
  ASSERT_FALSE(unsat_core.empty());
}

TEST_F(TestApiBlackSolver, proj_issue373)
{
  Sort s1 = d_tm.getRealSort();

  DatatypeConstructorDecl ctor13 = d_tm.mkDatatypeConstructorDecl("_x115");
  ctor13.addSelector("_x109", s1);
  Sort s4 = d_solver->declareDatatype("_x86", {ctor13});

  Term t452 = d_tm.mkVar(s1, "_x281");
  Term bvl = d_tm.mkTerm(d_tm.mkOp(Kind::VARIABLE_LIST), {t452});
  Term acons =
      d_tm.mkTerm(d_tm.mkOp(Kind::APPLY_CONSTRUCTOR),
                  {s4.getDatatype().getConstructor("_x115").getTerm(), t452});
  // type exception
  ASSERT_THROW(
      d_tm.mkTerm(d_tm.mkOp(Kind::APPLY_CONSTRUCTOR), {bvl, acons, t452}),
      CVC5ApiException);
}

TEST_F(TestApiBlackSolver, proj_issue378)
{
  DatatypeDecl dtdecl;
  DatatypeConstructorDecl cdecl;

  Sort s1 = d_tm.getBooleanSort();

  dtdecl = d_tm.mkDatatypeDecl("_x0");
  cdecl = d_tm.mkDatatypeConstructorDecl("_x6");
  cdecl.addSelector("_x1", s1);
  dtdecl.addConstructor(cdecl);
  Sort s2 = d_tm.mkDatatypeSort(dtdecl);

  dtdecl = d_tm.mkDatatypeDecl("_x36");
  cdecl = d_tm.mkDatatypeConstructorDecl("_x42");
  cdecl.addSelector("_x37", s1);
  dtdecl.addConstructor(cdecl);
  Sort s4 = d_tm.mkDatatypeSort(dtdecl);

  Term t1 = d_tm.mkConst(s1, "_x53");
  Term t4 = d_tm.mkConst(s4, "_x56");
  Term t7 = d_tm.mkConst(s2, "_x58");

  Sort sp = d_tm.mkParamSort("_x178");
  dtdecl = d_tm.mkDatatypeDecl("_x176", {sp});
  cdecl = d_tm.mkDatatypeConstructorDecl("_x184");
  cdecl.addSelector("_x180", s2);
  dtdecl.addConstructor(cdecl);
  cdecl = d_tm.mkDatatypeConstructorDecl("_x186");
  cdecl.addSelector("_x185", sp);
  dtdecl.addConstructor(cdecl);
  Sort s7 = d_tm.mkDatatypeSort(dtdecl);
  Sort s9 = s7.instantiate({s2});
  Term t1507 =
      d_tm.mkTerm(Kind::APPLY_CONSTRUCTOR,
                  {s9.getDatatype().getConstructor("_x184").getTerm(), t7});
  ASSERT_NO_THROW(d_tm.mkTerm(
      Kind::APPLY_UPDATER,
      {s9.getDatatype().getConstructor("_x186").getSelector("_x185").getTerm(),
       t1507,
       t7}));
}

TEST_F(TestApiBlackSolver, proj_issue379)
{
  Sort bsort = d_tm.getBooleanSort();
  Sort psort = d_tm.mkParamSort("_x1");
  DatatypeConstructorDecl cdecl;
  DatatypeDecl dtdecl = d_tm.mkDatatypeDecl("x_0", {psort});
  cdecl = d_tm.mkDatatypeConstructorDecl("_x8");
  cdecl.addSelector("_x7", bsort);
  dtdecl.addConstructor(cdecl);
  cdecl = d_tm.mkDatatypeConstructorDecl("_x6");
  cdecl.addSelector("_x2", psort);
  cdecl.addSelectorSelf("_x3");
  cdecl.addSelector("_x4", psort);
  cdecl.addSelector("_x5", bsort);
  Sort s2 = d_tm.mkDatatypeSort(dtdecl);
  Sort s6 = s2.instantiate({bsort});
  Term t317 = d_tm.mkConst(bsort, "_x345");
  Term t843 = d_tm.mkConst(s6, "_x346");
  Term t879 = d_tm.mkTerm(Kind::APPLY_UPDATER,
                          {t843.getSort()
                               .getDatatype()
                               .getConstructor("_x8")
                               .getSelector("_x7")
                               .getUpdaterTerm(),
                           t843,
                           t317});
  ASSERT_EQ(t879.getSort(), s6);
}

TEST_F(TestApiBlackSolver, getDatatypeArity)
{
  DatatypeConstructorDecl ctor1 = d_tm.mkDatatypeConstructorDecl("_x21");
  DatatypeConstructorDecl ctor2 = d_tm.mkDatatypeConstructorDecl("_x31");
  Sort s3 = d_solver->declareDatatype(std::string("_x17"), {ctor1, ctor2});
  ASSERT_EQ(s3.getDatatypeArity(), 0);
}

TEST_F(TestApiBlackSolver, proj_issue381)
{
  Sort s1 = d_tm.getBooleanSort();

  Sort psort = d_tm.mkParamSort("_x9");
  DatatypeDecl dtdecl = d_tm.mkDatatypeDecl("_x8", {psort});
  DatatypeConstructorDecl ctor = d_tm.mkDatatypeConstructorDecl("_x22");
  ctor.addSelector("_x19", s1);
  dtdecl.addConstructor(ctor);
  Sort s3 = d_tm.mkDatatypeSort(dtdecl);
  Sort s6 = s3.instantiate({s1});
  Term t26 = d_tm.mkConst(s6, "_x63");
  Term t5 = d_tm.mkTrue();
  Term t187 = d_tm.mkTerm(Kind::APPLY_UPDATER,
                          {t26.getSort()
                               .getDatatype()
                               .getConstructor("_x22")
                               .getSelector("_x19")
                               .getUpdaterTerm(),
                           t26,
                           t5});
  ASSERT_NO_THROW(d_solver->simplify(t187));
}


TEST_F(TestApiBlackSolver, proj_issue382)
{
  Sort s1 = d_tm.getBooleanSort();
  Sort psort = d_tm.mkParamSort("_x1");
  DatatypeConstructorDecl ctor = d_tm.mkDatatypeConstructorDecl("_x20");
  ctor.addSelector("_x19", psort);
  DatatypeDecl dtdecl = d_tm.mkDatatypeDecl("_x0", {psort});
  dtdecl.addConstructor(ctor);
  Sort s2 = d_tm.mkDatatypeSort(dtdecl);
  Sort s6 = s2.instantiate({s1});
  Term t13 = d_tm.mkVar(s6, "_x58");
  Term t18 = d_tm.mkConst(s6, "_x63");
  Term t52 = d_tm.mkVar(s6, "_x70");
  Term t53 = d_tm.mkTerm(Kind::MATCH_BIND_CASE,
                         {d_tm.mkTerm(Kind::VARIABLE_LIST, {t52}), t52, t18});
  Term t73 = d_tm.mkVar(s1, "_x78");
  Term t81 = d_tm.mkTerm(
      Kind::MATCH_BIND_CASE,
      {d_tm.mkTerm(Kind::VARIABLE_LIST, {t73}),
       d_tm.mkTerm(
           Kind::APPLY_CONSTRUCTOR,
           {s6.getDatatype().getConstructor("_x20").getInstantiatedTerm(s6),
            t73}),
       t18});
  Term t82 = d_tm.mkTerm(Kind::MATCH, {t13, t53, t53, t53, t81});
  Term t325 = d_tm.mkTerm(
      Kind::APPLY_SELECTOR,
      {t82.getSort().getDatatype().getSelector("_x19").getTerm(), t82});
  ASSERT_NO_THROW(d_solver->simplify(t325));
}

TEST_F(TestApiBlackSolver, proj_issue383)
{
  d_solver->setOption("produce-models", "true");

  Sort s1 = d_tm.getBooleanSort();

  DatatypeConstructorDecl ctordecl = d_tm.mkDatatypeConstructorDecl("_x5");
  DatatypeDecl dtdecl = d_tm.mkDatatypeDecl("_x0");
  dtdecl.addConstructor(ctordecl);
  Sort s2 = d_tm.mkDatatypeSort(dtdecl);

  ctordecl = d_tm.mkDatatypeConstructorDecl("_x23");
  ctordecl.addSelectorSelf("_x21");
  dtdecl = d_tm.mkDatatypeDecl("_x12");
  dtdecl.addConstructor(ctordecl);
  ASSERT_THROW(d_tm.mkDatatypeSort(dtdecl), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, proj_issue386)
{
  Sort s1 = d_tm.getBooleanSort();
  Sort p1 = d_tm.mkParamSort("_p1");
  Sort p2 = d_tm.mkParamSort("_p2");
  DatatypeDecl dtdecl = d_tm.mkDatatypeDecl("_x0", {p1, p2});
  DatatypeConstructorDecl ctordecl = d_tm.mkDatatypeConstructorDecl("_x1");
  ctordecl.addSelector("_x2", p1);
  dtdecl.addConstructor(ctordecl);
  Sort s2 = d_tm.mkDatatypeSort(dtdecl);
  ASSERT_THROW(s2.instantiate({s1}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, proj_issue414)
{
  Sort s2 = d_tm.getRealSort();
  Term t1 = d_tm.mkConst(s2, "_x0");
  Term t16 = d_tm.mkTerm(Kind::PI);
  Term t53 = d_tm.mkTerm(Kind::SUB, {t1, t16});
  Term t54 = d_tm.mkTerm(Kind::SECANT, {t53});
  ASSERT_NO_THROW(d_solver->simplify(t54));
}

TEST_F(TestApiBlackSolver, proj_issue420)
{
  d_solver->setOption("strings-exp", "true");
  d_solver->setOption("produce-models", "true");
  d_solver->setOption("produce-unsat-cores", "true");
  Sort s2 = d_tm.getRealSort();
  Sort s3 = d_tm.mkUninterpretedSort("_u0");
  DatatypeDecl _dt1 = d_tm.mkDatatypeDecl("_dt1", {});
  DatatypeConstructorDecl _cons16 = d_tm.mkDatatypeConstructorDecl("_cons16");
  _cons16.addSelector("_sel13", s3);
  _dt1.addConstructor(_cons16);
  std::vector<Sort> _s4 = d_tm.mkDatatypeSorts({_dt1});
  Sort s4 = _s4[0];
  Sort s5 = d_tm.mkSequenceSort(s2);
  Term t3 = d_tm.mkConst(s5, "_x18");
  Term t7 = d_tm.mkConst(s4, "_x22");
  // was initially a dt size application
  Term t13 = d_tm.mkConst(d_tm.getIntegerSort(), "t13");
  Term t53 = d_tm.mkTerm(Kind::SEQ_NTH, {t3, t13});
  ASSERT_NO_THROW(d_solver->checkSat());
  ASSERT_NO_THROW(d_solver->blockModelValues({t53, t7}));
  ASSERT_NO_THROW(d_solver->checkSat());
}

TEST_F(TestApiBlackSolver, proj_issue440)
{
  d_solver->setLogic("QF_ALL");
  d_solver->setOption("global-negate", "true");
  d_solver->setOption("produce-unsat-cores", "true");
  Sort s1 = d_tm.getBooleanSort();
  Term t9 = d_tm.mkBoolean(true);
  Term t109 = d_tm.mkTerm(Kind::NOT, {t9});
  // should throw an option exception
  ASSERT_THROW(d_solver->checkSatAssuming({t109}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, proj_issue434)
{
  d_solver->setOption("dump-difficulty", "true");
  d_solver->setOption("debug-check-models", "true");
  Sort s1 = d_tm.mkUninterpretedSort("_u0");
  Sort s2 = d_tm.mkUninterpretedSort("_u1");
  Sort s3 = d_tm.mkUninterpretedSort("_u2");
  Sort s4 = d_tm.getBooleanSort();
  Term t1 = d_tm.mkConst(s1, "_x3");
  Term t3 = d_tm.mkConst(s3, "_x5");
  Term t15 = d_tm.mkConst(s1, "_x17");
  Term t26 = d_tm.mkBoolean(false);
  Term t60 = d_tm.mkVar(s4, "_f29_1");
  Term t73 = d_solver->defineFun("_f29", {t60}, t60.getSort(), t60);
  Term t123 = d_tm.mkVar(s4, "_f31_0");
  Term t135 = d_solver->defineFun("_f31", {t123}, t123.getSort(), t123);
  Term t506 = d_tm.mkVar(s1, "_f37_0");
  Term t507 = d_tm.mkVar(s4, "_f37_1");
  Term t510 = d_tm.mkTerm(Kind::APPLY_UF, {t73, t507});
  Term t530 = d_solver->defineFun("_f37", {t507}, t510.getSort(), t510);
  Term t559 = d_tm.mkTerm(Kind::DISTINCT, {t15, t1});
  Term t631 = d_tm.mkTerm(Kind::XOR, {t559, t26});
  Term t632 = d_tm.mkTerm(Kind::APPLY_UF, {t135, t631});
  Term t715 = d_tm.mkVar(s4, "_f40_0");
  Term t721 = d_tm.mkTerm(Kind::APPLY_UF, {t530, t715});
  Term t722 = d_tm.mkTerm(Kind::APPLY_UF, {t530, t721});
  Term t731 = d_solver->defineFun("_f40", {t715}, t722.getSort(), t722);
  Term t1014 = d_tm.mkVar(s4, "_f45_0");
  Term t1034 = d_tm.mkTerm(Kind::DISTINCT, {t510, t510});
  Term t1035 = d_tm.mkTerm(Kind::XOR, {t1034, t632});
  Term t1037 = d_tm.mkTerm(Kind::APPLY_UF, {t135, t1035});
  Term t1039 = d_tm.mkTerm(Kind::APPLY_UF, {t731, t1037});
  Term t1040 = d_solver->defineFun("_f45", {t1014}, t1039.getSort(), t1039);
  Term t1072 = d_tm.mkTerm(Kind::APPLY_UF, {t1040, t510});
  Term t1073 = d_tm.mkTerm(Kind::APPLY_UF, {t73, t1072});
  // the query has free variables, and should throw an exception
  ASSERT_THROW(d_solver->checkSatAssuming({t1073, t510}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, proj_issue436)
{
  d_solver->setOption("produce-abducts", "true");
  d_solver->setOption("solve-bv-as-int", "sum");
  Sort s8 = d_tm.mkBitVectorSort(68);
  Term t17 = d_tm.mkConst(s8, "_x6");
  Term t23;
  {
    uint32_t bw = s8.getBitVectorSize();
    t23 = d_tm.mkBitVector(bw, 1);
  }
  Term t33 = d_tm.mkTerm(Kind::BITVECTOR_ULT, {t17, t23});
  // solve-bv-as-int is incompatible with get-abduct
  ASSERT_THROW(d_solver->getAbduct(t33), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, proj_issue431)
{
  d_solver->setOption("produce-models", "true");
  d_solver->setOption("produce-unsat-assumptions", "true");
  d_solver->setOption("produce-assertions", "true");
  Sort s1 = d_tm.getStringSort();
  Sort s3 = d_tm.getIntegerSort();
  Sort s7 = d_tm.mkArraySort(s1, s3);
  Term t3 = d_tm.mkConst(s1, "_x2");
  Term t57 = d_tm.mkVar(s7, "_x38");
  Term t103 = d_tm.mkTerm(Kind::SELECT, {t57, t3});
  d_solver->checkSat();
  ASSERT_THROW(d_solver->blockModelValues({t103}), CVC5ApiException);
}
TEST_F(TestApiBlackSolver, proj_issue426)
{
  d_solver->setLogic("ALL");
  d_solver->setOption("strings-exp", "true");
  d_solver->setOption("produce-models", "true");
  d_solver->setOption("produce-assertions", "true");
  Sort s1 = d_tm.getRealSort();
  Sort s2 = d_tm.getRoundingModeSort();
  Sort s4 = d_tm.mkSequenceSort(s1);
  Sort s5 = d_tm.mkArraySort(s4, s4);
  Term t4 = d_tm.mkConst(s1, "_x3");
  Term t5 = d_tm.mkReal("9192/832927743");
  Term t19 = d_tm.mkConst(s2, "_x42");
  Term t24 = d_tm.mkConst(s5, "_x44");
  Term t37 = d_tm.mkRoundingMode(RoundingMode::ROUND_TOWARD_POSITIVE);
  d_solver->checkSat();
  d_solver->blockModelValues({t24, t19, t4, t37});
  d_solver->checkSat();
  ASSERT_NO_THROW(d_solver->getValue({t5}));
}

TEST_F(TestApiBlackSolver, proj_issue429)
{
  Sort s1 = d_tm.getRealSort();
  Term t6 = d_tm.mkConst(s1, "_x5");
  Term t16 =
      d_tm.mkReal(std::stoll("1696223.9473797265702297792792306581323741"));
  Term t111 = d_tm.mkTerm(Kind::SEQ_UNIT, {t16});
  Term t119 = d_tm.mkTerm(d_tm.mkOp(Kind::SEQ_UNIT), {t6});
  Term t126 = d_tm.mkTerm(Kind::SEQ_PREFIX, {t111, t119});
  d_solver->checkSatAssuming({t126.notTerm()});
}

TEST_F(TestApiBlackSolver, proj_issue422)
{
  d_solver->setOption("strings-exp", "true");
  d_solver->setOption("sygus-abort-size", "1");
  Sort s1 = d_tm.mkBitVectorSort(36);
  Sort s2 = d_tm.getStringSort();
  Term t1 = d_tm.mkConst(s2, "_x0");
  Term t2 = d_tm.mkConst(s1, "_x1");
  Term t11;
  {
    uint32_t bw = s1.getBitVectorSize();
    std::string val(bw, '1');
    val[0] = '0';
    t11 = d_tm.mkBitVector(bw, val, 2);
  }
  Term t60 = d_tm.mkTerm(Kind::SET_SINGLETON, {t1});
  Term t66 = d_tm.mkTerm(Kind::BITVECTOR_COMP, {t2, t11});
  Term t92 = d_tm.mkRegexpAll();
  Term t96 = d_tm.mkTerm(d_tm.mkOp(Kind::BITVECTOR_ZERO_EXTEND, {51}), {t66});
  Term t105 = d_tm.mkTerm(Kind::BITVECTOR_ADD, {t96, t96});
  Term t113 = d_tm.mkTerm(Kind::BITVECTOR_SUB, {t105, t105});
  Term t137 = d_tm.mkTerm(Kind::BITVECTOR_XOR, {t113, t105});
  Term t211 = d_tm.mkTerm(Kind::BITVECTOR_SLTBV, {t137, t137});
  Term t212 = d_tm.mkTerm(Kind::SET_MINUS, {t60, t60});
  Term t234 = d_tm.mkTerm(Kind::SET_CHOOSE, {t212});
  Term t250 = d_tm.mkTerm(Kind::STRING_REPLACE_RE_ALL, {t1, t92, t1});
  Term t259 = d_tm.mkTerm(Kind::STRING_REPLACE_ALL, {t234, t234, t250});
  Term t263 = d_tm.mkTerm(Kind::STRING_TO_LOWER, {t259});
  Term t272 = d_tm.mkTerm(Kind::BITVECTOR_SDIV, {t211, t66});
  Term t276 = d_tm.mkTerm(d_tm.mkOp(Kind::BITVECTOR_ZERO_EXTEND, {71}), {t272});
  Term t288 = d_tm.mkTerm(Kind::EQUAL, {t263, t1});
  Term t300 = d_tm.mkTerm(Kind::BITVECTOR_SLT, {t276, t276});
  Term t301 = d_tm.mkTerm(Kind::EQUAL, {t288, t300});
  d_solver->assertFormula({t301});
  Term t = d_solver->findSynth(modes::FindSynthTarget::REWRITE_INPUT);
}

TEST_F(TestApiBlackSolver, proj_issue423)
{
  d_solver->setOption("produce-models", "true");
  d_solver->setOption("produce-difficulty", "true");
  Sort s2 = d_tm.getRealSort();
  Sort s3 = d_tm.mkSequenceSort(s2);
  Term t2;
  {
    t2 = d_tm.mkEmptySequence(s3.getSequenceElementSort());
  }
  Term t22 = d_tm.mkReal("119605652059157009");
  Term t32 = d_tm.mkTerm(Kind::SEQ_UNIT, {t22});
  Term t43 = d_tm.mkTerm(Kind::SEQ_CONCAT, {t2, t32});
  Term t51 = d_tm.mkTerm(Kind::DISTINCT, {t32, t32});
  d_solver->checkSat();
  d_solver->blockModelValues({t51, t43});
}

TEST_F(TestApiBlackSolver, projIssue431)
{
  d_solver->setOption("produce-abducts", "true");
  Sort s2 = d_tm.mkBitVectorSort(22);
  Sort s4 = d_tm.mkSetSort(s2);
  Sort s5 = d_tm.getBooleanSort();
  Sort s6 = d_tm.getRealSort();
  Sort s7 = d_tm.mkFunctionSort({s6}, s5);
  DatatypeDecl _dt46 = d_tm.mkDatatypeDecl("_dt46", {});
  DatatypeConstructorDecl _cons64 = d_tm.mkDatatypeConstructorDecl("_cons64");
  _cons64.addSelector("_sel62", s6);
  _cons64.addSelector("_sel63", s4);
  _dt46.addConstructor(_cons64);
  Sort s14 = d_tm.mkDatatypeSorts({_dt46})[0];
  Term t31 = d_tm.mkConst(s7, "_x100");
  Term t47 = d_tm.mkConst(s14, "_x112");
  Term sel = t47.getSort()
                 .getDatatype()
                 .getConstructor("_cons64")
                 .getSelector("_sel62")
                 .getTerm();
  Term t274 = d_tm.mkTerm(Kind::APPLY_SELECTOR, {sel, t47});
  Term t488 = d_tm.mkTerm(Kind::APPLY_UF, {t31, t274});
  d_solver->assertFormula({t488});
  Term abduct;
  abduct = d_solver->getAbduct(t488);
}

TEST_F(TestApiBlackSolver, projIssue337)
{
  Term t =
      d_tm.mkTerm(Kind::SEQ_UNIT, {d_tm.mkReal("3416574625719121610379268")});
  Term tt = d_solver->simplify(t);
  ASSERT_EQ(t.getSort(), tt.getSort());
}

TEST_F(TestApiBlackSolver, declareOracleFunError)
{
  Sort iSort = d_tm.getIntegerSort();
  // cannot declare without option
  ASSERT_THROW(d_solver->declareOracleFun(
      "f",
      {iSort},
      iSort,
      [&](const std::vector<Term>& input) { return d_tm.mkInteger(0); });
               , CVC5ApiException);
  d_solver->setOption("oracles", "true");
  Sort nullSort;
  // bad sort
  ASSERT_THROW(d_solver->declareOracleFun(
      "f",
      {nullSort},
      iSort,
      [&](const std::vector<Term>& input) { return d_tm.mkInteger(0); });
               , CVC5ApiException);
}

TEST_F(TestApiBlackSolver, declareOracleFunUnsat)
{
  d_solver->setOption("oracles", "true");
  Sort iSort = d_tm.getIntegerSort();
  // f is the function implementing (lambda ((x Int)) (+ x 1))
  Term f = d_solver->declareOracleFun(
      "f", {iSort}, iSort, [&](const std::vector<Term>& input) {
        if (input[0].isUInt32Value())
        {
          return d_tm.mkInteger(input[0].getUInt32Value() + 1);
        }
        return d_tm.mkInteger(0);
      });
  Term three = d_tm.mkInteger(3);
  Term five = d_tm.mkInteger(5);
  Term eq =
      d_tm.mkTerm(Kind::EQUAL, {d_tm.mkTerm(Kind::APPLY_UF, {f, three}), five});
  d_solver->assertFormula(eq);
  // (f 3) = 5
  ASSERT_TRUE(d_solver->checkSat().isUnsat());
}

TEST_F(TestApiBlackSolver, declareOracleFunSat)
{
  d_solver->setOption("oracles", "true");
  d_solver->setOption("produce-models", "true");
  Sort iSort = d_tm.getIntegerSort();
  // f is the function implementing (lambda ((x Int)) (% x 10))
  Term f = d_solver->declareOracleFun(
      "f", {iSort}, iSort, [&](const std::vector<Term>& input) {
        if (input[0].isUInt32Value())
        {
          return d_tm.mkInteger(input[0].getUInt32Value() % 10);
        }
        return d_tm.mkInteger(0);
      });
  Term seven = d_tm.mkInteger(7);
  Term x = d_tm.mkConst(iSort, "x");
  Term lb = d_tm.mkTerm(Kind::GEQ, {x, d_tm.mkInteger(0)});
  d_solver->assertFormula(lb);
  Term ub = d_tm.mkTerm(Kind::LEQ, {x, d_tm.mkInteger(100)});
  d_solver->assertFormula(ub);
  Term eq =
      d_tm.mkTerm(Kind::EQUAL, {d_tm.mkTerm(Kind::APPLY_UF, {f, x}), seven});
  d_solver->assertFormula(eq);
  // x >= 0 ^ x <= 100 ^ (f x) = 7
  ASSERT_TRUE(d_solver->checkSat().isSat());
  Term xval = d_solver->getValue(x);
  ASSERT_TRUE(xval.isUInt32Value());
  ASSERT_TRUE(xval.getUInt32Value() % 10 == 7);
}

TEST_F(TestApiBlackSolver, declareOracleFunSat2)
{
  d_solver->setOption("oracles", "true");
  d_solver->setOption("produce-models", "true");
  Sort iSort = d_tm.getIntegerSort();
  Sort bSort = d_tm.getBooleanSort();
  // f is the function implementing (lambda ((x Int) (y Int)) (= x y))
  Term eq = d_solver->declareOracleFun(
      "eq", {iSort, iSort}, bSort, [&](const std::vector<Term>& input) {
        return d_tm.mkBoolean(input[0] == input[1]);
      });
  Term x = d_tm.mkConst(iSort, "x");
  Term y = d_tm.mkConst(iSort, "y");
  Term neq = d_tm.mkTerm(Kind::NOT, {d_tm.mkTerm(Kind::APPLY_UF, {eq, x, y})});
  d_solver->assertFormula(neq);
  // (not (eq x y))
  ASSERT_TRUE(d_solver->checkSat().isSat());
  Term xval = d_solver->getValue(x);
  Term yval = d_solver->getValue(y);
  ASSERT_TRUE(xval != yval);
}

TEST_F(TestApiBlackSolver, verticalBars)
{
  Term a = d_solver->declareFun("|a |", {}, d_tm.getRealSort());
  ASSERT_EQ("|a |", a.toString());
}

TEST_F(TestApiBlackSolver, getVersion)
{
  std::cout << d_solver->getVersion() << std::endl;
}

TEST_F(TestApiBlackSolver, multipleSolvers)
{
  Term function1, function2, value1, value2, definedFunction;
  Sort integerSort;
  Term zero;
  {
    Solver s1(d_tm);
    s1.setLogic("ALL");
    s1.setOption("produce-models", "true");
    integerSort = d_tm.getIntegerSort();
    function1 = s1.declareFun("f1", {}, d_tm.getIntegerSort());
    Term x = d_tm.mkVar(integerSort, "x");
    zero = d_tm.mkInteger(0);
    definedFunction = s1.defineFun("f", {x}, integerSort, zero);
    s1.assertFormula(function1.eqTerm(zero));
    s1.checkSat();
    value1 = s1.getValue(function1);
  }
  ASSERT_EQ(zero, value1);
  {
    Solver s2(d_tm);
    s2.setLogic("ALL");
    s2.setOption("produce-models", "true");
    function2 = s2.declareFun("function2", {}, integerSort);
    s2.assertFormula(function2.eqTerm(value1));
    s2.checkSat();
    value2 = s2.getValue(function2);
  }
  ASSERT_EQ(value1, value2);
  {
    Solver s3(d_tm);
    s3.setLogic("ALL");
    s3.setOption("produce-models", "true");
    function2 = s3.declareFun("function3", {}, integerSort);
    Term apply = d_tm.mkTerm(Kind::APPLY_UF, {definedFunction, zero});
    s3.assertFormula(function2.eqTerm(apply));
    s3.checkSat();
    Term value3 = s3.getValue(function2);
    ASSERT_EQ(value1, value3);
  }
}

#ifdef CVC5_USE_COCOA

TEST_F(TestApiBlackSolver, basicFiniteField)
{
  d_solver->setOption("produce-models", "true");

  Sort F = d_tm.mkFiniteFieldSort("5");
  Term a = d_tm.mkConst(F, "a");
  Term b = d_tm.mkConst(F, "b");
  ASSERT_EQ("5", F.getFiniteFieldSize());

  Term inv = d_tm.mkTerm(Kind::EQUAL,
                         {d_tm.mkTerm(Kind::FINITE_FIELD_MULT, {a, b}),
                          d_tm.mkFiniteFieldElem("1", F)});
  Term aIsTwo = d_tm.mkTerm(Kind::EQUAL, {a, d_tm.mkFiniteFieldElem("2", F)});

  d_solver->assertFormula(inv);
  d_solver->assertFormula(aIsTwo);
  ASSERT_TRUE(d_solver->checkSat().isSat());
  ASSERT_EQ(d_solver->getValue(a).getFiniteFieldValue(), "2");
  ASSERT_EQ(d_solver->getValue(b).getFiniteFieldValue(), "-2");

  Term bIsTwo = d_tm.mkTerm(Kind::EQUAL, {b, d_tm.mkFiniteFieldElem("2", F)});
  d_solver->assertFormula(bIsTwo);
  ASSERT_FALSE(d_solver->checkSat().isSat());
}

TEST_F(TestApiBlackSolver, basicFiniteFieldBase)
{
  Solver slv(d_tm);
  d_solver->setOption("produce-models", "true");

  Sort F = d_tm.mkFiniteFieldSort("101", 2);
  Term a = d_tm.mkConst(F, "a");
  Term b = d_tm.mkConst(F, "b");
  ASSERT_EQ("5", F.getFiniteFieldSize());

  Term inv = d_tm.mkTerm(Kind::EQUAL,
                         {d_tm.mkTerm(Kind::FINITE_FIELD_MULT, {a, b}),
                          d_tm.mkFiniteFieldElem("1", F, 3)});
  Term aIsTwo =
      d_tm.mkTerm(Kind::EQUAL, {a, d_tm.mkFiniteFieldElem("10", F, 2)});

  d_solver->assertFormula(inv);
  d_solver->assertFormula(aIsTwo);
  ASSERT_TRUE(d_solver->checkSat().isSat());
  ASSERT_EQ(d_solver->getValue(a).getFiniteFieldValue(), "2");
  ASSERT_EQ(d_solver->getValue(b).getFiniteFieldValue(), "-2");

  Term bIsTwo = d_tm.mkTerm(Kind::EQUAL, {b, d_tm.mkFiniteFieldElem("2", F)});
  d_solver->assertFormula(bIsTwo);
  ASSERT_FALSE(d_solver->checkSat().isSat());
}

#endif  // CVC5_USE_COCOA

}  // namespace test
}  // namespace cvc5::internal
