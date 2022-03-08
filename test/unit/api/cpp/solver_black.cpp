/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mudathir Mohamed, Andrew Reynolds
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

#include <algorithm>

#include "base/output.h"
#include "test_api.h"

namespace cvc5 {

using namespace api;

namespace test {

class TestApiBlackSolver : public TestApi
{
};

TEST_F(TestApiBlackSolver, pow2Large1)
{
  // Based on https://github.com/cvc5/cvc5-projects/issues/371
  Sort s1 = d_solver.getStringSort();
  Sort s2 = d_solver.getIntegerSort();
  Sort s4 = d_solver.mkArraySort(s1, s2);
  Sort s7 = d_solver.mkArraySort(s2, s1);
  Term t10 = d_solver.mkInteger("68038927088685865242724985643");
  Term t74 = d_solver.mkInteger("8416288636405");
  std::vector<DatatypeConstructorDecl> ctors;
  ctors.push_back(d_solver.mkDatatypeConstructorDecl("_x109"));
  ctors.back().addSelector("_x108", s7);
  ctors.push_back(d_solver.mkDatatypeConstructorDecl("_x113"));
  ctors.back().addSelector("_x110", s4);
  ctors.back().addSelector("_x111", s2);
  ctors.back().addSelector("_x112", s7);
  Sort s11 = d_solver.declareDatatype("_x107", ctors);
  Term t82 = d_solver.mkConst(s11, "_x114");
  Term t180 = d_solver.mkTerm(POW2, t10);
  Term t258 = d_solver.mkTerm(GEQ, t74, t180);
  d_solver.assertFormula(t258);
  ASSERT_THROW(d_solver.simplify(t82), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, pow2Large2)
{
  // Based on https://github.com/cvc5/cvc5-projects/issues/333
  Term t1 = d_solver.mkBitVector(63, ~(((uint64_t)1) << 62));
  Term t2 = d_solver.mkTerm(Kind::BITVECTOR_TO_NAT, t1);
  Term t3 = d_solver.mkTerm(Kind::POW2, t2);
  Term t4 = d_solver.mkTerm(Kind::DISTINCT, t3, t2);
  ASSERT_THROW(d_solver.checkSatAssuming({t4}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, pow2Large3)
{
  // Based on https://github.com/cvc5/cvc5-projects/issues/339
  Sort s4 = d_solver.getIntegerSort();
  Term t203 = d_solver.mkInteger("6135470354240554220207");
  Term t262 = d_solver.mkTerm(POW2, t203);
  Term t536 = d_solver.mkTerm(d_solver.mkOp(INT_TO_BITVECTOR, 49), t262);
  ASSERT_THROW(d_solver.simplify(t536), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, recoverableException)
{
  d_solver.setOption("produce-models", "true");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x).notTerm());
  ASSERT_THROW(d_solver.getValue(x), CVC5ApiRecoverableException);
}

TEST_F(TestApiBlackSolver, supportsFloatingPoint)
{
  ASSERT_NO_THROW(d_solver.mkRoundingMode(ROUND_NEAREST_TIES_TO_EVEN));
}

TEST_F(TestApiBlackSolver, getBooleanSort)
{
  ASSERT_NO_THROW(d_solver.getBooleanSort());
}

TEST_F(TestApiBlackSolver, getIntegerSort)
{
  ASSERT_NO_THROW(d_solver.getIntegerSort());
}

TEST_F(TestApiBlackSolver, getNullSort)
{
  ASSERT_NO_THROW(d_solver.getNullSort());
}

TEST_F(TestApiBlackSolver, getRealSort)
{
  ASSERT_NO_THROW(d_solver.getRealSort());
}

TEST_F(TestApiBlackSolver, getRegExpSort)
{
  ASSERT_NO_THROW(d_solver.getRegExpSort());
}

TEST_F(TestApiBlackSolver, getStringSort)
{
  ASSERT_NO_THROW(d_solver.getStringSort());
}

TEST_F(TestApiBlackSolver, getRoundingModeSort)
{
  ASSERT_NO_THROW(d_solver.getRoundingModeSort());
}

TEST_F(TestApiBlackSolver, mkArraySort)
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

  Sort fpSort = d_solver.mkFloatingPointSort(3, 5);
  ASSERT_NO_THROW(d_solver.mkArraySort(fpSort, fpSort));
  ASSERT_NO_THROW(d_solver.mkArraySort(bvSort, fpSort));

  Solver slv;
  ASSERT_THROW(slv.mkArraySort(boolSort, boolSort), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkBitVectorSort)
{
  ASSERT_NO_THROW(d_solver.mkBitVectorSort(32));
  ASSERT_THROW(d_solver.mkBitVectorSort(0), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkFloatingPointSort)
{
  ASSERT_NO_THROW(d_solver.mkFloatingPointSort(4, 8));
  ASSERT_THROW(d_solver.mkFloatingPointSort(0, 8), CVC5ApiException);
  ASSERT_THROW(d_solver.mkFloatingPointSort(4, 0), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkDatatypeSort)
{
  DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_solver.getIntegerSort());
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  ASSERT_NO_THROW(d_solver.mkDatatypeSort(dtypeSpec));

  Solver slv;
  ASSERT_THROW(slv.mkDatatypeSort(dtypeSpec), CVC5ApiException);

  DatatypeDecl throwsDtypeSpec = d_solver.mkDatatypeDecl("list");
  ASSERT_THROW(d_solver.mkDatatypeSort(throwsDtypeSpec), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkDatatypeSorts)
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

  ASSERT_THROW(slv.mkDatatypeSorts(decls), CVC5ApiException);

  DatatypeDecl throwsDtypeSpec = d_solver.mkDatatypeDecl("list");
  std::vector<DatatypeDecl> throwsDecls = {throwsDtypeSpec};
  ASSERT_THROW(d_solver.mkDatatypeSorts(throwsDecls), CVC5ApiException);

  /* with unresolved sorts */
  Sort unresList = d_solver.mkUnresolvedSort("ulist");
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

  ASSERT_THROW(slv.mkDatatypeSorts(udecls, unresSorts), CVC5ApiException);

  /* mutually recursive with unresolved parameterized sorts */
  Sort p0 = d_solver.mkParamSort("p0");
  Sort p1 = d_solver.mkParamSort("p1");
  Sort u0 = d_solver.mkUnresolvedSort("dt0", 1);
  Sort u1 = d_solver.mkUnresolvedSort("dt1", 1);
  DatatypeDecl dtdecl0 = d_solver.mkDatatypeDecl("dt0", p0);
  DatatypeDecl dtdecl1 = d_solver.mkDatatypeDecl("dt1", p1);
  DatatypeConstructorDecl ctordecl0 = d_solver.mkDatatypeConstructorDecl("c0");
  ctordecl0.addSelector("s0", u1.instantiate({p0}));
  DatatypeConstructorDecl ctordecl1 = d_solver.mkDatatypeConstructorDecl("c1");
  ctordecl1.addSelector("s1", u0.instantiate({p1}));
  dtdecl0.addConstructor(ctordecl0);
  dtdecl1.addConstructor(ctordecl1);
  std::vector<Sort> dt_sorts =
      d_solver.mkDatatypeSorts({dtdecl0, dtdecl1}, {u0, u1});
  Sort isort1 = dt_sorts[1].instantiate({d_solver.getBooleanSort()});
  Term t1 = d_solver.mkConst(isort1, "t");
  Term t0 = d_solver.mkTerm(
      APPLY_SELECTOR,
      t1.getSort().getDatatype().getSelector("s1").getSelectorTerm(),
      t1);
  ASSERT_EQ(dt_sorts[0].instantiate({d_solver.getBooleanSort()}), t0.getSort());

  /* Note: More tests are in datatype_api_black. */
}

TEST_F(TestApiBlackSolver, mkFunctionSort)
{
  ASSERT_NO_THROW(d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                          d_solver.getIntegerSort()));
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  // function arguments are allowed
  ASSERT_NO_THROW(d_solver.mkFunctionSort(funSort, d_solver.getIntegerSort()));
  // non-first-class arguments are not allowed
  Sort reSort = d_solver.getRegExpSort();
  ASSERT_THROW(d_solver.mkFunctionSort(reSort, d_solver.getIntegerSort()),
               CVC5ApiException);
  ASSERT_THROW(d_solver.mkFunctionSort(d_solver.getIntegerSort(), funSort),
               CVC5ApiException);
  ASSERT_NO_THROW(d_solver.mkFunctionSort(
      {d_solver.mkUninterpretedSort("u"), d_solver.getIntegerSort()},
      d_solver.getIntegerSort()));
  Sort funSort2 = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                          d_solver.getIntegerSort());
  // function arguments are allowed
  ASSERT_NO_THROW(
      d_solver.mkFunctionSort({funSort2, d_solver.mkUninterpretedSort("u")},
                              d_solver.getIntegerSort()));
  ASSERT_THROW(d_solver.mkFunctionSort({d_solver.getIntegerSort(),
                                        d_solver.mkUninterpretedSort("u")},
                                       funSort2),
               CVC5ApiException);

  Solver slv;
  ASSERT_THROW(slv.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                  d_solver.getIntegerSort()),
               CVC5ApiException);
  ASSERT_THROW(slv.mkFunctionSort(slv.mkUninterpretedSort("u"),
                                  d_solver.getIntegerSort()),
               CVC5ApiException);
  std::vector<Sort> sorts1 = {d_solver.getBooleanSort(),
                              slv.getIntegerSort(),
                              d_solver.getIntegerSort()};
  std::vector<Sort> sorts2 = {slv.getBooleanSort(), slv.getIntegerSort()};
  ASSERT_NO_THROW(slv.mkFunctionSort(sorts2, slv.getIntegerSort()));
  ASSERT_THROW(slv.mkFunctionSort(sorts1, slv.getIntegerSort()),
               CVC5ApiException);
  ASSERT_THROW(slv.mkFunctionSort(sorts2, d_solver.getIntegerSort()),
               CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkParamSort)
{
  ASSERT_NO_THROW(d_solver.mkParamSort("T"));
  ASSERT_NO_THROW(d_solver.mkParamSort(""));
}

TEST_F(TestApiBlackSolver, mkPredicateSort)
{
  ASSERT_NO_THROW(d_solver.mkPredicateSort({d_solver.getIntegerSort()}));
  ASSERT_THROW(d_solver.mkPredicateSort({}), CVC5ApiException);
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  // functions as arguments are allowed
  ASSERT_NO_THROW(
      d_solver.mkPredicateSort({d_solver.getIntegerSort(), funSort}));

  Solver slv;
  ASSERT_THROW(slv.mkPredicateSort({d_solver.getIntegerSort()}),
               CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkRecordSort)
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
  ASSERT_THROW(slv.mkRecordSort(fields), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkSetSort)
{
  ASSERT_NO_THROW(d_solver.mkSetSort(d_solver.getBooleanSort()));
  ASSERT_NO_THROW(d_solver.mkSetSort(d_solver.getIntegerSort()));
  ASSERT_NO_THROW(d_solver.mkSetSort(d_solver.mkBitVectorSort(4)));
  Solver slv;
  ASSERT_THROW(slv.mkSetSort(d_solver.mkBitVectorSort(4)), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkBagSort)
{
  ASSERT_NO_THROW(d_solver.mkBagSort(d_solver.getBooleanSort()));
  ASSERT_NO_THROW(d_solver.mkBagSort(d_solver.getIntegerSort()));
  ASSERT_NO_THROW(d_solver.mkBagSort(d_solver.mkBitVectorSort(4)));
  Solver slv;
  ASSERT_THROW(slv.mkBagSort(d_solver.mkBitVectorSort(4)), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkSequenceSort)
{
  ASSERT_NO_THROW(d_solver.mkSequenceSort(d_solver.getBooleanSort()));
  ASSERT_NO_THROW(d_solver.mkSequenceSort(
      d_solver.mkSequenceSort(d_solver.getIntegerSort())));
  Solver slv;
  ASSERT_THROW(slv.mkSequenceSort(d_solver.getIntegerSort()), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkUninterpretedSort)
{
  ASSERT_NO_THROW(d_solver.mkUninterpretedSort("u"));
  ASSERT_NO_THROW(d_solver.mkUninterpretedSort(""));
}

TEST_F(TestApiBlackSolver, mkUnresolvedSort)
{
  ASSERT_NO_THROW(d_solver.mkUnresolvedSort("u"));
  ASSERT_NO_THROW(d_solver.mkUnresolvedSort("u", 1));
  ASSERT_NO_THROW(d_solver.mkUnresolvedSort(""));
  ASSERT_NO_THROW(d_solver.mkUnresolvedSort("", 1));
}

TEST_F(TestApiBlackSolver, mkSortConstructorSort)
{
  ASSERT_NO_THROW(d_solver.mkSortConstructorSort("s", 2));
  ASSERT_NO_THROW(d_solver.mkSortConstructorSort("", 2));
  ASSERT_THROW(d_solver.mkSortConstructorSort("", 0), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkTupleSort)
{
  ASSERT_NO_THROW(d_solver.mkTupleSort({d_solver.getIntegerSort()}));
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  ASSERT_THROW(d_solver.mkTupleSort({d_solver.getIntegerSort(), funSort}),
               CVC5ApiException);

  Solver slv;
  ASSERT_THROW(slv.mkTupleSort({d_solver.getIntegerSort()}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkBitVector)
{
  ASSERT_NO_THROW(d_solver.mkBitVector(8, 2));
  ASSERT_NO_THROW(d_solver.mkBitVector(32, 2));
  ASSERT_NO_THROW(d_solver.mkBitVector(8, "-1111111", 2));
  ASSERT_NO_THROW(d_solver.mkBitVector(8, "0101", 2));
  ASSERT_NO_THROW(d_solver.mkBitVector(8, "00000101", 2));
  ASSERT_NO_THROW(d_solver.mkBitVector(8, "-127", 10));
  ASSERT_NO_THROW(d_solver.mkBitVector(8, "255", 10));
  ASSERT_NO_THROW(d_solver.mkBitVector(8, "-7f", 16));
  ASSERT_NO_THROW(d_solver.mkBitVector(8, "a0", 16));

  ASSERT_THROW(d_solver.mkBitVector(0, 2), CVC5ApiException);
  ASSERT_THROW(d_solver.mkBitVector(0, "-127", 10), CVC5ApiException);
  ASSERT_THROW(d_solver.mkBitVector(0, "a0", 16), CVC5ApiException);

  ASSERT_THROW(d_solver.mkBitVector(8, "", 2), CVC5ApiException);

  ASSERT_THROW(d_solver.mkBitVector(8, "101", 5), CVC5ApiException);
  ASSERT_THROW(d_solver.mkBitVector(8, "128", 11), CVC5ApiException);
  ASSERT_THROW(d_solver.mkBitVector(8, "a0", 21), CVC5ApiException);

  ASSERT_THROW(d_solver.mkBitVector(8, "-11111111", 2), CVC5ApiException);
  ASSERT_THROW(d_solver.mkBitVector(8, "101010101", 2), CVC5ApiException);
  ASSERT_THROW(d_solver.mkBitVector(8, "-256", 10), CVC5ApiException);
  ASSERT_THROW(d_solver.mkBitVector(8, "257", 10), CVC5ApiException);
  ASSERT_THROW(d_solver.mkBitVector(8, "-a0", 16), CVC5ApiException);
  ASSERT_THROW(d_solver.mkBitVector(8, "fffff", 16), CVC5ApiException);

  ASSERT_THROW(d_solver.mkBitVector(8, "10201010", 2), CVC5ApiException);
  ASSERT_THROW(d_solver.mkBitVector(8, "-25x", 10), CVC5ApiException);
  ASSERT_THROW(d_solver.mkBitVector(8, "2x7", 10), CVC5ApiException);
  ASSERT_THROW(d_solver.mkBitVector(8, "fzff", 16), CVC5ApiException);

  ASSERT_EQ(d_solver.mkBitVector(8, "0101", 2),
            d_solver.mkBitVector(8, "00000101", 2));
  ASSERT_EQ(d_solver.mkBitVector(4, "-1", 2),
            d_solver.mkBitVector(4, "1111", 2));
  ASSERT_EQ(d_solver.mkBitVector(4, "-1", 16),
            d_solver.mkBitVector(4, "1111", 2));
  ASSERT_EQ(d_solver.mkBitVector(4, "-1", 10),
            d_solver.mkBitVector(4, "1111", 2));
  ASSERT_EQ(d_solver.mkBitVector(8, "01010101", 2).toString(), "#b01010101");
  ASSERT_EQ(d_solver.mkBitVector(8, "F", 16).toString(), "#b00001111");
  ASSERT_EQ(d_solver.mkBitVector(8, "-1", 10),
            d_solver.mkBitVector(8, "FF", 16));
}

TEST_F(TestApiBlackSolver, mkVar)
{
  Sort boolSort = d_solver.getBooleanSort();
  Sort intSort = d_solver.getIntegerSort();
  Sort funSort = d_solver.mkFunctionSort(intSort, boolSort);
  ASSERT_NO_THROW(d_solver.mkVar(boolSort));
  ASSERT_NO_THROW(d_solver.mkVar(funSort));
  ASSERT_NO_THROW(d_solver.mkVar(boolSort, std::string("b")));
  ASSERT_NO_THROW(d_solver.mkVar(funSort, ""));
  ASSERT_THROW(d_solver.mkVar(Sort()), CVC5ApiException);
  ASSERT_THROW(d_solver.mkVar(Sort(), "a"), CVC5ApiException);
  Solver slv;
  ASSERT_THROW(slv.mkVar(boolSort, "x"), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkBoolean)
{
  ASSERT_NO_THROW(d_solver.mkBoolean(true));
  ASSERT_NO_THROW(d_solver.mkBoolean(false));
}

TEST_F(TestApiBlackSolver, mkRoundingMode)
{
  ASSERT_NO_THROW(d_solver.mkRoundingMode(RoundingMode::ROUND_TOWARD_ZERO));
}

TEST_F(TestApiBlackSolver, mkFloatingPoint)
{
  Term t1 = d_solver.mkBitVector(8);
  Term t2 = d_solver.mkBitVector(4);
  Term t3 = d_solver.mkInteger(2);
  ASSERT_NO_THROW(d_solver.mkFloatingPoint(3, 5, t1));
  ASSERT_THROW(d_solver.mkFloatingPoint(0, 5, Term()), CVC5ApiException);
  ASSERT_THROW(d_solver.mkFloatingPoint(0, 5, t1), CVC5ApiException);
  ASSERT_THROW(d_solver.mkFloatingPoint(3, 0, t1), CVC5ApiException);
  ASSERT_THROW(d_solver.mkFloatingPoint(3, 5, t2), CVC5ApiException);
  ASSERT_THROW(d_solver.mkFloatingPoint(3, 5, t2), CVC5ApiException);

  Solver slv;
  ASSERT_THROW(slv.mkFloatingPoint(3, 5, t1), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkCardinalityConstraint)
{
  Sort su = d_solver.mkUninterpretedSort("u");
  Sort si = d_solver.getIntegerSort();
  ASSERT_NO_THROW(d_solver.mkCardinalityConstraint(su, 3));
  ASSERT_THROW(d_solver.mkCardinalityConstraint(si, 3), CVC5ApiException);
  ASSERT_THROW(d_solver.mkCardinalityConstraint(su, 0), CVC5ApiException);
  Solver slv;
  ASSERT_THROW(slv.mkCardinalityConstraint(su, 3), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkEmptySet)
{
  Solver slv;
  Sort s = d_solver.mkSetSort(d_solver.getBooleanSort());
  ASSERT_NO_THROW(d_solver.mkEmptySet(Sort()));
  ASSERT_NO_THROW(d_solver.mkEmptySet(s));
  ASSERT_THROW(d_solver.mkEmptySet(d_solver.getBooleanSort()),
               CVC5ApiException);
  ASSERT_THROW(slv.mkEmptySet(s), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkEmptyBag)
{
  Solver slv;
  Sort s = d_solver.mkBagSort(d_solver.getBooleanSort());
  ASSERT_NO_THROW(d_solver.mkEmptyBag(Sort()));
  ASSERT_NO_THROW(d_solver.mkEmptyBag(s));
  ASSERT_THROW(d_solver.mkEmptyBag(d_solver.getBooleanSort()),
               CVC5ApiException);
  ASSERT_THROW(slv.mkEmptyBag(s), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkEmptySequence)
{
  Solver slv;
  Sort s = d_solver.mkSequenceSort(d_solver.getBooleanSort());
  ASSERT_NO_THROW(d_solver.mkEmptySequence(s));
  ASSERT_NO_THROW(d_solver.mkEmptySequence(d_solver.getBooleanSort()));
  ASSERT_THROW(slv.mkEmptySequence(s), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkFalse)
{
  ASSERT_NO_THROW(d_solver.mkFalse());
  ASSERT_NO_THROW(d_solver.mkFalse());
}

TEST_F(TestApiBlackSolver, mkFloatingPointNaN)
{
  ASSERT_NO_THROW(d_solver.mkFloatingPointNaN(3, 5));
}

TEST_F(TestApiBlackSolver, mkFloatingPointNegZero)
{
  ASSERT_NO_THROW(d_solver.mkFloatingPointNegZero(3, 5));
}

TEST_F(TestApiBlackSolver, mkFloatingPointNegInf)
{
  ASSERT_NO_THROW(d_solver.mkFloatingPointNegInf(3, 5));
}

TEST_F(TestApiBlackSolver, mkFloatingPointPosInf)
{
  ASSERT_NO_THROW(d_solver.mkFloatingPointPosInf(3, 5));
}

TEST_F(TestApiBlackSolver, mkFloatingPointPosZero)
{
  ASSERT_NO_THROW(d_solver.mkFloatingPointPosZero(3, 5));
}

TEST_F(TestApiBlackSolver, mkOp)
{
  // mkOp(Kind kind, Kind k)
  ASSERT_THROW(d_solver.mkOp(BITVECTOR_EXTRACT, EQUAL), CVC5ApiException);

  // mkOp(Kind kind, const std::string& arg)
  ASSERT_NO_THROW(d_solver.mkOp(DIVISIBLE, "2147483648"));
  ASSERT_THROW(d_solver.mkOp(BITVECTOR_EXTRACT, "asdf"), CVC5ApiException);

  // mkOp(Kind kind, uint32_t arg)
  ASSERT_NO_THROW(d_solver.mkOp(DIVISIBLE, 1));
  ASSERT_NO_THROW(d_solver.mkOp(BITVECTOR_ROTATE_LEFT, 1));
  ASSERT_NO_THROW(d_solver.mkOp(BITVECTOR_ROTATE_RIGHT, 1));
  ASSERT_THROW(d_solver.mkOp(BITVECTOR_EXTRACT, 1), CVC5ApiException);

  // mkOp(Kind kind, uint32_t arg1, uint32_t arg2)
  ASSERT_NO_THROW(d_solver.mkOp(BITVECTOR_EXTRACT, 1, 1));
  ASSERT_THROW(d_solver.mkOp(DIVISIBLE, 1, 2), CVC5ApiException);

  // mkOp(Kind kind, std::vector<uint32_t> args)
  std::vector<uint32_t> args = {1, 2, 2};
  ASSERT_NO_THROW(d_solver.mkOp(TUPLE_PROJECT, args));
}

TEST_F(TestApiBlackSolver, mkPi) { ASSERT_NO_THROW(d_solver.mkPi()); }

TEST_F(TestApiBlackSolver, mkInteger)
{
  ASSERT_NO_THROW(d_solver.mkInteger("123"));
  ASSERT_THROW(d_solver.mkInteger("1.23"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger("1/23"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger("12/3"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger(".2"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger("2."), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger(""), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger("asdf"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger("1.2/3"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger("."), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger("/"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger("2/"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger("/2"), CVC5ApiException);

  ASSERT_NO_THROW(d_solver.mkReal(std::string("123")));
  ASSERT_THROW(d_solver.mkInteger(std::string("1.23")), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("1/23")), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("12/3")), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string(".2")), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("2.")), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("")), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("asdf")), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("1.2/3")), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string(".")), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("/")), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("2/")), CVC5ApiException);
  ASSERT_THROW(d_solver.mkInteger(std::string("/2")), CVC5ApiException);

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

TEST_F(TestApiBlackSolver, mkReal)
{
  ASSERT_NO_THROW(d_solver.mkReal("123"));
  ASSERT_NO_THROW(d_solver.mkReal("1.23"));
  ASSERT_NO_THROW(d_solver.mkReal("1/23"));
  ASSERT_NO_THROW(d_solver.mkReal("12/3"));
  ASSERT_NO_THROW(d_solver.mkReal(".2"));
  ASSERT_NO_THROW(d_solver.mkReal("2."));
  ASSERT_THROW(d_solver.mkReal(""), CVC5ApiException);
  ASSERT_THROW(d_solver.mkReal("asdf"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkReal("1.2/3"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkReal("."), CVC5ApiException);
  ASSERT_THROW(d_solver.mkReal("/"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkReal("2/"), CVC5ApiException);
  ASSERT_THROW(d_solver.mkReal("/2"), CVC5ApiException);

  ASSERT_NO_THROW(d_solver.mkReal(std::string("123")));
  ASSERT_NO_THROW(d_solver.mkReal(std::string("1.23")));
  ASSERT_NO_THROW(d_solver.mkReal(std::string("1/23")));
  ASSERT_NO_THROW(d_solver.mkReal(std::string("12/3")));
  ASSERT_NO_THROW(d_solver.mkReal(std::string(".2")));
  ASSERT_NO_THROW(d_solver.mkReal(std::string("2.")));
  ASSERT_THROW(d_solver.mkReal(std::string("")), CVC5ApiException);
  ASSERT_THROW(d_solver.mkReal(std::string("asdf")), CVC5ApiException);
  ASSERT_THROW(d_solver.mkReal(std::string("1.2/3")), CVC5ApiException);
  ASSERT_THROW(d_solver.mkReal(std::string(".")), CVC5ApiException);
  ASSERT_THROW(d_solver.mkReal(std::string("/")), CVC5ApiException);
  ASSERT_THROW(d_solver.mkReal(std::string("2/")), CVC5ApiException);
  ASSERT_THROW(d_solver.mkReal(std::string("/2")), CVC5ApiException);

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
  ASSERT_NO_THROW(d_solver.mkReal("-1/-1"));
  ASSERT_NO_THROW(d_solver.mkReal("1/-1"));
  ASSERT_NO_THROW(d_solver.mkReal("-1/1"));
  ASSERT_NO_THROW(d_solver.mkReal("1/1"));
  ASSERT_THROW(d_solver.mkReal("/-5"), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkRegexpAll)
{
  Sort strSort = d_solver.getStringSort();
  Term s = d_solver.mkConst(strSort, "s");
  ASSERT_NO_THROW(d_solver.mkTerm(STRING_IN_REGEXP, s, d_solver.mkRegexpAll()));
}

TEST_F(TestApiBlackSolver, mkRegexpAllchar)
{
  Sort strSort = d_solver.getStringSort();
  Term s = d_solver.mkConst(strSort, "s");
  ASSERT_NO_THROW(
      d_solver.mkTerm(STRING_IN_REGEXP, s, d_solver.mkRegexpAllchar()));
}

TEST_F(TestApiBlackSolver, mkRegexpNone)
{
  Sort strSort = d_solver.getStringSort();
  Term s = d_solver.mkConst(strSort, "s");
  ASSERT_NO_THROW(
      d_solver.mkTerm(STRING_IN_REGEXP, s, d_solver.mkRegexpNone()));
}

TEST_F(TestApiBlackSolver, mkSepEmp) { ASSERT_NO_THROW(d_solver.mkSepEmp()); }

TEST_F(TestApiBlackSolver, mkSepNil)
{
  ASSERT_NO_THROW(d_solver.mkSepNil(d_solver.getBooleanSort()));
  ASSERT_THROW(d_solver.mkSepNil(Sort()), CVC5ApiException);
  Solver slv;
  ASSERT_THROW(slv.mkSepNil(d_solver.getIntegerSort()), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkString)
{
  ASSERT_NO_THROW(d_solver.mkString(""));
  ASSERT_NO_THROW(d_solver.mkString("asdfasdf"));
  ASSERT_EQ(d_solver.mkString("asdf\\nasdf").toString(),
            "\"asdf\\u{5c}nasdf\"");
  ASSERT_EQ(d_solver.mkString("asdf\\u{005c}nasdf", true).toString(),
            "\"asdf\\u{5c}nasdf\"");
}

TEST_F(TestApiBlackSolver, mkTerm)
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
  ASSERT_NO_THROW(d_solver.mkTerm(PI, v6));
  ASSERT_NO_THROW(d_solver.mkTerm(d_solver.mkOp(PI)));
  ASSERT_NO_THROW(d_solver.mkTerm(d_solver.mkOp(PI), v6));
  ASSERT_NO_THROW(d_solver.mkTerm(REGEXP_NONE));
  ASSERT_NO_THROW(d_solver.mkTerm(REGEXP_NONE, v6));
  ASSERT_NO_THROW(d_solver.mkTerm(d_solver.mkOp(REGEXP_NONE)));
  ASSERT_NO_THROW(d_solver.mkTerm(d_solver.mkOp(REGEXP_NONE), v6));
  ASSERT_NO_THROW(d_solver.mkTerm(REGEXP_ALLCHAR));
  ASSERT_NO_THROW(d_solver.mkTerm(REGEXP_ALLCHAR, v6));
  ASSERT_NO_THROW(d_solver.mkTerm(d_solver.mkOp(REGEXP_ALLCHAR)));
  ASSERT_NO_THROW(d_solver.mkTerm(d_solver.mkOp(REGEXP_ALLCHAR), v6));
  ASSERT_NO_THROW(d_solver.mkTerm(SEP_EMP));
  ASSERT_NO_THROW(d_solver.mkTerm(SEP_EMP, v6));
  ASSERT_NO_THROW(d_solver.mkTerm(d_solver.mkOp(SEP_EMP)));
  ASSERT_NO_THROW(d_solver.mkTerm(d_solver.mkOp(SEP_EMP), v6));
  ASSERT_THROW(d_solver.mkTerm(CONST_BITVECTOR), CVC5ApiException);

  // mkTerm(Kind kind, Term child) const
  ASSERT_NO_THROW(d_solver.mkTerm(NOT, d_solver.mkTrue()));
  ASSERT_NO_THROW(
      d_solver.mkTerm(BAG_MAKE, d_solver.mkTrue(), d_solver.mkInteger(1)));
  ASSERT_THROW(d_solver.mkTerm(NOT, Term()), CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(NOT, a), CVC5ApiException);
  ASSERT_THROW(slv.mkTerm(NOT, d_solver.mkTrue()), CVC5ApiException);

  // mkTerm(Kind kind, Term child1, Term child2) const
  ASSERT_NO_THROW(d_solver.mkTerm(EQUAL, a, b));
  ASSERT_THROW(d_solver.mkTerm(EQUAL, Term(), b), CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(EQUAL, a, Term()), CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(EQUAL, a, d_solver.mkTrue()), CVC5ApiException);
  ASSERT_THROW(slv.mkTerm(EQUAL, a, b), CVC5ApiException);

  // mkTerm(Kind kind, Term child1, Term child2, Term child3) const
  ASSERT_NO_THROW(d_solver.mkTerm(
      ITE, d_solver.mkTrue(), d_solver.mkTrue(), d_solver.mkTrue()));
  ASSERT_THROW(
      d_solver.mkTerm(ITE, Term(), d_solver.mkTrue(), d_solver.mkTrue()),
      CVC5ApiException);
  ASSERT_THROW(
      d_solver.mkTerm(ITE, d_solver.mkTrue(), Term(), d_solver.mkTrue()),
      CVC5ApiException);
  ASSERT_THROW(
      d_solver.mkTerm(ITE, d_solver.mkTrue(), d_solver.mkTrue(), Term()),
      CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(ITE, d_solver.mkTrue(), d_solver.mkTrue(), b),
               CVC5ApiException);
  ASSERT_THROW(
      slv.mkTerm(ITE, d_solver.mkTrue(), d_solver.mkTrue(), d_solver.mkTrue()),
      CVC5ApiException);

  // mkTerm(Kind kind, const std::vector<Term>& children) const
  ASSERT_NO_THROW(d_solver.mkTerm(EQUAL, v1));
  ASSERT_THROW(d_solver.mkTerm(EQUAL, v2), CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(EQUAL, v3), CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(DISTINCT, v6), CVC5ApiException);

  // Test cases that are nary via the API but have arity = 2 internally
  Sort s_bool = d_solver.getBooleanSort();
  Term t_bool = d_solver.mkConst(s_bool, "t_bool");
  ASSERT_NO_THROW(d_solver.mkTerm(IMPLIES, {t_bool, t_bool, t_bool}));
  ASSERT_NO_THROW(
      d_solver.mkTerm(d_solver.mkOp(IMPLIES), {t_bool, t_bool, t_bool}));
  ASSERT_NO_THROW(d_solver.mkTerm(XOR, {t_bool, t_bool, t_bool}));
  ASSERT_NO_THROW(
      d_solver.mkTerm(d_solver.mkOp(XOR), {t_bool, t_bool, t_bool}));
  Term t_int = d_solver.mkConst(d_solver.getIntegerSort(), "t_int");
  ASSERT_NO_THROW(d_solver.mkTerm(DIVISION, {t_int, t_int, t_int}));
  ASSERT_NO_THROW(
      d_solver.mkTerm(d_solver.mkOp(DIVISION), {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_solver.mkTerm(INTS_DIVISION, {t_int, t_int, t_int}));
  ASSERT_NO_THROW(
      d_solver.mkTerm(d_solver.mkOp(INTS_DIVISION), {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_solver.mkTerm(SUB, {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_solver.mkTerm(d_solver.mkOp(SUB), {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_solver.mkTerm(EQUAL, {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_solver.mkTerm(d_solver.mkOp(EQUAL), {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_solver.mkTerm(LT, {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_solver.mkTerm(d_solver.mkOp(LT), {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_solver.mkTerm(GT, {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_solver.mkTerm(d_solver.mkOp(GT), {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_solver.mkTerm(LEQ, {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_solver.mkTerm(d_solver.mkOp(LEQ), {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_solver.mkTerm(GEQ, {t_int, t_int, t_int}));
  ASSERT_NO_THROW(d_solver.mkTerm(d_solver.mkOp(GEQ), {t_int, t_int, t_int}));
  Term t_reg = d_solver.mkConst(d_solver.getRegExpSort(), "t_reg");
  ASSERT_NO_THROW(d_solver.mkTerm(REGEXP_DIFF, {t_reg, t_reg, t_reg}));
  ASSERT_NO_THROW(
      d_solver.mkTerm(d_solver.mkOp(REGEXP_DIFF), {t_reg, t_reg, t_reg}));
  Term t_fun = d_solver.mkConst(
      d_solver.mkFunctionSort({s_bool, s_bool, s_bool}, s_bool));
  ASSERT_NO_THROW(d_solver.mkTerm(HO_APPLY, {t_fun, t_bool, t_bool, t_bool}));
  ASSERT_NO_THROW(d_solver.mkTerm(d_solver.mkOp(HO_APPLY),
                                  {t_fun, t_bool, t_bool, t_bool}));
}

TEST_F(TestApiBlackSolver, mkTermFromOp)
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
  ASSERT_THROW(d_solver.mkTerm(APPLY_SELECTOR, nilTerm1), CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(APPLY_SELECTOR, consTerm1), CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(APPLY_CONSTRUCTOR, consTerm2), CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(opterm1), CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(APPLY_SELECTOR, headTerm1), CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(opterm1), CVC5ApiException);
  ASSERT_THROW(slv.mkTerm(APPLY_CONSTRUCTOR, nilTerm1), CVC5ApiException);

  // mkTerm(Op op, Term child) const
  ASSERT_NO_THROW(d_solver.mkTerm(opterm1, a));
  ASSERT_NO_THROW(d_solver.mkTerm(opterm2, d_solver.mkInteger(1)));
  ASSERT_NO_THROW(d_solver.mkTerm(APPLY_SELECTOR, headTerm1, c));
  ASSERT_NO_THROW(d_solver.mkTerm(APPLY_SELECTOR, tailTerm2, c));
  ASSERT_THROW(d_solver.mkTerm(opterm2, a), CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(opterm1, Term()), CVC5ApiException);
  ASSERT_THROW(
      d_solver.mkTerm(APPLY_CONSTRUCTOR, consTerm1, d_solver.mkInteger(0)),
      CVC5ApiException);
  ASSERT_THROW(slv.mkTerm(opterm1, a), CVC5ApiException);

  // mkTerm(Op op, Term child1, Term child2) const
  ASSERT_NO_THROW(
      d_solver.mkTerm(APPLY_CONSTRUCTOR,
                      consTerm1,
                      d_solver.mkInteger(0),
                      d_solver.mkTerm(APPLY_CONSTRUCTOR, nilTerm1)));
  ASSERT_THROW(
      d_solver.mkTerm(opterm2, d_solver.mkInteger(1), d_solver.mkInteger(2)),
      CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(opterm1, a, b), CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(opterm2, d_solver.mkInteger(1), Term()),
               CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(opterm2, Term(), d_solver.mkInteger(1)),
               CVC5ApiException);
  ASSERT_THROW(slv.mkTerm(APPLY_CONSTRUCTOR,
                          consTerm1,
                          d_solver.mkInteger(0),
                          d_solver.mkTerm(APPLY_CONSTRUCTOR, nilTerm1)),
               CVC5ApiException);

  // mkTerm(Op op, Term child1, Term child2, Term child3) const
  ASSERT_THROW(d_solver.mkTerm(opterm1, a, b, a), CVC5ApiException);
  ASSERT_THROW(
      d_solver.mkTerm(
          opterm2, d_solver.mkInteger(1), d_solver.mkInteger(1), Term()),
      CVC5ApiException);

  // mkTerm(Op op, const std::vector<Term>& children) const
  ASSERT_NO_THROW(d_solver.mkTerm(opterm2, v4));
  ASSERT_THROW(d_solver.mkTerm(opterm2, v1), CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(opterm2, v2), CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(opterm2, v3), CVC5ApiException);
  ASSERT_THROW(slv.mkTerm(opterm2, v4), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkTrue)
{
  ASSERT_NO_THROW(d_solver.mkTrue());
  ASSERT_NO_THROW(d_solver.mkTrue());
}

TEST_F(TestApiBlackSolver, mkTuple)
{
  ASSERT_NO_THROW(d_solver.mkTuple({d_solver.mkBitVectorSort(3)},
                                   {d_solver.mkBitVector(3, "101", 2)}));
  ASSERT_NO_THROW(
      d_solver.mkTuple({d_solver.getRealSort()}, {d_solver.mkInteger("5")}));

  ASSERT_THROW(d_solver.mkTuple({}, {d_solver.mkBitVector(3, "101", 2)}),
               CVC5ApiException);
  ASSERT_THROW(d_solver.mkTuple({d_solver.mkBitVectorSort(4)},
                                {d_solver.mkBitVector(3, "101", 2)}),
               CVC5ApiException);
  ASSERT_THROW(
      d_solver.mkTuple({d_solver.getIntegerSort()}, {d_solver.mkReal("5.3")}),
      CVC5ApiException);
  Solver slv;
  ASSERT_THROW(slv.mkTuple({d_solver.mkBitVectorSort(3)},
                           {slv.mkBitVector(3, "101", 2)}),
               CVC5ApiException);
  ASSERT_THROW(slv.mkTuple({slv.mkBitVectorSort(3)},
                           {d_solver.mkBitVector(3, "101", 2)}),
               CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkUniverseSet)
{
  ASSERT_NO_THROW(d_solver.mkUniverseSet(d_solver.getBooleanSort()));
  ASSERT_THROW(d_solver.mkUniverseSet(Sort()), CVC5ApiException);
  Solver slv;
  ASSERT_THROW(slv.mkUniverseSet(d_solver.getBooleanSort()), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkConst)
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
  ASSERT_THROW(d_solver.mkConst(Sort()), CVC5ApiException);
  ASSERT_THROW(d_solver.mkConst(Sort(), "a"), CVC5ApiException);

  Solver slv;
  ASSERT_THROW(slv.mkConst(boolSort), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkConstArray)
{
  Sort intSort = d_solver.getIntegerSort();
  Sort arrSort = d_solver.mkArraySort(intSort, intSort);
  Term zero = d_solver.mkInteger(0);
  Term constArr = d_solver.mkConstArray(arrSort, zero);

  ASSERT_NO_THROW(d_solver.mkConstArray(arrSort, zero));
  ASSERT_THROW(d_solver.mkConstArray(Sort(), zero), CVC5ApiException);
  ASSERT_THROW(d_solver.mkConstArray(arrSort, Term()), CVC5ApiException);
  ASSERT_THROW(d_solver.mkConstArray(arrSort, d_solver.mkBitVector(1, 1)),
               CVC5ApiException);
  ASSERT_THROW(d_solver.mkConstArray(intSort, zero), CVC5ApiException);
  Solver slv;
  Term zero2 = slv.mkInteger(0);
  Sort arrSort2 = slv.mkArraySort(slv.getIntegerSort(), slv.getIntegerSort());
  ASSERT_THROW(slv.mkConstArray(arrSort2, zero), CVC5ApiException);
  ASSERT_THROW(slv.mkConstArray(arrSort, zero2), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, declareDatatype)
{
  DatatypeConstructorDecl lin = d_solver.mkDatatypeConstructorDecl("lin");
  std::vector<DatatypeConstructorDecl> ctors0 = {lin};
  ASSERT_NO_THROW(d_solver.declareDatatype(std::string(""), ctors0));

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

  // must have at least one constructor
  std::vector<DatatypeConstructorDecl> ctors4;
  ASSERT_THROW(d_solver.declareDatatype(std::string("c"), ctors4),
               CVC5ApiException);
  // constructors may not be reused
  DatatypeConstructorDecl ctor1 = d_solver.mkDatatypeConstructorDecl("_x21");
  DatatypeConstructorDecl ctor2 = d_solver.mkDatatypeConstructorDecl("_x31");
  Sort s3 = d_solver.declareDatatype(std::string("_x17"), {ctor1, ctor2});
  ASSERT_THROW(d_solver.declareDatatype(std::string("_x86"), {ctor1, ctor2}),
               CVC5ApiException);
  // constructor belongs to different solver instance
  Solver slv;
  ASSERT_THROW(slv.declareDatatype(std::string("a"), ctors1), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, declareFun)
{
  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  ASSERT_NO_THROW(d_solver.declareFun("f1", {}, bvSort));
  ASSERT_NO_THROW(
      d_solver.declareFun("f3", {bvSort, d_solver.getIntegerSort()}, bvSort));
  ASSERT_THROW(d_solver.declareFun("f2", {}, funSort), CVC5ApiException);
  // functions as arguments is allowed
  ASSERT_NO_THROW(d_solver.declareFun("f4", {bvSort, funSort}, bvSort));
  ASSERT_THROW(d_solver.declareFun("f5", {bvSort, bvSort}, funSort),
               CVC5ApiException);
  Solver slv;
  ASSERT_THROW(slv.declareFun("f1", {}, bvSort), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, declareSort)
{
  ASSERT_NO_THROW(d_solver.declareSort("s", 0));
  ASSERT_NO_THROW(d_solver.declareSort("s", 2));
  ASSERT_NO_THROW(d_solver.declareSort("", 2));
}

TEST_F(TestApiBlackSolver, defineSort)
{
  Sort sortVar0 = d_solver.mkParamSort("T0");
  Sort sortVar1 = d_solver.mkParamSort("T1");
  Sort intSort = d_solver.getIntegerSort();
  Sort realSort = d_solver.getRealSort();
  Sort arraySort0 = d_solver.mkArraySort(sortVar0, sortVar0);
  Sort arraySort1 = d_solver.mkArraySort(sortVar0, sortVar1);
  // Now create instantiations of the defined sorts
  ASSERT_NO_THROW(arraySort0.substitute(sortVar0, intSort));
  ASSERT_NO_THROW(
      arraySort1.substitute({sortVar0, sortVar1}, {intSort, realSort}));
}

TEST_F(TestApiBlackSolver, defineFun)
{
  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort funSort = d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"),
                                         d_solver.getIntegerSort());
  Term b1 = d_solver.mkVar(bvSort, "b1");
  Term b2 = d_solver.mkVar(d_solver.getIntegerSort(), "b2");
  Term b3 = d_solver.mkVar(funSort, "b3");
  Term v1 = d_solver.mkConst(bvSort, "v1");
  Term v2 = d_solver.mkConst(funSort, "v2");
  ASSERT_NO_THROW(d_solver.defineFun("f", {}, bvSort, v1));
  ASSERT_NO_THROW(d_solver.defineFun("ff", {b1, b2}, bvSort, v1));
  ASSERT_THROW(d_solver.defineFun("ff", {v1, b2}, bvSort, v1),
               CVC5ApiException);
  ASSERT_THROW(d_solver.defineFun("fff", {b1}, bvSort, v2), CVC5ApiException);
  ASSERT_THROW(d_solver.defineFun("ffff", {b1}, funSort, v2), CVC5ApiException);
  // b3 has function sort, which is allowed as an argument
  ASSERT_NO_THROW(d_solver.defineFun("fffff", {b1, b3}, bvSort, v1));

  Solver slv;
  Sort bvSort2 = slv.mkBitVectorSort(32);
  Term v12 = slv.mkConst(bvSort2, "v1");
  Term b12 = slv.mkVar(bvSort2, "b1");
  Term b22 = slv.mkVar(slv.getIntegerSort(), "b2");
  ASSERT_THROW(slv.defineFun("f", {}, bvSort, v12), CVC5ApiException);
  ASSERT_THROW(slv.defineFun("f", {}, bvSort2, v1), CVC5ApiException);
  ASSERT_THROW(slv.defineFun("ff", {b1, b22}, bvSort2, v12), CVC5ApiException);
  ASSERT_THROW(slv.defineFun("ff", {b12, b2}, bvSort2, v12), CVC5ApiException);
  ASSERT_THROW(slv.defineFun("ff", {b12, b22}, bvSort, v12), CVC5ApiException);
  ASSERT_THROW(slv.defineFun("ff", {b12, b22}, bvSort2, v1), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, defineFunGlobal)
{
  Sort bSort = d_solver.getBooleanSort();

  Term bTrue = d_solver.mkBoolean(true);
  // (define-fun f () Bool true)
  Term f = d_solver.defineFun("f", {}, bSort, bTrue, true);
  Term b = d_solver.mkVar(bSort, "b");
  // (define-fun g (b Bool) Bool b)
  Term g = d_solver.defineFun("g", {b}, bSort, b, true);

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

TEST_F(TestApiBlackSolver, defineFunRec)
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
               CVC5ApiException);
  ASSERT_THROW(d_solver.defineFunRec("ff", {b1, v2}, bvSort, v1),
               CVC5ApiException);
  ASSERT_THROW(d_solver.defineFunRec("ffff", {b1}, funSort2, v3),
               CVC5ApiException);
  // b3 has function sort, which is allowed as an argument
  ASSERT_NO_THROW(d_solver.defineFunRec("fffff", {b1, b3}, bvSort, v1));
  ASSERT_THROW(d_solver.defineFunRec(f1, {b1}, v1), CVC5ApiException);
  ASSERT_THROW(d_solver.defineFunRec(f1, {b1, b11}, v2), CVC5ApiException);
  ASSERT_THROW(d_solver.defineFunRec(f1, {b1, b11}, v3), CVC5ApiException);
  ASSERT_THROW(d_solver.defineFunRec(f2, {b1}, v2), CVC5ApiException);
  ASSERT_THROW(d_solver.defineFunRec(f3, {b1}, v1), CVC5ApiException);

  Solver slv;
  Sort bvSort2 = slv.mkBitVectorSort(32);
  Term v12 = slv.mkConst(bvSort2, "v1");
  Term b12 = slv.mkVar(bvSort2, "b1");
  Term b22 = slv.mkVar(slv.getIntegerSort(), "b2");
  ASSERT_NO_THROW(slv.defineFunRec("f", {}, bvSort2, v12));
  ASSERT_NO_THROW(slv.defineFunRec("ff", {b12, b22}, bvSort2, v12));
  ASSERT_THROW(slv.defineFunRec("f", {}, bvSort, v12), CVC5ApiException);
  ASSERT_THROW(slv.defineFunRec("f", {}, bvSort2, v1), CVC5ApiException);
  ASSERT_THROW(slv.defineFunRec("ff", {b1, b22}, bvSort2, v12),
               CVC5ApiException);
  ASSERT_THROW(slv.defineFunRec("ff", {b12, b2}, bvSort2, v12),
               CVC5ApiException);
  ASSERT_THROW(slv.defineFunRec("ff", {b12, b22}, bvSort, v12),
               CVC5ApiException);
  ASSERT_THROW(slv.defineFunRec("ff", {b12, b22}, bvSort2, v1),
               CVC5ApiException);
}

TEST_F(TestApiBlackSolver, defineFunRecWrongLogic)
{
  d_solver.setLogic("QF_BV");
  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort funSort = d_solver.mkFunctionSort({bvSort, bvSort}, bvSort);
  Term b = d_solver.mkVar(bvSort, "b");
  Term v = d_solver.mkConst(bvSort, "v");
  Term f = d_solver.mkConst(funSort, "f");
  ASSERT_THROW(d_solver.defineFunRec("f", {}, bvSort, v), CVC5ApiException);
  ASSERT_THROW(d_solver.defineFunRec(f, {b, b}, v), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, defineFunRecGlobal)
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

TEST_F(TestApiBlackSolver, defineFunsRec)
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
               CVC5ApiException);
  ASSERT_THROW(d_solver.defineFunsRec({f1, f3}, {{b1, b11}, {b4}}, {v1, v2}),
               CVC5ApiException);
  ASSERT_THROW(d_solver.defineFunsRec({f1, f2}, {{b1}, {b4}}, {v1, v2}),
               CVC5ApiException);
  ASSERT_THROW(d_solver.defineFunsRec({f1, f2}, {{b1, b2}, {b4}}, {v1, v2}),
               CVC5ApiException);
  ASSERT_THROW(d_solver.defineFunsRec({f1, f2}, {{b1, b11}, {b4}}, {v1, v4}),
               CVC5ApiException);

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
               CVC5ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f2}, {{b12, b112}, {b42}}, {v12, v22}),
               CVC5ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f22}, {{b1, b112}, {b42}}, {v12, v22}),
               CVC5ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f22}, {{b12, b11}, {b42}}, {v12, v22}),
               CVC5ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f22}, {{b12, b112}, {b4}}, {v12, v22}),
               CVC5ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f22}, {{b12, b112}, {b42}}, {v1, v22}),
               CVC5ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f22}, {{b12, b112}, {b42}}, {v12, v2}),
               CVC5ApiException);
}

TEST_F(TestApiBlackSolver, defineFunsRecWrongLogic)
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
               CVC5ApiException);
}

TEST_F(TestApiBlackSolver, defineFunsRecGlobal)
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

TEST_F(TestApiBlackSolver, uFIteration)
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
    ASSERT_LT(idx, 3);
    ASSERT_EQ(c, expected_children[idx]);
    idx++;
  }
}

TEST_F(TestApiBlackSolver, getInfo)
{
  ASSERT_NO_THROW(d_solver.getInfo("name"));
  ASSERT_THROW(d_solver.getInfo("asdf"), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getAbduct)
{
  d_solver.setLogic("QF_LIA");
  d_solver.setOption("produce-abducts", "true");
  d_solver.setOption("incremental", "false");

  Sort intSort = d_solver.getIntegerSort();
  Term zero = d_solver.mkInteger(0);
  Term x = d_solver.mkConst(intSort, "x");
  Term y = d_solver.mkConst(intSort, "y");

  // Assumptions for abduction: x > 0
  d_solver.assertFormula(d_solver.mkTerm(GT, x, zero));
  // Conjecture for abduction: y > 0
  Term conj = d_solver.mkTerm(GT, y, zero);
  Term output;
  // Call the abduction api, while the resulting abduct is the output
  ASSERT_TRUE(d_solver.getAbduct(conj, output));
  // We expect the resulting output to be a boolean formula
  ASSERT_TRUE(!output.isNull() && output.getSort().isBoolean());

  // try with a grammar, a simple grammar admitting true
  Sort boolean = d_solver.getBooleanSort();
  Term truen = d_solver.mkBoolean(true);
  Term start = d_solver.mkVar(boolean);
  Term output2;
  Grammar g = d_solver.mkSygusGrammar({}, {start});
  Term conj2 = d_solver.mkTerm(GT, x, zero);
  ASSERT_NO_THROW(g.addRule(start, truen));
  // Call the abduction api, while the resulting abduct is the output
  ASSERT_TRUE(d_solver.getAbduct(conj2, g, output2));
  // abduct must be true
  ASSERT_EQ(output2, truen);
}

TEST_F(TestApiBlackSolver, getAbduct2)
{
  d_solver.setLogic("QF_LIA");
  d_solver.setOption("incremental", "false");
  Sort intSort = d_solver.getIntegerSort();
  Term zero = d_solver.mkInteger(0);
  Term x = d_solver.mkConst(intSort, "x");
  Term y = d_solver.mkConst(intSort, "y");
  // Assumptions for abduction: x > 0
  d_solver.assertFormula(d_solver.mkTerm(GT, x, zero));
  // Conjecture for abduction: y > 0
  Term conj = d_solver.mkTerm(GT, y, zero);
  Term output;
  // Fails due to option not set
  ASSERT_THROW(d_solver.getAbduct(conj, output), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getAbductNext)
{
  d_solver.setLogic("QF_LIA");
  d_solver.setOption("produce-abducts", "true");
  d_solver.setOption("incremental", "true");

  Sort intSort = d_solver.getIntegerSort();
  Term zero = d_solver.mkInteger(0);
  Term x = d_solver.mkConst(intSort, "x");
  Term y = d_solver.mkConst(intSort, "y");

  // Assumptions for abduction: x > 0
  d_solver.assertFormula(d_solver.mkTerm(GT, x, zero));
  // Conjecture for abduction: y > 0
  Term conj = d_solver.mkTerm(GT, y, zero);
  Term output;
  // Call the abduction api, while the resulting abduct is the output
  ASSERT_TRUE(d_solver.getAbduct(conj, output));
  Term output2;
  ASSERT_TRUE(d_solver.getAbductNext(output2));
  // should produce a different output
  ASSERT_TRUE(output != output2);
}

TEST_F(TestApiBlackSolver, getInterpolant)
{
  d_solver.setLogic("QF_LIA");
  d_solver.setOption("produce-interpols", "default");
  d_solver.setOption("incremental", "false");

  Sort intSort = d_solver.getIntegerSort();
  Term zero = d_solver.mkInteger(0);
  Term x = d_solver.mkConst(intSort, "x");
  Term y = d_solver.mkConst(intSort, "y");
  Term z = d_solver.mkConst(intSort, "z");

  // Assumptions for interpolation: x + y > 0 /\ x < 0
  d_solver.assertFormula(d_solver.mkTerm(GT, d_solver.mkTerm(ADD, x, y), zero));
  d_solver.assertFormula(d_solver.mkTerm(LT, x, zero));
  // Conjecture for interpolation: y + z > 0 \/ z < 0
  Term conj =
      d_solver.mkTerm(OR,
                      d_solver.mkTerm(GT, d_solver.mkTerm(ADD, y, z), zero),
                      d_solver.mkTerm(LT, z, zero));
  Term output;
  // Call the interpolation api, while the resulting interpolant is the output
  d_solver.getInterpolant(conj, output);

  // We expect the resulting output to be a boolean formula
  ASSERT_TRUE(output.getSort().isBoolean());
}

TEST_F(TestApiBlackSolver, getInterpolantNext)
{
  d_solver.setLogic("QF_LIA");
  d_solver.setOption("produce-interpols", "default");
  d_solver.setOption("incremental", "true");

  Sort intSort = d_solver.getIntegerSort();
  Term zero = d_solver.mkInteger(0);
  Term x = d_solver.mkConst(intSort, "x");
  Term y = d_solver.mkConst(intSort, "y");
  Term z = d_solver.mkConst(intSort, "z");
  // Assumptions for interpolation: x + y > 0 /\ x < 0
  d_solver.assertFormula(d_solver.mkTerm(GT, d_solver.mkTerm(ADD, x, y), zero));
  d_solver.assertFormula(d_solver.mkTerm(LT, x, zero));
  // Conjecture for interpolation: y + z > 0 \/ z < 0
  Term conj =
      d_solver.mkTerm(OR,
                      d_solver.mkTerm(GT, d_solver.mkTerm(ADD, y, z), zero),
                      d_solver.mkTerm(LT, z, zero));
  Term output;
  d_solver.getInterpolant(conj, output);
  Term output2;
  d_solver.getInterpolantNext(output2);

  // We expect the next output to be distinct
  ASSERT_TRUE(output != output2);
}

TEST_F(TestApiBlackSolver, declarePool)
{
  Sort intSort = d_solver.getIntegerSort();
  Sort setSort = d_solver.mkSetSort(intSort);
  Term zero = d_solver.mkInteger(0);
  Term x = d_solver.mkConst(intSort, "x");
  Term y = d_solver.mkConst(intSort, "y");
  // declare a pool with initial value { 0, x, y }
  Term p = d_solver.declarePool("p", intSort, {zero, x, y});
  // pool should have the same sort
  ASSERT_TRUE(p.getSort() == setSort);
  // cannot pass null sort
  Sort nullSort;
  ASSERT_THROW(d_solver.declarePool("i", nullSort, {}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getOp)
{
  Sort bv32 = d_solver.mkBitVectorSort(32);
  Term a = d_solver.mkConst(bv32, "a");
  Op ext = d_solver.mkOp(BITVECTOR_EXTRACT, 2, 1);
  Term exta = d_solver.mkTerm(ext, a);

  ASSERT_FALSE(a.hasOp());
  ASSERT_THROW(a.getOp(), CVC5ApiException);
  ASSERT_TRUE(exta.hasOp());
  ASSERT_EQ(exta.getOp(), ext);

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
  ASSERT_TRUE(listcons1.hasOp());
  ASSERT_TRUE(listhead.hasOp());
}

TEST_F(TestApiBlackSolver, getOption)
{
  ASSERT_NO_THROW(d_solver.getOption("incremental"));
  ASSERT_THROW(d_solver.getOption("asdf"), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getOptionNames)
{
  std::vector<std::string> names = d_solver.getOptionNames();
  ASSERT_TRUE(names.size() > 100);
  ASSERT_NE(std::find(names.begin(), names.end(), "verbose"), names.end());
  ASSERT_EQ(std::find(names.begin(), names.end(), "foobar"), names.end());
}

TEST_F(TestApiBlackSolver, getOptionInfo)
{
  {
    EXPECT_THROW(d_solver.getOptionInfo("asdf-invalid"), CVC5ApiException);
  }
  {
    api::OptionInfo info = d_solver.getOptionInfo("verbose");
    EXPECT_EQ("verbose", info.name);
    EXPECT_EQ(std::vector<std::string>{}, info.aliases);
    EXPECT_TRUE(std::holds_alternative<OptionInfo::VoidInfo>(info.valueInfo));
  }
  {
    // int64 type with default
    api::OptionInfo info = d_solver.getOptionInfo("verbosity");
    EXPECT_EQ("verbosity", info.name);
    EXPECT_EQ(std::vector<std::string>{}, info.aliases);
    EXPECT_TRUE(std::holds_alternative<OptionInfo::NumberInfo<int64_t>>(
        info.valueInfo));
    auto numInfo = std::get<OptionInfo::NumberInfo<int64_t>>(info.valueInfo);
    EXPECT_EQ(0, numInfo.defaultValue);
    EXPECT_EQ(0, numInfo.currentValue);
    EXPECT_FALSE(numInfo.minimum || numInfo.maximum);
    ASSERT_EQ(info.intValue(), 0);
  }
  {
    auto info = d_solver.getOptionInfo("random-freq");
    ASSERT_EQ(info.name, "random-freq");
    ASSERT_EQ(info.aliases, std::vector<std::string>{"random-frequency"});
    ASSERT_TRUE(std::holds_alternative<api::OptionInfo::NumberInfo<double>>(
        info.valueInfo));
    auto ni = std::get<api::OptionInfo::NumberInfo<double>>(info.valueInfo);
    ASSERT_EQ(ni.currentValue, 0.0);
    ASSERT_EQ(ni.defaultValue, 0.0);
    ASSERT_TRUE(ni.minimum && ni.maximum);
    ASSERT_EQ(*ni.minimum, 0.0);
    ASSERT_EQ(*ni.maximum, 1.0);
    ASSERT_EQ(info.doubleValue(), 0.0);
  }
  {
    // mode option
    api::OptionInfo info = d_solver.getOptionInfo("simplification");
    EXPECT_EQ("simplification", info.name);
    EXPECT_EQ(std::vector<std::string>{"simplification-mode"}, info.aliases);
    EXPECT_TRUE(std::holds_alternative<OptionInfo::ModeInfo>(info.valueInfo));
    auto modeInfo = std::get<OptionInfo::ModeInfo>(info.valueInfo);
    EXPECT_EQ("batch", modeInfo.defaultValue);
    EXPECT_EQ("batch", modeInfo.currentValue);
    EXPECT_EQ(2, modeInfo.modes.size());
    EXPECT_TRUE(std::find(modeInfo.modes.begin(), modeInfo.modes.end(), "batch")
                != modeInfo.modes.end());
    EXPECT_TRUE(std::find(modeInfo.modes.begin(), modeInfo.modes.end(), "none")
                != modeInfo.modes.end());
  }
}

TEST_F(TestApiBlackSolver, getUnsatAssumptions1)
{
  d_solver.setOption("incremental", "false");
  d_solver.checkSatAssuming(d_solver.mkFalse());
  ASSERT_THROW(d_solver.getUnsatAssumptions(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getUnsatAssumptions2)
{
  d_solver.setOption("incremental", "true");
  d_solver.setOption("produce-unsat-assumptions", "false");
  d_solver.checkSatAssuming(d_solver.mkFalse());
  ASSERT_THROW(d_solver.getUnsatAssumptions(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getUnsatAssumptions3)
{
  d_solver.setOption("incremental", "true");
  d_solver.setOption("produce-unsat-assumptions", "true");
  d_solver.checkSatAssuming(d_solver.mkFalse());
  ASSERT_NO_THROW(d_solver.getUnsatAssumptions());
  d_solver.checkSatAssuming(d_solver.mkTrue());
  ASSERT_THROW(d_solver.getUnsatAssumptions(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getUnsatCore1)
{
  d_solver.setOption("incremental", "false");
  d_solver.assertFormula(d_solver.mkFalse());
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getUnsatCore(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getUnsatCore2)
{
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-unsat-cores", "false");
  d_solver.assertFormula(d_solver.mkFalse());
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getUnsatCore(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getUnsatCoreAndProof)
{
  d_solver.setOption("incremental", "true");
  d_solver.setOption("produce-unsat-cores", "true");
  d_solver.setOption("produce-proofs", "true");

  Sort uSort = d_solver.mkUninterpretedSort("u");
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();
  Sort uToIntSort = d_solver.mkFunctionSort(uSort, intSort);
  Sort intPredSort = d_solver.mkFunctionSort(intSort, boolSort);
  std::vector<Term> uc;

  Term x = d_solver.mkConst(uSort, "x");
  Term y = d_solver.mkConst(uSort, "y");
  Term f = d_solver.mkConst(uToIntSort, "f");
  Term p = d_solver.mkConst(intPredSort, "p");
  Term zero = d_solver.mkInteger(0);
  Term one = d_solver.mkInteger(1);
  Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
  Term f_y = d_solver.mkTerm(APPLY_UF, f, y);
  Term sum = d_solver.mkTerm(ADD, f_x, f_y);
  Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
  Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);
  d_solver.assertFormula(d_solver.mkTerm(GT, zero, f_x));
  d_solver.assertFormula(d_solver.mkTerm(GT, zero, f_y));
  d_solver.assertFormula(d_solver.mkTerm(GT, sum, one));
  d_solver.assertFormula(p_0);
  d_solver.assertFormula(p_f_y.notTerm());
  ASSERT_TRUE(d_solver.checkSat().isUnsat());

  ASSERT_NO_THROW(uc = d_solver.getUnsatCore());
  ASSERT_FALSE(uc.empty());

  ASSERT_NO_THROW(d_solver.getProof());

  d_solver.resetAssertions();
  for (const auto& t : uc)
  {
    d_solver.assertFormula(t);
  }
  cvc5::api::Result res = d_solver.checkSat();
  ASSERT_TRUE(res.isUnsat());
  ASSERT_NO_THROW(d_solver.getProof());
}

TEST_F(TestApiBlackSolver, getDifficulty)
{
  d_solver.setOption("produce-difficulty", "true");
  // cannot ask before a check sat
  ASSERT_THROW(d_solver.getDifficulty(), CVC5ApiException);
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.getDifficulty());
}

TEST_F(TestApiBlackSolver, getDifficulty2)
{
  d_solver.checkSat();
  // option is not set
  ASSERT_THROW(d_solver.getDifficulty(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getDifficulty3)
{
  d_solver.setOption("produce-difficulty", "true");
  Sort intSort = d_solver.getIntegerSort();
  Term x = d_solver.mkConst(intSort, "x");
  Term zero = d_solver.mkInteger(0);
  Term ten = d_solver.mkInteger(10);
  Term f0 = d_solver.mkTerm(GEQ, x, ten);
  Term f1 = d_solver.mkTerm(GEQ, zero, x);
  d_solver.assertFormula(f0);
  d_solver.assertFormula(f1);
  d_solver.checkSat();
  std::map<Term, Term> dmap;
  ASSERT_NO_THROW(dmap = d_solver.getDifficulty());
  // difficulty should map assertions to integer values
  for (const std::pair<const Term, Term>& t : dmap)
  {
    ASSERT_TRUE(t.first == f0 || t.first == f1);
    ASSERT_TRUE(t.second.getKind() == CONST_RATIONAL);
  }
}

TEST_F(TestApiBlackSolver, getLearnedLiterals)
{
  d_solver.setOption("produce-learned-literals", "true");
  // cannot ask before a check sat
  ASSERT_THROW(d_solver.getLearnedLiterals(), CVC5ApiException);
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.getLearnedLiterals());
}

TEST_F(TestApiBlackSolver, getLearnedLiterals2)
{
  d_solver.setOption("produce-learned-literals", "true");
  Sort intSort = d_solver.getIntegerSort();
  Term x = d_solver.mkConst(intSort, "x");
  Term y = d_solver.mkConst(intSort, "y");
  Term zero = d_solver.mkInteger(0);
  Term ten = d_solver.mkInteger(10);
  Term f0 = d_solver.mkTerm(GEQ, x, ten);
  Term f1 = d_solver.mkTerm(
      OR, d_solver.mkTerm(GEQ, zero, x), d_solver.mkTerm(GEQ, y, zero));
  d_solver.assertFormula(f0);
  d_solver.assertFormula(f1);
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.getLearnedLiterals());
}

TEST_F(TestApiBlackSolver, getValue1)
{
  d_solver.setOption("produce-models", "false");
  Term t = d_solver.mkTrue();
  d_solver.assertFormula(t);
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getValue(t), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValue2)
{
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkFalse();
  d_solver.assertFormula(t);
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getValue(t), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValue3)
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
  Term sum = d_solver.mkTerm(ADD, f_x, f_y);
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
  ASSERT_THROW(slv.getValue(x), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getModelDomainElements)
{
  d_solver.setOption("produce-models", "true");
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Sort intSort = d_solver.getIntegerSort();
  Term x = d_solver.mkConst(uSort, "x");
  Term y = d_solver.mkConst(uSort, "y");
  Term z = d_solver.mkConst(uSort, "z");
  Term f = d_solver.mkTerm(DISTINCT, x, y, z);
  d_solver.assertFormula(f);
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.getModelDomainElements(uSort));
  ASSERT_TRUE(d_solver.getModelDomainElements(uSort).size() >= 3);
  ASSERT_THROW(d_solver.getModelDomainElements(intSort), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getModelDomainElements2)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("finite-model-find", "true");
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkVar(uSort, "x");
  Term y = d_solver.mkVar(uSort, "y");
  Term eq = d_solver.mkTerm(EQUAL, x, y);
  Term bvl = d_solver.mkTerm(VARIABLE_LIST, x, y);
  Term f = d_solver.mkTerm(FORALL, bvl, eq);
  d_solver.assertFormula(f);
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.getModelDomainElements(uSort));
  // a model for the above must interpret u as size 1
  ASSERT_TRUE(d_solver.getModelDomainElements(uSort).size() == 1);
}

TEST_F(TestApiBlackSolver, isModelCoreSymbol)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("model-cores", "simple");
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkConst(uSort, "x");
  Term y = d_solver.mkConst(uSort, "y");
  Term z = d_solver.mkConst(uSort, "z");
  Term zero = d_solver.mkInteger(0);
  Term f = d_solver.mkTerm(NOT, d_solver.mkTerm(EQUAL, x, y));
  d_solver.assertFormula(f);
  d_solver.checkSat();
  ASSERT_TRUE(d_solver.isModelCoreSymbol(x));
  ASSERT_TRUE(d_solver.isModelCoreSymbol(y));
  ASSERT_FALSE(d_solver.isModelCoreSymbol(z));
  ASSERT_THROW(d_solver.isModelCoreSymbol(zero), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getModel)
{
  d_solver.setOption("produce-models", "true");
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkConst(uSort, "x");
  Term y = d_solver.mkConst(uSort, "y");
  Term z = d_solver.mkConst(uSort, "z");
  Term f = d_solver.mkTerm(NOT, d_solver.mkTerm(EQUAL, x, y));
  d_solver.assertFormula(f);
  d_solver.checkSat();
  std::vector<Sort> sorts;
  sorts.push_back(uSort);
  std::vector<Term> terms;
  terms.push_back(x);
  terms.push_back(y);
  ASSERT_NO_THROW(d_solver.getModel(sorts, terms));
  Term null;
  terms.push_back(null);
  ASSERT_THROW(d_solver.getModel(sorts, terms), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getModel2)
{
  d_solver.setOption("produce-models", "true");
  std::vector<Sort> sorts;
  std::vector<Term> terms;
  ASSERT_THROW(d_solver.getModel(sorts, terms), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getModel3)
{
  d_solver.setOption("produce-models", "true");
  std::vector<Sort> sorts;
  std::vector<Term> terms;
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.getModel(sorts, terms));
  Sort integer = d_solver.getIntegerSort();
  sorts.push_back(integer);
  ASSERT_THROW(d_solver.getModel(sorts, terms), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getQuantifierElimination)
{
  Term x = d_solver.mkVar(d_solver.getBooleanSort(), "x");
  Term forall =
      d_solver.mkTerm(FORALL,
                      d_solver.mkTerm(VARIABLE_LIST, x),
                      d_solver.mkTerm(OR, x, d_solver.mkTerm(NOT, x)));
  ASSERT_THROW(d_solver.getQuantifierElimination(Term()), CVC5ApiException);
  ASSERT_THROW(d_solver.getQuantifierElimination(Solver().mkBoolean(false)),
               CVC5ApiException);
  ASSERT_NO_THROW(d_solver.getQuantifierElimination(forall));
}

TEST_F(TestApiBlackSolver, getQuantifierEliminationDisjunct)
{
  Term x = d_solver.mkVar(d_solver.getBooleanSort(), "x");
  Term forall =
      d_solver.mkTerm(FORALL,
                      d_solver.mkTerm(VARIABLE_LIST, x),
                      d_solver.mkTerm(OR, x, d_solver.mkTerm(NOT, x)));
  ASSERT_THROW(d_solver.getQuantifierEliminationDisjunct(Term()),
               CVC5ApiException);
  ASSERT_THROW(
      d_solver.getQuantifierEliminationDisjunct(Solver().mkBoolean(false)),
      CVC5ApiException);
  ASSERT_NO_THROW(d_solver.getQuantifierEliminationDisjunct(forall));
}

TEST_F(TestApiBlackSolver, declareSepHeap)
{
  d_solver.setLogic("ALL");
  d_solver.setOption("incremental", "false");
  Sort integer = d_solver.getIntegerSort();
  ASSERT_NO_THROW(d_solver.declareSepHeap(integer, integer));
  // cannot declare separation logic heap more than once
  ASSERT_THROW(d_solver.declareSepHeap(integer, integer), CVC5ApiException);
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
  solver->declareSepHeap(integer, integer);
  Term x = solver->mkConst(integer, "x");
  Term p = solver->mkConst(integer, "p");
  Term heap = solver->mkTerm(cvc5::api::Kind::SEP_PTO, p, x);
  solver->assertFormula(heap);
  Term nil = solver->mkSepNil(integer);
  solver->assertFormula(nil.eqTerm(solver->mkReal(5)));
  solver->checkSat();
}
}  // namespace

TEST_F(TestApiBlackSolver, getValueSepHeap1)
{
  d_solver.setLogic("QF_BV");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkTrue();
  d_solver.assertFormula(t);
  ASSERT_THROW(d_solver.getValueSepHeap(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValueSepHeap2)
{
  d_solver.setLogic("ALL");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "false");
  checkSimpleSeparationConstraints(&d_solver);
  ASSERT_THROW(d_solver.getValueSepHeap(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValueSepHeap3)
{
  d_solver.setLogic("ALL");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkFalse();
  d_solver.assertFormula(t);
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getValueSepHeap(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValueSepHeap4)
{
  d_solver.setLogic("ALL");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkTrue();
  d_solver.assertFormula(t);
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getValueSepHeap(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValueSepHeap5)
{
  d_solver.setLogic("ALL");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  checkSimpleSeparationConstraints(&d_solver);
  ASSERT_NO_THROW(d_solver.getValueSepHeap());
}

TEST_F(TestApiBlackSolver, getValueSepNil1)
{
  d_solver.setLogic("QF_BV");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkTrue();
  d_solver.assertFormula(t);
  ASSERT_THROW(d_solver.getValueSepNil(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValueSepNil2)
{
  d_solver.setLogic("ALL");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "false");
  checkSimpleSeparationConstraints(&d_solver);
  ASSERT_THROW(d_solver.getValueSepNil(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValueSepNil3)
{
  d_solver.setLogic("ALL");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkFalse();
  d_solver.assertFormula(t);
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getValueSepNil(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValueSepNil4)
{
  d_solver.setLogic("ALL");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkTrue();
  d_solver.assertFormula(t);
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getValueSepNil(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getValueSepNil5)
{
  d_solver.setLogic("ALL");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  checkSimpleSeparationConstraints(&d_solver);
  ASSERT_NO_THROW(d_solver.getValueSepNil());
}

TEST_F(TestApiBlackSolver, push1)
{
  d_solver.setOption("incremental", "true");
  ASSERT_NO_THROW(d_solver.push(1));
  ASSERT_THROW(d_solver.setOption("incremental", "false"), CVC5ApiException);
  ASSERT_THROW(d_solver.setOption("incremental", "true"), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, push2)
{
  d_solver.setOption("incremental", "false");
  ASSERT_THROW(d_solver.push(1), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, pop1)
{
  d_solver.setOption("incremental", "false");
  ASSERT_THROW(d_solver.pop(1), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, pop2)
{
  d_solver.setOption("incremental", "true");
  ASSERT_THROW(d_solver.pop(1), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, pop3)
{
  d_solver.setOption("incremental", "true");
  ASSERT_NO_THROW(d_solver.push(1));
  ASSERT_NO_THROW(d_solver.pop(1));
  ASSERT_THROW(d_solver.pop(1), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, blockModel1)
{
  d_solver.setOption("produce-models", "true");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_THROW(d_solver.blockModel(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, blockModel2)
{
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_THROW(d_solver.blockModel(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, blockModel3)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  ASSERT_THROW(d_solver.blockModel(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, blockModel4)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.blockModel());
}

TEST_F(TestApiBlackSolver, blockModelValues1)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_THROW(d_solver.blockModelValues({}), CVC5ApiException);
  ASSERT_THROW(d_solver.blockModelValues({Term()}), CVC5ApiException);
  ASSERT_THROW(d_solver.blockModelValues({Solver().mkBoolean(false)}),
               CVC5ApiException);
}

TEST_F(TestApiBlackSolver, blockModelValues2)
{
  d_solver.setOption("produce-models", "true");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.blockModelValues({x}));
}

TEST_F(TestApiBlackSolver, blockModelValues3)
{
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_THROW(d_solver.blockModelValues({x}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, blockModelValues4)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  ASSERT_THROW(d_solver.blockModelValues({x}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, blockModelValues5)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.blockModelValues({x}));
}

TEST_F(TestApiBlackSolver, setInfo)
{
  ASSERT_THROW(d_solver.setInfo("cvc5-lagic", "QF_BV"), CVC5ApiException);
  ASSERT_THROW(d_solver.setInfo("cvc2-logic", "QF_BV"), CVC5ApiException);
  ASSERT_THROW(d_solver.setInfo("cvc5-logic", "asdf"), CVC5ApiException);

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
  ASSERT_THROW(d_solver.setInfo("smt-lib-version", ".0"), CVC5ApiException);

  ASSERT_NO_THROW(d_solver.setInfo("status", "sat"));
  ASSERT_NO_THROW(d_solver.setInfo("status", "unsat"));
  ASSERT_NO_THROW(d_solver.setInfo("status", "unknown"));
  ASSERT_THROW(d_solver.setInfo("status", "asdf"), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, simplify)
{
  ASSERT_THROW(d_solver.simplify(Term()), CVC5ApiException);

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
  ASSERT_NE(d_solver.mkTrue(), x_eq_x);
  ASSERT_EQ(d_solver.mkTrue(), d_solver.simplify(x_eq_x));
  Term x_eq_b = d_solver.mkTerm(EQUAL, x, b);
  ASSERT_NO_THROW(d_solver.simplify(x_eq_b));
  ASSERT_NE(d_solver.mkTrue(), x_eq_b);
  ASSERT_NE(d_solver.mkTrue(), d_solver.simplify(x_eq_b));
  Solver slv;
  ASSERT_THROW(slv.simplify(x), CVC5ApiException);

  Term i1 = d_solver.mkConst(d_solver.getIntegerSort(), "i1");
  ASSERT_NO_THROW(d_solver.simplify(i1));
  Term i2 = d_solver.mkTerm(MULT, i1, d_solver.mkInteger("23"));
  ASSERT_NO_THROW(d_solver.simplify(i2));
  ASSERT_NE(i1, i2);
  ASSERT_NE(i1, d_solver.simplify(i2));
  Term i3 = d_solver.mkTerm(ADD, i1, d_solver.mkInteger(0));
  ASSERT_NO_THROW(d_solver.simplify(i3));
  ASSERT_NE(i1, i3);
  ASSERT_EQ(i1, d_solver.simplify(i3));

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

TEST_F(TestApiBlackSolver, assertFormula)
{
  ASSERT_NO_THROW(d_solver.assertFormula(d_solver.mkTrue()));
  ASSERT_THROW(d_solver.assertFormula(Term()), CVC5ApiException);
  Solver slv;
  ASSERT_THROW(slv.assertFormula(d_solver.mkTrue()), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, checkEntailed)
{
  d_solver.setOption("incremental", "false");
  ASSERT_NO_THROW(d_solver.checkEntailed(d_solver.mkTrue()));
  ASSERT_THROW(d_solver.checkEntailed(d_solver.mkTrue()), CVC5ApiException);
  Solver slv;
  ASSERT_THROW(slv.checkEntailed(d_solver.mkTrue()), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, checkEntailed1)
{
  Sort boolSort = d_solver.getBooleanSort();
  Term x = d_solver.mkConst(boolSort, "x");
  Term y = d_solver.mkConst(boolSort, "y");
  Term z = d_solver.mkTerm(AND, x, y);
  d_solver.setOption("incremental", "true");
  ASSERT_NO_THROW(d_solver.checkEntailed(d_solver.mkTrue()));
  ASSERT_THROW(d_solver.checkEntailed(Term()), CVC5ApiException);
  ASSERT_NO_THROW(d_solver.checkEntailed(d_solver.mkTrue()));
  ASSERT_NO_THROW(d_solver.checkEntailed(z));
  Solver slv;
  ASSERT_THROW(slv.checkEntailed(d_solver.mkTrue()), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, checkEntailed2)
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
  Term sum = d_solver.mkTerm(ADD, f_x, f_y);
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
  ASSERT_THROW(d_solver.checkEntailed(n), CVC5ApiException);
  ASSERT_THROW(d_solver.checkEntailed({n, d_solver.mkTerm(DISTINCT, x, y)}),
               CVC5ApiException);
  Solver slv;
  ASSERT_THROW(slv.checkEntailed(d_solver.mkTrue()), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, checkSat)
{
  d_solver.setOption("incremental", "false");
  ASSERT_NO_THROW(d_solver.checkSat());
  ASSERT_THROW(d_solver.checkSat(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, checkSatAssuming)
{
  d_solver.setOption("incremental", "false");
  ASSERT_NO_THROW(d_solver.checkSatAssuming(d_solver.mkTrue()));
  ASSERT_THROW(d_solver.checkSatAssuming(d_solver.mkTrue()), CVC5ApiException);
  Solver slv;
  ASSERT_THROW(slv.checkSatAssuming(d_solver.mkTrue()), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, checkSatAssuming1)
{
  Sort boolSort = d_solver.getBooleanSort();
  Term x = d_solver.mkConst(boolSort, "x");
  Term y = d_solver.mkConst(boolSort, "y");
  Term z = d_solver.mkTerm(AND, x, y);
  d_solver.setOption("incremental", "true");
  ASSERT_NO_THROW(d_solver.checkSatAssuming(d_solver.mkTrue()));
  ASSERT_THROW(d_solver.checkSatAssuming(Term()), CVC5ApiException);
  ASSERT_NO_THROW(d_solver.checkSatAssuming(d_solver.mkTrue()));
  ASSERT_NO_THROW(d_solver.checkSatAssuming(z));
  Solver slv;
  ASSERT_THROW(slv.checkSatAssuming(d_solver.mkTrue()), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, checkSatAssuming2)
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
  Term sum = d_solver.mkTerm(ADD, f_x, f_y);
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
  ASSERT_THROW(d_solver.checkSatAssuming(n), CVC5ApiException);
  ASSERT_THROW(d_solver.checkSatAssuming({n, d_solver.mkTerm(DISTINCT, x, y)}),
               CVC5ApiException);
  Solver slv;
  ASSERT_THROW(slv.checkSatAssuming(d_solver.mkTrue()), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, setLogic)
{
  ASSERT_NO_THROW(d_solver.setLogic("AUFLIRA"));
  ASSERT_THROW(d_solver.setLogic("AF_BV"), CVC5ApiException);
  d_solver.assertFormula(d_solver.mkTrue());
  ASSERT_THROW(d_solver.setLogic("AUFLIRA"), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, setOption)
{
  ASSERT_NO_THROW(d_solver.setOption("bv-sat-solver", "minisat"));
  ASSERT_THROW(d_solver.setOption("bv-sat-solver", "1"), CVC5ApiException);
  d_solver.assertFormula(d_solver.mkTrue());
  ASSERT_THROW(d_solver.setOption("bv-sat-solver", "minisat"),
               CVC5ApiException);
}

TEST_F(TestApiBlackSolver, resetAssertions)
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

TEST_F(TestApiBlackSolver, mkSygusVar)
{
  Sort boolSort = d_solver.getBooleanSort();
  Sort intSort = d_solver.getIntegerSort();
  Sort funSort = d_solver.mkFunctionSort(intSort, boolSort);

  ASSERT_NO_THROW(d_solver.mkSygusVar(boolSort));
  ASSERT_NO_THROW(d_solver.mkSygusVar(funSort));
  ASSERT_NO_THROW(d_solver.mkSygusVar(boolSort, std::string("b")));
  ASSERT_NO_THROW(d_solver.mkSygusVar(funSort, ""));
  ASSERT_THROW(d_solver.mkSygusVar(Sort()), CVC5ApiException);
  ASSERT_THROW(d_solver.mkSygusVar(d_solver.getNullSort(), "a"),
               CVC5ApiException);
  Solver slv;
  ASSERT_THROW(slv.mkSygusVar(boolSort), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, mkSygusGrammar)
{
  Term nullTerm;
  Term boolTerm = d_solver.mkBoolean(true);
  Term boolVar = d_solver.mkVar(d_solver.getBooleanSort());
  Term intVar = d_solver.mkVar(d_solver.getIntegerSort());

  ASSERT_NO_THROW(d_solver.mkSygusGrammar({}, {intVar}));
  ASSERT_NO_THROW(d_solver.mkSygusGrammar({boolVar}, {intVar}));
  ASSERT_THROW(d_solver.mkSygusGrammar({}, {}), CVC5ApiException);
  ASSERT_THROW(d_solver.mkSygusGrammar({}, {nullTerm}), CVC5ApiException);
  ASSERT_THROW(d_solver.mkSygusGrammar({}, {boolTerm}), CVC5ApiException);
  ASSERT_THROW(d_solver.mkSygusGrammar({boolTerm}, {intVar}), CVC5ApiException);
  Solver slv;
  Term boolVar2 = slv.mkVar(slv.getBooleanSort());
  Term intVar2 = slv.mkVar(slv.getIntegerSort());
  ASSERT_NO_THROW(slv.mkSygusGrammar({boolVar2}, {intVar2}));
  ASSERT_THROW(slv.mkSygusGrammar({boolVar}, {intVar2}), CVC5ApiException);
  ASSERT_THROW(slv.mkSygusGrammar({boolVar2}, {intVar}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, synthFun)
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

  ASSERT_THROW(d_solver.synthFun("f3", {nullTerm}, boolean), CVC5ApiException);
  ASSERT_THROW(d_solver.synthFun("f4", {}, null), CVC5ApiException);
  ASSERT_THROW(d_solver.synthFun("f6", {x}, boolean, g2), CVC5ApiException);
  Solver slv;
  Term x2 = slv.mkVar(slv.getBooleanSort());
  ASSERT_NO_THROW(slv.synthFun("f1", {x2}, slv.getBooleanSort()));
  ASSERT_THROW(slv.synthFun("", {}, d_solver.getBooleanSort()),
               CVC5ApiException);
  ASSERT_THROW(slv.synthFun("f1", {x}, d_solver.getBooleanSort()),
               CVC5ApiException);
}

TEST_F(TestApiBlackSolver, synthInv)
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

  ASSERT_THROW(d_solver.synthInv("i3", {nullTerm}), CVC5ApiException);
  ASSERT_THROW(d_solver.synthInv("i4", {x}, g2), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, addSygusConstraint)
{
  Term nullTerm;
  Term boolTerm = d_solver.mkBoolean(true);
  Term intTerm = d_solver.mkInteger(1);

  ASSERT_NO_THROW(d_solver.addSygusConstraint(boolTerm));
  ASSERT_THROW(d_solver.addSygusConstraint(nullTerm), CVC5ApiException);
  ASSERT_THROW(d_solver.addSygusConstraint(intTerm), CVC5ApiException);

  Solver slv;
  ASSERT_THROW(slv.addSygusConstraint(boolTerm), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, addSygusAssume)
{
  Term nullTerm;
  Term boolTerm = d_solver.mkBoolean(false);
  Term intTerm = d_solver.mkInteger(1);

  ASSERT_NO_THROW(d_solver.addSygusAssume(boolTerm));
  ASSERT_THROW(d_solver.addSygusAssume(nullTerm), CVC5ApiException);
  ASSERT_THROW(d_solver.addSygusAssume(intTerm), CVC5ApiException);

  Solver slv;
  ASSERT_THROW(slv.addSygusAssume(boolTerm), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, addSygusInvConstraint)
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
               CVC5ApiException);
  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, nullTerm, trans, post),
               CVC5ApiException);
  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, pre, nullTerm, post),
               CVC5ApiException);
  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, pre, trans, nullTerm),
               CVC5ApiException);

  ASSERT_THROW(d_solver.addSygusInvConstraint(intTerm, pre, trans, post),
               CVC5ApiException);

  ASSERT_THROW(d_solver.addSygusInvConstraint(inv1, pre, trans, post),
               CVC5ApiException);

  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, trans, trans, post),
               CVC5ApiException);

  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, pre, intTerm, post),
               CVC5ApiException);
  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, pre, pre, post),
               CVC5ApiException);
  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, pre, trans1, post),
               CVC5ApiException);
  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, pre, trans2, post),
               CVC5ApiException);
  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, pre, trans3, post),
               CVC5ApiException);

  ASSERT_THROW(d_solver.addSygusInvConstraint(inv, pre, trans, trans),
               CVC5ApiException);
  Solver slv;
  Sort boolean2 = slv.getBooleanSort();
  Sort real2 = slv.getRealSort();
  Term inv22 = slv.declareFun("inv", {real2}, boolean2);
  Term pre22 = slv.declareFun("pre", {real2}, boolean2);
  Term trans22 = slv.declareFun("trans", {real2, real2}, boolean2);
  Term post22 = slv.declareFun("post", {real2}, boolean2);
  ASSERT_NO_THROW(slv.addSygusInvConstraint(inv22, pre22, trans22, post22));
  ASSERT_THROW(slv.addSygusInvConstraint(inv, pre22, trans22, post22),
               CVC5ApiException);
  ASSERT_THROW(slv.addSygusInvConstraint(inv22, pre, trans22, post22),
               CVC5ApiException);
  ASSERT_THROW(slv.addSygusInvConstraint(inv22, pre22, trans, post22),
               CVC5ApiException);
  ASSERT_THROW(slv.addSygusInvConstraint(inv22, pre22, trans22, post),
               CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getSynthSolution)
{
  d_solver.setOption("lang", "sygus2");
  d_solver.setOption("incremental", "false");

  Term nullTerm;
  Term x = d_solver.mkBoolean(false);
  Term f = d_solver.synthFun("f", {}, d_solver.getBooleanSort());

  ASSERT_THROW(d_solver.getSynthSolution(f), CVC5ApiException);

  d_solver.checkSynth();

  ASSERT_NO_THROW(d_solver.getSynthSolution(f));
  ASSERT_NO_THROW(d_solver.getSynthSolution(f));

  ASSERT_THROW(d_solver.getSynthSolution(nullTerm), CVC5ApiException);
  ASSERT_THROW(d_solver.getSynthSolution(x), CVC5ApiException);

  Solver slv;
  ASSERT_THROW(slv.getSynthSolution(f), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, getSynthSolutions)
{
  d_solver.setOption("lang", "sygus2");
  d_solver.setOption("incremental", "false");

  Term nullTerm;
  Term x = d_solver.mkBoolean(false);
  Term f = d_solver.synthFun("f", {}, d_solver.getBooleanSort());

  ASSERT_THROW(d_solver.getSynthSolutions({}), CVC5ApiException);
  ASSERT_THROW(d_solver.getSynthSolutions({f}), CVC5ApiException);

  d_solver.checkSynth();

  ASSERT_NO_THROW(d_solver.getSynthSolutions({f}));
  ASSERT_NO_THROW(d_solver.getSynthSolutions({f, f}));

  ASSERT_THROW(d_solver.getSynthSolutions({}), CVC5ApiException);
  ASSERT_THROW(d_solver.getSynthSolutions({nullTerm}), CVC5ApiException);
  ASSERT_THROW(d_solver.getSynthSolutions({x}), CVC5ApiException);

  Solver slv;
  ASSERT_THROW(slv.getSynthSolutions({x}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, checkSynthNext)
{
  d_solver.setOption("lang", "sygus2");
  d_solver.setOption("incremental", "true");
  Term f = d_solver.synthFun("f", {}, d_solver.getBooleanSort());

  d_solver.checkSynth();
  ASSERT_NO_THROW(d_solver.getSynthSolutions({f}));
  d_solver.checkSynthNext();
  ASSERT_NO_THROW(d_solver.getSynthSolutions({f}));
}

TEST_F(TestApiBlackSolver, checkSynthNext2)
{
  d_solver.setOption("lang", "sygus2");
  d_solver.setOption("incremental", "false");
  Term f = d_solver.synthFun("f", {}, d_solver.getBooleanSort());

  d_solver.checkSynth();
  ASSERT_THROW(d_solver.checkSynthNext(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, checkSynthNext3)
{
  d_solver.setOption("lang", "sygus2");
  d_solver.setOption("incremental", "true");
  Term f = d_solver.synthFun("f", {}, d_solver.getBooleanSort());

  ASSERT_THROW(d_solver.checkSynthNext(), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, tupleProject)
{
  std::vector<Sort> sorts = {d_solver.getBooleanSort(),
                             d_solver.getIntegerSort(),
                             d_solver.getStringSort(),
                             d_solver.mkSetSort(d_solver.getStringSort())};
  std::vector<Term> elements = {
      d_solver.mkBoolean(true),
      d_solver.mkInteger(3),
      d_solver.mkString("C"),
      d_solver.mkTerm(SET_SINGLETON, d_solver.mkString("Z"))};

  Term tuple = d_solver.mkTuple(sorts, elements);

  std::vector<uint32_t> indices1 = {};
  std::vector<uint32_t> indices2 = {0};
  std::vector<uint32_t> indices3 = {0, 1};
  std::vector<uint32_t> indices4 = {0, 0, 2, 2, 3, 3, 0};
  std::vector<uint32_t> indices5 = {4};
  std::vector<uint32_t> indices6 = {0, 4};

  ASSERT_NO_THROW(
      d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices1), tuple));
  ASSERT_NO_THROW(
      d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices2), tuple));
  ASSERT_NO_THROW(
      d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices3), tuple));
  ASSERT_NO_THROW(
      d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices4), tuple));

  ASSERT_THROW(d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices5), tuple),
               CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices6), tuple),
               CVC5ApiException);

  std::vector<uint32_t> indices = {0, 3, 2, 0, 1, 2};

  Op op = d_solver.mkOp(TUPLE_PROJECT, indices);
  Term projection = d_solver.mkTerm(op, tuple);

  Datatype datatype = tuple.getSort().getDatatype();
  DatatypeConstructor constructor = datatype[0];

  for (size_t i = 0; i < indices.size(); i++)
  {
    Term selectorTerm = constructor[indices[i]].getSelectorTerm();
    Term selectedTerm = d_solver.mkTerm(APPLY_SELECTOR, selectorTerm, tuple);
    Term simplifiedTerm = d_solver.simplify(selectedTerm);
    ASSERT_EQ(elements[indices[i]], simplifiedTerm);
  }

  ASSERT_EQ(
      "((_ tuple_project 0 3 2 0 1 2) (tuple true 3 \"C\" (set.singleton "
      "\"Z\")))",
      projection.toString());
}

TEST_F(TestApiBlackSolver, Output)
{
  ASSERT_THROW(d_solver.isOutputOn("foo-invalid"), CVC5ApiException);
  ASSERT_THROW(d_solver.getOutput("foo-invalid"), CVC5ApiException);
  ASSERT_FALSE(d_solver.isOutputOn("inst"));
  ASSERT_EQ(cvc5::null_os.rdbuf(), d_solver.getOutput("inst").rdbuf());
  d_solver.setOption("output", "inst");
  ASSERT_TRUE(d_solver.isOutputOn("inst"));
  ASSERT_NE(cvc5::null_os.rdbuf(), d_solver.getOutput("inst").rdbuf());
}

TEST_F(TestApiBlackSolver, issue7000)
{
  Sort s1 = d_solver.getIntegerSort();
  Sort s2 = d_solver.mkFunctionSort(s1, s1);
  Sort s3 = d_solver.getRealSort();
  Term t4 = d_solver.mkPi();
  Term t7 = d_solver.mkConst(s3, "_x5");
  Term t37 = d_solver.mkConst(s2, "_x32");
  Term t59 = d_solver.mkConst(s2, "_x51");
  Term t72 = d_solver.mkTerm(EQUAL, t37, t59);
  Term t74 = d_solver.mkTerm(GT, t4, t7);
  // throws logic exception since logic is not higher order by default
  ASSERT_THROW(d_solver.checkEntailed({t72, t74, t72, t72}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, issue5893)
{
  Solver slv;
  Sort bvsort4 = d_solver.mkBitVectorSort(4);
  Sort bvsort8 = d_solver.mkBitVectorSort(8);
  Sort arrsort = d_solver.mkArraySort(bvsort4, bvsort8);
  Term arr = d_solver.mkConst(arrsort, "arr");
  Term idx = d_solver.mkConst(bvsort4, "idx");
  Term ten = d_solver.mkBitVector(8, "10", 10);
  Term sel = d_solver.mkTerm(SELECT, arr, idx);
  Term distinct = d_solver.mkTerm(DISTINCT, sel, ten);
  ASSERT_NO_FATAL_FAILURE(distinct.getOp());
}

TEST_F(TestApiBlackSolver, proj_issue308)
{
  Solver slv;
  slv.setOption("check-proofs", "true");
  Sort s1 = slv.getBooleanSort();
  Term t1 = slv.mkConst(s1, "_x0");
  Term t2 = slv.mkTerm(Kind::XOR, t1, t1);
  slv.checkSatAssuming({t2});
  auto unsat_core = slv.getUnsatCore();
  ASSERT_FALSE(unsat_core.empty());
}

TEST_F(TestApiBlackSolver, proj_issue373)
{
  Sort s1 = d_solver.getRealSort();

  DatatypeConstructorDecl ctor13 = d_solver.mkDatatypeConstructorDecl("_x115");
  ctor13.addSelector("_x109", s1);
  Sort s4 = d_solver.declareDatatype("_x86", {ctor13});

  Term t452 = d_solver.mkVar(s1, "_x281");
  Term bvl = d_solver.mkTerm(d_solver.mkOp(VARIABLE_LIST), {t452});
  Term acons =
      d_solver.mkTerm(d_solver.mkOp(APPLY_CONSTRUCTOR),
                      {s4.getDatatype().getConstructorTerm("_x115"), t452});
  // type exception
  ASSERT_THROW(
      d_solver.mkTerm(d_solver.mkOp(APPLY_CONSTRUCTOR), {bvl, acons, t452}),
      CVC5ApiException);
}

TEST_F(TestApiBlackSolver, proj_issue378)
{
  DatatypeDecl dtdecl;
  DatatypeConstructorDecl cdecl;

  Sort s1 = d_solver.getBooleanSort();

  dtdecl = d_solver.mkDatatypeDecl("_x0");
  cdecl = d_solver.mkDatatypeConstructorDecl("_x6");
  cdecl.addSelector("_x1", s1);
  dtdecl.addConstructor(cdecl);
  Sort s2 = d_solver.mkDatatypeSort(dtdecl);

  dtdecl = d_solver.mkDatatypeDecl("_x36");
  cdecl = d_solver.mkDatatypeConstructorDecl("_x42");
  cdecl.addSelector("_x37", s1);
  dtdecl.addConstructor(cdecl);
  Sort s4 = d_solver.mkDatatypeSort(dtdecl);

  Term t1 = d_solver.mkConst(s1, "_x53");
  Term t4 = d_solver.mkConst(s4, "_x56");
  Term t7 = d_solver.mkConst(s2, "_x58");

  Sort sp = d_solver.mkParamSort("_x178");
  dtdecl = d_solver.mkDatatypeDecl("_x176", sp);
  cdecl = d_solver.mkDatatypeConstructorDecl("_x184");
  cdecl.addSelector("_x180", s2);
  dtdecl.addConstructor(cdecl);
  cdecl = d_solver.mkDatatypeConstructorDecl("_x186");
  cdecl.addSelector("_x185", sp);
  dtdecl.addConstructor(cdecl);
  Sort s7 = d_solver.mkDatatypeSort(dtdecl);
  Sort s9 = s7.instantiate({s2});
  Term t1507 = d_solver.mkTerm(
      APPLY_CONSTRUCTOR, s9.getDatatype().getConstructorTerm("_x184"), t7);
  ASSERT_NO_THROW(d_solver.mkTerm(
      APPLY_UPDATER,
      s9.getDatatype().getConstructor("_x186").getSelectorTerm("_x185"),
      t1507,
      t7));
}

TEST_F(TestApiBlackSolver, proj_issue379)
{
  Sort bsort = d_solver.getBooleanSort();
  Sort psort = d_solver.mkParamSort("_x1");
  DatatypeConstructorDecl cdecl;
  DatatypeDecl dtdecl = d_solver.mkDatatypeDecl("x_0", psort);
  cdecl = d_solver.mkDatatypeConstructorDecl("_x8");
  cdecl.addSelector("_x7", bsort);
  dtdecl.addConstructor(cdecl);
  cdecl = d_solver.mkDatatypeConstructorDecl("_x6");
  cdecl.addSelector("_x2", psort);
  cdecl.addSelectorSelf("_x3");
  cdecl.addSelector("_x4", psort);
  cdecl.addSelector("_x5", bsort);
  Sort s2 = d_solver.mkDatatypeSort(dtdecl);
  Sort s6 = s2.instantiate({bsort});
  Term t317 = d_solver.mkConst(bsort, "_x345");
  Term t843 = d_solver.mkConst(s6, "_x346");
  Term t879 = d_solver.mkTerm(APPLY_UPDATER,
                              t843.getSort()
                                  .getDatatype()
                                  .getConstructor("_x8")
                                  .getSelector("_x7")
                                  .getUpdaterTerm(),
                              t843,
                              t317);
  ASSERT_EQ(t879.getSort(), s6);
}

TEST_F(TestApiBlackSolver, getDatatypeArity)
{
  DatatypeConstructorDecl ctor1 = d_solver.mkDatatypeConstructorDecl("_x21");
  DatatypeConstructorDecl ctor2 = d_solver.mkDatatypeConstructorDecl("_x31");
  Sort s3 = d_solver.declareDatatype(std::string("_x17"), {ctor1, ctor2});
  ASSERT_EQ(s3.getDatatypeArity(), 0);
}

TEST_F(TestApiBlackSolver, proj_issue381)
{
  Sort s1 = d_solver.getBooleanSort();

  Sort psort = d_solver.mkParamSort("_x9");
  DatatypeDecl dtdecl = d_solver.mkDatatypeDecl("_x8", psort);
  DatatypeConstructorDecl ctor = d_solver.mkDatatypeConstructorDecl("_x22");
  ctor.addSelector("_x19", s1);
  dtdecl.addConstructor(ctor);
  Sort s3 = d_solver.mkDatatypeSort(dtdecl);
  Sort s6 = s3.instantiate({s1});
  Term t26 = d_solver.mkConst(s6, "_x63");
  Term t5 = d_solver.mkTrue();
  Term t187 = d_solver.mkTerm(APPLY_UPDATER,
                              t26.getSort()
                                  .getDatatype()
                                  .getConstructor("_x22")
                                  .getSelector("_x19")
                                  .getUpdaterTerm(),
                              t26,
                              t5);
  ASSERT_NO_THROW(d_solver.simplify(t187));
}


TEST_F(TestApiBlackSolver, proj_issue382)
{
  Sort s1 = d_solver.getBooleanSort();
  Sort psort = d_solver.mkParamSort("_x1");
  DatatypeConstructorDecl ctor = d_solver.mkDatatypeConstructorDecl("_x20");
  ctor.addSelector("_x19", psort);
  DatatypeDecl dtdecl = d_solver.mkDatatypeDecl("_x0", psort);
  dtdecl.addConstructor(ctor);
  Sort s2 = d_solver.mkDatatypeSort(dtdecl);
  Sort s6 = s2.instantiate({s1});
  Term t13 = d_solver.mkVar(s6, "_x58");
  Term t18 = d_solver.mkConst(s6, "_x63");
  Term t52 = d_solver.mkVar(s6, "_x70");
  Term t53 = d_solver.mkTerm(
      MATCH_BIND_CASE, d_solver.mkTerm(VARIABLE_LIST, t52), t52, t18);
  Term t73 = d_solver.mkVar(s1, "_x78");
  Term t81 =
      d_solver.mkTerm(MATCH_BIND_CASE,
                      d_solver.mkTerm(VARIABLE_LIST, t73),
                      d_solver.mkTerm(APPLY_CONSTRUCTOR,
                                      s6.getDatatype()
                                          .getConstructor("_x20")
                                          .getInstantiatedConstructorTerm(s6),
                                      t73),
                      t18);
  Term t82 = d_solver.mkTerm(MATCH, {t13, t53, t53, t53, t81});
  Term t325 = d_solver.mkTerm(
      APPLY_SELECTOR,
      t82.getSort().getDatatype().getSelector("_x19").getSelectorTerm(),
      t82);
  ASSERT_NO_THROW(d_solver.simplify(t325));
}

TEST_F(TestApiBlackSolver, proj_issue383)
{
  d_solver.setOption("produce-models", "true");

  Sort s1 = d_solver.getBooleanSort();

  DatatypeConstructorDecl ctordecl = d_solver.mkDatatypeConstructorDecl("_x5");
  DatatypeDecl dtdecl = d_solver.mkDatatypeDecl("_x0");
  dtdecl.addConstructor(ctordecl);
  Sort s2 = d_solver.mkDatatypeSort(dtdecl);

  ctordecl = d_solver.mkDatatypeConstructorDecl("_x23");
  ctordecl.addSelectorSelf("_x21");
  dtdecl = d_solver.mkDatatypeDecl("_x12");
  dtdecl.addConstructor(ctordecl);
  Sort s4 = d_solver.mkDatatypeSort(dtdecl);
  ASSERT_FALSE(s4.getDatatype().isWellFounded());

  Term t3 = d_solver.mkConst(s4, "_x25");
  Term t13 = d_solver.mkConst(s1, "_x34");

  d_solver.checkEntailed(t13);
  ASSERT_THROW(d_solver.getValue(t3), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, proj_issue386)
{
  Sort s1 = d_solver.getBooleanSort();
  Sort p1 = d_solver.mkParamSort("_p1");
  Sort p2 = d_solver.mkParamSort("_p2");
  DatatypeDecl dtdecl = d_solver.mkDatatypeDecl("_x0", {p1, p2});
  DatatypeConstructorDecl ctordecl = d_solver.mkDatatypeConstructorDecl("_x1");
  ctordecl.addSelector("_x2", p1);
  dtdecl.addConstructor(ctordecl);
  Sort s2 = d_solver.mkDatatypeSort(dtdecl);
  ASSERT_THROW(s2.instantiate({s1}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, proj_issue414)
{
  Solver slv;
  Sort s2 = slv.getRealSort();
  Term t1 = slv.mkConst(s2, "_x0");
  Term t16 = slv.mkTerm(Kind::PI);
  Term t53 = slv.mkTerm(Kind::SUB, {t1, t16});
  Term t54 = slv.mkTerm(Kind::SECANT, {t53});
  ASSERT_NO_THROW(slv.simplify(t54));
}

TEST_F(TestApiBlackSolver, proj_issue420)
{
  Solver slv;
  slv.setOption("strings-exp", "true");
  slv.setOption("produce-models", "true");
  slv.setOption("produce-unsat-cores", "true");
  Sort s2 = slv.getRealSort();
  Sort s3 = slv.mkUninterpretedSort("_u0");
  DatatypeDecl _dt1 = slv.mkDatatypeDecl("_dt1", {});
  DatatypeConstructorDecl _cons16 = slv.mkDatatypeConstructorDecl("_cons16");
  _cons16.addSelector("_sel13", s3);
  _dt1.addConstructor(_cons16);
  std::vector<Sort> _s4 = slv.mkDatatypeSorts({_dt1});
  Sort s4 = _s4[0];
  Sort s5 = slv.mkSequenceSort(s2);
  Term t3 = slv.mkConst(s5, "_x18");
  Term t7 = slv.mkConst(s4, "_x22");
  Term t13 = slv.mkTerm(Kind::DT_SIZE, {t7});
  Term t53 = slv.mkTerm(Kind::SEQ_NTH, {t3, t13});
  ASSERT_NO_THROW(slv.checkSat());
  ASSERT_NO_THROW(slv.blockModelValues({t53, t7}));
  ASSERT_NO_THROW(slv.checkSat());
}

TEST_F(TestApiBlackSolver, proj_issue440)
{
  Solver slv;
  slv.setLogic("QF_ALL");
  slv.setOption("global-negate", "true");
  slv.setOption("produce-unsat-cores", "true");
  Sort s1 = slv.getBooleanSort();
  Term t9 = slv.mkBoolean(true);
  Term t109 = slv.mkTerm(Kind::NOT, {t9});
  // should throw an option exception
  ASSERT_THROW(slv.checkSatAssuming({t109}), CVC5ApiException);
}

TEST_F(TestApiBlackSolver, proj_issue434)
{
  Solver slv;
  slv.setOption("dump-difficulty", "true");
  slv.setOption("debug-check-models", "true");
  Sort s1 = slv.mkUninterpretedSort("_u0");
  Sort s2 = slv.mkUninterpretedSort("_u1");
  Sort s3 = slv.mkUninterpretedSort("_u2");
  Sort s4 = slv.getBooleanSort();
  Term t1 = slv.mkConst(s1, "_x3");
  Term t3 = slv.mkConst(s3, "_x5");
  Term t15 = slv.mkConst(s1, "_x17");
  Term t26 = slv.mkBoolean(false);
  Term t60 = slv.mkVar(s4, "_f29_1");
  Term t73 = slv.defineFun("_f29", {t60}, t60.getSort(), t60);
  Term t123 = slv.mkVar(s4, "_f31_0");
  Term t135 = slv.defineFun("_f31", {t123}, t123.getSort(), t123);
  Term t506 = slv.mkVar(s1, "_f37_0");
  Term t507 = slv.mkVar(s4, "_f37_1");
  Term t510 = slv.mkTerm(Kind::APPLY_UF, {t73, t507});
  Term t530 = slv.defineFun("_f37", {t507}, t510.getSort(), t510);
  Term t559 = slv.mkTerm(Kind::DISTINCT, {t15, t1});
  Term t631 = slv.mkTerm(Kind::XOR, {t559, t26});
  Term t632 = slv.mkTerm(Kind::APPLY_UF, {t135, t631});
  Term t715 = slv.mkVar(s4, "_f40_0");
  Term t721 = slv.mkTerm(Kind::APPLY_UF, {t530, t715});
  Term t722 = slv.mkTerm(Kind::APPLY_UF, {t530, t721});
  Term t731 = slv.defineFun("_f40", {t715}, t722.getSort(), t722);
  Term t1014 = slv.mkVar(s4, "_f45_0");
  Term t1034 = slv.mkTerm(Kind::DISTINCT, {t510, t510});
  Term t1035 = slv.mkTerm(Kind::XOR, {t1034, t632});
  Term t1037 = slv.mkTerm(Kind::APPLY_UF, {t135, t1035});
  Term t1039 = slv.mkTerm(Kind::APPLY_UF, {t731, t1037});
  Term t1040 = slv.defineFun("_f45", {t1014}, t1039.getSort(), t1039);
  Term t1072 = slv.mkTerm(Kind::APPLY_UF, {t1040, t510});
  Term t1073 = slv.mkTerm(Kind::APPLY_UF, {t73, t1072});
  // the query has free variables, and should throw an exception
  ASSERT_THROW(slv.checkSatAssuming({t1073, t510}), CVC5ApiException);
}
  
TEST_F(TestApiBlackSolver, proj_issue436)
{
  Solver slv;
  slv.setOption("produce-abducts", "true");
  slv.setOption("solve-bv-as-int", "sum");
  Sort s8 = slv.mkBitVectorSort(68);
  Term t17 = slv.mkConst(s8, "_x6");
  Term t23;
  {
    uint32_t bw = s8.getBitVectorSize();
    t23 = slv.mkBitVector(bw, 1);
  }
  Term t33 = slv.mkTerm(Kind::BITVECTOR_ULT, {t17, t23});
  Term abduct;
  // solve-bv-as-int is incompatible with get-abduct
  ASSERT_THROW(slv.getAbduct(t33, abduct), CVC5ApiException);
}
  
TEST_F(TestApiBlackSolver, proj_issue431)
{
  Solver slv;
  slv.setOption("produce-models", "true");
  slv.setOption("produce-unsat-assumptions", "true");
  slv.setOption("produce-assertions", "true");
  Sort s1 = slv.getStringSort();
  Sort s3 = slv.getIntegerSort();
  Sort s7 = slv.mkArraySort(s1, s3);
  Term t3 = slv.mkConst(s1, "_x2");
  Term t57 = slv.mkVar(s7, "_x38");
  Term t103 = slv.mkTerm(Kind::SELECT, {t57, t3});
  slv.checkSat();
  ASSERT_THROW(slv.blockModelValues({t103}), CVC5ApiException);
}
TEST_F(TestApiBlackSolver, proj_issue426)
{
  Solver slv;
  slv.setLogic("ALL");
  slv.setOption("strings-exp", "true");
  slv.setOption("produce-models", "true");
  slv.setOption("produce-assertions", "true");
  Sort s1 = slv.getRealSort();
  Sort s2 = slv.getRoundingModeSort();
  Sort s4 = slv.mkSequenceSort(s1);
  Sort s5 = slv.mkArraySort(s4, s4);
  Term t4 = slv.mkConst(s1, "_x3");
  Term t5 = slv.mkReal("9192/832927743");
  Term t19 = slv.mkConst(s2, "_x42");
  Term t24 = slv.mkConst(s5, "_x44");
  Term t37 = slv.mkRoundingMode(RoundingMode::ROUND_TOWARD_POSITIVE);
  slv.checkSat();
  slv.blockModelValues({t24, t19, t4, t37});
  slv.checkSat();
  ASSERT_NO_THROW(slv.getValue({t5}));
}

TEST_F(TestApiBlackSolver, proj_issue429)
{
  Solver slv;
  Sort s1 = slv.getRealSort();
  Term t6 = slv.mkConst(s1, "_x5");
  Term t16 =
      slv.mkReal(std::stoll("1696223.9473797265702297792792306581323741"));
  Term t111 = slv.mkTerm(Kind::SEQ_UNIT, {t16});
  Term t119 = slv.mkTerm(slv.mkOp(Kind::SEQ_UNIT), {t6});
  Term t126 = slv.mkTerm(Kind::SEQ_PREFIX, {t111, t119});
  slv.checkEntailed({t126});
}

TEST_F(TestApiBlackSolver, proj_issue422)
{
  Solver slv;
  slv.setOption("sygus-rr-synth-input", "true");
  Sort s1 = slv.mkBitVectorSort(36);
  Sort s2 = slv.getStringSort();
  Term t1 = slv.mkConst(s2, "_x0");
  Term t2 = slv.mkConst(s1, "_x1");
  Term t11;
  {
    uint32_t bw = s1.getBitVectorSize();
    std::string val(bw, '1');
    val[0] = '0';
    t11 = slv.mkBitVector(bw, val, 2);
  }
  Term t60 = slv.mkTerm(Kind::SET_SINGLETON, {t1});
  Term t66 = slv.mkTerm(Kind::BITVECTOR_COMP, {t2, t11});
  Term t92 = slv.mkRegexpAll();
  Term t96 = slv.mkTerm(slv.mkOp(Kind::BITVECTOR_ZERO_EXTEND, 51), {t66});
  Term t105 = slv.mkTerm(Kind::BITVECTOR_ADD, {t96, t96});
  Term t113 = slv.mkTerm(Kind::BITVECTOR_SUB, {t105, t105});
  Term t137 = slv.mkTerm(Kind::BITVECTOR_XOR, {t113, t105});
  Term t211 = slv.mkTerm(Kind::BITVECTOR_SLTBV, {t137, t137});
  Term t212 = slv.mkTerm(Kind::SET_MINUS, {t60, t60});
  Term t234 = slv.mkTerm(Kind::SET_CHOOSE, {t212});
  Term t250 = slv.mkTerm(Kind::STRING_REPLACE_RE_ALL, {t1, t92, t1});
  Term t259 = slv.mkTerm(Kind::STRING_REPLACE_ALL, {t234, t234, t250});
  Term t263 = slv.mkTerm(Kind::STRING_TOLOWER, {t259});
  Term t272 = slv.mkTerm(Kind::BITVECTOR_SDIV, {t211, t66});
  Term t276 = slv.mkTerm(slv.mkOp(Kind::BITVECTOR_ZERO_EXTEND, 71), {t272});
  Term t288 = slv.mkTerm(Kind::EQUAL, {t263, t1});
  Term t300 = slv.mkTerm(Kind::BITVECTOR_SLT, {t276, t276});
  Term t301 = slv.mkTerm(Kind::EQUAL, {t288, t300});
  slv.assertFormula({t301});
  slv.push(4);
}

}  // namespace test
}  // namespace cvc5
