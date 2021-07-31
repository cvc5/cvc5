/******************************************************************************
 * Top contributors (to current version):
 *   Yancheng Ou
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the optimization functionality
 */

#include "test_api.h"

namespace cvc5 {

using namespace api;

namespace test {

class TestApiBlackOpt : public TestApi
{
};

TEST_F(TestApiBlackOpt, pushpoplexico)
{
  using namespace std::string_literals;
  d_solver.setOption("incremental", "true");
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("produce-assertions", "true");
  Sort bvsort = d_solver.mkBitVectorSort(8);
  Term x = d_solver.mkConst(bvsort, "x");
  Term y = d_solver.mkConst(bvsort, "y");
  Term z = d_solver.mkConst(bvsort, "z");

  // 18 U<= x
  d_solver.assertFormula(
      d_solver.mkTerm(Kind::BITVECTOR_ULE, d_solver.mkBitVector(8, 18), x));
  // y S<= x
  d_solver.assertFormula(d_solver.mkTerm(Kind::BITVECTOR_SLE, y, x));

  // minimize x unsigned
  d_solver.addObjective(x, Solver::MINIMIZE, false);

  // push
  d_solver.push();

  // maximize y signed
  d_solver.addObjective(y, Solver::MAXIMIZE, true);
  // maximize z unsigned
  d_solver.addObjective(z, Solver::MAXIMIZE, false);

  // check-opt
  std::pair<api::Result, std::vector<OptimizationResult>> rstPair =
      d_solver.checkOpt(Solver::LEXICOGRAPHIC);

  ASSERT_TRUE(rstPair.first.isSat());

  // x == 18
  ASSERT_TRUE(rstPair.second[0].getResult().isSat());
  ASSERT_EQ(rstPair.second[0].getValue().getBitVectorValue(10), "18"s);

  // y == 18
  ASSERT_TRUE(rstPair.second[1].getResult().isSat());
  ASSERT_EQ(rstPair.second[1].getValue().getBitVectorValue(10), "18"s);

  // z == 0xFF
  ASSERT_TRUE(rstPair.second[2].getResult().isSat());
  ASSERT_EQ(rstPair.second[2].getValue().getBitVectorValue(2), "11111111"s);

  // pop
  d_solver.pop();

  // check-opt
  rstPair = d_solver.checkOpt(Solver::LEXICOGRAPHIC);

  ASSERT_TRUE(rstPair.first.isSat());
  ASSERT_EQ(rstPair.second.size(), 1);
  // x == 18
  ASSERT_EQ(rstPair.second[0].getValue().getBitVectorValue(10), "18"s);

  // reset-assertions
  d_solver.resetAssertions();

  // check-opt
  rstPair = d_solver.checkOpt(Solver::LEXICOGRAPHIC);

  ASSERT_TRUE(rstPair.first.isSat());
  ASSERT_EQ(rstPair.second.size(), 0);
}

TEST_F(TestApiBlackOpt, pareto)
{
  using std::string, std::pair, std::vector, std::set;
  d_solver.setOption("incremental", "true");
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("produce-assertions", "true");

  Sort bvsort = d_solver.mkBitVectorSort(4);
  Term a = d_solver.mkConst(bvsort, "a");
  Term b = d_solver.mkConst(bvsort, "b");
  Term aplusb = d_solver.mkTerm(Kind::BITVECTOR_ADD, a, b);
  // a + b U<= 4
  d_solver.assertFormula(
      d_solver.mkTerm(Kind::BITVECTOR_ULE, aplusb, d_solver.mkBitVector(4, 4)));
  // a U> 0
  d_solver.assertFormula(
      d_solver.mkTerm(Kind::BITVECTOR_UGT, a, d_solver.mkBitVector(4, 0)));
  // b U> 0
  d_solver.assertFormula(
      d_solver.mkTerm(Kind::BITVECTOR_UGT, b, d_solver.mkBitVector(4, 0)));

  // a U< 4
  d_solver.assertFormula(
      d_solver.mkTerm(Kind::BITVECTOR_ULT, a, d_solver.mkBitVector(4, 4)));
  // b U< 4
  d_solver.assertFormula(
      d_solver.mkTerm(Kind::BITVECTOR_ULT, b, d_solver.mkBitVector(4, 4)));

  // maximize a and maximize b
  d_solver.addObjective(a, Solver::MAXIMIZE);
  d_solver.addObjective(b, Solver::MAXIMIZE);

  // (a, b) = (1, 3), (2, 2), (3, 1)
  set<pair<string, string>> possibleResults = {
      {"1", "3"}, {"2", "2"}, {"3", "1"}};

  pair<api::Result, vector<OptimizationResult>> rstPair;
  pair<string, string> resultValues;
  for (int i = 0; i < 3; ++i)
  {
    rstPair = d_solver.checkOpt(Solver::PARETO);
    ASSERT_TRUE(rstPair.first.isSat());
    ASSERT_EQ(rstPair.second.size(), 2);

    resultValues =
        std::make_pair(rstPair.second[0].getValue().getBitVectorValue(10),
                       rstPair.second[1].getValue().getBitVectorValue(10));

    ASSERT_EQ(possibleResults.count(resultValues), 1);

    possibleResults.erase(resultValues);
  }

  rstPair = d_solver.checkOpt(Solver::PARETO);
  ASSERT_TRUE(rstPair.first.isUnsat());
  ASSERT_EQ(possibleResults.size(), 0);
}

}  // namespace test
}  // namespace cvc5
