/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Blackbox tests using the API targeting UF + higher-order.
 */

#include "base/configuration.h"
#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestTheoryBlackUfHo : public TestApi
{
};

TEST_F(TestTheoryBlackUfHo, proj_issue361)
{
  d_solver.setLogic("HO_ALL");
  d_solver.setOption("produce-models", "true");
  Sort s1 = d_solver.getBooleanSort();
  Term t1 = d_solver.mkConst(s1, "_x0");
  Term t145 = d_solver.mkTerm(NOT, {t1});
  Term t169 = d_solver.mkTerm(AND, {t145, t1});
  Sort s4 = d_solver.mkFunctionSort({s1, s1, s1}, s1);
  Sort s6 = d_solver.mkBagSort(s1);
  Term t189 = d_solver.mkConst(s4, "_x32");
  Term t200 = d_solver.mkConst(s6, "_x43");
  Term t250 = d_solver.mkTerm(BAG_COUNT, {t145, t200});
  Term t367 = d_solver.mkTerm(APPLY_UF, {t189, t1, t169, t1});
  d_solver.checkSatAssuming({t145, t367, t145, t145, t145});
  Term v = d_solver.getValue(t250);
  ASSERT_TRUE(
      d_solver.checkSatAssuming(d_solver.mkTerm(EQUAL, {t250, v})).isSat());
}

}  // namespace test
}  // namespace cvc5::internal
