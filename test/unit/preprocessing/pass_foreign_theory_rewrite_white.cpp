/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for Foreign Theory Rerwrite prepricessing pass.
 */

#include "expr/node_manager.h"
#include "preprocessing/passes/foreign_theory_rewrite.h"
#include "smt/solver_engine.h"
#include "test_smt.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::preprocessing::passes;

namespace cvc5::internal {
namespace test {

class TestPPWhiteForeignTheoryRewrite : public TestSmt
{
};

TEST_F(TestPPWhiteForeignTheoryRewrite, simplify)
{
  ForeignTheoryRewriter ftr(d_slvEngine->getEnv());
  std::cout << "len(x) >= 0 is simplified to true" << std::endl;
  Node x = d_nodeManager->mkVar("x", d_nodeManager->stringType());
  Node len_x = d_nodeManager->mkNode(kind::STRING_LENGTH, x);
  Node zero = d_nodeManager->mkConstInt(0);
  Node geq1 = d_nodeManager->mkNode(kind::GEQ, len_x, zero);
  Node tt = d_nodeManager->mkConst<bool>(true);
  Node simplified1 = ftr.foreignRewrite(geq1);
  ASSERT_EQ(simplified1, tt);

  std::cout << "len(x) >= n is not simplified to true" << std::endl;
  Node n = d_nodeManager->mkVar("n", d_nodeManager->integerType());
  Node geq2 = d_nodeManager->mkNode(kind::GEQ, len_x, n);
  Node simplified2 = ftr.foreignRewrite(geq2);
  ASSERT_NE(simplified2, tt);
}

}  // namespace test
}  // namespace cvc5::internal
