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
 * Blackbox tests involving parametric datatypes.
 */

#include "test_api.h"
#include "base/configuration.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackParametricDatatype : public TestApi
{
};

TEST_F(TestApiBlackParametricDatatype, proj_issue387)
{
  Sort s1 = d_solver.getBooleanSort();

  Sort u1 = d_solver.mkUninterpretedSortConstructorSort(1, "_x0");
  Sort u2 = d_solver.mkUninterpretedSortConstructorSort(1);
  Sort p1 = d_solver.mkParamSort("_x4");
  Sort p2 = d_solver.mkParamSort("_x27");
  Sort p3 = d_solver.mkParamSort("_x3");

  DatatypeDecl dtdecl1 = d_solver.mkDatatypeDecl("_x0", {p1});
  DatatypeConstructorDecl ctordecl1 =
      d_solver.mkDatatypeConstructorDecl("_x18");
  ASSERT_THROW(ctordecl1.addSelector("_x17", u2.instantiate({p1, p1})),
               CVC5ApiException);
}

}  // namespace test
}  // namespace cvc5::internal
