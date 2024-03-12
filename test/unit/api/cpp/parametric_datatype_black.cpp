/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
  Sort s1 = d_tm.getBooleanSort();

  Sort u1 = d_tm.mkUninterpretedSortConstructorSort(1, "_x0");
  Sort u2 = d_tm.mkUninterpretedSortConstructorSort(1);
  Sort p1 = d_tm.mkParamSort("_x4");
  Sort p2 = d_tm.mkParamSort("_x27");
  Sort p3 = d_tm.mkParamSort("_x3");

  DatatypeDecl dtdecl1 = d_tm.mkDatatypeDecl("_x0", {p1});
  DatatypeConstructorDecl ctordecl1 = d_tm.mkDatatypeConstructorDecl("_x18");
  ASSERT_THROW(ctordecl1.addSelector("_x17", u2.instantiate({p1, p1})),
               CVC5ApiException);
}

}  // namespace test
}  // namespace cvc5::internal
