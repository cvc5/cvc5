/*********************                                                        */
/*! \file theory_bags_type_rules_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of bags typing rules
 **/

#include <cxxtest/TestSuite.h>

#include "api/cvc4cpp.h"

using namespace CVC4;
using namespace CVC4::api;

class SetsTypeRuleWhite : public CxxTest::TestSuite
{
 public:
  void setUp() override { d_slv.reset(new Solver()); }

  void tearDown() override { d_slv.reset(); }

  void testSingletonOperator()
  {
    Sort setSort = d_slv->mkSetSort(d_slv->getRealSort());
    Term emptyReal = d_slv->mkEmptySet(setSort);

    Term singletonInt = d_slv->mkTerm(SINGLETON, d_slv->mkReal(1));
    std::cout << std::endl << singletonInt.getSort() << std::endl;

    Term singletonReal = d_slv->mkTerm(SINGLETON, d_slv->mkReal(1, 5));
    std::cout << singletonReal.getSort() << std::endl;
    TS_ASSERT_THROWS(d_slv->mkTerm(UNION, singletonInt, emptyReal),
                     CVC4ApiException);
    TS_ASSERT_THROWS_NOTHING(d_slv->mkTerm(UNION, singletonReal, emptyReal));
  }

 private:
  std::unique_ptr<Solver> d_slv;
}; /* class SetsTypeRuleWhite */
