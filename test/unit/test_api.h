/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common header for API unit test.
 */

#ifndef CVC5__TEST__UNIT__TEST_API_H
#define CVC5__TEST__UNIT__TEST_API_H

#include <cvc5/cvc5.h>

#include "gtest/gtest.h"

namespace cvc5::internal {
namespace test {

class TestApi : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_solver.reset(new cvc5::Solver(d_tm));
    d_bool = d_tm.getBooleanSort();
    d_int = d_tm.getIntegerSort();
    d_real = d_tm.getRealSort();
    d_string = d_tm.getStringSort();
    d_uninterpreted = d_tm.mkUninterpretedSort("u");
  }
  cvc5::TermManager d_tm;
  std::unique_ptr<cvc5::Solver> d_solver;
  Sort d_bool;
  Sort d_int;
  Sort d_real;
  Sort d_string;
  Sort d_uninterpreted;
};

}  // namespace test
}  // namespace cvc5::internal
#endif
