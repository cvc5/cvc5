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
  void SetUp() override { d_solver.reset(new cvc5::Solver(d_tm)); }

 protected:
  cvc5::TermManager d_tm;
  std::unique_ptr<cvc5::Solver> d_solver;
};

}  // namespace test
}  // namespace cvc5::internal
#endif
