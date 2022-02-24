/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for parts of the transcendental solver.
 */

#include <iostream>
#include <memory>
#include <vector>

#include "test_smt.h"
#include "theory/arith/nl/transcendental/approximate_pi.h"

namespace cvc5 {
namespace test {

using namespace theory::arith::nl::transcendental;

class TestTheoryWhiteArithTranscendental : public TestSmt
{
};

TEST_F(TestTheoryWhiteArithTranscendental, test_approximate_pi)
{
  Rational pi_approx = Rational(
      Integer("314159265358979323846264338327950288419716939937510582097494"),
      Integer("100000000000000000000000000000000000000000000000000000000000"));

  ApproximatePi approx;
  for (uint64_t i = 0; i < 46; ++i)
  {
    EXPECT_TRUE(approx.getLowerBound() < pi_approx
                && pi_approx < approx.getUpperBound());
    approx.refine();
  }
  // now the approximation is getting more accurate than pi_approx...
  EXPECT_FALSE(approx.getLowerBound() < pi_approx
               && pi_approx < approx.getUpperBound());
}

}  // namespace test
}  // namespace cvc5
