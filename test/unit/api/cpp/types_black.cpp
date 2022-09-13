/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the cvc5_types file of the C++ API.
 */

#include <algorithm>

#include "api/cpp/cvc5.h"
#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal {

namespace test {

class TestApiTypes : public ::testing::Test
{
};

TEST_F(TestApiTypes, printEnum)
{
  std::stringstream ss;
  ss << cvc5::UnknownExplanation::UNKNOWN_REASON;
  ss << cvc5::modes::BlockModelsMode::LITERALS;
  ss << cvc5::modes::LearnedLitType::LEARNED_LIT_PREPROCESS;
  ss << cvc5::modes::ProofComponent::PROOF_COMPONENT_FULL;
}

}  // namespace test
}  // namespace cvc5::internal
