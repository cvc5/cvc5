/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the cvc5_types file of the C++ API.
 */

#include <cvc5/cvc5.h>

#include <algorithm>

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal {

namespace test {

class TestApiTypes : public ::testing::Test
{
};

TEST_F(TestApiTypes, printEnum)
{
  std::string expected =
      "LT ARRAY_SORT RTZ UNKNOWN_REASON literals preprocess full "
      "enum "
      "smt_lib_2_6 lfsc";
  {
    std::stringstream ss;
    ss << cvc5::Kind::LT << " ";
    ss << cvc5::SortKind::ARRAY_SORT << " ";
    ss << cvc5::RoundingMode::ROUND_TOWARD_ZERO << " ";
    ss << cvc5::UnknownExplanation::UNKNOWN_REASON << " ";
    ss << cvc5::modes::BlockModelsMode::LITERALS << " ";
    ss << cvc5::modes::LearnedLitType::PREPROCESS << " ";
    ss << cvc5::modes::ProofComponent::FULL << " ";
    ss << cvc5::modes::FindSynthTarget::ENUM << " ";
    ss << cvc5::modes::InputLanguage::SMT_LIB_2_6 << " ";
    ss << cvc5::modes::ProofFormat::LFSC;
    ASSERT_EQ(ss.str(), expected);
  }
  {
    std::stringstream ss;
    ss << std::to_string(cvc5::Kind::LT) << " ";
    ss << std::to_string(cvc5::SortKind::ARRAY_SORT) << " ";
    ss << std::to_string(cvc5::RoundingMode::ROUND_TOWARD_ZERO) << " ";
    ss << std::to_string(cvc5::UnknownExplanation::UNKNOWN_REASON) << " ";
    ss << std::to_string(cvc5::modes::BlockModelsMode::LITERALS) << " ";
    ss << std::to_string(cvc5::modes::LearnedLitType::PREPROCESS) << " ";
    ss << std::to_string(cvc5::modes::ProofComponent::FULL) << " ";
    ss << std::to_string(cvc5::modes::FindSynthTarget::ENUM) << " ";
    ss << std::to_string(cvc5::modes::InputLanguage::SMT_LIB_2_6) << " ";
    ss << std::to_string(cvc5::modes::ProofFormat::LFSC);
    ASSERT_EQ(ss.str(), expected);
  }
}

}  // namespace test
}  // namespace cvc5::internal
