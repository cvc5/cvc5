/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the cvc5_types file of the C++ API.
 */

#include <cvc5/c/cvc5.h>

#include <algorithm>

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal {

namespace test {

class TestCApiBlackTypes : public ::testing::Test
{
};

TEST_F(TestCApiBlackTypes, printEnum)
{
  ASSERT_DEATH(cvc5_kind_to_string(static_cast<Cvc5Kind>(-5)),
               "invalid term kind");
  ASSERT_DEATH(cvc5_sort_kind_to_string(static_cast<Cvc5SortKind>(-5)),
               "invalid sort kind");
  ASSERT_DEATH(cvc5_rm_to_string(static_cast<Cvc5RoundingMode>(-5)),
               "invalid rounding mode");
  ASSERT_DEATH(cvc5_unknown_explanation_to_string(
                   static_cast<Cvc5UnknownExplanation>(-5)),
               "invalid unknown explanation kind");
  ASSERT_DEATH(cvc5_modes_block_models_mode_to_string(
                   static_cast<Cvc5BlockModelsMode>(-5)),
               "invalid block models mode");
  ASSERT_DEATH(cvc5_modes_find_synth_target_to_string(
                   static_cast<Cvc5FindSynthTarget>(-5)),
               "invalid find synthesis target");
  ASSERT_DEATH(
      cvc5_modes_input_language_to_string(static_cast<Cvc5InputLanguage>(-5)),
      "invalid input language");
  ASSERT_DEATH(cvc5_modes_learned_lit_type_to_string(
                   static_cast<Cvc5LearnedLitType>(-5)),
               "invalid learned literal type");
  ASSERT_DEATH(
      cvc5_modes_proof_component_to_string(static_cast<Cvc5ProofComponent>(-5)),
      "invalid proof component kind");
  ASSERT_DEATH(
      cvc5_modes_proof_format_to_string(static_cast<Cvc5ProofFormat>(-5)),
      "invalid proof format");
  std::string expected =
      "CVC5_KIND_LT CVC5_SORT_KIND_ARRAY_SORT RTZ UNKNOWN_REASON literals "
      "preprocess full enum smt_lib_2_6 lfsc";
  std::stringstream ss;
  ss << cvc5_kind_to_string(CVC5_KIND_LT) << " ";
  ss << cvc5_sort_kind_to_string(CVC5_SORT_KIND_ARRAY_SORT) << " ";
  ss << cvc5_rm_to_string(CVC5_RM_ROUND_TOWARD_ZERO) << " ";
  ss << cvc5_unknown_explanation_to_string(
      CVC5_UNKNOWN_EXPLANATION_UNKNOWN_REASON)
     << " ";
  ss << cvc5_modes_block_models_mode_to_string(CVC5_BLOCK_MODELS_MODE_LITERALS)
     << " ";
  ss << cvc5_modes_learned_lit_type_to_string(CVC5_LEARNED_LIT_TYPE_PREPROCESS)
     << " ";
  ss << cvc5_modes_proof_component_to_string(CVC5_PROOF_COMPONENT_FULL) << " ";
  ss << cvc5_modes_find_synth_target_to_string(CVC5_FIND_SYNTH_TARGET_ENUM)
     << " ";
  ss << cvc5_modes_input_language_to_string(CVC5_INPUT_LANGUAGE_SMT_LIB_2_6)
     << " ";
  ss << cvc5_modes_proof_format_to_string(CVC5_PROOF_FORMAT_LFSC);
  ASSERT_EQ(ss.str(), expected);
}

}  // namespace test
}  // namespace cvc5::internal
