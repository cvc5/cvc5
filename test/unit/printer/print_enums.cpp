/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of printing enumerator types
 */

#include <cvc5/cvc5.h>

#include <iostream>

#include "test_smt.h"
#include "theory/arith/nl/strategy.h"
#include "theory/arith/rewrites.h"
#include "theory/ext_theory.h"
#include "theory/incomplete_id.h"
#include "theory/inference_id.h"
#include "theory/strings/rewrites.h"
#include "theory/strings/strategy.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace test {

/**
 * Set domain.optName to value due to reason. Notify if value changes.
 */
#define TEST_ENUM_RANGE(enumName, firstEnum, lastEnum) \
  {                                                    \
    size_t begin = static_cast<size_t>(firstEnum);     \
    size_t end = static_cast<size_t>(lastEnum);        \
    for (size_t i = begin; i < end; i++)               \
    {                                                  \
      out << static_cast<enumName>(i) << std::endl;    \
    }                                                  \
  }

class TestPrintEnums : public TestSmt
{
};

TEST_F(TestPrintEnums, print_enums)
{
  std::stringstream out;
  TEST_ENUM_RANGE(InferenceId, InferenceId::NONE, InferenceId::UNKNOWN);
  TEST_ENUM_RANGE(IncompleteId, IncompleteId::NONE, IncompleteId::UNKNOWN);
  TEST_ENUM_RANGE(ExtReducedId, ExtReducedId::NONE, ExtReducedId::UNKNOWN);
  TEST_ENUM_RANGE(
      strings::Rewrite, strings::Rewrite::NONE, strings::Rewrite::UNKNOWN);
  TEST_ENUM_RANGE(strings::InferStep,
                  strings::InferStep::NONE,
                  strings::InferStep::UNKNOWN);
  TEST_ENUM_RANGE(
      arith::Rewrite, arith::Rewrite::NONE, arith::Rewrite::UNKNOWN);
  TEST_ENUM_RANGE(arith::nl::InferStep,
                  arith::nl::InferStep::NONE,
                  arith::nl::InferStep::UNKNOWN);
}

}  // namespace test
}  // namespace cvc5::internal
