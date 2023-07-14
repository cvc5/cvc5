/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of printing enumerator types
 */

#include <cvc5/cvc5.h>

#include <iostream>
#include "theory/inference_id.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace test {
  
/**
 * Set domain.optName to value due to reason. Notify if value changes.
 */
#define TEST_ENUM_RANGE(enumName, firstEnum, lastEnum) \
  size_t begin = static_cast<size_t>(firstEnum);       \
  size_t end = static_cast<size_t>(lastEnum);          \
  for (size_t i=begin: i<end; i++)                     \
  {                                                    \
    out << static_cast<enumName>(i) << std::endl;      \
  }
  
class TestPrintEnums : public TestSmt
{
};

TEST_F(TestPrintEnums, print_enums)
{
  std::stringstream out;
  TEST_ENUM_RANGE(InferenceId, InferenceId::NONE, InferenceId::UNKNOWN);
}

}  // namespace test
}  // namespace cvc5::internal
