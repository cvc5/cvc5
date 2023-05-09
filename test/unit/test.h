/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common header for API unit test.
 */

#ifndef CVC5__TEST__UNIT__TEST_H
#define CVC5__TEST__UNIT__TEST_H

#include "gtest/gtest.h"

namespace cvc5::internal {
namespace test {

class TestInternal : public ::testing::Test
{
};

}  // namespace test
}  // namespace cvc5::internal
#endif
