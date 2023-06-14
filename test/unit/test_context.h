/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Header for context unit tests.
 */

#ifndef CVC5__TEST__UNIT__TEST_CONTEXT_H
#define CVC5__TEST__UNIT__TEST_CONTEXT_H

#include "context/context.h"
#include "test.h"

namespace cvc5::internal {
namespace test {

class TestContext : public TestInternal
{
 protected:
  void SetUp() override { d_context.reset(new cvc5::context::Context()); }
  std::unique_ptr<cvc5::context::Context> d_context;
};

}  // namespace test
}  // namespace cvc5::internal
#endif
