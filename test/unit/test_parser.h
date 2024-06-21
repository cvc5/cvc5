/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common header for parser API unit test.
 */
#ifndef CVC5__TEST__UNIT__TEST_PARSER_H
#define CVC5__TEST__UNIT__TEST_PARSER_H

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include "test_api.h"

using namespace cvc5::parser;

namespace cvc5::internal {
namespace test {

class TestParser : public TestApi
{
 protected:
  TestParser() {}

  virtual ~TestParser() {}

  void SetUp() override
  {
    TestApi::SetUp();
    d_symman.reset(new SymbolManager(d_tm));
  }

  void TearDown() override { d_symman.reset(nullptr); }
  std::unique_ptr<SymbolManager> d_symman;
};

}  // namespace test
}  // namespace cvc5::internal

#endif
