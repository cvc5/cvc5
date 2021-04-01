/*********************                                                        */
/*! \file test_context.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Header for context unit tests.
 **/

#ifndef CVC4__TEST__UNIT__TEST_CONTEXT_H
#define CVC4__TEST__UNIT__TEST_CONTEXT_H

#include "context/context.h"
#include "test.h"

namespace CVC5 {
namespace test {

class TestContext : public TestInternal
{
 protected:
  void SetUp() override { d_context.reset(new CVC5::context::Context()); }
  std::unique_ptr<CVC5::context::Context> d_context;
};

}  // namespace test
}  // namespace CVC5
#endif
