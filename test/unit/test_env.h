/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andres Noetzli, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common header for unit tests involving env.
 */

#ifndef CVC5__TEST__UNIT__TEST_NODE_H
#define CVC5__TEST__UNIT__TEST_NODE_H

#include "expr/node_manager.h"
#include "expr/skolem_manager.h"
#include "options/options.h"
#include "smt/env.h"
#include "smt/solver_engine.h"
#include "test.h"

namespace cvc5::internal {
namespace test {

class TestEnv : public TestInternal
{
 protected:
  void SetUp() override
  {
    d_options.reset(new Options());
    d_nodeManager = NodeManager::currentNM();
    d_env.reset(new Env(d_options.get()));
  }

  std::unique_ptr<Options> d_options;
  NodeManager* d_nodeManager;
  std::unique_ptr<Env> d_env;
};

}  // namespace test
}  // namespace cvc5::internal
#endif
