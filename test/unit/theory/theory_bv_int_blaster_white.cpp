/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for bit-vector solving via integers.
 */

#include <iostream>
#include <memory>
#include <vector>

#include "test_smt.h"
#include "theory/bv/int_blaster.h"
#include "util/bitvector.h"

namespace cvc5 {

using namespace kind;
using namespace theory;

namespace test {

class TestTheoryWhiteBvIntblaster : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_smtEngine->setOption("produce-models", "true");
    d_smtEngine->finishInit();
    d_true = d_nodeManager->mkConst<bool>(true);
    d_one = d_nodeManager->mkConst<Rational>(Rational(1));
  }
  Node d_true;
  Node d_one;
};
}  // namespace test
}  // namespace cvc5
