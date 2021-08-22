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
#include "util/rational.h"
#include "context/context.h"

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
    d_intBlaster(d_smtEngine->getContext(), options::SolveBVAsIntMode::SUM, 1, false);
  }
  Node d_true;
  Node d_one;
  IntBlaster d_intBlaster;
};

TEST_F(TestTheoryWhiteBvIntblaster, bitblaster_constants)
{
	std::vector<Node> lemmas;
	std::map<Node, Node> skolems;
	BitVector c1(4, 7);
	Node bv0_4 = d_nodeManager->mkConst<BitVector>(c1);
	Node result = d_intBlaster->translateNoChildren(c1, lemmas, skolems);
	Node expected = d_nodeManager->mkConst(Rational(7));
	ASSERT_EQ(bv0_4, result);
}

}  // namespace test
}  // namespace cvc5
