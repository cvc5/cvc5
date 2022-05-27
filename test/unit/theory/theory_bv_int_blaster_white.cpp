/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Makai Mann, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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

#include "context/context.h"
#include "options/options.h"
#include "test_smt.h"
#include "theory/bv/int_blaster.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"
#include "util/rational.h"
namespace cvc5::internal {

using namespace kind;
using namespace theory;

namespace test {

class TestTheoryWhiteBvIntblaster : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_slvEngine->setOption("produce-models", "true");
    d_slvEngine->finishInit();
  }
};

TEST_F(TestTheoryWhiteBvIntblaster, intblaster_constants)
{
  // place holders for lemmas and skolem
  std::vector<Node> lemmas;
  std::map<Node, Node> skolems;

  // bit-vector constant representing the integer 7, with 4 bits
  BitVector c1(4, Integer(7));
  Node bv7_4 = d_nodeManager->mkConst<BitVector>(c1);

  // translating it to integers should yield 7.
  Options opts;
  Env env(d_nodeManager, &opts);
  env.d_logic.setLogicString("QF_UFBV");
  env.d_logic.lock();
  IntBlaster intBlaster(env, options::SolveBVAsIntMode::SUM, 1);
  Node result = intBlaster.translateNoChildren(bv7_4, lemmas, skolems);
  Node seven = d_nodeManager->mkConstInt(Rational(7));
  ASSERT_EQ(seven, result);

  // translating integer constants should not change them
  result = intBlaster.translateNoChildren(seven, lemmas, skolems);
  ASSERT_EQ(seven, result);
}

TEST_F(TestTheoryWhiteBvIntblaster, intblaster_symbolic_constant)
{
  // place holders for lemmas and skolem
  std::vector<Node> lemmas;
  std::map<Node, Node> skolems;

  // bit-vector variable
  TypeNode bvType = d_nodeManager->mkBitVectorType(4);
  Node bv = d_nodeManager->mkVar("bv1", bvType);

  // translating it to integers should yield an integer variable.
  Options opts;
  Env env(d_nodeManager, &opts);
  env.d_logic.setLogicString("QF_UFBV");
  env.d_logic.lock();
  IntBlaster intBlaster(env, options::SolveBVAsIntMode::SUM, 1);
  Node result = intBlaster.translateNoChildren(bv, lemmas, skolems);
  ASSERT_TRUE(result.isVar() && result.getType().isInteger());

  // translating integer variables should not change them
  Node resultSquared = intBlaster.translateNoChildren(result, lemmas, skolems);
  ASSERT_EQ(resultSquared, result);
}


}  // namespace test
}  // namespace cvc5::internal
