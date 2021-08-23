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

#include "context/context.h"
#include "options/options.h"
#include "test_smt.h"
#include "theory/bv/int_blaster.h"
#include "util/bitvector.h"
#include "util/rational.h"
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

TEST_F(TestTheoryWhiteBvIntblaster, bitblaster_constants)
{
  // place holders for lemmas and skolem
  std::vector<Node> lemmas;
  std::map<Node, Node> skolems;

  // bit-vector constant representing the integer 7, with 4 bits
  BitVector c1(4, Integer(7));
  Node bv7_4 = d_nodeManager->mkConst<BitVector>(c1);

  // translating it to integers should yield 7.
  IntBlaster intBlaster(
      d_smtEngine->getContext(), options::SolveBVAsIntMode::SUM, 1, false);
  Node result = intBlaster.translateNoChildren(bv7_4, lemmas, skolems);
  Node seven = d_nodeManager->mkConst(Rational(7));
  ASSERT_EQ(seven, result);

  // translating integer constants should not change them
  result = intBlaster.translateNoChildren(seven, lemmas, skolems);
  ASSERT_EQ(seven, result);
}

TEST_F(TestTheoryWhiteBvIntblaster, bitblaster_symbolic_constant)
{
  // place holders for lemmas and skolem
  std::vector<Node> lemmas;
  std::map<Node, Node> skolems;

  // bit-vector variable
  TypeNode bvType = d_nodeManager->mkBitVectorType(4);
  Node bv = d_nodeManager->mkVar("bv1", bvType);

  // translating it to integers should yield an integer variable.
  IntBlaster intBlaster(
      d_smtEngine->getContext(), options::SolveBVAsIntMode::SUM, 1, true);
  Node result = intBlaster.translateNoChildren(bv, lemmas, skolems);
  ASSERT_TRUE(result.isVar() && result.getType().isInteger());

  // translating integer variables should not change them
  Node resultSquared = intBlaster.translateNoChildren(result, lemmas, skolems);
  ASSERT_EQ(resultSquared, result);
}

TEST_F(TestTheoryWhiteBvIntblaster, bitblaster_uf)
{
  // place holders for lemmas and skolem
  std::vector<Node> lemmas;
  std::map<Node, Node> skolems;

  // uf from integers and bit-vectors to Bools
  std::vector<TypeNode> domain;
  TypeNode bvType = d_nodeManager->mkBitVectorType(4);
  TypeNode intType = d_nodeManager->integerType();
  domain.push_back(intType);
  domain.push_back(bvType);
  TypeNode range = d_nodeManager->booleanType();
  TypeNode funType = d_nodeManager->mkFunctionType(domain, range);
  Node f = d_nodeManager->mkVar("f", funType);

  // translating it to integers should yield an Int x Int -> Bool function
  IntBlaster intBlaster(
      d_smtEngine->getContext(), options::SolveBVAsIntMode::SUM, 1, true);
  Node result = intBlaster.translateNoChildren(f, lemmas, skolems);
  TypeNode resultType = result.getType();
  std::vector<TypeNode> resultDomain = resultType.getArgTypes();
  TypeNode resultRange = resultType.getRangeType();
  ASSERT_TRUE(result.isVar());
  ASSERT_TRUE(resultType.isFunction());
  ASSERT_TRUE(resultDomain.size() == 2);
  ASSERT_TRUE(resultDomain[0].isInteger());
  ASSERT_TRUE(resultDomain[1].isInteger());
  ASSERT_TRUE(resultRange.isBoolean());
}

}  // namespace test
}  // namespace cvc5
