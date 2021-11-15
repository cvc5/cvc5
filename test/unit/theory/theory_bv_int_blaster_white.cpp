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
#include "theory/bv/theory_bv_utils.h"
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
    d_slvEngine->setOption("produce-models", "true");
    d_slvEngine->finishInit();
    d_true = d_nodeManager->mkConst<bool>(true);
    d_one = d_nodeManager->mkConst<Rational>(CONST_RATIONAL, Rational(1));
  }
  Node d_true;
  Node d_one;
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
  IntBlaster intBlaster(
      env, options::SolveBVAsIntMode::SUM, 1, false);
  Node result = intBlaster.translateNoChildren(bv7_4, lemmas, skolems);
  Node seven = d_nodeManager->mkConst(CONST_RATIONAL, Rational(7));
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
  IntBlaster intBlaster(
      env, options::SolveBVAsIntMode::SUM, 1, true);
  Node result = intBlaster.translateNoChildren(bv, lemmas, skolems);
  ASSERT_TRUE(result.isVar() && result.getType().isInteger());

  // translating integer variables should not change them
  Node resultSquared = intBlaster.translateNoChildren(result, lemmas, skolems);
  ASSERT_EQ(resultSquared, result);
}

TEST_F(TestTheoryWhiteBvIntblaster, intblaster_uf)
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
  Options opts;
  Env env(d_nodeManager, &opts);
  env.d_logic.setLogicString("QF_UFBV");
  env.d_logic.lock();
  IntBlaster intBlaster(
      env, options::SolveBVAsIntMode::SUM, 1, true);
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

/** Check all cases of the translation.
 * This is a sanity check, that noly verifies
 * the expected type, and that there were no
 * failures.
 */
TEST_F(TestTheoryWhiteBvIntblaster, intblaster_with_children)
{
  // place holders for lemmas and skolem
  std::vector<Node> lemmas;
  std::map<Node, Node> skolems;
  Options opts;
  Env env(d_nodeManager, &opts);
  env.d_logic.setLogicString("QF_UFBV");
  env.d_logic.lock();
  IntBlaster intBlaster(
      env, options::SolveBVAsIntMode::SUM, 1, true);

  // bit-vector variables
  TypeNode bvType = d_nodeManager->mkBitVectorType(4);
  Node v1 = d_nodeManager->mkVar("v1", bvType);
  Node v2 = d_nodeManager->mkVar("v2", bvType);

  // translated integer variables
  Node i1 = intBlaster.translateNoChildren(v1, lemmas, skolems);
  Node i2 = intBlaster.translateNoChildren(v2, lemmas, skolems);

  // if original is BV, result should be Int.
  // Otherwise, they should have the same type.
  Node original;
  Node result;

  // sum
  original = d_nodeManager->mkNode(BITVECTOR_ADD, v1, v2);
  result = intBlaster.translateWithChildren(original, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());

  // multiplication
  original = d_nodeManager->mkNode(BITVECTOR_MULT, v1, v2);
  result = intBlaster.translateWithChildren(original, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());

  // division 1
  original = d_nodeManager->mkNode(BITVECTOR_UDIV, v1, v2);
  result = intBlaster.translateWithChildren(original, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());

  // division 2
  original = d_nodeManager->mkNode(BITVECTOR_UREM, v1, v2);
  result = intBlaster.translateWithChildren(original, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());

  // bit-wise negation
  original = d_nodeManager->mkNode(BITVECTOR_NOT, v1);
  result = intBlaster.translateWithChildren(original, {i1}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());

  // arithmetic negation
  original = d_nodeManager->mkNode(BITVECTOR_NEG, v1);
  result = intBlaster.translateWithChildren(original, {i1}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());

  // bv2nat
  original = d_nodeManager->mkNode(BITVECTOR_TO_NAT, v1);
  result = intBlaster.translateWithChildren(original, {i1}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());

  // int2bv
  Node intToBVOp = d_nodeManager->mkConst<IntToBitVector>(IntToBitVector(4));
  original = d_nodeManager->mkNode(intToBVOp, i1);
  result = intBlaster.translateWithChildren(original, {i1}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());

  // zero extend
  Node zeroExtOp =
      d_nodeManager->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(4));
  original = d_nodeManager->mkNode(zeroExtOp, v1);
  result = intBlaster.translateWithChildren(original, {i1}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());

  // extract + BV ITE
  Node extract = theory::bv::utils::mkExtract(v1, 0, 0);
  original = d_nodeManager->mkNode(BITVECTOR_ITE, extract, v2, v1);
  Node intExtract = intBlaster.translateWithChildren(extract, {i1}, lemmas);
  result =
      intBlaster.translateWithChildren(original, {intExtract, i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());
  ASSERT_TRUE(intExtract.getType().isInteger());

  // concat
  original = d_nodeManager->mkNode(BITVECTOR_CONCAT, v1, v2);
  result = intBlaster.translateWithChildren(original, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());

  // predicates
  original = d_nodeManager->mkNode(EQUAL, v1, v2);
  result = intBlaster.translateWithChildren(original, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isBoolean());

  original = d_nodeManager->mkNode(BITVECTOR_ULT, v1, v2);
  result = intBlaster.translateWithChildren(original, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isBoolean());

  original = d_nodeManager->mkNode(BITVECTOR_ULE, v1, v2);
  result = intBlaster.translateWithChildren(original, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isBoolean());

  original = d_nodeManager->mkNode(BITVECTOR_UGT, v1, v2);
  result = intBlaster.translateWithChildren(original, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isBoolean());

  original = d_nodeManager->mkNode(BITVECTOR_UGE, v1, v2);
  result = intBlaster.translateWithChildren(original, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isBoolean());

  // BVULT with a BV result
  original = d_nodeManager->mkNode(BITVECTOR_ULTBV, v1, v2);
  result = intBlaster.translateWithChildren(original, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());

  // function application
  TypeNode funType = d_nodeManager->mkFunctionType({bvType}, bvType);
  Node f = d_nodeManager->mkVar("f", funType);
  Node g = intBlaster.translateNoChildren(f, lemmas, skolems);
  original = d_nodeManager->mkNode(APPLY_UF, f, v1);
  result = intBlaster.translateWithChildren(original, {g, i1}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());
}

}  // namespace test
}  // namespace cvc5
