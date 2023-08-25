/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include <vector>

#include "expr/node.h"
#include "test_smt.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/evaluator.h"
#include "theory/rewriter.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace test {

class TestTheoryWhiteEvaluator : public TestSmt
{
};

TEST_F(TestTheoryWhiteEvaluator, simple)
{
  TypeNode bv64Type = d_nodeManager->mkBitVectorType(64);

  Node w = d_nodeManager->mkVar("w", bv64Type);
  Node x = d_nodeManager->mkVar("x", bv64Type);
  Node y = d_nodeManager->mkVar("y", bv64Type);
  Node z = d_nodeManager->mkVar("z", bv64Type);

  Node zero = d_nodeManager->mkConst(BitVector(64, (unsigned int)0));
  Node one = d_nodeManager->mkConst(BitVector(64, (unsigned int)1));
  Node c1 = d_nodeManager->mkConst(BitVector(
      64,
      (unsigned int)0b0000000100000101001110111001101000101110011101011011110011100111));
  Node c2 = d_nodeManager->mkConst(BitVector(
      64,
      (unsigned int)0b0000000100000101001110111001101000101110011101011011110011100111));

  Node t = d_nodeManager->mkNode(
      kind::ITE, d_nodeManager->mkNode(kind::EQUAL, y, one), x, w);

  std::vector<Node> args = {w, x, y, z};
  std::vector<Node> vals = {c1, zero, one, c1};

  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  Evaluator eval(rr);
  Node r = eval.eval(t, args, vals);
  ASSERT_EQ(r,
            rr->rewrite(t.substitute(
                args.begin(), args.end(), vals.begin(), vals.end())));
}

TEST_F(TestTheoryWhiteEvaluator, loop)
{
  TypeNode bv64Type = d_nodeManager->mkBitVectorType(64);

  Node w = d_nodeManager->mkBoundVar(bv64Type);
  Node x = d_nodeManager->mkVar("x", bv64Type);

  Node zero = d_nodeManager->mkConst(BitVector(1, (unsigned int)0));
  Node one = d_nodeManager->mkConst(BitVector(64, (unsigned int)1));
  Node c = d_nodeManager->mkConst(BitVector(
      64,
      (unsigned int)0b0001111000010111110000110110001101011110111001101100000101010100));

  Node largs = d_nodeManager->mkNode(kind::BOUND_VAR_LIST, w);
  Node lbody = d_nodeManager->mkNode(
      kind::BITVECTOR_CONCAT, bv::utils::mkExtract(w, 62, 0), zero);
  Node lambda = d_nodeManager->mkNode(kind::LAMBDA, largs, lbody);
  Node t =
      d_nodeManager->mkNode(kind::BITVECTOR_AND,
                            d_nodeManager->mkNode(kind::APPLY_UF, lambda, one),
                            d_nodeManager->mkNode(kind::APPLY_UF, lambda, x));

  std::vector<Node> args = {x};
  std::vector<Node> vals = {c};
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  Evaluator eval(rr);
  Node r = eval.eval(t, args, vals);
  ASSERT_EQ(r,
            rr->rewrite(t.substitute(
                args.begin(), args.end(), vals.begin(), vals.end())));
}

TEST_F(TestTheoryWhiteEvaluator, strIdOf)
{
  Node a = d_nodeManager->mkConst(String("A"));
  Node empty = d_nodeManager->mkConst(String(""));
  Node one = d_nodeManager->mkConstInt(Rational(1));
  Node two = d_nodeManager->mkConstInt(Rational(2));

  std::vector<Node> args;
  std::vector<Node> vals;
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  Evaluator eval(rr);

  {
    Node n = d_nodeManager->mkNode(kind::STRING_INDEXOF, a, empty, one);
    Node r = eval.eval(n, args, vals);
    ASSERT_EQ(r, rr->rewrite(n));
  }

  {
    Node n = d_nodeManager->mkNode(kind::STRING_INDEXOF, a, a, one);
    Node r = eval.eval(n, args, vals);
    ASSERT_EQ(r, rr->rewrite(n));
  }

  {
    Node n = d_nodeManager->mkNode(kind::STRING_INDEXOF, a, empty, two);
    Node r = eval.eval(n, args, vals);
    ASSERT_EQ(r, rr->rewrite(n));
  }

  {
    Node n = d_nodeManager->mkNode(kind::STRING_INDEXOF, a, a, two);
    Node r = eval.eval(n, args, vals);
    ASSERT_EQ(r, rr->rewrite(n));
  }
}

TEST_F(TestTheoryWhiteEvaluator, code)
{
  Node a = d_nodeManager->mkConst(String("A"));
  Node empty = d_nodeManager->mkConst(String(""));

  std::vector<Node> args;
  std::vector<Node> vals;
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  Evaluator eval(rr);

  // (str.code "A") ---> 65
  {
    Node n = d_nodeManager->mkNode(kind::STRING_TO_CODE, a);
    Node r = eval.eval(n, args, vals);
    ASSERT_EQ(r, d_nodeManager->mkConstInt(Rational(65)));
  }

  // (str.code "") ---> -1
  {
    Node n = d_nodeManager->mkNode(kind::STRING_TO_CODE, empty);
    Node r = eval.eval(n, args, vals);
    ASSERT_EQ(r, d_nodeManager->mkConstInt(Rational(-1)));
  }
}
}  // namespace test
}  // namespace cvc5::internal
