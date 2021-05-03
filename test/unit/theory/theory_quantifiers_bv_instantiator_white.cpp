/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mathias Preiner, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for BvInstantiator.
 */

#include <iostream>
#include <vector>

#include "expr/node.h"
#include "test_smt.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/quantifiers/cegqi/ceg_bv_instantiator_utils.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"

namespace cvc5 {

using namespace theory;
using namespace theory::bv;
using namespace theory::bv::utils;
using namespace theory::quantifiers;
using namespace theory::quantifiers::utils;

namespace test {

class TestTheoryWhiteyQuantifiersBvInstantiator : public TestSmt
{
 protected:
  Node mkNeg(TNode n) { return d_nodeManager->mkNode(kind::BITVECTOR_NEG, n); }

  Node mkMult(TNode a, TNode b)
  {
    return d_nodeManager->mkNode(kind::BITVECTOR_MULT, a, b);
  }

  Node mkMult(const std::vector<Node>& children)
  {
    return d_nodeManager->mkNode(kind::BITVECTOR_MULT, children);
  }

  Node mkPlus(TNode a, TNode b)
  {
    return d_nodeManager->mkNode(kind::BITVECTOR_PLUS, a, b);
  }

  Node mkPlus(const std::vector<Node>& children)
  {
    return d_nodeManager->mkNode(kind::BITVECTOR_PLUS, children);
  }
};

/**
 * getPvCoeff(x, n) should return
 *
 *  1           if n == x
 * -1           if n == -x
 *  a           if n == x * a
 * -a           if n == x * -a
 * Node::null() otherwise.
 *
 * Note that x * a and x * -a have to be normalized.
 */
TEST_F(TestTheoryWhiteyQuantifiersBvInstantiator, getPvCoeff)
{
  Node x = mkVar(32);
  Node a = mkVar(32);
  Node one = mkOne(32);
  BvLinearAttribute is_linear;

  /* x -> 1 */
  Node coeff_x = getPvCoeff(x, x);
  ASSERT_EQ(coeff_x, one);

  /* -x -> -1 */
  Node coeff_neg_x = getPvCoeff(x, mkNeg(x));
  ASSERT_EQ(coeff_neg_x, mkNeg(one));

  /* x * a -> null (since x * a not a normalized) */
  Node x_mult_a = mkMult(x, a);
  Node coeff_x_mult_a = getPvCoeff(x, x_mult_a);
  ASSERT_TRUE(coeff_x_mult_a.isNull());

  /* x * a -> a */
  x_mult_a.setAttribute(is_linear, true);
  coeff_x_mult_a = getPvCoeff(x, x_mult_a);
  ASSERT_EQ(coeff_x_mult_a, a);

  /* x * -a -> -a */
  Node x_mult_neg_a = mkMult(x, mkNeg(a));
  x_mult_neg_a.setAttribute(is_linear, true);
  Node coeff_x_mult_neg_a = getPvCoeff(x, x_mult_neg_a);
  ASSERT_EQ(coeff_x_mult_neg_a, mkNeg(a));
}

TEST_F(TestTheoryWhiteyQuantifiersBvInstantiator, normalizePvMult)
{
  Node x = mkVar(32);
  Node neg_x = mkNeg(x);
  Node a = mkVar(32);
  Node b = mkVar(32);
  Node c = mkVar(32);
  Node d = mkVar(32);
  Node zero = mkZero(32);
  Node one = mkOne(32);
  BvLinearAttribute is_linear;
  std::unordered_map<Node, bool, NodeHashFunction> contains_x;

  contains_x[x] = true;
  contains_x[neg_x] = true;

  /* x * -x -> null (since non linear) */
  Node norm_xx = normalizePvMult(x, {x, neg_x}, contains_x);
  ASSERT_TRUE(norm_xx.isNull());

  /* nothing to normalize -> create a * a */
  Node norm_aa = normalizePvMult(x, {a, a}, contains_x);
  ASSERT_EQ(norm_aa, Rewriter::rewrite(mkMult(a, a)));

  /* normalize x * a -> x * a */
  Node norm_xa = normalizePvMult(x, {x, a}, contains_x);
  ASSERT_TRUE(contains_x[norm_xa]);
  ASSERT_TRUE(norm_xa.getAttribute(is_linear));
  ASSERT_EQ(norm_xa.getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_xa.getNumChildren(), 2);
  ASSERT_EQ(norm_xa[0], x);
  ASSERT_EQ(norm_xa[1], a);

  /* normalize a * x -> x * a */
  Node norm_ax = normalizePvMult(x, {a, x}, contains_x);
  ASSERT_TRUE(contains_x[norm_ax]);
  ASSERT_TRUE(norm_ax.getAttribute(is_linear));
  ASSERT_EQ(norm_ax.getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_ax.getNumChildren(), 2);
  ASSERT_EQ(norm_ax[0], x);
  ASSERT_EQ(norm_ax[1], a);

  /* normalize a * -x -> x * -a */
  Node norm_neg_ax = normalizePvMult(x, {a, neg_x}, contains_x);
  ASSERT_TRUE(contains_x[norm_neg_ax]);
  ASSERT_TRUE(norm_neg_ax.getAttribute(is_linear));
  ASSERT_EQ(norm_neg_ax.getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_neg_ax.getNumChildren(), 2);
  ASSERT_EQ(norm_neg_ax[0], x);
  ASSERT_EQ(norm_neg_ax[1], mkNeg(a));

  /* normalize 0 * x -> 0 */
  Node norm_zx = normalizePvMult(x, {zero, x}, contains_x);
  ASSERT_EQ(norm_zx, zero);

  /* normalize 1 * x -> x */
  Node norm_ox = normalizePvMult(x, {one, x}, contains_x);
  ASSERT_EQ(norm_ox, x);

  /* normalize a * b * c * x * d -> x * (a * b * c * d) */
  Node norm_abcxd = normalizePvMult(x, {a, b, c, x, d}, contains_x);
  ASSERT_TRUE(contains_x[norm_abcxd]);
  ASSERT_TRUE(norm_abcxd.getAttribute(is_linear));
  ASSERT_EQ(norm_abcxd.getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_abcxd.getNumChildren(), 2);
  ASSERT_EQ(norm_abcxd[0], x);
  ASSERT_EQ(norm_abcxd[1], Rewriter::rewrite(mkMult({a, b, c, d})));

  /* normalize a * b * c * -x * d -> x * -(a * b * c * d) */
  Node norm_neg_abcxd = normalizePvMult(x, {a, b, c, neg_x, d}, contains_x);
  ASSERT_TRUE(contains_x[norm_neg_abcxd]);
  ASSERT_TRUE(norm_neg_abcxd.getAttribute(is_linear));
  ASSERT_EQ(norm_neg_abcxd.getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_neg_abcxd.getNumChildren(), 2);
  ASSERT_EQ(norm_neg_abcxd[0], x);
  ASSERT_TRUE(norm_neg_abcxd[1]
              == mkNeg(Rewriter::rewrite(mkMult({a, b, c, d}))));

  /* normalize b * (x * a) -> x * (b * a) */
  Node norm_bxa = normalizePvMult(x, {b, norm_ax}, contains_x);
  ASSERT_TRUE(contains_x[norm_bxa]);
  ASSERT_TRUE(norm_bxa.getAttribute(is_linear));
  ASSERT_EQ(norm_bxa.getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_bxa.getNumChildren(), 2);
  ASSERT_EQ(norm_bxa[0], x);
  ASSERT_EQ(norm_bxa[1], Rewriter::rewrite(mkMult(b, a)));

  /* normalize b * -(x * a) -> x * -(a * b) */
  Node neg_norm_ax = mkNeg(norm_ax);
  contains_x[neg_norm_ax] = true;
  Node norm_neg_bxa = normalizePvMult(x, {b, neg_norm_ax}, contains_x);
  ASSERT_TRUE(contains_x[norm_neg_bxa]);
  ASSERT_TRUE(norm_neg_bxa.getAttribute(is_linear));
  ASSERT_EQ(norm_neg_bxa.getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_neg_bxa.getNumChildren(), 2);
  ASSERT_EQ(norm_neg_bxa[0], x);
  ASSERT_EQ(norm_neg_bxa[1], mkNeg(Rewriter::rewrite(mkMult(b, a))));
}

TEST_F(TestTheoryWhiteyQuantifiersBvInstantiator, normalizePvPlus)
{
  Node one = mkOne(32);
  Node x = mkVar(32);
  Node neg_x = mkNeg(x);
  Node a = mkVar(32);
  Node b = mkVar(32);
  Node c = mkVar(32);
  Node d = mkVar(32);
  BvLinearAttribute is_linear;
  std::unordered_map<Node, bool, NodeHashFunction> contains_x;

  contains_x[x] = true;
  contains_x[neg_x] = true;

  /* a + b * x -> null (since b * x not normalized) */
  Node mult_bx = mkMult(b, x);
  contains_x[mult_bx] = true;
  Node norm_abx = normalizePvPlus(x, {a, mult_bx}, contains_x);
  ASSERT_TRUE(norm_abx.isNull());

  /* nothing to normalize -> create a + a */
  Node norm_aa = normalizePvPlus(x, {a, a}, contains_x);
  ASSERT_EQ(norm_aa, Rewriter::rewrite(mkPlus(a, a)));

  /* x + a -> x + a */
  Node norm_xa = normalizePvPlus(x, {x, a}, contains_x);
  ASSERT_TRUE(contains_x[norm_xa]);
  ASSERT_TRUE(norm_xa.getAttribute(is_linear));
  ASSERT_EQ(norm_xa.getKind(), kind::BITVECTOR_PLUS);
  ASSERT_EQ(norm_xa.getNumChildren(), 2);
  ASSERT_EQ(norm_xa[0], x);
  ASSERT_EQ(norm_xa[1], a);

  /* a * x -> x * a */
  Node norm_ax = normalizePvPlus(x, {a, x}, contains_x);
  ASSERT_TRUE(contains_x[norm_ax]);
  ASSERT_TRUE(norm_ax.getAttribute(is_linear));
  ASSERT_EQ(norm_ax.getKind(), kind::BITVECTOR_PLUS);
  ASSERT_EQ(norm_ax.getNumChildren(), 2);
  ASSERT_EQ(norm_ax[0], x);
  ASSERT_EQ(norm_ax[1], a);

  /* a + -x -> (x * -1) + a */
  Node norm_neg_ax = normalizePvPlus(x, {a, neg_x}, contains_x);
  ASSERT_TRUE(contains_x[norm_neg_ax]);
  ASSERT_TRUE(norm_neg_ax.getAttribute(is_linear));
  ASSERT_EQ(norm_neg_ax.getKind(), kind::BITVECTOR_PLUS);
  ASSERT_EQ(norm_neg_ax.getNumChildren(), 2);
  ASSERT_EQ(norm_neg_ax[0].getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_neg_ax[0].getNumChildren(), 2);
  ASSERT_TRUE(norm_neg_ax[0].getAttribute(is_linear));
  ASSERT_TRUE(contains_x[norm_neg_ax[0]]);
  ASSERT_EQ(norm_neg_ax[0][0], x);
  ASSERT_EQ(norm_neg_ax[0][1], Rewriter::rewrite(mkNeg(one)));
  ASSERT_EQ(norm_neg_ax[1], a);

  /* -x + -a * x -> x * (-1 - a) */
  Node norm_xax = normalizePvPlus(
      x, {mkNeg(x), normalizePvMult(x, {mkNeg(a), x}, contains_x)}, contains_x);
  ASSERT_TRUE(contains_x[norm_xax]);
  ASSERT_TRUE(norm_xax.getAttribute(is_linear));
  ASSERT_EQ(norm_xax.getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_xax.getNumChildren(), 2);
  ASSERT_EQ(norm_xax[0], x);
  ASSERT_EQ(norm_xax[1], Rewriter::rewrite(mkPlus(mkNeg(one), mkNeg(a))));

  /* a + b + c + x + d -> x + (a + b + c + d) */
  Node norm_abcxd = normalizePvPlus(x, {a, b, c, x, d}, contains_x);
  ASSERT_TRUE(contains_x[norm_abcxd]);
  ASSERT_TRUE(norm_abcxd.getAttribute(is_linear));
  ASSERT_EQ(norm_abcxd.getKind(), kind::BITVECTOR_PLUS);
  ASSERT_EQ(norm_abcxd.getNumChildren(), 2);
  ASSERT_EQ(norm_abcxd[0], x);
  ASSERT_EQ(norm_abcxd[1], Rewriter::rewrite(mkPlus({a, b, c, d})));

  /* a + b + c + -x + d -> (x * -1) + (a + b + c + d) */
  Node norm_neg_abcxd = normalizePvPlus(x, {a, b, c, neg_x, d}, contains_x);
  ASSERT_TRUE(contains_x[norm_neg_abcxd]);
  ASSERT_TRUE(norm_neg_abcxd.getAttribute(is_linear));
  ASSERT_EQ(norm_neg_abcxd.getKind(), kind::BITVECTOR_PLUS);
  ASSERT_EQ(norm_neg_abcxd.getNumChildren(), 2);
  ASSERT_EQ(norm_neg_abcxd[0].getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_neg_abcxd[0].getNumChildren(), 2);
  ASSERT_TRUE(norm_neg_abcxd[0].getAttribute(is_linear));
  ASSERT_TRUE(contains_x[norm_neg_abcxd[0]]);
  ASSERT_EQ(norm_neg_abcxd[0][0], x);
  ASSERT_EQ(norm_neg_abcxd[0][1], Rewriter::rewrite(mkNeg(one)));
  ASSERT_EQ(norm_neg_abcxd[1], Rewriter::rewrite(mkPlus({a, b, c, d})));

  /* b + (x + a) -> x + (b + a) */
  Node norm_bxa = normalizePvPlus(x, {b, norm_ax}, contains_x);
  ASSERT_TRUE(contains_x[norm_bxa]);
  ASSERT_TRUE(norm_bxa.getAttribute(is_linear));
  ASSERT_EQ(norm_bxa.getKind(), kind::BITVECTOR_PLUS);
  ASSERT_EQ(norm_bxa.getNumChildren(), 2);
  ASSERT_EQ(norm_bxa[0], x);
  ASSERT_EQ(norm_bxa[1], Rewriter::rewrite(mkPlus(b, a)));

  /* b + -(x + a) -> (x * -1) + b - a */
  Node neg_norm_ax = mkNeg(norm_ax);
  contains_x[neg_norm_ax] = true;
  Node norm_neg_bxa = normalizePvPlus(x, {b, neg_norm_ax}, contains_x);
  ASSERT_TRUE(contains_x[norm_neg_bxa]);
  ASSERT_TRUE(norm_neg_bxa.getAttribute(is_linear));
  ASSERT_EQ(norm_neg_bxa.getKind(), kind::BITVECTOR_PLUS);
  ASSERT_EQ(norm_neg_bxa.getNumChildren(), 2);
  ASSERT_EQ(norm_neg_abcxd[0].getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_neg_abcxd[0].getNumChildren(), 2);
  ASSERT_TRUE(norm_neg_abcxd[0].getAttribute(is_linear));
  ASSERT_TRUE(contains_x[norm_neg_abcxd[0]]);
  ASSERT_EQ(norm_neg_abcxd[0][0], x);
  ASSERT_EQ(norm_neg_abcxd[0][1], Rewriter::rewrite(mkNeg(one)));
  ASSERT_EQ(norm_neg_bxa[1], Rewriter::rewrite((mkPlus(b, mkNeg(a)))));

  /* -x + x + a -> a */
  Node norm_neg_xxa = normalizePvPlus(x, {neg_x, x, a}, contains_x);
  ASSERT_FALSE(contains_x[norm_neg_xxa]);
  ASSERT_EQ(norm_neg_xxa, a);
}

TEST_F(TestTheoryWhiteyQuantifiersBvInstantiator, normalizePvEqual)
{
  Node x = mkVar(32);
  Node neg_x = mkNeg(x);
  Node a = mkVar(32);
  Node b = mkVar(32);
  Node c = mkVar(32);
  Node d = mkVar(32);
  Node zero = mkZero(32);
  Node one = mkOne(32);
  Node ntrue = mkTrue();
  BvLinearAttribute is_linear;
  std::unordered_map<Node, bool, NodeHashFunction> contains_x;

  contains_x[x] = true;
  contains_x[neg_x] = true;

  /* x = a -> null (nothing to normalize) */
  Node norm_xa = normalizePvEqual(x, {x, a}, contains_x);
  ASSERT_TRUE(norm_xa.isNull());

  /* x = x -> true */
  Node norm_xx = normalizePvEqual(x, {x, x}, contains_x);
  ASSERT_EQ(norm_xx, ntrue);

  /* x = -x -> x * 2 = 0 */
  Node norm_neg_xx = normalizePvEqual(x, {x, neg_x}, contains_x);
  ASSERT_EQ(norm_neg_xx.getKind(), kind::EQUAL);
  ASSERT_EQ(norm_neg_xx[0].getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_neg_xx[0].getNumChildren(), 2);
  ASSERT_TRUE(norm_neg_xx[0].getAttribute(is_linear));
  ASSERT_TRUE(contains_x[norm_neg_xx[0]]);
  ASSERT_EQ(norm_neg_xx[0][0], x);
  ASSERT_EQ(norm_neg_xx[0][1], Rewriter::rewrite(mkConst(32, 2)));
  ASSERT_EQ(norm_neg_xx[1], zero);

  /* a + x = x -> 0 = -a */
  Node norm_axx = normalizePvEqual(
      x, {normalizePvPlus(x, {a, x}, contains_x), x}, contains_x);
  ASSERT_EQ(norm_axx.getKind(), kind::EQUAL);
  ASSERT_EQ(norm_axx[0], zero);
  ASSERT_EQ(norm_axx[1], mkNeg(a));

  /* a + -x = x -> x * -2 = a */
  Node norm_neg_axx = normalizePvEqual(
      x, {normalizePvPlus(x, {a, neg_x}, contains_x), x}, contains_x);
  ASSERT_EQ(norm_neg_axx.getKind(), kind::EQUAL);
  ASSERT_EQ(norm_neg_axx[0].getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_neg_axx[0].getNumChildren(), 2);
  ASSERT_TRUE(norm_neg_axx[0].getAttribute(is_linear));
  ASSERT_TRUE(contains_x[norm_neg_axx[0]]);
  ASSERT_EQ(norm_neg_axx[0][0], x);
  ASSERT_EQ(norm_neg_axx[0][1], Rewriter::rewrite(mkNeg(mkConst(32, 2))));
  ASSERT_EQ(norm_neg_axx[1], mkNeg(a));

  /* a * x = x -> x * (a - 1) = 0 */
  Node norm_mult_axx = normalizePvEqual(
      x, {normalizePvMult(x, {a, x}, contains_x), x}, contains_x);
  ASSERT_EQ(norm_mult_axx.getKind(), kind::EQUAL);
  ASSERT_EQ(norm_mult_axx[0].getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_mult_axx[0].getNumChildren(), 2);
  ASSERT_TRUE(norm_mult_axx[0].getAttribute(is_linear));
  ASSERT_TRUE(contains_x[norm_mult_axx[0]]);
  ASSERT_EQ(norm_mult_axx[0][0], x);
  ASSERT_EQ(norm_mult_axx[0][1], Rewriter::rewrite(mkPlus(a, mkNeg(one))));
  ASSERT_EQ(norm_mult_axx[1], zero);

  /* a * x = x + b -> x * (a - 1) = b */
  Node norm_axxb = normalizePvEqual(x,
                                    {normalizePvMult(x, {a, x}, contains_x),
                                     normalizePvPlus(x, {b, x}, contains_x)},
                                    contains_x);
  ASSERT_EQ(norm_axxb.getKind(), kind::EQUAL);
  ASSERT_EQ(norm_axxb[0].getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_axxb[0].getNumChildren(), 2);
  ASSERT_TRUE(norm_axxb[0].getAttribute(is_linear));
  ASSERT_TRUE(contains_x[norm_axxb[0]]);
  ASSERT_EQ(norm_axxb[0][0], x);
  ASSERT_EQ(norm_axxb[0][1], Rewriter::rewrite(mkPlus(a, mkNeg(one))));
  ASSERT_EQ(norm_axxb[1], b);

  /* a * x + c = x -> x * (a - 1) = -c */
  Node norm_axcx = normalizePvEqual(
      x,
      {normalizePvPlus(
           x, {normalizePvMult(x, {a, x}, contains_x), c}, contains_x),
       x},
      contains_x);
  ASSERT_EQ(norm_axcx.getKind(), kind::EQUAL);
  ASSERT_EQ(norm_axcx[0].getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_axcx[0].getNumChildren(), 2);
  ASSERT_TRUE(norm_axcx[0].getAttribute(is_linear));
  ASSERT_TRUE(contains_x[norm_axcx[0]]);
  ASSERT_EQ(norm_axcx[0][0], x);
  ASSERT_EQ(norm_axcx[0][1], Rewriter::rewrite(mkPlus(a, mkNeg(one))));
  ASSERT_EQ(norm_axcx[1], mkNeg(c));

  /* a * x + c = x + b -> x * (a - 1) = b - c*/
  Node norm_axcxb = normalizePvEqual(
      x,
      {normalizePvPlus(
           x, {normalizePvMult(x, {a, x}, contains_x), c}, contains_x),
       normalizePvPlus(x, {b, x}, contains_x)},
      contains_x);
  ASSERT_EQ(norm_axcxb.getKind(), kind::EQUAL);
  ASSERT_EQ(norm_axcxb[0].getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_axcxb[0].getNumChildren(), 2);
  ASSERT_TRUE(norm_axcxb[0].getAttribute(is_linear));
  ASSERT_TRUE(contains_x[norm_axcxb[0]]);
  ASSERT_EQ(norm_axcxb[0][0], x);
  ASSERT_EQ(norm_axcxb[0][1], Rewriter::rewrite(mkPlus(a, mkNeg(one))));
  ASSERT_EQ(norm_axcxb[1], Rewriter::rewrite(mkPlus(b, mkNeg(c))));

  /* -(a + -x) = a * x -> x * (1 - a) = a */
  Node norm_axax =
      normalizePvEqual(x,
                       {mkNeg(normalizePvPlus(x, {a, neg_x}, contains_x)),
                        normalizePvMult(x, {a, x}, contains_x)},
                       contains_x);
  ASSERT_EQ(norm_axax.getKind(), kind::EQUAL);
  ASSERT_EQ(norm_axax[0].getKind(), kind::BITVECTOR_MULT);
  ASSERT_EQ(norm_axax[0].getNumChildren(), 2);
  ASSERT_TRUE(norm_axax[0].getAttribute(is_linear));
  ASSERT_TRUE(contains_x[norm_axax[0]]);
  ASSERT_EQ(norm_axax[0][0], x);
  ASSERT_EQ(norm_axax[0][1], Rewriter::rewrite(mkPlus(one, mkNeg(a))));
  ASSERT_EQ(norm_axax[1], a);
}
}  // namespace test
}  // namespace cvc5
