/*********************                                                        */
/*! \file theory_quantifiers_bv_instantiator_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Andres Noetzli, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Unit tests for BvInstantiator.
 **
 ** Unit tests for BvInstantiator.
 **/

#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/quantifiers/cegqi/ceg_bv_instantiator_utils.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"

#include <cxxtest/TestSuite.h>
#include <iostream>
#include <vector>

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::theory::quantifiers::utils;
using namespace CVC4::smt;

class BvInstantiatorWhite : public CxxTest::TestSuite
{
 public:
  void setUp() override;
  void tearDown() override;

  void testGetPvCoeff();
  void testNormalizePvMult();
  void testNormalizePvPlus();
  void testNormalizePvEqual();

 private:
  ExprManager* d_em;
  NodeManager* d_nm;
  SmtEngine* d_smt;
  SmtScope* d_scope;

  Node mkNeg(TNode n);
  Node mkMult(TNode a, TNode b);
  Node mkMult(const std::vector<Node>& children);
  Node mkPlus(TNode a, TNode b);
  Node mkPlus(const std::vector<Node>& children);
};

void BvInstantiatorWhite::setUp()
{
  d_em = new ExprManager();
  d_nm = NodeManager::fromExprManager(d_em);
  d_smt = new SmtEngine(d_em);
  d_scope = new SmtScope(d_smt);
  d_smt->finishInit();
}

void BvInstantiatorWhite::tearDown()
{
  delete d_scope;
  delete d_smt;
  delete d_em;
}

Node BvInstantiatorWhite::mkNeg(TNode n)
{
  return d_nm->mkNode(kind::BITVECTOR_NEG, n);
}

Node BvInstantiatorWhite::mkMult(TNode a, TNode b)
{
  return d_nm->mkNode(kind::BITVECTOR_MULT, a, b);
}

Node BvInstantiatorWhite::mkMult(const std::vector<Node>& children)
{
  return d_nm->mkNode(kind::BITVECTOR_MULT, children);
}

Node BvInstantiatorWhite::mkPlus(TNode a, TNode b)
{
  return d_nm->mkNode(kind::BITVECTOR_PLUS, a, b);
}

Node BvInstantiatorWhite::mkPlus(const std::vector<Node>& children)
{
  return d_nm->mkNode(kind::BITVECTOR_PLUS, children);
}

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
void BvInstantiatorWhite::testGetPvCoeff()
{
  Node x = mkVar(32);
  Node a = mkVar(32);
  Node one = mkOne(32);
  BvLinearAttribute is_linear;

  /* x -> 1 */
  Node coeff_x = getPvCoeff(x, x);
  TS_ASSERT(coeff_x == one);

  /* -x -> -1 */
  Node coeff_neg_x = getPvCoeff(x, mkNeg(x));
  TS_ASSERT(coeff_neg_x == mkNeg(one));

  /* x * a -> null (since x * a not a normalized) */
  Node x_mult_a = mkMult(x, a);
  Node coeff_x_mult_a = getPvCoeff(x, x_mult_a);
  TS_ASSERT(coeff_x_mult_a.isNull());

  /* x * a -> a */
  x_mult_a.setAttribute(is_linear, true);
  coeff_x_mult_a = getPvCoeff(x, x_mult_a);
  TS_ASSERT(coeff_x_mult_a == a);

  /* x * -a -> -a */
  Node x_mult_neg_a = mkMult(x, mkNeg(a));
  x_mult_neg_a.setAttribute(is_linear, true);
  Node coeff_x_mult_neg_a = getPvCoeff(x, x_mult_neg_a);
  TS_ASSERT(coeff_x_mult_neg_a == mkNeg(a));
}

void BvInstantiatorWhite::testNormalizePvMult()
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
  TS_ASSERT(norm_xx.isNull());

  /* nothing to normalize -> create a * a */
  Node norm_aa = normalizePvMult(x, {a, a}, contains_x);
  TS_ASSERT(norm_aa == Rewriter::rewrite(mkMult(a, a)));

  /* normalize x * a -> x * a */
  Node norm_xa = normalizePvMult(x, {x, a}, contains_x);
  TS_ASSERT(contains_x[norm_xa]);
  TS_ASSERT(norm_xa.getAttribute(is_linear));
  TS_ASSERT(norm_xa.getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_xa.getNumChildren() == 2);
  TS_ASSERT(norm_xa[0] == x);
  TS_ASSERT(norm_xa[1] == a);

  /* normalize a * x -> x * a */
  Node norm_ax = normalizePvMult(x, {a, x}, contains_x);
  TS_ASSERT(contains_x[norm_ax]);
  TS_ASSERT(norm_ax.getAttribute(is_linear));
  TS_ASSERT(norm_ax.getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_ax.getNumChildren() == 2);
  TS_ASSERT(norm_ax[0] == x);
  TS_ASSERT(norm_ax[1] == a);

  /* normalize a * -x -> x * -a */
  Node norm_neg_ax = normalizePvMult(x, {a, neg_x}, contains_x);
  TS_ASSERT(contains_x[norm_neg_ax]);
  TS_ASSERT(norm_neg_ax.getAttribute(is_linear));
  TS_ASSERT(norm_neg_ax.getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_neg_ax.getNumChildren() == 2);
  TS_ASSERT(norm_neg_ax[0] == x);
  TS_ASSERT(norm_neg_ax[1] == mkNeg(a));

  /* normalize 0 * x -> 0 */
  Node norm_zx = normalizePvMult(x, {zero, x}, contains_x);
  TS_ASSERT(norm_zx == zero);

  /* normalize 1 * x -> x */
  Node norm_ox = normalizePvMult(x, {one, x}, contains_x);
  TS_ASSERT(norm_ox == x);

  /* normalize a * b * c * x * d -> x * (a * b * c * d) */
  Node norm_abcxd = normalizePvMult(x, {a, b, c, x, d}, contains_x);
  TS_ASSERT(contains_x[norm_abcxd]);
  TS_ASSERT(norm_abcxd.getAttribute(is_linear));
  TS_ASSERT(norm_abcxd.getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_abcxd.getNumChildren() == 2);
  TS_ASSERT(norm_abcxd[0] == x);
  TS_ASSERT(norm_abcxd[1] == Rewriter::rewrite(mkMult({a, b, c, d})));

  /* normalize a * b * c * -x * d -> x * -(a * b * c * d) */
  Node norm_neg_abcxd = normalizePvMult(x, {a, b, c, neg_x, d}, contains_x);
  TS_ASSERT(contains_x[norm_neg_abcxd]);
  TS_ASSERT(norm_neg_abcxd.getAttribute(is_linear));
  TS_ASSERT(norm_neg_abcxd.getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_neg_abcxd.getNumChildren() == 2);
  TS_ASSERT(norm_neg_abcxd[0] == x);
  TS_ASSERT(norm_neg_abcxd[1]
            == mkNeg(Rewriter::rewrite(mkMult({a, b, c, d}))));

  /* normalize b * (x * a) -> x * (b * a) */
  Node norm_bxa = normalizePvMult(x, {b, norm_ax}, contains_x);
  TS_ASSERT(contains_x[norm_bxa]);
  TS_ASSERT(norm_bxa.getAttribute(is_linear));
  TS_ASSERT(norm_bxa.getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_bxa.getNumChildren() == 2);
  TS_ASSERT(norm_bxa[0] == x);
  TS_ASSERT(norm_bxa[1] == Rewriter::rewrite(mkMult(b, a)));

  /* normalize b * -(x * a) -> x * -(a * b) */
  Node neg_norm_ax = mkNeg(norm_ax);
  contains_x[neg_norm_ax] = true;
  Node norm_neg_bxa = normalizePvMult(x, {b, neg_norm_ax}, contains_x);
  TS_ASSERT(contains_x[norm_neg_bxa]);
  TS_ASSERT(norm_neg_bxa.getAttribute(is_linear));
  TS_ASSERT(norm_neg_bxa.getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_neg_bxa.getNumChildren() == 2);
  TS_ASSERT(norm_neg_bxa[0] == x);
  TS_ASSERT(norm_neg_bxa[1] == mkNeg(Rewriter::rewrite(mkMult(b, a))));
}

void BvInstantiatorWhite::testNormalizePvPlus()
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
  TS_ASSERT(norm_abx.isNull());

  /* nothing to normalize -> create a + a */
  Node norm_aa = normalizePvPlus(x, {a, a}, contains_x);
  TS_ASSERT(norm_aa == Rewriter::rewrite(mkPlus(a, a)));

  /* x + a -> x + a */
  Node norm_xa = normalizePvPlus(x, {x, a}, contains_x);
  TS_ASSERT(contains_x[norm_xa]);
  TS_ASSERT(norm_xa.getAttribute(is_linear));
  TS_ASSERT(norm_xa.getKind() == kind::BITVECTOR_PLUS);
  TS_ASSERT(norm_xa.getNumChildren() == 2);
  TS_ASSERT(norm_xa[0] == x);
  TS_ASSERT(norm_xa[1] == a);

  /* a * x -> x * a */
  Node norm_ax = normalizePvPlus(x, {a, x}, contains_x);
  TS_ASSERT(contains_x[norm_ax]);
  TS_ASSERT(norm_ax.getAttribute(is_linear));
  TS_ASSERT(norm_ax.getKind() == kind::BITVECTOR_PLUS);
  TS_ASSERT(norm_ax.getNumChildren() == 2);
  TS_ASSERT(norm_ax[0] == x);
  TS_ASSERT(norm_ax[1] == a);

  /* a + -x -> (x * -1) + a */
  Node norm_neg_ax = normalizePvPlus(x, {a, neg_x}, contains_x);
  TS_ASSERT(contains_x[norm_neg_ax]);
  TS_ASSERT(norm_neg_ax.getAttribute(is_linear));
  TS_ASSERT(norm_neg_ax.getKind() == kind::BITVECTOR_PLUS);
  TS_ASSERT(norm_neg_ax.getNumChildren() == 2);
  TS_ASSERT(norm_neg_ax[0].getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_neg_ax[0].getNumChildren() == 2);
  TS_ASSERT(norm_neg_ax[0].getAttribute(is_linear));
  TS_ASSERT(contains_x[norm_neg_ax[0]]);
  TS_ASSERT(norm_neg_ax[0][0] == x);
  TS_ASSERT(norm_neg_ax[0][1] == Rewriter::rewrite(mkNeg(one)));
  TS_ASSERT(norm_neg_ax[1] == a);

  /* -x + -a * x -> x * (-1 - a) */
  Node norm_xax = normalizePvPlus(
      x, {mkNeg(x), normalizePvMult(x, {mkNeg(a), x}, contains_x)}, contains_x);
  TS_ASSERT(contains_x[norm_xax]);
  TS_ASSERT(norm_xax.getAttribute(is_linear));
  TS_ASSERT(norm_xax.getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_xax.getNumChildren() == 2);
  TS_ASSERT(norm_xax[0] == x);
  TS_ASSERT(norm_xax[1] == Rewriter::rewrite(mkPlus(mkNeg(one), mkNeg(a))));

  /* a + b + c + x + d -> x + (a + b + c + d) */
  Node norm_abcxd = normalizePvPlus(x, {a, b, c, x, d}, contains_x);
  TS_ASSERT(contains_x[norm_abcxd]);
  TS_ASSERT(norm_abcxd.getAttribute(is_linear));
  TS_ASSERT(norm_abcxd.getKind() == kind::BITVECTOR_PLUS);
  TS_ASSERT(norm_abcxd.getNumChildren() == 2);
  TS_ASSERT(norm_abcxd[0] == x);
  TS_ASSERT(norm_abcxd[1] == Rewriter::rewrite(mkPlus({a, b, c, d})));

  /* a + b + c + -x + d -> (x * -1) + (a + b + c + d) */
  Node norm_neg_abcxd = normalizePvPlus(x, {a, b, c, neg_x, d}, contains_x);
  TS_ASSERT(contains_x[norm_neg_abcxd]);
  TS_ASSERT(norm_neg_abcxd.getAttribute(is_linear));
  TS_ASSERT(norm_neg_abcxd.getKind() == kind::BITVECTOR_PLUS);
  TS_ASSERT(norm_neg_abcxd.getNumChildren() == 2);
  TS_ASSERT(norm_neg_abcxd[0].getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_neg_abcxd[0].getNumChildren() == 2);
  TS_ASSERT(norm_neg_abcxd[0].getAttribute(is_linear));
  TS_ASSERT(contains_x[norm_neg_abcxd[0]]);
  TS_ASSERT(norm_neg_abcxd[0][0] == x);
  TS_ASSERT(norm_neg_abcxd[0][1] == Rewriter::rewrite(mkNeg(one)));
  TS_ASSERT(norm_neg_abcxd[1] == Rewriter::rewrite(mkPlus({a, b, c, d})));

  /* b + (x + a) -> x + (b + a) */
  Node norm_bxa = normalizePvPlus(x, {b, norm_ax}, contains_x);
  TS_ASSERT(contains_x[norm_bxa]);
  TS_ASSERT(norm_bxa.getAttribute(is_linear));
  TS_ASSERT(norm_bxa.getKind() == kind::BITVECTOR_PLUS);
  TS_ASSERT(norm_bxa.getNumChildren() == 2);
  TS_ASSERT(norm_bxa[0] == x);
  TS_ASSERT(norm_bxa[1] == Rewriter::rewrite(mkPlus(b, a)));

  /* b + -(x + a) -> (x * -1) + b - a */
  Node neg_norm_ax = mkNeg(norm_ax);
  contains_x[neg_norm_ax] = true;
  Node norm_neg_bxa = normalizePvPlus(x, {b, neg_norm_ax}, contains_x);
  TS_ASSERT(contains_x[norm_neg_bxa]);
  TS_ASSERT(norm_neg_bxa.getAttribute(is_linear));
  TS_ASSERT(norm_neg_bxa.getKind() == kind::BITVECTOR_PLUS);
  TS_ASSERT(norm_neg_bxa.getNumChildren() == 2);
  TS_ASSERT(norm_neg_abcxd[0].getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_neg_abcxd[0].getNumChildren() == 2);
  TS_ASSERT(norm_neg_abcxd[0].getAttribute(is_linear));
  TS_ASSERT(contains_x[norm_neg_abcxd[0]]);
  TS_ASSERT(norm_neg_abcxd[0][0] == x);
  TS_ASSERT(norm_neg_abcxd[0][1] == Rewriter::rewrite(mkNeg(one)));
  TS_ASSERT(norm_neg_bxa[1] == Rewriter::rewrite((mkPlus(b, mkNeg(a)))));

  /* -x + x + a -> a */
  Node norm_neg_xxa = normalizePvPlus(x, {neg_x, x, a}, contains_x);
  TS_ASSERT(!contains_x[norm_neg_xxa]);
  TS_ASSERT(norm_neg_xxa == a);
}

void BvInstantiatorWhite::testNormalizePvEqual()
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
  TS_ASSERT(norm_xa.isNull());

  /* x = x -> true */
  Node norm_xx = normalizePvEqual(x, {x, x}, contains_x);
  TS_ASSERT(norm_xx == ntrue);

  /* x = -x -> x * 2 = 0 */
  Node norm_neg_xx = normalizePvEqual(x, {x, neg_x}, contains_x);
  TS_ASSERT(norm_neg_xx.getKind() == kind::EQUAL);
  TS_ASSERT(norm_neg_xx[0].getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_neg_xx[0].getNumChildren() == 2);
  TS_ASSERT(norm_neg_xx[0].getAttribute(is_linear));
  TS_ASSERT(contains_x[norm_neg_xx[0]]);
  TS_ASSERT(norm_neg_xx[0][0] == x);
  TS_ASSERT(norm_neg_xx[0][1] == Rewriter::rewrite(mkConst(32, 2)));
  TS_ASSERT(norm_neg_xx[1] == zero);

  /* a + x = x -> 0 = -a */
  Node norm_axx = normalizePvEqual(
      x, {normalizePvPlus(x, {a, x}, contains_x), x}, contains_x);
  TS_ASSERT(norm_axx.getKind() == kind::EQUAL);
  TS_ASSERT(norm_axx[0] == zero);
  TS_ASSERT(norm_axx[1] == mkNeg(a));

  /* a + -x = x -> x * -2 = a */
  Node norm_neg_axx = normalizePvEqual(
      x, {normalizePvPlus(x, {a, neg_x}, contains_x), x}, contains_x);
  TS_ASSERT(norm_neg_axx.getKind() == kind::EQUAL);
  TS_ASSERT(norm_neg_axx[0].getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_neg_axx[0].getNumChildren() == 2);
  TS_ASSERT(norm_neg_axx[0].getAttribute(is_linear));
  TS_ASSERT(contains_x[norm_neg_axx[0]]);
  TS_ASSERT(norm_neg_axx[0][0] == x);
  TS_ASSERT(norm_neg_axx[0][1] == Rewriter::rewrite(mkNeg(mkConst(32, 2))));
  TS_ASSERT(norm_neg_axx[1] == mkNeg(a));

  /* a * x = x -> x * (a - 1) = 0 */
  Node norm_mult_axx = normalizePvEqual(
      x, {normalizePvMult(x, {a, x}, contains_x), x}, contains_x);
  TS_ASSERT(norm_mult_axx.getKind() == kind::EQUAL);
  TS_ASSERT(norm_mult_axx[0].getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_mult_axx[0].getNumChildren() == 2);
  TS_ASSERT(norm_mult_axx[0].getAttribute(is_linear));
  TS_ASSERT(contains_x[norm_mult_axx[0]]);
  TS_ASSERT(norm_mult_axx[0][0] == x);
  TS_ASSERT(norm_mult_axx[0][1] == Rewriter::rewrite(mkPlus(a, mkNeg(one))));
  TS_ASSERT(norm_mult_axx[1] == zero);

  /* a * x = x + b -> x * (a - 1) = b */
  Node norm_axxb = normalizePvEqual(x,
                                    {normalizePvMult(x, {a, x}, contains_x),
                                     normalizePvPlus(x, {b, x}, contains_x)},
                                    contains_x);
  TS_ASSERT(norm_axxb.getKind() == kind::EQUAL);
  TS_ASSERT(norm_axxb[0].getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_axxb[0].getNumChildren() == 2);
  TS_ASSERT(norm_axxb[0].getAttribute(is_linear));
  TS_ASSERT(contains_x[norm_axxb[0]]);
  TS_ASSERT(norm_axxb[0][0] == x);
  TS_ASSERT(norm_axxb[0][1] == Rewriter::rewrite(mkPlus(a, mkNeg(one))));
  TS_ASSERT(norm_axxb[1] == b);

  /* a * x + c = x -> x * (a - 1) = -c */
  Node norm_axcx = normalizePvEqual(
      x,
      {normalizePvPlus(
           x, {normalizePvMult(x, {a, x}, contains_x), c}, contains_x),
       x},
      contains_x);
  TS_ASSERT(norm_axcx.getKind() == kind::EQUAL);
  TS_ASSERT(norm_axcx[0].getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_axcx[0].getNumChildren() == 2);
  TS_ASSERT(norm_axcx[0].getAttribute(is_linear));
  TS_ASSERT(contains_x[norm_axcx[0]]);
  TS_ASSERT(norm_axcx[0][0] == x);
  TS_ASSERT(norm_axcx[0][1] == Rewriter::rewrite(mkPlus(a, mkNeg(one))));
  TS_ASSERT(norm_axcx[1] == mkNeg(c));

  /* a * x + c = x + b -> x * (a - 1) = b - c*/
  Node norm_axcxb = normalizePvEqual(
      x,
      {normalizePvPlus(
           x, {normalizePvMult(x, {a, x}, contains_x), c}, contains_x),
       normalizePvPlus(x, {b, x}, contains_x)},
      contains_x);
  TS_ASSERT(norm_axcxb.getKind() == kind::EQUAL);
  TS_ASSERT(norm_axcxb[0].getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_axcxb[0].getNumChildren() == 2);
  TS_ASSERT(norm_axcxb[0].getAttribute(is_linear));
  TS_ASSERT(contains_x[norm_axcxb[0]]);
  TS_ASSERT(norm_axcxb[0][0] == x);
  TS_ASSERT(norm_axcxb[0][1] == Rewriter::rewrite(mkPlus(a, mkNeg(one))));
  TS_ASSERT(norm_axcxb[1] == Rewriter::rewrite(mkPlus(b, mkNeg(c))));

  /* -(a + -x) = a * x -> x * (1 - a) = a */
  Node norm_axax =
      normalizePvEqual(x,
                       {mkNeg(normalizePvPlus(x, {a, neg_x}, contains_x)),
                        normalizePvMult(x, {a, x}, contains_x)},
                       contains_x);
  TS_ASSERT(norm_axax.getKind() == kind::EQUAL);
  TS_ASSERT(norm_axax[0].getKind() == kind::BITVECTOR_MULT);
  TS_ASSERT(norm_axax[0].getNumChildren() == 2);
  TS_ASSERT(norm_axax[0].getAttribute(is_linear));
  TS_ASSERT(contains_x[norm_axax[0]]);
  TS_ASSERT(norm_axax[0][0] == x);
  TS_ASSERT(norm_axax[0][1] == Rewriter::rewrite(mkPlus(one, mkNeg(a))));
  TS_ASSERT(norm_axax[1] == a);
}
