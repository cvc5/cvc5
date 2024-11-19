/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for BV inverter.
 */

#include "expr/node.h"
#include "test_smt.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/quantifiers/bv_inverter_utils.h"
#include "util/result.h"

namespace cvc5::internal {

using namespace theory;
using namespace theory::quantifiers;
using namespace theory::quantifiers::utils;

namespace test {

class TestTheoryWhiteQuantifiersBvInverter : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_slvEngine->setOption("cegqi-full", "true");
    d_slvEngine->setOption("produce-models", "true");
    d_slvEngine->finishInit();

    d_s = d_nodeManager->mkVar("s", d_nodeManager->mkBitVectorType(4));
    d_t = d_nodeManager->mkVar("t", d_nodeManager->mkBitVectorType(4));
    d_sk = d_skolemManager->mkDummySkolem("sk", d_t.getType());
    d_x = d_nodeManager->mkBoundVar(d_t.getType());
    d_bvarlist = d_nodeManager->mkNode(Kind::BOUND_VAR_LIST, {d_x});
  }

  void runTestPred(bool pol,
                   Kind k,
                   Node x,
                   Node (*getic)(bool, Kind, Node, Node))
  {
    ASSERT_TRUE(k == Kind::BITVECTOR_ULT || k == Kind::BITVECTOR_SLT
                || k == Kind::EQUAL || k == Kind::BITVECTOR_UGT
                || k == Kind::BITVECTOR_SGT);
    ASSERT_TRUE(k != Kind::EQUAL || pol == false);

    Node sc = getic(pol, k, d_sk, d_t);
    Kind ksc = sc.getKind();
    ASSERT_TRUE((k == Kind::BITVECTOR_ULT && pol == false)
                || (k == Kind::BITVECTOR_SLT && pol == false)
                || (k == Kind::BITVECTOR_UGT && pol == false)
                || (k == Kind::BITVECTOR_SGT && pol == false)
                || ksc == Kind::IMPLIES);
    Node scl = ksc == Kind::IMPLIES ? sc[0] : bv::utils::mkTrue();
    if (!pol)
    {
      if (k == Kind::BITVECTOR_ULT)
      {
        k = Kind::BITVECTOR_UGE;
      }
      else if (k == Kind::BITVECTOR_UGT)
      {
        k = Kind::BITVECTOR_ULE;
      }
      else if (k == Kind::BITVECTOR_SLT)
      {
        k = Kind::BITVECTOR_SGE;
      }
      else if (k == Kind::BITVECTOR_SGT)
      {
        k = Kind::BITVECTOR_ULE;
      }
      else
      {
        ASSERT_TRUE(k == Kind::EQUAL);
        k = Kind::DISTINCT;
      }
    }
    Node body = d_nodeManager->mkNode(k, x, d_t);
    Node scr = d_nodeManager->mkNode(Kind::EXISTS, d_bvarlist, body);
    Node a = d_nodeManager->mkNode(Kind::DISTINCT, scl, scr);
    Result res = d_slvEngine->checkSat(a);
    ASSERT_EQ(res.getStatus(), Result::UNSAT);
  }

  void runTest(bool pol,
               Kind litk,
               Kind k,
               unsigned idx,
               Node (*getsc)(bool, Kind, Kind, unsigned, Node, Node, Node))
  {
    ASSERT_TRUE(k == Kind::BITVECTOR_MULT || k == Kind::BITVECTOR_UREM
                || k == Kind::BITVECTOR_UDIV || k == Kind::BITVECTOR_AND
                || k == Kind::BITVECTOR_OR || k == Kind::BITVECTOR_LSHR
                || k == Kind::BITVECTOR_ASHR || k == Kind::BITVECTOR_SHL);

    Node sc = getsc(pol, litk, k, idx, d_sk, d_s, d_t);
    ASSERT_FALSE(sc.isNull());
    Kind ksc = sc.getKind();
    ASSERT_TRUE((k == Kind::BITVECTOR_UDIV && idx == 1 && pol == false)
                || (k == Kind::BITVECTOR_ASHR && idx == 0 && pol == false)
                || ksc == Kind::IMPLIES);
    Node scl = ksc == Kind::IMPLIES ? sc[0] : bv::utils::mkTrue();
    Node body = idx == 0 ? d_nodeManager->mkNode(
                    litk, d_nodeManager->mkNode(k, d_x, d_s), d_t)
                         : d_nodeManager->mkNode(
                             litk, d_nodeManager->mkNode(k, d_s, d_x), d_t);
    Node scr = d_nodeManager->mkNode(
        Kind::EXISTS, d_bvarlist, pol ? body : body.notNode());
    Node a = d_nodeManager->mkNode(Kind::DISTINCT, scl, scr);
    Result res = d_slvEngine->checkSat(a);
    if (res.getStatus() == Result::SAT)
    {
      std::cout << std::endl;
      std::cout << "s " << d_slvEngine->getValue(d_s) << std::endl;
      std::cout << "t " << d_slvEngine->getValue(d_t) << std::endl;
      std::cout << "x " << d_slvEngine->getValue(d_x) << std::endl;
    }
    ASSERT_EQ(res.getStatus(), Result::UNSAT);
  }

  void runTestConcat(bool pol, Kind litk, unsigned idx)
  {
    Node s1, s2, sv_t;
    Node x, t, sk;
    Node sc;

    if (idx == 0)
    {
      s2 = d_nodeManager->mkVar("s2", d_nodeManager->mkBitVectorType(4));
      x = d_nodeManager->mkBoundVar(s2.getType());
      sk = d_skolemManager->mkDummySkolem("sk", s2.getType());
      t = d_nodeManager->mkVar("t", d_nodeManager->mkBitVectorType(8));
      sv_t = d_nodeManager->mkNode(Kind::BITVECTOR_CONCAT, x, s2);
      sc = getICBvConcat(pol, litk, 0, sk, sv_t, t);
    }
    else if (idx == 1)
    {
      s1 = d_nodeManager->mkVar("s1", d_nodeManager->mkBitVectorType(4));
      x = d_nodeManager->mkBoundVar(s1.getType());
      sk = d_skolemManager->mkDummySkolem("sk", s1.getType());
      t = d_nodeManager->mkVar("t", d_nodeManager->mkBitVectorType(8));
      sv_t = d_nodeManager->mkNode(Kind::BITVECTOR_CONCAT, s1, x);
      sc = getICBvConcat(pol, litk, 1, sk, sv_t, t);
    }
    else
    {
      ASSERT_TRUE(idx == 2);
      s1 = d_nodeManager->mkVar("s1", d_nodeManager->mkBitVectorType(4));
      s2 = d_nodeManager->mkVar("s2", d_nodeManager->mkBitVectorType(4));
      x = d_nodeManager->mkBoundVar(s2.getType());
      sk = d_skolemManager->mkDummySkolem("sk", s1.getType());
      t = d_nodeManager->mkVar("t", d_nodeManager->mkBitVectorType(12));
      sv_t = d_nodeManager->mkNode(Kind::BITVECTOR_CONCAT, s1, x, s2);
      sc = getICBvConcat(pol, litk, 1, sk, sv_t, t);
    }

    ASSERT_FALSE(sc.isNull());
    Kind ksc = sc.getKind();
    ASSERT_TRUE((litk == Kind::EQUAL && pol == false) || ksc == Kind::IMPLIES);
    Node scl = ksc == Kind::IMPLIES ? sc[0] : bv::utils::mkTrue();
    Node body = d_nodeManager->mkNode(litk, sv_t, t);
    Node bvarlist = d_nodeManager->mkNode(Kind::BOUND_VAR_LIST, {x});
    Node scr = d_nodeManager->mkNode(
        Kind::EXISTS, bvarlist, pol ? body : body.notNode());
    Node a = d_nodeManager->mkNode(Kind::DISTINCT, scl, scr);
    Result res = d_slvEngine->checkSat(a);
    if (res.getStatus() == Result::SAT)
    {
      std::cout << std::endl;
      if (!s1.isNull())
        std::cout << "s1 " << d_slvEngine->getValue(s1) << std::endl;
      if (!s2.isNull())
        std::cout << "s2 " << d_slvEngine->getValue(s2) << std::endl;
      std::cout << "t " << d_slvEngine->getValue(t) << std::endl;
      std::cout << "x " << d_slvEngine->getValue(x) << std::endl;
    }
    ASSERT_TRUE(res.getStatus() == Result::UNSAT);
  }

  void runTestSext(bool pol, Kind litk)
  {
    unsigned ws = 3;
    unsigned wx = 5;
    unsigned w = 8;

    Node x = d_nodeManager->mkVar("x", d_nodeManager->mkBitVectorType(wx));
    Node sk = d_skolemManager->mkDummySkolem("sk", x.getType());
    x = d_nodeManager->mkBoundVar(x.getType());

    Node t = d_nodeManager->mkVar("t", d_nodeManager->mkBitVectorType(w));
    Node sv_t = bv::utils::mkSignExtend(x, ws);
    Node sc = getICBvSext(pol, litk, 0, sk, sv_t, t);

    ASSERT_FALSE(sc.isNull());
    Kind ksc = sc.getKind();
    ASSERT_TRUE((litk == Kind::EQUAL && pol == false)
                || (litk == Kind::BITVECTOR_ULT && pol == false)
                || (litk == Kind::BITVECTOR_UGT && pol == false)
                || ksc == Kind::IMPLIES);
    Node scl = ksc == Kind::IMPLIES ? sc[0] : bv::utils::mkTrue();
    Node body = d_nodeManager->mkNode(litk, sv_t, t);
    Node bvarlist = d_nodeManager->mkNode(Kind::BOUND_VAR_LIST, {x});
    Node scr = d_nodeManager->mkNode(
        Kind::EXISTS, bvarlist, pol ? body : body.notNode());
    Node a = d_nodeManager->mkNode(Kind::DISTINCT, scl, scr);
    Result res = d_slvEngine->checkSat(a);
    if (res.getStatus() == Result::SAT)
    {
      std::cout << std::endl;
      std::cout << "t " << d_slvEngine->getValue(t) << std::endl;
      std::cout << "x " << d_slvEngine->getValue(x) << std::endl;
    }
    ASSERT_TRUE(res.getStatus() == Result::UNSAT);
  }

  Node d_s;
  Node d_t;
  Node d_sk;
  Node d_x;
  Node d_bvarlist;
};

/* Generic invertibility conditions for LT ---------------------------------  */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ult_true)
{
  runTestPred(true, Kind::BITVECTOR_ULT, d_x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ult_false)
{
  runTestPred(false, Kind::BITVECTOR_ULT, d_x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ugt_true)
{
  runTestPred(true, Kind::BITVECTOR_UGT, d_x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ugt_false)
{
  runTestPred(false, Kind::BITVECTOR_UGT, d_x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_slt_true)
{
  runTestPred(true, Kind::BITVECTOR_SLT, d_x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_slt_false)
{
  runTestPred(false, Kind::BITVECTOR_SLT, d_x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_sgt_true)
{
  runTestPred(true, Kind::BITVECTOR_SGT, d_x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, test_getIC_bv_sgt_false)
{
  runTestPred(false, Kind::BITVECTOR_SGT, d_x, getICBvSltSgt);
}

/* Equality and Disequality   ----------------------------------------------  */

/* Mult */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_eq_true0)
{
  runTest(true, Kind::EQUAL, Kind::BITVECTOR_MULT, 0, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_eq_trueu)
{
  runTest(true, Kind::EQUAL, Kind::BITVECTOR_MULT, 1, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_eq_false0)
{
  runTest(false, Kind::EQUAL, Kind::BITVECTOR_MULT, 0, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_eq_false1)
{
  runTest(false, Kind::EQUAL, Kind::BITVECTOR_MULT, 1, getICBvMult);
}

/* Urem */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_eq_true0)
{
  runTest(true, Kind::EQUAL, Kind::BITVECTOR_UREM, 0, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_eq_true1)
{
  runTest(true, Kind::EQUAL, Kind::BITVECTOR_UREM, 1, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_eq_false0)
{
  runTest(false, Kind::EQUAL, Kind::BITVECTOR_UREM, 0, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_eq_false1)
{
  runTest(false, Kind::EQUAL, Kind::BITVECTOR_UREM, 1, getICBvUrem);
}

/* Udiv */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_eq_true0)
{
  runTest(true, Kind::EQUAL, Kind::BITVECTOR_UDIV, 0, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_eq_true1)
{
  runTest(true, Kind::EQUAL, Kind::BITVECTOR_UDIV, 1, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_eq_false0)
{
  runTest(false, Kind::EQUAL, Kind::BITVECTOR_UDIV, 0, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_eq_false1)
{
  runTest(false, Kind::EQUAL, Kind::BITVECTOR_UDIV, 1, getICBvUdiv);
}

/* And */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_eq_true0)
{
  runTest(true, Kind::EQUAL, Kind::BITVECTOR_AND, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_eq_true1)
{
  runTest(true, Kind::EQUAL, Kind::BITVECTOR_AND, 1, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_eq_false0)
{
  runTest(false, Kind::EQUAL, Kind::BITVECTOR_AND, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_eq_false1)
{
  runTest(false, Kind::EQUAL, Kind::BITVECTOR_AND, 1, getICBvAndOr);
}

/* Or */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_eq_true0)
{
  runTest(true, Kind::EQUAL, Kind::BITVECTOR_OR, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_eq_true1)
{
  runTest(true, Kind::EQUAL, Kind::BITVECTOR_OR, 1, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_eq_false0)
{
  runTest(false, Kind::EQUAL, Kind::BITVECTOR_OR, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_eq_false1)
{
  runTest(false, Kind::EQUAL, Kind::BITVECTOR_OR, 1, getICBvAndOr);
}

/* Lshr */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_eq_true0)
{
  runTest(true, Kind::EQUAL, Kind::BITVECTOR_LSHR, 0, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_eq_true1)
{
  runTest(true, Kind::EQUAL, Kind::BITVECTOR_LSHR, 1, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_eq_false0)
{
  runTest(false, Kind::EQUAL, Kind::BITVECTOR_LSHR, 0, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_eq_false1)
{
  runTest(false, Kind::EQUAL, Kind::BITVECTOR_LSHR, 1, getICBvLshr);
}

/* Ashr */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_eq_true0)
{
  runTest(true, Kind::EQUAL, Kind::BITVECTOR_ASHR, 0, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_eq_true1)
{
  runTest(true, Kind::EQUAL, Kind::BITVECTOR_ASHR, 1, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_eq_false0)
{
  runTest(false, Kind::EQUAL, Kind::BITVECTOR_ASHR, 0, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_eq_false1)
{
  runTest(false, Kind::EQUAL, Kind::BITVECTOR_ASHR, 1, getICBvAshr);
}

/* Shl */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_eq_true0)
{
  runTest(true, Kind::EQUAL, Kind::BITVECTOR_SHL, 0, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_eq_true1)
{
  runTest(true, Kind::EQUAL, Kind::BITVECTOR_SHL, 1, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_eq_false0)
{
  runTest(false, Kind::EQUAL, Kind::BITVECTOR_SHL, 0, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_eq_false1)
{
  runTest(false, Kind::EQUAL, Kind::BITVECTOR_SHL, 1, getICBvShl);
}

/* Concat */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_eq_true0)
{
  runTestConcat(true, Kind::EQUAL, 0);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_eq_true1)
{
  runTestConcat(true, Kind::EQUAL, 1);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_eq_true2)
{
  runTestConcat(true, Kind::EQUAL, 2);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_eq_false0)
{
  runTestConcat(false, Kind::EQUAL, 0);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_eq_false1)
{
  runTestConcat(false, Kind::EQUAL, 1);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_eq_false2)
{
  runTestConcat(false, Kind::EQUAL, 2);
}

/* Sext */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_sext_eq_true)
{
  runTestSext(true, Kind::EQUAL);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_sext_eq_false)
{
  runTestSext(false, Kind::EQUAL);
}

/* Inequality --------------------------------------------------------------  */

/* Not */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_not_ult_true0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NOT, d_x);
  runTestPred(true, Kind::BITVECTOR_ULT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_not_ult_true1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NOT, d_x);
  runTestPred(true, Kind::BITVECTOR_ULT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_not_ult_false0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NOT, d_x);
  runTestPred(false, Kind::BITVECTOR_ULT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_not_ult_false1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NOT, d_x);
  runTestPred(false, Kind::BITVECTOR_ULT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_not_ugt_true0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NOT, d_x);
  runTestPred(true, Kind::BITVECTOR_UGT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_not_ugt_true1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NOT, d_x);
  runTestPred(true, Kind::BITVECTOR_UGT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_not_ugt_false0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NOT, d_x);
  runTestPred(false, Kind::BITVECTOR_UGT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_not_ugt_false1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NOT, d_x);
  runTestPred(false, Kind::BITVECTOR_UGT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_not_slt_true0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NOT, d_x);
  runTestPred(true, Kind::BITVECTOR_SLT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_not_slt_true1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NOT, d_x);
  runTestPred(true, Kind::BITVECTOR_SLT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_not_slt_false0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NOT, d_x);
  runTestPred(false, Kind::BITVECTOR_SLT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_not_slt_false1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NOT, d_x);
  runTestPred(false, Kind::BITVECTOR_SLT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_not_sgt_true0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NOT, d_x);
  runTestPred(true, Kind::BITVECTOR_SGT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_not_sgt_true1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NOT, d_x);
  runTestPred(true, Kind::BITVECTOR_SGT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_not_sgt_false0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NOT, d_x);
  runTestPred(false, Kind::BITVECTOR_SGT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_not_sgt_false1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NOT, d_x);
  runTestPred(false, Kind::BITVECTOR_SGT, x, getICBvSltSgt);
}

/* Neg */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_neg_ult_true0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NEG, d_x);
  runTestPred(true, Kind::BITVECTOR_ULT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_neg_ult_true1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NEG, d_x);
  runTestPred(true, Kind::BITVECTOR_ULT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_neg_ult_false0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NEG, d_x);
  runTestPred(false, Kind::BITVECTOR_ULT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_neg_ult_false1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NEG, d_x);
  runTestPred(false, Kind::BITVECTOR_ULT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_neg_ugt_true0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NEG, d_x);
  runTestPred(true, Kind::BITVECTOR_UGT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_neg_ugt_true1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NEG, d_x);
  runTestPred(true, Kind::BITVECTOR_UGT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_neg_ugt_false0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NEG, d_x);
  runTestPred(false, Kind::BITVECTOR_UGT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_neg_ugt_false1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NEG, d_x);
  runTestPred(false, Kind::BITVECTOR_UGT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_neg_slt_true0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NEG, d_x);
  runTestPred(true, Kind::BITVECTOR_SLT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_neg_slt_true1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NEG, d_x);
  runTestPred(true, Kind::BITVECTOR_SLT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_neg_slt_false0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NEG, d_x);
  runTestPred(false, Kind::BITVECTOR_SLT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_neg_slt_false1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NEG, d_x);
  runTestPred(false, Kind::BITVECTOR_SLT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_neg_sgt_true0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NEG, d_x);
  runTestPred(true, Kind::BITVECTOR_SGT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_neg_sgt_true1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NEG, d_x);
  runTestPred(true, Kind::BITVECTOR_SGT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_neg_sgt_false0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NEG, d_x);
  runTestPred(false, Kind::BITVECTOR_SGT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_neg_sgt_false1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_NEG, d_x);
  runTestPred(false, Kind::BITVECTOR_SGT, x, getICBvSltSgt);
}

/* Add */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_plus_ult_true0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_ADD, d_x, d_s);
  runTestPred(true, Kind::BITVECTOR_ULT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_plus_ult_true1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_ADD, d_s, d_x);
  runTestPred(true, Kind::BITVECTOR_ULT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_plus_ult_false0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_ADD, d_x, d_s);
  runTestPred(false, Kind::BITVECTOR_ULT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_plus_ult_false1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_ADD, d_s, d_x);
  runTestPred(false, Kind::BITVECTOR_ULT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_plus_ugt_true0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_ADD, d_x, d_s);
  runTestPred(true, Kind::BITVECTOR_UGT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_plus_ugt_true1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_ADD, d_s, d_x);
  runTestPred(true, Kind::BITVECTOR_UGT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_plus_ugt_false0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_ADD, d_x, d_s);
  runTestPred(false, Kind::BITVECTOR_UGT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_plus_ugt_false1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_ADD, d_s, d_x);
  runTestPred(false, Kind::BITVECTOR_UGT, x, getICBvUltUgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_plus_slt_true0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_ADD, d_x, d_s);
  runTestPred(true, Kind::BITVECTOR_SLT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_plus_slt_true1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_ADD, d_s, d_x);
  runTestPred(true, Kind::BITVECTOR_SLT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_plus_slt_false0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_ADD, d_x, d_s);
  runTestPred(false, Kind::BITVECTOR_SLT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_plus_slt_false1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_ADD, d_s, d_x);
  runTestPred(false, Kind::BITVECTOR_SLT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_plus_sgt_true0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_ADD, d_x, d_s);
  runTestPred(true, Kind::BITVECTOR_SGT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_plus_sgt_true1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_ADD, d_s, d_x);
  runTestPred(true, Kind::BITVECTOR_SGT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_plus_sgt_false0)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_ADD, d_x, d_s);
  runTestPred(false, Kind::BITVECTOR_SGT, x, getICBvSltSgt);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_plus_sgt_false1)
{
  Node x = d_nodeManager->mkNode(Kind::BITVECTOR_ADD, d_s, d_x);
  runTestPred(false, Kind::BITVECTOR_SGT, x, getICBvSltSgt);
}

/* Mult */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_ult_true0)
{
  runTest(true, Kind::BITVECTOR_ULT, Kind::BITVECTOR_MULT, 0, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_ult_true1)
{
  runTest(true, Kind::BITVECTOR_ULT, Kind::BITVECTOR_MULT, 1, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_ult_false0)
{
  runTest(false, Kind::BITVECTOR_ULT, Kind::BITVECTOR_MULT, 0, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_ult_false1)
{
  runTest(false, Kind::BITVECTOR_ULT, Kind::BITVECTOR_MULT, 1, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_ugt_true0)
{
  runTest(true, Kind::BITVECTOR_UGT, Kind::BITVECTOR_MULT, 0, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_ugt_true1)
{
  runTest(true, Kind::BITVECTOR_UGT, Kind::BITVECTOR_MULT, 1, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_ugt_false0)
{
  runTest(false, Kind::BITVECTOR_UGT, Kind::BITVECTOR_MULT, 0, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_ugt_false1)
{
  runTest(false, Kind::BITVECTOR_UGT, Kind::BITVECTOR_MULT, 1, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_slt_true0)
{
  runTest(true, Kind::BITVECTOR_SLT, Kind::BITVECTOR_MULT, 0, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_slt_true1)
{
  runTest(true, Kind::BITVECTOR_SLT, Kind::BITVECTOR_MULT, 1, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_slt_false0)
{
  runTest(false, Kind::BITVECTOR_SLT, Kind::BITVECTOR_MULT, 0, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_slt_false1)
{
  runTest(false, Kind::BITVECTOR_SLT, Kind::BITVECTOR_MULT, 1, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_sgt_true0)
{
  runTest(true, Kind::BITVECTOR_SGT, Kind::BITVECTOR_MULT, 0, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_sgt_true1)
{
  runTest(true, Kind::BITVECTOR_SGT, Kind::BITVECTOR_MULT, 1, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_sgt_false0)
{
  runTest(false, Kind::BITVECTOR_SGT, Kind::BITVECTOR_MULT, 0, getICBvMult);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_mult_sgt_false1)
{
  runTest(false, Kind::BITVECTOR_SGT, Kind::BITVECTOR_MULT, 1, getICBvMult);
}

/* Urem */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_ult_true0)
{
  runTest(true, Kind::BITVECTOR_ULT, Kind::BITVECTOR_UREM, 0, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_ult_true1)
{
  runTest(true, Kind::BITVECTOR_ULT, Kind::BITVECTOR_UREM, 1, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_ult_false0)
{
  runTest(false, Kind::BITVECTOR_ULT, Kind::BITVECTOR_UREM, 0, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_ult_false1)
{
  runTest(false, Kind::BITVECTOR_ULT, Kind::BITVECTOR_UREM, 1, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_ugt_true0)
{
  runTest(true, Kind::BITVECTOR_UGT, Kind::BITVECTOR_UREM, 0, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_ugt_true1)
{
  runTest(true, Kind::BITVECTOR_UGT, Kind::BITVECTOR_UREM, 1, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_ugt_false0)
{
  runTest(false, Kind::BITVECTOR_UGT, Kind::BITVECTOR_UREM, 0, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_ugt_false1)
{
  runTest(false, Kind::BITVECTOR_UGT, Kind::BITVECTOR_UREM, 1, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_slt_true0)
{
  runTest(true, Kind::BITVECTOR_SLT, Kind::BITVECTOR_UREM, 0, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_slt_true1)
{
  runTest(true, Kind::BITVECTOR_SLT, Kind::BITVECTOR_UREM, 1, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_slt_false0)
{
  runTest(false, Kind::BITVECTOR_SLT, Kind::BITVECTOR_UREM, 0, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_slt_false1)
{
  runTest(false, Kind::BITVECTOR_SLT, Kind::BITVECTOR_UREM, 1, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_sgt_true0)
{
  runTest(true, Kind::BITVECTOR_SGT, Kind::BITVECTOR_UREM, 0, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_sgt_true1)
{
  runTest(true, Kind::BITVECTOR_SGT, Kind::BITVECTOR_UREM, 1, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_sgt_false0)
{
  runTest(false, Kind::BITVECTOR_SGT, Kind::BITVECTOR_UREM, 0, getICBvUrem);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_urem_sgt_false1)
{
  runTest(false, Kind::BITVECTOR_SGT, Kind::BITVECTOR_UREM, 1, getICBvUrem);
}

/* Udiv */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_ult_true0)
{
  runTest(true, Kind::BITVECTOR_ULT, Kind::BITVECTOR_UDIV, 0, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_ult_true1)
{
  runTest(true, Kind::BITVECTOR_ULT, Kind::BITVECTOR_UDIV, 1, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_ult_false0)
{
  runTest(false, Kind::BITVECTOR_ULT, Kind::BITVECTOR_UDIV, 0, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_ult_false1)
{
  runTest(false, Kind::BITVECTOR_ULT, Kind::BITVECTOR_UDIV, 1, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_ugt_true0)
{
  runTest(true, Kind::BITVECTOR_UGT, Kind::BITVECTOR_UDIV, 0, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_ugt_true1)
{
  runTest(true, Kind::BITVECTOR_UGT, Kind::BITVECTOR_UDIV, 1, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_ugt_false0)
{
  runTest(false, Kind::BITVECTOR_UGT, Kind::BITVECTOR_UDIV, 0, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_ugt_false1)
{
  runTest(false, Kind::BITVECTOR_UGT, Kind::BITVECTOR_UDIV, 1, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_slt_true0)
{
  runTest(true, Kind::BITVECTOR_SLT, Kind::BITVECTOR_UDIV, 0, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_slt_true1)
{
  runTest(true, Kind::BITVECTOR_SLT, Kind::BITVECTOR_UDIV, 1, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_slt_false0)
{
  runTest(false, Kind::BITVECTOR_SLT, Kind::BITVECTOR_UDIV, 0, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_slt_false1)
{
  runTest(false, Kind::BITVECTOR_SLT, Kind::BITVECTOR_UDIV, 1, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_sgt_true0)
{
  runTest(true, Kind::BITVECTOR_SGT, Kind::BITVECTOR_UDIV, 0, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_sgt_true1)
{
  runTest(true, Kind::BITVECTOR_SGT, Kind::BITVECTOR_UDIV, 1, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_sgt_false0)
{
  runTest(false, Kind::BITVECTOR_SGT, Kind::BITVECTOR_UDIV, 0, getICBvUdiv);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_udiv_sgt_false1)
{
  runTest(false, Kind::BITVECTOR_SGT, Kind::BITVECTOR_UDIV, 1, getICBvUdiv);
}

/* And */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_ult_true0)
{
  runTest(true, Kind::BITVECTOR_ULT, Kind::BITVECTOR_AND, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_ult_true1)
{
  runTest(true, Kind::BITVECTOR_ULT, Kind::BITVECTOR_AND, 1, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_ult_false0)
{
  runTest(false, Kind::BITVECTOR_ULT, Kind::BITVECTOR_AND, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_ult_false1)
{
  runTest(false, Kind::BITVECTOR_ULT, Kind::BITVECTOR_AND, 1, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_ugt_true0)
{
  runTest(true, Kind::BITVECTOR_UGT, Kind::BITVECTOR_AND, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_ugt_true1)
{
  runTest(true, Kind::BITVECTOR_UGT, Kind::BITVECTOR_AND, 1, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_ugt_false0)
{
  runTest(false, Kind::BITVECTOR_UGT, Kind::BITVECTOR_AND, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_ugt_false1)
{
  runTest(false, Kind::BITVECTOR_UGT, Kind::BITVECTOR_AND, 1, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_slt_true0)
{
  runTest(true, Kind::BITVECTOR_SLT, Kind::BITVECTOR_AND, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_slt_true1)
{
  runTest(true, Kind::BITVECTOR_SLT, Kind::BITVECTOR_AND, 1, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_slt_false0)
{
  runTest(false, Kind::BITVECTOR_SLT, Kind::BITVECTOR_AND, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_slt_false1)
{
  runTest(false, Kind::BITVECTOR_SLT, Kind::BITVECTOR_AND, 1, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_sgt_true0)
{
  runTest(true, Kind::BITVECTOR_SGT, Kind::BITVECTOR_AND, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_sgt_true1)
{
  runTest(true, Kind::BITVECTOR_SGT, Kind::BITVECTOR_AND, 1, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_sgt_false0)
{
  runTest(false, Kind::BITVECTOR_SGT, Kind::BITVECTOR_AND, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_and_sgt_false1)
{
  runTest(false, Kind::BITVECTOR_SGT, Kind::BITVECTOR_AND, 1, getICBvAndOr);
}

/* Or */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_ult_true0)
{
  runTest(true, Kind::BITVECTOR_ULT, Kind::BITVECTOR_OR, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_ult_true1)
{
  runTest(true, Kind::BITVECTOR_ULT, Kind::BITVECTOR_OR, 1, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_ult_false0)
{
  runTest(false, Kind::BITVECTOR_ULT, Kind::BITVECTOR_OR, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_ult_false1)
{
  runTest(false, Kind::BITVECTOR_ULT, Kind::BITVECTOR_OR, 1, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_ugt_true0)
{
  runTest(true, Kind::BITVECTOR_UGT, Kind::BITVECTOR_OR, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_ugt_true1)
{
  runTest(true, Kind::BITVECTOR_UGT, Kind::BITVECTOR_OR, 1, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_ugt_false0)
{
  runTest(false, Kind::BITVECTOR_UGT, Kind::BITVECTOR_OR, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_ugt_false1)
{
  runTest(false, Kind::BITVECTOR_UGT, Kind::BITVECTOR_OR, 1, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_slt_true0)
{
  runTest(true, Kind::BITVECTOR_SLT, Kind::BITVECTOR_OR, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_slt_true1)
{
  runTest(true, Kind::BITVECTOR_SLT, Kind::BITVECTOR_OR, 1, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_slt_false0)
{
  runTest(false, Kind::BITVECTOR_SLT, Kind::BITVECTOR_OR, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_slt_false1)
{
  runTest(false, Kind::BITVECTOR_SLT, Kind::BITVECTOR_OR, 1, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_sgt_true0)
{
  runTest(true, Kind::BITVECTOR_SGT, Kind::BITVECTOR_OR, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_sgt_true1)
{
  runTest(true, Kind::BITVECTOR_SGT, Kind::BITVECTOR_OR, 1, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_sgt_false0)
{
  runTest(false, Kind::BITVECTOR_SGT, Kind::BITVECTOR_OR, 0, getICBvAndOr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_or_sgt_false1)
{
  runTest(false, Kind::BITVECTOR_SGT, Kind::BITVECTOR_OR, 1, getICBvAndOr);
}

/* Lshr */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_ult_true0)
{
  runTest(true, Kind::BITVECTOR_ULT, Kind::BITVECTOR_LSHR, 0, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_ult_true1)
{
  runTest(true, Kind::BITVECTOR_ULT, Kind::BITVECTOR_LSHR, 1, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_ult_false0)
{
  runTest(false, Kind::BITVECTOR_ULT, Kind::BITVECTOR_LSHR, 0, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_ult_false1)
{
  runTest(false, Kind::BITVECTOR_ULT, Kind::BITVECTOR_LSHR, 1, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_ugt_true0)
{
  runTest(true, Kind::BITVECTOR_UGT, Kind::BITVECTOR_LSHR, 0, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_ugt_true1)
{
  runTest(true, Kind::BITVECTOR_UGT, Kind::BITVECTOR_LSHR, 1, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_ugt_false0)
{
  runTest(false, Kind::BITVECTOR_UGT, Kind::BITVECTOR_LSHR, 0, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_ugt_false1)
{
  runTest(false, Kind::BITVECTOR_UGT, Kind::BITVECTOR_LSHR, 1, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_slt_true0)
{
  runTest(true, Kind::BITVECTOR_SLT, Kind::BITVECTOR_LSHR, 0, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_slt_true1)
{
  runTest(true, Kind::BITVECTOR_SLT, Kind::BITVECTOR_LSHR, 1, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_slt_false0)
{
  runTest(false, Kind::BITVECTOR_SLT, Kind::BITVECTOR_LSHR, 0, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_slt_false1)
{
  runTest(false, Kind::BITVECTOR_SLT, Kind::BITVECTOR_LSHR, 1, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_sgt_true0)
{
  runTest(true, Kind::BITVECTOR_SGT, Kind::BITVECTOR_LSHR, 0, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_sgt_true1)
{
  runTest(true, Kind::BITVECTOR_SGT, Kind::BITVECTOR_LSHR, 1, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_sgt_false0)
{
  runTest(false, Kind::BITVECTOR_SGT, Kind::BITVECTOR_LSHR, 0, getICBvLshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_lshr_sgt_false1)
{
  runTest(false, Kind::BITVECTOR_SGT, Kind::BITVECTOR_LSHR, 1, getICBvLshr);
}

/* Ashr */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_ult_true0)
{
  runTest(true, Kind::BITVECTOR_ULT, Kind::BITVECTOR_ASHR, 0, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_ult_true1)
{
  runTest(true, Kind::BITVECTOR_ULT, Kind::BITVECTOR_ASHR, 1, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_ult_false0)
{
  runTest(false, Kind::BITVECTOR_ULT, Kind::BITVECTOR_ASHR, 0, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_ult_false1)
{
  runTest(false, Kind::BITVECTOR_ULT, Kind::BITVECTOR_ASHR, 1, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_ugt_true0)
{
  runTest(true, Kind::BITVECTOR_UGT, Kind::BITVECTOR_ASHR, 0, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_ugt_true1)
{
  runTest(true, Kind::BITVECTOR_UGT, Kind::BITVECTOR_ASHR, 1, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_ugt_false0)
{
  runTest(false, Kind::BITVECTOR_UGT, Kind::BITVECTOR_ASHR, 0, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_ugt_false1)
{
  runTest(false, Kind::BITVECTOR_UGT, Kind::BITVECTOR_ASHR, 1, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_slt_true0)
{
  runTest(true, Kind::BITVECTOR_SLT, Kind::BITVECTOR_ASHR, 0, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_slt_true1)
{
  runTest(true, Kind::BITVECTOR_SLT, Kind::BITVECTOR_ASHR, 1, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_slt_false0)
{
  runTest(false, Kind::BITVECTOR_SLT, Kind::BITVECTOR_ASHR, 0, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_slt_false1)
{
  runTest(false, Kind::BITVECTOR_SLT, Kind::BITVECTOR_ASHR, 1, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_sgt_true0)
{
  runTest(true, Kind::BITVECTOR_SGT, Kind::BITVECTOR_ASHR, 0, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_sgt_true1)
{
  runTest(true, Kind::BITVECTOR_SGT, Kind::BITVECTOR_ASHR, 1, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_sgt_false0)
{
  runTest(false, Kind::BITVECTOR_SGT, Kind::BITVECTOR_ASHR, 0, getICBvAshr);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_ashr_sgt_false1)
{
  runTest(false, Kind::BITVECTOR_SGT, Kind::BITVECTOR_ASHR, 1, getICBvAshr);
}

/* Shl */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_ult_true0)
{
  runTest(true, Kind::BITVECTOR_ULT, Kind::BITVECTOR_SHL, 0, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_ult_true1)
{
  runTest(true, Kind::BITVECTOR_ULT, Kind::BITVECTOR_SHL, 1, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_ult_false0)
{
  runTest(false, Kind::BITVECTOR_ULT, Kind::BITVECTOR_SHL, 0, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_ult_false1)
{
  runTest(false, Kind::BITVECTOR_ULT, Kind::BITVECTOR_SHL, 1, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_ugt_true0)
{
  runTest(true, Kind::BITVECTOR_UGT, Kind::BITVECTOR_SHL, 0, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_ugt_true1)
{
  runTest(true, Kind::BITVECTOR_UGT, Kind::BITVECTOR_SHL, 1, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_ugt_false0)
{
  runTest(false, Kind::BITVECTOR_UGT, Kind::BITVECTOR_SHL, 0, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_ugt_false1)
{
  runTest(false, Kind::BITVECTOR_UGT, Kind::BITVECTOR_SHL, 1, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_slt_true0)
{
  runTest(true, Kind::BITVECTOR_SLT, Kind::BITVECTOR_SHL, 0, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_slt_true1)
{
  runTest(true, Kind::BITVECTOR_SLT, Kind::BITVECTOR_SHL, 1, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_slt_false0)
{
  runTest(false, Kind::BITVECTOR_SLT, Kind::BITVECTOR_SHL, 0, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_slt_false1)
{
  runTest(false, Kind::BITVECTOR_SLT, Kind::BITVECTOR_SHL, 1, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_sgt_true0)
{
  runTest(true, Kind::BITVECTOR_SGT, Kind::BITVECTOR_SHL, 0, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_sgt_true1)
{
  runTest(true, Kind::BITVECTOR_SGT, Kind::BITVECTOR_SHL, 1, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_sgt_false0)
{
  runTest(false, Kind::BITVECTOR_SGT, Kind::BITVECTOR_SHL, 0, getICBvShl);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_shl_sgt_false1)
{
  runTest(false, Kind::BITVECTOR_SGT, Kind::BITVECTOR_SHL, 1, getICBvShl);
}

/* Concat */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_ult_true0)
{
  runTestConcat(true, Kind::BITVECTOR_ULT, 0);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_ult_true1)
{
  runTestConcat(true, Kind::BITVECTOR_ULT, 1);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_ult_true2)
{
  runTestConcat(true, Kind::BITVECTOR_ULT, 2);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_ult_false0)
{
  runTestConcat(false, Kind::BITVECTOR_ULT, 0);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_ult_false1)
{
  runTestConcat(false, Kind::BITVECTOR_ULT, 1);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_ult_false2)
{
  runTestConcat(false, Kind::BITVECTOR_ULT, 2);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_ugt_true0)
{
  runTestConcat(true, Kind::BITVECTOR_UGT, 0);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_ugt_true1)
{
  runTestConcat(true, Kind::BITVECTOR_UGT, 1);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_ugt_true2)
{
  runTestConcat(true, Kind::BITVECTOR_UGT, 2);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_ugt_false0)
{
  runTestConcat(false, Kind::BITVECTOR_UGT, 0);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_ugt_false1)
{
  runTestConcat(false, Kind::BITVECTOR_UGT, 1);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_ugt_false2)
{
  runTestConcat(false, Kind::BITVECTOR_UGT, 2);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_slt_true0)
{
  runTestConcat(true, Kind::BITVECTOR_SLT, 0);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_slt_true1)
{
  runTestConcat(true, Kind::BITVECTOR_SLT, 1);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_slt_true2)
{
  runTestConcat(true, Kind::BITVECTOR_SLT, 2);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_slt_false0)
{
  runTestConcat(false, Kind::BITVECTOR_SLT, 0);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_slt_false1)
{
  runTestConcat(false, Kind::BITVECTOR_SLT, 1);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_slt_false2)
{
  runTestConcat(false, Kind::BITVECTOR_SLT, 2);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_sgt_true0)
{
  runTestConcat(true, Kind::BITVECTOR_SGT, 0);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_sgt_true1)
{
  runTestConcat(true, Kind::BITVECTOR_SGT, 1);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_sgt_true2)
{
  runTestConcat(true, Kind::BITVECTOR_SGT, 2);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_sgt_false0)
{
  runTestConcat(false, Kind::BITVECTOR_SGT, 0);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_sgt_false1)
{
  runTestConcat(false, Kind::BITVECTOR_SGT, 1);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_concat_sgt_false2)
{
  runTestConcat(false, Kind::BITVECTOR_SGT, 2);
}

/* Sext */

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_sext_ult_true)
{
  runTestSext(true, Kind::BITVECTOR_ULT);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_sext_ult_false)
{
  runTestSext(false, Kind::BITVECTOR_ULT);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_sext_ugt_true)
{
  runTestSext(true, Kind::BITVECTOR_UGT);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_sext_ugt_false)
{
  runTestSext(false, Kind::BITVECTOR_UGT);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_sext_slt_true)
{
  runTestSext(true, Kind::BITVECTOR_SLT);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_sext_slt_false)
{
  runTestSext(false, Kind::BITVECTOR_SLT);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_sext_sgt_true)
{
  runTestSext(true, Kind::BITVECTOR_SGT);
}

TEST_F(TestTheoryWhiteQuantifiersBvInverter, getIC_bv_sext_sgt_false)
{
  runTestSext(false, Kind::BITVECTOR_SGT);
}
}  // namespace test
}  // namespace cvc5::internal
