/*********************                                                        */
/*! \file theory_quantifiers_bv_inverter_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Unit tests for BV inverter.
 **
 ** Unit tests for BV inverter.
 **/

#include "theory/quantifiers/bv_inverter.cpp"

#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "util/result.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::smt;

class TheoryQuantifiersBvInverter : public CxxTest::TestSuite
{
  ExprManager *d_em;
  NodeManager *d_nm;
  SmtEngine *d_smt;
  SmtScope *d_scope;

  Node d_s;
  Node d_t;
  Node d_sk;
  Node d_x;
  Node d_bvarlist;

  void runTestPred(bool pol,
                   Kind k,
                   Node x,
                   Node (*getsc)(bool, Kind, Node, Node))
  {
    Assert(k == BITVECTOR_ULT || k == BITVECTOR_SLT || k == EQUAL
           || k == BITVECTOR_UGT || k == BITVECTOR_SGT);
    Assert(k != EQUAL || pol == false);

    Node sc = getsc(pol, k, d_sk, d_t);
    Kind ksc = sc.getKind();
    TS_ASSERT((k == BITVECTOR_ULT && pol == false)
           || (k == BITVECTOR_SLT && pol == false)
           || (k == BITVECTOR_UGT && pol == false)
           || (k == BITVECTOR_SGT && pol == false)
           || ksc == IMPLIES);
    Node scl = ksc == IMPLIES ? sc[0] : bv::utils::mkTrue();
    if (!pol)
    {
      if (k == BITVECTOR_ULT)
      {
        k = BITVECTOR_UGE;
      }
      else if (k == BITVECTOR_UGT)
      {
        k = BITVECTOR_ULE;
      }
      else if (k == BITVECTOR_SLT)
      {
        k = BITVECTOR_SGE;
      }
      else if (k == BITVECTOR_SGT)
      {
        k = BITVECTOR_ULE;
      }
      else
      {
        Assert(k == EQUAL);
        k = DISTINCT;
      }
    }
    Node body = d_nm->mkNode(k, x, d_t);
    Node scr = d_nm->mkNode(EXISTS, d_bvarlist, body);
    Expr a = d_nm->mkNode(DISTINCT, scl, scr).toExpr();
    Result res = d_smt->checkSat(a);
    TS_ASSERT(res.d_sat == Result::UNSAT);
  }

  void runTest(bool pol,
               Kind litk,
               Kind k,
               unsigned idx,
               Node (*getsc)(bool, Kind, Kind, unsigned, Node, Node, Node))
  {
    Assert(k == BITVECTOR_MULT
           || k == BITVECTOR_UREM_TOTAL
           || k == BITVECTOR_UDIV_TOTAL
           || k == BITVECTOR_AND
           || k == BITVECTOR_OR
           || k == BITVECTOR_LSHR
           || k == BITVECTOR_ASHR
           || k == BITVECTOR_SHL);

    Node sc = getsc(pol, litk, k, idx, d_sk, d_s, d_t);
    TS_ASSERT(!sc.isNull());
    Kind ksc = sc.getKind();
    TS_ASSERT((k == BITVECTOR_UDIV_TOTAL && idx == 1 && pol == false)
              || (k == BITVECTOR_ASHR && idx == 0 && pol == false)
              || ksc == IMPLIES);
    Node scl = ksc == IMPLIES ? sc[0] : bv::utils::mkTrue();
    Node body = idx == 0
      ? d_nm->mkNode(litk, d_nm->mkNode(k, d_x, d_s), d_t)
      : d_nm->mkNode(litk, d_nm->mkNode(k, d_s, d_x), d_t);
    Node scr = d_nm->mkNode(EXISTS, d_bvarlist, pol ? body : body.notNode());
    Expr a = d_nm->mkNode(DISTINCT, scl, scr).toExpr();
    Result res = d_smt->checkSat(a);
    if (res.d_sat == Result::SAT)
    {
      std::cout << std::endl;
      std::cout << "s " << d_smt->getValue(d_s.toExpr()) << std::endl;
      std::cout << "t " << d_smt->getValue(d_t.toExpr()) << std::endl;
      std::cout << "x " << d_smt->getValue(d_x.toExpr()) << std::endl;
    }
    TS_ASSERT(res.d_sat == Result::UNSAT);
  }

  void runTestConcat(bool pol, Kind litk, unsigned idx)
  {
    Node s1, s2, sv_t;
    Node x, t, sk;
    Node sc;

    if (idx == 0)
    {
      s2 = d_nm->mkVar("s2", d_nm->mkBitVectorType(4));
      x = d_nm->mkBoundVar(s2.getType());
      sk = d_nm->mkSkolem("sk", s2.getType());
      t = d_nm->mkVar("t", d_nm->mkBitVectorType(8));
      sv_t = d_nm->mkNode(BITVECTOR_CONCAT, x, s2);
      sc = getScBvConcat(pol, litk, 0, sk, sv_t, t);
    }
    else if (idx == 1)
    {
      s1 = d_nm->mkVar("s1", d_nm->mkBitVectorType(4));
      x = d_nm->mkBoundVar(s1.getType());
      sk = d_nm->mkSkolem("sk", s1.getType());
      t = d_nm->mkVar("t", d_nm->mkBitVectorType(8));
      sv_t = d_nm->mkNode(BITVECTOR_CONCAT, s1, x);
      sc = getScBvConcat(pol, litk, 1, sk, sv_t, t);
    }
    else
    {
      Assert(idx == 2);
      s1 = d_nm->mkVar("s1", d_nm->mkBitVectorType(4));
      s2 = d_nm->mkVar("s2", d_nm->mkBitVectorType(4));
      x = d_nm->mkBoundVar(s2.getType());
      sk = d_nm->mkSkolem("sk", s1.getType());
      t = d_nm->mkVar("t", d_nm->mkBitVectorType(12));
      sv_t = d_nm->mkNode(BITVECTOR_CONCAT, s1, x, s2);
      sc = getScBvConcat(pol, litk, 1, sk, sv_t, t);
    }

    TS_ASSERT(!sc.isNull());
    Kind ksc = sc.getKind();
    TS_ASSERT((litk == kind::EQUAL && pol == false)
              || ksc == IMPLIES);
    Node scl = ksc == IMPLIES ? sc[0] : bv::utils::mkTrue();
    Node body = d_nm->mkNode(litk, sv_t, t);
    Node bvarlist = d_nm->mkNode(BOUND_VAR_LIST, { x });
    Node scr = d_nm->mkNode(EXISTS, bvarlist, pol ? body : body.notNode());
    Expr a = d_nm->mkNode(DISTINCT, scl, scr).toExpr();
    Result res = d_smt->checkSat(a);
    if (res.d_sat == Result::SAT)
    {
      std::cout << std::endl;
      if (!s1.isNull())
        std::cout << "s1 " << d_smt->getValue(s1.toExpr()) << std::endl;
      if (!s2.isNull())
        std::cout << "s2 " << d_smt->getValue(s2.toExpr()) << std::endl;
      std::cout << "t " << d_smt->getValue(t.toExpr()) << std::endl;
      std::cout << "x " << d_smt->getValue(x.toExpr()) << std::endl;
    }
    TS_ASSERT(res.d_sat == Result::UNSAT);
  }

  void runTestSext(bool pol, Kind litk)
  {
    unsigned ws = 3;
    unsigned wx = 5;
    unsigned w = 8;

    Node x = d_nm->mkVar("x", d_nm->mkBitVectorType(wx));
    Node sk = d_nm->mkSkolem("sk", x.getType());
    x = d_nm->mkBoundVar(x.getType());

    Node t = d_nm->mkVar("t", d_nm->mkBitVectorType(w));
    Node sv_t = bv::utils::mkSignExtend(x, ws);
    Node sc = getScBvSext(pol, litk, 0, sk, sv_t, t);

    TS_ASSERT(!sc.isNull());
    Kind ksc = sc.getKind();
    TS_ASSERT((litk == kind::EQUAL && pol == false)
              || (litk == kind::BITVECTOR_ULT && pol == false)
              || (litk == kind::BITVECTOR_UGT && pol == false)
              || ksc == IMPLIES);
    Node scl = ksc == IMPLIES ? sc[0] : bv::utils::mkTrue();
    Node body = d_nm->mkNode(litk, sv_t, t);
    Node bvarlist = d_nm->mkNode(BOUND_VAR_LIST, { x });
    Node scr = d_nm->mkNode(EXISTS, bvarlist, pol ? body : body.notNode());
    Expr a = d_nm->mkNode(DISTINCT, scl, scr).toExpr();
    Result res = d_smt->checkSat(a);
    if (res.d_sat == Result::SAT)
    {
      std::cout << std::endl;
      std::cout << "t " << d_smt->getValue(t.toExpr()) << std::endl;
      std::cout << "x " << d_smt->getValue(x.toExpr()) << std::endl;
    }
    TS_ASSERT(res.d_sat == Result::UNSAT);
  }

 public:
  TheoryQuantifiersBvInverter() {}

  void setUp()
  {
    d_em = new ExprManager();
    d_nm = NodeManager::fromExprManager(d_em);
    d_smt = new SmtEngine(d_em);
    d_smt->setOption("cbqi-full", CVC4::SExpr(true));
    d_smt->setOption("produce-models", CVC4::SExpr(true));
    d_scope = new SmtScope(d_smt);

    d_s = d_nm->mkVar("s", d_nm->mkBitVectorType(4));
    d_t = d_nm->mkVar("t", d_nm->mkBitVectorType(4));
    d_sk = d_nm->mkSkolem("sk", d_t.getType());
    d_x = d_nm->mkBoundVar(d_t.getType());
    d_bvarlist = d_nm->mkNode(BOUND_VAR_LIST, { d_x });
  }

  void tearDown()
  {
    d_bvarlist = Node::null();
    d_x = Node::null();
    d_sk = Node::null();
    d_t = Node::null();
    d_s = Node::null();
    delete d_scope;
    delete d_smt;
    delete d_em;
  }

  /* Generic side conditions for LT ---------------------------------------  */

  void testGetScBvUltTrue()
  {
    runTestPred(true, BITVECTOR_ULT, d_x, getScBvUltUgt);
  }

  void testGetScBvUltFalse()
  {
    runTestPred(false, BITVECTOR_ULT, d_x, getScBvUltUgt);
  }

  void testGetScBvUgtTrue()
  {
    runTestPred(true, BITVECTOR_UGT, d_x, getScBvUltUgt);
  }

  void testGetScBvUgtFalse()
  {
    runTestPred(false, BITVECTOR_UGT, d_x, getScBvUltUgt);
  }

  void testGetScBvSltTrue()
  {
    runTestPred(true, BITVECTOR_SLT, d_x, getScBvSltSgt);
  }

  void testGetScBvSltFalse()
  {
    runTestPred(false, BITVECTOR_SLT, d_x, getScBvSltSgt);
  }

  void testGetScBvSgtTrue()
  {
    runTestPred(true, BITVECTOR_SGT, d_x, getScBvSltSgt);
  }

  void testGetScBvSgtFalse()
  {
    runTestPred(false, BITVECTOR_SGT, d_x, getScBvSltSgt);
  }

  /* Equality and Disequality ----------------------------------------------  */

  /* Mult */

  void testGetScBvMultEqTrue0()
  {
    runTest(true, EQUAL, BITVECTOR_MULT, 0, getScBvMult);
  }

  void testGetScBvMultEqTrue1()
  {
    runTest(true, EQUAL, BITVECTOR_MULT, 1, getScBvMult);
  }

  void testGetScBvMultEqFalse0()
  {
    runTest(false, EQUAL, BITVECTOR_MULT, 0, getScBvMult);
  }

  void testGetScBvMultEqFalse1()
  {
    runTest(false, EQUAL, BITVECTOR_MULT, 1, getScBvMult);
  }

  /* Urem */

  void testGetScBvUremEqTrue0()
  {
    runTest(true, EQUAL, BITVECTOR_UREM_TOTAL, 0, getScBvUrem);
  }

  void testGetScBvUremEqTrue1()
  {
    runTest(true, EQUAL, BITVECTOR_UREM_TOTAL, 1, getScBvUrem);
  }

  void testGetScBvUremEqFalse0()
  {
    runTest(false, EQUAL, BITVECTOR_UREM_TOTAL, 0, getScBvUrem);
  }

  void testGetScBvUremEqFalse1()
  {
    runTest(false, EQUAL, BITVECTOR_UREM_TOTAL, 1, getScBvUrem);
  }

  /* Udiv */
  void testGetScBvUdivEqTrue0()
  {
    runTest(true, EQUAL, BITVECTOR_UDIV_TOTAL, 0, getScBvUdiv);
  }

  void testGetScBvUdivEqTrue1()
  {
    runTest(true, EQUAL, BITVECTOR_UDIV_TOTAL, 1, getScBvUdiv);
  }

  void testGetScBvUdivEqFalse0()
  {
    runTest(false, EQUAL, BITVECTOR_UDIV_TOTAL, 0, getScBvUdiv);
  }

  void testGetScBvUdivEqFalse1()
  {
    runTest(false, EQUAL, BITVECTOR_UDIV_TOTAL, 1, getScBvUdiv);
  }

  /* And */

  void testGetScBvAndEqTrue0()
  {
    runTest(true, EQUAL, BITVECTOR_AND, 0, getScBvAndOr);
  }

  void testGetScBvAndEqTrue1()
  {
    runTest(true, EQUAL, BITVECTOR_AND, 1, getScBvAndOr);
  }

  void testGetScBvAndEqFalse0()
  {
    runTest(false, EQUAL, BITVECTOR_AND, 0, getScBvAndOr);
  }

  void testGetScBvAndEqFalse1()
  {
    runTest(false, EQUAL, BITVECTOR_AND, 1, getScBvAndOr);
  }

  /* Or */

  void testGetScBvOrEqTrue0()
  {
    runTest(true, EQUAL, BITVECTOR_OR, 0, getScBvAndOr);
  }

  void testGetScBvOrEqTrue1()
  {
    runTest(true, EQUAL, BITVECTOR_OR, 1, getScBvAndOr);
  }

  void testGetScBvOrEqFalse0()
  {
    runTest(false, EQUAL, BITVECTOR_OR, 0, getScBvAndOr);
  }

  void testGetScBvOrEqFalse1()
  {
    runTest(false, EQUAL, BITVECTOR_OR, 1, getScBvAndOr);
  }

  /* Lshr */

  void testGetScBvLshrEqTrue0()
  {
    runTest(true, EQUAL, BITVECTOR_LSHR, 0, getScBvLshr);
  }

  void testGetScBvLshrEqTrue1()
  {
    runTest(true, EQUAL, BITVECTOR_LSHR, 1, getScBvLshr);
  }

  void testGetScBvLshrEqFalse0()
  {
    runTest(false, EQUAL, BITVECTOR_LSHR, 0, getScBvLshr);
  }

  void testGetScBvLshrEqFalse1()
  {
    runTest(false, EQUAL, BITVECTOR_LSHR, 1, getScBvLshr);
  }

  /* Ashr */

  void testGetScBvAshrEqTrue0()
  {
    runTest(true, EQUAL, BITVECTOR_ASHR, 0, getScBvAshr);
  }

  void testGetScBvAshrEqTrue1()
  {
    runTest(true, EQUAL, BITVECTOR_ASHR, 1, getScBvAshr);
  }

  void testGetScBvAshrEqFalse0()
  {
    runTest(false, EQUAL, BITVECTOR_ASHR, 0, getScBvAshr);
  }

  void testGetScBvAshrEqFalse1()
  {
    runTest(false, EQUAL, BITVECTOR_ASHR, 1, getScBvAshr);
  }

  /* Shl */

  void testGetScBvShlEqTrue0()
  {
    runTest(true, EQUAL, BITVECTOR_SHL, 0, getScBvShl);
  }

  void testGetScBvShlEqTrue1()
  {
    runTest(true, EQUAL, BITVECTOR_SHL, 1, getScBvShl);
  }

  void testGetScBvShlEqFalse0()
  {
    runTest(false, EQUAL, BITVECTOR_SHL, 0, getScBvShl);
  }

  void testGetScBvShlEqFalse1()
  {
    runTest(false, EQUAL, BITVECTOR_SHL, 1, getScBvShl);
  }

  /* Concat */

  void testGetScBvConcatEqTrue0()
  {
    runTestConcat(true, EQUAL, 0);
  }

  void testGetScBvConcatEqTrue1()
  {
    runTestConcat(true, EQUAL, 1);
  }

  void testGetScBvConcatEqTrue2()
  {
    runTestConcat(true, EQUAL, 2);
  }

  void testGetScBvConcatEqFalse0()
  {
    runTestConcat(false, EQUAL, 0);
  }

  void testGetScBvConcatEqFalse1()
  {
    runTestConcat(false, EQUAL, 1);
  }

  void testGetScBvConcatEqFalse2()
  {
    runTestConcat(false, EQUAL, 2);
  }

  /* Sext */

  void testGetScBvSextEqTrue()
  {
    runTestSext(true, EQUAL);
  }

  void testGetScBvSextEqFalse()
  {
    runTestSext(false, EQUAL);
  }

  /* Inequality ------------------------------------------------------------  */

  /* Not */

  void testGetScBvNotUltTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(true, BITVECTOR_ULT, x, getScBvUltUgt);
  }

  void testGetScBvNotUltTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(true, BITVECTOR_ULT, x, getScBvUltUgt);
  }

  void testGetScBvNotUltFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(false, BITVECTOR_ULT, x, getScBvUltUgt);
  }

  void testGetScBvNotUltFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(false, BITVECTOR_ULT, x, getScBvUltUgt);
  }

  void testGetScBvNotUgtTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(true, BITVECTOR_UGT, x, getScBvUltUgt);
  }

  void testGetScBvNotUgtTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(true, BITVECTOR_UGT, x, getScBvUltUgt);
  }

  void testGetScBvNotUgtFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(false, BITVECTOR_UGT, x, getScBvUltUgt);
  }

  void testGetScBvNotUgtFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(false, BITVECTOR_UGT, x, getScBvUltUgt);
  }

  void testGetScBvNotSltTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(true, BITVECTOR_SLT, x, getScBvSltSgt);
  }

  void testGetScBvNotSltTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(true, BITVECTOR_SLT, x, getScBvSltSgt);
  }

  void testGetScBvNotSltFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(false, BITVECTOR_SLT, x, getScBvSltSgt);
  }

  void testGetScBvNotSltFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(false, BITVECTOR_SLT, x, getScBvSltSgt);
  }

  void testGetScBvNotSgtTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(true, BITVECTOR_SGT, x, getScBvSltSgt);
  }

  void testGetScBvNotSgtTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(true, BITVECTOR_SGT, x, getScBvSltSgt);
  }

  void testGetScBvNotSgtFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(false, BITVECTOR_SGT, x, getScBvSltSgt);
  }

  void testGetScBvNotSgtFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(false, BITVECTOR_SGT, x, getScBvSltSgt);
  }

  /* Neg */

  void testGetScBvNegUltTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(true, BITVECTOR_ULT, x, getScBvUltUgt);
  }

  void testGetScBvNegUltTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(true, BITVECTOR_ULT, x, getScBvUltUgt);
  }

  void testGetScBvNegUltFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(false, BITVECTOR_ULT, x, getScBvUltUgt);
  }

  void testGetScBvNegUltFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(false, BITVECTOR_ULT, x, getScBvUltUgt);
  }

  void testGetScBvNegUgtTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(true, BITVECTOR_UGT, x, getScBvUltUgt);
  }

  void testGetScBvNegUgtTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(true, BITVECTOR_UGT, x, getScBvUltUgt);
  }

  void testGetScBvNegUgtFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(false, BITVECTOR_UGT, x, getScBvUltUgt);
  }

  void testGetScBvNegUgtFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(false, BITVECTOR_UGT, x, getScBvUltUgt);
  }

  void testGetScBvNegSltTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(true, BITVECTOR_SLT, x, getScBvSltSgt);
  }

  void testGetScBvNegSltTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(true, BITVECTOR_SLT, x, getScBvSltSgt);
  }

  void testGetScBvNegSltFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(false, BITVECTOR_SLT, x, getScBvSltSgt);
  }

  void testGetScBvNegSltFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(false, BITVECTOR_SLT, x, getScBvSltSgt);
  }

  void testGetScBvNegSgtTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(true, BITVECTOR_SGT, x, getScBvSltSgt);
  }

  void testGetScBvNegSgtTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(true, BITVECTOR_SGT, x, getScBvSltSgt);
  }

  void testGetScBvNegSgtFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(false, BITVECTOR_SGT, x, getScBvSltSgt);
  }

  void testGetScBvNegSgtFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(false, BITVECTOR_SGT, x, getScBvSltSgt);
  }

  /* Add */

  void testGetScBvPlusUltTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_x, d_s);
    runTestPred(true, BITVECTOR_ULT, x, getScBvUltUgt);
  }

  void testGetScBvPlusUltTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_s, d_x);
    runTestPred(true, BITVECTOR_ULT, x, getScBvUltUgt);
  }

  void testGetScBvPlusUltFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_x, d_s);
    runTestPred(false, BITVECTOR_ULT, x, getScBvUltUgt);
  }

  void testGetScBvPlusUltFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_s, d_x);
    runTestPred(false, BITVECTOR_ULT, x, getScBvUltUgt);
  }

  void testGetScBvPlusUgtTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_x, d_s);
    runTestPred(true, BITVECTOR_UGT, x, getScBvUltUgt);
  }

  void testGetScBvPlusUgtTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_s, d_x);
    runTestPred(true, BITVECTOR_UGT, x, getScBvUltUgt);
  }

  void testGetScBvPlusUgtFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_x, d_s);
    runTestPred(false, BITVECTOR_UGT, x, getScBvUltUgt);
  }

  void testGetScBvPlusUgtFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_s, d_x);
    runTestPred(false, BITVECTOR_UGT, x, getScBvUltUgt);
  }

  void testGetScBvPlusSltTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_x, d_s);
    runTestPred(true, BITVECTOR_SLT, x, getScBvSltSgt);
  }

  void testGetScBvPlusSltTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_s, d_x);
    runTestPred(true, BITVECTOR_SLT, x, getScBvSltSgt);
  }

  void testGetScBvPlusSltFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_x, d_s);
    runTestPred(false, BITVECTOR_SLT, x, getScBvSltSgt);
  }

  void testGetScBvPlusSltFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_s, d_x);
    runTestPred(false, BITVECTOR_SLT, x, getScBvSltSgt);
  }

  void testGetScBvPlusSgtTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_x, d_s);
    runTestPred(true, BITVECTOR_SGT, x, getScBvSltSgt);
  }

  void testGetScBvPlusSgtTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_s, d_x);
    runTestPred(true, BITVECTOR_SGT, x, getScBvSltSgt);
  }

  void testGetScBvPlusSgtFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_x, d_s);
    runTestPred(false, BITVECTOR_SGT, x, getScBvSltSgt);
  }

  void testGetScBvPlusSgtFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_s, d_x);
    runTestPred(false, BITVECTOR_SGT, x, getScBvSltSgt);
  }

  /* Mult */

  void testGetScBvMultUltTrue0()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_MULT, 0, getScBvMult);
  }

  void testGetScBvMultUltTrue1()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_MULT, 1, getScBvMult);
  }

  void testGetScBvMultUltFalse0()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_MULT, 0, getScBvMult);
  }

  void testGetScBvMultUltFalse1()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_MULT, 1, getScBvMult);
  }

  void testGetScBvMultUgtTrue0()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_MULT, 0, getScBvMult);
  }

  void testGetScBvMultUgtTrue1()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_MULT, 1, getScBvMult);
  }

  void testGetScBvMultUgtFalse0()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_MULT, 0, getScBvMult);
  }

  void testGetScBvMultUgtFalse1()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_MULT, 1, getScBvMult);
  }

  void testGetScBvMultSltTrue0()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_MULT, 0, getScBvMult);
  }

  void testGetScBvMultSltTrue1()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_MULT, 1, getScBvMult);
  }

  void testGetScBvMultSltFalse0()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_MULT, 0, getScBvMult);
  }

  void testGetScBvMultSltFalse1()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_MULT, 1, getScBvMult);
  }

  void testGetScBvMultSgtTrue0()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_MULT, 0, getScBvMult);
  }

  void testGetScBvMultSgtTrue1()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_MULT, 1, getScBvMult);
  }

  void testGetScBvMultSgtFalse0()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_MULT, 0, getScBvMult);
  }

  void testGetScBvMultSgtFalse1()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_MULT, 1, getScBvMult);
  }

  /* Urem */

  void testGetScBvUremUltTrue0()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_UREM_TOTAL, 0, getScBvUrem);
  }

  void testGetScBvUremUltTrue1()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_UREM_TOTAL, 1, getScBvUrem);
  }

  void testGetScBvUremUltFalse0()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_UREM_TOTAL, 0, getScBvUrem);
  }

  void testGetScBvUremUltFalse1()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_UREM_TOTAL, 1, getScBvUrem);
  }

  void testGetScBvUremUgtTrue0()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_UREM_TOTAL, 0, getScBvUrem);
  }

  void testGetScBvUremUgtTrue1()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_UREM_TOTAL, 1, getScBvUrem);
  }

  void testGetScBvUremUgtFalse0()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_UREM_TOTAL, 0, getScBvUrem);
  }

  void testGetScBvUremUgtFalse1()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_UREM_TOTAL, 1, getScBvUrem);
  }

  void testGetScBvUremSltTrue0()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_UREM_TOTAL, 0, getScBvUrem);
  }

  void testGetScBvUremSltTrue1()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_UREM_TOTAL, 1, getScBvUrem);
  }

  void testGetScBvUremSltFalse0()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_UREM_TOTAL, 0, getScBvUrem);
  }

  void testGetScBvUremSltFalse1()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_UREM_TOTAL, 1, getScBvUrem);
  }

  void testGetScBvUremSgtTrue0()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_UREM_TOTAL, 0, getScBvUrem);
  }

  void testGetScBvUremSgtTrue1()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_UREM_TOTAL, 1, getScBvUrem);
  }

  void testGetScBvUremSgtFalse0()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_UREM_TOTAL, 0, getScBvUrem);
  }

  void testGetScBvUremSgtFalse1()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_UREM_TOTAL, 1, getScBvUrem);
  }

  /* Udiv */

  void testGetScBvUdivUltTrue0()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_UDIV_TOTAL, 0, getScBvUdiv);
  }

  void testGetScBvUdivUltTrue1()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_UDIV_TOTAL, 1, getScBvUdiv);
  }

  void testGetScBvUdivUltFalse0()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_UDIV_TOTAL, 0, getScBvUdiv);
  }

  void testGetScBvUdivUltFalse1()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_UDIV_TOTAL, 1, getScBvUdiv);
  }

  void testGetScBvUdivUgtTrue0()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_UDIV_TOTAL, 0, getScBvUdiv);
  }

  void testGetScBvUdivUgtTrue1()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_UDIV_TOTAL, 1, getScBvUdiv);
  }

  void testGetScBvUdivUgtFalse0()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_UDIV_TOTAL, 0, getScBvUdiv);
  }

  void testGetScBvUdivUgtFalse1()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_UDIV_TOTAL, 1, getScBvUdiv);
  }

  void testGetScBvUdivSltTrue0()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_UDIV_TOTAL, 0, getScBvUdiv);
  }

  void testGetScBvUdivSltTrue1()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_UDIV_TOTAL, 1, getScBvUdiv);
  }

  void testGetScBvUdivSltFalse0()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_UDIV_TOTAL, 0, getScBvUdiv);
  }

  void testGetScBvUdivSltFalse1()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_UDIV_TOTAL, 1, getScBvUdiv);
  }

  void testGetScBvUdivSgtTrue0()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_UDIV_TOTAL, 0, getScBvUdiv);
  }

  void testGetScBvUdivSgtTrue1()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_UDIV_TOTAL, 1, getScBvUdiv);
  }

  void testGetScBvUdivSgtFalse0()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_UDIV_TOTAL, 0, getScBvUdiv);
  }

  void testGetScBvUdivSgtFalse1()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_UDIV_TOTAL, 1, getScBvUdiv);
  }

  /* And */

  void testGetScBvAndUltTrue0()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_AND, 0, getScBvAndOr);
  }

  void testGetScBvAndUltTrue1()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_AND, 1, getScBvAndOr);
  }

  void testGetScBvAndUltFalse0()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_AND, 0, getScBvAndOr);
  }

  void testGetScBvAndUltFalse1()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_AND, 1, getScBvAndOr);
  }

  void testGetScBvAndUgtTrue0()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_AND, 0, getScBvAndOr);
  }

  void testGetScBvAndUgtTrue1()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_AND, 1, getScBvAndOr);
  }

  void testGetScBvAndUgtFalse0()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_AND, 0, getScBvAndOr);
  }

  void testGetScBvAndUgtFalse1()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_AND, 1, getScBvAndOr);
  }

  void testGetScBvAndSltTrue0()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_AND, 0, getScBvAndOr);
  }

  void testGetScBvAndSltTrue1()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_AND, 1, getScBvAndOr);
  }

  void testGetScBvAndSltFalse0()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_AND, 0, getScBvAndOr);
  }

  void testGetScBvAndSltFalse1()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_AND, 1, getScBvAndOr);
  }

  void testGetScBvAndSgtTrue0()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_AND, 0, getScBvAndOr);
  }

  void testGetScBvAndSgtTrue1()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_AND, 1, getScBvAndOr);
  }

  void testGetScBvAndSgtFalse0()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_AND, 0, getScBvAndOr);
  }

  void testGetScBvAndSgtFalse1()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_AND, 1, getScBvAndOr);
  }

  /* Or */

  void testGetScBvOrUltTrue0()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_OR, 0, getScBvAndOr);
  }

  void testGetScBvOrUltTrue1()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_OR, 1, getScBvAndOr);
  }

  void testGetScBvOrUltFalse0()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_OR, 0, getScBvAndOr);
  }

  void testGetScBvOrUltFalse1()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_OR, 1, getScBvAndOr);
  }

  void testGetScBvOrUgtTrue0()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_OR, 0, getScBvAndOr);
  }

  void testGetScBvOrUgtTrue1()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_OR, 1, getScBvAndOr);
  }

  void testGetScBvOrUgtFalse0()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_OR, 0, getScBvAndOr);
  }

  void testGetScBvOrUgtFalse1()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_OR, 1, getScBvAndOr);
  }

  void testGetScBvOrSltTrue0()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_OR, 0, getScBvAndOr);
  }

  void testGetScBvOrSltTrue1()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_OR, 1, getScBvAndOr);
  }

  void testGetScBvOrSltFalse0()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_OR, 0, getScBvAndOr);
  }

  void testGetScBvOrSltFalse1()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_OR, 1, getScBvAndOr);
  }

  void testGetScBvOrSgtTrue0()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_OR, 0, getScBvAndOr);
  }

  void testGetScBvOrSgtTrue1()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_OR, 1, getScBvAndOr);
  }

  void testGetScBvOrSgtFalse0()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_OR, 0, getScBvAndOr);
  }

  void testGetScBvOrSgtFalse1()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_OR, 1, getScBvAndOr);
  }

  /* Lshr */

  void testGetScBvLshrUltTrue0()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_LSHR, 0, getScBvLshr);
  }

  void testGetScBvLshrUltTrue1()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_LSHR, 1, getScBvLshr);
  }

  void testGetScBvLshrUltFalse0()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_LSHR, 0, getScBvLshr);
  }

  void testGetScBvLshrUltFalse1()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_LSHR, 1, getScBvLshr);
  }

  void testGetScBvLshrUgtTrue0()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_LSHR, 0, getScBvLshr);
  }

  void testGetScBvLshrUgtTrue1()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_LSHR, 1, getScBvLshr);
  }

  void testGetScBvLshrUgtFalse0()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_LSHR, 0, getScBvLshr);
  }

  void testGetScBvLshrUgtFalse1()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_LSHR, 1, getScBvLshr);
  }

  void testGetScBvLshrSltTrue0()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_LSHR, 0, getScBvLshr);
  }

  void testGetScBvLshrSltTrue1()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_LSHR, 1, getScBvLshr);
  }

  void testGetScBvLshrSltFalse0()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_LSHR, 0, getScBvLshr);
  }

  void testGetScBvLshrSltFalse1()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_LSHR, 1, getScBvLshr);
  }

  void testGetScBvLshrSgtTrue0()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_LSHR, 0, getScBvLshr);
  }

  void testGetScBvLshrSgtTrue1()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_LSHR, 1, getScBvLshr);
  }

  void testGetScBvLshrSgtFalse0()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_LSHR, 0, getScBvLshr);
  }

  void testGetScBvLshrSgtFalse1()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_LSHR, 1, getScBvLshr);
  }

  /* Ashr */

  void testGetScBvAshrUltTrue0()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_ASHR, 0, getScBvAshr);
  }

  void testGetScBvAshrUltTrue1()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_ASHR, 1, getScBvAshr);
  }

  void testGetScBvAshrUltFalse0()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_ASHR, 0, getScBvAshr);
  }

  void testGetScBvAshrUltFalse1()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_ASHR, 1, getScBvAshr);
  }

  void testGetScBvAshrUgtTrue0()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_ASHR, 0, getScBvAshr);
  }

  void testGetScBvAshrUgtTrue1()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_ASHR, 1, getScBvAshr);
  }

  void testGetScBvAshrUgtFalse0()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_ASHR, 0, getScBvAshr);
  }

  void testGetScBvAshrUgtFalse1()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_ASHR, 1, getScBvAshr);
  }

  void testGetScBvAshrSltTrue0()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_ASHR, 0, getScBvAshr);
  }

  void testGetScBvAshrSltTrue1()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_ASHR, 1, getScBvAshr);
  }

  void testGetScBvAshrSltFalse0()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_ASHR, 0, getScBvAshr);
  }

  void testGetScBvAshrSltFalse1()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_ASHR, 1, getScBvAshr);
  }

  void testGetScBvAshrSgtTrue0()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_ASHR, 0, getScBvAshr);
  }

  void testGetScBvAshrSgtTrue1()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_ASHR, 1, getScBvAshr);
  }

  void testGetScBvAshrSgtFalse0()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_ASHR, 0, getScBvAshr);
  }

  void testGetScBvAshrSgtFalse1()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_ASHR, 1, getScBvAshr);
  }

  /* Shl */

  void testGetScBvShlUltTrue0()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_SHL, 0, getScBvShl);
  }

  void testGetScBvShlUltTrue1()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_SHL, 1, getScBvShl);
  }

  void testGetScBvShlUltFalse0()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_SHL, 0, getScBvShl);
  }

  void testGetScBvShlUltFalse1()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_SHL, 1, getScBvShl);
  }

  void testGetScBvShlUgtTrue0()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_SHL, 0, getScBvShl);
  }

  void testGetScBvShlUgtTrue1()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_SHL, 1, getScBvShl);
  }

  void testGetScBvShlUgtFalse0()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_SHL, 0, getScBvShl);
  }

  void testGetScBvShlUgtFalse1()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_SHL, 1, getScBvShl);
  }

  void testGetScBvShlSltTrue0()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_SHL, 0, getScBvShl);
  }

  void testGetScBvShlSltTrue1()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_SHL, 1, getScBvShl);
  }

  void testGetScBvShlSltFalse0()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_SHL, 0, getScBvShl);
  }

  void testGetScBvShlSltFalse1()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_SHL, 1, getScBvShl);
  }

  void testGetScBvShlSgtTrue0()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_SHL, 0, getScBvShl);
  }

  void testGetScBvShlSgtTrue1()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_SHL, 1, getScBvShl);
  }

  void testGetScBvShlSgtFalse0()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_SHL, 0, getScBvShl);
  }

  void testGetScBvShlSgtFalse1()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_SHL, 1, getScBvShl);
  }

  /* Concat */

  void testGetScBvConcatUltTrue0()
  {
    runTestConcat(true, BITVECTOR_ULT, 0);
  }

  void testGetScBvConcatUltTrue1()
  {
    runTestConcat(true, BITVECTOR_ULT, 1);
  }

  void testGetScBvConcatUltTrue2()
  {
    runTestConcat(true, BITVECTOR_ULT, 2);
  }

  void testGetScBvConcatUltFalse0()
  {
    runTestConcat(false, BITVECTOR_ULT, 0);
  }

  void testGetScBvConcatUltFalse1()
  {
    runTestConcat(false, BITVECTOR_ULT, 1);
  }

  void testGetScBvConcatUltFalse2()
  {
    runTestConcat(false, BITVECTOR_ULT, 2);
  }

  void testGetScBvConcatUgtTrue0()
  {
    runTestConcat(true, BITVECTOR_UGT, 0);
  }

  void testGetScBvConcatUgtTrue1()
  {
    runTestConcat(true, BITVECTOR_UGT, 1);
  }

  void testGetScBvConcatUgtTrue2()
  {
    runTestConcat(true, BITVECTOR_UGT, 2);
  }

  void testGetScBvConcatUgtFalse0()
  {
    runTestConcat(false, BITVECTOR_UGT, 0);
  }

  void testGetScBvConcatUgtFalse1()
  {
    runTestConcat(false, BITVECTOR_UGT, 1);
  }

  void testGetScBvConcatUgtFalse2()
  {
    runTestConcat(false, BITVECTOR_UGT, 2);
  }

  void testGetScBvConcatSltTrue0()
  {
    runTestConcat(true, BITVECTOR_SLT, 0);
  }

  void testGetScBvConcatSltTrue1()
  {
    runTestConcat(true, BITVECTOR_SLT, 1);
  }

  void testGetScBvConcatSltTrue2()
  {
    runTestConcat(true, BITVECTOR_SLT, 2);
  }

  void testGetScBvConcatSltFalse0()
  {
    runTestConcat(false, BITVECTOR_SLT, 0);
  }

  void testGetScBvConcatSltFalse1()
  {
    runTestConcat(false, BITVECTOR_SLT, 1);
  }

  void testGetScBvConcatSltFalse2()
  {
    runTestConcat(false, BITVECTOR_SLT, 2);
  }

  void testGetScBvConcatSgtTrue0()
  {
    runTestConcat(true, BITVECTOR_SGT, 0);
  }

  void testGetScBvConcatSgtTrue1()
  {
    runTestConcat(true, BITVECTOR_SGT, 1);
  }

  void testGetScBvConcatSgtTrue2()
  {
    runTestConcat(true, BITVECTOR_SGT, 2);
  }

  void testGetScBvConcatSgtFalse0()
  {
    runTestConcat(false, BITVECTOR_SGT, 0);
  }

  void testGetScBvConcatSgtFalse1()
  {
    runTestConcat(false, BITVECTOR_SGT, 1);
  }

  void testGetScBvConcatSgtFalse2()
  {
    runTestConcat(false, BITVECTOR_SGT, 2);
  }

  /* Sext */

  void testGetScBvSextUltTrue()
  {
    runTestSext(true, BITVECTOR_ULT);
  }

  void testGetScBvSextUltFalse()
  {
    runTestSext(false, BITVECTOR_ULT);
  }

  void testGetScBvSextUgtTrue()
  {
    runTestSext(true, BITVECTOR_UGT);
  }

  void testGetScBvSextUgtFalse()
  {
    runTestSext(false, BITVECTOR_UGT);
  }

  void testGetScBvSextSltTrue()
  {
    runTestSext(true, BITVECTOR_SLT);
  }

  void testGetScBvSextSltFalse()
  {
    runTestSext(false, BITVECTOR_SLT);
  }

  void testGetScBvSextSgtTrue()
  {
    runTestSext(true, BITVECTOR_SGT);
  }

  void testGetScBvSextSgtFalse()
  {
    runTestSext(false, BITVECTOR_SGT);
  }

};
