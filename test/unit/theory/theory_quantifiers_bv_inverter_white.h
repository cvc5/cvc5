/*********************                                                        */
/*! \file theory_quantifiers_bv_inverter_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Mathias Preiner, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Unit tests for BV inverter.
 **
 ** Unit tests for BV inverter.
 **/

#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/quantifiers/bv_inverter_utils.h"
#include "util/result.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::theory::quantifiers::utils;
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
    TS_ASSERT(k == BITVECTOR_ULT || k == BITVECTOR_SLT || k == EQUAL
              || k == BITVECTOR_UGT || k == BITVECTOR_SGT);
    TS_ASSERT(k != EQUAL || pol == false);

    Node sc = getsc(pol, k, d_sk, d_t);
    Kind ksc = sc.getKind();
    TS_ASSERT((k == BITVECTOR_ULT && pol == false)
              || (k == BITVECTOR_SLT && pol == false)
              || (k == BITVECTOR_UGT && pol == false)
              || (k == BITVECTOR_SGT && pol == false) || ksc == IMPLIES);
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
        TS_ASSERT(k == EQUAL);
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
    TS_ASSERT(k == BITVECTOR_MULT || k == BITVECTOR_UREM_TOTAL
              || k == BITVECTOR_UDIV_TOTAL || k == BITVECTOR_AND
              || k == BITVECTOR_OR || k == BITVECTOR_LSHR || k == BITVECTOR_ASHR
              || k == BITVECTOR_SHL);

    Node sc = getsc(pol, litk, k, idx, d_sk, d_s, d_t);
    TS_ASSERT(!sc.isNull());
    Kind ksc = sc.getKind();
    TS_ASSERT((k == BITVECTOR_UDIV_TOTAL && idx == 1 && pol == false)
              || (k == BITVECTOR_ASHR && idx == 0 && pol == false)
              || ksc == IMPLIES);
    Node scl = ksc == IMPLIES ? sc[0] : bv::utils::mkTrue();
    Node body = idx == 0 ? d_nm->mkNode(litk, d_nm->mkNode(k, d_x, d_s), d_t)
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
      sc = getICBvConcat(pol, litk, 0, sk, sv_t, t);
    }
    else if (idx == 1)
    {
      s1 = d_nm->mkVar("s1", d_nm->mkBitVectorType(4));
      x = d_nm->mkBoundVar(s1.getType());
      sk = d_nm->mkSkolem("sk", s1.getType());
      t = d_nm->mkVar("t", d_nm->mkBitVectorType(8));
      sv_t = d_nm->mkNode(BITVECTOR_CONCAT, s1, x);
      sc = getICBvConcat(pol, litk, 1, sk, sv_t, t);
    }
    else
    {
      TS_ASSERT(idx == 2);
      s1 = d_nm->mkVar("s1", d_nm->mkBitVectorType(4));
      s2 = d_nm->mkVar("s2", d_nm->mkBitVectorType(4));
      x = d_nm->mkBoundVar(s2.getType());
      sk = d_nm->mkSkolem("sk", s1.getType());
      t = d_nm->mkVar("t", d_nm->mkBitVectorType(12));
      sv_t = d_nm->mkNode(BITVECTOR_CONCAT, s1, x, s2);
      sc = getICBvConcat(pol, litk, 1, sk, sv_t, t);
    }

    TS_ASSERT(!sc.isNull());
    Kind ksc = sc.getKind();
    TS_ASSERT((litk == kind::EQUAL && pol == false) || ksc == IMPLIES);
    Node scl = ksc == IMPLIES ? sc[0] : bv::utils::mkTrue();
    Node body = d_nm->mkNode(litk, sv_t, t);
    Node bvarlist = d_nm->mkNode(BOUND_VAR_LIST, {x});
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
    Node sc = getICBvSext(pol, litk, 0, sk, sv_t, t);

    TS_ASSERT(!sc.isNull());
    Kind ksc = sc.getKind();
    TS_ASSERT((litk == kind::EQUAL && pol == false)
              || (litk == kind::BITVECTOR_ULT && pol == false)
              || (litk == kind::BITVECTOR_UGT && pol == false)
              || ksc == IMPLIES);
    Node scl = ksc == IMPLIES ? sc[0] : bv::utils::mkTrue();
    Node body = d_nm->mkNode(litk, sv_t, t);
    Node bvarlist = d_nm->mkNode(BOUND_VAR_LIST, {x});
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
    d_smt->setOption("cegqi-full", CVC4::SExpr(true));
    d_smt->setOption("produce-models", CVC4::SExpr(true));
    d_scope = new SmtScope(d_smt);

    d_s = d_nm->mkVar("s", d_nm->mkBitVectorType(4));
    d_t = d_nm->mkVar("t", d_nm->mkBitVectorType(4));
    d_sk = d_nm->mkSkolem("sk", d_t.getType());
    d_x = d_nm->mkBoundVar(d_t.getType());
    d_bvarlist = d_nm->mkNode(BOUND_VAR_LIST, {d_x});
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
    runTestPred(true, BITVECTOR_ULT, d_x, getICBvUltUgt);
  }

  void testGetScBvUltFalse()
  {
    runTestPred(false, BITVECTOR_ULT, d_x, getICBvUltUgt);
  }

  void testGetScBvUgtTrue()
  {
    runTestPred(true, BITVECTOR_UGT, d_x, getICBvUltUgt);
  }

  void testGetScBvUgtFalse()
  {
    runTestPred(false, BITVECTOR_UGT, d_x, getICBvUltUgt);
  }

  void testGetScBvSltTrue()
  {
    runTestPred(true, BITVECTOR_SLT, d_x, getICBvSltSgt);
  }

  void testGetScBvSltFalse()
  {
    runTestPred(false, BITVECTOR_SLT, d_x, getICBvSltSgt);
  }

  void testGetScBvSgtTrue()
  {
    runTestPred(true, BITVECTOR_SGT, d_x, getICBvSltSgt);
  }

  void testGetScBvSgtFalse()
  {
    runTestPred(false, BITVECTOR_SGT, d_x, getICBvSltSgt);
  }

  /* Equality and Disequality ----------------------------------------------  */

  /* Mult */

  void testGetScBvMultEqTrue0()
  {
    runTest(true, EQUAL, BITVECTOR_MULT, 0, getICBvMult);
  }

  void testGetScBvMultEqTrue1()
  {
    runTest(true, EQUAL, BITVECTOR_MULT, 1, getICBvMult);
  }

  void testGetScBvMultEqFalse0()
  {
    runTest(false, EQUAL, BITVECTOR_MULT, 0, getICBvMult);
  }

  void testGetScBvMultEqFalse1()
  {
    runTest(false, EQUAL, BITVECTOR_MULT, 1, getICBvMult);
  }

  /* Urem */

  void testGetScBvUremEqTrue0()
  {
    runTest(true, EQUAL, BITVECTOR_UREM_TOTAL, 0, getICBvUrem);
  }

  void testGetScBvUremEqTrue1()
  {
    runTest(true, EQUAL, BITVECTOR_UREM_TOTAL, 1, getICBvUrem);
  }

  void testGetScBvUremEqFalse0()
  {
    runTest(false, EQUAL, BITVECTOR_UREM_TOTAL, 0, getICBvUrem);
  }

  void testGetScBvUremEqFalse1()
  {
    runTest(false, EQUAL, BITVECTOR_UREM_TOTAL, 1, getICBvUrem);
  }

  /* Udiv */
  void testGetScBvUdivEqTrue0()
  {
    runTest(true, EQUAL, BITVECTOR_UDIV_TOTAL, 0, getICBvUdiv);
  }

  void testGetScBvUdivEqTrue1()
  {
    runTest(true, EQUAL, BITVECTOR_UDIV_TOTAL, 1, getICBvUdiv);
  }

  void testGetScBvUdivEqFalse0()
  {
    runTest(false, EQUAL, BITVECTOR_UDIV_TOTAL, 0, getICBvUdiv);
  }

  void testGetScBvUdivEqFalse1()
  {
    runTest(false, EQUAL, BITVECTOR_UDIV_TOTAL, 1, getICBvUdiv);
  }

  /* And */

  void testGetScBvAndEqTrue0()
  {
    runTest(true, EQUAL, BITVECTOR_AND, 0, getICBvAndOr);
  }

  void testGetScBvAndEqTrue1()
  {
    runTest(true, EQUAL, BITVECTOR_AND, 1, getICBvAndOr);
  }

  void testGetScBvAndEqFalse0()
  {
    runTest(false, EQUAL, BITVECTOR_AND, 0, getICBvAndOr);
  }

  void testGetScBvAndEqFalse1()
  {
    runTest(false, EQUAL, BITVECTOR_AND, 1, getICBvAndOr);
  }

  /* Or */

  void testGetScBvOrEqTrue0()
  {
    runTest(true, EQUAL, BITVECTOR_OR, 0, getICBvAndOr);
  }

  void testGetScBvOrEqTrue1()
  {
    runTest(true, EQUAL, BITVECTOR_OR, 1, getICBvAndOr);
  }

  void testGetScBvOrEqFalse0()
  {
    runTest(false, EQUAL, BITVECTOR_OR, 0, getICBvAndOr);
  }

  void testGetScBvOrEqFalse1()
  {
    runTest(false, EQUAL, BITVECTOR_OR, 1, getICBvAndOr);
  }

  /* Lshr */

  void testGetScBvLshrEqTrue0()
  {
    runTest(true, EQUAL, BITVECTOR_LSHR, 0, getICBvLshr);
  }

  void testGetScBvLshrEqTrue1()
  {
    runTest(true, EQUAL, BITVECTOR_LSHR, 1, getICBvLshr);
  }

  void testGetScBvLshrEqFalse0()
  {
    runTest(false, EQUAL, BITVECTOR_LSHR, 0, getICBvLshr);
  }

  void testGetScBvLshrEqFalse1()
  {
    runTest(false, EQUAL, BITVECTOR_LSHR, 1, getICBvLshr);
  }

  /* Ashr */

  void testGetScBvAshrEqTrue0()
  {
    runTest(true, EQUAL, BITVECTOR_ASHR, 0, getICBvAshr);
  }

  void testGetScBvAshrEqTrue1()
  {
    runTest(true, EQUAL, BITVECTOR_ASHR, 1, getICBvAshr);
  }

  void testGetScBvAshrEqFalse0()
  {
    runTest(false, EQUAL, BITVECTOR_ASHR, 0, getICBvAshr);
  }

  void testGetScBvAshrEqFalse1()
  {
    runTest(false, EQUAL, BITVECTOR_ASHR, 1, getICBvAshr);
  }

  /* Shl */

  void testGetScBvShlEqTrue0()
  {
    runTest(true, EQUAL, BITVECTOR_SHL, 0, getICBvShl);
  }

  void testGetScBvShlEqTrue1()
  {
    runTest(true, EQUAL, BITVECTOR_SHL, 1, getICBvShl);
  }

  void testGetScBvShlEqFalse0()
  {
    runTest(false, EQUAL, BITVECTOR_SHL, 0, getICBvShl);
  }

  void testGetScBvShlEqFalse1()
  {
    runTest(false, EQUAL, BITVECTOR_SHL, 1, getICBvShl);
  }

  /* Concat */

  void testGetScBvConcatEqTrue0() { runTestConcat(true, EQUAL, 0); }

  void testGetScBvConcatEqTrue1() { runTestConcat(true, EQUAL, 1); }

  void testGetScBvConcatEqTrue2() { runTestConcat(true, EQUAL, 2); }

  void testGetScBvConcatEqFalse0() { runTestConcat(false, EQUAL, 0); }

  void testGetScBvConcatEqFalse1() { runTestConcat(false, EQUAL, 1); }

  void testGetScBvConcatEqFalse2() { runTestConcat(false, EQUAL, 2); }

  /* Sext */

  void testGetScBvSextEqTrue() { runTestSext(true, EQUAL); }

  void testGetScBvSextEqFalse() { runTestSext(false, EQUAL); }

  /* Inequality ------------------------------------------------------------  */

  /* Not */

  void testGetScBvNotUltTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(true, BITVECTOR_ULT, x, getICBvUltUgt);
  }

  void testGetScBvNotUltTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(true, BITVECTOR_ULT, x, getICBvUltUgt);
  }

  void testGetScBvNotUltFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(false, BITVECTOR_ULT, x, getICBvUltUgt);
  }

  void testGetScBvNotUltFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(false, BITVECTOR_ULT, x, getICBvUltUgt);
  }

  void testGetScBvNotUgtTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(true, BITVECTOR_UGT, x, getICBvUltUgt);
  }

  void testGetScBvNotUgtTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(true, BITVECTOR_UGT, x, getICBvUltUgt);
  }

  void testGetScBvNotUgtFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(false, BITVECTOR_UGT, x, getICBvUltUgt);
  }

  void testGetScBvNotUgtFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(false, BITVECTOR_UGT, x, getICBvUltUgt);
  }

  void testGetScBvNotSltTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(true, BITVECTOR_SLT, x, getICBvSltSgt);
  }

  void testGetScBvNotSltTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(true, BITVECTOR_SLT, x, getICBvSltSgt);
  }

  void testGetScBvNotSltFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(false, BITVECTOR_SLT, x, getICBvSltSgt);
  }

  void testGetScBvNotSltFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(false, BITVECTOR_SLT, x, getICBvSltSgt);
  }

  void testGetScBvNotSgtTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(true, BITVECTOR_SGT, x, getICBvSltSgt);
  }

  void testGetScBvNotSgtTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(true, BITVECTOR_SGT, x, getICBvSltSgt);
  }

  void testGetScBvNotSgtFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(false, BITVECTOR_SGT, x, getICBvSltSgt);
  }

  void testGetScBvNotSgtFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NOT, d_x);
    runTestPred(false, BITVECTOR_SGT, x, getICBvSltSgt);
  }

  /* Neg */

  void testGetScBvNegUltTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(true, BITVECTOR_ULT, x, getICBvUltUgt);
  }

  void testGetScBvNegUltTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(true, BITVECTOR_ULT, x, getICBvUltUgt);
  }

  void testGetScBvNegUltFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(false, BITVECTOR_ULT, x, getICBvUltUgt);
  }

  void testGetScBvNegUltFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(false, BITVECTOR_ULT, x, getICBvUltUgt);
  }

  void testGetScBvNegUgtTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(true, BITVECTOR_UGT, x, getICBvUltUgt);
  }

  void testGetScBvNegUgtTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(true, BITVECTOR_UGT, x, getICBvUltUgt);
  }

  void testGetScBvNegUgtFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(false, BITVECTOR_UGT, x, getICBvUltUgt);
  }

  void testGetScBvNegUgtFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(false, BITVECTOR_UGT, x, getICBvUltUgt);
  }

  void testGetScBvNegSltTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(true, BITVECTOR_SLT, x, getICBvSltSgt);
  }

  void testGetScBvNegSltTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(true, BITVECTOR_SLT, x, getICBvSltSgt);
  }

  void testGetScBvNegSltFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(false, BITVECTOR_SLT, x, getICBvSltSgt);
  }

  void testGetScBvNegSltFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(false, BITVECTOR_SLT, x, getICBvSltSgt);
  }

  void testGetScBvNegSgtTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(true, BITVECTOR_SGT, x, getICBvSltSgt);
  }

  void testGetScBvNegSgtTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(true, BITVECTOR_SGT, x, getICBvSltSgt);
  }

  void testGetScBvNegSgtFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(false, BITVECTOR_SGT, x, getICBvSltSgt);
  }

  void testGetScBvNegSgtFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_NEG, d_x);
    runTestPred(false, BITVECTOR_SGT, x, getICBvSltSgt);
  }

  /* Add */

  void testGetScBvPlusUltTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_x, d_s);
    runTestPred(true, BITVECTOR_ULT, x, getICBvUltUgt);
  }

  void testGetScBvPlusUltTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_s, d_x);
    runTestPred(true, BITVECTOR_ULT, x, getICBvUltUgt);
  }

  void testGetScBvPlusUltFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_x, d_s);
    runTestPred(false, BITVECTOR_ULT, x, getICBvUltUgt);
  }

  void testGetScBvPlusUltFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_s, d_x);
    runTestPred(false, BITVECTOR_ULT, x, getICBvUltUgt);
  }

  void testGetScBvPlusUgtTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_x, d_s);
    runTestPred(true, BITVECTOR_UGT, x, getICBvUltUgt);
  }

  void testGetScBvPlusUgtTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_s, d_x);
    runTestPred(true, BITVECTOR_UGT, x, getICBvUltUgt);
  }

  void testGetScBvPlusUgtFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_x, d_s);
    runTestPred(false, BITVECTOR_UGT, x, getICBvUltUgt);
  }

  void testGetScBvPlusUgtFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_s, d_x);
    runTestPred(false, BITVECTOR_UGT, x, getICBvUltUgt);
  }

  void testGetScBvPlusSltTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_x, d_s);
    runTestPred(true, BITVECTOR_SLT, x, getICBvSltSgt);
  }

  void testGetScBvPlusSltTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_s, d_x);
    runTestPred(true, BITVECTOR_SLT, x, getICBvSltSgt);
  }

  void testGetScBvPlusSltFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_x, d_s);
    runTestPred(false, BITVECTOR_SLT, x, getICBvSltSgt);
  }

  void testGetScBvPlusSltFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_s, d_x);
    runTestPred(false, BITVECTOR_SLT, x, getICBvSltSgt);
  }

  void testGetScBvPlusSgtTrue0()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_x, d_s);
    runTestPred(true, BITVECTOR_SGT, x, getICBvSltSgt);
  }

  void testGetScBvPlusSgtTrue1()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_s, d_x);
    runTestPred(true, BITVECTOR_SGT, x, getICBvSltSgt);
  }

  void testGetScBvPlusSgtFalse0()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_x, d_s);
    runTestPred(false, BITVECTOR_SGT, x, getICBvSltSgt);
  }

  void testGetScBvPlusSgtFalse1()
  {
    Node x = d_nm->mkNode(BITVECTOR_PLUS, d_s, d_x);
    runTestPred(false, BITVECTOR_SGT, x, getICBvSltSgt);
  }

  /* Mult */

  void testGetScBvMultUltTrue0()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_MULT, 0, getICBvMult);
  }

  void testGetScBvMultUltTrue1()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_MULT, 1, getICBvMult);
  }

  void testGetScBvMultUltFalse0()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_MULT, 0, getICBvMult);
  }

  void testGetScBvMultUltFalse1()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_MULT, 1, getICBvMult);
  }

  void testGetScBvMultUgtTrue0()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_MULT, 0, getICBvMult);
  }

  void testGetScBvMultUgtTrue1()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_MULT, 1, getICBvMult);
  }

  void testGetScBvMultUgtFalse0()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_MULT, 0, getICBvMult);
  }

  void testGetScBvMultUgtFalse1()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_MULT, 1, getICBvMult);
  }

  void testGetScBvMultSltTrue0()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_MULT, 0, getICBvMult);
  }

  void testGetScBvMultSltTrue1()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_MULT, 1, getICBvMult);
  }

  void testGetScBvMultSltFalse0()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_MULT, 0, getICBvMult);
  }

  void testGetScBvMultSltFalse1()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_MULT, 1, getICBvMult);
  }

  void testGetScBvMultSgtTrue0()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_MULT, 0, getICBvMult);
  }

  void testGetScBvMultSgtTrue1()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_MULT, 1, getICBvMult);
  }

  void testGetScBvMultSgtFalse0()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_MULT, 0, getICBvMult);
  }

  void testGetScBvMultSgtFalse1()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_MULT, 1, getICBvMult);
  }

  /* Urem */

  void testGetScBvUremUltTrue0()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_UREM_TOTAL, 0, getICBvUrem);
  }

  void testGetScBvUremUltTrue1()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_UREM_TOTAL, 1, getICBvUrem);
  }

  void testGetScBvUremUltFalse0()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_UREM_TOTAL, 0, getICBvUrem);
  }

  void testGetScBvUremUltFalse1()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_UREM_TOTAL, 1, getICBvUrem);
  }

  void testGetScBvUremUgtTrue0()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_UREM_TOTAL, 0, getICBvUrem);
  }

  void testGetScBvUremUgtTrue1()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_UREM_TOTAL, 1, getICBvUrem);
  }

  void testGetScBvUremUgtFalse0()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_UREM_TOTAL, 0, getICBvUrem);
  }

  void testGetScBvUremUgtFalse1()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_UREM_TOTAL, 1, getICBvUrem);
  }

  void testGetScBvUremSltTrue0()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_UREM_TOTAL, 0, getICBvUrem);
  }

  void testGetScBvUremSltTrue1()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_UREM_TOTAL, 1, getICBvUrem);
  }

  void testGetScBvUremSltFalse0()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_UREM_TOTAL, 0, getICBvUrem);
  }

  void testGetScBvUremSltFalse1()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_UREM_TOTAL, 1, getICBvUrem);
  }

  void testGetScBvUremSgtTrue0()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_UREM_TOTAL, 0, getICBvUrem);
  }

  void testGetScBvUremSgtTrue1()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_UREM_TOTAL, 1, getICBvUrem);
  }

  void testGetScBvUremSgtFalse0()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_UREM_TOTAL, 0, getICBvUrem);
  }

  void testGetScBvUremSgtFalse1()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_UREM_TOTAL, 1, getICBvUrem);
  }

  /* Udiv */

  void testGetScBvUdivUltTrue0()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_UDIV_TOTAL, 0, getICBvUdiv);
  }

  void testGetScBvUdivUltTrue1()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_UDIV_TOTAL, 1, getICBvUdiv);
  }

  void testGetScBvUdivUltFalse0()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_UDIV_TOTAL, 0, getICBvUdiv);
  }

  void testGetScBvUdivUltFalse1()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_UDIV_TOTAL, 1, getICBvUdiv);
  }

  void testGetScBvUdivUgtTrue0()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_UDIV_TOTAL, 0, getICBvUdiv);
  }

  void testGetScBvUdivUgtTrue1()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_UDIV_TOTAL, 1, getICBvUdiv);
  }

  void testGetScBvUdivUgtFalse0()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_UDIV_TOTAL, 0, getICBvUdiv);
  }

  void testGetScBvUdivUgtFalse1()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_UDIV_TOTAL, 1, getICBvUdiv);
  }

  void testGetScBvUdivSltTrue0()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_UDIV_TOTAL, 0, getICBvUdiv);
  }

  void testGetScBvUdivSltTrue1()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_UDIV_TOTAL, 1, getICBvUdiv);
  }

  void testGetScBvUdivSltFalse0()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_UDIV_TOTAL, 0, getICBvUdiv);
  }

  void testGetScBvUdivSltFalse1()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_UDIV_TOTAL, 1, getICBvUdiv);
  }

  void testGetScBvUdivSgtTrue0()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_UDIV_TOTAL, 0, getICBvUdiv);
  }

  void testGetScBvUdivSgtTrue1()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_UDIV_TOTAL, 1, getICBvUdiv);
  }

  void testGetScBvUdivSgtFalse0()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_UDIV_TOTAL, 0, getICBvUdiv);
  }

  void testGetScBvUdivSgtFalse1()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_UDIV_TOTAL, 1, getICBvUdiv);
  }

  /* And */

  void testGetScBvAndUltTrue0()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_AND, 0, getICBvAndOr);
  }

  void testGetScBvAndUltTrue1()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_AND, 1, getICBvAndOr);
  }

  void testGetScBvAndUltFalse0()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_AND, 0, getICBvAndOr);
  }

  void testGetScBvAndUltFalse1()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_AND, 1, getICBvAndOr);
  }

  void testGetScBvAndUgtTrue0()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_AND, 0, getICBvAndOr);
  }

  void testGetScBvAndUgtTrue1()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_AND, 1, getICBvAndOr);
  }

  void testGetScBvAndUgtFalse0()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_AND, 0, getICBvAndOr);
  }

  void testGetScBvAndUgtFalse1()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_AND, 1, getICBvAndOr);
  }

  void testGetScBvAndSltTrue0()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_AND, 0, getICBvAndOr);
  }

  void testGetScBvAndSltTrue1()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_AND, 1, getICBvAndOr);
  }

  void testGetScBvAndSltFalse0()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_AND, 0, getICBvAndOr);
  }

  void testGetScBvAndSltFalse1()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_AND, 1, getICBvAndOr);
  }

  void testGetScBvAndSgtTrue0()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_AND, 0, getICBvAndOr);
  }

  void testGetScBvAndSgtTrue1()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_AND, 1, getICBvAndOr);
  }

  void testGetScBvAndSgtFalse0()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_AND, 0, getICBvAndOr);
  }

  void testGetScBvAndSgtFalse1()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_AND, 1, getICBvAndOr);
  }

  /* Or */

  void testGetScBvOrUltTrue0()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_OR, 0, getICBvAndOr);
  }

  void testGetScBvOrUltTrue1()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_OR, 1, getICBvAndOr);
  }

  void testGetScBvOrUltFalse0()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_OR, 0, getICBvAndOr);
  }

  void testGetScBvOrUltFalse1()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_OR, 1, getICBvAndOr);
  }

  void testGetScBvOrUgtTrue0()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_OR, 0, getICBvAndOr);
  }

  void testGetScBvOrUgtTrue1()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_OR, 1, getICBvAndOr);
  }

  void testGetScBvOrUgtFalse0()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_OR, 0, getICBvAndOr);
  }

  void testGetScBvOrUgtFalse1()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_OR, 1, getICBvAndOr);
  }

  void testGetScBvOrSltTrue0()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_OR, 0, getICBvAndOr);
  }

  void testGetScBvOrSltTrue1()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_OR, 1, getICBvAndOr);
  }

  void testGetScBvOrSltFalse0()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_OR, 0, getICBvAndOr);
  }

  void testGetScBvOrSltFalse1()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_OR, 1, getICBvAndOr);
  }

  void testGetScBvOrSgtTrue0()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_OR, 0, getICBvAndOr);
  }

  void testGetScBvOrSgtTrue1()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_OR, 1, getICBvAndOr);
  }

  void testGetScBvOrSgtFalse0()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_OR, 0, getICBvAndOr);
  }

  void testGetScBvOrSgtFalse1()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_OR, 1, getICBvAndOr);
  }

  /* Lshr */

  void testGetScBvLshrUltTrue0()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_LSHR, 0, getICBvLshr);
  }

  void testGetScBvLshrUltTrue1()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_LSHR, 1, getICBvLshr);
  }

  void testGetScBvLshrUltFalse0()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_LSHR, 0, getICBvLshr);
  }

  void testGetScBvLshrUltFalse1()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_LSHR, 1, getICBvLshr);
  }

  void testGetScBvLshrUgtTrue0()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_LSHR, 0, getICBvLshr);
  }

  void testGetScBvLshrUgtTrue1()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_LSHR, 1, getICBvLshr);
  }

  void testGetScBvLshrUgtFalse0()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_LSHR, 0, getICBvLshr);
  }

  void testGetScBvLshrUgtFalse1()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_LSHR, 1, getICBvLshr);
  }

  void testGetScBvLshrSltTrue0()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_LSHR, 0, getICBvLshr);
  }

  void testGetScBvLshrSltTrue1()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_LSHR, 1, getICBvLshr);
  }

  void testGetScBvLshrSltFalse0()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_LSHR, 0, getICBvLshr);
  }

  void testGetScBvLshrSltFalse1()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_LSHR, 1, getICBvLshr);
  }

  void testGetScBvLshrSgtTrue0()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_LSHR, 0, getICBvLshr);
  }

  void testGetScBvLshrSgtTrue1()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_LSHR, 1, getICBvLshr);
  }

  void testGetScBvLshrSgtFalse0()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_LSHR, 0, getICBvLshr);
  }

  void testGetScBvLshrSgtFalse1()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_LSHR, 1, getICBvLshr);
  }

  /* Ashr */

  void testGetScBvAshrUltTrue0()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_ASHR, 0, getICBvAshr);
  }

  void testGetScBvAshrUltTrue1()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_ASHR, 1, getICBvAshr);
  }

  void testGetScBvAshrUltFalse0()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_ASHR, 0, getICBvAshr);
  }

  void testGetScBvAshrUltFalse1()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_ASHR, 1, getICBvAshr);
  }

  void testGetScBvAshrUgtTrue0()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_ASHR, 0, getICBvAshr);
  }

  void testGetScBvAshrUgtTrue1()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_ASHR, 1, getICBvAshr);
  }

  void testGetScBvAshrUgtFalse0()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_ASHR, 0, getICBvAshr);
  }

  void testGetScBvAshrUgtFalse1()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_ASHR, 1, getICBvAshr);
  }

  void testGetScBvAshrSltTrue0()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_ASHR, 0, getICBvAshr);
  }

  void testGetScBvAshrSltTrue1()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_ASHR, 1, getICBvAshr);
  }

  void testGetScBvAshrSltFalse0()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_ASHR, 0, getICBvAshr);
  }

  void testGetScBvAshrSltFalse1()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_ASHR, 1, getICBvAshr);
  }

  void testGetScBvAshrSgtTrue0()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_ASHR, 0, getICBvAshr);
  }

  void testGetScBvAshrSgtTrue1()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_ASHR, 1, getICBvAshr);
  }

  void testGetScBvAshrSgtFalse0()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_ASHR, 0, getICBvAshr);
  }

  void testGetScBvAshrSgtFalse1()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_ASHR, 1, getICBvAshr);
  }

  /* Shl */

  void testGetScBvShlUltTrue0()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_SHL, 0, getICBvShl);
  }

  void testGetScBvShlUltTrue1()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_SHL, 1, getICBvShl);
  }

  void testGetScBvShlUltFalse0()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_SHL, 0, getICBvShl);
  }

  void testGetScBvShlUltFalse1()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_SHL, 1, getICBvShl);
  }

  void testGetScBvShlUgtTrue0()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_SHL, 0, getICBvShl);
  }

  void testGetScBvShlUgtTrue1()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_SHL, 1, getICBvShl);
  }

  void testGetScBvShlUgtFalse0()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_SHL, 0, getICBvShl);
  }

  void testGetScBvShlUgtFalse1()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_SHL, 1, getICBvShl);
  }

  void testGetScBvShlSltTrue0()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_SHL, 0, getICBvShl);
  }

  void testGetScBvShlSltTrue1()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_SHL, 1, getICBvShl);
  }

  void testGetScBvShlSltFalse0()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_SHL, 0, getICBvShl);
  }

  void testGetScBvShlSltFalse1()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_SHL, 1, getICBvShl);
  }

  void testGetScBvShlSgtTrue0()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_SHL, 0, getICBvShl);
  }

  void testGetScBvShlSgtTrue1()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_SHL, 1, getICBvShl);
  }

  void testGetScBvShlSgtFalse0()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_SHL, 0, getICBvShl);
  }

  void testGetScBvShlSgtFalse1()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_SHL, 1, getICBvShl);
  }

  /* Concat */

  void testGetScBvConcatUltTrue0() { runTestConcat(true, BITVECTOR_ULT, 0); }

  void testGetScBvConcatUltTrue1() { runTestConcat(true, BITVECTOR_ULT, 1); }

  void testGetScBvConcatUltTrue2() { runTestConcat(true, BITVECTOR_ULT, 2); }

  void testGetScBvConcatUltFalse0() { runTestConcat(false, BITVECTOR_ULT, 0); }

  void testGetScBvConcatUltFalse1() { runTestConcat(false, BITVECTOR_ULT, 1); }

  void testGetScBvConcatUltFalse2() { runTestConcat(false, BITVECTOR_ULT, 2); }

  void testGetScBvConcatUgtTrue0() { runTestConcat(true, BITVECTOR_UGT, 0); }

  void testGetScBvConcatUgtTrue1() { runTestConcat(true, BITVECTOR_UGT, 1); }

  void testGetScBvConcatUgtTrue2() { runTestConcat(true, BITVECTOR_UGT, 2); }

  void testGetScBvConcatUgtFalse0() { runTestConcat(false, BITVECTOR_UGT, 0); }

  void testGetScBvConcatUgtFalse1() { runTestConcat(false, BITVECTOR_UGT, 1); }

  void testGetScBvConcatUgtFalse2() { runTestConcat(false, BITVECTOR_UGT, 2); }

  void testGetScBvConcatSltTrue0() { runTestConcat(true, BITVECTOR_SLT, 0); }

  void testGetScBvConcatSltTrue1() { runTestConcat(true, BITVECTOR_SLT, 1); }

  void testGetScBvConcatSltTrue2() { runTestConcat(true, BITVECTOR_SLT, 2); }

  void testGetScBvConcatSltFalse0() { runTestConcat(false, BITVECTOR_SLT, 0); }

  void testGetScBvConcatSltFalse1() { runTestConcat(false, BITVECTOR_SLT, 1); }

  void testGetScBvConcatSltFalse2() { runTestConcat(false, BITVECTOR_SLT, 2); }

  void testGetScBvConcatSgtTrue0() { runTestConcat(true, BITVECTOR_SGT, 0); }

  void testGetScBvConcatSgtTrue1() { runTestConcat(true, BITVECTOR_SGT, 1); }

  void testGetScBvConcatSgtTrue2() { runTestConcat(true, BITVECTOR_SGT, 2); }

  void testGetScBvConcatSgtFalse0() { runTestConcat(false, BITVECTOR_SGT, 0); }

  void testGetScBvConcatSgtFalse1() { runTestConcat(false, BITVECTOR_SGT, 1); }

  void testGetScBvConcatSgtFalse2() { runTestConcat(false, BITVECTOR_SGT, 2); }

  /* Sext */

  void testGetScBvSextUltTrue() { runTestSext(true, BITVECTOR_ULT); }

  void testGetScBvSextUltFalse() { runTestSext(false, BITVECTOR_ULT); }

  void testGetScBvSextUgtTrue() { runTestSext(true, BITVECTOR_UGT); }

  void testGetScBvSextUgtFalse() { runTestSext(false, BITVECTOR_UGT); }

  void testGetScBvSextSltTrue() { runTestSext(true, BITVECTOR_SLT); }

  void testGetScBvSextSltFalse() { runTestSext(false, BITVECTOR_SLT); }

  void testGetScBvSextSgtTrue() { runTestSext(true, BITVECTOR_SGT); }

  void testGetScBvSextSgtFalse() { runTestSext(false, BITVECTOR_SGT); }
};
