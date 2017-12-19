/*********************                                                        */
/*! \file theory_quantifiers_bv_inverter_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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
                   unsigned idx,
                   Node (*getsc)(bool, Kind, unsigned, Node, Node))
  {
    Assert(k == BITVECTOR_ULT || k == BITVECTOR_SLT || k == EQUAL);
    Assert(k != EQUAL || pol == false);

    Node sc = getsc(pol, k, idx, d_sk, d_t);
    Kind ksc = sc.getKind();
    TS_ASSERT((k == BITVECTOR_ULT && pol == false)
           || (k == BITVECTOR_SLT && pol == false)
           || ksc == IMPLIES);
    Node scl = ksc == IMPLIES ? sc[0] : bv::utils::mkTrue();
    if (!pol)
    {
      k = k == BITVECTOR_ULT
        ? BITVECTOR_UGE
        : (k == BITVECTOR_SLT ? BITVECTOR_SGE : DISTINCT);
    }
    Node body = idx == 0
      ? d_nm->mkNode(k, d_x, d_t)
      : d_nm->mkNode(k, d_t, d_x);
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
    Assert(k != BITVECTOR_UREM_TOTAL || pol == false || idx == 1);

    Node sc = getsc(pol, litk, k, idx, d_sk, d_s, d_t);
    TS_ASSERT (litk != EQUAL || sc != Node::null());
    Kind ksc = sc.getKind();
    TS_ASSERT((k == BITVECTOR_UDIV_TOTAL && idx == 1 && pol == false)
              || (k == BITVECTOR_ASHR && idx == 0 && pol == false)
              || ksc == IMPLIES);
    Node scl = ksc == IMPLIES ? sc[0] : bv::utils::mkTrue();
    Node body = idx == 0
      ? d_nm->mkNode(pol ? EQUAL : DISTINCT, d_nm->mkNode(k, d_x, d_s), d_t)
      : d_nm->mkNode(pol ? EQUAL : DISTINCT, d_nm->mkNode(k, d_s, d_x), d_t);
    Node scr = d_nm->mkNode(EXISTS, d_bvarlist, body);
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

 public:
  TheoryQuantifiersBvInverter() {}

  void setUp()
  {
    d_em = new ExprManager();
    d_nm = NodeManager::fromExprManager(d_em);
    d_smt = new SmtEngine(d_em);
    d_smt->setOption("cbqi-bv", CVC4::SExpr(false));
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

  void testGetScBvUltTrue0()
  {
    runTestPred(true, BITVECTOR_ULT, 0, getScBvUlt);
  }

  void testGetScBvUltTrue1()
  {
    runTestPred(true, BITVECTOR_ULT, 1, getScBvUlt);
  }

  void testGetScBvUltFalse0()
  {
    runTestPred(false, BITVECTOR_ULT, 0, getScBvUlt);
  }

  void testGetScBvUltFalse1()
  {
    runTestPred(false, BITVECTOR_ULT, 1, getScBvUlt);
  }

  void testGetScBvSltTrue0()
  {
    runTestPred(true, BITVECTOR_SLT, 0, getScBvSlt);
  }

  void testGetScBvSltTrue1()
  {
    runTestPred(true, BITVECTOR_SLT, 1, getScBvSlt);
  }

  void testGetScBvSltFalse0()
  {
    runTestPred(false, BITVECTOR_SLT, 0, getScBvSlt);
  }

  void testGetScBvSltFalse1()
  {
    runTestPred(false, BITVECTOR_SLT, 1, getScBvSlt);
  }

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

  void testGetScBvUremEqTrue0()
  {
    TS_ASSERT_THROWS(runTest(true, EQUAL, BITVECTOR_UREM_TOTAL, 0, getScBvUrem),
                     AssertionException);
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
  void testGetScBvUdivEqTrue0()
  {
    runTest(true, EQUAL, BITVECTOR_UDIV_TOTAL, 0, getScBvUdiv);
  }

  void testGetScBvUdivEqTrue1()
  {
    runTest(true, EQUAL, BITVECTOR_UDIV_TOTAL, 1, getScBvUdiv);
  }

  void testGetScBvUdivFalse0()
  {
    runTest(false, EQUAL, BITVECTOR_UDIV_TOTAL, 0, getScBvUdiv);
  }

  void testGetScBvUdivFalse1()
  {
    runTest(false, EQUAL, BITVECTOR_UDIV_TOTAL, 1, getScBvUdiv);
  }

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
};
