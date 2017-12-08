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
    Assert(k == kind::BITVECTOR_ULT
        || k == kind::BITVECTOR_SLT
        || k == kind::EQUAL);
    Assert(k != kind::EQUAL || pol == false);

    Node sc = getsc(pol, k, idx, d_sk, d_t);
    Kind ksc = sc.getKind();
    TS_ASSERT((k == kind::BITVECTOR_ULT && pol == false)
           || (k == kind::BITVECTOR_SLT && pol == false)
           || ksc == kind::IMPLIES);
    Node scl = ksc == kind::IMPLIES ? sc[0] : bv::utils::mkTrue();
    if (!pol)
    {
      k = k == kind::BITVECTOR_ULT
        ? kind::BITVECTOR_UGE
        : (k == kind::BITVECTOR_SLT ? kind::BITVECTOR_SGE : kind::DISTINCT);
    }
    Node body = idx == 0
      ? d_nm->mkNode(k, d_x, d_t)
      : d_nm->mkNode(k, d_t, d_x);
    Node scr = d_nm->mkNode(kind::EXISTS, d_bvarlist, body);
    Expr a = d_nm->mkNode(kind::DISTINCT, scl, scr).toExpr();
    Result res = d_smt->checkSat(a);
    TS_ASSERT(res.d_sat == Result::UNSAT);
  }

  void runTest(Kind k,
               unsigned idx,
               Node (*getsc)(Kind, unsigned, Node, Node, Node))
  {
    Assert(k == kind::BITVECTOR_MULT
           || k == kind::BITVECTOR_UREM_TOTAL
           || k == kind::BITVECTOR_UDIV_TOTAL
           || k == kind::BITVECTOR_AND
           || k == kind::BITVECTOR_OR
           || k == kind::BITVECTOR_LSHR
           || k == kind::BITVECTOR_ASHR
           || k == kind::BITVECTOR_SHL);
    Assert(k != kind::BITVECTOR_UREM_TOTAL || idx == 1);
    Assert((k != kind::BITVECTOR_LSHR
            && k != kind::BITVECTOR_ASHR
            && k != kind::BITVECTOR_SHL)
           || idx == 0);

    Node sc = getsc(k, idx, d_sk, d_s, d_t);
    Kind ksc = sc.getKind();
    TS_ASSERT(ksc == kind::IMPLIES);
    Node body = idx == 0
      ? d_nm->mkNode(k, d_x, d_s).eqNode(d_t)
      : d_nm->mkNode(k, d_s, d_x).eqNode(d_t);
    Node scr = d_nm->mkNode(kind::EXISTS, d_bvarlist, body);
    Expr a = d_nm->mkNode(kind::DISTINCT, sc[0], scr).toExpr();
    Result res = d_smt->checkSat(a);
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
    d_scope = new SmtScope(d_smt);

    d_s = d_nm->mkVar("s", d_nm->mkBitVectorType(4));
    d_t = d_nm->mkVar("t", d_nm->mkBitVectorType(4));
    d_sk = d_nm->mkSkolem("sk", d_t.getType());
    d_x = d_nm->mkBoundVar(d_t.getType());
    d_bvarlist = d_nm->mkNode(kind::BOUND_VAR_LIST, { d_x });
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

  void testGetScBvEq0()
  {
    runTestPred(false, EQUAL, 0, getScBvEq);
    TS_ASSERT_THROWS(runTestPred(true, EQUAL, 0, getScBvEq),
                     AssertionException);
  }

  void testGetScBvEq1()
  {
    runTestPred(false, EQUAL, 1, getScBvEq);
    TS_ASSERT_THROWS(runTestPred(true, EQUAL, 1, getScBvEq),
                     AssertionException);
  }

  void testGetScBvMult0()
  {
    runTest(BITVECTOR_MULT, 0, getScBvMult);
  }

  void testGetScBvMult1()
  {
    runTest(BITVECTOR_MULT, 1, getScBvMult);
  }

  void testGetScBvUrem0()
  {
    TS_ASSERT_THROWS(runTest(BITVECTOR_UREM_TOTAL, 0, getScBvUrem),
                     AssertionException);
  }

  void testGetScBvUrem1()
  {
    runTest(BITVECTOR_UREM_TOTAL, 1, getScBvUrem);
  }

  void testGetScBvUdiv0()
  {
    runTest(BITVECTOR_UDIV_TOTAL, 0, getScBvUdiv);
  }

  void testGetScBvUdiv1()
  {
    runTest(BITVECTOR_UDIV_TOTAL, 1, getScBvUdiv);
  }

  void testGetScBvAnd0()
  {
    runTest(BITVECTOR_AND, 0, getScBvAndOr);
  }

  void testGetScBvAnd1()
  {
    runTest(BITVECTOR_AND, 1, getScBvAndOr);
  }

  void testGetScBvOr0()
  {
    runTest(BITVECTOR_OR, 0, getScBvAndOr);
  }

  void testGetScBvOr1()
  {
    runTest(BITVECTOR_OR, 1, getScBvAndOr);
  }

  void testGetScBvLshr0()
  {
    runTest(BITVECTOR_LSHR, 0, getScBvLshr);
  }

  void testGetScBvLshr1()
  {
    TS_ASSERT_THROWS(runTest(BITVECTOR_LSHR, 1, getScBvLshr),
                     AssertionException);
  }

  void testGetScBvAshr0()
  {
    runTest(BITVECTOR_ASHR, 0, getScBvAshr);
  }

  void testGetScBvAshr1()
  {
    TS_ASSERT_THROWS(runTest(BITVECTOR_ASHR, 1, getScBvAshr),
                     AssertionException);
  }

  void testGetScBvShl0()
  {
    runTest(BITVECTOR_SHL, 0, getScBvShl);
  }

  void testGetScBvShl1()
  {
    TS_ASSERT_THROWS(runTest(BITVECTOR_SHL, 1, getScBvShl),
                     AssertionException);
  }

};
