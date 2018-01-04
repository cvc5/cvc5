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
    Node body = d_nm->mkNode(k, d_x, d_t);
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
    Assert(k == BITVECTOR_PLUS
           || k == BITVECTOR_MULT
           || k == BITVECTOR_UREM_TOTAL
           || k == BITVECTOR_UDIV_TOTAL
           || k == BITVECTOR_AND
           || k == BITVECTOR_OR
           || k == BITVECTOR_LSHR
           || k == BITVECTOR_ASHR
           || k == BITVECTOR_SHL);

    Node sc = getsc(pol, litk, k, idx, d_sk, d_s, d_t);
    // TODO amend / remove the following six lines as soon as inequality
    // handling is implemented in getScBv*
    TS_ASSERT (litk != EQUAL || sc != Node::null());
    if (sc.isNull())
    {
      TS_ASSERT (litk == BITVECTOR_ULT || litk  == BITVECTOR_SLT
                 || litk == BITVECTOR_UGT || litk == BITVECTOR_SGT);
      return;
    }
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

  /* Generic side conditions for LT ---------------------------------------  */

  void testGetScBvUltTrue()
  {
    runTestPred(true, BITVECTOR_ULT, getScBvUltUgt);
  }

  void testGetScBvUltFalse()
  {
    runTestPred(false, BITVECTOR_ULT, getScBvUltUgt);
  }

  void testGetScBvUgtTrue()
  {
    runTestPred(true, BITVECTOR_UGT, getScBvUltUgt);
  }

  void testGetScBvUgtFalse()
  {
    runTestPred(false, BITVECTOR_UGT, getScBvUltUgt);
  }

  void testGetScBvSltTrue()
  {
    runTestPred(true, BITVECTOR_SLT, getScBvSltSgt);
  }

  void testGetScBvSltFalse()
  {
    runTestPred(false, BITVECTOR_SLT, getScBvSltSgt);
  }

  void testGetScBvSgtTrue()
  {
    runTestPred(true, BITVECTOR_SGT, getScBvSltSgt);
  }

  void testGetScBvSgtFalse()
  {
    runTestPred(false, BITVECTOR_SGT, getScBvSltSgt);
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

  /* Inequality ------------------------------------------------------------  */

  /* Plus */

  void testGetScBvPlusUltTrue0()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_PLUS, 0, getScBvPlus);
  }

  void testGetScBvPlusUltTrue1()
  {
    runTest(true, BITVECTOR_ULT, BITVECTOR_PLUS, 1, getScBvPlus);
  }

  void testGetScBvPlusUltFalse0()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_PLUS, 0, getScBvPlus);
  }

  void testGetScBvPlusUltFalse1()
  {
    runTest(false, BITVECTOR_ULT, BITVECTOR_PLUS, 1, getScBvPlus);
  }

  void testGetScBvPlusUgtTrue0()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_PLUS, 0, getScBvPlus);
  }

  void testGetScBvPlusUgtTrue1()
  {
    runTest(true, BITVECTOR_UGT, BITVECTOR_PLUS, 1, getScBvPlus);
  }

  void testGetScBvPlusUgtFalse0()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_PLUS, 0, getScBvPlus);
  }

  void testGetScBvPlusUgtFalse1()
  {
    runTest(false, BITVECTOR_UGT, BITVECTOR_PLUS, 1, getScBvPlus);
  }

  void testGetScBvPlusSltTrue0()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_PLUS, 0, getScBvPlus);
  }

  void testGetScBvPlusSltTrue1()
  {
    runTest(true, BITVECTOR_SLT, BITVECTOR_PLUS, 1, getScBvPlus);
  }

  void testGetScBvPlusSltFalse0()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_PLUS, 0, getScBvPlus);
  }

  void testGetScBvPlusSltFalse1()
  {
    runTest(false, BITVECTOR_SLT, BITVECTOR_PLUS, 1, getScBvPlus);
  }

  void testGetScBvPlusSgtTrue0()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_PLUS, 0, getScBvPlus);
  }

  void testGetScBvPlusSgtTrue1()
  {
    runTest(true, BITVECTOR_SGT, BITVECTOR_PLUS, 1, getScBvPlus);
  }

  void testGetScBvPlusSgtFalse0()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_PLUS, 0, getScBvPlus);
  }

  void testGetScBvPlusSgtFalse1()
  {
    runTest(false, BITVECTOR_SGT, BITVECTOR_PLUS, 1, getScBvPlus);
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
};
