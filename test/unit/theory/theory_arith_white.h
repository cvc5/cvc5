/*********************                                                        */
/*! \file theory_arith_white.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include <cxxtest/TestSuite.h>

#include "theory/theory.h"
#include "theory/arith/theory_arith.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "context/context.h"
#include "util/rational.h"

#include "theory/theory_test_utils.h"

#include <vector>

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;
using namespace CVC4::expr;
using namespace CVC4::context;
using namespace CVC4::kind;

using namespace std;

class TheoryArithWhite : public CxxTest::TestSuite {

  Context* d_ctxt;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;

  TestOutputChannel d_outputChannel;
  Theory::Effort d_level;

  TheoryArith* d_arith;

  TypeNode* d_booleanType;
  TypeNode* d_realType;

  const Rational d_zero;
  const Rational d_one;

  std::set<Node>* preregistered;

  bool debug;

public:

  TheoryArithWhite() : d_level(Theory::FULL_EFFORT), d_zero(0), d_one(1), debug(false) {}

  void setUp() {
    d_ctxt = new Context;
    d_nm = new NodeManager(d_ctxt);
    d_scope = new NodeManagerScope(d_nm);
    d_outputChannel.clear();
    d_arith = new TheoryArith(0, d_ctxt, d_outputChannel);

    preregistered = new std::set<Node>();

    d_booleanType = new TypeNode(d_nm->booleanType());
    d_realType = new TypeNode(d_nm->realType());

  }

  void tearDown() {
    delete d_realType;
    delete d_booleanType;

    delete preregistered;

    delete d_arith;
    d_outputChannel.clear();
    delete d_scope;
    delete d_nm;
    delete d_ctxt;
  }

  Node fakeTheoryEnginePreprocess(TNode inp){
    Node rewrite = d_arith->rewrite(inp);

    if(debug) cout << rewrite << inp << endl;

    std::list<Node> toPreregister;

    toPreregister.push_back(rewrite);
    for(std::list<Node>::iterator i = toPreregister.begin(); i != toPreregister.end(); ++i){
      Node n = *i;
      preregistered->insert(n);

      for(Node::iterator citer = n.begin(); citer != n.end(); ++citer){
        Node c = *citer;
        if(preregistered->find(c) == preregistered->end()){
          toPreregister.push_back(c);
        }
      }
    }
    for(std::list<Node>::reverse_iterator i = toPreregister.rbegin(); i != toPreregister.rend(); ++i){
      Node n = *i;
      if(debug) cout << n.getId() << " "<< n << endl;
      d_arith->preRegisterTerm(n);
    }

    return rewrite;
  }

  void testAssert() {
    Node x = d_nm->mkVar(*d_realType);
    Node c = d_nm->mkConst<Rational>(d_zero);

    Node leq = d_nm->mkNode(LEQ, x, c);
    Node rLeq = fakeTheoryEnginePreprocess(leq);

    d_arith->assertFact(rLeq);

    d_arith->check(d_level);

    TS_ASSERT_EQUALS(d_outputChannel.getNumCalls(), 0u);
  }

  Node simulateSplit(TNode l, TNode r){
    Node eq = d_nm->mkNode(EQUAL, l, r);
    Node lt = d_nm->mkNode(LT, l, r);
    Node gt = d_nm->mkNode(GT, l, r);

    Node dis = d_nm->mkNode(OR, eq, lt, gt);
    return dis;
  }

  void testAssertEqualityEagerSplit() {
    Node x = d_nm->mkVar(*d_realType);
    Node c = d_nm->mkConst<Rational>(d_zero);

    Node eq = d_nm->mkNode(EQUAL, x, c);
    Node expectedDisjunct = simulateSplit(x,c);

    Node rEq = fakeTheoryEnginePreprocess(eq);

    d_arith->assertFact(rEq);

    d_arith->check(d_level);

    TS_ASSERT_EQUALS(d_outputChannel.getNumCalls(), 1u);

    TS_ASSERT_EQUALS(d_outputChannel.getIthNode(0), expectedDisjunct);
    TS_ASSERT_EQUALS(d_outputChannel.getIthCallType(0), AUG_LEMMA);

  }
  void testLtRewrite() {
    Node x = d_nm->mkVar(*d_realType);
    Node c = d_nm->mkConst<Rational>(d_zero);

    Node lt = d_nm->mkNode(LT, x, c);
    Node geq = d_nm->mkNode(GEQ, x, c);
    Node expectedRewrite = d_nm->mkNode(NOT, geq);

    Node rewrite = d_arith->rewrite(lt);

    TS_ASSERT_EQUALS(expectedRewrite, rewrite);
  }

  void testBasicConflict() {
    Node x = d_nm->mkVar(*d_realType);
    Node c = d_nm->mkConst<Rational>(d_zero);

    Node eq = d_nm->mkNode(EQUAL, x, c);
    Node lt = d_nm->mkNode(LT, x, c);
    Node expectedDisjunct = simulateSplit(x,c);

    Node rEq = fakeTheoryEnginePreprocess(eq);
    Node rLt = fakeTheoryEnginePreprocess(lt);

    d_arith->assertFact(rEq);
    d_arith->assertFact(rLt);


    d_arith->check(d_level);

    TS_ASSERT_EQUALS(d_outputChannel.getNumCalls(), 2u);
    TS_ASSERT_EQUALS(d_outputChannel.getIthNode(0), expectedDisjunct);
    TS_ASSERT_EQUALS(d_outputChannel.getIthCallType(0), AUG_LEMMA);

    TS_ASSERT_EQUALS(d_outputChannel.getIthCallType(1), CONFLICT);

    Node expectedClonflict = d_nm->mkNode(AND, rEq, rLt);

    TS_ASSERT_EQUALS(d_outputChannel.getIthNode(1), expectedClonflict);
  }

  void testBasicPropagate() {
    Node x = d_nm->mkVar(*d_realType);
    Node c = d_nm->mkConst<Rational>(d_zero);

    Node eq = d_nm->mkNode(EQUAL, x, c);
    Node lt = d_nm->mkNode(LT, x, c);
    Node expectedDisjunct = simulateSplit(x,c);

    Node rEq = fakeTheoryEnginePreprocess(eq);
    Node rLt = fakeTheoryEnginePreprocess(lt);

    d_arith->assertFact(rEq);


    d_arith->check(d_level);
    d_arith->propagate(d_level);

    TS_ASSERT_EQUALS(d_outputChannel.getNumCalls(), 2u);
    TS_ASSERT_EQUALS(d_outputChannel.getIthCallType(0), AUG_LEMMA);


    Node expectedProp = d_nm->mkNode(GEQ, x, c);
    TS_ASSERT_EQUALS(d_outputChannel.getIthCallType(1), PROPAGATE);
    TS_ASSERT_EQUALS(d_outputChannel.getIthNode(1), expectedProp);

  }
  void testTPLt1() {
    Node x = d_nm->mkVar(*d_realType);
    Node c0 = d_nm->mkConst<Rational>(d_zero);
    Node c1 = d_nm->mkConst<Rational>(d_one);

    Node leq0 = d_nm->mkNode(LEQ, x, c0);
    Node leq1 = d_nm->mkNode(LEQ, x, c1);
    Node lt1 = d_nm->mkNode(LT, x, c1);

    Node rLeq0 = fakeTheoryEnginePreprocess(leq0);
    Node rLt1 = fakeTheoryEnginePreprocess(lt1);
    Node rLeq1 = fakeTheoryEnginePreprocess(leq1);

    d_arith->assertFact(rLt1);


    d_arith->check(d_level);
    d_arith->propagate(d_level);

#ifdef CVC4_ASSERTIONS
    TS_ASSERT_THROWS(  d_arith->explain(rLeq0, d_level), AssertionException );
    TS_ASSERT_THROWS(  d_arith->explain(rLt1, d_level), AssertionException );
#endif
    d_arith->explain(rLeq1, d_level);

    TS_ASSERT_EQUALS(d_outputChannel.getNumCalls(), 2u);
    TS_ASSERT_EQUALS(d_outputChannel.getIthCallType(0), PROPAGATE);
    TS_ASSERT_EQUALS(d_outputChannel.getIthCallType(1), EXPLANATION);
    TS_ASSERT_EQUALS(d_outputChannel.getIthNode(0), leq1);
    TS_ASSERT_EQUALS(d_outputChannel.getIthNode(1), rLt1);
  }


  void testTPLeq0() {
    Node x = d_nm->mkVar(*d_realType);
    Node c0 = d_nm->mkConst<Rational>(d_zero);
    Node c1 = d_nm->mkConst<Rational>(d_one);

    Node leq0 = d_nm->mkNode(LEQ, x, c0);
    Node leq1 = d_nm->mkNode(LEQ, x, c1);
    Node lt1 = d_nm->mkNode(LT, x, c1);

    Node rLeq0 = fakeTheoryEnginePreprocess(leq0);
    Node rLt1 = fakeTheoryEnginePreprocess(lt1);
    Node rLeq1 = fakeTheoryEnginePreprocess(leq1);

    d_arith->assertFact(rLeq0);


    d_arith->check(d_level);
    d_arith->propagate(d_level);


    d_arith->explain(rLt1, d_level);
#ifdef CVC4_ASSERTIONS
    TS_ASSERT_THROWS(  d_arith->explain(rLeq0, d_level), AssertionException );
#endif
    d_arith->explain(rLeq1, d_level);

    TS_ASSERT_EQUALS(d_outputChannel.getNumCalls(), 4u);
    TS_ASSERT_EQUALS(d_outputChannel.getIthCallType(0), PROPAGATE);
    TS_ASSERT_EQUALS(d_outputChannel.getIthCallType(1), PROPAGATE);
    TS_ASSERT_EQUALS(d_outputChannel.getIthCallType(2), EXPLANATION);
    TS_ASSERT_EQUALS(d_outputChannel.getIthCallType(3), EXPLANATION);

    TS_ASSERT_EQUALS(d_outputChannel.getIthNode(0), rLt1);
    TS_ASSERT_EQUALS(d_outputChannel.getIthNode(1), rLeq1);


    TS_ASSERT_EQUALS(d_outputChannel.getIthNode(2), rLeq0);
    TS_ASSERT_EQUALS(d_outputChannel.getIthNode(3), rLeq0);
  }
  void testTPLeq1() {
    Node x = d_nm->mkVar(*d_realType);
    Node c0 = d_nm->mkConst<Rational>(d_zero);
    Node c1 = d_nm->mkConst<Rational>(d_one);

    Node leq0 = d_nm->mkNode(LEQ, x, c0);
    Node leq1 = d_nm->mkNode(LEQ, x, c1);
    Node lt1 = d_nm->mkNode(LT, x, c1);

    Node rLeq0 = fakeTheoryEnginePreprocess(leq0);
    Node rLt1 = fakeTheoryEnginePreprocess(lt1);
    Node rLeq1 = fakeTheoryEnginePreprocess(leq1);

    d_arith->assertFact(rLeq1);


    d_arith->check(d_level);
    d_arith->propagate(d_level);

#ifdef CVC4_ASSERTIONS
    TS_ASSERT_THROWS(  d_arith->explain(rLeq0, d_level), AssertionException );
    TS_ASSERT_THROWS(  d_arith->explain(rLeq1, d_level), AssertionException );
    TS_ASSERT_THROWS(  d_arith->explain(rLt1, d_level), AssertionException );
#endif

    TS_ASSERT_EQUALS(d_outputChannel.getNumCalls(), 0u);
  }
};
