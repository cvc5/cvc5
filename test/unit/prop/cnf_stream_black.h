/*********************                                                        */
/*! \file cnf_stream_black.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): taking, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief White box testing of CVC4::prop::CnfStream.
 **
 ** White box testing of CVC4::prop::CnfStream.
 **/

#include <cxxtest/TestSuite.h>
/* #include <gmock/gmock.h> */
/* #include <gtest/gtest.h> */

#include "util/Assert.h"


#include "expr/expr_manager.h"
#include "expr/node_manager.h"
#include "context/context.h"
#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "prop/theory_proxy.h"
#include "smt/smt_engine.h"

#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "theory/theory_registrar.h"

#include "theory/builtin/theory_builtin.h"
#include "theory/booleans/theory_bool.h"
#include "theory/arith/theory_arith.h"

using namespace CVC4;
using namespace CVC4::context;
using namespace CVC4::prop;
using namespace std;

/* This fake class relies on the face that a MiniSat variable is just an int. */
class FakeSatSolver : public SatSolver {
  SatVariable d_nextVar;
  bool d_addClauseCalled;

public:
  FakeSatSolver() :
    d_nextVar(0),
    d_addClauseCalled(false) {
  }

  SatVariable newVar(bool theoryAtom) {
    return d_nextVar++;
  }

  SatVariable trueVar() {
    return d_nextVar++;
  }

  SatVariable falseVar() {
    return d_nextVar++;
  }

  void addClause(SatClause& c, bool lemma) {
    d_addClauseCalled = true;
  }

  void reset() {
    d_addClauseCalled = false;
  }

  unsigned int addClauseCalled() {
    return d_addClauseCalled;
  }

  unsigned getAssertionLevel() const {
    return 0;
  }

  void unregisterVar(SatLiteral lit) {
  }

  void renewVar(SatLiteral lit, int level = -1) {
  }

  void interrupt() {
  }
  
  SatValue solve() {
    return SAT_VALUE_UNKNOWN;
  }

  SatValue solve(long unsigned int& resource) {
    return SAT_VALUE_UNKNOWN;
  }

  SatValue value(SatLiteral l) {
    return SAT_VALUE_UNKNOWN;
  }

  SatValue modelValue(SatLiteral l) {
    return SAT_VALUE_UNKNOWN;
  }

  bool properExplanation(SatLiteral lit, SatLiteral expl) const {
    return true;
  }

};/* class FakeSatSolver */

class CnfStreamBlack : public CxxTest::TestSuite {
  /** The SAT solver proxy */
  FakeSatSolver* d_satSolver;

  /** The logic info */
  LogicInfo* d_logicInfo;

  /** The theory engine */
  TheoryEngine* d_theoryEngine;

  /** The output channel */
  theory::OutputChannel* d_outputChannel;

  /** The CNF converter in use */
  CnfStream* d_cnfStream;

  /** The context */
  Context* d_context;

  /** The user context */
  UserContext* d_userContext;

  /** The node manager */
  NodeManager* d_nodeManager;

  void setUp() {
    d_context = new Context();
    d_userContext = new UserContext();
    d_nodeManager = new NodeManager(d_context, NULL);
    NodeManagerScope nms(d_nodeManager);
    d_satSolver = new FakeSatSolver();
    d_logicInfo = new LogicInfo();
    d_logicInfo->lock();
    d_theoryEngine = new TheoryEngine(d_context, d_userContext, *d_logicInfo);
    d_theoryEngine->addTheory<theory::builtin::TheoryBuiltin>(theory::THEORY_BUILTIN);
    d_theoryEngine->addTheory<theory::booleans::TheoryBool>(theory::THEORY_BOOL);
    d_theoryEngine->addTheory<theory::arith::TheoryArith>(theory::THEORY_ARITH);
    d_cnfStream = new CVC4::prop::TseitinCnfStream(d_satSolver, new theory::TheoryRegistrar(d_theoryEngine));
  }

  void tearDown() {
    NodeManagerScope nms(d_nodeManager);
    delete d_cnfStream;
    d_theoryEngine->shutdown();
    delete d_theoryEngine;
    delete d_logicInfo;
    delete d_satSolver;
    delete d_nodeManager;
    delete d_userContext;
    delete d_context;
  }

public:

  /* [chris 5/26/2010] In the tests below, we don't attempt to delve into the
   * deep structure of the CNF conversion. Firstly, we just want to make sure
   * that the conversion doesn't choke on any boolean Exprs. We'll also check
   * that addClause got called. We won't check that it gets called a particular
   * number of times, or with what.
   */

  void testAnd() {
    NodeManagerScope nms(d_nodeManager);
    Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
    Node b = d_nodeManager->mkVar(d_nodeManager->booleanType());
    Node c = d_nodeManager->mkVar(d_nodeManager->booleanType());
    d_cnfStream->convertAndAssert(d_nodeManager->mkNode(kind::AND, a, b, c), false, false);
    TS_ASSERT( d_satSolver->addClauseCalled() );
  }

  void testComplexExpr() {
    NodeManagerScope nms(d_nodeManager);
    Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
    Node b = d_nodeManager->mkVar(d_nodeManager->booleanType());
    Node c = d_nodeManager->mkVar(d_nodeManager->booleanType());
    Node d = d_nodeManager->mkVar(d_nodeManager->booleanType());
    Node e = d_nodeManager->mkVar(d_nodeManager->booleanType());
    Node f = d_nodeManager->mkVar(d_nodeManager->booleanType());
    d_cnfStream->convertAndAssert(d_nodeManager->mkNode(kind::IMPLIES,
                                                        d_nodeManager->mkNode(kind::AND, a, b),
                                                        d_nodeManager->mkNode(kind::IFF,
                                                                              d_nodeManager->mkNode(kind::OR, c, d),
                                                                              d_nodeManager->mkNode(kind::NOT,
                                                                                                    d_nodeManager->mkNode(kind::XOR, e, f)))), false, false );
    TS_ASSERT( d_satSolver->addClauseCalled() );
  }

  void testTrue() {
    NodeManagerScope nms(d_nodeManager);
    d_cnfStream->convertAndAssert( d_nodeManager->mkConst(true), false, false );
    TS_ASSERT( d_satSolver->addClauseCalled() );
  }

  void testFalse() {
    NodeManagerScope nms(d_nodeManager);
    d_cnfStream->convertAndAssert( d_nodeManager->mkConst(false), false, false );
    TS_ASSERT( d_satSolver->addClauseCalled() );
  }

  void testIff() {
    NodeManagerScope nms(d_nodeManager);
    Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
    Node b = d_nodeManager->mkVar(d_nodeManager->booleanType());
    d_cnfStream->convertAndAssert( d_nodeManager->mkNode(kind::IFF, a, b), false, false );
    TS_ASSERT( d_satSolver->addClauseCalled() );
  }

  void testImplies() {
    NodeManagerScope nms(d_nodeManager);
    Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
    Node b = d_nodeManager->mkVar(d_nodeManager->booleanType());
    d_cnfStream->convertAndAssert( d_nodeManager->mkNode(kind::IMPLIES, a, b), false, false );
    TS_ASSERT( d_satSolver->addClauseCalled() );
  }

  // ITEs should be removed before going to CNF
  //void testIte() {
  //  NodeManagerScope nms(d_nodeManager);
  //  d_cnfStream->convertAndAssert(
  //      d_nodeManager->mkNode(
  //          kind::EQUAL,
  //          d_nodeManager->mkNode(
  //              kind::ITE,
  //              d_nodeManager->mkVar(d_nodeManager->booleanType()),
  //              d_nodeManager->mkVar(d_nodeManager->integerType()),
  //              d_nodeManager->mkVar(d_nodeManager->integerType())
  //          ),
  //          d_nodeManager->mkVar(d_nodeManager->integerType())
  //                            ), false, false);
  //
  //}

  void testNot() {
    NodeManagerScope nms(d_nodeManager);
    Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
    d_cnfStream->convertAndAssert( d_nodeManager->mkNode(kind::NOT, a), false, false );
    TS_ASSERT( d_satSolver->addClauseCalled() );
  }

  void testOr() {
    NodeManagerScope nms(d_nodeManager);
    Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
    Node b = d_nodeManager->mkVar(d_nodeManager->booleanType());
    Node c = d_nodeManager->mkVar(d_nodeManager->booleanType());
    d_cnfStream->convertAndAssert( d_nodeManager->mkNode(kind::OR, a, b, c), false, false );
    TS_ASSERT( d_satSolver->addClauseCalled() );
  }

  void testVar() {
    NodeManagerScope nms(d_nodeManager);
    Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
    Node b = d_nodeManager->mkVar(d_nodeManager->booleanType());
    d_cnfStream->convertAndAssert(a, false, false);
    TS_ASSERT( d_satSolver->addClauseCalled() );
    d_satSolver->reset();
    d_cnfStream->convertAndAssert(b, false, false);
    TS_ASSERT( d_satSolver->addClauseCalled() );
  }

  void testXor() {
    NodeManagerScope nms(d_nodeManager);
    Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
    Node b = d_nodeManager->mkVar(d_nodeManager->booleanType());
    d_cnfStream->convertAndAssert( d_nodeManager->mkNode(kind::XOR, a, b), false, false );
    TS_ASSERT( d_satSolver->addClauseCalled() );
  }

  void testEnsureLiteral() {
    NodeManagerScope nms(d_nodeManager);
    Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
    Node b = d_nodeManager->mkVar(d_nodeManager->booleanType());
    Node a_and_b = d_nodeManager->mkNode(kind::AND, a, b);
    d_cnfStream->ensureLiteral(a_and_b);
    // Clauses are necessary to "literal-ize" a_and_b; this perhaps
    // doesn't belong in a black-box test though...
    TS_ASSERT( d_satSolver->addClauseCalled() );
    TS_ASSERT( d_cnfStream->hasLiteral(a_and_b) );
  }
};
