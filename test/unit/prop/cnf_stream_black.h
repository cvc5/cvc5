/*********************                                                        */
/** cnf_stream_black.h
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): dejan, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
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
#include "prop/sat.h"
#include "smt/smt_engine.h"
#include "util/options.h"
#include "util/decision_engine.h"

using namespace CVC4;
using namespace CVC4::context;
using namespace CVC4::prop;
using namespace std;

/* This fake class relies on the face that a MiniSat variable is just an int. */
class FakeSatSolver : public SatInputInterface {
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

  void addClause(SatClause& c, bool lemma) {
    d_addClauseCalled = true;
  }

  void reset() {
    d_addClauseCalled = false;
  }

  unsigned int addClauseCalled() {
    return d_addClauseCalled;
  }
};

class CnfStreamBlack : public CxxTest::TestSuite {
  /** The SAT solver proxy */
  FakeSatSolver *d_satSolver;

  /** The CNF converter in use */
  CnfStream* d_cnfStream;

  Context* d_context;

  /* ExprManager *d_exprManager; */
  NodeManager *d_nodeManager;

void setUp() {
  d_context = new Context;
  d_nodeManager = new NodeManager(d_context);
  d_satSolver = new FakeSatSolver;
  d_cnfStream = new CVC4::prop::TseitinCnfStream(d_satSolver);
}

void tearDown() {
  NodeManagerScope nms(d_nodeManager);
  delete d_cnfStream;
  delete d_satSolver;
  delete d_nodeManager;
}

public:

/* [chris 5/26/2010] In the tests below, we don't attempt to delve into the
 * deep structure of the CNF conversion. Firstly, we just want to make sure
 * that the conversion doesn't choke on any boolean Exprs. In some cases,
 * we'll check to make sure a certain number of assertions are generated.
 */

void testTrue() {
  NodeManagerScope nms(d_nodeManager);
  d_satSolver->reset();
  d_cnfStream->convertAndAssert( d_nodeManager->mkConst(true) );
  TS_ASSERT( d_satSolver->addClauseCalled() );
}

void testIte() {
  NodeManagerScope nms(d_nodeManager);
  d_cnfStream->convertAndAssert(
      d_nodeManager->mkNode(
          kind::EQUAL,
          d_nodeManager->mkNode(
              kind::ITE,
              d_nodeManager->mkVar(d_nodeManager->booleanType()),
              d_nodeManager->mkVar(d_nodeManager->integerType()),
              d_nodeManager->mkVar(d_nodeManager->integerType())
          ),
          d_nodeManager->mkVar(d_nodeManager->integerType())
                            ));

}
};
