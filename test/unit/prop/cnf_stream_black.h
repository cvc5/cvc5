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

/** Mock objects and definitions from sat.h*/

/* Prevent sat.h from being included, so we can mock it. */
/* #define __CVC4__PROP__SAT_H */

/* namespace CVC4 { */
/* namespace prop { */

/* typedef unsigned int SatVariable; */
/* typedef int SatLiteralValue; */

/* class SatLiteral { */
/*   friend class SatSolver; */

/*   SatLiteralValue d_value; */

/* public: */
/*   SatLiteral(SatVariable x) { */
/*     AlwaysAssert( x > 0 ); */
/*     d_value = (SatLiteralValue)x; */
/*   } */

/* friend SatLiteral operator~(SatLiteral lit); */
/* }; */

/* SatLiteral operator~(SatLiteral lit) { */
/*   return SatLiteral(-lit.d_value); */
/* } */

/* typedef std::vector<SatLiteral> SatClause; */


/* class SatSolver { */
/*   SatVariable d_nextVar; */

/* public: */
/*   /\** Hash function for literals *\/ */
/*   struct SatLiteralHashFunction { */
/*     size_t operator()(const SatLiteral& literal) const { */
/*       return literal.d_value; */
/*     } */
/*   }; */

/*   SatSolver() : */
/*     d_nextVar(1) { */
/*   } */

/*   SatVariable newVar(bool theoryAtom) { */
/*     return d_nextVar++; */
/*   } */

/*   void addClause(SatClause& clause) { */
/*     // do nothing */
/*   } */
/* }; */
/* } */
/* } */

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
public:
  FakeSatSolver() :
    d_nextVar(0) {
  }

  void addClause(SatClause& clause) { }

  SatVariable newVar(bool theoryAtom) {
    return d_nextVar++;
  }

//   MOCK_METHOD1(addClause, void (SatClause&));
//   MOCK_METHOD1(newVar, SatVariable (bool));
};

class CnfStreamBlack : public CxxTest::TestSuite {
  /** The SAT solver proxy */
  SatInputInterface *d_satSolver;

  /** The CNF converter in use */
  CnfStream* d_cnfStream;

  Context* d_context;

  /* SmtEngine* d_smtEngine; */

//  * The decision engine
  /* DecisionEngine* d_decisionEngine; */

//  * The decision engine
  /* TheoryEngine* d_theoryEngine; */

  /* ExprManager *d_exprManager; */
  NodeManager *d_nodeManager;

void setUp() {
  /* int argc = 1; */
  /* char *argv[] = { static_cast<char *>("cnf_stream_black") }; */
  /* ::testing::GTEST_FLAG(throw_on_failure) = true; */
  /* ::testing::InitGoogleMock(&argc, argv); */

  d_context = new Context;
  d_nodeManager = new NodeManager(d_context);
  d_satSolver = new FakeSatSolver;
  /* d_exprManager = new ExprManager(); */

  /* opts = new Options;  */
  /* d_smtEngine = new SmtEngine(d_exprManager, opts); */
  /* d_cnfStream = d_smtEngine->getPropEngine()->getCnfStream(); */
  /* d_decisionEngine = new DecisionEngine; */
  /* d_theoryEngine = new TheoryEngine(d_smtEngine, d_ctxt); */
  /* d_propEngine = new PropEngine(opts, d_decisionEngine, d_theoryEngine, d_ctxt); */
  /* d_satSolver = new SatSolver(d_propEngine, d_theoryEngine, d_context, opts); */
  d_cnfStream = new CVC4::prop::TseitinCnfStream(d_satSolver);
  /* d_satSolver->setCnfStream(d_cnfStream); */
}

void tearDown() {
  NodeManagerScope nms(d_nodeManager);
  delete d_cnfStream;
  delete d_satSolver;
  delete d_nodeManager;
}

public:
void testTrue() {
  NodeManagerScope nms(d_nodeManager);
  d_cnfStream->convertAndAssert( d_nodeManager->mkConst(true) );
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
