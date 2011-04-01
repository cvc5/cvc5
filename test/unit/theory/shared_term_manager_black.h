/*********************                                                        */
/*! \file shared_term_manager_black.h
 ** \verbatim
 ** Original author: barrett
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Black box testing of CVC4::SharedTermManager.
 **
 ** Black box testing of CVC4::SharedTermManager.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <string>
#include <deque>

#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/kind.h"
#include "context/context.h"
#include "util/rational.h"
#include "util/integer.h"
#include "util/options.h"
#include "util/Assert.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::expr;
using namespace CVC4::context;
using namespace CVC4::kind;

using namespace std;

/**
 * Test the SharedTermManager.
 */
class SharedTermManagerBlack : public CxxTest::TestSuite {
  Context* d_ctxt;

  NodeManager* d_nm;
  NodeManagerScope* d_scope;
  TheoryEngine* d_theoryEngine;

public:

  void setUp() {
    d_ctxt = new Context;

    d_nm = new NodeManager(d_ctxt);
    d_scope = new NodeManagerScope(d_nm);

    d_theoryEngine = new TheoryEngine(d_ctxt);
  }

  void tearDown() {
    d_theoryEngine->shutdown();
    delete d_theoryEngine;

    delete d_scope;
    delete d_nm;

    delete d_ctxt;
  }

  void testExplanation() {
    // Example from Barcelogic paper
    SharedTermManager* stm = d_theoryEngine->getSharedTermManager();

    Node x1 = d_nm->mkVar("x1", d_nm->integerType());
    Node x2 = d_nm->mkVar("x2", d_nm->integerType());
    Node x3 = d_nm->mkVar("x3", d_nm->integerType());
    Node x4 = d_nm->mkVar("x4", d_nm->integerType());
    Node x5 = d_nm->mkVar("x5", d_nm->integerType());
    Node x6 = d_nm->mkVar("x6", d_nm->integerType());
    Node x7 = d_nm->mkVar("x7", d_nm->integerType());
    Node x8 = d_nm->mkVar("x8", d_nm->integerType());
    Node x9 = d_nm->mkVar("x9", d_nm->integerType());
    Node x10 = d_nm->mkVar("x10", d_nm->integerType());
    Node x11 = d_nm->mkVar("x11", d_nm->integerType());
    Node x12 = d_nm->mkVar("x12", d_nm->integerType());
    Node x13 = d_nm->mkVar("x13", d_nm->integerType());
    Node x14 = d_nm->mkVar("x14", d_nm->integerType());

    Node a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12;

    d_ctxt->push();

    stm->addEq(a1 = d_nm->mkNode(EQUAL, x1, x8));
    stm->addEq(a2 = d_nm->mkNode(EQUAL, x7, x2));
    stm->addEq(a3 = d_nm->mkNode(EQUAL, x3, x13));
    stm->addEq(a4 = d_nm->mkNode(EQUAL, x7, x1));
    stm->addEq(a5 = d_nm->mkNode(EQUAL, x6, x7));
    stm->addEq(a6 = d_nm->mkNode(EQUAL, x9, x5));
    stm->addEq(a7 = d_nm->mkNode(EQUAL, x9, x3));
    stm->addEq(a8 = d_nm->mkNode(EQUAL, x14, x11));
    stm->addEq(a9 = d_nm->mkNode(EQUAL, x10, x4));
    stm->addEq(a10 = d_nm->mkNode(EQUAL, x12, x9));
    stm->addEq(a11 = d_nm->mkNode(EQUAL, x4, x11));
    stm->addEq(a12 = d_nm->mkNode(EQUAL, x10, x7));

    Node explanation = stm->explain(d_nm->mkNode(EQUAL, x1, x4));

    TS_ASSERT(explanation.getNumChildren() == 3);

    Node e0 = explanation[0];
    Node e1 = explanation[1];
    Node e2 = explanation[2];

    TS_ASSERT(e0 == a4 && e1 == a9 && e2 == a12);

    TS_ASSERT(stm->getRep(x8) == stm->getRep(x14));
    TS_ASSERT(stm->getRep(x2) != stm->getRep(x12));

    d_ctxt->pop();

    TS_ASSERT(stm->getRep(x8) != stm->getRep(x14));

    d_ctxt->push();

    stm->addEq(a1 = d_nm->mkNode(EQUAL, x1, x8));
    stm->addEq(a2 = d_nm->mkNode(EQUAL, x8, x2));
    stm->addEq(a3 = d_nm->mkNode(EQUAL, x2, x3));

    explanation = stm->explain(d_nm->mkNode(EQUAL, x1, x3));
    TS_ASSERT(explanation.getNumChildren() == 3);

    e0 = explanation[0];
    e1 = explanation[1];
    e2 = explanation[2];

    TS_ASSERT(e0 == a1 && e1 == a2 && e2 == a3);

    TS_ASSERT(stm->getRep(x8) == stm->getRep(x2));

    d_ctxt->pop();
  }

};
