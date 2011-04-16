/*********************                                                        */
/*! \file theory_uf_tim_white.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: barrett
 ** Minor contributors (to current version): cconway, dejan, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief White box testing of CVC4::theory::uf::tim::TheoryUFTim.
 **
 ** White box testing of CVC4::theory::uf::tim::TheoryUFTim.
 **/

#include <cxxtest/TestSuite.h>

#include "theory/theory.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/tim/theory_uf_tim.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "context/context.h"

#include "theory/theory_test_utils.h"

#include <vector>

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;
using namespace CVC4::theory::uf::tim;
using namespace CVC4::expr;
using namespace CVC4::context;

using namespace std;


class TheoryUFTimWhite : public CxxTest::TestSuite {

  Context* d_ctxt;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;

  TestOutputChannel d_outputChannel;
  Theory::Effort d_level;

  TheoryUFTim* d_euf;

  TypeNode* d_booleanType;

public:

  TheoryUFTimWhite() : d_level(Theory::FULL_EFFORT) {}

  void setUp() {
    d_ctxt = new Context;
    d_nm = new NodeManager(d_ctxt, NULL);
    d_scope = new NodeManagerScope(d_nm);
    d_outputChannel.clear();
    d_euf = new TheoryUFTim(d_ctxt, d_outputChannel, Valuation(NULL));

    d_booleanType = new TypeNode(d_nm->booleanType());
  }

  void tearDown() {
    delete d_booleanType;
    delete d_euf;
    d_outputChannel.clear();
    delete d_scope;
    delete d_nm;
    delete d_ctxt;
  }

  void testPushPopSimple() {
    TypeNode t = d_nm->mkSort();
    Node x = d_nm->mkVar(t);
    Node x_eq_x = x.eqNode(x);

    d_ctxt->push();
    d_ctxt->pop();
  }

// FIXME: This is broken because of moving registration into theory_engine @CB
// //   void testPushPopChain() {
// //     Node x = d_nm->mkVar(*d_booleanType);
// //     Node f = d_nm->mkVar(*d_booleanType);
// //     Node f_x = d_nm->mkNode(kind::APPLY_UF, f, x);
// //     Node f_f_x = d_nm->mkNode(kind::APPLY_UF, f, f_x);
// //     Node f_f_f_x = d_nm->mkNode(kind::APPLY_UF, f, f_f_x);
// //     Node f_f_f_f_x = d_nm->mkNode(kind::APPLY_UF, f, f_f_f_x);
// //     Node f_f_f_f_f_x = d_nm->mkNode(kind::APPLY_UF, f, f_f_f_f_x);

// //     Node f3_x_eq_x = f_f_f_x.eqNode(x);
// //     Node f5_x_eq_x = f_f_f_f_f_x.eqNode(x);
// //     Node f1_x_neq_x = f_x.eqNode(x).notNode();

// //     Node expectedConflict = d_nm->mkNode(kind::AND,
// //                                          f1_x_neq_x,
// //                                          f3_x_eq_x,
// //                                          f5_x_eq_x
// //                                          );

// //     d_euf->assertFact( f3_x_eq_x );
// //     d_euf->assertFact( f1_x_neq_x );
// //     d_euf->check(d_level);
// //     d_ctxt->push();

// //     d_euf->assertFact( f5_x_eq_x );
// //     d_euf->check(d_level);

// //     TS_ASSERT_EQUALS(1u, d_outputChannel.getNumCalls());
// //     TS_ASSERT_EQUALS(CONFLICT, d_outputChannel.getIthCallType(0));
// //     Node realConflict = d_outputChannel.getIthNode(0);
// //     TS_ASSERT_EQUALS(expectedConflict, realConflict);

// //     d_ctxt->pop();
// //     d_euf->check(d_level);

// //     //Test that no additional calls to the output channel occurred.
// //     TS_ASSERT_EQUALS(1u, d_outputChannel.getNumCalls());

// //     d_euf->assertFact( f5_x_eq_x );

// //     d_euf->check(d_level);

// //     TS_ASSERT_EQUALS(2u, d_outputChannel.getNumCalls());
// //     TS_ASSERT_EQUALS(CONFLICT, d_outputChannel.getIthCallType(0));
// //     TS_ASSERT_EQUALS(CONFLICT, d_outputChannel.getIthCallType(1));
// //     Node  firstConflict = d_outputChannel.getIthNode(0);
// //     Node secondConflict = d_outputChannel.getIthNode(1);
// //     TS_ASSERT_EQUALS(expectedConflict,  firstConflict);
// //     TS_ASSERT_EQUALS(expectedConflict, secondConflict);

// //   }



//   /* test that {f(f(x)) == x, f(f(f(x))) != f(x)} is inconsistent */
//   void testSimpleChain() {
//     Node x = d_nm->mkVar(*d_booleanType);
//     Node f = d_nm->mkVar(*d_booleanType);
//     Node f_x = d_nm->mkNode(kind::APPLY_UF, f, x);
//     Node f_f_x = d_nm->mkNode(kind::APPLY_UF, f, f_x);
//     Node f_f_f_x = d_nm->mkNode(kind::APPLY_UF, f, f_f_x);

//     Node f_f_x_eq_x = f_f_x.eqNode(x);
//     Node f_f_f_x_neq_f_x = (f_f_f_x.eqNode(f_x)).notNode();

//     Node expectedConflict = f_f_f_x_neq_f_x.andNode(f_f_x_eq_x);

//     d_euf->assertFact(f_f_x_eq_x);
//     d_euf->assertFact(f_f_f_x_neq_f_x);
//     d_euf->check(d_level);

//     TS_ASSERT_EQUALS(1u, d_outputChannel.getNumCalls());
//     TS_ASSERT_EQUALS(CONFLICT, d_outputChannel.getIthCallType(0));

//     Node realConflict = d_outputChannel.getIthNode(0);
//     TS_ASSERT_EQUALS(expectedConflict, realConflict);

//   }

  /* test that !(x == x) is inconsistent */
//   void testSelfInconsistent() {
//     Node x = d_nm->mkVar(*d_booleanType);
//     Node x_neq_x = (x.eqNode(x)).notNode();

//     d_euf->assertFact(x_neq_x);
//     d_euf->check(d_level);

//     TS_ASSERT_EQUALS(1u, d_outputChannel.getNumCalls());
//     TS_ASSERT_EQUALS(x_neq_x, d_outputChannel.getIthNode(0));
//     TS_ASSERT_EQUALS(CONFLICT, d_outputChannel.getIthCallType(0));
//   }

//   /* test that (x == x) is consistent */
//   void testSelfConsistent() {
//     Node x = d_nm->mkVar(*d_booleanType);
//     Node x_eq_x = x.eqNode(x);

//     d_euf->assertFact(x_eq_x);
//     d_euf->check(d_level);

//     TS_ASSERT_EQUALS(0u, d_outputChannel.getNumCalls());
//   }


//   /* test that
//      {f(f(f(x))) == x,
//       f(f(f(f(f(x))))) = x,
//       f(x) != x
//      } is inconsistent */
//   void testChain() {
//     Node x = d_nm->mkVar(*d_booleanType);
//     Node f = d_nm->mkVar(*d_booleanType);
//     Node f_x = d_nm->mkNode(kind::APPLY_UF, f, x);
//     Node f_f_x = d_nm->mkNode(kind::APPLY_UF, f, f_x);
//     Node f_f_f_x = d_nm->mkNode(kind::APPLY_UF, f, f_f_x);
//     Node f_f_f_f_x = d_nm->mkNode(kind::APPLY_UF, f, f_f_f_x);
//     Node f_f_f_f_f_x = d_nm->mkNode(kind::APPLY_UF, f, f_f_f_f_x);

//     Node f3_x_eq_x = f_f_f_x.eqNode(x);
//     Node f5_x_eq_x = f_f_f_f_f_x.eqNode(x);
//     Node f1_x_neq_x = f_x.eqNode(x).notNode();

//     Node expectedConflict = d_nm->mkNode(kind::AND,
//                                          f1_x_neq_x,
//                                          f3_x_eq_x,
//                                          f5_x_eq_x
//                                          );

//     d_euf->assertFact( f3_x_eq_x );
//     d_euf->assertFact( f5_x_eq_x );
//     d_euf->assertFact( f1_x_neq_x );
//     d_euf->check(d_level);

//     TS_ASSERT_EQUALS(1u, d_outputChannel.getNumCalls());
//     TS_ASSERT_EQUALS(CONFLICT, d_outputChannel.getIthCallType(0));
//     Node realConflict = d_outputChannel.getIthNode(0);
//     TS_ASSERT_EQUALS(expectedConflict, realConflict);
//   }


//   void testPushPopA() {
//     Node x = d_nm->mkVar(*d_booleanType);
//     Node x_eq_x = x.eqNode(x);

//     d_ctxt->push();
//     d_euf->assertFact( x_eq_x );
//     d_euf->check(d_level);
//     d_ctxt->pop();
//     d_euf->check(d_level);
//   }

//   void testPushPopB() {
//     Node x = d_nm->mkVar(*d_booleanType);
//     Node f = d_nm->mkVar(*d_booleanType);
//     Node f_x = d_nm->mkNode(kind::APPLY_UF, f, x);
//     Node f_x_eq_x = f_x.eqNode(x);

//     d_euf->assertFact( f_x_eq_x );
//     d_ctxt->push();
//     d_euf->check(d_level);
//     d_ctxt->pop();
//     d_euf->check(d_level);
//   }

};
