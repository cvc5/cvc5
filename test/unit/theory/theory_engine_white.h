/*********************                                                        */
/*! \file theory_engine_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of CVC4::theory::Theory.
 **
 ** White box testing of CVC4::theory::Theory.  This test creates
 ** "fake" theory interfaces and injects them into TheoryEngine, so we
 ** can test TheoryEngine's behavior without relying on independent
 ** theory behavior.  This is done in TheoryEngineWhite::setUp() by
 ** means of the TheoryEngineWhite::registerTheory() interface.
 **/

#include <cxxtest/TestSuite.h>

#include <deque>
#include <iostream>
#include <string>

#include "base/cvc4_assert.h"
#include "context/context.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "options/options.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/bv/theory_bv_rewrite_rules_normalization.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "theory/valuation.h"
#include "util/integer.h"
#include "util/rational.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::expr;
using namespace CVC4::context;
using namespace CVC4::kind;
using namespace CVC4::smt;
using namespace CVC4::theory::bv;

using namespace std;

class FakeOutputChannel : public OutputChannel {
  void conflict(TNode n, Proof* pf = NULL) throw(AssertionException) {
    Unimplemented();
  }
  bool propagate(TNode n) throw(AssertionException) {
    Unimplemented();
  }
  void propagateAsDecision(TNode n) throw(AssertionException) {
    Unimplemented();
  }
  LemmaStatus lemma(TNode n, ProofRule rule,
                    bool removable,
                    bool preprocess,
                    bool sendAtoms) throw(AssertionException) {
    Unimplemented();
  }
  void requirePhase(TNode, bool) throw(AssertionException) {
    Unimplemented();
  }
  bool flipDecision() throw(AssertionException) {
    Unimplemented();
  }
  void explanation(TNode n) throw(AssertionException) {
    Unimplemented();
  }
  void setIncomplete() throw(AssertionException) {
    Unimplemented();
  }
  void handleUserAttribute( const char* attr, Theory* t ){
    Unimplemented();
  }
  LemmaStatus splitLemma(TNode n, bool removable) throw(TypeCheckingExceptionPrivate, AssertionException){
    Unimplemented();
  }
};/* class FakeOutputChannel */

template<TheoryId theory>
class FakeTheory;

/** Expected rewrite calls can be PRE- or POST-rewrites */
enum RewriteType {
  PRE,
  POST
};/* enum RewriteType */

/**
 * Stores an "expected" rewrite call.  The main test class will set up a sequence
 * of these RewriteItems, then do a rewrite, ensuring that the actual call sequence
 * matches the sequence of expected RewriteItems. */
struct RewriteItem {
  RewriteType d_type;
//  FakeTheory* d_theory;
  Node d_node;
  bool d_topLevel;
};/* struct RewriteItem */

/**
 * Fake Theory interface.  Looks like a Theory, but really all it does is note when and
 * how rewriting behavior is requested.
 */
template<TheoryId theoryId>
class FakeTheory : public Theory {
  /**
   * This fake theory class is equally useful for bool, uf, arith, etc.  It keeps an
   * identifier to identify itself.
   */
  std::string d_id;

  /**
   * The expected sequence of rewrite calls.  Filled by FakeTheory::expect() and consumed
   * by FakeTheory::preRewrite() and FakeTheory::postRewrite().
   */
  // static std::deque<RewriteItem> s_expected;

public:
  FakeTheory(context::Context* ctxt, context::UserContext* uctxt, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo) :
      Theory(theoryId, ctxt, uctxt, out, valuation, logicInfo)
  { }

  /** Register an expected rewrite call */
  static void expect(RewriteType type, FakeTheory* thy, TNode n, bool topLevel)
      throw()
  {
    RewriteItem item = { type, thy, n, topLevel };
    //s_expected.push_back(item);
  }

  /**
   * Returns whether the expected queue is empty.  This is done after a call into
   * the rewriter to ensure that the actual set of observed rewrite calls completed
   * the sequence of expected rewrite calls.
   */
  static bool nothingMoreExpected() throw() {
    return true; // s_expected.empty();
  }

  /**
   * Overrides Theory::preRewrite().  This "fake theory" version ensures that
   * this actual, observed pre-rewrite call matches the next "expected" call set up
   * by the test.
   */
  RewriteResponse preRewrite(TNode n, bool topLevel) {
//    if(false) { //s_expected.empty()) {
//      cout << std::endl
//           << "didn't expect anything more, but got" << std::endl
//           << "     PRE  " << topLevel << " " << identify() << " " << n
//           << std::endl;
//    }
//    TS_ASSERT(!s_expected.empty());
//
//    RewriteItem expected = s_expected.front();
//    s_expected.pop_front();
//
//    if(expected.d_type != PRE ||
////       expected.d_theory != this ||
//       expected.d_node != n ||
//       expected.d_topLevel != topLevel) {
//      cout << std::endl
//           << "HAVE PRE  " << topLevel << " " << identify() << " " << n
//           << std::endl
//           << "WANT " << (expected.d_type == PRE ? "PRE  " : "POST ")
//  //         << expected.d_topLevel << " " << expected.d_theory->identify()
//           << " " << expected.d_node << std::endl << std::endl;
//    }
//
//    TS_ASSERT_EQUALS(expected.d_type, PRE);
////    TS_ASSERT_EQUALS(expected.d_theory, this);
//    TS_ASSERT_EQUALS(expected.d_node, n);
//    TS_ASSERT_EQUALS(expected.d_topLevel, topLevel);

    return RewriteResponse(REWRITE_DONE, n);
  }

  /**
   * Overrides Theory::postRewrite().  This "fake theory" version ensures that
   * this actual, observed post-rewrite call matches the next "expected" call set up
   * by the test.
   */
  RewriteResponse postRewrite(TNode n, bool topLevel) {
//    if(s_expected.empty()) {
//      cout << std::endl
//           << "didn't expect anything more, but got" << std::endl
//           << "     POST " << topLevel << " " << identify() << " " << n
//           << std::endl;
//    }
//    TS_ASSERT(!s_expected.empty());
//
//    RewriteItem expected = s_expected.front();
//    s_expected.pop_front();
//
//    if(expected.d_type != POST ||
////       expected.d_theory != this ||
//       expected.d_node != n ||
//       expected.d_topLevel != topLevel) {
//      cout << std::endl
//           << "HAVE POST " << topLevel << " " << identify() << " " << n
//           << std::endl
//           << "WANT " << (expected.d_type == PRE ? "PRE  " : "POST ")
////           << expected.d_topLevel << " " << expected.d_theory->identify()
//           << " " << expected.d_node << std::endl << std::endl;
//    }
//
//    TS_ASSERT_EQUALS(expected.d_type, POST);
//    TS_ASSERT_EQUALS(expected.d_theory, this);
//    TS_ASSERT_EQUALS(expected.d_node, n);
//    TS_ASSERT_EQUALS(expected.d_topLevel, topLevel);

    return RewriteResponse(REWRITE_DONE, n);
  }

  std::string identify() const throw() {
    return "Fake" + d_id;
  }

  void presolve() { Unimplemented(); }

  void preRegisterTerm(TNode) { Unimplemented(); }
  void registerTerm(TNode) { Unimplemented(); }
  void check(Theory::Effort) { Unimplemented(); }
  void propagate(Theory::Effort) { Unimplemented(); }
  Node explain(TNode) { Unimplemented(); }
  Node getValue(TNode n) { return Node::null(); }
};/* class FakeTheory */


/* definition of the s_expected static field in FakeTheory; see above */
// std::deque<RewriteItem> FakeTheory::s_expected;


/**
 * Test the TheoryEngine.
 */
class TheoryEngineWhite : public CxxTest::TestSuite {
  Context* d_ctxt;
  UserContext* d_uctxt;

  ExprManager* d_em;
  NodeManager* d_nm;
  SmtEngine* d_smt;
  SmtScope* d_scope;
  FakeOutputChannel *d_nullChannel;
  TheoryEngine* d_theoryEngine;

public:

  void setUp() {
    d_em = new ExprManager();
    d_smt = new SmtEngine(d_em);
    d_nm = NodeManager::fromExprManager(d_em);
    d_scope = new SmtScope(d_smt);

    d_ctxt = d_smt->d_context;
    d_uctxt = d_smt->d_userContext;

    d_nullChannel = new FakeOutputChannel();

    d_theoryEngine = d_smt->d_theoryEngine;
    for(TheoryId id = THEORY_FIRST; id != THEORY_LAST; ++id) {
      delete d_theoryEngine->d_theoryOut[id];
      delete d_theoryEngine->d_theoryTable[id];
      d_theoryEngine->d_theoryOut[id] = NULL;
      d_theoryEngine->d_theoryTable[id] = NULL;
    }
    d_theoryEngine->addTheory< FakeTheory<THEORY_BUILTIN> >(THEORY_BUILTIN);
    d_theoryEngine->addTheory< FakeTheory<THEORY_BOOL> >(THEORY_BOOL);
    d_theoryEngine->addTheory< FakeTheory<THEORY_UF> >(THEORY_UF);
    d_theoryEngine->addTheory< FakeTheory<THEORY_ARITH> >(THEORY_ARITH);
    d_theoryEngine->addTheory< FakeTheory<THEORY_ARRAY> >(THEORY_ARRAY);
    d_theoryEngine->addTheory< FakeTheory<THEORY_BV> >(THEORY_BV);
  }

  void tearDown() {
    delete d_nullChannel;

    delete d_scope;
    delete d_smt;
    delete d_em;
  }

  void testRewriterSimple() {
    Node x = d_nm->mkVar("x", d_nm->integerType());
    Node y = d_nm->mkVar("y", d_nm->integerType());
    Node z = d_nm->mkVar("z", d_nm->integerType());

    // make the expression (PLUS x y (MULT z 0))
    Node zero = d_nm->mkConst(Rational("0"));
    Node zTimesZero = d_nm->mkNode(MULT, z, zero);
    Node n = d_nm->mkNode(PLUS, x, y, zTimesZero);

    Node nExpected = n;
    Node nOut;

//    // set up the expected sequence of calls
//    FakeTheory::expect(PRE, d_arith, n, true);
//    FakeTheory::expect(PRE, d_arith, x, false);
//    FakeTheory::expect(POST, d_arith, x, false);
//    FakeTheory::expect(PRE, d_arith, y, false);
//    FakeTheory::expect(POST, d_arith, y, false);
//    FakeTheory::expect(PRE, d_arith, zTimesZero, false);
//    FakeTheory::expect(PRE, d_arith, z, false);
//    FakeTheory::expect(POST, d_arith, z, false);
//    FakeTheory::expect(PRE, d_arith, zero, false);
//    FakeTheory::expect(POST, d_arith, zero, false);
//    FakeTheory::expect(POST, d_arith, zTimesZero, false);
//    FakeTheory::expect(POST, d_arith, n, true);

    // do a full rewrite; FakeTheory::preRewrite() and FakeTheory::postRewrite()
    // assert that the rewrite calls that are made match the expected sequence
    // set up above
    nOut = Rewriter::rewrite(n);

    // assert that we consumed the sequence of expected calls completely
//    TS_ASSERT(FakeTheory::nothingMoreExpected());

    // assert that the rewritten node is what we expect
//    TS_ASSERT_EQUALS(nOut, nExpected);
  }

  void testRewriterComplicated() {
    Node x = d_nm->mkVar("x", d_nm->integerType());
    Node y = d_nm->mkVar("y", d_nm->realType());
    TypeNode u = d_nm->mkSort("U");
    Node z1 = d_nm->mkVar("z1", u);
    Node z2 = d_nm->mkVar("z2", u);
    Node f = d_nm->mkVar("f", d_nm->mkFunctionType(d_nm->integerType(),
                                                   d_nm->integerType()));
    Node g = d_nm->mkVar("g", d_nm->mkFunctionType(d_nm->realType(),
                                                   d_nm->integerType()));
    Node one = d_nm->mkConst(Rational("1"));
    Node two = d_nm->mkConst(Rational("2"));

    Node f1 = d_nm->mkNode(APPLY_UF, f, one);
    Node f2 = d_nm->mkNode(APPLY_UF, f, two);
    Node fx = d_nm->mkNode(APPLY_UF, f, x);
    Node ffx = d_nm->mkNode(APPLY_UF, f, fx);
    Node gy = d_nm->mkNode(APPLY_UF, g, y);
    Node z1eqz2 = d_nm->mkNode(EQUAL, z1, z2);
    Node f1eqf2 = d_nm->mkNode(EQUAL, f1, f2);
    Node ffxeqgy = d_nm->mkNode(EQUAL, ffx, gy);
    Node and1 = d_nm->mkNode(AND, ffxeqgy, z1eqz2);
    Node ffxeqf1 = d_nm->mkNode(EQUAL, ffx, f1);
    Node or1 = d_nm->mkNode(OR, and1, ffxeqf1);
    // make the expression:
    // (IMPLIES (EQUAL (f 1) (f 2))
    //   (OR (AND (EQUAL (f (f x)) (g y))
    //            (EQUAL z1 z2))
    //       (EQUAL (f (f x)) (f 1))))
    Node n = d_nm->mkNode(IMPLIES, f1eqf2, or1);
    Node nExpected = n;
    Node nOut;

    // set up the expected sequence of calls
//    FakeTheory::expect(PRE, d_bool, n, true);
//    FakeTheory::expect(PRE, d_uf, f1eqf2, true);
//    FakeTheory::expect(PRE, d_uf, f1, false);
    //FakeTheory::expect(PRE, d_builtin, f, true);
    //FakeTheory::expect(POST, d_builtin, f, true);
//    FakeTheory::expect(PRE, d_arith, one, true);
//    FakeTheory::expect(POST, d_arith, one, true);
//    FakeTheory::expect(POST, d_uf, f1, false);
//    FakeTheory::expect(PRE, d_uf, f2, false);
    // these aren't called because they're in the rewrite cache
    //FakeTheory::expect(PRE, d_builtin, f, true);
    //FakeTheory::expect(POST, d_builtin, f, true);
//    FakeTheory::expect(PRE, d_arith, two, true);
//    FakeTheory::expect(POST, d_arith, two, true);
//    FakeTheory::expect(POST, d_uf, f2, false);
//    FakeTheory::expect(POST, d_uf, f1eqf2, true);
//    FakeTheory::expect(PRE, d_bool, or1, false);
//    FakeTheory::expect(PRE, d_bool, and1, false);
//    FakeTheory::expect(PRE, d_uf, ffxeqgy, true);
//    FakeTheory::expect(PRE, d_uf, ffx, false);
//    FakeTheory::expect(PRE, d_uf, fx, false);
    // these aren't called because they're in the rewrite cache
    //FakeTheory::expect(PRE, d_builtin, f, true);
    //FakeTheory::expect(POST, d_builtin, f, true);
//    FakeTheory::expect(PRE, d_arith, x, true);
//    FakeTheory::expect(POST, d_arith, x, true);
//    FakeTheory::expect(POST, d_uf, fx, false);
//    FakeTheory::expect(POST, d_uf, ffx, false);
//    FakeTheory::expect(PRE, d_uf, gy, false);
    //FakeTheory::expect(PRE, d_builtin, g, true);
    //FakeTheory::expect(POST, d_builtin, g, true);
//    FakeTheory::expect(PRE, d_arith, y, true);
//    FakeTheory::expect(POST, d_arith, y, true);
//    FakeTheory::expect(POST, d_uf, gy, false);
//    FakeTheory::expect(POST, d_uf, ffxeqgy, true);
//    FakeTheory::expect(PRE, d_uf, z1eqz2, true);
//    FakeTheory::expect(PRE, d_uf, z1, false);
//    FakeTheory::expect(POST, d_uf, z1, false);
//    FakeTheory::expect(PRE, d_uf, z2, false);
//    FakeTheory::expect(POST, d_uf, z2, false);
//    FakeTheory::expect(POST, d_uf, z1eqz2, true);
//    FakeTheory::expect(POST, d_bool, and1, false);
//    FakeTheory::expect(PRE, d_uf, ffxeqf1, true);
    // these aren't called because they're in the rewrite cache
    //FakeTheory::expect(PRE, d_uf, ffx, false);
    //FakeTheory::expect(POST, d_uf, ffx, false);
    //FakeTheory::expect(PRE, d_uf, f1, false);
    //FakeTheory::expect(POST, d_uf, f1, false);
//    FakeTheory::expect(POST, d_uf, ffxeqf1, true);
//    FakeTheory::expect(POST, d_bool, or1, false);
//    FakeTheory::expect(POST, d_bool, n, true);

    // do a full rewrite; FakeTheory::preRewrite() and FakeTheory::postRewrite()
    // assert that the rewrite calls that are made match the expected sequence
    // set up above
    nOut = Rewriter::rewrite(n);

    // assert that we consumed the sequence of expected calls completely
//    TS_ASSERT(FakeTheory::nothingMoreExpected());

    // assert that the rewritten node is what we expect
//    TS_ASSERT_EQUALS(nOut, nExpected);
  }

  void testRewriterRules() {
    TypeNode t = d_nm->mkBitVectorType(8);
    Node x = d_nm->mkVar("x", t);
    Node y = d_nm->mkVar("y", t);
    Node z = d_nm->mkVar("z", t);

    // (x - y) * z --> (x * z) - (y * z)
    Node expr =
        d_nm->mkNode(BITVECTOR_MULT, d_nm->mkNode(BITVECTOR_SUB, x, y), z);
    Node result = expr;
    if (RewriteRule<MultDistrib>::applies(expr)) {
      result = RewriteRule<MultDistrib>::apply(expr);
    }
    Node expected =
        d_nm->mkNode(BITVECTOR_SUB, d_nm->mkNode(BITVECTOR_MULT, x, z),
                     d_nm->mkNode(BITVECTOR_MULT, y, z));
    TS_ASSERT_EQUALS(result, expected);

    // Try to apply MultSlice to a multiplication of two and three different
    // variables, expect different results (x * y and x * y * z should not get
    // rewritten to the same term).
    expr = d_nm->mkNode(BITVECTOR_MULT, x, y, z);
    result = expr;
    Node expr2 = d_nm->mkNode(BITVECTOR_MULT, x, y);
    Node result2 = expr;
    if (RewriteRule<MultSlice>::applies(expr)) {
      result = RewriteRule<MultSlice>::apply(expr);
    }
    if (RewriteRule<MultSlice>::applies(expr2)) {
      result2 = RewriteRule<MultSlice>::apply(expr2);
    }
    TS_ASSERT_DIFFERS(result, result2);
  }
};
