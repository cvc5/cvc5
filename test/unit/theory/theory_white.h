/*********************                                                        */
/*! \file theory_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::theory::Theory.
 **
 ** Black box testing of CVC4::theory::Theory.
 **/

#include <cxxtest/TestSuite.h>
#include <vector>

// taking: Add include for Proof*.
#include "context/context.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"


using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::expr;
using namespace CVC4::context;
using namespace CVC4::smt;

using namespace std;

/**
 * Very basic OutputChannel for testing simple Theory Behaviour.
 * Stores a call sequence for the output channel
 */
enum OutputChannelCallType{CONFLICT, PROPAGATE, LEMMA, EXPLANATION};
class TestOutputChannel : public OutputChannel {
private:
  void push(OutputChannelCallType call, TNode n) {
    d_callHistory.push_back(make_pair(call, n));
  }

public:
  vector< pair<OutputChannelCallType, Node> > d_callHistory;

  TestOutputChannel() {}

  ~TestOutputChannel() {}

  void safePoint(uint64_t amount)
      throw(Interrupted, UnsafeInterruptException, AssertionException)
  {}

  void conflict(TNode n, Proof* pf = NULL)
    throw(AssertionException) {
    push(CONFLICT, n);
  }

  bool propagate(TNode n)
    throw(AssertionException) {
    push(PROPAGATE, n);
    return true;
  }

  void propagateAsDecision(TNode n)
    throw(AssertionException) {
    // ignore
  }

  LemmaStatus lemma(TNode n, ProofRule rule,
                    bool removable = false,
                    bool preprocess = false,
                    bool sendAtoms = false)
    throw(AssertionException) {
    push(LEMMA, n);
    return LemmaStatus(Node::null(), 0);
  }

  LemmaStatus splitLemma(TNode n, bool removable) throw (TypeCheckingExceptionPrivate, AssertionException){
    push(LEMMA, n);
    return LemmaStatus(Node::null(), 0);
  }

  void requirePhase(TNode, bool)
    throw(Interrupted, AssertionException) {
    Unreachable();
  }

  bool flipDecision()
    throw(Interrupted, AssertionException) {
    Unreachable();
  }

  void setIncomplete()
    throw(AssertionException) {
    Unreachable();
  }

  void clear() {
    d_callHistory.clear();
  }

  Node getIthNode(int i) {
    Node tmp = (d_callHistory[i]).second;
    return tmp;
  }

  OutputChannelCallType getIthCallType(int i) {
    return (d_callHistory[i]).first;
  }

  unsigned getNumCalls() {
    return d_callHistory.size();
  }
};

class DummyTheory : public Theory {
public:
  set<Node> d_registered;
  vector<Node> d_getSequence;

  DummyTheory(Context* ctxt, UserContext* uctxt, OutputChannel& out,
              Valuation valuation, const LogicInfo& logicInfo)
      : Theory(theory::THEORY_BUILTIN, ctxt, uctxt, out, valuation, logicInfo)
  {}

  void registerTerm(TNode n) {
    // check that we registerTerm() a term only once
    TS_ASSERT(d_registered.find(n) == d_registered.end());

    for(TNode::iterator i = n.begin(); i != n.end(); ++i) {
      // check that registerTerm() is called in reverse topological order
      TS_ASSERT(d_registered.find(*i) != d_registered.end());
    }

    d_registered.insert(n);
  }

  Node getWrapper() {
    Node n = get();
    d_getSequence.push_back(n);
    return n;
  }

  bool doneWrapper() {
    return done();
  }

  void check(Effort e) {
    while(!done()) {
      getWrapper();
    }
  }

  void presolve() {
    Unimplemented();
  }
  void preRegisterTerm(TNode n) {}
  void propagate(Effort level) {}
  Node explain(TNode n) { return Node::null(); }
  Node getValue(TNode n) { return Node::null(); }
  string identify() const { return "DummyTheory"; }
};/* class DummyTheory */

class TheoryBlack : public CxxTest::TestSuite {

  Context* d_ctxt;
  UserContext* d_uctxt;
  NodeManager* d_nm;
  ExprManager* d_em;
  SmtScope* d_scope;
  SmtEngine* d_smt;
  LogicInfo* d_logicInfo;

  TestOutputChannel d_outputChannel;

  DummyTheory* d_dummy;

  Node atom0;
  Node atom1;

public:

  void setUp() {
    d_em = new ExprManager();
    d_nm = NodeManager::fromExprManager(d_em);
    d_smt = new SmtEngine(d_em);
    d_ctxt = d_smt->d_context;
    d_uctxt = d_smt->d_userContext;
    d_scope = new SmtScope(d_smt);
    d_logicInfo = new LogicInfo();
    d_logicInfo->lock();

    // guard against duplicate statistics assertion errors
    delete d_smt->d_theoryEngine->d_theoryTable[THEORY_BUILTIN];
    delete d_smt->d_theoryEngine->d_theoryOut[THEORY_BUILTIN];
    d_smt->d_theoryEngine->d_theoryTable[THEORY_BUILTIN] = NULL;
    d_smt->d_theoryEngine->d_theoryOut[THEORY_BUILTIN] = NULL;

    d_dummy = new DummyTheory(d_ctxt, d_uctxt, d_outputChannel, Valuation(NULL),
                              *d_logicInfo);
    d_outputChannel.clear();
    atom0 = d_nm->mkConst(true);
    atom1 = d_nm->mkConst(false);
  }

  void tearDown() {
    atom1 = Node::null();
    atom0 = Node::null();
    delete d_dummy;
    delete d_logicInfo;
    delete d_scope;
    delete d_smt;
    delete d_em;
  }

  void testEffort(){
    Theory::Effort s = Theory::EFFORT_STANDARD;
    Theory::Effort f = Theory::EFFORT_FULL;

    TS_ASSERT( Theory::standardEffortOnly(s));
    TS_ASSERT(!Theory::standardEffortOnly(f));

    TS_ASSERT(!Theory::fullEffort(s));
    TS_ASSERT( Theory::fullEffort(f));

    TS_ASSERT( Theory::standardEffortOrMore(s));
    TS_ASSERT( Theory::standardEffortOrMore(f));
  }

  void testDone() {
    TS_ASSERT(d_dummy->doneWrapper());

    d_dummy->assertFact(atom0, true);
    d_dummy->assertFact(atom1, true);

    TS_ASSERT(!d_dummy->doneWrapper());

    d_dummy->check(Theory::EFFORT_FULL);

    TS_ASSERT(d_dummy->doneWrapper());
  }

  // FIXME: move this to theory_engine test?
//   void testRegisterTerm() {
//     TS_ASSERT(d_dummy->doneWrapper());

//     TypeNode typeX = d_nm->booleanType();
//     TypeNode typeF = d_nm->mkFunctionType(typeX, typeX);

//     Node x = d_nm->mkVar("x",typeX);
//     Node f = d_nm->mkVar("f",typeF);
//     Node f_x = d_nm->mkNode(kind::APPLY_UF, f, x);
//     Node f_f_x = d_nm->mkNode(kind::APPLY_UF, f, f_x);
//     Node f_x_eq_x = f_x.eqNode(x);
//     Node x_eq_f_f_x = x.eqNode(f_f_x);

//     d_dummy->assertFact(f_x_eq_x);
//     d_dummy->assertFact(x_eq_f_f_x);

//     Node got = d_dummy->getWrapper();

//     TS_ASSERT_EQUALS(got, f_x_eq_x);

//     TS_ASSERT_EQUALS(5u, d_dummy->d_registered.size());
//     TS_ASSERT(d_dummy->d_registered.find(x) != d_dummy->d_registered.end());
//     TS_ASSERT(d_dummy->d_registered.find(f) != d_dummy->d_registered.end());
//     TS_ASSERT(d_dummy->d_registered.find(f_x) != d_dummy->d_registered.end());
//     TS_ASSERT(d_dummy->d_registered.find(f_x_eq_x) != d_dummy->d_registered.end());
//     TS_ASSERT(d_dummy->d_registered.find(d_nm->operatorOf(kind::EQUAL)) != d_dummy->d_registered.end());
//     TS_ASSERT(d_dummy->d_registered.find(f_f_x) == d_dummy->d_registered.end());
//     TS_ASSERT(d_dummy->d_registered.find(x_eq_f_f_x) == d_dummy->d_registered.end());

//     TS_ASSERT(!d_dummy->doneWrapper());

//     got = d_dummy->getWrapper();

//     TS_ASSERT_EQUALS(got, x_eq_f_f_x);

//     TS_ASSERT_EQUALS(7u, d_dummy->d_registered.size());
//     TS_ASSERT(d_dummy->d_registered.find(f_f_x) != d_dummy->d_registered.end());
//     TS_ASSERT(d_dummy->d_registered.find(x_eq_f_f_x) != d_dummy->d_registered.end());

//     TS_ASSERT(d_dummy->doneWrapper());
//   }

  void testOutputChannelAccessors() {
    /* void setOutputChannel(OutputChannel& out)  */
    /* OutputChannel& getOutputChannel() */

    TestOutputChannel theOtherChannel;

    TS_ASSERT_EQUALS(&(d_dummy->getOutputChannel()), &d_outputChannel);

    d_dummy->setOutputChannel(theOtherChannel);

    TS_ASSERT_EQUALS(&(d_dummy->getOutputChannel()), &theOtherChannel);

    const OutputChannel& oc = d_dummy->getOutputChannel();

    TS_ASSERT_EQUALS(&oc, &theOtherChannel);
  }

  void testOutputChannel() {
    Node n = atom0.orNode(atom1);
    d_outputChannel.lemma(n, RULE_INVALID);
    d_outputChannel.split(atom0);
    Node s = atom0.orNode(atom0.notNode());
    TS_ASSERT_EQUALS(d_outputChannel.d_callHistory.size(), 2u);
    TS_ASSERT_EQUALS(d_outputChannel.d_callHistory[0], make_pair(LEMMA, n));
    TS_ASSERT_EQUALS(d_outputChannel.d_callHistory[1], make_pair(LEMMA, s));
    d_outputChannel.d_callHistory.clear();
  }
};
