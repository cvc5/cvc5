/*********************                                                        */
/*! \file theory_black.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: barrett, mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Black box testing of CVC4::theory::Theory.
 **
 ** Black box testing of CVC4::theory::Theory.
 **/

#include <cxxtest/TestSuite.h>

#include "theory/theory.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "context/context.h"

#include <vector>

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::expr;
using namespace CVC4::context;

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

  void safePoint() throw(Interrupted, AssertionException) {}

  void conflict(TNode n, bool safe = false)
    throw(Interrupted, AssertionException) {
    push(CONFLICT, n);
  }

  void propagate(TNode n, bool safe = false)
    throw(Interrupted, AssertionException) {
    push(PROPAGATE, n);
  }

  void lemma(TNode n, bool safe = false)
    throw(Interrupted, AssertionException) {
    push(LEMMA, n);
  }
  void augmentingLemma(TNode n, bool safe = false)
    throw(Interrupted, AssertionException) {
    Unreachable();
  }

  void explanation(TNode n, bool safe = false)
    throw(Interrupted, AssertionException) {
    push(EXPLANATION, n);
  }

  void setIncomplete()
    throw(Interrupted, AssertionException) {
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

  DummyTheory(Context* ctxt, OutputChannel& out) :
    Theory(0, ctxt, out) {
  }

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

  void preRegisterTerm(TNode n) {}
  void propagate(Effort level) {}
  void explain(TNode n, Effort level) {}
  Node getValue(TNode n, TheoryEngine* engine) { return Node::null(); }
  string identify() const { return "DummyTheory"; }
};

class TheoryBlack : public CxxTest::TestSuite {

  Context* d_ctxt;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;

  TestOutputChannel d_outputChannel;

  DummyTheory* d_dummy;

  Node atom0;
  Node atom1;

public:

  void setUp() {
    d_ctxt = new Context;
    d_nm = new NodeManager(d_ctxt);
    d_scope = new NodeManagerScope(d_nm);
    d_dummy = new DummyTheory(d_ctxt, d_outputChannel);
    d_outputChannel.clear();
    atom0 = d_nm->mkConst(true);
    atom1 = d_nm->mkConst(false);
  }

  void tearDown() {
    atom1 = Node::null();
    atom0 = Node::null();
    delete d_dummy;
    delete d_scope;
    delete d_nm;
    delete d_ctxt;
  }

  void testEffort(){
    Theory::Effort m = Theory::MIN_EFFORT;
    Theory::Effort q = Theory::QUICK_CHECK;
    Theory::Effort s = Theory::STANDARD;
    Theory::Effort f = Theory::FULL_EFFORT;

    TS_ASSERT( Theory::minEffortOnly(m));
    TS_ASSERT(!Theory::minEffortOnly(q));
    TS_ASSERT(!Theory::minEffortOnly(s));
    TS_ASSERT(!Theory::minEffortOnly(f));

    TS_ASSERT(!Theory::quickCheckOnly(m));
    TS_ASSERT( Theory::quickCheckOnly(q));
    TS_ASSERT(!Theory::quickCheckOnly(s));
    TS_ASSERT(!Theory::quickCheckOnly(f));

    TS_ASSERT(!Theory::standardEffortOnly(m));
    TS_ASSERT(!Theory::standardEffortOnly(q));
    TS_ASSERT( Theory::standardEffortOnly(s));
    TS_ASSERT(!Theory::standardEffortOnly(f));

    TS_ASSERT(!Theory::fullEffort(m));
    TS_ASSERT(!Theory::fullEffort(q));
    TS_ASSERT(!Theory::fullEffort(s));
    TS_ASSERT( Theory::fullEffort(f));

    TS_ASSERT(!Theory::quickCheckOrMore(m));
    TS_ASSERT( Theory::quickCheckOrMore(q));
    TS_ASSERT( Theory::quickCheckOrMore(s));
    TS_ASSERT( Theory::quickCheckOrMore(f));

    TS_ASSERT(!Theory::standardEffortOrMore(m));
    TS_ASSERT(!Theory::standardEffortOrMore(q));
    TS_ASSERT( Theory::standardEffortOrMore(s));
    TS_ASSERT( Theory::standardEffortOrMore(f));
  }

  void testDone() {
    TS_ASSERT(d_dummy->doneWrapper());

    d_dummy->assertFact(atom0);
    d_dummy->assertFact(atom1);

    TS_ASSERT(!d_dummy->doneWrapper());

    d_dummy->check(Theory::FULL_EFFORT);

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
};
