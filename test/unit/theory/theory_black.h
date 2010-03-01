/*********************                                                        */
/** theory_black.h
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
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
enum OutputChannelCallType{CONFLICT, PROPOGATE, LEMMA, EXPLANATION};
class TestOutputChannel : public OutputChannel {
private:
  void push(OutputChannelCallType call, TNode n){
    d_callHistory.push_back(make_pair(call,n));
  }
public:
  vector< pair<OutputChannelCallType, Node> > d_callHistory;

  TestOutputChannel() {}

  ~TestOutputChannel() {}

  void safePoint() throw(Interrupted) {}

  void conflict(TNode n, bool safe = false) throw(Interrupted){
    push(CONFLICT, n);
  }

  void propagate(TNode n, bool safe = false) throw(Interrupted){
    push(PROPOGATE, n);
  }

  void lemma(TNode n, bool safe = false) throw(Interrupted){
    push(LEMMA, n);
  }
  void explanation(TNode n, bool safe = false) throw(Interrupted){
    push(EXPLANATION, n);
  }

  void clear(){
    d_callHistory.clear();
  }
  Node getIthNode(int i){
    Node tmp = (d_callHistory[i]).second;
    return tmp;
  }

  OutputChannelCallType getIthCallType(int i){
    return (d_callHistory[i]).first;
  }

  unsigned getNumCalls(){
    return d_callHistory.size();
  }
};

class DummyTheory : public TheoryImpl<DummyTheory> {
public:
  vector<Node> d_registerSequence;
  vector<Node> d_getSequence;

  DummyTheory(context::Context* ctxt, OutputChannel& out) :
    TheoryImpl<DummyTheory>(ctxt, out) {}

  void registerTerm(TNode n){
    d_registerSequence.push_back(n);
  }


  Node getWrapper(){
    Node n = get();
    d_getSequence.push_back(n);
    return n;
  }

  bool doneWrapper(){
    return done();
  }

  void check(Effort e){
    while(!done()){
      getWrapper();
    }
  }

  void preRegisterTerm(TNode n ){}
  void propagate(Effort level = FULL_EFFORT){}
  void explain(TNode n, Effort level = FULL_EFFORT){}

};

class TheoryBlack : public CxxTest::TestSuite {

  NodeManagerScope *d_scope;
  NodeManager *d_nm;

  TestOutputChannel d_outputChannel;

  Context* d_context;

  DummyTheory* d_dummy;

  Node atom0;
  Node atom1;

public:

  TheoryBlack() { }

  void setUp() {
    d_nm = new NodeManager();

    d_scope = new NodeManagerScope(d_nm);

    d_context = new Context();

    d_dummy = new DummyTheory(d_context, d_outputChannel);

    d_outputChannel.clear();

    atom0 = d_nm->mkNode(kind::TRUE);
    atom1 = d_nm->mkNode(kind::FALSE);
  }

  void tearDown() {
    delete d_dummy;
    delete d_context;
    delete d_scope;
    delete d_nm;
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

  void testDone(){
    TS_ASSERT(d_dummy->doneWrapper());

    d_dummy->assertFact(atom0);
    d_dummy->assertFact(atom1);

    TS_ASSERT(!d_dummy->doneWrapper());

    d_dummy->check(Theory::FULL_EFFORT);

    TS_ASSERT(d_dummy->doneWrapper());
  }

  void testRegisterSequence(){
    TS_ASSERT(d_dummy->doneWrapper());

    Node x = d_nm->mkVar();
    Node f = d_nm->mkVar();
    Node f_x = d_nm->mkNode(kind::APPLY, f, x);
    Node f_f_x = d_nm->mkNode(kind::APPLY, f, f_x);
    Node f_x_eq_x = f_x.eqNode(x);
    Node x_eq_f_f_x = x.eqNode(f_f_x);


    d_dummy->assertFact(f_x_eq_x);
    d_dummy->assertFact(x_eq_f_f_x);

    Node got = d_dummy->getWrapper();

    TS_ASSERT_EQUALS(got, f_x_eq_x);

    TS_ASSERT_EQUALS(4, d_dummy-> d_registerSequence.size());
    TS_ASSERT_EQUALS(x, d_dummy-> d_registerSequence[0]);
    TS_ASSERT_EQUALS(f, d_dummy-> d_registerSequence[1]);
    TS_ASSERT_EQUALS(f_x, d_dummy-> d_registerSequence[2]);
    TS_ASSERT_EQUALS(f_x_eq_x, d_dummy-> d_registerSequence[3]);

    TS_ASSERT(!d_dummy->doneWrapper());

    got = d_dummy->getWrapper();

    TS_ASSERT_EQUALS(got, x_eq_f_f_x);

    TS_ASSERT_EQUALS(6, d_dummy-> d_registerSequence.size());
    TS_ASSERT_EQUALS(f_f_x, d_dummy-> d_registerSequence[4]);
    TS_ASSERT_EQUALS(x_eq_f_f_x, d_dummy-> d_registerSequence[5]);

    TS_ASSERT(d_dummy->doneWrapper());
  }


  void testOutputChannelAccessors(){
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
