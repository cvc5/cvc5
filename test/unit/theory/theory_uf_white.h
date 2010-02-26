/*********************                                                        */
/** theory_uf_white.h
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** White box testing of CVC4::theory::uf::TheoryUF.
 **/

#include <cxxtest/TestSuite.h>

#include "theory/theory.h"
#include "theory/uf/theory_uf.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "context/context.h"

#include <vector>

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;
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

class TheoryUFWhite : public CxxTest::TestSuite {

  NodeManagerScope *d_scope;
  NodeManager *d_nm;

  TestOutputChannel d_outputChannel;
  Theory::Effort level;

  Context* d_context;
  TheoryUF* d_euf;

public:

  TheoryUFWhite(): level(Theory::FULL_EFFORT) { }

  void setUp() {
    d_nm = new NodeManager();
    d_scope = new NodeManagerScope(d_nm);

    d_context = new Context();

    d_outputChannel.clear();
    d_euf = new TheoryUF(d_context, d_outputChannel);
  }

  void tearDown() {
    delete d_euf;
    delete d_context;
    delete d_scope;
    delete d_nm;
  }

  /* test that {f(f(x)) == x, f(f(f(x))) != f(x)} is inconsistent */
  void testSimpleChain(){
    Node x = d_nm->mkVar();
    Node f = d_nm->mkVar();
    Node f_x = d_nm->mkNode(kind::APPLY, f, x);
    Node f_f_x = d_nm->mkNode(kind::APPLY, f, f_x);
    Node f_f_f_x = d_nm->mkNode(kind::APPLY, f, f_f_x);

    Node f_f_x_eq_x = f_f_x.eqNode(x);
    Node f_f_f_x_neq_f_x = (f_f_f_x.eqNode(f_x)).notNode();

    Node expectedConflict = f_f_f_x_neq_f_x.andNode(f_f_x_eq_x);

    d_euf->assertFact(f_f_x_eq_x);
    d_euf->assertFact(f_f_f_x_neq_f_x);
    d_euf->check(level);

    TS_ASSERT_EQUALS(1, d_outputChannel.getNumCalls());
    TS_ASSERT_EQUALS(CONFLICT, d_outputChannel.getIthCallType(0));

    Node realConflict = d_outputChannel.getIthNode(0);
    TS_ASSERT_EQUALS(expectedConflict, realConflict);

  }

  /* test that !(x == x) is inconsistent */
  void testSelfInconsistent(){
    Node x = d_nm->mkVar();
    Node x_neq_x = (x.eqNode(x)).notNode();
    Node and_x_neq_x = d_nm->mkNode(kind::AND, x_neq_x);

    d_euf->assertFact(x_neq_x);
    d_euf->check(level);

    TS_ASSERT_EQUALS(1, d_outputChannel.getNumCalls());
    TS_ASSERT_EQUALS(and_x_neq_x, d_outputChannel.getIthNode(0));
    TS_ASSERT_EQUALS(CONFLICT, d_outputChannel.getIthCallType(0));
  }

  /* test that (x == x) is consistent */
  void testSelfConsistent(){
    Node x = d_nm->mkVar();
    Node x_eq_x = x.eqNode(x);

    d_euf->assertFact(x_eq_x);
    d_euf->check(level);

    TS_ASSERT_EQUALS(0, d_outputChannel.getNumCalls());
  }


  /* test that
     {f(f(f(x))) == x,
      f(f(f(f(f(x))))) = x,
      f(x) != x
     } is inconsistent */
  void testChain(){
    Node x = d_nm->mkVar();
    Node f = d_nm->mkVar();
    Node f_x = d_nm->mkNode(kind::APPLY, f, x);
    Node f_f_x = d_nm->mkNode(kind::APPLY, f, f_x);
    Node f_f_f_x = d_nm->mkNode(kind::APPLY, f, f_f_x);
    Node f_f_f_f_x = d_nm->mkNode(kind::APPLY, f, f_f_f_x);
    Node f_f_f_f_f_x = d_nm->mkNode(kind::APPLY, f, f_f_f_f_x);

    Node f3_x_eq_x = f_f_f_x.eqNode(x);
    Node f5_x_eq_x = f_f_f_f_f_x.eqNode(x);
    Node f1_x_neq_x = f_x.eqNode(x).notNode();

    Node expectedConflict = d_nm->mkNode(kind::AND,
                                         f1_x_neq_x,
                                         f3_x_eq_x,
                                         f5_x_eq_x
                                         );

    d_euf->assertFact( f3_x_eq_x );
    d_euf->assertFact( f5_x_eq_x );
    d_euf->assertFact( f1_x_neq_x );
    d_euf->check(level);

    TS_ASSERT_EQUALS(1, d_outputChannel.getNumCalls());
    TS_ASSERT_EQUALS(CONFLICT, d_outputChannel.getIthCallType(0));
    Node realConflict = d_outputChannel.getIthNode(0);
    TS_ASSERT_EQUALS(expectedConflict, realConflict);
  }
};
