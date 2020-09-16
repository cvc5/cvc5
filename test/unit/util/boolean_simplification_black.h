/*********************                                                        */
/*! \file boolean_simplification_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andres Noetzli, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::BooleanSimplification
 **
 ** Black box testing of CVC4::BooleanSimplification.
 **/

#include <algorithm>
#include <set>
#include <vector>

#include "expr/expr_iomanip.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "options/language.h"
#include "options/set_language.h"
#include "smt_util/boolean_simplification.h"

using namespace CVC4;
using namespace std;

class BooleanSimplificationBlack : public CxxTest::TestSuite {

  NodeManager* d_nm;
  NodeManagerScope* d_scope;

  Node a, b, c, d, e, f, g, h;
  Node fa, fb, fc, ga, ha, hc, ffb, fhc, hfc, gfb;
  Node ac, ffbd, efhc, dfa;

  // assert equality up to commuting children
  void ASSERT_NODES_EQUAL(TNode n1, TNode n2) {
    cout << "ASSERTING: " << n1 << endl
         << "        ~= " << n2 << endl;
    TS_ASSERT_EQUALS( n1.getKind(), n2.getKind() );
    TS_ASSERT_EQUALS( n1.getNumChildren(), n2.getNumChildren() );
    vector<TNode> v1(n1.begin(), n1.end());
    vector<TNode> v2(n2.begin(), n2.end());
    sort(v1.begin(), v1.end());
    sort(v2.begin(), v2.end());
    TS_ASSERT_EQUALS( v1, v2 );
  }

  // assert that node's children have same elements as the set
  // (so no duplicates); also n is asserted to have kind k
  void ASSERT_NODE_EQUALS_SET(TNode n, Kind k, set<TNode> elts) {
    vector<TNode> v(n.begin(), n.end());

    // BooleanSimplification implementation sorts its output nodes, BUT
    // that's an implementation detail, not part of the contract, so we
    // should be robust to it here; this is a black-box test!
    sort(v.begin(), v.end());

    TS_ASSERT_EQUALS( n.getKind(), k );
    TS_ASSERT_EQUALS( elts.size(), n.getNumChildren() );
    TS_ASSERT( equal(n.begin(), n.end(), elts.begin()) );
  }

public:

  void setUp() {
    d_nm = new NodeManager(NULL);
    d_scope = new NodeManagerScope(d_nm);

    a = d_nm->mkSkolem("a", d_nm->booleanType());
    b = d_nm->mkSkolem("b", d_nm->booleanType());
    c = d_nm->mkSkolem("c", d_nm->booleanType());
    d = d_nm->mkSkolem("d", d_nm->booleanType());
    e = d_nm->mkSkolem("e", d_nm->booleanType());
    f = d_nm->mkSkolem("f", d_nm->mkFunctionType(d_nm->booleanType(),
                                                 d_nm->booleanType()));
    g = d_nm->mkSkolem("g", d_nm->mkFunctionType(d_nm->booleanType(),
                                                 d_nm->booleanType()));
    h = d_nm->mkSkolem("h", d_nm->mkFunctionType(d_nm->booleanType(),
                                                 d_nm->booleanType()));
    fa = d_nm->mkNode(kind::APPLY_UF, f, a);
    fb = d_nm->mkNode(kind::APPLY_UF, f, b);
    fc = d_nm->mkNode(kind::APPLY_UF, f, c);
    ga = d_nm->mkNode(kind::APPLY_UF, g, a);
    ha = d_nm->mkNode(kind::APPLY_UF, h, a);
    hc = d_nm->mkNode(kind::APPLY_UF, h, c);
    ffb = d_nm->mkNode(kind::APPLY_UF, f, fb);
    fhc = d_nm->mkNode(kind::APPLY_UF, f, hc);
    hfc = d_nm->mkNode(kind::APPLY_UF, h, fc);
    gfb = d_nm->mkNode(kind::APPLY_UF, g, fb);

    ac = d_nm->mkNode(kind::EQUAL, a, c);
    ffbd = d_nm->mkNode(kind::EQUAL, ffb, d);
    efhc = d_nm->mkNode(kind::EQUAL, e, fhc);
    dfa = d_nm->mkNode(kind::EQUAL, d, fa);

    // this test is designed for >= 10 removal threshold
    TS_ASSERT_LESS_THAN_EQUALS(10u,
      BooleanSimplification::DUPLICATE_REMOVAL_THRESHOLD);

    cout << expr::ExprSetDepth(-1)
         << language::SetLanguage(language::output::LANG_CVC4);
  }

  void tearDown() {
    a = b = c = d = e = f = g = h = Node();
    fa = fb = fc = ga = ha = hc = ffb = fhc = hfc = gfb = Node();
    ac = ffbd = efhc = dfa = Node();

    delete d_scope;
    delete d_nm;
  }

  void testNegate() {
    Node in, out;

    in = d_nm->mkNode(kind::NOT, a);
    out = a;
    ASSERT_NODES_EQUAL( out, BooleanSimplification::negate(in) );
    ASSERT_NODES_EQUAL( in, BooleanSimplification::negate(out) );

    in = fa.andNode(ac).notNode().notNode().notNode().notNode();
    out = fa.andNode(ac).notNode();
    ASSERT_NODES_EQUAL( out, BooleanSimplification::negate(in) );

#ifdef CVC4_ASSERTIONS
    in = Node();
    TS_ASSERT_THROWS(BooleanSimplification::negate(in),
                     AssertArgumentException&);
#endif /* CVC4_ASSERTIONS */
  }

  void testRemoveDuplicates() {
  }

  void testPushBackAssociativeCommute() {
  }

  void testSimplifyClause() {
    Node in, out;

    in = a.orNode(b);
    out = in;
    ASSERT_NODES_EQUAL(out, BooleanSimplification::simplifyClause(in));

    in = d_nm->mkNode(kind::OR, a, d.andNode(b));
    out = in;
    ASSERT_NODES_EQUAL(out, BooleanSimplification::simplifyClause(in));

    in = d_nm->mkNode(kind::OR, a, d.orNode(b));
    out = d_nm->mkNode(kind::OR, a, d, b);
    ASSERT_NODES_EQUAL(out, BooleanSimplification::simplifyClause(in));

    in = d_nm->mkNode(kind::OR, fa, ga.orNode(c).notNode(), hfc, ac, d.andNode(b));
    out = NodeBuilder<>(kind::OR) << fa << ga.orNode(c).notNode() << hfc << ac << d.andNode(b);
    ASSERT_NODES_EQUAL(out, BooleanSimplification::simplifyClause(in));

    in = d_nm->mkNode(kind::OR, fa, ga.andNode(c).notNode(), hfc, ac, d.andNode(b));
    out = NodeBuilder<>(kind::OR) << fa << ga.notNode() << c.notNode() << hfc << ac << d.andNode(b);
    ASSERT_NODES_EQUAL(out, BooleanSimplification::simplifyClause(in));

#ifdef CVC4_ASSERTIONS
    in = d_nm->mkNode(kind::AND, a, b);
    TS_ASSERT_THROWS(BooleanSimplification::simplifyClause(in),
                     AssertArgumentException&);
#endif /* CVC4_ASSERTIONS */
  }

  void testSimplifyHorn() {
    Node in, out;

    in = a.impNode(b);
    out = a.notNode().orNode(b);
    ASSERT_NODES_EQUAL(out, BooleanSimplification::simplifyHornClause(in));

    in = a.notNode().impNode(ac.andNode(b));
    out = d_nm->mkNode(kind::OR, a, ac.andNode(b));
    ASSERT_NODES_EQUAL(out, BooleanSimplification::simplifyHornClause(in));

    in = a.andNode(b).impNode(d_nm->mkNode(kind::AND, fa, ga.orNode(c).notNode(), hfc.orNode(ac), d.andNode(b)));
    out = d_nm->mkNode(kind::OR, a.notNode(), b.notNode(), d_nm->mkNode(kind::AND, fa, ga.orNode(c).notNode(), hfc.orNode(ac), d.andNode(b)));
    ASSERT_NODES_EQUAL(out, BooleanSimplification::simplifyHornClause(in));

    in = a.andNode(b).impNode(d_nm->mkNode(kind::OR, fa, ga.orNode(c).notNode(), hfc.orNode(ac), d.andNode(b).notNode()));
    out = NodeBuilder<>(kind::OR) << a.notNode() << b.notNode() << fa << ga.orNode(c).notNode() << hfc << ac << d.notNode();
    ASSERT_NODES_EQUAL(out, BooleanSimplification::simplifyHornClause(in));

#ifdef CVC4_ASSERTIONS
    in = d_nm->mkNode(kind::OR, a, b);
    TS_ASSERT_THROWS(BooleanSimplification::simplifyHornClause(in),
                     AssertArgumentException&);
#endif /* CVC4_ASSERTIONS */
  }

  void testSimplifyConflict() {
    Node in, out;

    in = a.andNode(b);
    out = in;
    ASSERT_NODES_EQUAL(out, BooleanSimplification::simplifyConflict(in));

    in = d_nm->mkNode(kind::AND, a, d.andNode(b));
    out = d_nm->mkNode(kind::AND, a, d, b);
    ASSERT_NODES_EQUAL(out, BooleanSimplification::simplifyConflict(in));

    in = d_nm->mkNode(kind::AND, fa, ga.orNode(c).notNode(), fa, hfc.orNode(ac), d.andNode(b));
    out = NodeBuilder<>(kind::AND) << fa << ga.notNode() << c.notNode() << hfc.orNode(ac) << d << b;
    ASSERT_NODES_EQUAL(out, BooleanSimplification::simplifyConflict(in));

#ifdef CVC4_ASSERTIONS
    in = d_nm->mkNode(kind::OR, a, b);
    TS_ASSERT_THROWS(BooleanSimplification::simplifyConflict(in),
                     AssertArgumentException&);
#endif /* CVC4_ASSERTIONS */
  }

};/* class BooleanSimplificationBlack */
