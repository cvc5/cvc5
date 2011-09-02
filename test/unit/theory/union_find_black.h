/*********************                                                        */
/*! \file union_find_black.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Black box testing of CVC4::datatypes::UnionFind
 **
 ** Black box testing of CVC4::theory::datatypes::UnionFind.
 **/

#include <cxxtest/TestSuite.h>

#include "context/context.h"
#include "expr/node.h"
#include "theory/datatypes/union_find.h"

using namespace CVC4;
using namespace CVC4::theory::datatypes;
using namespace CVC4::context;

using namespace std;

/**
 * Test the UnionFind.
 */
class UnionFindBlack : public CxxTest::TestSuite {
  Context* d_ctxt;
  UnionFind<TNode, TNodeHashFunction>* d_uf;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;

  Node a, b, c, d, e, f, g;

public:

  void setUp() {
    d_ctxt = new Context;
    d_nm = new NodeManager(d_ctxt, NULL);
    d_scope = new NodeManagerScope(d_nm);
    d_uf = new UnionFind<TNode, TNodeHashFunction>(d_ctxt);

    a = d_nm->mkVar("a", d_nm->realType());
    b = d_nm->mkVar("b", d_nm->realType());
    c = d_nm->mkVar("c", d_nm->realType());
    d = d_nm->mkVar("d", d_nm->realType());
    e = d_nm->mkVar("e", d_nm->realType());
    f = d_nm->mkVar("f", d_nm->realType());
    g = d_nm->mkVar("g", d_nm->realType());
  }

  void tearDown() {
    g = Node::null();
    f = Node::null();
    e = Node::null();
    d = Node::null();
    c = Node::null();
    b = Node::null();
    a = Node::null();

    delete d_uf;
    delete d_scope;
    delete d_nm;
    delete d_ctxt;
  }

  void testSimpleContextual() {
    TS_ASSERT(d_uf->find(a) == a);
    TS_ASSERT(d_uf->find(b) == b);
    TS_ASSERT(d_uf->find(c) == c);
    TS_ASSERT(d_uf->find(d) == d);
    TS_ASSERT(d_uf->find(e) == e);
    TS_ASSERT(d_uf->find(f) == f);
    TS_ASSERT(d_uf->find(g) == g);

    d_ctxt->push();

    d_uf->setCanon(a, b);

    TS_ASSERT(d_uf->find(a) == b);
    TS_ASSERT(d_uf->find(b) == b);
    TS_ASSERT(d_uf->find(c) == c);
    TS_ASSERT(d_uf->find(d) == d);
    TS_ASSERT(d_uf->find(e) == e);
    TS_ASSERT(d_uf->find(f) == f);
    TS_ASSERT(d_uf->find(g) == g);

    d_ctxt->push();
    {
      TS_ASSERT(d_uf->find(a) == b);
      TS_ASSERT(d_uf->find(b) == b);
      TS_ASSERT(d_uf->find(c) == c);
      TS_ASSERT(d_uf->find(d) == d);
      TS_ASSERT(d_uf->find(e) == e);
      TS_ASSERT(d_uf->find(f) == f);
      TS_ASSERT(d_uf->find(g) == g);

      d_uf->setCanon(c, d);
      d_uf->setCanon(f, e);

      TS_ASSERT(d_uf->find(a) == b);
      TS_ASSERT(d_uf->find(b) == b);
      TS_ASSERT(d_uf->find(c) == d);
      TS_ASSERT(d_uf->find(d) == d);
      TS_ASSERT(d_uf->find(e) == e);
      TS_ASSERT(d_uf->find(f) == e);
      TS_ASSERT(d_uf->find(g) == g);

      d_ctxt->push();
      {

        TS_ASSERT(d_uf->find(a) == b);
        TS_ASSERT(d_uf->find(b) == b);
        TS_ASSERT(d_uf->find(c) == d);
        TS_ASSERT(d_uf->find(d) == d);
        TS_ASSERT(d_uf->find(e) == e);
        TS_ASSERT(d_uf->find(f) == e);
        TS_ASSERT(d_uf->find(g) == g);

#ifdef CVC4_ASSERTIONS
        TS_ASSERT_THROWS(d_uf->setCanon(a, c), AssertionException);
        TS_ASSERT_THROWS(d_uf->setCanon(d_uf->find(a), c), AssertionException);
        TS_ASSERT_THROWS(d_uf->setCanon(a, d_uf->find(c)), AssertionException);
#endif /* CVC4_ASSERTIONS */
        d_uf->setCanon(d_uf->find(a), d_uf->find(c));
        d_uf->setCanon(d_uf->find(f), g);
        d_uf->setCanon(d_uf->find(e), d);
#ifdef CVC4_ASSERTIONS
        TS_ASSERT_THROWS(d_uf->setCanon(d_uf->find(c), f), AssertionException);
#endif /* CVC4_ASSERTIONS */
        d_uf->setCanon(d_uf->find(c), d_uf->find(f));

        TS_ASSERT(d_uf->find(a) == d);
        TS_ASSERT(d_uf->find(b) == d);
        TS_ASSERT(d_uf->find(c) == d);
        TS_ASSERT(d_uf->find(d) == d);
        TS_ASSERT(d_uf->find(e) == d);
        TS_ASSERT(d_uf->find(f) == d);
        TS_ASSERT(d_uf->find(g) == d);

        d_uf->setCanon(d_uf->find(g), d_uf->find(a));

        TS_ASSERT(d_uf->find(a) == d);
        TS_ASSERT(d_uf->find(b) == d);
        TS_ASSERT(d_uf->find(c) == d);
        TS_ASSERT(d_uf->find(d) == d);
        TS_ASSERT(d_uf->find(e) == d);
        TS_ASSERT(d_uf->find(f) == d);
        TS_ASSERT(d_uf->find(g) == d);

      }
      d_ctxt->pop();

      TS_ASSERT(d_uf->find(a) == b);
      TS_ASSERT(d_uf->find(b) == b);
      TS_ASSERT(d_uf->find(c) == d);
      TS_ASSERT(d_uf->find(d) == d);
      TS_ASSERT(d_uf->find(e) == e);
      TS_ASSERT(d_uf->find(f) == e);
      TS_ASSERT(d_uf->find(g) == g);
    }
    d_ctxt->pop();

    TS_ASSERT(d_uf->find(a) == b);
    TS_ASSERT(d_uf->find(b) == b);
    TS_ASSERT(d_uf->find(c) == c);
    TS_ASSERT(d_uf->find(d) == d);
    TS_ASSERT(d_uf->find(e) == e);
    TS_ASSERT(d_uf->find(f) == f);
    TS_ASSERT(d_uf->find(g) == g);

    d_ctxt->pop();

    TS_ASSERT(d_uf->find(a) == a);
    TS_ASSERT(d_uf->find(b) == b);
    TS_ASSERT(d_uf->find(c) == c);
    TS_ASSERT(d_uf->find(d) == d);
    TS_ASSERT(d_uf->find(e) == e);
    TS_ASSERT(d_uf->find(f) == f);
    TS_ASSERT(d_uf->find(g) == g);
  }
};
