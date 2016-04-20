/*********************                                                        */
/*! \file stacking_vector_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::context::StackingVector
 **
 ** Black box testing of CVC4::context::StackingVector.
 **/

#include <cxxtest/TestSuite.h>

#include "context/context.h"
#include "expr/node.h"
#include "context/stacking_vector.h"

using namespace CVC4;
using namespace CVC4::context;

using namespace std;

/**
 * Test the StackingVector.
 */
class StackingVectorBlack : public CxxTest::TestSuite {
  Context* d_ctxt;
  StackingVector<TNode>* d_vectorPtr;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;

  Node a, b, c, d, e, f, g;

public:

  void setUp() {
    d_ctxt = new Context();
    d_nm = new NodeManager(NULL);
    d_scope = new NodeManagerScope(d_nm);
    d_vectorPtr = new StackingVector<TNode>(d_ctxt);

    a = d_nm->mkSkolem("a", d_nm->realType());
    b = d_nm->mkSkolem("b", d_nm->realType());
    c = d_nm->mkSkolem("c", d_nm->realType());
    d = d_nm->mkSkolem("d", d_nm->realType());
    e = d_nm->mkSkolem("e", d_nm->realType());
    f = d_nm->mkSkolem("f", d_nm->realType());
    g = d_nm->mkSkolem("g", d_nm->realType());
  }

  void tearDown() {
    g = Node::null();
    f = Node::null();
    e = Node::null();
    d = Node::null();
    c = Node::null();
    b = Node::null();
    a = Node::null();

    delete d_vectorPtr;
    delete d_scope;
    delete d_nm;
    delete d_ctxt;
  }

  void testSimpleContextual() {
    StackingVector<TNode>& d_vector = *d_vectorPtr;

    TS_ASSERT(d_vector[1].isNull());
    TS_ASSERT(d_vector[2].isNull());
    TS_ASSERT(d_vector[3].isNull());
    TS_ASSERT(d_vector[4].isNull());
    TS_ASSERT(d_vector[5].isNull());
    TS_ASSERT(d_vector[6].isNull());
    TS_ASSERT(d_vector[7].isNull());

    d_vector.set(1, b);

    TS_ASSERT(d_vector[1] == b);
    TS_ASSERT(d_vector[2].isNull());
    TS_ASSERT(d_vector[3].isNull());
    TS_ASSERT(d_vector[4].isNull());
    TS_ASSERT(d_vector[5].isNull());
    TS_ASSERT(d_vector[6].isNull());
    TS_ASSERT(d_vector[7].isNull());

    d_ctxt->push();
    {
      TS_ASSERT(d_vector[1] == b);
      TS_ASSERT(d_vector[2].isNull());
      TS_ASSERT(d_vector[3].isNull());
      TS_ASSERT(d_vector[4].isNull());
      TS_ASSERT(d_vector[5].isNull());
      TS_ASSERT(d_vector[6].isNull());
      TS_ASSERT(d_vector[7].isNull());

      d_vector.set(3, d);
      d_vector.set(6, e);

      TS_ASSERT(d_vector[1] == b);
      TS_ASSERT(d_vector[2].isNull());
      TS_ASSERT(d_vector[3] == d);
      TS_ASSERT(d_vector[4].isNull());
      TS_ASSERT(d_vector[5].isNull());
      TS_ASSERT(d_vector[6] == e);
      TS_ASSERT(d_vector[7].isNull());

      d_ctxt->push();
      {

        TS_ASSERT(d_vector[1] == b);
        TS_ASSERT(d_vector[2].isNull());
        TS_ASSERT(d_vector[3] == d);
        TS_ASSERT(d_vector[4].isNull());
        TS_ASSERT(d_vector[5].isNull());
        TS_ASSERT(d_vector[6] == e);
        TS_ASSERT(d_vector[7].isNull());

        d_vector.set(1, c);
        d_vector.set(6, f);
        d_vector.set(5, d);
        d_vector.set(3, Node::null());
        d_vector.set(7, a);

        TS_ASSERT(d_vector[1] == c);
        TS_ASSERT(d_vector[2].isNull());
        TS_ASSERT(d_vector[3].isNull());
        TS_ASSERT(d_vector[4].isNull());
        TS_ASSERT(d_vector[5] == d);
        TS_ASSERT(d_vector[6] == f);
        TS_ASSERT(d_vector[7] == a);

      }
      d_ctxt->pop();

      TS_ASSERT(d_vector[1] == b);
      TS_ASSERT(d_vector[2].isNull());
      TS_ASSERT(d_vector[3] == d);
      TS_ASSERT(d_vector[4].isNull());
      TS_ASSERT(d_vector[5].isNull());
      TS_ASSERT(d_vector[6] == e);
      TS_ASSERT(d_vector[7].isNull());
    }
    d_ctxt->pop();

    TS_ASSERT(d_vector[1] == b);
    TS_ASSERT(d_vector[2].isNull());
    TS_ASSERT(d_vector[3].isNull());
    TS_ASSERT(d_vector[4].isNull());
    TS_ASSERT(d_vector[5].isNull());
    TS_ASSERT(d_vector[6].isNull());
    TS_ASSERT(d_vector[7].isNull());
  }
};
