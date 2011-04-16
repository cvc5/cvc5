/*********************                                                        */
/*! \file congruence_closure_white.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief White box testing of CVC4::CongruenceClosure.
 **
 ** White box testing of CVC4::CongruenceClosure.
 **/

#include <cxxtest/TestSuite.h>
#include <sstream>

#include "context/context.h"
#include "context/cdset.h"
#include "context/cdmap.h"
#include "expr/node.h"
#include "expr/kind.h"
#include "expr/node_manager.h"
#include "util/congruence_closure.h"


using namespace CVC4;
using namespace CVC4::context;
using namespace std;


struct MyOutputChannel {
  CDSet<Node, NodeHashFunction> d_notifications;
  CDMap<Node, Node, NodeHashFunction> d_equivalences;
  NodeManager* d_nm;

  MyOutputChannel(Context* ctxt, NodeManager* nm) :
    d_notifications(ctxt),
    d_equivalences(ctxt),
    d_nm(nm) {
  }

  bool saw(TNode a, TNode b) {
    return d_notifications.contains(d_nm->mkNode(kind::EQUAL, a, b)) ||
      d_notifications.contains(d_nm->mkNode(kind::EQUAL, b, a));
  }

  TNode find(TNode n) {
    CDMap<Node, Node, NodeHashFunction>::iterator i = d_equivalences.find(n);
    if(i == d_equivalences.end()) {
      return n;
    } else {
      // lazy path compression
      TNode p = (*i).second; // parent
      TNode f = d_equivalences[n] = find(p); // compress
      return f;
    }
  }

  bool areCongruent(TNode a, TNode b) {
    Debug("cc") << "=== a is  " << a << std::endl
                << "=== a' is " << find(a) << std::endl
                << "=== b is  " << b << std::endl
                << "=== b' is " << find(b) << std::endl;

    return find(a) == find(b);
  }

  void notifyCongruent(TNode a, TNode b) {
    Debug("cc") << "======OI!  I've been notified of: "
                << a << " == " << b << std::endl;

    Node eq = d_nm->mkNode(kind::EQUAL, a, b);
    Node eqRev = d_nm->mkNode(kind::EQUAL, b, a);

    TS_ASSERT(!d_notifications.contains(eq));
    TS_ASSERT(!d_notifications.contains(eqRev));

    d_notifications.insert(eq);

    d_equivalences.insert(a, b);
  }
};/* class MyOutputChannel */


class CongruenceClosureWhite : public CxxTest::TestSuite {
  Context* d_context;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;
  MyOutputChannel* d_out;
  CongruenceClosure<MyOutputChannel, CongruenceOperator<kind::APPLY_UF> >* d_cc;
  CongruenceClosure<MyOutputChannel, CONGRUENCE_OPERATORS_2(kind::SELECT, kind::STORE)>* d_ccArray;

  TypeNode U;
  Node a, f, fa, ffa, fffa, ffffa, b, fb, ffb, fffb, ffffb;
  Node g, gab, gba, gfafb, gfbfa, gfaa, gbfb;
  Node h, hab, hba, hfaa;
  Node a_eq_b, fa_eq_b, a_eq_fb, fa_eq_fb, h_eq_g;

  Node ar, ar_a, ar_b;
  Node arar, arar_a, arar_b;

public:

  void setUp() {
    d_context = new Context;
    d_nm = new NodeManager(d_context, NULL);
    d_scope = new NodeManagerScope(d_nm);
    d_out = new MyOutputChannel(d_context, d_nm);
    d_cc = new CongruenceClosure<MyOutputChannel, CongruenceOperator<kind::APPLY_UF> >(d_context, d_out);
    d_ccArray = new CongruenceClosure<MyOutputChannel, CONGRUENCE_OPERATORS_2(kind::SELECT, kind::STORE)>(d_context, d_out);

    U = d_nm->mkSort("U");

    f = d_nm->mkVar("f", d_nm->mkFunctionType(U, U));
    a = d_nm->mkVar("a", U);
    fa = d_nm->mkNode(kind::APPLY_UF, f, a);
    ffa = d_nm->mkNode(kind::APPLY_UF, f, fa);
    fffa = d_nm->mkNode(kind::APPLY_UF, f, ffa);
    ffffa = d_nm->mkNode(kind::APPLY_UF, f, fffa);
    b = d_nm->mkVar("b", U);
    fb = d_nm->mkNode(kind::APPLY_UF, f, b);
    ffb = d_nm->mkNode(kind::APPLY_UF, f, fb);
    fffb = d_nm->mkNode(kind::APPLY_UF, f, ffb);
    ffffb = d_nm->mkNode(kind::APPLY_UF, f, fffb);
    vector<TypeNode> args(2, U);
    g = d_nm->mkVar("g", d_nm->mkFunctionType(args, U));
    gab = d_nm->mkNode(kind::APPLY_UF, g, a, b);
    gfafb = d_nm->mkNode(kind::APPLY_UF, g, fa, fb);
    gba = d_nm->mkNode(kind::APPLY_UF, g, b, a);
    gfbfa = d_nm->mkNode(kind::APPLY_UF, g, fb, fa);
    gfaa = d_nm->mkNode(kind::APPLY_UF, g, fa, a);
    gbfb = d_nm->mkNode(kind::APPLY_UF, g, b, fb);
    h = d_nm->mkVar("h", d_nm->mkFunctionType(args, U));
    hab = d_nm->mkNode(kind::APPLY_UF, h, a, b);
    hba = d_nm->mkNode(kind::APPLY_UF, h, b, a);
    hfaa = d_nm->mkNode(kind::APPLY_UF, h, fa, a);

    a_eq_b = d_nm->mkNode(kind::EQUAL, a, b);
    fa_eq_b = d_nm->mkNode(kind::EQUAL, fa, b);
    a_eq_fb = d_nm->mkNode(kind::EQUAL, a, fb);
    fa_eq_fb = d_nm->mkNode(kind::EQUAL, fa, fb);

    h_eq_g = d_nm->mkNode(kind::EQUAL, h, g);

    // arrays
    ar = d_nm->mkVar("ar", d_nm->mkArrayType(U, U));
    ar_a = d_nm->mkNode(kind::SELECT, ar, a);
    ar_b = d_nm->mkNode(kind::SELECT, ar, b);

    arar = d_nm->mkVar("arar", d_nm->mkArrayType(U, d_nm->mkArrayType(U, U)));
    arar_a = d_nm->mkNode(kind::SELECT, arar, a);
    arar_b = d_nm->mkNode(kind::SELECT, arar, b);
  }

  void tearDown() {
    try {
      arar = arar_a = arar_b = Node::null();
      ar = ar_a = ar_b = Node::null();

      f = a = fa = ffa = fffa = ffffa = Node::null();
      b = fb = ffb = fffb = ffffb = Node::null();
      g = gab = gba = gfafb = gfbfa = gfaa = gbfb = Node::null();
      h = hab = hba = hfaa = Node::null();
      a_eq_b = fa_eq_b = a_eq_fb = fa_eq_fb = h_eq_g = Node::null();
      U = TypeNode::null();

      delete d_ccArray;
      delete d_cc;
      delete d_out;
      delete d_scope;
      delete d_nm;
      delete d_context;
    } catch(Exception& e) {
      cout << "\n\n" << e << "\n\n";
      throw;
    }
  }

  void testSimple() {
    //Debug.on("cc");
    // add terms, then add equalities

    d_cc->addTerm(fa);
    d_cc->addTerm(fb);

    d_cc->addEquality(a_eq_b);

    TS_ASSERT(d_out->areCongruent(fa, fb));
    TS_ASSERT(d_cc->areCongruent(fa, fb));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(d_cc->areCongruent(a, b));
  }

  void testSimpleReverse() {
    // add equalities, then add terms; should get the same as
    // testSimple()

    d_cc->addEquality(a_eq_b);

    d_cc->addTerm(fa);
    d_cc->addTerm(fb);

    TS_ASSERT(d_out->areCongruent(fa, fb));
    TS_ASSERT(d_cc->areCongruent(fa, fb));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(d_cc->areCongruent(a, b));
  }

  void testSimpleContextual() {
    TS_ASSERT(!d_out->areCongruent(fa, fb));
    TS_ASSERT(!d_cc->areCongruent(fa, fb));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(!d_cc->areCongruent(a, b));

    {
      d_context->push();

      d_cc->addTerm(fa);
      d_cc->addTerm(fb);

      TS_ASSERT(!d_out->areCongruent(fa, fb));
      TS_ASSERT(!d_cc->areCongruent(fa, fb));

      TS_ASSERT(!d_out->areCongruent(a, b));
      TS_ASSERT(!d_cc->areCongruent(a, b));

      {
        d_context->push();

        d_cc->addEquality(a_eq_b);

        TS_ASSERT(d_out->areCongruent(fa, fb));
        TS_ASSERT(d_cc->areCongruent(fa, fb));

        TS_ASSERT(!d_out->areCongruent(a, b));
        TS_ASSERT(d_cc->areCongruent(a, b));

        d_context->pop();
      }

      TS_ASSERT(!d_out->areCongruent(fa, fb));
      TS_ASSERT(!d_cc->areCongruent(fa, fb));

      TS_ASSERT(!d_out->areCongruent(a, b));
      TS_ASSERT(!d_cc->areCongruent(a, b));

      d_context->pop();
    }

    TS_ASSERT(!d_out->areCongruent(fa, fb));
    TS_ASSERT(!d_cc->areCongruent(fa, fb));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(!d_cc->areCongruent(a, b));
  }

  void testSimpleContextualReverse() {
    TS_ASSERT(!d_out->areCongruent(fa, fb));
    TS_ASSERT(!d_cc->areCongruent(fa, fb));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(!d_cc->areCongruent(a, b));

    {
      d_context->push();

      d_cc->addEquality(a_eq_b);

      TS_ASSERT(!d_out->areCongruent(fa, fb));
      TS_ASSERT(d_cc->areCongruent(fa, fb));

      TS_ASSERT(!d_out->areCongruent(a, b));
      TS_ASSERT(d_cc->areCongruent(a, b));

      {
        d_context->push();

        d_cc->addTerm(fa);
        d_cc->addTerm(fb);

        TS_ASSERT(d_out->areCongruent(fa, fb));
        TS_ASSERT(d_cc->areCongruent(fa, fb));

        TS_ASSERT(!d_out->areCongruent(a, b));
        TS_ASSERT(d_cc->areCongruent(a, b));

        d_context->pop();
      }

      TS_ASSERT(!d_out->areCongruent(fa, fb));
      TS_ASSERT(d_cc->areCongruent(fa, fb));

      TS_ASSERT(!d_out->areCongruent(a, b));
      TS_ASSERT(d_cc->areCongruent(a, b));

      d_context->pop();
    }

    TS_ASSERT(!d_out->areCongruent(fa, fb));
    TS_ASSERT(!d_cc->areCongruent(fa, fb));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(!d_cc->areCongruent(a, b));
  }

  void test_f_of_f_of_something() {
    d_cc->addTerm(ffa);
    d_cc->addTerm(ffb);

    d_cc->addEquality(a_eq_b);

    TS_ASSERT(d_out->areCongruent(ffa, ffb));
    TS_ASSERT(d_cc->areCongruent(ffa, ffb));

    TS_ASSERT(!d_out->areCongruent(fa, fb));
    TS_ASSERT(d_cc->areCongruent(fa, fb));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(d_cc->areCongruent(a, b));
  }

  void test_f4_of_something() {
    d_cc->addTerm(ffffa);
    d_cc->addTerm(ffffb);

    d_cc->addEquality(a_eq_b);

    TS_ASSERT(d_out->areCongruent(ffffa, ffffb));
    TS_ASSERT(d_cc->areCongruent(ffffa, ffffb));

    TS_ASSERT(!d_out->areCongruent(fffa, fffb));
    TS_ASSERT(d_cc->areCongruent(fffa, fffb));

    TS_ASSERT(!d_out->areCongruent(ffa, ffb));
    TS_ASSERT(d_cc->areCongruent(ffa, ffb));

    TS_ASSERT(!d_out->areCongruent(fa, fb));
    TS_ASSERT(d_cc->areCongruent(fa, fb));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(d_cc->areCongruent(a, b));
  }

  void testSimpleBinaryFunction() {
    d_cc->addTerm(gab);
    d_cc->addTerm(gba);

    d_cc->addEquality(a_eq_b);

    TS_ASSERT(d_out->areCongruent(gab, gba));
    TS_ASSERT(d_cc->areCongruent(gab, gba));
  }

  void testSimpleBinaryFunction2() {

    //Debug.on("cc");
    try {

    d_cc->addTerm(gfafb);
    d_cc->addTerm(gba);
    d_cc->addTerm(gfaa);
    d_cc->addTerm(hfaa);

    d_cc->addEquality(a_eq_fb);
    d_cc->addEquality(fa_eq_b);

    TS_ASSERT(d_cc->areCongruent(a, fb));
    TS_ASSERT(d_cc->areCongruent(b, fa));
    TS_ASSERT(d_cc->areCongruent(fb, ffa));

    Debug("cc") << "\n\n\n"
                << "a norm:     " << d_cc->normalize(a) << std::endl
                << "fb norm:    " << d_cc->normalize(fb) << std::endl
                << "b norm:     " << d_cc->normalize(b) << std::endl
                << "fa norm:    " << d_cc->normalize(fa) << std::endl
                << "ffa norm:   " << d_cc->normalize(ffa) << std::endl
                << "ffffa norm  " << d_cc->normalize(ffffa) << std::endl
                << "ffffb norm  " << d_cc->normalize(ffffb) << std::endl
                << "gba norm:   " << d_cc->normalize(gba) << std::endl
                << "gfaa norm:  " << d_cc->normalize(gfaa) << std::endl
                << "gbfb norm:  " << d_cc->normalize(gbfb) << std::endl
                << "gfafb norm: " << d_cc->normalize(gfafb) << std::endl
                << "hab norm:   " << d_cc->normalize(hab) << std::endl
                << "hba norm:   " << d_cc->normalize(hba) << std::endl
                << "hfaa norm:  " << d_cc->normalize(hfaa) << std::endl;

    TS_ASSERT(d_out->areCongruent(gfafb, gba));
    TS_ASSERT(d_cc->areCongruent(b, fa));
    TS_ASSERT(d_cc->areCongruent(gfafb, gba));
    TS_ASSERT(d_cc->areCongruent(hba, hba));
    TS_ASSERT(d_cc->areCongruent(hfaa, hba));
    TS_ASSERT(d_out->areCongruent(gfaa, gba));
    TS_ASSERT(d_cc->areCongruent(gfaa, gba));

    } catch(Exception& e) {
      cout << "\n\n" << e << "\n\n";
      throw;
    }
  }

  void testUF() {
    //Debug.on("cc");
    try{
    Node c_0 = d_nm->mkVar("c_0", U);
    Node c_1 = d_nm->mkVar("c_1", U);
    Node c_2 = d_nm->mkVar("c_2", U);
    Node c2 = d_nm->mkVar("c2", U);
    Node c3 = d_nm->mkVar("c3", U);
    Node c4 = d_nm->mkVar("c4", U);
    Node c5 = d_nm->mkVar("c5", U);
    Node c6 = d_nm->mkVar("c6", U);
    Node c7 = d_nm->mkVar("c7", U);
    Node c8 = d_nm->mkVar("c8", U);
    Node c9 = d_nm->mkVar("c9", U);
    vector<TypeNode> args2U(2, U);
    Node f1 = d_nm->mkVar("f1", d_nm->mkFunctionType(args2U, U));

    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::APPLY_UF, f1,d_nm->mkNode(kind::APPLY_UF, f1,c_0,c_0),c_0),d_nm->mkNode(kind::APPLY_UF, f1,c_0,d_nm->mkNode(kind::APPLY_UF, f1,c_0,c_0))));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::APPLY_UF, f1,d_nm->mkNode(kind::APPLY_UF, f1,c_0,c_0),c_2),d_nm->mkNode(kind::APPLY_UF, f1,c_0,d_nm->mkNode(kind::APPLY_UF, f1,c_0,c_2))));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::APPLY_UF, f1,d_nm->mkNode(kind::APPLY_UF, f1,c_0,c_1),c_1),d_nm->mkNode(kind::APPLY_UF, f1,c_0,d_nm->mkNode(kind::APPLY_UF, f1,c_1,c_1))));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::APPLY_UF, f1,d_nm->mkNode(kind::APPLY_UF, f1,c_0,c_1),c_2),d_nm->mkNode(kind::APPLY_UF, f1,c_0,d_nm->mkNode(kind::APPLY_UF, f1,c_1,c_2))));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::APPLY_UF, f1,d_nm->mkNode(kind::APPLY_UF, f1,c_2,c_1),c_2),d_nm->mkNode(kind::APPLY_UF, f1,c_2,d_nm->mkNode(kind::APPLY_UF, f1,c_1,c_2))));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::APPLY_UF, f1,d_nm->mkNode(kind::APPLY_UF, f1,c_2,c_2),c_0),d_nm->mkNode(kind::APPLY_UF, f1,c_2,d_nm->mkNode(kind::APPLY_UF, f1,c_2,c_0))));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::APPLY_UF, f1,d_nm->mkNode(kind::APPLY_UF, f1,c_2,c_2),c_1),d_nm->mkNode(kind::APPLY_UF, f1,c_2,d_nm->mkNode(kind::APPLY_UF, f1,c_2,c_1))));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::APPLY_UF, f1,c_0,d_nm->mkNode(kind::APPLY_UF, f1,c_2,d_nm->mkNode(kind::APPLY_UF, f1,c_2,d_nm->mkNode(kind::APPLY_UF, f1,c_2,c_0)))),d_nm->mkNode(kind::APPLY_UF, f1,c_2,d_nm->mkNode(kind::APPLY_UF, f1,c_0,d_nm->mkNode(kind::APPLY_UF, f1,c_2,d_nm->mkNode(kind::APPLY_UF, f1,c_0,c_2))))));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::APPLY_UF, f1,c2,c8),d_nm->mkNode(kind::APPLY_UF, f1,c4,c9)));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, c9,c_0));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, c8,c_0));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, c4,c_0));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, c2,c_0));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, c5,c_0));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, c7,c_0));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, c3,c_0));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, c6,c_1));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::APPLY_UF, f1,c_2,c_2),c_0));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::APPLY_UF, f1,c_2,c_1),c_0));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::APPLY_UF, f1,c_2,c_0),c_0));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::APPLY_UF, f1,c_1,c_2),c_0));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::APPLY_UF, f1,c_1,c_1),c_0));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::APPLY_UF, f1,c_1,c_0),c_1));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::APPLY_UF, f1,c_0,c_1),c_0));
    d_cc->addEquality(d_nm->mkNode(kind::EQUAL, d_nm->mkNode(kind::APPLY_UF, f1,c_0,c_0),c_0));
    } catch(Exception& e) {
      cout << "\n\n" << e << "\n\n";
      throw e;
    }
  }

  void testUF2() {
    Node f = d_nm->mkVar("f", d_nm->mkFunctionType(U, U));
    Node x = d_nm->mkVar("x", U);
    Node y = d_nm->mkVar("y", U);
    Node z = d_nm->mkVar("z", U);
    Node ffx = d_nm->mkNode(kind::APPLY_UF, f, d_nm->mkNode(kind::APPLY_UF, f, x));
    Node fffx = d_nm->mkNode(kind::APPLY_UF, f, ffx);
    Node ffffx = d_nm->mkNode(kind::APPLY_UF, f, fffx);
    Node ffx_eq_fffx = ffx.eqNode(fffx);
    Node ffx_eq_y = ffx.eqNode(y);
    Node ffffx_eq_z = ffffx.eqNode(z);

    d_cc->addEquality(ffx_eq_fffx);
    d_cc->addEquality(ffx_eq_y);
    d_cc->addEquality(ffffx_eq_z);
  }

  void testSimpleArray() {
    //Debug.on("cc");
    // add terms, then add equalities
    try {
    d_ccArray->addTerm(ar_a);
    d_ccArray->addTerm(ar_b);

    d_ccArray->addEquality(a_eq_b);

    TS_ASSERT(d_out->areCongruent(ar_a, ar_b));
    TS_ASSERT(d_ccArray->areCongruent(ar_a, ar_b));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(d_ccArray->areCongruent(a, b));
    } catch(Exception& e) {
      cout << "\n\n" << e << "\n\n";
      throw;
    }
  }

  void testSimpleReverseArray() {
    // add equalities, then add terms; should get the same as
    // testSimple()

    d_ccArray->addEquality(a_eq_b);

    d_ccArray->addTerm(ar_a);
    d_ccArray->addTerm(ar_b);

    TS_ASSERT(d_out->areCongruent(ar_a, ar_b));
    TS_ASSERT(d_ccArray->areCongruent(ar_a, ar_b));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(d_ccArray->areCongruent(a, b));
  }

  void testArray() {
    Node ar_eq_arar_a = d_nm->mkNode(kind::EQUAL, ar, arar_a);
    Node ar2 = d_nm->mkVar("ar2", d_nm->mkArrayType(U, U));
    Node store_arar_b_ar2 = d_nm->mkNode(kind::STORE, arar, b, ar2);
    Node select__store_arar_b_ar2__a =
      d_nm->mkNode(kind::SELECT, store_arar_b_ar2, a);
    Node select__store_arar_b_ar2__a__eq__arar_a =
      d_nm->mkNode(kind::EQUAL, select__store_arar_b_ar2__a, arar_a);

    d_ccArray->addTerm(ar);
    d_ccArray->addTerm(select__store_arar_b_ar2__a);

    d_ccArray->addEquality(ar_eq_arar_a);
    d_ccArray->addEquality(select__store_arar_b_ar2__a__eq__arar_a);

    TS_ASSERT(d_ccArray->areCongruent(ar, select__store_arar_b_ar2__a));
    TS_ASSERT(d_out->areCongruent(ar, select__store_arar_b_ar2__a));
  }

};/* class CongruenceClosureWhite */
