/*********************                                                        */
/*! \file datatype_black.h
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
 ** \brief Black box testing of CVC4::Datatype
 **
 ** Black box testing of CVC4::Datatype.
 **/

#include <cxxtest/TestSuite.h>
#include <sstream>

#include "util/datatype.h"

#include "expr/expr.h"
#include "expr/expr_manager.h"

using namespace CVC4;
using namespace std;

class DatatypeBlack : public CxxTest::TestSuite {

  ExprManager* d_em;

public:

  void setUp() {
    d_em = new ExprManager();
  }

  void tearDown() {
    delete d_em;
  }

  void testNat() {
    Datatype nat("nat");

    Datatype::Constructor succ("succ", "is_succ");
    succ.addArg("pred", Datatype::SelfType());
    nat.addConstructor(succ);

    Datatype::Constructor zero("zero", "is_zero");
    nat.addConstructor(zero);

    cout << nat << std::endl;
    DatatypeType natType = d_em->mkDatatypeType(nat);
    cout << natType << std::endl;

    Expr ctor = natType.getDatatype()[1].getConstructor();
    Expr apply = d_em->mkExpr(kind::APPLY_CONSTRUCTOR, ctor);
    cout << apply << std::endl;
  }

  void testTree() {
    Datatype tree("tree");
    Type integerType = d_em->integerType();

    Datatype::Constructor node("node", "is_node");
    node.addArg("left", Datatype::SelfType());
    node.addArg("right", Datatype::SelfType());
    tree.addConstructor(node);

    Datatype::Constructor leaf("leaf", "is_leaf");
    leaf.addArg("leaf", integerType);
    tree.addConstructor(leaf);

    cout << tree << std::endl;
    DatatypeType treeType = d_em->mkDatatypeType(tree);
    cout << treeType << std::endl;
  }

  void testList() {
    Datatype list("list");
    Type integerType = d_em->integerType();

    Datatype::Constructor cons("cons", "is_cons");
    cons.addArg("car", integerType);
    cons.addArg("cdr", Datatype::SelfType());
    list.addConstructor(cons);

    Datatype::Constructor nil("nil", "is_nil");
    list.addConstructor(nil);

    cout << list << std::endl;
    DatatypeType listType = d_em->mkDatatypeType(list);
    cout << listType << std::endl;
  }

  void testMutualListTrees() {
    /* Create two mutual datatypes corresponding to this definition
     * block:
     *
     *   DATATYPE
     *     tree = node(left: tree, right: tree) | leaf(list),
     *     list = cons(car: tree, cdr: list) | nil
     *   END;
     */
    Datatype tree("tree");
    Datatype::Constructor node("node", "is_node");
    node.addArg("left", Datatype::SelfType());
    node.addArg("right", Datatype::SelfType());
    tree.addConstructor(node);

    Datatype::Constructor leaf("leaf", "is_leaf");
    leaf.addArg("leaf", Datatype::UnresolvedType("list"));
    tree.addConstructor(leaf);

    cout << tree << std::endl;

    Datatype list("list");
    Datatype::Constructor cons("cons", "is_cons");
    cons.addArg("car", Datatype::UnresolvedType("tree"));
    cons.addArg("cdr", Datatype::SelfType());
    list.addConstructor(cons);

    Datatype::Constructor nil("nil", "is_nil");
    list.addConstructor(nil);

    cout << list << std::endl;

    TS_ASSERT(! tree.isResolved());
    TS_ASSERT(! node.isResolved());
    TS_ASSERT(! leaf.isResolved());
    TS_ASSERT(! list.isResolved());
    TS_ASSERT(! cons.isResolved());
    TS_ASSERT(! nil.isResolved());

    vector<Datatype> dts;
    dts.push_back(tree);
    dts.push_back(list);
    vector<DatatypeType> dtts = d_em->mkMutualDatatypeTypes(dts);

    TS_ASSERT(dtts[0].getDatatype().isResolved());
    TS_ASSERT(dtts[1].getDatatype().isResolved());

    // add another constructor to list datatype resulting in an
    // "otherNil-list"
    Datatype::Constructor otherNil("otherNil", "is_otherNil");
    dts[1].addConstructor(otherNil);

    // remake the types
    vector<DatatypeType> dtts2 = d_em->mkMutualDatatypeTypes(dts);

    TS_ASSERT_DIFFERS(dtts, dtts2);
    TS_ASSERT_DIFFERS(dtts[1], dtts2[1]);

    // tree is also different because it's a tree of otherNil-lists
    TS_ASSERT_DIFFERS(dtts[0], dtts2[0]);
  }

};/* class DatatypeBlack */
