/*********************                                                        */
/*! \file datatype_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Datatype
 **
 ** Black box testing of CVC4::Datatype.
 **/

#include <cxxtest/TestSuite.h>
#include <sstream>

#include "expr/datatype.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "expr/expr_manager_scope.h"
#include "expr/type_node.h"

using namespace CVC4;
using namespace std;

class DatatypeBlack : public CxxTest::TestSuite {

  ExprManager* d_em;
  ExprManagerScope* d_scope;

 public:
  void setUp() override
  {
    d_em = new ExprManager();
    d_scope = new ExprManagerScope(*d_em);
    Debug.on("datatypes");
    Debug.on("groundterms");
  }

  void tearDown() override
  {
    delete d_scope;
    delete d_em;
  }

  void testEnumeration() {
    Datatype colors(d_em, "colors");

    DatatypeConstructor yellow("yellow");
    DatatypeConstructor blue("blue");
    DatatypeConstructor green("green");
    DatatypeConstructor red("red");

    colors.addConstructor(yellow);
    colors.addConstructor(blue);
    colors.addConstructor(green);
    colors.addConstructor(red);

    Debug("datatypes") << colors << std::endl;
    DatatypeType colorsType = d_em->mkDatatypeType(colors);
    Debug("datatypes") << colorsType << std::endl;

    Expr ctor = colorsType.getDatatype()[1].getConstructor();
    Expr apply = d_em->mkExpr(kind::APPLY_CONSTRUCTOR, ctor);
    Debug("datatypes") << apply << std::endl;

    const Datatype& colorsDT = colorsType.getDatatype();
    TS_ASSERT(colorsDT.getConstructor("blue") == ctor);
    TS_ASSERT(colorsDT["blue"].getConstructor() == ctor);
    TS_ASSERT_THROWS(colorsDT["blue"].getSelector("foo"),
                     IllegalArgumentException&);
    TS_ASSERT_THROWS(colorsDT["blue"]["foo"], IllegalArgumentException&);

    TS_ASSERT(! colorsType.getDatatype().isParametric());
    TS_ASSERT(colorsType.getDatatype().isFinite());
    TS_ASSERT(colorsType.getDatatype().getCardinality().compare(4) == Cardinality::EQUAL);
    TS_ASSERT(ctor.getType().getCardinality().compare(1) == Cardinality::EQUAL);
    TS_ASSERT(colorsType.getDatatype().isWellFounded());
    Debug("groundterms") << "ground term of " << colorsType.getDatatype().getName() << endl
                         << "  is " << colorsType.mkGroundTerm() << endl;
    TS_ASSERT(colorsType.mkGroundTerm().getType() == colorsType);
  }

  void testNat() {
    Datatype nat(d_em, "nat");

    DatatypeConstructor succ("succ");
    succ.addArg("pred", DatatypeSelfType());
    nat.addConstructor(succ);

    DatatypeConstructor zero("zero");
    nat.addConstructor(zero);

    Debug("datatypes") << nat << std::endl;
    DatatypeType natType = d_em->mkDatatypeType(nat);
    Debug("datatypes") << natType << std::endl;

    Expr ctor = natType.getDatatype()[1].getConstructor();
    Expr apply = d_em->mkExpr(kind::APPLY_CONSTRUCTOR, ctor);
    Debug("datatypes") << apply << std::endl;

    TS_ASSERT(! natType.getDatatype().isParametric());
    TS_ASSERT(! natType.getDatatype().isFinite());
    TS_ASSERT(natType.getDatatype().getCardinality().compare(Cardinality::INTEGERS) == Cardinality::EQUAL);
    TS_ASSERT(natType.getDatatype().isWellFounded());
    Debug("groundterms") << "ground term of " << natType.getDatatype().getName() << endl
                         << "  is " << natType.mkGroundTerm() << endl;
    TS_ASSERT(natType.mkGroundTerm().getType() == natType);
  }

  void testTree() {
    Datatype tree(d_em, "tree");
    Type integerType = d_em->integerType();

    DatatypeConstructor node("node");
    node.addArg("left", DatatypeSelfType());
    node.addArg("right", DatatypeSelfType());
    tree.addConstructor(node);

    DatatypeConstructor leaf("leaf");
    leaf.addArg("leaf", integerType);
    tree.addConstructor(leaf);

    Debug("datatypes") << tree << std::endl;
    DatatypeType treeType = d_em->mkDatatypeType(tree);
    Debug("datatypes") << treeType << std::endl;

    Expr ctor = treeType.getDatatype()[1].getConstructor();
    TS_ASSERT(treeType.getConstructor("leaf") == ctor);
    TS_ASSERT(treeType.getConstructor("leaf") == ctor);
    TS_ASSERT_THROWS(treeType.getConstructor("leff"),
                     IllegalArgumentException&);

    TS_ASSERT(! treeType.getDatatype().isParametric());
    TS_ASSERT(! treeType.getDatatype().isFinite());
    TS_ASSERT(treeType.getDatatype().getCardinality().compare(Cardinality::INTEGERS) == Cardinality::EQUAL);
    TS_ASSERT(treeType.getDatatype().isWellFounded());
    Debug("groundterms") << "ground term of " << treeType.getDatatype().getName() << endl
                         << "  is " << treeType.mkGroundTerm() << endl;
    TS_ASSERT(treeType.mkGroundTerm().getType() == treeType);
  }

  void testListInt() {
    Datatype list(d_em, "list");
    Type integerType = d_em->integerType();

    DatatypeConstructor cons("cons");
    cons.addArg("car", integerType);
    cons.addArg("cdr", DatatypeSelfType());
    list.addConstructor(cons);

    DatatypeConstructor nil("nil");
    list.addConstructor(nil);

    Debug("datatypes") << list << std::endl;
    DatatypeType listType = d_em->mkDatatypeType(list);
    Debug("datatypes") << listType << std::endl;

    TS_ASSERT(! listType.getDatatype().isParametric());
    TS_ASSERT(! listType.getDatatype().isFinite());
    TS_ASSERT(listType.getDatatype().getCardinality().compare(Cardinality::INTEGERS) == Cardinality::EQUAL);
    TS_ASSERT(listType.getDatatype().isWellFounded());
    Debug("groundterms") << "ground term of " << listType.getDatatype().getName() << endl
                         << "  is " << listType.mkGroundTerm() << endl;
    TS_ASSERT(listType.mkGroundTerm().getType() == listType);
  }

  void testListReal() {
    Datatype list(d_em, "list");
    Type realType = d_em->realType();

    DatatypeConstructor cons("cons");
    cons.addArg("car", realType);
    cons.addArg("cdr", DatatypeSelfType());
    list.addConstructor(cons);

    DatatypeConstructor nil("nil");
    list.addConstructor(nil);

    Debug("datatypes") << list << std::endl;
    DatatypeType listType = d_em->mkDatatypeType(list);
    Debug("datatypes") << listType << std::endl;

    TS_ASSERT(! listType.getDatatype().isParametric());
    TS_ASSERT(! listType.getDatatype().isFinite());
    TS_ASSERT(listType.getDatatype().getCardinality().compare(Cardinality::REALS) == Cardinality::EQUAL);
    TS_ASSERT(listType.getDatatype().isWellFounded());
    Debug("groundterms") << "ground term of " << listType.getDatatype().getName() << endl
                         << "  is " << listType.mkGroundTerm() << endl;
    TS_ASSERT(listType.mkGroundTerm().getType() == listType);
  }

  void testListBoolean() {
    Datatype list(d_em, "list");
    Type booleanType = d_em->booleanType();

    DatatypeConstructor cons("cons");
    cons.addArg("car", booleanType);
    cons.addArg("cdr", DatatypeSelfType());
    list.addConstructor(cons);

    DatatypeConstructor nil("nil");
    list.addConstructor(nil);

    Debug("datatypes") << list << std::endl;
    DatatypeType listType = d_em->mkDatatypeType(list);
    Debug("datatypes") << listType << std::endl;

    TS_ASSERT(! listType.getDatatype().isFinite());
    TS_ASSERT(listType.getDatatype().getCardinality().compare(Cardinality::INTEGERS) == Cardinality::EQUAL);
    TS_ASSERT(listType.getDatatype().isWellFounded());
    Debug("groundterms") << "ground term of " << listType.getDatatype().getName() << endl
                         << "  is " << listType.mkGroundTerm() << endl;
    TS_ASSERT(listType.mkGroundTerm().getType() == listType);
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
    Datatype tree(d_em, "tree");
    DatatypeConstructor node("node");
    node.addArg("left", DatatypeSelfType());
    node.addArg("right", DatatypeSelfType());
    tree.addConstructor(node);

    DatatypeConstructor leaf("leaf");
    leaf.addArg("leaf", DatatypeUnresolvedType("list"));
    tree.addConstructor(leaf);

    Debug("datatypes") << tree << std::endl;

    Datatype list(d_em, "list");
    DatatypeConstructor cons("cons");
    cons.addArg("car", DatatypeUnresolvedType("tree"));
    cons.addArg("cdr", DatatypeSelfType());
    list.addConstructor(cons);

    DatatypeConstructor nil("nil");
    list.addConstructor(nil);

    Debug("datatypes") << list << std::endl;

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

    TS_ASSERT(! dtts[0].getDatatype().isFinite());
    TS_ASSERT(dtts[0].getDatatype().getCardinality().compare(Cardinality::INTEGERS) == Cardinality::EQUAL);
    TS_ASSERT(dtts[0].getDatatype().isWellFounded());
    Debug("groundterms") << "ground term of " << dtts[0].getDatatype().getName() << endl
                         << "  is " << dtts[0].mkGroundTerm() << endl;
    TS_ASSERT(dtts[0].mkGroundTerm().getType() == dtts[0]);

    TS_ASSERT(! dtts[1].getDatatype().isFinite());
    TS_ASSERT(dtts[1].getDatatype().getCardinality().compare(Cardinality::INTEGERS) == Cardinality::EQUAL);
    TS_ASSERT(dtts[1].getDatatype().isWellFounded());
    Debug("groundterms") << "ground term of " << dtts[1].getDatatype().getName() << endl
                         << "  is " << dtts[1].mkGroundTerm() << endl;
    TS_ASSERT(dtts[1].mkGroundTerm().getType() == dtts[1]);
  }
  void testMutualListTrees2()
  {
    Datatype tree(d_em, "tree");
    DatatypeConstructor node("node");
    node.addArg("left", DatatypeSelfType());
    node.addArg("right", DatatypeSelfType());
    tree.addConstructor(node);

    DatatypeConstructor leaf("leaf");
    leaf.addArg("leaf", DatatypeUnresolvedType("list"));
    tree.addConstructor(leaf);

    Datatype list(d_em, "list");
    DatatypeConstructor cons("cons");
    cons.addArg("car", DatatypeUnresolvedType("tree"));
    cons.addArg("cdr", DatatypeSelfType());
    list.addConstructor(cons);

    DatatypeConstructor nil("nil");
    list.addConstructor(nil);

    // add another constructor to list datatype resulting in an
    // "otherNil-list"
    DatatypeConstructor otherNil("otherNil");
    list.addConstructor(otherNil);

    vector<Datatype> dts;
    dts.push_back(tree);
    dts.push_back(list);
    // remake the types
    vector<DatatypeType> dtts2 = d_em->mkMutualDatatypeTypes(dts);

    TS_ASSERT(! dtts2[0].getDatatype().isFinite());
    TS_ASSERT(dtts2[0].getDatatype().getCardinality().compare(Cardinality::INTEGERS) == Cardinality::EQUAL);
    TS_ASSERT(dtts2[0].getDatatype().isWellFounded());
    Debug("groundterms") << "ground term of " << dtts2[0].getDatatype().getName() << endl
                         << "  is " << dtts2[0].mkGroundTerm() << endl;
    TS_ASSERT(dtts2[0].mkGroundTerm().getType() == dtts2[0]);

    TS_ASSERT(! dtts2[1].getDatatype().isParametric());
    TS_ASSERT(! dtts2[1].getDatatype().isFinite());
    TS_ASSERT(dtts2[1].getDatatype().getCardinality().compare(Cardinality::INTEGERS) == Cardinality::EQUAL);
    TS_ASSERT(dtts2[1].getDatatype().isWellFounded());
    Debug("groundterms") << "ground term of " << dtts2[1].getDatatype().getName() << endl
                         << "  is " << dtts2[1].mkGroundTerm() << endl;
    TS_ASSERT(dtts2[1].mkGroundTerm().getType() == dtts2[1]);
  }

  void testNotSoWellFounded() {
    Datatype tree(d_em, "tree");

    DatatypeConstructor node("node");
    node.addArg("left", DatatypeSelfType());
    node.addArg("right", DatatypeSelfType());
    tree.addConstructor(node);

    Debug("datatypes") << tree << std::endl;
    DatatypeType treeType = d_em->mkDatatypeType(tree);
    Debug("datatypes") << treeType << std::endl;

    TS_ASSERT(! treeType.getDatatype().isParametric());
    TS_ASSERT(! treeType.getDatatype().isFinite());
    TS_ASSERT(treeType.getDatatype().getCardinality().compare(Cardinality::INTEGERS) == Cardinality::EQUAL);
    TS_ASSERT(! treeType.getDatatype().isWellFounded());
    TS_ASSERT_THROWS_ANYTHING( treeType.mkGroundTerm() );
    TS_ASSERT_THROWS_ANYTHING( treeType.getDatatype().mkGroundTerm( treeType ) );
  }

  void testParametricDatatype() {
    vector<Type> v;
    Type t1, t2;
    v.push_back(t1 = d_em->mkSort("T1"));
    v.push_back(t2 = d_em->mkSort("T2"));
    Datatype pair(d_em, "pair", v);

    DatatypeConstructor mkpair("mk-pair");
    mkpair.addArg("first", t1);
    mkpair.addArg("second", t2);
    pair.addConstructor(mkpair);
    DatatypeType pairType = d_em->mkDatatypeType(pair);

    TS_ASSERT(pairType.getDatatype().isParametric());
    v.clear();
    v.push_back(d_em->integerType());
    v.push_back(d_em->integerType());
    DatatypeType pairIntInt = pairType.getDatatype().getDatatypeType(v);
    v.clear();
    v.push_back(d_em->realType());
    v.push_back(d_em->realType());
    DatatypeType pairRealReal = pairType.getDatatype().getDatatypeType(v);
    v.clear();
    v.push_back(d_em->realType());
    v.push_back(d_em->integerType());
    DatatypeType pairRealInt = pairType.getDatatype().getDatatypeType(v);
    v.clear();
    v.push_back(d_em->integerType());
    v.push_back(d_em->realType());
    DatatypeType pairIntReal = pairType.getDatatype().getDatatypeType(v);

    TS_ASSERT_DIFFERS(pairIntInt, pairRealReal);
    TS_ASSERT_DIFFERS(pairIntReal, pairRealReal);
    TS_ASSERT_DIFFERS(pairRealInt, pairRealReal);
    TS_ASSERT_DIFFERS(pairIntInt, pairIntReal);
    TS_ASSERT_DIFFERS(pairIntInt, pairRealInt);
    TS_ASSERT_DIFFERS(pairIntReal, pairRealInt);

    TS_ASSERT(pairRealReal.isComparableTo(pairRealReal));
    TS_ASSERT(!pairIntReal.isComparableTo(pairRealReal));
    TS_ASSERT(!pairRealInt.isComparableTo(pairRealReal));
    TS_ASSERT(!pairIntInt.isComparableTo(pairRealReal));
    TS_ASSERT(!pairRealReal.isComparableTo(pairRealInt));
    TS_ASSERT(!pairIntReal.isComparableTo(pairRealInt));
    TS_ASSERT(pairRealInt.isComparableTo(pairRealInt));
    TS_ASSERT(!pairIntInt.isComparableTo(pairRealInt));
    TS_ASSERT(!pairRealReal.isComparableTo(pairIntReal));
    TS_ASSERT(pairIntReal.isComparableTo(pairIntReal));
    TS_ASSERT(!pairRealInt.isComparableTo(pairIntReal));
    TS_ASSERT(!pairIntInt.isComparableTo(pairIntReal));
    TS_ASSERT(!pairRealReal.isComparableTo(pairIntInt));
    TS_ASSERT(!pairIntReal.isComparableTo(pairIntInt));
    TS_ASSERT(!pairRealInt.isComparableTo(pairIntInt));
    TS_ASSERT(pairIntInt.isComparableTo(pairIntInt));

    TS_ASSERT(pairRealReal.isSubtypeOf(pairRealReal));
    TS_ASSERT(!pairIntReal.isSubtypeOf(pairRealReal));
    TS_ASSERT(!pairRealInt.isSubtypeOf(pairRealReal));
    TS_ASSERT(!pairIntInt.isSubtypeOf(pairRealReal));
    TS_ASSERT(!pairRealReal.isSubtypeOf(pairRealInt));
    TS_ASSERT(!pairIntReal.isSubtypeOf(pairRealInt));
    TS_ASSERT(pairRealInt.isSubtypeOf(pairRealInt));
    TS_ASSERT(!pairIntInt.isSubtypeOf(pairRealInt));
    TS_ASSERT(!pairRealReal.isSubtypeOf(pairIntReal));
    TS_ASSERT(pairIntReal.isSubtypeOf(pairIntReal));
    TS_ASSERT(!pairRealInt.isSubtypeOf(pairIntReal));
    TS_ASSERT(!pairIntInt.isSubtypeOf(pairIntReal));
    TS_ASSERT(!pairRealReal.isSubtypeOf(pairIntInt));
    TS_ASSERT(!pairIntReal.isSubtypeOf(pairIntInt));
    TS_ASSERT(!pairRealInt.isSubtypeOf(pairIntInt));
    TS_ASSERT(pairIntInt.isSubtypeOf(pairIntInt));

    TS_ASSERT_EQUALS(TypeNode::leastCommonTypeNode(TypeNode::fromType(pairRealReal), TypeNode::fromType(pairRealReal)).toType(), pairRealReal);
    TS_ASSERT(TypeNode::leastCommonTypeNode(TypeNode::fromType(pairIntReal), TypeNode::fromType(pairRealReal)).isNull());
    TS_ASSERT(TypeNode::leastCommonTypeNode(TypeNode::fromType(pairRealInt), TypeNode::fromType(pairRealReal)).isNull());
    TS_ASSERT(TypeNode::leastCommonTypeNode(TypeNode::fromType(pairIntInt), TypeNode::fromType(pairRealReal)).isNull());
    TS_ASSERT(TypeNode::leastCommonTypeNode(TypeNode::fromType(pairRealReal), TypeNode::fromType(pairRealInt)).isNull());
    TS_ASSERT(TypeNode::leastCommonTypeNode(TypeNode::fromType(pairIntReal), TypeNode::fromType(pairRealInt)).isNull());
    TS_ASSERT_EQUALS(TypeNode::leastCommonTypeNode(TypeNode::fromType(pairRealInt), TypeNode::fromType(pairRealInt)).toType(), pairRealInt);
    TS_ASSERT(TypeNode::leastCommonTypeNode(TypeNode::fromType(pairIntInt), TypeNode::fromType(pairRealInt)).isNull());
    TS_ASSERT(TypeNode::leastCommonTypeNode(TypeNode::fromType(pairRealReal), TypeNode::fromType(pairIntReal)).isNull());
    TS_ASSERT_EQUALS(TypeNode::leastCommonTypeNode(TypeNode::fromType(pairIntReal), TypeNode::fromType(pairIntReal)).toType(), pairIntReal);
    TS_ASSERT(TypeNode::leastCommonTypeNode(TypeNode::fromType(pairRealInt), TypeNode::fromType(pairIntReal)).isNull());
    TS_ASSERT(TypeNode::leastCommonTypeNode(TypeNode::fromType(pairIntInt), TypeNode::fromType(pairIntReal)).isNull());
    TS_ASSERT(TypeNode::leastCommonTypeNode(TypeNode::fromType(pairRealReal), TypeNode::fromType(pairIntInt)).isNull());
    TS_ASSERT(TypeNode::leastCommonTypeNode(TypeNode::fromType(pairIntReal), TypeNode::fromType(pairIntInt)).isNull());
    TS_ASSERT(TypeNode::leastCommonTypeNode(TypeNode::fromType(pairRealInt), TypeNode::fromType(pairIntInt)).isNull());
    TS_ASSERT_EQUALS(TypeNode::leastCommonTypeNode(TypeNode::fromType(pairIntInt), TypeNode::fromType(pairIntInt)).toType(), pairIntInt);
  }

};/* class DatatypeBlack */
