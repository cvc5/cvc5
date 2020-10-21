/*********************                                                        */
/*! \file datatype_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::DType
 **
 ** Black box testing of CVC4::DType.
 **/

#include <cxxtest/TestSuite.h>

#include <sstream>

#include "api/cvc4cpp.h"
#include "expr/dtype.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "expr/expr_manager_scope.h"
#include "expr/type_node.h"

using namespace CVC4;
using namespace std;

class DatatypeBlack : public CxxTest::TestSuite {
 public:
  void setUp() override
  {
    d_slv = new api::Solver();
    d_nm = d_slv->getNodeManager();
    d_scope = new NodeManagerScope(d_nm);
    Debug.on("datatypes");
    Debug.on("groundterms");
  }

  void tearDown() override
  {
    delete d_scope;
    delete d_slv;
  }

  void testEnumeration() {
    DType colors("colors");

    std::shared_ptr<DTypeConstructor> yellow =
        std::make_shared<DTypeConstructor>("yellow");
    std::shared_ptr<DTypeConstructor> blue =
        std::make_shared<DTypeConstructor>("blue");
    std::shared_ptr<DTypeConstructor> green =
        std::make_shared<DTypeConstructor>("green");
    std::shared_ptr<DTypeConstructor> red =
        std::make_shared<DTypeConstructor>("red");

    colors.addConstructor(yellow);
    colors.addConstructor(blue);
    colors.addConstructor(green);
    colors.addConstructor(red);

    Debug("datatypes") << colors << std::endl;
    TypeNode colorsType = d_nm->mkDatatypeType(colors);
    Debug("datatypes") << colorsType << std::endl;

    Node ctor = colorsType.getDType()[1].getConstructor();
    Node apply = d_nm->mkNode(kind::APPLY_CONSTRUCTOR, ctor);
    Debug("datatypes") << apply << std::endl;

    TS_ASSERT(!colorsType.getDType().isParametric());
    TS_ASSERT(colorsType.getDType().isFinite());
    TS_ASSERT(colorsType.getDType().getCardinality().compare(4)
              == Cardinality::EQUAL);
    TS_ASSERT(ctor.getType().getCardinality().compare(1) == Cardinality::EQUAL);
    TS_ASSERT(colorsType.getDType().isWellFounded());
    Debug("groundterms") << "ground term of " << colorsType.getDType().getName()
                         << endl
                         << "  is " << colorsType.mkGroundTerm() << endl;
    TS_ASSERT(colorsType.mkGroundTerm().getType() == colorsType);
  }

  void testNat() {
    DType nat("nat");

    std::shared_ptr<DTypeConstructor> succ =
        std::make_shared<DTypeConstructor>("succ");
    succ->addArgSelf("pred");
    nat.addConstructor(succ);

    std::shared_ptr<DTypeConstructor> zero =
        std::make_shared<DTypeConstructor>("zero");
    nat.addConstructor(zero);

    Debug("datatypes") << nat << std::endl;
    TypeNode natType = d_nm->mkDatatypeType(nat);
    Debug("datatypes") << natType << std::endl;

    Node ctor = natType.getDType()[1].getConstructor();
    Node apply = d_nm->mkNode(kind::APPLY_CONSTRUCTOR, ctor);
    Debug("datatypes") << apply << std::endl;

    TS_ASSERT(!natType.getDType().isParametric());
    TS_ASSERT(!natType.getDType().isFinite());
    TS_ASSERT(natType.getDType().getCardinality().compare(Cardinality::INTEGERS)
              == Cardinality::EQUAL);
    TS_ASSERT(natType.getDType().isWellFounded());
    Debug("groundterms") << "ground term of " << natType.getDType().getName()
                         << endl
                         << "  is " << natType.mkGroundTerm() << endl;
    TS_ASSERT(natType.mkGroundTerm().getType() == natType);
  }

  void testTree() {
    DType tree("tree");
    TypeNode integerType = d_nm->integerType();

    std::shared_ptr<DTypeConstructor> node =
        std::make_shared<DTypeConstructor>("node");
    node->addArgSelf("left");
    node->addArgSelf("right");
    tree.addConstructor(node);

    std::shared_ptr<DTypeConstructor> leaf =
        std::make_shared<DTypeConstructor>("leaf");
    leaf->addArg("leaf", integerType);
    tree.addConstructor(leaf);

    Debug("datatypes") << tree << std::endl;
    TypeNode treeType = d_nm->mkDatatypeType(tree);
    Debug("datatypes") << treeType << std::endl;

    TS_ASSERT(!treeType.getDType().isParametric());
    TS_ASSERT(!treeType.getDType().isFinite());
    TS_ASSERT(
        treeType.getDType().getCardinality().compare(Cardinality::INTEGERS)
        == Cardinality::EQUAL);
    TS_ASSERT(treeType.getDType().isWellFounded());
    Debug("groundterms") << "ground term of " << treeType.getDType().getName()
                         << endl
                         << "  is " << treeType.mkGroundTerm() << endl;
    TS_ASSERT(treeType.mkGroundTerm().getType() == treeType);
  }

  void testListInt() {
    DType list("list");
    TypeNode integerType = d_nm->integerType();

    std::shared_ptr<DTypeConstructor> cons =
        std::make_shared<DTypeConstructor>("cons");
    cons->addArg("car", integerType);
    cons->addArgSelf("cdr");
    list.addConstructor(cons);

    std::shared_ptr<DTypeConstructor> nil =
        std::make_shared<DTypeConstructor>("nil");
    list.addConstructor(nil);

    Debug("datatypes") << list << std::endl;
    TypeNode listType = d_nm->mkDatatypeType(list);
    Debug("datatypes") << listType << std::endl;

    TS_ASSERT(!listType.getDType().isParametric());
    TS_ASSERT(!listType.getDType().isFinite());
    TS_ASSERT(
        listType.getDType().getCardinality().compare(Cardinality::INTEGERS)
        == Cardinality::EQUAL);
    TS_ASSERT(listType.getDType().isWellFounded());
    Debug("groundterms") << "ground term of " << listType.getDType().getName()
                         << endl
                         << "  is " << listType.mkGroundTerm() << endl;
    TS_ASSERT(listType.mkGroundTerm().getType() == listType);
  }

  void testListReal() {
    DType list("list");
    TypeNode realType = d_nm->realType();

    std::shared_ptr<DTypeConstructor> cons =
        std::make_shared<DTypeConstructor>("cons");
    cons->addArg("car", realType);
    cons->addArgSelf("cdr");
    list.addConstructor(cons);

    std::shared_ptr<DTypeConstructor> nil =
        std::make_shared<DTypeConstructor>("nil");
    list.addConstructor(nil);

    Debug("datatypes") << list << std::endl;
    TypeNode listType = d_nm->mkDatatypeType(list);
    Debug("datatypes") << listType << std::endl;

    TS_ASSERT(!listType.getDType().isParametric());
    TS_ASSERT(!listType.getDType().isFinite());
    TS_ASSERT(listType.getDType().getCardinality().compare(Cardinality::REALS)
              == Cardinality::EQUAL);
    TS_ASSERT(listType.getDType().isWellFounded());
    Debug("groundterms") << "ground term of " << listType.getDType().getName()
                         << endl
                         << "  is " << listType.mkGroundTerm() << endl;
    TS_ASSERT(listType.mkGroundTerm().getType() == listType);
  }

  void testListBoolean() {
    DType list("list");
    TypeNode booleanType = d_nm->booleanType();

    std::shared_ptr<DTypeConstructor> cons =
        std::make_shared<DTypeConstructor>("cons");
    cons->addArg("car", booleanType);
    cons->addArgSelf("cdr");
    list.addConstructor(cons);

    std::shared_ptr<DTypeConstructor> nil =
        std::make_shared<DTypeConstructor>("nil");
    list.addConstructor(nil);

    Debug("datatypes") << list << std::endl;
    TypeNode listType = d_nm->mkDatatypeType(list);
    Debug("datatypes") << listType << std::endl;

    TS_ASSERT(!listType.getDType().isFinite());
    TS_ASSERT(
        listType.getDType().getCardinality().compare(Cardinality::INTEGERS)
        == Cardinality::EQUAL);
    TS_ASSERT(listType.getDType().isWellFounded());
    Debug("groundterms") << "ground term of " << listType.getDType().getName()
                         << endl
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
    std::set<TypeNode> unresolvedTypes;
    TypeNode unresList =
        d_nm->mkSort("list", ExprManager::SORT_FLAG_PLACEHOLDER);
    unresolvedTypes.insert(unresList);
    TypeNode unresTree =
        d_nm->mkSort("tree", ExprManager::SORT_FLAG_PLACEHOLDER);
    unresolvedTypes.insert(unresTree);

    DType tree("tree");
    std::shared_ptr<DTypeConstructor> node =
        std::make_shared<DTypeConstructor>("node");
    node->addArgSelf("left");
    node->addArgSelf("right");
    tree.addConstructor(node);

    std::shared_ptr<DTypeConstructor> leaf =
        std::make_shared<DTypeConstructor>("leaf");
    leaf->addArg("leaf", unresList);
    tree.addConstructor(leaf);

    Debug("datatypes") << tree << std::endl;

    DType list("list");
    std::shared_ptr<DTypeConstructor> cons =
        std::make_shared<DTypeConstructor>("cons");
    cons->addArg("car", unresTree);
    cons->addArgSelf("cdr");
    list.addConstructor(cons);

    std::shared_ptr<DTypeConstructor> nil =
        std::make_shared<DTypeConstructor>("nil");
    list.addConstructor(nil);

    Debug("datatypes") << list << std::endl;

    TS_ASSERT(! tree.isResolved());
    TS_ASSERT(! list.isResolved());

    vector<DType> dts;
    dts.push_back(tree);
    dts.push_back(list);
    vector<TypeNode> dtts = d_nm->mkMutualDatatypeTypes(dts, unresolvedTypes);

    TS_ASSERT(dtts[0].getDType().isResolved());
    TS_ASSERT(dtts[1].getDType().isResolved());

    TS_ASSERT(!dtts[0].getDType().isFinite());
    TS_ASSERT(dtts[0].getDType().getCardinality().compare(Cardinality::INTEGERS)
              == Cardinality::EQUAL);
    TS_ASSERT(dtts[0].getDType().isWellFounded());
    Debug("groundterms") << "ground term of " << dtts[0].getDType().getName()
                         << endl
                         << "  is " << dtts[0].mkGroundTerm() << endl;
    TS_ASSERT(dtts[0].mkGroundTerm().getType() == dtts[0]);

    TS_ASSERT(!dtts[1].getDType().isFinite());
    TS_ASSERT(dtts[1].getDType().getCardinality().compare(Cardinality::INTEGERS)
              == Cardinality::EQUAL);
    TS_ASSERT(dtts[1].getDType().isWellFounded());
    Debug("groundterms") << "ground term of " << dtts[1].getDType().getName()
                         << endl
                         << "  is " << dtts[1].mkGroundTerm() << endl;
    TS_ASSERT(dtts[1].mkGroundTerm().getType() == dtts[1]);
  }
  void testMutualListTrees2()
  {
    std::set<TypeNode> unresolvedTypes;
    TypeNode unresList =
        d_nm->mkSort("list", ExprManager::SORT_FLAG_PLACEHOLDER);
    unresolvedTypes.insert(unresList);
    TypeNode unresTree =
        d_nm->mkSort("tree", ExprManager::SORT_FLAG_PLACEHOLDER);
    unresolvedTypes.insert(unresTree);

    DType tree("tree");
    std::shared_ptr<DTypeConstructor> node =
        std::make_shared<DTypeConstructor>("node");
    node->addArgSelf("left");
    node->addArgSelf("right");
    tree.addConstructor(node);

    std::shared_ptr<DTypeConstructor> leaf =
        std::make_shared<DTypeConstructor>("leaf");
    leaf->addArg("leaf", unresList);
    tree.addConstructor(leaf);

    DType list("list");
    std::shared_ptr<DTypeConstructor> cons =
        std::make_shared<DTypeConstructor>("cons");
    cons->addArg("car", unresTree);
    cons->addArgSelf("cdr");
    list.addConstructor(cons);

    std::shared_ptr<DTypeConstructor> nil =
        std::make_shared<DTypeConstructor>("nil");
    list.addConstructor(nil);

    // add another constructor to list datatype resulting in an
    // "otherNil-list"
    std::shared_ptr<DTypeConstructor> otherNil =
        std::make_shared<DTypeConstructor>("otherNil");
    list.addConstructor(otherNil);

    vector<DType> dts;
    dts.push_back(tree);
    dts.push_back(list);
    // remake the types
    vector<TypeNode> dtts2 = d_nm->mkMutualDatatypeTypes(dts, unresolvedTypes);

    TS_ASSERT(!dtts2[0].getDType().isFinite());
    TS_ASSERT(
        dtts2[0].getDType().getCardinality().compare(Cardinality::INTEGERS)
        == Cardinality::EQUAL);
    TS_ASSERT(dtts2[0].getDType().isWellFounded());
    Debug("groundterms") << "ground term of " << dtts2[0].getDType().getName()
                         << endl
                         << "  is " << dtts2[0].mkGroundTerm() << endl;
    TS_ASSERT(dtts2[0].mkGroundTerm().getType() == dtts2[0]);

    TS_ASSERT(!dtts2[1].getDType().isParametric());
    TS_ASSERT(!dtts2[1].getDType().isFinite());
    TS_ASSERT(
        dtts2[1].getDType().getCardinality().compare(Cardinality::INTEGERS)
        == Cardinality::EQUAL);
    TS_ASSERT(dtts2[1].getDType().isWellFounded());
    Debug("groundterms") << "ground term of " << dtts2[1].getDType().getName()
                         << endl
                         << "  is " << dtts2[1].mkGroundTerm() << endl;
    TS_ASSERT(dtts2[1].mkGroundTerm().getType() == dtts2[1]);
  }

  void testNotSoWellFounded() {
    DType tree("tree");

    std::shared_ptr<DTypeConstructor> node =
        std::make_shared<DTypeConstructor>("node");
    node->addArgSelf("left");
    node->addArgSelf("right");
    tree.addConstructor(node);

    Debug("datatypes") << tree << std::endl;
    TypeNode treeType = d_nm->mkDatatypeType(tree);
    Debug("datatypes") << treeType << std::endl;

    TS_ASSERT(!treeType.getDType().isParametric());
    TS_ASSERT(!treeType.getDType().isFinite());
    TS_ASSERT(
        treeType.getDType().getCardinality().compare(Cardinality::INTEGERS)
        == Cardinality::EQUAL);
    TS_ASSERT(!treeType.getDType().isWellFounded());
    TS_ASSERT(treeType.mkGroundTerm().isNull());
    TS_ASSERT(treeType.getDType().mkGroundTerm(treeType).isNull());
  }

  void testParametricDType()
  {
    vector<TypeNode> v;
    TypeNode t1, t2;
    v.push_back(t1 = d_nm->mkSort("T1"));
    v.push_back(t2 = d_nm->mkSort("T2"));
    DType pair("pair", v);

    std::shared_ptr<DTypeConstructor> mkpair =
        std::make_shared<DTypeConstructor>("mk-pair");
    mkpair->addArg("first", t1);
    mkpair->addArg("second", t2);
    pair.addConstructor(mkpair);
    TypeNode pairType = d_nm->mkDatatypeType(pair);

    TS_ASSERT(pairType.getDType().isParametric());
    v.clear();
    v.push_back(d_nm->integerType());
    v.push_back(d_nm->integerType());
    TypeNode pairIntInt = pairType.getDType().getTypeNode(v);
    v.clear();
    v.push_back(d_nm->realType());
    v.push_back(d_nm->realType());
    TypeNode pairRealReal = pairType.getDType().getTypeNode(v);
    v.clear();
    v.push_back(d_nm->realType());
    v.push_back(d_nm->integerType());
    TypeNode pairRealInt = pairType.getDType().getTypeNode(v);
    v.clear();
    v.push_back(d_nm->integerType());
    v.push_back(d_nm->realType());
    TypeNode pairIntReal = pairType.getDType().getTypeNode(v);

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

    TS_ASSERT_EQUALS(TypeNode::leastCommonTypeNode(pairRealReal, pairRealReal),
                     pairRealReal);
    TS_ASSERT(
        TypeNode::leastCommonTypeNode(pairIntReal, pairRealReal).isNull());
    TS_ASSERT(
        TypeNode::leastCommonTypeNode(pairRealInt, pairRealReal).isNull());
    TS_ASSERT(TypeNode::leastCommonTypeNode(pairIntInt, pairRealReal).isNull());
    TS_ASSERT(
        TypeNode::leastCommonTypeNode(pairRealReal, pairRealInt).isNull());
    TS_ASSERT(TypeNode::leastCommonTypeNode(pairIntReal, pairRealInt).isNull());
    TS_ASSERT_EQUALS(TypeNode::leastCommonTypeNode(pairRealInt, pairRealInt),
                     pairRealInt);
    TS_ASSERT(TypeNode::leastCommonTypeNode(pairIntInt, pairRealInt).isNull());
    TS_ASSERT(
        TypeNode::leastCommonTypeNode(pairRealReal, pairIntReal).isNull());
    TS_ASSERT_EQUALS(TypeNode::leastCommonTypeNode(pairIntReal, pairIntReal),
                     pairIntReal);
    TS_ASSERT(TypeNode::leastCommonTypeNode(pairRealInt, pairIntReal).isNull());
    TS_ASSERT(TypeNode::leastCommonTypeNode(pairIntInt, pairIntReal).isNull());
    TS_ASSERT(TypeNode::leastCommonTypeNode(pairRealReal, pairIntInt).isNull());
    TS_ASSERT(TypeNode::leastCommonTypeNode(pairIntReal, pairIntInt).isNull());
    TS_ASSERT(TypeNode::leastCommonTypeNode(pairRealInt, pairIntInt).isNull());
    TS_ASSERT_EQUALS(TypeNode::leastCommonTypeNode(pairIntInt, pairIntInt),
                     pairIntInt);
  }

 private:
  api::Solver* d_slv;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;
}; /* class DTypeBlack */
