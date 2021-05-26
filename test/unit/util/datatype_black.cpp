/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::DType.
 */

#include <sstream>

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/type_node.h"
#include "test_smt.h"
#include "util/rational.h"

namespace cvc5 {
namespace test {

class TestUtilBlackDatatype : public TestSmt
{
 public:
  void SetUp() override
  {
    TestSmt::SetUp();
    Debug.on("datatypes");
    Debug.on("groundterms");
  }
};

TEST_F(TestUtilBlackDatatype, enumeration)
{
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
  TypeNode colorsType = d_nodeManager->mkDatatypeType(colors);
  Debug("datatypes") << colorsType << std::endl;

  Node ctor = colorsType.getDType()[1].getConstructor();
  Node apply = d_nodeManager->mkNode(kind::APPLY_CONSTRUCTOR, ctor);
  Debug("datatypes") << apply << std::endl;

  ASSERT_FALSE(colorsType.getDType().isParametric());
  ASSERT_TRUE(colorsType.getDType().isFinite());
  ASSERT_EQ(colorsType.getDType().getCardinality().compare(4),
            Cardinality::EQUAL);
  ASSERT_EQ(ctor.getType().getCardinality().compare(1), Cardinality::EQUAL);
  ASSERT_TRUE(colorsType.getDType().isWellFounded());
  Debug("groundterms") << "ground term of " << colorsType.getDType().getName()
                       << std::endl
                       << "  is " << colorsType.mkGroundTerm() << std::endl;
  ASSERT_EQ(colorsType.mkGroundTerm().getType(), colorsType);
}

TEST_F(TestUtilBlackDatatype, nat)
{
  DType nat("nat");

  std::shared_ptr<DTypeConstructor> succ =
      std::make_shared<DTypeConstructor>("succ");
  succ->addArgSelf("pred");
  nat.addConstructor(succ);

  std::shared_ptr<DTypeConstructor> zero =
      std::make_shared<DTypeConstructor>("zero");
  nat.addConstructor(zero);

  Debug("datatypes") << nat << std::endl;
  TypeNode natType = d_nodeManager->mkDatatypeType(nat);
  Debug("datatypes") << natType << std::endl;

  Node ctor = natType.getDType()[1].getConstructor();
  Node apply = d_nodeManager->mkNode(kind::APPLY_CONSTRUCTOR, ctor);
  Debug("datatypes") << apply << std::endl;

  ASSERT_FALSE(natType.getDType().isParametric());
  ASSERT_FALSE(natType.getDType().isFinite());
  ASSERT_TRUE(natType.getDType().getCardinality().compare(Cardinality::INTEGERS)
              == Cardinality::EQUAL);
  ASSERT_TRUE(natType.getDType().isWellFounded());
  Debug("groundterms") << "ground term of " << natType.getDType().getName()
                       << std::endl
                       << "  is " << natType.mkGroundTerm() << std::endl;
  ASSERT_TRUE(natType.mkGroundTerm().getType() == natType);
}

TEST_F(TestUtilBlackDatatype, tree)
{
  DType tree("tree");
  TypeNode integerType = d_nodeManager->integerType();

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
  TypeNode treeType = d_nodeManager->mkDatatypeType(tree);
  Debug("datatypes") << treeType << std::endl;

  ASSERT_FALSE(treeType.getDType().isParametric());
  ASSERT_FALSE(treeType.getDType().isFinite());
  ASSERT_TRUE(
      treeType.getDType().getCardinality().compare(Cardinality::INTEGERS)
      == Cardinality::EQUAL);
  ASSERT_TRUE(treeType.getDType().isWellFounded());
  Debug("groundterms") << "ground term of " << treeType.getDType().getName()
                       << std::endl
                       << "  is " << treeType.mkGroundTerm() << std::endl;
  ASSERT_TRUE(treeType.mkGroundTerm().getType() == treeType);
}

TEST_F(TestUtilBlackDatatype, list_int)
{
  DType list("list");
  TypeNode integerType = d_nodeManager->integerType();

  std::shared_ptr<DTypeConstructor> cons =
      std::make_shared<DTypeConstructor>("cons");
  cons->addArg("car", integerType);
  cons->addArgSelf("cdr");
  list.addConstructor(cons);

  std::shared_ptr<DTypeConstructor> nil =
      std::make_shared<DTypeConstructor>("nil");
  list.addConstructor(nil);

  Debug("datatypes") << list << std::endl;
  TypeNode listType = d_nodeManager->mkDatatypeType(list);
  Debug("datatypes") << listType << std::endl;

  ASSERT_FALSE(listType.getDType().isParametric());
  ASSERT_FALSE(listType.getDType().isFinite());
  ASSERT_TRUE(
      listType.getDType().getCardinality().compare(Cardinality::INTEGERS)
      == Cardinality::EQUAL);
  ASSERT_TRUE(listType.getDType().isWellFounded());
  Debug("groundterms") << "ground term of " << listType.getDType().getName()
                       << std::endl
                       << "  is " << listType.mkGroundTerm() << std::endl;
  ASSERT_TRUE(listType.mkGroundTerm().getType() == listType);
}

TEST_F(TestUtilBlackDatatype, list_real)
{
  DType list("list");
  TypeNode realType = d_nodeManager->realType();

  std::shared_ptr<DTypeConstructor> cons =
      std::make_shared<DTypeConstructor>("cons");
  cons->addArg("car", realType);
  cons->addArgSelf("cdr");
  list.addConstructor(cons);

  std::shared_ptr<DTypeConstructor> nil =
      std::make_shared<DTypeConstructor>("nil");
  list.addConstructor(nil);

  Debug("datatypes") << list << std::endl;
  TypeNode listType = d_nodeManager->mkDatatypeType(list);
  Debug("datatypes") << listType << std::endl;

  ASSERT_FALSE(listType.getDType().isParametric());
  ASSERT_FALSE(listType.getDType().isFinite());
  ASSERT_TRUE(listType.getDType().getCardinality().compare(Cardinality::REALS)
              == Cardinality::EQUAL);
  ASSERT_TRUE(listType.getDType().isWellFounded());
  Debug("groundterms") << "ground term of " << listType.getDType().getName()
                       << std::endl
                       << "  is " << listType.mkGroundTerm() << std::endl;
  ASSERT_TRUE(listType.mkGroundTerm().getType() == listType);
}

TEST_F(TestUtilBlackDatatype, list_boolean)
{
  DType list("list");
  TypeNode booleanType = d_nodeManager->booleanType();

  std::shared_ptr<DTypeConstructor> cons =
      std::make_shared<DTypeConstructor>("cons");
  cons->addArg("car", booleanType);
  cons->addArgSelf("cdr");
  list.addConstructor(cons);

  std::shared_ptr<DTypeConstructor> nil =
      std::make_shared<DTypeConstructor>("nil");
  list.addConstructor(nil);

  Debug("datatypes") << list << std::endl;
  TypeNode listType = d_nodeManager->mkDatatypeType(list);
  Debug("datatypes") << listType << std::endl;

  ASSERT_FALSE(listType.getDType().isFinite());
  ASSERT_TRUE(
      listType.getDType().getCardinality().compare(Cardinality::INTEGERS)
      == Cardinality::EQUAL);
  ASSERT_TRUE(listType.getDType().isWellFounded());
  Debug("groundterms") << "ground term of " << listType.getDType().getName()
                       << std::endl
                       << "  is " << listType.mkGroundTerm() << std::endl;
  ASSERT_TRUE(listType.mkGroundTerm().getType() == listType);
}

TEST_F(TestUtilBlackDatatype, listIntUpdate)
{
  DType list("list");
  TypeNode integerType = d_nodeManager->integerType();

  std::shared_ptr<DTypeConstructor> cons =
      std::make_shared<DTypeConstructor>("cons");
  cons->addArg("car", integerType);
  cons->addArgSelf("cdr");
  list.addConstructor(cons);

  std::shared_ptr<DTypeConstructor> nil =
      std::make_shared<DTypeConstructor>("nil");
  list.addConstructor(nil);

  TypeNode listType = d_nodeManager->mkDatatypeType(list);
  const DType& ldt = listType.getDType();
  Node updater = ldt[0][0].getUpdater();
  Node gt = listType.mkGroundTerm();
  Node zero = d_nodeManager->mkConst(Rational(0));
  Node truen = d_nodeManager->mkConst(true);
  // construct an update term
  Node uterm = d_nodeManager->mkNode(kind::APPLY_UPDATER, updater, gt, zero);
  // construct a non well-formed update term
  ASSERT_THROW(d_nodeManager->mkNode(kind::APPLY_UPDATER, updater, gt, truen)
                   .getType(true),
               TypeCheckingExceptionPrivate);
}

TEST_F(TestUtilBlackDatatype, mutual_list_trees1)
{
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
      d_nodeManager->mkSort("list", NodeManager::SORT_FLAG_PLACEHOLDER);
  unresolvedTypes.insert(unresList);
  TypeNode unresTree =
      d_nodeManager->mkSort("tree", NodeManager::SORT_FLAG_PLACEHOLDER);
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

  ASSERT_FALSE(tree.isResolved());
  ASSERT_FALSE(list.isResolved());

  std::vector<DType> dts;
  dts.push_back(tree);
  dts.push_back(list);
  std::vector<TypeNode> dtts =
      d_nodeManager->mkMutualDatatypeTypes(dts, unresolvedTypes);

  ASSERT_TRUE(dtts[0].getDType().isResolved());
  ASSERT_TRUE(dtts[1].getDType().isResolved());

  ASSERT_FALSE(dtts[0].getDType().isFinite());
  ASSERT_TRUE(dtts[0].getDType().getCardinality().compare(Cardinality::INTEGERS)
              == Cardinality::EQUAL);
  ASSERT_TRUE(dtts[0].getDType().isWellFounded());
  Debug("groundterms") << "ground term of " << dtts[0].getDType().getName()
                       << std::endl
                       << "  is " << dtts[0].mkGroundTerm() << std::endl;
  ASSERT_TRUE(dtts[0].mkGroundTerm().getType() == dtts[0]);

  ASSERT_FALSE(dtts[1].getDType().isFinite());
  ASSERT_TRUE(dtts[1].getDType().getCardinality().compare(Cardinality::INTEGERS)
              == Cardinality::EQUAL);
  ASSERT_TRUE(dtts[1].getDType().isWellFounded());
  Debug("groundterms") << "ground term of " << dtts[1].getDType().getName()
                       << std::endl
                       << "  is " << dtts[1].mkGroundTerm() << std::endl;
  ASSERT_TRUE(dtts[1].mkGroundTerm().getType() == dtts[1]);
}

TEST_F(TestUtilBlackDatatype, mutual_list_trees2)
{
  std::set<TypeNode> unresolvedTypes;
  TypeNode unresList =
      d_nodeManager->mkSort("list", NodeManager::SORT_FLAG_PLACEHOLDER);
  unresolvedTypes.insert(unresList);
  TypeNode unresTree =
      d_nodeManager->mkSort("tree", NodeManager::SORT_FLAG_PLACEHOLDER);
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

  std::vector<DType> dts;
  dts.push_back(tree);
  dts.push_back(list);
  // remake the types
  std::vector<TypeNode> dtts2 =
      d_nodeManager->mkMutualDatatypeTypes(dts, unresolvedTypes);

  ASSERT_FALSE(dtts2[0].getDType().isFinite());
  ASSERT_TRUE(
      dtts2[0].getDType().getCardinality().compare(Cardinality::INTEGERS)
      == Cardinality::EQUAL);
  ASSERT_TRUE(dtts2[0].getDType().isWellFounded());
  Debug("groundterms") << "ground term of " << dtts2[0].getDType().getName()
                       << std::endl
                       << "  is " << dtts2[0].mkGroundTerm() << std::endl;
  ASSERT_TRUE(dtts2[0].mkGroundTerm().getType() == dtts2[0]);

  ASSERT_FALSE(dtts2[1].getDType().isParametric());
  ASSERT_FALSE(dtts2[1].getDType().isFinite());
  ASSERT_TRUE(
      dtts2[1].getDType().getCardinality().compare(Cardinality::INTEGERS)
      == Cardinality::EQUAL);
  ASSERT_TRUE(dtts2[1].getDType().isWellFounded());
  Debug("groundterms") << "ground term of " << dtts2[1].getDType().getName()
                       << std::endl
                       << "  is " << dtts2[1].mkGroundTerm() << std::endl;
  ASSERT_TRUE(dtts2[1].mkGroundTerm().getType() == dtts2[1]);
}

TEST_F(TestUtilBlackDatatype, not_so_well_founded)
{
  DType tree("tree");

  std::shared_ptr<DTypeConstructor> node =
      std::make_shared<DTypeConstructor>("node");
  node->addArgSelf("left");
  node->addArgSelf("right");
  tree.addConstructor(node);

  Debug("datatypes") << tree << std::endl;
  TypeNode treeType = d_nodeManager->mkDatatypeType(tree);
  Debug("datatypes") << treeType << std::endl;

  ASSERT_FALSE(treeType.getDType().isParametric());
  ASSERT_FALSE(treeType.getDType().isFinite());
  ASSERT_TRUE(
      treeType.getDType().getCardinality().compare(Cardinality::INTEGERS)
      == Cardinality::EQUAL);
  ASSERT_FALSE(treeType.getDType().isWellFounded());
  ASSERT_TRUE(treeType.mkGroundTerm().isNull());
  ASSERT_TRUE(treeType.getDType().mkGroundTerm(treeType).isNull());
}

TEST_F(TestUtilBlackDatatype, parametric_DType)
{
  std::vector<TypeNode> v;
  TypeNode t1, t2;
  v.push_back(t1 = d_nodeManager->mkSort("T1"));
  v.push_back(t2 = d_nodeManager->mkSort("T2"));
  DType pair("pair", v);

  std::shared_ptr<DTypeConstructor> mkpair =
      std::make_shared<DTypeConstructor>("mk-pair");
  mkpair->addArg("first", t1);
  mkpair->addArg("second", t2);
  pair.addConstructor(mkpair);
  TypeNode pairType = d_nodeManager->mkDatatypeType(pair);

  ASSERT_TRUE(pairType.getDType().isParametric());
  v.clear();
  v.push_back(d_nodeManager->integerType());
  v.push_back(d_nodeManager->integerType());
  TypeNode pairIntInt = pairType.getDType().getTypeNode(v);
  v.clear();
  v.push_back(d_nodeManager->realType());
  v.push_back(d_nodeManager->realType());
  TypeNode pairRealReal = pairType.getDType().getTypeNode(v);
  v.clear();
  v.push_back(d_nodeManager->realType());
  v.push_back(d_nodeManager->integerType());
  TypeNode pairRealInt = pairType.getDType().getTypeNode(v);
  v.clear();
  v.push_back(d_nodeManager->integerType());
  v.push_back(d_nodeManager->realType());
  TypeNode pairIntReal = pairType.getDType().getTypeNode(v);

  ASSERT_NE(pairIntInt, pairRealReal);
  ASSERT_NE(pairIntReal, pairRealReal);
  ASSERT_NE(pairRealInt, pairRealReal);
  ASSERT_NE(pairIntInt, pairIntReal);
  ASSERT_NE(pairIntInt, pairRealInt);
  ASSERT_NE(pairIntReal, pairRealInt);

  ASSERT_TRUE(pairRealReal.isComparableTo(pairRealReal));
  ASSERT_FALSE(pairIntReal.isComparableTo(pairRealReal));
  ASSERT_FALSE(pairRealInt.isComparableTo(pairRealReal));
  ASSERT_FALSE(pairIntInt.isComparableTo(pairRealReal));
  ASSERT_FALSE(pairRealReal.isComparableTo(pairRealInt));
  ASSERT_FALSE(pairIntReal.isComparableTo(pairRealInt));
  ASSERT_TRUE(pairRealInt.isComparableTo(pairRealInt));
  ASSERT_FALSE(pairIntInt.isComparableTo(pairRealInt));
  ASSERT_FALSE(pairRealReal.isComparableTo(pairIntReal));
  ASSERT_TRUE(pairIntReal.isComparableTo(pairIntReal));
  ASSERT_FALSE(pairRealInt.isComparableTo(pairIntReal));
  ASSERT_FALSE(pairIntInt.isComparableTo(pairIntReal));
  ASSERT_FALSE(pairRealReal.isComparableTo(pairIntInt));
  ASSERT_FALSE(pairIntReal.isComparableTo(pairIntInt));
  ASSERT_FALSE(pairRealInt.isComparableTo(pairIntInt));
  ASSERT_TRUE(pairIntInt.isComparableTo(pairIntInt));

  ASSERT_TRUE(pairRealReal.isSubtypeOf(pairRealReal));
  ASSERT_FALSE(pairIntReal.isSubtypeOf(pairRealReal));
  ASSERT_FALSE(pairRealInt.isSubtypeOf(pairRealReal));
  ASSERT_FALSE(pairIntInt.isSubtypeOf(pairRealReal));
  ASSERT_FALSE(pairRealReal.isSubtypeOf(pairRealInt));
  ASSERT_FALSE(pairIntReal.isSubtypeOf(pairRealInt));
  ASSERT_TRUE(pairRealInt.isSubtypeOf(pairRealInt));
  ASSERT_FALSE(pairIntInt.isSubtypeOf(pairRealInt));
  ASSERT_FALSE(pairRealReal.isSubtypeOf(pairIntReal));
  ASSERT_TRUE(pairIntReal.isSubtypeOf(pairIntReal));
  ASSERT_FALSE(pairRealInt.isSubtypeOf(pairIntReal));
  ASSERT_FALSE(pairIntInt.isSubtypeOf(pairIntReal));
  ASSERT_FALSE(pairRealReal.isSubtypeOf(pairIntInt));
  ASSERT_FALSE(pairIntReal.isSubtypeOf(pairIntInt));
  ASSERT_FALSE(pairRealInt.isSubtypeOf(pairIntInt));
  ASSERT_TRUE(pairIntInt.isSubtypeOf(pairIntInt));

  ASSERT_EQ(TypeNode::leastCommonTypeNode(pairRealReal, pairRealReal),
            pairRealReal);
  ASSERT_TRUE(
      TypeNode::leastCommonTypeNode(pairIntReal, pairRealReal).isNull());
  ASSERT_TRUE(
      TypeNode::leastCommonTypeNode(pairRealInt, pairRealReal).isNull());
  ASSERT_TRUE(TypeNode::leastCommonTypeNode(pairIntInt, pairRealReal).isNull());
  ASSERT_TRUE(
      TypeNode::leastCommonTypeNode(pairRealReal, pairRealInt).isNull());
  ASSERT_TRUE(TypeNode::leastCommonTypeNode(pairIntReal, pairRealInt).isNull());
  ASSERT_EQ(TypeNode::leastCommonTypeNode(pairRealInt, pairRealInt),
            pairRealInt);
  ASSERT_TRUE(TypeNode::leastCommonTypeNode(pairIntInt, pairRealInt).isNull());
  ASSERT_TRUE(
      TypeNode::leastCommonTypeNode(pairRealReal, pairIntReal).isNull());
  ASSERT_EQ(TypeNode::leastCommonTypeNode(pairIntReal, pairIntReal),
            pairIntReal);
  ASSERT_TRUE(TypeNode::leastCommonTypeNode(pairRealInt, pairIntReal).isNull());
  ASSERT_TRUE(TypeNode::leastCommonTypeNode(pairIntInt, pairIntReal).isNull());
  ASSERT_TRUE(TypeNode::leastCommonTypeNode(pairRealReal, pairIntInt).isNull());
  ASSERT_TRUE(TypeNode::leastCommonTypeNode(pairIntReal, pairIntInt).isNull());
  ASSERT_TRUE(TypeNode::leastCommonTypeNode(pairRealInt, pairIntInt).isNull());
  ASSERT_EQ(TypeNode::leastCommonTypeNode(pairIntInt, pairIntInt), pairIntInt);
}
}  // namespace test
}  // namespace cvc5
