/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of cvc5::theory::sets::SetsTypeEnumerator
 *
 * These tests depend on the ordering that the SetsTypeEnumerator use, so
 * it's a white-box test.
 */

#include "expr/dtype.h"
#include "test_smt.h"
#include "theory/sets/theory_sets_type_enumerator.h"

namespace cvc5::internal {

using namespace theory;
using namespace kind;
using namespace theory::sets;

namespace test {

class TestTheoryWhiteSetsTypeEnumerator : public TestSmt
{
 protected:
  void addAndCheckUnique(Node n, std::vector<Node>& elems)
  {
    ASSERT_TRUE(n.isConst());
    ASSERT_TRUE(std::find(elems.begin(), elems.end(), n) == elems.end());
    elems.push_back(n);
  }
};

TEST_F(TestTheoryWhiteSetsTypeEnumerator, set_of_booleans)
{
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  TypeNode boolType = d_nodeManager->booleanType();
  SetEnumerator setEnumerator(d_nodeManager->mkSetType(boolType));
  ASSERT_FALSE(setEnumerator.isFinished());

  std::vector<Node> elems;

  Node actual0 = *setEnumerator;
  addAndCheckUnique(actual0, elems);
  ASSERT_FALSE(setEnumerator.isFinished());

  Node actual1 = *++setEnumerator;
  addAndCheckUnique(actual1, elems);
  ASSERT_FALSE(setEnumerator.isFinished());

  Node actual2 = *++setEnumerator;
  addAndCheckUnique(actual2, elems);
  ASSERT_FALSE(setEnumerator.isFinished());

  Node actual3 = rr->rewrite(*++setEnumerator);
  addAndCheckUnique(actual3, elems);
  ASSERT_FALSE(setEnumerator.isFinished());

  ASSERT_THROW(*++setEnumerator, NoMoreValuesException);
  ASSERT_TRUE(setEnumerator.isFinished());
  ASSERT_THROW(*++setEnumerator, NoMoreValuesException);
  ASSERT_TRUE(setEnumerator.isFinished());
  ASSERT_THROW(*++setEnumerator, NoMoreValuesException);
  ASSERT_TRUE(setEnumerator.isFinished());
}

TEST_F(TestTheoryWhiteSetsTypeEnumerator, set_of_UF)
{
  TypeNode sort = d_nodeManager->mkSort("Atom");
  SetEnumerator setEnumerator(d_nodeManager->mkSetType(sort));

  Node actual0 = *setEnumerator;
  Node expected0 =
      d_nodeManager->mkConst(EmptySet(d_nodeManager->mkSetType(sort)));
  ASSERT_EQ(expected0, actual0);
  ASSERT_FALSE(setEnumerator.isFinished());

  std::vector<Node> elems;
  for (unsigned i = 0; i < 7; i++)
  {
    Node actual = *setEnumerator;
    addAndCheckUnique(actual, elems);
    ASSERT_FALSE(setEnumerator.isFinished());
    ++setEnumerator;
  }
}

TEST_F(TestTheoryWhiteSetsTypeEnumerator, set_of_finite_dataype)
{
  DType dt("Colors");
  dt.addConstructor(std::make_shared<DTypeConstructor>("red"));
  dt.addConstructor(std::make_shared<DTypeConstructor>("green"));
  dt.addConstructor(std::make_shared<DTypeConstructor>("blue"));
  TypeNode datatype = d_nodeManager->mkDatatypeType(dt);
  const std::vector<std::shared_ptr<DTypeConstructor> >& dtcons =
      datatype.getDType().getConstructors();
  SetEnumerator setEnumerator(d_nodeManager->mkSetType(datatype));

  Node red =
      d_nodeManager->mkNode(APPLY_CONSTRUCTOR, dtcons[0]->getConstructor());

  Node green =
      d_nodeManager->mkNode(APPLY_CONSTRUCTOR, dtcons[1]->getConstructor());

  Node blue =
      d_nodeManager->mkNode(APPLY_CONSTRUCTOR, dtcons[2]->getConstructor());

  std::vector<Node> elems;
  for (unsigned i = 0; i < 8; i++)
  {
    Node actual = *setEnumerator;
    addAndCheckUnique(actual, elems);
    ASSERT_FALSE(setEnumerator.isFinished());
    ++setEnumerator;
  }

  ASSERT_THROW(*++setEnumerator, NoMoreValuesException);
  ASSERT_TRUE(setEnumerator.isFinished());
  ASSERT_THROW(*++setEnumerator, NoMoreValuesException);
  ASSERT_TRUE(setEnumerator.isFinished());
  ASSERT_THROW(*++setEnumerator, NoMoreValuesException);
  ASSERT_TRUE(setEnumerator.isFinished());
}

TEST_F(TestTheoryWhiteSetsTypeEnumerator, bv)
{
  TypeNode bitVector2 = d_nodeManager->mkBitVectorType(2);
  SetEnumerator setEnumerator(d_nodeManager->mkSetType(bitVector2));

  std::vector<Node> elems;
  for (unsigned i = 0; i < 16; i++)
  {
    Node actual = *setEnumerator;
    addAndCheckUnique(actual, elems);
    ASSERT_FALSE(setEnumerator.isFinished());
    ++setEnumerator;
  }

  ASSERT_THROW(*++setEnumerator, NoMoreValuesException);
  ASSERT_TRUE(setEnumerator.isFinished());
  ASSERT_THROW(*++setEnumerator, NoMoreValuesException);
  ASSERT_TRUE(setEnumerator.isFinished());
  ASSERT_THROW(*++setEnumerator, NoMoreValuesException);
  ASSERT_TRUE(setEnumerator.isFinished());
}
}  // namespace test
}  // namespace cvc5::internal
