/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters, Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Public box testing of Type::getCardinality() for various Types.
 */

#include <string>

#include "expr/kind.h"
#include "expr/node_manager.h"
#include "test_node.h"
#include "util/cardinality.h"

namespace cvc5::internal {

using namespace kind;

namespace test {

class TestNodeBlackTypeCardinality : public TestNode
{
};

TEST_F(TestNodeBlackTypeCardinality, basics)
{
  ASSERT_EQ(d_nodeManager->booleanType().getCardinality().compare(2),
            Cardinality::EQUAL);
  ASSERT_EQ(d_nodeManager->integerType().getCardinality().compare(
                Cardinality::INTEGERS),
            Cardinality::EQUAL);
  ASSERT_EQ(
      d_nodeManager->realType().getCardinality().compare(Cardinality::REALS),
      Cardinality::EQUAL);
}

TEST_F(TestNodeBlackTypeCardinality, arrays)
{
  TypeNode intToInt = d_nodeManager->mkArrayType(d_nodeManager->integerType(),
                                                 d_nodeManager->integerType());
  TypeNode realToReal = d_nodeManager->mkArrayType(d_nodeManager->realType(),
                                                   d_nodeManager->realType());
  TypeNode realToInt = d_nodeManager->mkArrayType(d_nodeManager->realType(),
                                                  d_nodeManager->integerType());
  TypeNode intToReal = d_nodeManager->mkArrayType(d_nodeManager->integerType(),
                                                  d_nodeManager->realType());
  TypeNode intToBool = d_nodeManager->mkArrayType(d_nodeManager->integerType(),
                                                  d_nodeManager->booleanType());
  TypeNode realToBool = d_nodeManager->mkArrayType(
      d_nodeManager->realType(), d_nodeManager->booleanType());
  TypeNode boolToReal = d_nodeManager->mkArrayType(d_nodeManager->booleanType(),
                                                   d_nodeManager->realType());
  TypeNode boolToInt = d_nodeManager->mkArrayType(d_nodeManager->booleanType(),
                                                  d_nodeManager->integerType());
  TypeNode boolToBool = d_nodeManager->mkArrayType(
      d_nodeManager->booleanType(), d_nodeManager->booleanType());

  ASSERT_EQ(intToInt.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);
  ASSERT_EQ(realToReal.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);
  ASSERT_EQ(realToInt.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);
  ASSERT_EQ(intToReal.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);
  ASSERT_EQ(intToBool.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);
  ASSERT_EQ(realToBool.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);
  ASSERT_EQ(boolToReal.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);
  ASSERT_EQ(boolToInt.getCardinality().compare(Cardinality::INTEGERS),
            Cardinality::EQUAL);
  ASSERT_EQ(boolToBool.getCardinality().compare(4), Cardinality::EQUAL);
}

TEST_F(TestNodeBlackTypeCardinality, unary_functions)
{
  TypeNode intToInt = d_nodeManager->mkFunctionType(
      d_nodeManager->integerType(), d_nodeManager->integerType());
  TypeNode realToReal = d_nodeManager->mkFunctionType(
      d_nodeManager->realType(), d_nodeManager->realType());
  TypeNode realToInt = d_nodeManager->mkFunctionType(
      d_nodeManager->realType(), d_nodeManager->integerType());
  TypeNode intToReal = d_nodeManager->mkFunctionType(
      d_nodeManager->integerType(), d_nodeManager->realType());
  TypeNode intToBool = d_nodeManager->mkFunctionType(
      d_nodeManager->integerType(), d_nodeManager->booleanType());
  TypeNode realToBool = d_nodeManager->mkFunctionType(
      d_nodeManager->realType(), d_nodeManager->booleanType());
  TypeNode boolToReal = d_nodeManager->mkFunctionType(
      d_nodeManager->booleanType(), d_nodeManager->realType());
  TypeNode boolToInt = d_nodeManager->mkFunctionType(
      d_nodeManager->booleanType(), d_nodeManager->integerType());
  TypeNode boolToBool = d_nodeManager->mkFunctionType(
      d_nodeManager->booleanType(), d_nodeManager->booleanType());

  ASSERT_EQ(intToInt.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);
  ASSERT_EQ(realToReal.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);
  ASSERT_EQ(realToInt.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);
  ASSERT_EQ(intToReal.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);
  ASSERT_EQ(intToBool.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);
  ASSERT_EQ(realToBool.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);
  ASSERT_EQ(boolToReal.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);
  ASSERT_EQ(boolToInt.getCardinality().compare(Cardinality::INTEGERS),
            Cardinality::EQUAL);
  ASSERT_EQ(boolToBool.getCardinality().compare(4), Cardinality::EQUAL);
}

TEST_F(TestNodeBlackTypeCardinality, binary_functions)
{
  std::vector<TypeNode> boolbool;
  boolbool.push_back(d_nodeManager->booleanType());
  boolbool.push_back(d_nodeManager->booleanType());
  std::vector<TypeNode> boolint;
  boolint.push_back(d_nodeManager->booleanType());
  boolint.push_back(d_nodeManager->integerType());
  std::vector<TypeNode> intbool;
  intbool.push_back(d_nodeManager->integerType());
  intbool.push_back(d_nodeManager->booleanType());
  std::vector<TypeNode> intint;
  intint.push_back(d_nodeManager->integerType());
  intint.push_back(d_nodeManager->integerType());
  std::vector<TypeNode> intreal;
  intreal.push_back(d_nodeManager->integerType());
  intreal.push_back(d_nodeManager->realType());
  std::vector<TypeNode> realint;
  realint.push_back(d_nodeManager->realType());
  realint.push_back(d_nodeManager->integerType());
  std::vector<TypeNode> realreal;
  realreal.push_back(d_nodeManager->realType());
  realreal.push_back(d_nodeManager->realType());
  std::vector<TypeNode> realbool;
  realbool.push_back(d_nodeManager->realType());
  realbool.push_back(d_nodeManager->booleanType());
  std::vector<TypeNode> boolreal;
  boolreal.push_back(d_nodeManager->booleanType());
  boolreal.push_back(d_nodeManager->realType());

  TypeNode boolboolToBool =
      d_nodeManager->mkFunctionType(boolbool, d_nodeManager->booleanType());
  TypeNode boolboolToInt =
      d_nodeManager->mkFunctionType(boolbool, d_nodeManager->integerType());
  TypeNode boolboolToReal =
      d_nodeManager->mkFunctionType(boolbool, d_nodeManager->realType());

  TypeNode boolintToBool =
      d_nodeManager->mkFunctionType(boolint, d_nodeManager->booleanType());
  TypeNode boolintToInt =
      d_nodeManager->mkFunctionType(boolint, d_nodeManager->integerType());
  TypeNode boolintToReal =
      d_nodeManager->mkFunctionType(boolint, d_nodeManager->realType());

  TypeNode intboolToBool =
      d_nodeManager->mkFunctionType(intbool, d_nodeManager->booleanType());
  TypeNode intboolToInt =
      d_nodeManager->mkFunctionType(intbool, d_nodeManager->integerType());
  TypeNode intboolToReal =
      d_nodeManager->mkFunctionType(intbool, d_nodeManager->realType());

  TypeNode intintToBool =
      d_nodeManager->mkFunctionType(intint, d_nodeManager->booleanType());
  TypeNode intintToInt =
      d_nodeManager->mkFunctionType(intint, d_nodeManager->integerType());
  TypeNode intintToReal =
      d_nodeManager->mkFunctionType(intint, d_nodeManager->realType());

  TypeNode intrealToBool =
      d_nodeManager->mkFunctionType(intreal, d_nodeManager->booleanType());
  TypeNode intrealToInt =
      d_nodeManager->mkFunctionType(intreal, d_nodeManager->integerType());
  TypeNode intrealToReal =
      d_nodeManager->mkFunctionType(intreal, d_nodeManager->realType());

  TypeNode realintToBool =
      d_nodeManager->mkFunctionType(realint, d_nodeManager->booleanType());
  TypeNode realintToInt =
      d_nodeManager->mkFunctionType(realint, d_nodeManager->integerType());
  TypeNode realintToReal =
      d_nodeManager->mkFunctionType(realint, d_nodeManager->realType());

  TypeNode realrealToBool =
      d_nodeManager->mkFunctionType(realreal, d_nodeManager->booleanType());
  TypeNode realrealToInt =
      d_nodeManager->mkFunctionType(realreal, d_nodeManager->integerType());
  TypeNode realrealToReal =
      d_nodeManager->mkFunctionType(realreal, d_nodeManager->realType());

  TypeNode realboolToBool =
      d_nodeManager->mkFunctionType(realbool, d_nodeManager->booleanType());
  TypeNode realboolToInt =
      d_nodeManager->mkFunctionType(realbool, d_nodeManager->integerType());
  TypeNode realboolToReal =
      d_nodeManager->mkFunctionType(realbool, d_nodeManager->realType());

  TypeNode boolrealToBool =
      d_nodeManager->mkFunctionType(boolreal, d_nodeManager->booleanType());
  TypeNode boolrealToInt =
      d_nodeManager->mkFunctionType(boolreal, d_nodeManager->integerType());
  TypeNode boolrealToReal =
      d_nodeManager->mkFunctionType(boolreal, d_nodeManager->realType());

  ASSERT_EQ(boolboolToBool.getCardinality().compare(16), Cardinality::EQUAL);
  ASSERT_EQ(boolboolToInt.getCardinality().compare(Cardinality::INTEGERS),
            Cardinality::EQUAL);
  ASSERT_EQ(boolboolToReal.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);

  ASSERT_EQ(boolintToBool.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);
  ASSERT_EQ(boolintToInt.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);
  ASSERT_EQ(boolintToReal.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);

  ASSERT_EQ(intboolToBool.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);
  ASSERT_EQ(intboolToInt.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);
  ASSERT_EQ(intboolToReal.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);

  ASSERT_EQ(intintToBool.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);
  ASSERT_EQ(intintToInt.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);
  ASSERT_EQ(intintToReal.getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);

  ASSERT_EQ(intrealToBool.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);
  ASSERT_EQ(intrealToInt.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);
  ASSERT_EQ(intrealToReal.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);

  ASSERT_EQ(realintToBool.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);
  ASSERT_EQ(realintToInt.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);
  ASSERT_EQ(realintToReal.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);

  ASSERT_EQ(realrealToBool.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);
  ASSERT_EQ(realrealToInt.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);
  ASSERT_EQ(realrealToReal.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);

  ASSERT_EQ(realboolToBool.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);
  ASSERT_EQ(realboolToInt.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);
  ASSERT_EQ(realboolToReal.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);

  ASSERT_EQ(boolrealToBool.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);
  ASSERT_EQ(boolrealToInt.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);
  ASSERT_EQ(boolrealToReal.getCardinality().compare(Cardinality::REALS),
            Cardinality::GREATER);
}

TEST_F(TestNodeBlackTypeCardinality, ternary_functions)
{
  std::vector<TypeNode> boolbool;
  boolbool.push_back(d_nodeManager->booleanType());
  boolbool.push_back(d_nodeManager->booleanType());
  std::vector<TypeNode> boolboolbool = boolbool;
  boolboolbool.push_back(d_nodeManager->booleanType());

  TypeNode boolboolTuple = d_nodeManager->mkTupleType(boolbool);
  TypeNode boolboolboolTuple = d_nodeManager->mkTupleType(boolboolbool);

  TypeNode boolboolboolToBool =
      d_nodeManager->mkFunctionType(boolboolbool, d_nodeManager->booleanType());
  TypeNode boolboolToBoolbool =
      d_nodeManager->mkFunctionType(boolbool, boolboolTuple);
  TypeNode boolToBoolboolbool = d_nodeManager->mkFunctionType(
      d_nodeManager->booleanType(), boolboolboolTuple);

  ASSERT_EQ(boolboolboolToBool.getCardinality().compare(/* 2 ^ 8 */ 1 << 8),
            Cardinality::EQUAL);
  ASSERT_EQ(
      boolboolToBoolbool.getCardinality().compare(/* 4 ^ 4 */ 4 * 4 * 4 * 4),
      Cardinality::EQUAL);
  ASSERT_EQ(boolToBoolboolbool.getCardinality().compare(/* 8 ^ 2 */ 8 * 8),
            Cardinality::EQUAL);
}

TEST_F(TestNodeBlackTypeCardinality, undefined_sorts)
{
  TypeNode foo = d_nodeManager->mkSort("foo");
  // We've currently assigned them a specific Beth number, which
  // isn't really correct, but...
  ASSERT_FALSE(foo.getCardinality().isFinite());
}

TEST_F(TestNodeBlackTypeCardinality, bitvectors)
{
  ASSERT_EQ(d_nodeManager->mkBitVectorType(0).getCardinality().compare(0),
            Cardinality::EQUAL);
  Cardinality lastCard = 0;
  for (unsigned i = 1; i <= 65; ++i)
  {
    Cardinality card = Cardinality(2) ^ i;
    Cardinality typeCard = d_nodeManager->mkBitVectorType(i).getCardinality();
    ASSERT_TRUE(typeCard.compare(lastCard) == Cardinality::GREATER
                || (typeCard.isLargeFinite() && lastCard.isLargeFinite()));
    ASSERT_TRUE(typeCard.compare(card) == Cardinality::EQUAL
                || typeCard.isLargeFinite());
    lastCard = typeCard;
  }
}

TEST_F(TestNodeBlackTypeCardinality, lessThan)
{
  ASSERT_FALSE(d_nodeManager->booleanType().isCardinalityLessThan(2));
  ASSERT_TRUE(d_nodeManager->booleanType().isCardinalityLessThan(3));
  ASSERT_FALSE(d_nodeManager->mkBitVectorType(1).isCardinalityLessThan(2));
  ASSERT_TRUE(d_nodeManager->mkBitVectorType(1).isCardinalityLessThan(3));
  ASSERT_FALSE(d_nodeManager->mkBitVectorType(8).isCardinalityLessThan(256));
  ASSERT_TRUE(d_nodeManager->mkBitVectorType(8).isCardinalityLessThan(257));
  ASSERT_FALSE(
      d_nodeManager->mkFloatingPointType(3, 5).isCardinalityLessThan(229));
  ASSERT_TRUE(
      d_nodeManager->mkFloatingPointType(3, 5).isCardinalityLessThan(230));
  ASSERT_FALSE(d_nodeManager->roundingModeType().isCardinalityLessThan(5));
  ASSERT_TRUE(d_nodeManager->roundingModeType().isCardinalityLessThan(6));
  ASSERT_FALSE(
      d_nodeManager->mkFiniteFieldType(11).isCardinalityLessThan(11));
  ASSERT_TRUE(d_nodeManager->mkFiniteFieldType(11).isCardinalityLessThan(13));
}
}  // namespace test
}  // namespace cvc5::internal
