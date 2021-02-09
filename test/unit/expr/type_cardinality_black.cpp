/*********************                                                        */
/*! \file type_cardinality_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Public box testing of Type::getCardinality() for various Types
 **
 ** Public box testing of Type::getCardinality() for various Types.
 **/

#include <string>

#include "expr/expr_manager.h"
#include "expr/kind.h"
#include "expr/node_manager.h"
#include "expr/type.h"
#include "test_api.h"
#include "util/cardinality.h"

namespace CVC4 {

using namespace kind;

namespace test {

class TestTypeCardinalityBlack : public TestApi
{
 protected:
  void SetUp() override
  {
    TestApi::SetUp();
    d_em = d_solver.getExprManager();
    d_nm = d_solver.getNodeManager();
  }
  ExprManager* d_em;
  NodeManager* d_nm;
};

TEST_F(TestTypeCardinalityBlack, basics)
{
  ASSERT_EQ(d_em->booleanType().getCardinality().compare(2),
            Cardinality::EQUAL);
  ASSERT_EQ(d_em->integerType().getCardinality().compare(Cardinality::INTEGERS),
            Cardinality::EQUAL);
  ASSERT_EQ(d_em->realType().getCardinality().compare(Cardinality::REALS),
            Cardinality::EQUAL);
}

TEST_F(TestTypeCardinalityBlack, arrays)
{
  Type intToInt = d_em->mkArrayType(d_em->integerType(), d_em->integerType());
  Type realToReal = d_em->mkArrayType(d_em->realType(), d_em->realType());
  Type realToInt = d_em->mkArrayType(d_em->realType(), d_em->integerType());
  Type intToReal = d_em->mkArrayType(d_em->integerType(), d_em->realType());
  Type intToBool = d_em->mkArrayType(d_em->integerType(), d_em->booleanType());
  Type realToBool = d_em->mkArrayType(d_em->realType(), d_em->booleanType());
  Type boolToReal = d_em->mkArrayType(d_em->booleanType(), d_em->realType());
  Type boolToInt = d_em->mkArrayType(d_em->booleanType(), d_em->integerType());
  Type boolToBool = d_em->mkArrayType(d_em->booleanType(), d_em->booleanType());

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

TEST_F(TestTypeCardinalityBlack, unary_functions)
{
  Type intToInt =
      d_em->mkFunctionType(d_em->integerType(), d_em->integerType());
  Type realToReal = d_em->mkFunctionType(d_em->realType(), d_em->realType());
  Type realToInt = d_em->mkFunctionType(d_em->realType(), d_em->integerType());
  Type intToReal = d_em->mkFunctionType(d_em->integerType(), d_em->realType());
  Type intToBool =
      d_em->mkFunctionType(d_em->integerType(), d_em->booleanType());
  Type realToBool = d_em->mkFunctionType(d_em->realType(), d_em->booleanType());
  Type boolToReal = d_em->mkFunctionType(d_em->booleanType(), d_em->realType());
  Type boolToInt =
      d_em->mkFunctionType(d_em->booleanType(), d_em->integerType());
  Type boolToBool =
      d_em->mkFunctionType(d_em->booleanType(), d_em->booleanType());

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

TEST_F(TestTypeCardinalityBlack, binary_functions)
{
  std::vector<Type> boolbool;
  boolbool.push_back(d_em->booleanType());
  boolbool.push_back(d_em->booleanType());
  std::vector<Type> boolint;
  boolint.push_back(d_em->booleanType());
  boolint.push_back(d_em->integerType());
  std::vector<Type> intbool;
  intbool.push_back(d_em->integerType());
  intbool.push_back(d_em->booleanType());
  std::vector<Type> intint;
  intint.push_back(d_em->integerType());
  intint.push_back(d_em->integerType());
  std::vector<Type> intreal;
  intreal.push_back(d_em->integerType());
  intreal.push_back(d_em->realType());
  std::vector<Type> realint;
  realint.push_back(d_em->realType());
  realint.push_back(d_em->integerType());
  std::vector<Type> realreal;
  realreal.push_back(d_em->realType());
  realreal.push_back(d_em->realType());
  std::vector<Type> realbool;
  realbool.push_back(d_em->realType());
  realbool.push_back(d_em->booleanType());
  std::vector<Type> boolreal;
  boolreal.push_back(d_em->booleanType());
  boolreal.push_back(d_em->realType());

  Type boolboolToBool = d_em->mkFunctionType(boolbool, d_em->booleanType());
  Type boolboolToInt = d_em->mkFunctionType(boolbool, d_em->integerType());
  Type boolboolToReal = d_em->mkFunctionType(boolbool, d_em->realType());

  Type boolintToBool = d_em->mkFunctionType(boolint, d_em->booleanType());
  Type boolintToInt = d_em->mkFunctionType(boolint, d_em->integerType());
  Type boolintToReal = d_em->mkFunctionType(boolint, d_em->realType());

  Type intboolToBool = d_em->mkFunctionType(intbool, d_em->booleanType());
  Type intboolToInt = d_em->mkFunctionType(intbool, d_em->integerType());
  Type intboolToReal = d_em->mkFunctionType(intbool, d_em->realType());

  Type intintToBool = d_em->mkFunctionType(intint, d_em->booleanType());
  Type intintToInt = d_em->mkFunctionType(intint, d_em->integerType());
  Type intintToReal = d_em->mkFunctionType(intint, d_em->realType());

  Type intrealToBool = d_em->mkFunctionType(intreal, d_em->booleanType());
  Type intrealToInt = d_em->mkFunctionType(intreal, d_em->integerType());
  Type intrealToReal = d_em->mkFunctionType(intreal, d_em->realType());

  Type realintToBool = d_em->mkFunctionType(realint, d_em->booleanType());
  Type realintToInt = d_em->mkFunctionType(realint, d_em->integerType());
  Type realintToReal = d_em->mkFunctionType(realint, d_em->realType());

  Type realrealToBool = d_em->mkFunctionType(realreal, d_em->booleanType());
  Type realrealToInt = d_em->mkFunctionType(realreal, d_em->integerType());
  Type realrealToReal = d_em->mkFunctionType(realreal, d_em->realType());

  Type realboolToBool = d_em->mkFunctionType(realbool, d_em->booleanType());
  Type realboolToInt = d_em->mkFunctionType(realbool, d_em->integerType());
  Type realboolToReal = d_em->mkFunctionType(realbool, d_em->realType());

  Type boolrealToBool = d_em->mkFunctionType(boolreal, d_em->booleanType());
  Type boolrealToInt = d_em->mkFunctionType(boolreal, d_em->integerType());
  Type boolrealToReal = d_em->mkFunctionType(boolreal, d_em->realType());

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

TEST_F(TestTypeCardinalityBlack, ternary_functions)
{
  std::vector<TypeNode> boolbool;
  boolbool.push_back(d_nm->booleanType());
  boolbool.push_back(d_nm->booleanType());
  std::vector<TypeNode> boolboolbool = boolbool;
  boolboolbool.push_back(d_nm->booleanType());

  TypeNode boolboolTuple = d_nm->mkTupleType(boolbool);
  TypeNode boolboolboolTuple = d_nm->mkTupleType(boolboolbool);

  TypeNode boolboolboolToBool =
      d_nm->mkFunctionType(boolboolbool, d_nm->booleanType());
  TypeNode boolboolToBoolbool = d_nm->mkFunctionType(boolbool, boolboolTuple);
  TypeNode boolToBoolboolbool =
      d_nm->mkFunctionType(d_nm->booleanType(), boolboolboolTuple);

  ASSERT_EQ(boolboolboolToBool.getCardinality().compare(/* 2 ^ 8 */ 1 << 8),
            Cardinality::EQUAL);
  ASSERT_EQ(
      boolboolToBoolbool.getCardinality().compare(/* 4 ^ 4 */ 4 * 4 * 4 * 4),
      Cardinality::EQUAL);
  ASSERT_EQ(boolToBoolboolbool.getCardinality().compare(/* 8 ^ 2 */ 8 * 8),
            Cardinality::EQUAL);
}

TEST_F(TestTypeCardinalityBlack, undefined_sorts)
{
  Type foo = d_em->mkSort("foo", NodeManager::SORT_FLAG_NONE);
  // We've currently assigned them a specific Beth number, which
  // isn't really correct, but...
  ASSERT_FALSE(foo.getCardinality().isFinite());
}

TEST_F(TestTypeCardinalityBlack, bitvectors)
{
  ASSERT_EQ(d_em->mkBitVectorType(0).getCardinality().compare(0),
            Cardinality::EQUAL);
  Cardinality lastCard = 0;
  for (unsigned i = 1; i <= 65; ++i)
  {
    Cardinality card = Cardinality(2) ^ i;
    Cardinality typeCard = d_em->mkBitVectorType(i).getCardinality();
    ASSERT_TRUE(typeCard.compare(lastCard) == Cardinality::GREATER
                || (typeCard.isLargeFinite() && lastCard.isLargeFinite()));
    ASSERT_TRUE(typeCard.compare(card) == Cardinality::EQUAL
                || typeCard.isLargeFinite());
    lastCard = typeCard;
  }
}

}  // namespace test
}  // namespace CVC4
