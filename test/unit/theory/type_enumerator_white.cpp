/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of cvc5::theory::TypeEnumerator.
 *
 * These tests depend on the ordering that the TypeEnumerators use, so it's a
 * white-box test.
 */

#include <unordered_set>

#include "expr/array_store_all.h"
#include "expr/dtype.h"
#include "expr/kind.h"
#include "expr/type_node.h"
#include "options/language.h"
#include "test_smt.h"
#include "theory/type_enumerator.h"
#include "util/bitvector.h"
#include "util/rational.h"
#include "util/uninterpreted_sort_value.h"

namespace cvc5::internal {

using namespace theory;
using namespace kind;

namespace test {

class TestTheoryWhiteTypeEnumerator : public TestSmt
{
};

TEST_F(TestTheoryWhiteTypeEnumerator, booleans)
{
  TypeEnumerator te(d_nodeManager->booleanType());
  ASSERT_FALSE(te.isFinished());
  ASSERT_EQ(*te, d_nodeManager->mkConst(false));
  ASSERT_FALSE(te.isFinished());
  ASSERT_EQ(*++te, d_nodeManager->mkConst(true));
  ASSERT_FALSE(te.isFinished());
  ASSERT_THROW(*++te, NoMoreValuesException);
  ASSERT_TRUE(te.isFinished());
  ASSERT_THROW(*++te, NoMoreValuesException);
  ASSERT_TRUE(te.isFinished());
  ASSERT_THROW(*++te, NoMoreValuesException);
  ASSERT_TRUE(te.isFinished());
}

TEST_F(TestTheoryWhiteTypeEnumerator, uf)
{
  TypeNode sort = d_nodeManager->mkSort("T");
  TypeNode sort2 = d_nodeManager->mkSort("U");
  TypeEnumerator te(sort);
  ASSERT_EQ(*te, d_nodeManager->mkConst(UninterpretedSortValue(sort, 0)));
  for (size_t i = 1; i < 100; ++i)
  {
    ASSERT_NE(*te, d_nodeManager->mkConst(UninterpretedSortValue(sort, i)));
    ASSERT_NE(*te, d_nodeManager->mkConst(UninterpretedSortValue(sort2, i)));
    ASSERT_EQ(*++te, d_nodeManager->mkConst(UninterpretedSortValue(sort, i)));
    ASSERT_NE(*te, d_nodeManager->mkConst(UninterpretedSortValue(sort, i + 2)));
  }
}

TEST_F(TestTheoryWhiteTypeEnumerator, arith)
{
  TypeEnumerator te(d_nodeManager->integerType());
  ASSERT_FALSE(te.isFinished());
  ASSERT_EQ(*te, d_nodeManager->mkConstInt(Rational(0)));
  for (int i = 1; i <= 100; ++i)
  {
    ASSERT_FALSE(te.isFinished());
    ASSERT_EQ(*++te, d_nodeManager->mkConstInt(Rational(i)));
    ASSERT_FALSE(te.isFinished());
    ASSERT_EQ(*++te, d_nodeManager->mkConstInt(Rational(-i)));
  }
  ASSERT_FALSE(te.isFinished());

  te = TypeEnumerator(d_nodeManager->realType());
  ASSERT_FALSE(te.isFinished());
  ASSERT_EQ(*te, d_nodeManager->mkConstReal(Rational(0, 1)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(1, 1)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-1, 1)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(2, 1)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-2, 1)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(1, 2)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-1, 2)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(3, 1)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-3, 1)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(1, 3)));
  ASSERT_FALSE(te.isFinished());
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-1, 3)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(4, 1)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-4, 1)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(3, 2)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-3, 2)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(2, 3)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-2, 3)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(1, 4)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-1, 4)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(5, 1)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-5, 1)));
  ASSERT_FALSE(te.isFinished());
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(1, 5)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-1, 5)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(6, 1)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-6, 1)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(5, 2)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-5, 2)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(4, 3)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-4, 3)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(3, 4)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-3, 4)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(2, 5)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-2, 5)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(1, 6)));
  ASSERT_FALSE(te.isFinished());
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-1, 6)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(7, 1)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-7, 1)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(5, 3)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-5, 3)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(3, 5)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-3, 5)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(1, 7)));
  ASSERT_EQ(*++te, d_nodeManager->mkConstReal(Rational(-1, 7)));
  ASSERT_FALSE(te.isFinished());
}

TEST_F(TestTheoryWhiteTypeEnumerator, dtypes_finite)
{
  DType dt("Colors");
  dt.addConstructor(std::make_shared<DTypeConstructor>("red"));
  dt.addConstructor(std::make_shared<DTypeConstructor>("orange"));
  dt.addConstructor(std::make_shared<DTypeConstructor>("yellow"));
  dt.addConstructor(std::make_shared<DTypeConstructor>("green"));
  dt.addConstructor(std::make_shared<DTypeConstructor>("blue"));
  dt.addConstructor(std::make_shared<DTypeConstructor>("violet"));
  TypeNode datatype = d_nodeManager->mkDatatypeType(dt);
  const std::vector<std::shared_ptr<DTypeConstructor> >& dtcons =
      datatype.getDType().getConstructors();
  TypeEnumerator te(datatype);
  ASSERT_EQ(
      *te,
      d_nodeManager->mkNode(APPLY_CONSTRUCTOR, dtcons[0]->getConstructor()));
  ASSERT_EQ(
      *++te,
      d_nodeManager->mkNode(APPLY_CONSTRUCTOR, dtcons[1]->getConstructor()));
  ASSERT_EQ(
      *++te,
      d_nodeManager->mkNode(APPLY_CONSTRUCTOR, dtcons[2]->getConstructor()));
  ASSERT_EQ(
      *++te,
      d_nodeManager->mkNode(APPLY_CONSTRUCTOR, dtcons[3]->getConstructor()));
  ASSERT_EQ(
      *++te,
      d_nodeManager->mkNode(APPLY_CONSTRUCTOR, dtcons[4]->getConstructor()));
  ASSERT_EQ(
      *++te,
      d_nodeManager->mkNode(APPLY_CONSTRUCTOR, dtcons[5]->getConstructor()));
  ASSERT_THROW(*++te, NoMoreValuesException);
  ASSERT_THROW(*++te, NoMoreValuesException);
  ASSERT_THROW(*++te, NoMoreValuesException);
}

TEST_F(TestTheoryWhiteTypeEnumerator, dtypes_infinite)
{
  DType colors("Colors");
  colors.addConstructor(std::make_shared<DTypeConstructor>("red"));
  colors.addConstructor(std::make_shared<DTypeConstructor>("orange"));
  colors.addConstructor(std::make_shared<DTypeConstructor>("yellow"));
  colors.addConstructor(std::make_shared<DTypeConstructor>("green"));
  colors.addConstructor(std::make_shared<DTypeConstructor>("blue"));
  colors.addConstructor(std::make_shared<DTypeConstructor>("violet"));
  TypeNode colorsType = d_nodeManager->mkDatatypeType(colors);
  const std::vector<std::shared_ptr<DTypeConstructor> >& ctCons =
      colorsType.getDType().getConstructors();
  DType listColors("ListColors");
  std::shared_ptr<DTypeConstructor> consC =
      std::make_shared<DTypeConstructor>("cons");
  consC->addArg("car", colorsType);
  consC->addArgSelf("cdr");
  listColors.addConstructor(consC);
  listColors.addConstructor(std::make_shared<DTypeConstructor>("nil"));
  TypeNode listColorsType = d_nodeManager->mkDatatypeType(listColors);
  const std::vector<std::shared_ptr<DTypeConstructor> >& lctCons =
      listColorsType.getDType().getConstructors();

  TypeEnumerator te(listColorsType);
  ASSERT_FALSE(te.isFinished());
  Node cons = lctCons[0]->getConstructor();
  Node nil =
      d_nodeManager->mkNode(APPLY_CONSTRUCTOR, lctCons[1]->getConstructor());
  Node red =
      d_nodeManager->mkNode(APPLY_CONSTRUCTOR, ctCons[0]->getConstructor());
  Node orange =
      d_nodeManager->mkNode(APPLY_CONSTRUCTOR, ctCons[1]->getConstructor());
  Node yellow =
      d_nodeManager->mkNode(APPLY_CONSTRUCTOR, ctCons[2]->getConstructor());
  ASSERT_EQ(*te, nil);
  ASSERT_EQ(*++te, d_nodeManager->mkNode(APPLY_CONSTRUCTOR, cons, red, nil));
  ASSERT_FALSE(te.isFinished());
  ASSERT_EQ(*++te,
            d_nodeManager->mkNode(
                APPLY_CONSTRUCTOR,
                cons,
                red,
                d_nodeManager->mkNode(APPLY_CONSTRUCTOR, cons, red, nil)));
  ASSERT_FALSE(te.isFinished());
  ASSERT_EQ(*++te, d_nodeManager->mkNode(APPLY_CONSTRUCTOR, cons, orange, nil));
  ASSERT_FALSE(te.isFinished());
  ASSERT_EQ(*++te,
            d_nodeManager->mkNode(
                APPLY_CONSTRUCTOR,
                cons,
                red,
                d_nodeManager->mkNode(
                    APPLY_CONSTRUCTOR,
                    cons,
                    red,
                    d_nodeManager->mkNode(APPLY_CONSTRUCTOR, cons, red, nil))));
  ASSERT_FALSE(te.isFinished());
  ASSERT_EQ(*++te,
            d_nodeManager->mkNode(
                APPLY_CONSTRUCTOR,
                cons,
                orange,
                d_nodeManager->mkNode(APPLY_CONSTRUCTOR, cons, red, nil)));
  ASSERT_FALSE(te.isFinished());
  ASSERT_EQ(*++te, d_nodeManager->mkNode(APPLY_CONSTRUCTOR, cons, yellow, nil));
  ASSERT_FALSE(te.isFinished());
  ASSERT_EQ(*++te,
            d_nodeManager->mkNode(
                APPLY_CONSTRUCTOR,
                cons,
                red,
                d_nodeManager->mkNode(APPLY_CONSTRUCTOR, cons, orange, nil)));
  ASSERT_FALSE(te.isFinished());
}

TEST_F(TestTheoryWhiteTypeEnumerator, arrays_infinite)
{
  TypeEnumerator te(d_nodeManager->mkArrayType(d_nodeManager->integerType(),
                                               d_nodeManager->integerType()));
  std::unordered_set<Node> elts;
  for (uint32_t i = 0; i < 1000; ++i)
  {
    ASSERT_FALSE(te.isFinished());
    Node elt = *te++;
    // ensure no duplicates
    ASSERT_TRUE(elts.find(elt) == elts.end());
    elts.insert(elt);
  }
  ASSERT_FALSE(te.isFinished());

  // ensure that certain items were found
  TypeNode arrayType = d_nodeManager->mkArrayType(d_nodeManager->integerType(),
                                                  d_nodeManager->integerType());
  Node zeroes = d_nodeManager->mkConst(
      ArrayStoreAll(arrayType, d_nodeManager->mkConstInt(Rational(0))));
  Node ones = d_nodeManager->mkConst(
      ArrayStoreAll(arrayType, d_nodeManager->mkConstInt(Rational(1))));
  Node twos = d_nodeManager->mkConst(
      ArrayStoreAll(arrayType, d_nodeManager->mkConstInt(Rational(2))));
  Node threes = d_nodeManager->mkConst(
      ArrayStoreAll(arrayType, d_nodeManager->mkConstInt(Rational(3))));
  Node fours = d_nodeManager->mkConst(
      ArrayStoreAll(arrayType, d_nodeManager->mkConstInt(Rational(4))));
  Node tens = d_nodeManager->mkConst(
      ArrayStoreAll(arrayType, d_nodeManager->mkConstInt(Rational(10))));

  Node zero = d_nodeManager->mkConstInt(Rational(0));
  Node one = d_nodeManager->mkConstInt(Rational(1));
  Node two = d_nodeManager->mkConstInt(Rational(2));
  Node three = d_nodeManager->mkConstInt(Rational(3));
  Node four = d_nodeManager->mkConstInt(Rational(4));
  Node five = d_nodeManager->mkConstInt(Rational(5));
  Node eleven = d_nodeManager->mkConstInt(Rational(11));

  ASSERT_EQ(elts.find(d_nodeManager->mkNode(STORE, ones, zero, zero)),
            elts.end());

  // the arrays enumerator is currently not a fair enumerator -- when it is,
  // these should be flipped
  ASSERT_EQ(elts.find(d_nodeManager->mkNode(STORE, tens, four, five)),
            elts.end());
  ASSERT_EQ(elts.find(d_nodeManager->mkNode(
                STORE,
                d_nodeManager->mkNode(
                    STORE,
                    d_nodeManager->mkNode(STORE, fours, eleven, two),
                    two,
                    one),
                zero,
                two)),
            elts.end());
  ASSERT_EQ(elts.find(threes), elts.end());
  ASSERT_EQ(elts.find(d_nodeManager->mkNode(
                STORE,
                d_nodeManager->mkNode(
                    STORE,
                    d_nodeManager->mkNode(
                        STORE,
                        d_nodeManager->mkNode(STORE, twos, three, zero),
                        two,
                        zero),
                    one,
                    zero),
                zero,
                zero)),
            elts.end());
}

TEST_F(TestTheoryWhiteTypeEnumerator, bv)
{
  TypeEnumerator te(d_nodeManager->mkBitVectorType(3));
  ASSERT_EQ(*te, d_nodeManager->mkConst(BitVector(3u, 0u)));
  ASSERT_EQ(*++te, d_nodeManager->mkConst(BitVector(3u, 1u)));
  ASSERT_EQ(*++te, d_nodeManager->mkConst(BitVector(3u, 2u)));
  ASSERT_EQ(*++te, d_nodeManager->mkConst(BitVector(3u, 3u)));
  ASSERT_EQ(*++te, d_nodeManager->mkConst(BitVector(3u, 4u)));
  ASSERT_EQ(*++te, d_nodeManager->mkConst(BitVector(3u, 5u)));
  ASSERT_EQ(*++te, d_nodeManager->mkConst(BitVector(3u, 6u)));
  ASSERT_EQ(*++te, d_nodeManager->mkConst(BitVector(3u, 7u)));
  ASSERT_THROW(*++te, NoMoreValuesException);
  ASSERT_THROW(*++te, NoMoreValuesException);
  ASSERT_THROW(*++te, NoMoreValuesException);
}
}  // namespace test
}  // namespace cvc5::internal
