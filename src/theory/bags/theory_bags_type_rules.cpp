/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bags theory type rules.
 */

#include "theory/bags/theory_bags_type_rules.h"

#include <sstream>

#include "base/check.h"
#include "expr/emptybag.h"
#include "theory/bags/bag_make_op.h"
#include "theory/bags/bags_utils.h"
#include "util/cardinality.h"
#include "util/rational.h"

namespace cvc5 {
namespace theory {
namespace bags {

TypeNode BinaryOperatorTypeRule::computeType(NodeManager* nodeManager,
                                             TNode n,
                                             bool check)
{
  Assert(n.getKind() == kind::BAG_UNION_MAX
         || n.getKind() == kind::BAG_UNION_DISJOINT
         || n.getKind() == kind::BAG_INTER_MIN
         || n.getKind() == kind::BAG_DIFFERENCE_SUBTRACT
         || n.getKind() == kind::BAG_DIFFERENCE_REMOVE);
  TypeNode bagType = n[0].getType(check);
  if (check)
  {
    if (!bagType.isBag())
    {
      throw TypeCheckingExceptionPrivate(
          n, "operator expects a bag, first argument is not");
    }
    TypeNode secondBagType = n[1].getType(check);
    if (secondBagType != bagType)
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind()
         << " expects two bags of the same type. Found types '" << bagType
         << "' and '" << secondBagType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }
  return bagType;
}

bool BinaryOperatorTypeRule::computeIsConst(NodeManager* nodeManager, TNode n)
{
  // only UNION_DISJOINT has a const rule in kinds.
  // Other binary operators do not have const rules in kinds
  Assert(n.getKind() == kind::BAG_UNION_DISJOINT);
  return BagsUtils::isConstant(n);
}

TypeNode SubBagTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
{
  Assert(n.getKind() == kind::BAG_SUBBAG);
  TypeNode bagType = n[0].getType(check);
  if (check)
  {
    if (!bagType.isBag())
    {
      throw TypeCheckingExceptionPrivate(n, "BAG_SUBBAG operating on non-bag");
    }
    TypeNode secondBagType = n[1].getType(check);
    if (secondBagType != bagType)
    {
      if (!bagType.isComparableTo(secondBagType))
      {
        throw TypeCheckingExceptionPrivate(
            n, "BAG_SUBBAG operating on bags of different types");
      }
    }
  }
  return nodeManager->booleanType();
}

TypeNode CountTypeRule::computeType(NodeManager* nodeManager,
                                    TNode n,
                                    bool check)
{
  Assert(n.getKind() == kind::BAG_COUNT);
  TypeNode bagType = n[1].getType(check);
  if (check)
  {
    if (!bagType.isBag())
    {
      throw TypeCheckingExceptionPrivate(
          n, "checking for membership in a non-bag");
    }
    TypeNode elementType = n[0].getType(check);
    // e.g. (bag.count 1 (bag (BagMakeOp Real) 1.0 3))) is 3 whereas
    // (bag.count 1.0 (bag (BagMakeOp Int) 1 3)) throws a typing error
    if (!elementType.isSubtypeOf(bagType.getBagElementType()))
    {
      std::stringstream ss;
      ss << "member operating on bags of different types:\n"
         << "child type:  " << elementType << "\n"
         << "not subtype: " << bagType.getBagElementType() << "\n"
         << "in term : " << n;
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }
  return nodeManager->integerType();
}

TypeNode MemberTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
{
  Assert(n.getKind() == kind::BAG_MEMBER);
  TypeNode bagType = n[1].getType(check);
  if (check)
  {
    if (!bagType.isBag())
    {
      throw TypeCheckingExceptionPrivate(
          n, "checking for membership in a non-bag");
    }
    TypeNode elementType = n[0].getType(check);
    // e.g. (bag.member 1 (bag 1.0 1)) is true whereas
    // (bag.member 1.0 (bag 1 1)) throws a typing error
    if (!elementType.isSubtypeOf(bagType.getBagElementType()))
    {
      std::stringstream ss;
      ss << "member operating on bags of different types:\n"
         << "child type:  " << elementType << "\n"
         << "not subtype: " << bagType.getBagElementType() << "\n"
         << "in term : " << n;
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }
  return nodeManager->booleanType();
}

TypeNode DuplicateRemovalTypeRule::computeType(NodeManager* nodeManager,
                                               TNode n,
                                               bool check)
{
  Assert(n.getKind() == kind::BAG_DUPLICATE_REMOVAL);
  TypeNode bagType = n[0].getType(check);
  if (check)
  {
    if (!bagType.isBag())
    {
      std::stringstream ss;
      ss << "Applying BAG_DUPLICATE_REMOVAL on a non-bag argument in term "
         << n;
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }
  return bagType;
}

TypeNode BagMakeTypeRule::computeType(NodeManager* nm, TNode n, bool check)
{
  Assert(n.getKind() == kind::BAG_MAKE && n.hasOperator()
         && n.getOperator().getKind() == kind::BAG_MAKE_OP);
  BagMakeOp op = n.getOperator().getConst<BagMakeOp>();
  TypeNode expectedElementType = op.getType();
  if (check)
  {
    if (n.getNumChildren() != 2)
    {
      std::stringstream ss;
      ss << "operands in term " << n << " are " << n.getNumChildren()
         << ", but BAG_MAKE expects 2 operands.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    TypeNode type1 = n[1].getType(check);
    if (!type1.isInteger())
    {
      std::stringstream ss;
      ss << "BAG_MAKE expects an integer for " << n[1] << ". Found" << type1;
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }

    TypeNode actualElementType = n[0].getType(check);
    // the type of the element should be a subtype of the type of the operator
    // e.g. (bag (bag_op Real) 1 1) where 1 is an Int
    if (!actualElementType.isSubtypeOf(expectedElementType))
    {
      std::stringstream ss;
      ss << "The type '" << actualElementType
         << "' of the element is not a subtype of '" << expectedElementType
         << "' in term : " << n;
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }

  return nm->mkBagType(expectedElementType);
}

bool BagMakeTypeRule::computeIsConst(NodeManager* nodeManager, TNode n)
{
  Assert(n.getKind() == kind::BAG_MAKE);
  // for a bag to be a constant, both the element and its multiplicity should
  // be constants, and the multiplicity should be > 0.
  return n[0].isConst() && n[1].isConst()
         && n[1].getConst<Rational>().sgn() == 1;
}

TypeNode IsSingletonTypeRule::computeType(NodeManager* nodeManager,
                                          TNode n,
                                          bool check)
{
  Assert(n.getKind() == kind::BAG_IS_SINGLETON);
  TypeNode bagType = n[0].getType(check);
  if (check)
  {
    if (!bagType.isBag())
    {
      throw TypeCheckingExceptionPrivate(
          n, "BAG_IS_SINGLETON operator expects a bag, a non-bag is found");
    }
  }
  return nodeManager->booleanType();
}

TypeNode EmptyBagTypeRule::computeType(NodeManager* nodeManager,
                                       TNode n,
                                       bool check)
{
  Assert(n.getKind() == kind::BAG_EMPTY);
  EmptyBag emptyBag = n.getConst<EmptyBag>();
  return emptyBag.getType();
}

TypeNode CardTypeRule::computeType(NodeManager* nodeManager,
                                   TNode n,
                                   bool check)
{
  Assert(n.getKind() == kind::BAG_CARD);
  TypeNode bagType = n[0].getType(check);
  if (check)
  {
    if (!bagType.isBag())
    {
      throw TypeCheckingExceptionPrivate(
          n, "cardinality operates on a bag, non-bag object found");
    }
  }
  return nodeManager->integerType();
}

TypeNode ChooseTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
{
  Assert(n.getKind() == kind::BAG_CHOOSE);
  TypeNode bagType = n[0].getType(check);
  if (check)
  {
    if (!bagType.isBag())
    {
      throw TypeCheckingExceptionPrivate(
          n, "BAG_CHOOSE operator expects a bag, a non-bag is found");
    }
  }
  return bagType.getBagElementType();
}

TypeNode FromSetTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check)
{
  Assert(n.getKind() == kind::BAG_FROM_SET);
  TypeNode setType = n[0].getType(check);
  if (check)
  {
    if (!setType.isSet())
    {
      throw TypeCheckingExceptionPrivate(
          n, "bag.from_set operator expects a set, a non-set is found");
    }
  }
  TypeNode elementType = setType.getSetElementType();
  TypeNode bagType = nodeManager->mkBagType(elementType);
  return bagType;
}

TypeNode ToSetTypeRule::computeType(NodeManager* nodeManager,
                                    TNode n,
                                    bool check)
{
  Assert(n.getKind() == kind::BAG_TO_SET);
  TypeNode bagType = n[0].getType(check);
  if (check)
  {
    if (!bagType.isBag())
    {
      throw TypeCheckingExceptionPrivate(
          n, "bag.to_set operator expects a bag, a non-bag is found");
    }
  }
  TypeNode elementType = bagType.getBagElementType();
  TypeNode setType = nodeManager->mkSetType(elementType);
  return setType;
}

TypeNode BagMapTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
{
  Assert(n.getKind() == kind::BAG_MAP);
  TypeNode functionType = n[0].getType(check);
  TypeNode bagType = n[1].getType(check);
  if (check)
  {
    if (!bagType.isBag())
    {
      throw TypeCheckingExceptionPrivate(
          n,
          "bag.map operator expects a bag in the second argument, "
          "a non-bag is found");
    }

    TypeNode elementType = bagType.getBagElementType();

    if (!(functionType.isFunction()))
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind() << " expects a function of type  (-> "
         << elementType << " *) as a first argument. "
         << "Found a term of type '" << functionType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    std::vector<TypeNode> argTypes = functionType.getArgTypes();
    if (!(argTypes.size() == 1 && argTypes[0] == elementType))
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind() << " expects a function of type  (-> "
         << elementType << " *). "
         << "Found a function of type '" << functionType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }
  TypeNode rangeType = n[0].getType().getRangeType();
  TypeNode retType = nodeManager->mkBagType(rangeType);
  return retType;
}

TypeNode BagFilterTypeRule::computeType(NodeManager* nodeManager,
                                        TNode n,
                                        bool check)
{
  Assert(n.getKind() == kind::BAG_FILTER);
  TypeNode functionType = n[0].getType(check);
  TypeNode bagType = n[1].getType(check);
  if (check)
  {
    if (!bagType.isBag())
    {
      throw TypeCheckingExceptionPrivate(
          n,
          "bag.filter operator expects a bag in the second argument, "
          "a non-bag is found");
    }

    TypeNode elementType = bagType.getBagElementType();

    if (!(functionType.isFunction()))
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind() << " expects a function of type  (-> "
         << elementType << " Bool) as a first argument. "
         << "Found a term of type '" << functionType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    std::vector<TypeNode> argTypes = functionType.getArgTypes();
    NodeManager* nm = NodeManager::currentNM();
    if (!(argTypes.size() == 1 && argTypes[0] == elementType
          && functionType.getRangeType() == nm->booleanType()))
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind() << " expects a function of type  (-> "
         << elementType << " Bool). "
         << "Found a function of type '" << functionType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }
  return bagType;
}

TypeNode BagFoldTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check)
{
  Assert(n.getKind() == kind::BAG_FOLD);
  TypeNode functionType = n[0].getType(check);
  TypeNode initialValueType = n[1].getType(check);
  TypeNode bagType = n[2].getType(check);
  if (check)
  {
    if (!bagType.isBag())
    {
      throw TypeCheckingExceptionPrivate(
          n,
          "bag.fold operator expects a bag in the third argument, "
          "a non-bag is found");
    }

    TypeNode elementType = bagType.getBagElementType();

    if (!(functionType.isFunction()))
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind() << " expects a function of type  (-> "
         << elementType << " T2 T2) as a first argument. "
         << "Found a term of type '" << functionType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    std::vector<TypeNode> argTypes = functionType.getArgTypes();
    TypeNode rangeType = functionType.getRangeType();
    if (!(argTypes.size() == 2 && argTypes[0] == elementType
          && argTypes[1] == rangeType))
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind() << " expects a function of type  (-> "
         << elementType << " T2 T2). "
         << "Found a function of type '" << functionType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    if (rangeType != initialValueType)
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind() << " expects an initial value of type "
         << rangeType << ". Found a term of type '" << initialValueType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }
  TypeNode retType = n[0].getType().getRangeType();
  return retType;
}

TypeNode TableProductTypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check)
{
  Assert(n.getKind() == kind::TABLE_PRODUCT);
  Node A = n[0];
  Node B = n[1];
  TypeNode typeA = n[0].getType(check);
  TypeNode typeB = n[1].getType(check);

  if (check && !(typeA.isBag() && typeB.isBag()))
  {
    std::stringstream ss;
    ss << "Operator " << n.getKind() << " expects two bags. "
       << "Found two terms of types '" << typeA << "' and '" << typeB
       << "' respectively.";
    throw TypeCheckingExceptionPrivate(n, ss.str());
  }

  TypeNode elementAType = typeA.getBagElementType();
  TypeNode elementBType = typeB.getBagElementType();

  if (check && !(elementAType.isTuple() && elementBType.isTuple()))
  {
    std::stringstream ss;
    ss << "Operator " << n.getKind() << " expects two tables (bags of tuples). "
       << "Found two terms of types '" << typeA << "' and '" << typeB
       << "' respectively.";
    throw TypeCheckingExceptionPrivate(n, ss.str());
  }

  std::vector<TypeNode> productTupleTypes;
  std::vector<TypeNode> tupleATypes = elementAType.getTupleTypes();
  std::vector<TypeNode> tupleBTypes = elementBType.getTupleTypes();

  productTupleTypes.insert(
      productTupleTypes.end(), tupleATypes.begin(), tupleATypes.end());
  productTupleTypes.insert(
      productTupleTypes.end(), tupleBTypes.begin(), tupleBTypes.end());

  TypeNode retTupleType = nodeManager->mkTupleType(productTupleTypes);
  TypeNode retType = nodeManager->mkBagType(retTupleType);
  return retType;
}

Cardinality BagsProperties::computeCardinality(TypeNode type)
{
  return Cardinality::INTEGERS;
}

bool BagsProperties::isWellFounded(TypeNode type)
{
  return type[0].isWellFounded();
}

Node BagsProperties::mkGroundTerm(TypeNode type)
{
  Assert(type.isBag());
  return NodeManager::currentNM()->mkConst(EmptyBag(type));
}
}  // namespace bags
}  // namespace theory
}  // namespace cvc5
