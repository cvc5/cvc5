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
#include "theory/bags/make_bag_op.h"
#include "theory/bags/normal_form.h"
#include "util/cardinality.h"
#include "util/rational.h"

namespace cvc5 {
namespace theory {
namespace bags {

TypeNode BinaryOperatorTypeRule::computeType(NodeManager* nodeManager,
                                             TNode n,
                                             bool check)
{
  Assert(n.getKind() == kind::UNION_MAX || n.getKind() == kind::UNION_DISJOINT
         || n.getKind() == kind::INTERSECTION_MIN
         || n.getKind() == kind::DIFFERENCE_SUBTRACT
         || n.getKind() == kind::DIFFERENCE_REMOVE);
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
  Assert(n.getKind() == kind::UNION_DISJOINT);
  return NormalForm::isConstant(n);
}

TypeNode SubBagTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
{
  Assert(n.getKind() == kind::SUBBAG);
  TypeNode bagType = n[0].getType(check);
  if (check)
  {
    if (!bagType.isBag())
    {
      throw TypeCheckingExceptionPrivate(n, "SUBBAG operating on non-bag");
    }
    TypeNode secondBagType = n[1].getType(check);
    if (secondBagType != bagType)
    {
      if (!bagType.isComparableTo(secondBagType))
      {
        throw TypeCheckingExceptionPrivate(
            n, "SUBBAG operating on bags of different types");
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
    // e.g. (count 1 (mkBag (mkBag_op Real) 1.0 3))) is 3 whereas
    // (count 1.0 (mkBag (mkBag_op Int) 1 3))) throws a typing error
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

TypeNode DuplicateRemovalTypeRule::computeType(NodeManager* nodeManager,
                                               TNode n,
                                               bool check)
{
  Assert(n.getKind() == kind::DUPLICATE_REMOVAL);
  TypeNode bagType = n[0].getType(check);
  if (check)
  {
    if (!bagType.isBag())
    {
      std::stringstream ss;
      ss << "Applying DUPLICATE_REMOVAL on a non-bag argument in term " << n;
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }
  return bagType;
}

TypeNode MkBagTypeRule::computeType(NodeManager* nm, TNode n, bool check)
{
  Assert(n.getKind() == kind::MK_BAG && n.hasOperator()
         && n.getOperator().getKind() == kind::MK_BAG_OP);
  MakeBagOp op = n.getOperator().getConst<MakeBagOp>();
  TypeNode expectedElementType = op.getType();
  if (check)
  {
    if (n.getNumChildren() != 2)
    {
      std::stringstream ss;
      ss << "operands in term " << n << " are " << n.getNumChildren()
         << ", but MK_BAG expects 2 operands.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    TypeNode type1 = n[1].getType(check);
    if (!type1.isInteger())
    {
      std::stringstream ss;
      ss << "MK_BAG expects an integer for " << n[1] << ". Found" << type1;
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }

    TypeNode actualElementType = n[0].getType(check);
    // the type of the element should be a subtype of the type of the operator
    // e.g. (mkBag (mkBag_op Real) 1 1) where 1 is an Int
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

bool MkBagTypeRule::computeIsConst(NodeManager* nodeManager, TNode n)
{
  Assert(n.getKind() == kind::MK_BAG);
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
  Assert(n.getKind() == kind::EMPTYBAG);
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
          n, "CHOOSE operator expects a bag, a non-bag is found");
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
