/*********************                                                        */
/*! \file theory_bags_type_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory type rules.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__THEORY_BAGS_TYPE_RULES_H
#define CVC4__THEORY__BAGS__THEORY_BAGS_TYPE_RULES_H

#include "theory/bags/normal_form.h"

namespace CVC4 {
namespace theory {
namespace bags {

struct BinaryOperatorTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
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
        if (n.getKind() == kind::INTERSECTION_MIN)
        {
          bagType = TypeNode::mostCommonTypeNode(secondBagType, bagType);
        }
        else
        {
          bagType = TypeNode::leastCommonTypeNode(secondBagType, bagType);
        }
        if (bagType.isNull())
        {
          throw TypeCheckingExceptionPrivate(
              n, "operator expects two bags of comparable types");
        }
      }
    }
    return bagType;
  }

  static bool computeIsConst(NodeManager* nodeManager, TNode n)
  {
    // only UNION_DISJOINT has a const rule in kinds.
    // Other binary operators do not have const rules in kinds
    Assert(n.getKind() == kind::UNION_DISJOINT);
    return NormalForm::checkNormalConstant(n);
  }
}; /* struct BinaryOperatorTypeRule */

struct IsIncludedTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    Assert(n.getKind() == kind::BAG_IS_INCLUDED);
    TypeNode bagType = n[0].getType(check);
    if (check)
    {
      if (!bagType.isBag())
      {
        throw TypeCheckingExceptionPrivate(
            n, "BAG_IS_INCLUDED operating on non-bag");
      }
      TypeNode secondBagType = n[1].getType(check);
      if (secondBagType != bagType)
      {
        if (!bagType.isComparableTo(secondBagType))
        {
          throw TypeCheckingExceptionPrivate(
              n, "BAG_IS_INCLUDED operating on bags of different types");
        }
      }
    }
    return nodeManager->booleanType();
  }
}; /* struct IsIncludedTypeRule */

struct CountTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
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
      // TODO(projects#226): comments from sets
      //
      // T : (Bag Int)
      // B : (Bag Real)
      // (= (as T (Bag Real)) B)
      // (= (bag-count 0.5 B) 1)
      // ...where (bag-count 0.5 T) is inferred

      if (!elementType.isComparableTo(bagType.getBagElementType()))
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
}; /* struct CountTypeRule */

struct MkBagTypeRule
{
  static TypeNode computeType(NodeManager* nm, TNode n, bool check)
  {
    Assert(n.getKind() == kind::MK_BAG);
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
    }

    return nm->mkBagType(n[0].getType(check));
  }

  static bool computeIsConst(NodeManager* nodeManager, TNode n)
  {
    Assert(n.getKind() == kind::MK_BAG);
    // for a bag to be a constant, both the element and its multiplicity should
    // be constants, and the multiplicity should be > 0.
    return n[0].isConst() && n[1].isConst()
           && n[1].getConst<Rational>().sgn() == 1;
  }
}; /* struct MkBagTypeRule */

struct IsSingletonTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
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
}; /* struct IsMkBagTypeRule */

struct EmptyBagTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    Assert(n.getKind() == kind::EMPTYBAG);
    EmptyBag emptyBag = n.getConst<EmptyBag>();
    return emptyBag.getType();
  }
}; /* struct EmptyBagTypeRule */

struct CardTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
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
}; /* struct CardTypeRule */

struct ChooseTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
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
}; /* struct ChooseTypeRule */

struct BagsProperties
{
  static Cardinality computeCardinality(TypeNode type)
  {
    return Cardinality::UNKNOWN_CARD;
  }

  static bool isWellFounded(TypeNode type) { return type[0].isWellFounded(); }

  static Node mkGroundTerm(TypeNode type)
  {
    Assert(type.isBag());
    return NodeManager::currentNM()->mkConst(EmptyBag(type));
  }
}; /* struct BagsProperties */

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__THEORY_BAGS_TYPE_RULES_H */
