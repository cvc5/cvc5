/*********************                                                        */
/*! \file theory_bags_type_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Andrew Reynolds, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory type rules.
 **
 ** Bags theory type rules.
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
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    Assert(n.getKind() == kind::MAX_UNION || n.getKind() == kind::DISJOINT_UNION
           || n.getKind() == kind::MIN_INTERSECTION
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
        if (n.getKind() == kind::MIN_INTERSECTION)
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

  inline static bool computeIsConst(NodeManager* nodeManager, TNode n)
  {
    // only DISJOINT_UNION has a const rule in kinds.
    // Other binary operators do not have const rules in kinds
    Assert(n.getKind() == kind::DISJOINT_UNION);
    return NormalForm::checkNormalConstant(n);
  }
}; /* struct BinaryOperatorTypeRule */

struct IsIncludedTypeRule
{
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
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
  inline static TypeNode computeType(NodeManager* nodeManager,
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
      // TODO : still need to be flexible here due to situations like:
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

struct BagPairTypeRule
{
  inline static TypeNode computeType(NodeManager* nm, TNode n, bool check)
  {
    Assert(n.getKind() == kind::BAG_PAIR);
    if (check)
    {
      if (n.getNumChildren() != 2)
      {
        std::stringstream ss;
        ss << "operands in term " << n << " are " << n.getNumChildren()
           << ", but BAG_PAIR expects 2 operands.";
        throw TypeCheckingExceptionPrivate(n, ss.str());
      }
      TypeNode type1 = n[1].getType(check);
      if (!type1.isInteger())
      {
        std::stringstream ss;
        ss << "BAG_PAIR expects an integer for " << n[1] << ". Found" << type1;
        throw TypeCheckingExceptionPrivate(n, ss.str());
      }
      if (n[1].isConst())
      {
        Rational count = n[1].getConst<Rational>();
        if (count <= Rational::fromDecimal("0"))
        {
          std::stringstream ss;
          ss << "BAG_PAIR expects a positive integer. Found " << n[1];
          throw TypeCheckingExceptionPrivate(n, ss.str());
        }
      }
    }

    return nm->mkBagType(n[0].getType(check));
  }

  inline static bool computeIsConst(NodeManager* nodeManager, TNode n)
  {
    Assert(n.getKind() == kind::BAG_PAIR);
    // for a bag to be a constant, both the element and its multiplicity should
    // be constants.
    return n[0].isConst() && n[1].isConst();
  }
}; /* struct BagPairTypeRule */

struct IsSingletonTypeRule
{
  inline static TypeNode computeType(NodeManager* nodeManager,
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
}; /* struct IsBagPairTypeRule */

struct EmptyBagTypeRule
{
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    Assert(n.getKind() == kind::EMPTYBAG);
    EmptyBag emptyBag = n.getConst<EmptyBag>();
    return emptyBag.getType();
  }
}; /* struct EmptyBagTypeRule */

struct CardTypeRule
{
  inline static TypeNode computeType(NodeManager* nodeManager,
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
}; /* struct CardTypeRule */

struct ChooseTypeRule
{
  inline static TypeNode computeType(NodeManager* nodeManager,
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
}; /* struct ChooseTypeRule */

struct InsertTypeRule
{
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    Assert(n.getKind() == kind::BAG_INSERT);
    size_t numChildren = n.getNumChildren();
    Assert(numChildren >= 3);
    TypeNode bagType = n[numChildren - 1].getType(check);
    if (check)
    {
      // e.g. (BAG_INSERT "E" 2 "D" 4 "C" 6 "B" 8 (BAG_PAIR "A" 100))
      if (!bagType.isBag())
      {
        throw TypeCheckingExceptionPrivate(n, "inserting into a non-bag");
      }

      if (numChildren % 2 != 1)
      {
        std::stringstream ss;
        ss << "BAG_INSERT needs an odd number of children. Node " << n
           << " has " << numChildren << " children." << std::endl;
        throw TypeCheckingExceptionPrivate(n, ss.str());
      }

      TypeNode baseType = bagType.getBagElementType();
      for (size_t i = 0; i < numChildren - 1; i += 2)
      {
        TypeNode elementType = n[i].getType(check);
        if (!elementType.isComparableTo(baseType))
        {
          std::stringstream ss;
          ss << "node " << n << " inserts node " << n[i] << " of type "
             << elementType << " into a bag of type " << bagType << std::endl;
          throw TypeCheckingExceptionPrivate(n, ss.str());
        }
        TypeNode countType = n[i + 1].getType(check);
        if (!countType.isInteger())
        {
          std::stringstream ss;
          ss << "BAG_PAIR expects an integer for " << n[i + 1] << " in " << n
             << ". Found " << countType << "." << std::endl;
          throw TypeCheckingExceptionPrivate(n, ss.str());
        }
        if (n[i + 1].isConst())
        {
          Rational count = n[i + 1].getConst<Rational>();
          if (count <= Rational::fromDecimal("0"))
          {
            std::stringstream ss;
            ss << "BAG_INSERT expects a positive integer. Found " << n[i + 1];
            throw TypeCheckingExceptionPrivate(n, ss.str());
          }
        }
      }
    }
    return bagType;
  }
}; /* struct InsertTypeRule */

struct BagsProperties
{
  inline static Cardinality computeCardinality(TypeNode type)
  {
    // ToDo: review this
    return Cardinality::UNKNOWN_CARD;
  }

  inline static bool isWellFounded(TypeNode type)
  {
    return type[0].isWellFounded();
  }

  inline static Node mkGroundTerm(TypeNode type)
  {
    Assert(type.isBag());
    return NodeManager::currentNM()->mkConst(EmptyBag(type));
  }
}; /* struct BagsProperties */

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__THEORY_BAGS_TYPE_RULES_H */
