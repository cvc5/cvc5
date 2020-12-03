/*********************                                                        */
/*! \file theory_bags_type_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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
        std::stringstream ss;
        ss << "Operator " << n.getKind()
           << " expects two bags of the same type. Found types '" << bagType
           << "' and '" << secondBagType << "'.";
        throw TypeCheckingExceptionPrivate(n, ss.str());
      }
    }
    return bagType;
  }

  static bool computeIsConst(NodeManager* nodeManager, TNode n)
  {
    // only UNION_DISJOINT has a const rule in kinds.
    // Other binary operators do not have const rules in kinds
    Assert(n.getKind() == kind::UNION_DISJOINT);
    return NormalForm::isConstant(n);
  }
}; /* struct BinaryOperatorTypeRule */

struct SubBagTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
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
}; /* struct SubBagTypeRule */

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
}; /* struct CountTypeRule */

struct DuplicateRemovalTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
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
}; /* struct DuplicateRemovalTypeRule */

struct MkBagTypeRule
{
  static TypeNode computeType(NodeManager* nm, TNode n, bool check)
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

struct FromSetTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
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
}; /* struct FromSetTypeRule */

struct ToSetTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
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
}; /* struct ToSetTypeRule */

struct BagsProperties
{
  static Cardinality computeCardinality(TypeNode type)
  {
    return Cardinality::INTEGERS;
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
