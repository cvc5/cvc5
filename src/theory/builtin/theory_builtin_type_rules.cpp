/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Type rules for the builtin theory.
 */

#include "theory/builtin/theory_builtin_type_rules.h"

#include "expr/attribute.h"
#include "expr/skolem_manager.h"
#include "theory/builtin/generic_op.h"
#include "util/uninterpreted_sort_value.h"

namespace cvc5::internal {
namespace theory {
namespace builtin {

TypeNode EqualityTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode EqualityTypeRule::computeType(NodeManager* nodeManager,
                                       TNode n,
                                       bool check,
                                       std::ostream* errOut)
{
  if (check)
  {
    TypeNode lhsType = n[0].getTypeOrNull();
    TypeNode rhsType = n[1].getTypeOrNull();
    if (!lhsType.isComparableTo(rhsType))
    {
      if (errOut)
      {
        (*errOut) << "Subexpressions must have the same type:" << std::endl;
        (*errOut) << "Equation: " << n << std::endl;
        (*errOut) << "Type 1: " << lhsType << std::endl;
        (*errOut) << "Type 2: " << rhsType << std::endl;
      }
      return TypeNode::null();
    }
  }
  return nodeManager->booleanType();
}

TypeNode DistinctTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode DistinctTypeRule::computeType(NodeManager* nodeManager,
                                       TNode n,
                                       bool check,
                                       std::ostream* errOut)
{
  if (check)
  {
    TNode::iterator child_it = n.begin();
    TNode::iterator child_it_end = n.end();
    TypeNode joinType = (*child_it).getTypeOrNull();
    for (++child_it; child_it != child_it_end; ++child_it)
    {
      TypeNode currentType = (*child_it).getType();
      joinType = joinType.leastUpperBound(currentType);
      if (joinType.isNull())
      {
        if (errOut)
        {
          (*errOut) << "Not all arguments are of the same type";
        }
        return TypeNode::null();
      }
    }
  }
  return nodeManager->booleanType();
}

TypeNode SExprTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->sExprType();
}
TypeNode SExprTypeRule::computeType(NodeManager* nodeManager,
                                    TNode n,
                                    bool check,
                                    std::ostream* errOut)
{
  return nodeManager->sExprType();
}

TypeNode UninterpretedSortValueTypeRule::preComputeType(NodeManager* nm,
                                                        TNode n)
{
  return TypeNode::null();
}
TypeNode UninterpretedSortValueTypeRule::computeType(NodeManager* nodeManager,
                                                     TNode n,
                                                     bool check,
                                                     std::ostream* errOut)
{
  return n.getConst<UninterpretedSortValue>().getType();
}

TypeNode WitnessTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode WitnessTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check,
                                      std::ostream* errOut)
{
  if (n[0].getTypeOrNull() != nodeManager->boundVarListType())
  {
    if (errOut)
    {
      (*errOut) << "expected a bound var list for WITNESS expression, got `"
                << n[0].getType().toString() << "'";
    }
    return TypeNode::null();
  }
  if (n[0].getNumChildren() != 1)
  {
    if (errOut)
    {
      (*errOut) << "expected a bound var list with one argument for WITNESS "
                   "expression";
    }
    return TypeNode::null();
  }
  if (check)
  {
    TypeNode rangeType = n[1].getTypeOrNull();
    if (!rangeType.isBoolean())
    {
      if (errOut)
      {
        (*errOut)
            << "expected a body of a WITNESS expression to have Boolean type";
      }
      return TypeNode::null();
    }
    if (n.getNumChildren() == 3)
    {
      if (n[2].getTypeOrNull() != nodeManager->instPatternListType())
      {
        if (errOut)
        {
          (*errOut)
              << "third argument of witness is not instantiation pattern list";
        }
        return TypeNode::null();
      }
    }
  }
  // The type of a witness function is the type of its bound variable.
  return n[0][0].getType();
}

TypeNode ApplyIndexedSymbolicTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode ApplyIndexedSymbolicTypeRule::computeType(NodeManager* nodeManager,
                                                   TNode n,
                                                   bool check,
                                                   std::ostream* errOut)
{
  // get the concrete application version of this, if possible
  Node cn = GenericOp::getConcreteApp(n);
  if (cn == n)
  {
    // if it cannot be made concrete, it has abstract type
    return nodeManager->mkAbstractType(Kind::ABSTRACT_TYPE);
  }
  // if we can make concrete, return its type
  return cn.getType();
}
/**
 * Attribute for caching the ground term for each type. Maps TypeNode to the
 * skolem to return for mkGroundTerm.
 */
struct GroundTermAttributeId
{
};
typedef expr::Attribute<GroundTermAttributeId, Node> GroundTermAttribute;

Node SortProperties::mkGroundTerm(TypeNode type)
{
  // we typically use this method for sorts, although there are other types
  // where it is used as well, e.g. arrays that are not closed enumerable.
  GroundTermAttribute gta;
  if (type.hasAttribute(gta))
  {
    return type.getAttribute(gta);
  }
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  Node k = sm->mkDummySkolem(
      "groundTerm", type, "a ground term created for type " + type.toString());
  type.setAttribute(gta, k);
  return k;
}

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5::internal
