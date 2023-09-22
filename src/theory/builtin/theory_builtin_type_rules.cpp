/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  TypeNode booleanType = nodeManager->booleanType();

  if (check)
  {
    TypeNode lhsType = n[0].getType(check);
    TypeNode rhsType = n[1].getType(check);

    if (lhsType != rhsType)
    {
      std::stringstream ss;
      ss << "Subexpressions must have the same type:" << std::endl;
      ss << "Equation: " << n << std::endl;
      ss << "Type 1: " << lhsType << std::endl;
      ss << "Type 2: " << rhsType << std::endl;

      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }
  return booleanType;
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
    TypeNode joinType = (*child_it).getType(check);
    for (++child_it; child_it != child_it_end; ++child_it)
    {
      TypeNode currentType = (*child_it).getType();
      if (joinType != currentType)
      {
        throw TypeCheckingExceptionPrivate(
            n, "Not all arguments are of the same type");
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
  if (check)
  {
    for (TNode c : n)
    {
      c.getType(check);
    }
  }
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
  if (n[0].getType(check) != nodeManager->boundVarListType())
  {
    std::stringstream ss;
    ss << "expected a bound var list for WITNESS expression, got `"
       << n[0].getType().toString() << "'";
    throw TypeCheckingExceptionPrivate(n, ss.str());
  }
  if (n[0].getNumChildren() != 1)
  {
    std::stringstream ss;
    ss << "expected a bound var list with one argument for WITNESS expression";
    throw TypeCheckingExceptionPrivate(n, ss.str());
  }
  if (check)
  {
    TypeNode rangeType = n[1].getType(check);
    if (!rangeType.isBoolean())
    {
      std::stringstream ss;
      ss << "expected a body of a WITNESS expression to have Boolean type";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    if (n.getNumChildren() == 3)
    {
      if (n[2].getType(check) != nodeManager->instPatternListType())
      {
        throw TypeCheckingExceptionPrivate(
            n,
            "third argument of witness is not instantiation "
            "pattern list");
      }
    }
  }
  // The type of a witness function is the type of its bound variable.
  return n[0][0].getType();
}

TypeNode ApplyIndexedSymbolicTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->mkAbstractType(kind::ABSTRACT_TYPE);
}
TypeNode ApplyIndexedSymbolicTypeRule::computeType(NodeManager* nodeManager,
                                                   TNode n,
                                                   bool check,
                                                   std::ostream* errOut)
{
  // Note that this could be more precise by case splitting on the kind
  // of indexed operator, but we don't do this for simplicity.
  return nodeManager->mkAbstractType(kind::ABSTRACT_TYPE);
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
