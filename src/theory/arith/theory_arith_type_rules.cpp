/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Typing and cardinality rules for theory arithmetic.
 */

#include "theory/arith/theory_arith_type_rules.h"

#include "util/rational.h"

namespace cvc5 {
namespace theory {
namespace arith {

TypeNode ArithConstantTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check)
{
  Assert(n.getKind() == kind::CONST_RATIONAL);
  if (n.getConst<Rational>().isIntegral())
  {
    return nodeManager->integerType();
  }
  else
  {
    return nodeManager->realType();
  }
}

TypeNode ArithRealAlgebraicNumberOpTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check)
{
  return nodeManager->realType();
}
TypeNode ArithRealAlgebraicNumberTypeRule::computeType(NodeManager* nodeManager,
                                                       TNode n,
                                                       bool check)
{
  return nodeManager->realType();
}

TypeNode ArithOperatorTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check)
{
  TypeNode integerType = nodeManager->integerType();
  TypeNode realType = nodeManager->realType();
  TNode::iterator child_it = n.begin();
  TNode::iterator child_it_end = n.end();
  bool isInteger = true;
  Kind k = n.getKind();
  for (; child_it != child_it_end; ++child_it)
  {
    TypeNode childType = (*child_it).getType(check);
    if (!childType.isInteger())
    {
      isInteger = false;
      if (!check)
      {  // if we're not checking, nothing left to do
        break;
      }
    }
    if (check)
    {
      if (!childType.isRealOrInt())
      {
        throw TypeCheckingExceptionPrivate(n,
                                           "expecting an arithmetic subterm");
      }
      if (k == kind::TO_REAL && !childType.isInteger())
      {
        throw TypeCheckingExceptionPrivate(n, "expecting an integer subterm");
      }
    }
  }
  switch (k)
  {
    case kind::TO_REAL:
    case kind::CAST_TO_REAL: return realType;
    case kind::TO_INTEGER: return integerType;
    default:
    {
      bool isDivision = k == kind::DIVISION || k == kind::DIVISION_TOTAL;
      return (isInteger && !isDivision ? integerType : realType);
    }
  }
}

TypeNode ArithRelationTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check)
{
  if (check)
  {
    Assert(n.getNumChildren() == 2);
    TypeNode t1 = n[0].getType(check);
    if (!t1.isRealOrInt())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting an arithmetic term for arithmetic relation");
    }
    TypeNode t2 = n[1].getType(check);
    if (!t1.isComparableTo(t2))
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting arithmetic terms of comparable type");
    }
  }
  return nodeManager->booleanType();
}

TypeNode RealNullaryOperatorTypeRule::computeType(NodeManager* nodeManager,
                                                  TNode n,
                                                  bool check)
{
  // for nullary operators, we only computeType for check=true, since they are
  // given TypeAttr() on creation
  Assert(check);
  TypeNode realType = n.getType();
  if (realType != NodeManager::currentNM()->realType())
  {
    throw TypeCheckingExceptionPrivate(n, "expecting real type");
  }
  return realType;
}

TypeNode IAndOpTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
{
  if (n.getKind() != kind::IAND_OP)
  {
    InternalError() << "IAND_OP typerule invoked for " << n << " instead of IAND_OP kind";
  }
  TypeNode iType = nodeManager->integerType();
  std::vector<TypeNode> argTypes;
  argTypes.push_back(iType);
  argTypes.push_back(iType);
  return nodeManager->mkFunctionType(argTypes, iType);
}

TypeNode IAndTypeRule::computeType(NodeManager* nodeManager,
                                   TNode n,
                                   bool check)
{
  if (n.getKind() != kind::IAND)
  {
    InternalError() << "IAND typerule invoked for " << n << " instead of IAND kind";
  }
  if (check)
  {
    TypeNode arg1 = n[0].getType(check);
    TypeNode arg2 = n[1].getType(check);
    if (!arg1.isInteger() || !arg2.isInteger())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting integer terms");
    }
  }
  return nodeManager->integerType();
}

TypeNode Pow2TypeRule::computeType(NodeManager* nodeManager,
                                   TNode n,
                                   bool check)
{
  if (n.getKind() != kind::POW2)
  {
    InternalError() << "POW2 typerule invoked for " << n << " instead of POW2 kind";
  }
  if (check)
  {
    TypeNode arg1 = n[0].getType(check);
    if (!arg1.isInteger())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting integer terms");
    }
  }
  return nodeManager->integerType();
}

TypeNode IndexedRootPredicateTypeRule::computeType(NodeManager* nodeManager,
                                                   TNode n,
                                                   bool check)
{
  if (check)
  {
    TypeNode t1 = n[0].getType(check);
    if (!t1.isBoolean())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting boolean term as first argument");
    }
    TypeNode t2 = n[1].getType(check);
    if (!t2.isRealOrInt())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting polynomial as second argument");
    }
  }
  return nodeManager->booleanType();
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5
