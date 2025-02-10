/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Typing and cardinality rules for theory arithmetic.
 */

#include "theory/arith/theory_arith_type_rules.h"

#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

bool isMaybeRealOrInt(const TypeNode& tn)
{
  return tn.isRealOrInt() || tn.isFullyAbstract();
}

bool isMaybeInteger(const TypeNode& tn)
{
  return tn.isInteger() || tn.isFullyAbstract();
}

TypeNode ArithConstantTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode ArithConstantTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check,
                                            std::ostream* errOut)
{
  // we use different kinds for constant integers and reals
  if (n.getKind() == Kind::CONST_RATIONAL)
  {
    // constant rationals are always real type, even if their value is integral
    return nodeManager->realType();
  }
  Assert(n.getKind() == Kind::CONST_INTEGER);
  // constant integers should always have integral value
  if (check)
  {
    if (!n.getConst<Rational>().isIntegral())
    {
      throw TypeCheckingExceptionPrivate(
          n, "making an integer constant from a non-integral rational");
      return TypeNode::null();
    }
  }
  return nodeManager->integerType();
}

TypeNode ArithRealAlgebraicNumberOpTypeRule::preComputeType(NodeManager* nm,
                                                            TNode n)
{
  return nm->realType();
}
TypeNode ArithRealAlgebraicNumberOpTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check, std::ostream* errOut)
{
  return nodeManager->realType();
}
TypeNode ArithRealAlgebraicNumberTypeRule::preComputeType(NodeManager* nm,
                                                          TNode n)
{
  return nm->realType();
}
TypeNode ArithRealAlgebraicNumberTypeRule::computeType(NodeManager* nodeManager,
                                                       TNode n,
                                                       bool check,
                                                       std::ostream* errOut)
{
  return nodeManager->realType();
}

TypeNode ArithOperatorTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode ArithOperatorTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check,
                                            std::ostream* errOut)
{
  TypeNode integerType = nodeManager->integerType();
  TypeNode realType = nodeManager->realType();
  TNode::iterator child_it = n.begin();
  TNode::iterator child_it_end = n.end();
  bool isAbstract = false;
  bool isInteger = true;
  Kind k = n.getKind();
  for (; child_it != child_it_end; ++child_it)
  {
    TypeNode childType = (*child_it).getTypeOrNull();
    if (childType.isAbstract())
    {
      isAbstract = true;
    }
    else if (!childType.isInteger())
    {
      isInteger = false;
      if (!check)
      {  // if we're not checking, nothing left to do
        break;
      }
    }
    if (check)
    {
      if (!isMaybeRealOrInt(childType))
      {
        if (errOut)
        {
          (*errOut) << "expecting an arithmetic subterm";
        }
        return TypeNode::null();
      }
      if (k == Kind::TO_REAL && !childType.isInteger())
      {
        if (errOut)
        {
          (*errOut) << "expecting an integer subterm";
        }
        return TypeNode::null();
      }
    }
  }
  switch (k)
  {
    case Kind::TO_REAL:
    case Kind::DIVISION:
    case Kind::DIVISION_TOTAL: return realType;
    case Kind::TO_INTEGER: return integerType;
    default:
    {
      if (isAbstract)
      {
        // fully abstract since Int and Real are incomparable
        // NOTE: could use an abstract real???
        return nodeManager->mkAbstractType(Kind::ABSTRACT_TYPE);
      }
      return isInteger ? integerType : realType;
    }
  }
}

TypeNode ArithRelationTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode ArithRelationTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check,
                                            std::ostream* errOut)
{
  if (check)
  {
    Assert(n.getNumChildren() == 2);
    if (!isMaybeRealOrInt(n[0].getTypeOrNull())
        || !isMaybeRealOrInt(n[1].getTypeOrNull()))
    {
      if (errOut)
      {
        (*errOut) << "expecting an arithmetic subterm for arithmetic relation";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->booleanType();
}

TypeNode RealNullaryOperatorTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode RealNullaryOperatorTypeRule::computeType(NodeManager* nodeManager,
                                                  TNode n,
                                                  bool check,
                                                  std::ostream* errOut)
{
  // for nullary operators, we only computeType for check=true, since they are
  // given TypeAttr() on creation
  Assert(check);
  if (!n.getTypeOrNull().isReal())
  {
    if (errOut)
    {
      (*errOut) << "expecting real type";
    }
    return TypeNode::null();
  }
  return nodeManager->realType();
}

TypeNode IAndTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->integerType();
}
TypeNode IAndTypeRule::computeType(NodeManager* nodeManager,
                                   TNode n,
                                   bool check,
                                   std::ostream* errOut)
{
  Assert(n.getKind() == Kind::IAND)
      << "IAND typerule invoked for " << n << " instead of IAND kind";
  if (check)
  {
    TypeNode arg1 = n[0].getTypeOrNull();
    TypeNode arg2 = n[1].getTypeOrNull();
    if (!isMaybeInteger(arg1) || !isMaybeInteger(arg2))
    {
      if (errOut)
      {
        (*errOut) << "expecting integer terms";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->integerType();
}

TypeNode PowTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}

TypeNode PowTypeRule::computeType(NodeManager* nodeManager,
                                   TNode n,
                                   bool check,
                                   std::ostream* errOut)
{
  Assert (n.getKind() == Kind::POW);
  TypeNode arg1 = n[0].getTypeOrNull();
  TypeNode arg2 = n[1].getTypeOrNull();
  TypeNode t = arg1.leastUpperBound(arg2);
  if (t.isNull())
  {
    if (errOut)
    {
      (*errOut) << "expecting same arithmetic types to POW";
    }
    return TypeNode::null();
  }
  return t;
}

TypeNode IndexedRootPredicateTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode IndexedRootPredicateTypeRule::computeType(NodeManager* nodeManager,
                                                   TNode n,
                                                   bool check,
                                                   std::ostream* errOut)
{
  // used internally, does not accept arguments of abstract type
  if (check)
  {
    TypeNode t1 = n[0].getTypeOrNull();
    if (!t1.isBoolean())
    {
      if (errOut)
      {
        (*errOut) << "expecting boolean term as first argument";
      }
      return TypeNode::null();
    }
    TypeNode t2 = n[1].getTypeOrNull();
    if (!t2.isRealOrInt())
    {
      if (errOut)
      {
        (*errOut) << "expecting polynomial as second argument";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->booleanType();
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
