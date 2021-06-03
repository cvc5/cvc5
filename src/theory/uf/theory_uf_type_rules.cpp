/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Typing and cardinality rules for the theory of UF.
 */

#include "theory/uf/theory_uf_type_rules.h"

#include <climits>
#include <sstream>

#include "util/rational.h"

namespace cvc5 {
namespace theory {
namespace uf {

TypeNode UfTypeRule::computeType(NodeManager* nodeManager, TNode n, bool check)
{
  TNode f = n.getOperator();
  TypeNode fType = f.getType(check);
  if (!fType.isFunction())
  {
    throw TypeCheckingExceptionPrivate(n,
                                       "operator does not have function type");
  }
  if (check)
  {
    if (n.getNumChildren() != fType.getNumChildren() - 1)
    {
      throw TypeCheckingExceptionPrivate(
          n, "number of arguments does not match the function type");
    }
    TNode::iterator argument_it = n.begin();
    TNode::iterator argument_it_end = n.end();
    TypeNode::iterator argument_type_it = fType.begin();
    for (; argument_it != argument_it_end; ++argument_it, ++argument_type_it)
    {
      TypeNode currentArgument = (*argument_it).getType();
      TypeNode currentArgumentType = *argument_type_it;
      if (!currentArgument.isSubtypeOf(currentArgumentType))
      {
        std::stringstream ss;
        ss << "argument type is not a subtype of the function's argument "
           << "type:\n"
           << "argument:  " << *argument_it << "\n"
           << "has type:  " << (*argument_it).getType() << "\n"
           << "not subtype: " << *argument_type_it << "\n"
           << "in term : " << n;
        throw TypeCheckingExceptionPrivate(n, ss.str());
      }
    }
  }
  return fType.getRangeType();
}

TypeNode CardinalityConstraintTypeRule::computeType(NodeManager* nodeManager,
                                                    TNode n,
                                                    bool check)
{
  if (check)
  {
    // don't care what it is, but it should be well-typed
    n[0].getType(check);

    TypeNode valType = n[1].getType(check);
    if (valType != nodeManager->integerType())
    {
      throw TypeCheckingExceptionPrivate(
          n, "cardinality constraint must be integer");
    }
    if (n[1].getKind() != kind::CONST_RATIONAL)
    {
      throw TypeCheckingExceptionPrivate(
          n, "cardinality constraint must be a constant");
    }
    cvc5::Rational r(INT_MAX);
    if (n[1].getConst<Rational>() > r)
    {
      throw TypeCheckingExceptionPrivate(
          n, "Exceeded INT_MAX in cardinality constraint");
    }
    if (n[1].getConst<Rational>().getNumerator().sgn() != 1)
    {
      throw TypeCheckingExceptionPrivate(
          n, "cardinality constraint must be positive");
    }
  }
  return nodeManager->booleanType();
}

TypeNode CombinedCardinalityConstraintTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check)
{
  if (check)
  {
    TypeNode valType = n[0].getType(check);
    if (valType != nodeManager->integerType())
    {
      throw TypeCheckingExceptionPrivate(
          n, "combined cardinality constraint must be integer");
    }
    if (n[0].getKind() != kind::CONST_RATIONAL)
    {
      throw TypeCheckingExceptionPrivate(
          n, "combined cardinality constraint must be a constant");
    }
    cvc5::Rational r(INT_MAX);
    if (n[0].getConst<Rational>() > r)
    {
      throw TypeCheckingExceptionPrivate(
          n, "Exceeded INT_MAX in combined cardinality constraint");
    }
    if (n[0].getConst<Rational>().getNumerator().sgn() == -1)
    {
      throw TypeCheckingExceptionPrivate(
          n, "combined cardinality constraint must be non-negative");
    }
  }
  return nodeManager->booleanType();
}

TypeNode PartialTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check)
{
  return n.getOperator().getType().getRangeType();
}

TypeNode CardinalityValueTypeRule::computeType(NodeManager* nodeManager,
                                               TNode n,
                                               bool check)
{
  if (check)
  {
    n[0].getType(check);
  }
  return nodeManager->integerType();
}

TypeNode HoApplyTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check)
{
  Assert(n.getKind() == kind::HO_APPLY);
  TypeNode fType = n[0].getType(check);
  if (!fType.isFunction())
  {
    throw TypeCheckingExceptionPrivate(
        n, "first argument does not have function type");
  }
  Assert(fType.getNumChildren() >= 2);
  if (check)
  {
    TypeNode aType = n[1].getType(check);
    if (!aType.isSubtypeOf(fType[0]))
    {
      throw TypeCheckingExceptionPrivate(
          n, "argument does not match function type");
    }
  }
  if (fType.getNumChildren() == 2)
  {
    return fType.getRangeType();
  }
  else
  {
    std::vector<TypeNode> children;
    TypeNode::iterator argument_type_it = fType.begin();
    TypeNode::iterator argument_type_it_end = fType.end();
    ++argument_type_it;
    for (; argument_type_it != argument_type_it_end; ++argument_type_it)
    {
      children.push_back(*argument_type_it);
    }
    return nodeManager->mkFunctionType(children);
  }
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5
