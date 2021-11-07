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

#include "expr/cardinality_constraint.h"
#include "theory/uf/function_const.h"
#include "util/cardinality.h"
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

TypeNode CardinalityConstraintOpTypeRule::computeType(NodeManager* nodeManager,
                                                      TNode n,
                                                      bool check)
{
  if (check)
  {
    const CardinalityConstraint& cc = n.getConst<CardinalityConstraint>();
    if (!cc.getType().isSort())
    {
      throw TypeCheckingExceptionPrivate(
          n, "cardinality constraint must apply to uninterpreted sort");
    }
    if (cc.getUpperBound().sgn() != 1)
    {
      throw TypeCheckingExceptionPrivate(
          n, "cardinality constraint must be positive");
    }
  }
  return nodeManager->booleanType();
}

TypeNode CardinalityConstraintTypeRule::computeType(NodeManager* nodeManager,
                                                    TNode n,
                                                    bool check)
{
  return nodeManager->booleanType();
}

TypeNode CombinedCardinalityConstraintOpTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check)
{
  if (check)
  {
    const CombinedCardinalityConstraint& cc =
        n.getConst<CombinedCardinalityConstraint>();
    if (cc.getUpperBound().sgn() != 1)
    {
      throw TypeCheckingExceptionPrivate(
          n, "combined cardinality constraint must be positive");
    }
  }
  return nodeManager->booleanType();
}

TypeNode CombinedCardinalityConstraintTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check)
{
  return nodeManager->booleanType();
}

TypeNode PartialTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check)
{
  return n.getOperator().getType().getRangeType();
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

TypeNode LambdaTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
{
  if (n[0].getType(check) != nodeManager->boundVarListType())
  {
    std::stringstream ss;
    ss << "expected a bound var list for LAMBDA expression, got `"
       << n[0].getType().toString() << "'";
    throw TypeCheckingExceptionPrivate(n, ss.str());
  }
  std::vector<TypeNode> argTypes;
  for (TNode::iterator i = n[0].begin(); i != n[0].end(); ++i)
  {
    argTypes.push_back((*i).getType());
  }
  TypeNode rangeType = n[1].getType(check);
  return nodeManager->mkFunctionType(argTypes, rangeType);
}

bool LambdaTypeRule::computeIsConst(NodeManager* nodeManager, TNode n)
{
  Assert(n.getKind() == kind::LAMBDA);
  // get array representation of this function, if possible
  Node na = FunctionConst::getArrayRepresentationForLambda(n);
  if (!na.isNull())
  {
    Assert(na.getType().isArray());
    Trace("lambda-const") << "Array representation for " << n << " is " << na
                          << " " << na.getType() << std::endl;
    // must have the standard bound variable list
    Node bvl =
        NodeManager::currentNM()->getBoundVarListForFunctionType(n.getType());
    if (bvl == n[0])
    {
      // array must be constant
      if (na.isConst())
      {
        Trace("lambda-const") << "*** Constant lambda : " << n;
        Trace("lambda-const") << " since its array representation : " << na
                              << " is constant." << std::endl;
        return true;
      }
      else
      {
        Trace("lambda-const") << "Non-constant lambda : " << n
                              << " since array is not constant." << std::endl;
      }
    }
    else
    {
      Trace("lambda-const")
          << "Non-constant lambda : " << n
          << " since its varlist is not standard." << std::endl;
      Trace("lambda-const") << "  standard : " << bvl << std::endl;
      Trace("lambda-const") << "   current : " << n[0] << std::endl;
    }
  }
  else
  {
    Trace("lambda-const") << "Non-constant lambda : " << n
                          << " since it has no array representation."
                          << std::endl;
  }
  return false;
}

Cardinality FunctionProperties::computeCardinality(TypeNode type)
{
  // Don't assert this; allow other theories to use this cardinality
  // computation.
  //
  // Assert(type.getKind() == kind::FUNCTION_TYPE);

  Cardinality argsCard(1);
  // get the largest cardinality of function arguments/return type
  for (size_t i = 0, i_end = type.getNumChildren() - 1; i < i_end; ++i)
  {
    argsCard *= type[i].getCardinality();
  }

  Cardinality valueCard = type[type.getNumChildren() - 1].getCardinality();

  return valueCard ^ argsCard;
}

bool FunctionProperties::isWellFounded(TypeNode type)
{
  for (TypeNode::iterator i = type.begin(), i_end = type.end(); i != i_end; ++i)
  {
    if (!(*i).isWellFounded())
    {
      return false;
    }
  }
  return true;
}

Node FunctionProperties::mkGroundTerm(TypeNode type)
{
  NodeManager* nm = NodeManager::currentNM();
  Node bvl = nm->getBoundVarListForFunctionType(type);
  Node ret = type.getRangeType().mkGroundTerm();
  return nm->mkNode(kind::LAMBDA, bvl, ret);
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5
