/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
#include "expr/function_array_const.h"
#include "theory/uf/function_const.h"
#include "util/bitvector.h"
#include "util/cardinality.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace uf {

TypeNode UfTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode UfTypeRule::computeType(NodeManager* nodeManager,
                                 TNode n,
                                 bool check,
                                 std::ostream* errOut)
{
  TNode f = n.getOperator();
  TypeNode fType = f.getTypeOrNull();
  if (!fType.isFunction())
  {
    // if it is not even maybe a function type
    if (!fType.isMaybeKind(Kind::FUNCTION_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "operator does not have function type";
      }
      return TypeNode::null();
    }
    // otherwise, application of abstract function is always abstract
    return nodeManager->mkAbstractType(Kind::ABSTRACT_TYPE);
  }
  if (check)
  {
    if (n.getNumChildren() != fType.getNumChildren() - 1)
    {
      if (errOut)
      {
        (*errOut) << "number of arguments does not match the function type";
      }
      return TypeNode::null();
    }
    TNode::iterator argument_it = n.begin();
    TNode::iterator argument_it_end = n.end();
    TypeNode::iterator argument_type_it = fType.begin();
    for (; argument_it != argument_it_end; ++argument_it, ++argument_type_it)
    {
      TypeNode currentArgument = (*argument_it).getTypeOrNull();
      TypeNode currentArgumentType = *argument_type_it;
      if (!currentArgument.isComparableTo(currentArgumentType))
      {
        if (errOut)
        {
          (*errOut)
              << "argument type is not the type of the function's argument "
              << "type:\n"
              << "argument:  " << *argument_it << "\n"
              << "has type:  " << (*argument_it).getTypeOrNull() << "\n"
              << "not type: " << *argument_type_it << "\n"
              << "in term : " << n;
        }
        return TypeNode::null();
      }
    }
  }
  return fType.getRangeType();
}

TypeNode CardinalityConstraintOpTypeRule::preComputeType(NodeManager* nm,
                                                         TNode n)
{
  return TypeNode::null();
}
TypeNode CardinalityConstraintOpTypeRule::computeType(NodeManager* nodeManager,
                                                      TNode n,
                                                      bool check,
                                                      std::ostream* errOut)
{
  if (check)
  {
    const CardinalityConstraint& cc = n.getConst<CardinalityConstraint>();
    if (!cc.getType().isUninterpretedSort())
    {
      if (errOut)
      {
        (*errOut) << "cardinality constraint must apply to uninterpreted sort";
      }
      return TypeNode::null();
    }
    if (cc.getUpperBound().sgn() != 1)
    {
      if (errOut)
      {
        (*errOut) << "cardinality constraint must be positive";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->builtinOperatorType();
}

TypeNode CombinedCardinalityConstraintOpTypeRule::preComputeType(
    NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode CombinedCardinalityConstraintOpTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check, std::ostream* errOut)
{
  if (check)
  {
    const CombinedCardinalityConstraint& cc =
        n.getConst<CombinedCardinalityConstraint>();
    if (cc.getUpperBound().sgn() != 1)
    {
      if (errOut)
      {
        (*errOut) << "combined cardinality constraint must be positive";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->builtinOperatorType();
}

TypeNode HoApplyTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}

TypeNode HoApplyTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check,
                                      std::ostream* errOut)
{
  Assert(n.getKind() == Kind::HO_APPLY);
  TypeNode fType = n[0].getTypeOrNull();
  if (!fType.isFunction())
  {
    // if it is not even maybe a function type
    if (!fType.isMaybeKind(Kind::FUNCTION_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "first argument does not have function type";
      }
      return TypeNode::null();
    }
    // otherwise, application of abstract function is always abstract
    return nodeManager->mkAbstractType(Kind::ABSTRACT_TYPE);
  }
  Assert(fType.getNumChildren() >= 2);
  if (check)
  {
    TypeNode aType = n[1].getTypeOrNull();
    if (!aType.isComparableTo(fType[0]))
    {
      if (errOut)
      {
        (*errOut) << "argument does not match function type";
      }
      return TypeNode::null();
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

TypeNode LambdaTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode LambdaTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  if (n[0].getTypeOrNull() != nodeManager->boundVarListType())
  {
    if (errOut)
    {
      (*errOut) << "expected a bound var list for LAMBDA expression, got `"
                << n[0].getTypeOrNull().toString() << "'";
    }
    return TypeNode::null();
  }
  std::vector<TypeNode> argTypes;
  for (TNode::iterator i = n[0].begin(); i != n[0].end(); ++i)
  {
    argTypes.push_back((*i).getTypeOrNull());
  }
  TypeNode rangeType = n[1].getTypeOrNull();
  return nodeManager->mkFunctionType(argTypes, rangeType);
}

TypeNode FunctionArrayConstTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode FunctionArrayConstTypeRule::computeType(NodeManager* nodeManager,
                                                 TNode n,
                                                 bool check,
                                                 std::ostream* errOut)
{
  Assert(n.getKind() == Kind::FUNCTION_ARRAY_CONST);
  const FunctionArrayConst& fc = n.getConst<FunctionArrayConst>();
  return fc.getType();
}

Cardinality FunctionProperties::computeCardinality(TypeNode type)
{
  // Don't assert this; allow other theories to use this cardinality
  // computation.
  //
  // Assert(type.getKind() == Kind::FUNCTION_TYPE);

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
  Node ret = nm->mkGroundTerm(type.getRangeType());
  return nm->mkNode(Kind::LAMBDA, bvl, ret);
}

TypeNode IntToBitVectorOpTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode IntToBitVectorOpTypeRule::computeType(NodeManager* nodeManager,
                                               TNode n,
                                               bool check,
                                               std::ostream* errOut)
{
  Assert(n.getKind() == Kind::INT_TO_BITVECTOR_OP);
  size_t bvSize = n.getConst<IntToBitVector>();
  if (bvSize == 0)
  {
    if (errOut)
    {
      (*errOut) << "expecting bit-width > 0";
    }
    return TypeNode::null();
  }
  return nodeManager->builtinOperatorType();
}

TypeNode BitVectorConversionTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  if (n.getKind() == Kind::BITVECTOR_TO_NAT)
  {
    return nm->integerType();
  }
  size_t bvSize = n.getOperator().getConst<IntToBitVector>();
  return nm->mkBitVectorType(bvSize);
}
TypeNode BitVectorConversionTypeRule::computeType(NodeManager* nodeManager,
                                                  TNode n,
                                                  bool check,
                                                  std::ostream* errOut)
{
  if (n.getKind() == Kind::BITVECTOR_TO_NAT)
  {
    if (check && !n[0].getTypeOrNull().isMaybeKind(Kind::BITVECTOR_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "expecting bit-vector term";
      }
      return TypeNode::null();
    }
    return nodeManager->integerType();
  }
  Assert(n.getKind() == Kind::INT_TO_BITVECTOR);
  size_t bvSize = n.getOperator().getConst<IntToBitVector>();
  TypeNode tn = n[0].getTypeOrNull();
  if (check && !tn.isInteger() && !tn.isFullyAbstract())
  {
    if (errOut)
    {
      (*errOut) << "expecting integer term";
    }
    return TypeNode::null();
  }
  return nodeManager->mkBitVectorType(bvSize);
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
