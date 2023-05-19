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
      if (currentArgument != currentArgumentType)
      {
        std::stringstream ss;
        ss << "argument type is not the type of the function's argument "
           << "type:\n"
           << "argument:  " << *argument_it << "\n"
           << "has type:  " << (*argument_it).getType() << "\n"
           << "not type: " << *argument_type_it << "\n"
           << "in term : " << n;
        throw TypeCheckingExceptionPrivate(n, ss.str());
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
      throw TypeCheckingExceptionPrivate(
          n, "cardinality constraint must apply to uninterpreted sort");
    }
    if (cc.getUpperBound().sgn() != 1)
    {
      throw TypeCheckingExceptionPrivate(
          n, "cardinality constraint must be positive");
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
      throw TypeCheckingExceptionPrivate(
          n, "combined cardinality constraint must be positive");
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
    if (aType != fType[0])
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

TypeNode LambdaTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode LambdaTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
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

TypeNode FunctionArrayConstTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode FunctionArrayConstTypeRule::computeType(NodeManager* nodeManager,
                                                 TNode n,
                                                 bool check,
                                                 std::ostream* errOut)
{
  Assert(n.getKind() == kind::FUNCTION_ARRAY_CONST);
  const FunctionArrayConst& fc = n.getConst<FunctionArrayConst>();
  return fc.getType();
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
  Node ret = nm->mkGroundTerm(type.getRangeType());
  return nm->mkNode(kind::LAMBDA, bvl, ret);
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
  Assert(n.getKind() == kind::INT_TO_BITVECTOR_OP);
  size_t bvSize = n.getConst<IntToBitVector>();
  if (bvSize == 0)
  {
    throw TypeCheckingExceptionPrivate(n, "expecting bit-width > 0");
  }
  return nodeManager->builtinOperatorType();
}

TypeNode BitVectorConversionTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  if (n.getKind() == kind::BITVECTOR_TO_NAT)
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
  if (n.getKind() == kind::BITVECTOR_TO_NAT)
  {
    if (check && !n[0].getType(check).isBitVector())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
    }
    return nodeManager->integerType();
  }

  Assert(n.getKind() == kind::INT_TO_BITVECTOR);
  size_t bvSize = n.getOperator().getConst<IntToBitVector>();
  if (check && !n[0].getType(check).isInteger())
  {
    throw TypeCheckingExceptionPrivate(n, "expecting integer term");
  }
  return nodeManager->mkBitVectorType(bvSize);
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
