/******************************************************************************
 * Top contributors (to current version):
 *   Yancheng Ou, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The base class for optimizers of individual cvc5 type.
 */

#include "omt/omt_optimizer.h"

#include "omt/bitvector_optimizer.h"
#include "omt/integer_optimizer.h"

using namespace cvc5::internal::theory;
using namespace cvc5::internal::smt;
namespace cvc5::internal::omt {

bool OMTOptimizer::nodeSupportsOptimization(TNode node)
{
  TypeNode type = node.getType();
  // only supports Integer and BitVectors as of now
  return (type.isInteger() || type.isBitVector());
}

std::unique_ptr<OMTOptimizer> OMTOptimizer::getOptimizerForObjective(
    const OptimizationObjective& objective)
{
  // the datatype of the target node
  TypeNode objectiveType = objective.getTarget().getType(true);
  if (objectiveType.isInteger())
  {
    // integer type: use OMTOptimizerInteger
    return std::unique_ptr<OMTOptimizer>(new OMTOptimizerInteger());
  }
  else if (objectiveType.isBitVector())
  {
    // bitvector type: use OMTOptimizerBitVector
    return std::unique_ptr<OMTOptimizer>(
        new OMTOptimizerBitVector(objective.bvIsSigned()));
  }
  else
  {
    Unimplemented() << "Target type " << objectiveType
                    << " does not support optimization";
  }
}

Node OMTOptimizer::mkStrongIncrementalExpression(
    NodeManager* nm,
    TNode lhs,
    TNode rhs,
    const OptimizationObjective& objective)
{
  constexpr const char lhsTypeError[] =
      "lhs type does not match or is not implicitly convertable to the target "
      "type";
  constexpr const char rhsTypeError[] =
      "rhs type does not match or is not implicitly convertable to the target "
      "type";
  TypeNode targetType = objective.getTarget().getType();
  switch (objective.getType())
  {
    case OptimizationObjective::MINIMIZE:
    {
      if (targetType.isInteger())
      {
        Assert(lhs.getType().isInteger()) << lhsTypeError;
        Assert(rhs.getType().isInteger()) << rhsTypeError;
        return nm->mkNode(Kind::LT, lhs, rhs);
      }
      else if (targetType.isBitVector())
      {
        Assert(lhs.getType() == targetType) << lhsTypeError;
        Assert(rhs.getType() == targetType) << rhsTypeError;
        return (objective.bvIsSigned())
                   ? (nm->mkNode(Kind::BITVECTOR_SLT, lhs, rhs))
                   : (nm->mkNode(Kind::BITVECTOR_ULT, lhs, rhs));
      }
      else
      {
        Unimplemented() << "Target type " << targetType
                        << " does not support optimization";
      }
    }
    case OptimizationObjective::MAXIMIZE:
    {
      if (targetType.isInteger())
      {
        Assert(lhs.getType().isInteger()) << lhsTypeError;
        Assert(rhs.getType().isInteger()) << rhsTypeError;
        return nm->mkNode(Kind::GT, lhs, rhs);
      }
      else if (targetType.isBitVector())
      {
        Assert(lhs.getType() == targetType) << lhsTypeError;
        Assert(rhs.getType() == targetType) << rhsTypeError;
        return (objective.bvIsSigned())
                   ? (nm->mkNode(Kind::BITVECTOR_SGT, lhs, rhs))
                   : (nm->mkNode(Kind::BITVECTOR_UGT, lhs, rhs));
      }
      else
      {
        Unimplemented() << "Target type " << targetType
                        << " does not support optimization";
      }
    }
    default:
      CVC5_FATAL() << "Optimization objective is neither MAXIMIZE nor MINIMIZE";
  }
  Unreachable();
}

Node OMTOptimizer::mkWeakIncrementalExpression(
    NodeManager* nm,
    TNode lhs,
    TNode rhs,
    const OptimizationObjective& objective)
{
  constexpr const char lhsTypeError[] =
      "lhs type does not match or is not implicitly convertable to the target "
      "type";
  constexpr const char rhsTypeError[] =
      "rhs type does not match or is not implicitly convertable to the target "
      "type";
  TypeNode targetType = objective.getTarget().getType();
  switch (objective.getType())
  {
    case OptimizationObjective::MINIMIZE:
    {
      if (targetType.isInteger())
      {
        Assert(lhs.getType().isInteger()) << lhsTypeError;
        Assert(rhs.getType().isInteger()) << rhsTypeError;
        return nm->mkNode(Kind::LEQ, lhs, rhs);
      }
      else if (targetType.isBitVector())
      {
        Assert(lhs.getType() == targetType) << lhsTypeError;
        Assert(rhs.getType() == targetType) << rhsTypeError;
        return (objective.bvIsSigned())
                   ? (nm->mkNode(Kind::BITVECTOR_SLE, lhs, rhs))
                   : (nm->mkNode(Kind::BITVECTOR_ULE, lhs, rhs));
      }
      else
      {
        Unimplemented() << "Target type " << targetType
                        << " does not support optimization";
      }
    }
    case OptimizationObjective::MAXIMIZE:
    {
      if (targetType.isInteger())
      {
        Assert(lhs.getType().isInteger()) << lhsTypeError;
        Assert(rhs.getType().isInteger()) << rhsTypeError;
        return nm->mkNode(Kind::GEQ, lhs, rhs);
      }
      else if (targetType.isBitVector())
      {
        Assert(lhs.getType() == targetType) << lhsTypeError;
        Assert(rhs.getType() == targetType) << rhsTypeError;
        return (objective.bvIsSigned())
                   ? (nm->mkNode(Kind::BITVECTOR_SGE, lhs, rhs))
                   : (nm->mkNode(Kind::BITVECTOR_UGE, lhs, rhs));
      }
      else
      {
        Unimplemented() << "Target type " << targetType
                        << " does not support optimization";
      }
    }
    default:
      CVC5_FATAL() << "Optimization objective is neither MAXIMIZE nor MINIMIZE";
  }
  Unreachable();
}

}  // namespace cvc5::internal::omt
