/*********************                                                        */
/*! \file optimization_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Michael Chang, Yancheng Ou
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The solver for optimization queries
 **/

#include "smt/optimization_solver.h"

#include "options/smt_options.h"
#include "smt/smt_engine.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/smt_engine_subsolver.h"

using namespace CVC4::theory;

namespace CVC4 {
namespace smt {

/**
 * d_activatedObjective is initialized to a default objective:
 * default objective constructed with Null Node and OBJECTIVE_UNDEFINED
 *
 * d_savedValue is initialized to a default node (Null Node)
 */

OptimizationSolver::OptimizationSolver(SmtEngine* parent)
    : d_parent(parent),
      d_activatedObjective(Node(), OBJECTIVE_UNDEFINED),
      d_savedValue()
{
}

OptimizationSolver::~OptimizationSolver() {}

OptResult OptimizationSolver::checkOpt()
{
  // Make sure that the objective is not the default one
  Assert(d_activatedObjective.getType() != OBJECTIVE_UNDEFINED);
  Assert(!d_activatedObjective.getNode().isNull());

  std::unique_ptr<OMTOptimizer> optimizer = OMTOptimizer::getOptimizerForNode(
      d_activatedObjective.getNode(), d_activatedObjective.getSigned());

  Assert(optimizer != nullptr);

  std::pair<OptResult, Node> optResult;
  if (d_activatedObjective.getType() == OBJECTIVE_MAXIMIZE)
  {
    optResult = optimizer->maximize(this->d_parent,
                                    this->d_activatedObjective.getNode());
  }
  else if (d_activatedObjective.getType() == OBJECTIVE_MINIMIZE)
  {
    optResult = optimizer->minimize(this->d_parent,
                                    this->d_activatedObjective.getNode());
  }

  this->d_savedValue = optResult.second;
  return optResult.first;
}

void OptimizationSolver::activateObj(const Node& obj,
                                     const int& type,
                                     bool bvSigned)
{
  d_activatedObjective = Objective(obj, (ObjectiveType)type, bvSigned);
}

Node OptimizationSolver::objectiveGetValue()
{
  Assert(!d_savedValue.isNull());
  return d_savedValue;
}

Objective::Objective(Node obj, ObjectiveType type, bool bvSigned)
    : d_type(type), d_node(obj), d_bvSigned(bvSigned)
{
}

ObjectiveType Objective::getType() { return d_type; }

Node Objective::getNode() { return d_node; }

bool Objective::getSigned() { return d_bvSigned; }

std::pair<OptResult, Node> OMTOptimizerInteger::optimize(
    SmtEngine* parentSMTSolver, Node target, ObjectiveType objType)
{
  // linear search for integer goal
  // the smt engine to which we send intermediate queries
  // for the linear search.
  std::unique_ptr<SmtEngine> optChecker;
  CVC4::theory::initializeSubsolver(optChecker);
  NodeManager* nm = optChecker->getNodeManager();
  // we need to be in incremental mode for multiple objectives since we need to
  // push pop we need to produce models to inrement on our objective
  optChecker->setOption("incremental", "true");
  optChecker->setOption("produce-models", "true");
  // Move assertions from the parent solver to the subsolver
  std::vector<Node> p_assertions = parentSMTSolver->getExpandedAssertions();
  for (const Node& e : p_assertions)
  {
    optChecker->assertFormula(e);
  }

  Result intermediateSatResult = optChecker->checkSat();
  // Model-value of objective (used in optimization loop)
  Node value;
  if (intermediateSatResult.isUnknown())
  {
    return std::make_pair(OptResult::OPT_UNKNOWN, value);
  }
  if (!intermediateSatResult.isSat())
  {
    return std::make_pair(OptResult::OPT_UNSAT, value);
  }
  // asserts objective > old_value (used in optimization loop)
  Node increment;
  Kind incrementalOperator = kind::NULL_EXPR;
  if (objType == ObjectiveType::OBJECTIVE_MINIMIZE)
  {
    // if objective is MIN, then assert optimization_target <
    // current_model_value
    incrementalOperator = kind::LT;
  }
  else if (objType == ObjectiveType::OBJECTIVE_MAXIMIZE)
  {
    // if objective is MAX, then assert optimization_target >
    // current_model_value
    incrementalOperator = kind::GT;
  }
  // Workhorse of linear search:
  // This loop will keep incrmenting/decrementing the objective until unsat
  // When unsat is hit,
  // the optimized value is the model value just before the unsat call
  while (intermediateSatResult.isSat())
  {
    value = optChecker->getValue(target);
    Assert(!value.isNull());
    increment = nm->mkNode(incrementalOperator, target, value);
    optChecker->assertFormula(increment);
    intermediateSatResult = optChecker->checkSat();
  }
  return std::make_pair(OptResult::OPT_OPTIMAL, value);
}

std::pair<OptResult, Node> OMTOptimizerInteger::minimize(
    SmtEngine* parentSMTSolver, Node target)
{
  return this->optimize(
      parentSMTSolver, target, ObjectiveType::OBJECTIVE_MINIMIZE);
}
std::pair<OptResult, Node> OMTOptimizerInteger::maximize(
    SmtEngine* parentSMTSolver, Node target)
{
  return this->optimize(
      parentSMTSolver, target, ObjectiveType::OBJECTIVE_MAXIMIZE);
}

OMTOptimizerBitVector::OMTOptimizerBitVector(bool isSigned)
    : d_isSigned(isSigned)
{
}

BitVector OMTOptimizerBitVector::computeAverage(const BitVector& a,
                                                const BitVector& b,
                                                bool isSigned)
{
  // computes (a + b) / 2 without overflow
  // rounding towards -infinity: -1.5 --> -2,  1.5 --> 1
  // average = (a / 2) + (b / 2) + (((a % 2) + (b % 2)) / 2)
  // Assert(a.getSize() == b.getSize());
  uint32_t aMod2 = (uint32_t)(a.isBitSet(0));
  uint32_t bMod2 = (uint32_t)(b.isBitSet(0));
  BitVector aMod2PlusbMod2(a.getSize(), uint32_t((aMod2 + bMod2) / 2));
  BitVector bv1(a.getSize(), (uint32_t)1);
  if (isSigned)
  {
    return (a.arithRightShift(bv1) + b.arithRightShift(bv1)
            + aMod2PlusbMod2.arithRightShift(bv1));
  }
  else
  {
    return (a.logicalRightShift(bv1) + b.logicalRightShift(bv1)
            + aMod2PlusbMod2.logicalRightShift(bv1));
  }
}

std::unique_ptr<SmtEngine> OMTOptimizerBitVector::initOptChecker(
    SmtEngine* parentSMTSolver)
{
  std::unique_ptr<SmtEngine> optChecker;
  CVC4::theory::initializeSubsolver(optChecker);
  // we need to be in incremental mode for multiple objectives since we need to
  // push pop we need to produce models to inrement on our objective
  optChecker->setOption("incremental", "true");
  optChecker->setOption("produce-models", "true");
  // Move assertions from the parent solver to the subsolver
  std::vector<Node> p_assertions = parentSMTSolver->getExpandedAssertions();
  for (const Node& e : p_assertions)
  {
    optChecker->assertFormula(e);
  }
  return optChecker;
}

std::pair<OptResult, Node> OMTOptimizerBitVector::minimize(
    SmtEngine* parentSMTSolver, Node target)
{
  // the smt engine to which we send intermediate queries
  // for the binary search.
  std::unique_ptr<SmtEngine> optChecker = initOptChecker(parentSMTSolver);
  NodeManager* nm = optChecker->getNodeManager();
  Result intermediateSatResult = optChecker->checkSat();
  // Model-value of objective (used in optimization loop)
  Node value;
  if (intermediateSatResult.isUnknown())
  {
    return std::make_pair(OptResult::OPT_UNKNOWN, value);
  }
  if (!intermediateSatResult.isSat())
  {
    return std::make_pair(OptResult::OPT_UNSAT, value);
  }

  // value equals to upperBound
  value = optChecker->getValue(target);

  // this gets the bitvector!
  BitVector bvValue = value.getConst<BitVector>();
  unsigned int bvSize = bvValue.getSize();

  // lowerbound
  BitVector lowerBound = ((this->d_isSigned) ? (BitVector::mkMinSigned(bvSize))
                                             : (BitVector::mkZero(bvSize)));
  // upperbound must be a satisfying value
  // and value == upperbound
  BitVector upperBound = bvValue;

  Kind LTOperator =
      ((d_isSigned) ? (kind::BITVECTOR_SLT) : (kind::BITVECTOR_ULT));
  Kind GEOperator =
      ((d_isSigned) ? (kind::BITVECTOR_SGE) : (kind::BITVECTOR_UGE));
  BitVector pivot;
  while (true)
  {
    if (d_isSigned)
    {
      if (!lowerBound.signedLessThan(upperBound)) break;
    }
    else
    {
      if (!lowerBound.unsignedLessThan(upperBound)) break;
    }
    pivot = computeAverage(lowerBound, upperBound, d_isSigned);
    optChecker->push();
    // lowerBound <= target < pivot
    optChecker->assertFormula(
        nm->mkNode(kind::AND,
                   nm->mkNode(GEOperator, target, nm->mkConst(lowerBound)),
                   nm->mkNode(LTOperator, target, nm->mkConst(pivot))));
    intermediateSatResult = optChecker->checkSat();
    if (intermediateSatResult.isUnknown() || intermediateSatResult.isNull())
    {
      return std::make_pair(OptResult::OPT_UNKNOWN, value);
    }
    if (intermediateSatResult.isSat() == Result::SAT)
    {
      value = optChecker->getValue(target);
      upperBound = value.getConst<BitVector>();
    }
    else if (intermediateSatResult.isSat() == Result::UNSAT)
    {
      if (lowerBound == pivot)
      {
        // lowerBound == pivot ==> upperbound = lowerbound + 1
        // and lowerbound <= target < upperbound is UNSAT
        // return the upperbound
        return std::make_pair(OptResult::OPT_OPTIMAL, value);
      }
      else
      {
        lowerBound = pivot;
      }
    }
    else
    {
      return std::make_pair(OptResult::OPT_UNKNOWN, value);
    }
    optChecker->pop();
  }
  return std::make_pair(OptResult::OPT_OPTIMAL, value);
}

std::pair<OptResult, Node> OMTOptimizerBitVector::maximize(
    SmtEngine* parentSMTSolver, Node target)
{
  // the smt engine to which we send intermediate queries
  // for the binary search.
  std::unique_ptr<SmtEngine> optChecker = initOptChecker(parentSMTSolver);
  NodeManager* nm = optChecker->getNodeManager();
  Result intermediateSatResult = optChecker->checkSat();
  // Model-value of objective (used in optimization loop)
  Node value;
  if (intermediateSatResult.isUnknown())
  {
    return std::make_pair(OptResult::OPT_UNKNOWN, value);
  }
  if (!intermediateSatResult.isSat())
  {
    return std::make_pair(OptResult::OPT_UNSAT, value);
  }

  // value equals to upperBound
  value = optChecker->getValue(target);

  // this gets the bitvector!
  BitVector bvValue = value.getConst<BitVector>();
  unsigned int bvSize = bvValue.getSize();
  // BitVector bv1 = BitVector::mkOne(bvSize);

  // lowerbound must be a satisfying value
  // and value == lowerbound
  BitVector lowerBound = bvValue;

  // upperbound
  BitVector upperBound = ((this->d_isSigned) ? (BitVector::mkMaxSigned(bvSize))
                                             : (BitVector::mkOnes(bvSize)));

  Kind LEOperator =
      ((d_isSigned) ? (kind::BITVECTOR_SLE) : (kind::BITVECTOR_ULE));
  Kind GTOperator =
      ((d_isSigned) ? (kind::BITVECTOR_SGT) : (kind::BITVECTOR_UGT));
  BitVector pivot;
  while (true)
  {
    if (d_isSigned)
    {
      if (!lowerBound.signedLessThan(upperBound)) break;
    }
    else
    {
      if (!lowerBound.unsignedLessThan(upperBound)) break;
    }
    pivot = computeAverage(lowerBound, upperBound, d_isSigned);

    optChecker->push();
    // pivot < target <= upperBound
    optChecker->assertFormula(
        nm->mkNode(kind::AND,
                   nm->mkNode(GTOperator, target, nm->mkConst(pivot)),
                   nm->mkNode(LEOperator, target, nm->mkConst(upperBound))));
    intermediateSatResult = optChecker->checkSat();
    if (intermediateSatResult.isUnknown() || intermediateSatResult.isNull())
    {
      return std::make_pair(OptResult::OPT_UNKNOWN, value);
    }
    if (intermediateSatResult.isSat() == Result::SAT)
    {
      value = optChecker->getValue(target);
      lowerBound = value.getConst<BitVector>();
    }
    else if (intermediateSatResult.isSat() == Result::UNSAT)
    {
      if (lowerBound == pivot)
      {
        // upperbound = lowerbound + 1
        // and lowerbound < target <= upperbound is UNSAT
        // return the lowerbound
        return std::make_pair(OptResult::OPT_OPTIMAL, value);
      }
      else
      {
        upperBound = pivot;
      }
    }
    else
    {
      return std::make_pair(OptResult::OPT_UNKNOWN, value);
    }
    optChecker->pop();
  }
  return std::make_pair(OptResult::OPT_OPTIMAL, value);
}

std::unique_ptr<OMTOptimizer> OMTOptimizer::getOptimizerForNode(Node targetNode,
                                                                bool isSigned)
{
  // the datatype of the target node
  TypeNode objectiveType = targetNode.getType(true);
  if (objectiveType.isInteger())
  {
    // integer type: use OMTOptimizerInteger
    return std::unique_ptr<OMTOptimizer>(new OMTOptimizerInteger());
  }
  else if (objectiveType.isBitVector())
  {
    // bitvector type: use OMTOptimizerBitVector
    return std::unique_ptr<OMTOptimizer>(new OMTOptimizerBitVector(isSigned));
  }
  else
  {
    return nullptr;
  }
}

}  // namespace smt
}  // namespace CVC4
