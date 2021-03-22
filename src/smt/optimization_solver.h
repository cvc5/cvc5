/*********************                                                        */
/*! \file optimization_solver.h
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

#include "cvc4_private.h"

#ifndef CVC4__SMT__OPTIMIZATION_SOLVER_H
#define CVC4__SMT__OPTIMIZATION_SOLVER_H

#include "expr/node.h"
#include "expr/type_node.h"
#include "smt/assertions.h"
#include "util/result.h"

#include "options/smt_options.h"
#include "smt/smt_engine.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/smt_engine_subsolver.h"

namespace CVC4 {

class SmtEngine;

namespace smt {

/**
 * An enum for optimization queries.
 *
 * Represents whether an objective should be minimized or maximized
 */
enum ObjectiveType
{
  OBJECTIVE_MINIMIZE,
  OBJECTIVE_MAXIMIZE,
  OBJECTIVE_UNDEFINED
};

/**
 * An enum for optimization queries.
 *
 * Represents the result of a checkopt query
 * (unimplemented) OPT_OPTIMAL: if value was found
 */
enum OptResult
{
  // the original set of assertions has result UNKNOWN
  OPT_UNKNOWN,
  // the original set of assertions has result UNSAT
  OPT_UNSAT,
  // the optimization loop finished and optimal
  OPT_OPTIMAL,

  // the goal is unbounded, so it would be -inf or +inf 
  OPT_UNBOUNDED, 

  // The last value is here as a preparation for future work
  // in which pproximate optimizations will be supported.

  // if the solver halted early and value is only approximate
  OPT_SAT_APPROX
};

class Objective
{
 public:
  Objective(Node n, ObjectiveType type, bool bv_is_signed_compare = true);
  ~Objective(){};

  /** A getter for d_type **/
  ObjectiveType getType();
  /** A getter for d_node **/
  Node getNode();
  /** A getter for is_signed **/
  bool getSigned();

 private:
  /** The type of objective this is, either OBJECTIVE_MAXIMIZE OR
   * OBJECTIVE_MINIMIZE  **/
  ObjectiveType d_type;
  /** The node associated to the term that was used to construct the objective.
   * **/
  Node d_node;

  /** Specify whether to use signed or unsigned comparison
   * for BitVectors (only for BitVectors), this variable is defaulted to true
   * **/
  bool d_signed;
};


/**
 * A solver for optimization queries.
 *
 * This class is responsible for responding to optmization queries. It
 * spawns a subsolver SmtEngine that captures the parent assertions and
 * implements a linear optimization loop. Supports activateObjective,
 * checkOpt, and objectiveGetValue in that order.
 */
class OptimizationSolver
{
 public:
  /** parent is the smt_solver that the user added their assertions to **/
  OptimizationSolver(SmtEngine* parent);
  ~OptimizationSolver();

  /** Runs the optimization loop for the activated objective **/
  OptResult checkOpt();
  /** Activates an objective: will be optimized for
   * Parameter is_signed specifies whether we should use signed/unsigned
   * comparison for BitVectors (only effective for BitVectors) **/
  void activateObj(const Node& obj,
                   const int& type,
                   bool bv_is_signed_compare = true);
  /** Gets the value of the optimized objective after checkopt is called **/
  Node objectiveGetValue();

//  private:
//   /** Returns the less than operator for the activated objective
//    * if objective does not support comparison, return kind::NULL_EXPR **/
//   Kind getLessThanOperatorForObjective();

 private:
  /** The parent SMT engine **/
  SmtEngine* d_parent;
  /** The objectives to optimize for **/
  Objective d_activatedObjective;
  /** A saved value of the objective from the last sat call. **/
  Node d_savedValue;
};

/**
 * Optimizer for individual datatype 
 */
struct OMTOptimizer 
{
  static std::unique_ptr<OMTOptimizer> getOptimizerForNode(CVC4::Node node, bool isSigned=false);
  virtual ~OMTOptimizer() {}
  virtual std::pair<OptResult, CVC4::Node> minimize(SmtEngine *parentSMTSolver, CVC4::Node target) = 0;
  virtual std::pair<OptResult, CVC4::Node> maximize(SmtEngine *parentSMTSolver, CVC4::Node target) = 0;
};

/**
 * The class is the optimizer implementation for individual types. 
 */
template <typename T>
struct OMTOptimizerImpl : OMTOptimizer
{ 
  virtual ~OMTOptimizerImpl() {}
  // for generic types, we couldn't optimize 
  virtual std::pair<OptResult, CVC4::Node> maximize(SmtEngine *parentSMTSolver, CVC4::Node target) override {
    return std::make_pair(OptResult::OPT_UNKNOWN, CVC4::Node());
  }
  virtual std::pair<OptResult, CVC4::Node> minimize(SmtEngine *parentSMTSolver, CVC4::Node target) override {
    return std::make_pair(OptResult::OPT_UNKNOWN, CVC4::Node());
  }
};

/**
 * The goal is of type Integer 
*/
template <>
struct OMTOptimizerImpl<Rational> : OMTOptimizer
{
public: 
  std::pair<OptResult, CVC4::Node> optimize(SmtEngine *parentSMTSolver, CVC4::Node target, ObjectiveType objType) {
    // linear search for integer goal 
    // the smt engine to which we send intermediate queries
    // for the linear search.
    std::unique_ptr<CVC4::SmtEngine> optChecker; 
    CVC4::theory::initializeSubsolver(optChecker);
    CVC4::NodeManager* nm = optChecker->getNodeManager();
    // we need to be in incremental mode for multiple objectives since we need to
    // push pop we need to produce models to inrement on our objective
    optChecker->setOption("incremental", "true");
    optChecker->setOption("produce-models", "true");
    // Move assertions from the parent solver to the subsolver
    std::vector<Node> p_assertions = parentSMTSolver->getExpandedAssertions();
    for (const Node &e : p_assertions) {
      optChecker->assertFormula(e);
    }
    CVC4::Result intermediateSatResult = optChecker->checkSat();
    // Model-value of objective (used in optimization loop)
    CVC4::Node value;
    if (intermediateSatResult.isUnknown()) {
      return std::make_pair(OptResult::OPT_UNKNOWN, value);
    }
    if (!intermediateSatResult.isSat()) {
      return std::make_pair(OptResult::OPT_UNSAT, value);
    }
    // asserts objective > old_value (used in optimization loop)
    CVC4::Node increment;
    CVC4::Kind incrementalOperator = kind::NULL_EXPR; 
    if (objType == ObjectiveType::OBJECTIVE_MINIMIZE) {
      // if objective is MIN, then assert optimization_target < current_model_value 
      incrementalOperator = kind::LT;
    } else if (objType == ObjectiveType::OBJECTIVE_MAXIMIZE) {
      // if objective is MAX, then assert optimization_target > current_model_value 
      incrementalOperator = kind::GT;
    }
    // Workhorse of linear search:
    // This loop will keep incrmenting/decrementing the objective until unsat
    // When unsat is hit, 
    // the optimized value is the model value just before the unsat call
    while (intermediateSatResult.isSat()) {
      value = optChecker->getValue(target);
      Assert(!value.isNull());
      increment = nm->mkNode(incrementalOperator, target, value);
      optChecker->assertFormula(increment);
      intermediateSatResult = optChecker->checkSat();
    }
    return std::make_pair(OptResult::OPT_OPTIMAL, value);
  }
  virtual ~OMTOptimizerImpl() {}
  virtual std::pair<OptResult, CVC4::Node> minimize(SmtEngine *parentSMTSolver, CVC4::Node target) override {
    return this->optimize(parentSMTSolver, target, ObjectiveType::OBJECTIVE_MINIMIZE);
  }
  virtual std::pair<OptResult, CVC4::Node> maximize(SmtEngine *parentSMTSolver, CVC4::Node target) override {
    return this->optimize(parentSMTSolver, target, ObjectiveType::OBJECTIVE_MAXIMIZE);
  }
};


template <>
struct OMTOptimizerImpl<BitVector> : OMTOptimizer {
private: 
  bool d_isSigned;
public: 
  OMTOptimizerImpl(bool isSigned) : 
    d_isSigned(isSigned) {}
  virtual ~OMTOptimizerImpl() {}

  BitVector computeAverage(const BitVector &a, const BitVector &b, bool isSigned) {
    // computes (a + b) / 2 without overflow 
    // rounding towards -infinity
    // average = (a / 2) + (b / 2) + (((a % 2) + (b % 2)) / 2)
    Assert(a.getSize() == b.getSize());
    uint32_t aMod2 = (uint32_t)(a.isBitSet(0));
    uint32_t bMod2 = (uint32_t)(b.isBitSet(0));
    BitVector aMod2PlusbMod2(a.getSize(), uint32_t((aMod2 + bMod2)/2));
    BitVector bv1(a.getSize(), (uint32_t)1);
    if (isSigned) {
      return (a.arithRightShift(bv1) + b.arithRightShift(bv1) + aMod2PlusbMod2.arithRightShift(bv1));
    } else {
      return (a.logicalRightShift(bv1) + b.logicalRightShift(bv1) + aMod2PlusbMod2.logicalRightShift(bv1));
    }
  }

  std::unique_ptr<CVC4::SmtEngine> initOptChecker(SmtEngine *parentSMTSolver) {
    std::unique_ptr<CVC4::SmtEngine> optChecker; 
    CVC4::theory::initializeSubsolver(optChecker);
    // we need to be in incremental mode for multiple objectives since we need to
    // push pop we need to produce models to inrement on our objective
    optChecker->setOption("incremental", "true");
    optChecker->setOption("produce-models", "true");
    // Move assertions from the parent solver to the subsolver
    std::vector<Node> p_assertions = parentSMTSolver->getExpandedAssertions();
    for (const Node &e : p_assertions) {
      optChecker->assertFormula(e);
    }
    return optChecker;
  }

  virtual std::pair<OptResult, CVC4::Node> minimize(SmtEngine *parentSMTSolver, CVC4::Node target) override {
    // the smt engine to which we send intermediate queries
    // for the linear search.
    std::unique_ptr<CVC4::SmtEngine> optChecker = initOptChecker(parentSMTSolver); 
    NodeManager* nm = optChecker->getNodeManager();
    Result intermediateSatResult = optChecker->checkSat();
    // Model-value of objective (used in optimization loop)
    Node value;
    if (intermediateSatResult.isUnknown()) {
      return std::make_pair(OptResult::OPT_UNKNOWN, value);
    }
    if (!intermediateSatResult.isSat()) {
      return std::make_pair(OptResult::OPT_UNSAT, value);
    }

    // value equals to upperBound 
    value = optChecker->getValue(target);

    // this gets the bitvector! 
    BitVector bvValue = value.getConst<BitVector>();
    unsigned int bvSize = bvValue.getSize();

    // BitVector bv1 = BitVector::mkOne(bvSize);
    

    // lowerbound
    BitVector lowerBound = ((this->d_isSigned) ? 
                            (BitVector::mkMinSigned(bvSize)) : (BitVector::mkZero(bvSize)));
    // upperbound must be a satisfying value 
    // and value == upperbound
    BitVector upperBound = bvValue;

    Kind LTOperator = ((d_isSigned) ? (kind::BITVECTOR_SLT) : (kind::BITVECTOR_ULT));
    Kind GEOperator = ((d_isSigned) ? (kind::BITVECTOR_SGE) : (kind::BITVECTOR_UGE));
    BitVector pivot;
    // int counter = 0;
    // int counter2 = 0;
    while (true) {
      if (d_isSigned) {
        if (!lowerBound.signedLessThan(upperBound)) break;
      } else {
        if (!lowerBound.unsignedLessThan(upperBound)) break;
      }
      pivot = computeAverage(lowerBound, upperBound, d_isSigned);
      optChecker->push();
      // lowerBound <= target < pivot 
      optChecker->assertFormula(
        nm->mkNode(kind::AND, 
          nm->mkNode(GEOperator, target, nm->mkConst(lowerBound)), 
          nm->mkNode(LTOperator, target, nm->mkConst(pivot)))
      );
      intermediateSatResult = optChecker->checkSat();
      if (intermediateSatResult.isUnknown() || intermediateSatResult.isNull()) {
        return std::make_pair(OptResult::OPT_UNKNOWN, value);
      }
      if (intermediateSatResult.isSat() == Result::SAT) {
        value = optChecker->getValue(target);
        upperBound = value.getConst<BitVector>();
        
        // counter += 1;
        // if (counter > 100) return std::make_pair(OptResult::OPT_UNBOUNDED, value);
      } else if (intermediateSatResult.isSat() == Result::UNSAT) {
        
        if (lowerBound == pivot) {
          // lowerBound == pivot ==> upperbound = lowerbound + 1 
          // and lowerbound <= target < upperbound is UNSAT 
          // return the upperbound
          return std::make_pair(OptResult::OPT_OPTIMAL, value);
        } else {
          lowerBound = pivot;
        }
        // counter2 += 1;
        // if (counter2 > 100) return std::make_pair(OptResult::OPT_UNBOUNDED, value);
      } else {
        return std::make_pair(OptResult::OPT_UNKNOWN, value);
      }
      optChecker->pop();
    }
    return std::make_pair(OptResult::OPT_OPTIMAL, value);
  }

  virtual std::pair<OptResult, CVC4::Node> maximize(SmtEngine *parentSMTSolver, CVC4::Node target) override {
    // the smt engine to which we send intermediate queries
    // for the linear search.
    std::unique_ptr<CVC4::SmtEngine> optChecker = initOptChecker(parentSMTSolver); 
    NodeManager* nm = optChecker->getNodeManager();
    Result intermediateSatResult = optChecker->checkSat();
    // Model-value of objective (used in optimization loop)
    Node value;
    if (intermediateSatResult.isUnknown()) {
      return std::make_pair(OptResult::OPT_UNKNOWN, value);
    }
    if (!intermediateSatResult.isSat()) {
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
    BitVector upperBound = ((this->d_isSigned) ? 
                            (BitVector::mkMaxSigned(bvSize)) : (BitVector::mkOnes(bvSize)));

    Kind LEOperator = ((d_isSigned) ? (kind::BITVECTOR_SLE) : (kind::BITVECTOR_ULE));
    Kind GTOperator = ((d_isSigned) ? (kind::BITVECTOR_SGT) : (kind::BITVECTOR_UGT));
    BitVector pivot;
    int counter = 0;
    // int counter2 = 0;
    while (true) {
      if (d_isSigned) {
        if (!lowerBound.signedLessThan(upperBound)) break;
      } else {
        if (!lowerBound.unsignedLessThan(upperBound)) break;
      }
      pivot = computeAverage(lowerBound, upperBound, d_isSigned);
      
      optChecker->push();
      // pivot < target <= upperBound 
      optChecker->assertFormula(
        nm->mkNode(kind::AND, 
          nm->mkNode(GTOperator, target, nm->mkConst(pivot)), 
          nm->mkNode(LEOperator, target, nm->mkConst(upperBound)))
      );
      intermediateSatResult = optChecker->checkSat();
      if (intermediateSatResult.isUnknown() || intermediateSatResult.isNull()) {
        return std::make_pair(OptResult::OPT_UNKNOWN, value);
      }
      if (intermediateSatResult.isSat() == Result::SAT) {
        value = optChecker->getValue(target);
        lowerBound = value.getConst<BitVector>();
        counter += 1;
        if (counter > 299) {
          // Assert(value.getConst<BitVector>() == pivot);
          return std::make_pair(OptResult::OPT_UNKNOWN, nm->mkConst(pivot));
        }
      } else if (intermediateSatResult.isSat() == Result::UNSAT) {
        if (lowerBound == pivot) {
          // upperbound = lowerbound + 1 
          // and lowerbound < target <= upperbound is UNSAT 
          // return the lowerbound
          return std::make_pair(OptResult::OPT_OPTIMAL, value);
        } else {
          upperBound = pivot;
        }
        
      } else {
        return std::make_pair(OptResult::OPT_UNKNOWN, value);
      }
      optChecker->pop();
    }
    return std::make_pair(OptResult::OPT_OPTIMAL, value);
  }
  
};

std::unique_ptr<OMTOptimizer> OMTOptimizer::getOptimizerForNode(CVC4::Node node, bool isSigned) {
  CVC4::TypeNode objectiveType = node.getType(true);
  if (objectiveType.isInteger()) {
    return std::unique_ptr<OMTOptimizer>(new OMTOptimizerImpl<CVC4::Rational>());
  } 
  else if (objectiveType.isBitVector()) {
    return std::unique_ptr<OMTOptimizer>(new OMTOptimizerImpl<CVC4::BitVector>(isSigned));
  }
  else {
    return nullptr;
  }
}



}  // namespace smt
}  // namespace CVC4

#endif /* CVC4__SMT__OPTIMIZATION_SOLVER_H */
