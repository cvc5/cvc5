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
  Objective(Node n, ObjectiveType type, bool bvSignedCompare = true);
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
  bool d_isSigned;
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
                   bool bvSignedCompare = true);
  /** Gets the value of the optimized objective after checkopt is called **/
  Node objectiveGetValue();

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
 * Currently supported: Integer, BitVector
 */
struct OMTOptimizer 
{
  virtual ~OMTOptimizer() = default;
  /** Given a target node, retrieve an optimizer specific for the node's datatype 
   * the second field isSigned specifies whether we should use signed comparison for BitVectors 
   * and it's only valid when the datatype is BitVector
   **/
  static std::unique_ptr<OMTOptimizer> getOptimizerForNode(CVC4::Node targetNode, bool isSigned=false);
  /** Minimize the target node with constraints encoded in parentSMTSolver 
   * Parameters: 
   * - parentSMTSolver: an SMT solver encoding the assertions as the constraints 
   * - target: the target expression to optimize 
   * Return value: 
   * - std::pair<OptResult, CVC4::Node>: the result of optimization and the optimized value 
   **/
  virtual std::pair<OptResult, CVC4::Node> minimize(SmtEngine *parentSMTSolver, CVC4::Node target) = 0;
  /** Maximize the target node with constraints encoded in parentSMTSolver 
   * Parameters: 
   * - parentSMTSolver: an SMT solver encoding the assertions as the constraints 
   * - target: the target expression to optimize 
   * Return value: 
   * - std::pair<OptResult, CVC4::Node>: the result of optimization and the optimized value 
   **/
  virtual std::pair<OptResult, CVC4::Node> maximize(SmtEngine *parentSMTSolver, CVC4::Node target) = 0;
};

/**
 * Optimizer for Integer datatype 
 */
struct OMTOptimizerInteger : OMTOptimizer 
{
public:
  virtual ~OMTOptimizerInteger() = default;
  /** Minimize the target node with constraints encoded in parentSMTSolver 
   * Parameters: 
   * - parentSMTSolver: an SMT solver encoding the assertions as the constraints 
   * - target: the target expression to optimize 
   * Return value: 
   * - std::pair<OptResult, CVC4::Node>: the result of optimization and the optimized value 
   **/
  virtual std::pair<OptResult, CVC4::Node> minimize(SmtEngine *parentSMTSolver, CVC4::Node target) override;
  /** Maximize the target node with constraints encoded in parentSMTSolver 
   * Parameters: 
   * - parentSMTSolver: an SMT solver encoding the assertions as the constraints 
   * - target: the target expression to optimize 
   * Return value: 
   * - std::pair<OptResult, CVC4::Node>: the result of optimization and the optimized value 
   **/
  virtual std::pair<OptResult, CVC4::Node> maximize(SmtEngine *parentSMTSolver, CVC4::Node target) override;
private:
  /** Handles the optimization query specified by objType (=OBJECTIVE_MINIMIZE/MAXIMIZE) **/
  std::pair<OptResult, CVC4::Node> optimize(SmtEngine *parentSMTSolver, CVC4::Node target, ObjectiveType objType);
};

/**
 * Optimizer for BitVector datatype 
 */
struct OMTOptimizerBitVector : OMTOptimizer 
{
public:
  OMTOptimizerBitVector(bool isSigned);
  virtual ~OMTOptimizerBitVector() = default;
  /** Minimize the target node with constraints encoded in parentSMTSolver 
   * Parameters: 
   * - parentSMTSolver: an SMT solver encoding the assertions as the constraints 
   * - target: the target expression to optimize 
   * Return value: 
   * - std::pair<OptResult, CVC4::Node>: the result of optimization and the optimized value 
   **/
  virtual std::pair<OptResult, CVC4::Node> minimize(SmtEngine *parentSMTSolver, CVC4::Node target) override;
  /** Maximize the target node with constraints encoded in parentSMTSolver 
   * Parameters: 
   * - parentSMTSolver: an SMT solver encoding the assertions as the constraints 
   * - target: the target expression to optimize 
   * Return value: 
   * - std::pair<OptResult, CVC4::Node>: the result of optimization and the optimized value 
   **/
  virtual std::pair<OptResult, CVC4::Node> maximize(SmtEngine *parentSMTSolver, CVC4::Node target) override;
private:
  /** Computes the BitVector version of (a + b) / 2 without overflow, rounding towards -infinity **/
  BitVector computeAverage(const BitVector &a, const BitVector &b, bool isSigned);
  /** Initialize an SMT subsolver for offline optimization purpose **/
  std::unique_ptr<CVC4::SmtEngine> initOptChecker(SmtEngine *parentSMTSolver);
  /** Is the BitVector doing signed comparison? **/
  bool d_isSigned;
};


}  // namespace smt
}  // namespace CVC4

#endif /* CVC4__SMT__OPTIMIZATION_SOLVER_H */
