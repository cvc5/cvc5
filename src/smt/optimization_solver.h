/*********************                                                        */
/*! \file optimization_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Michael Chang, Yancheng Ou
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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

namespace CVC4 {
namespace smt {

/**
 * An enum for optimization queries.
 *
 * Represents whether an objective should be minimized or maximized
 */
enum CVC4_PUBLIC ObjectiveType
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
enum CVC4_PUBLIC OptResult
{
  // the original set of assertions has result UNKNOWN
  OPT_UNKNOWN,
  // the original set of assertions has result UNSAT
  OPT_UNSAT,
  // the optimization loop finished and optimal
  OPT_OPTIMAL,

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

 private:
  /** Returns the less than operator for the activated objective
   * if objective does not support comparison, return kind::NULL_EXPR **/
  Kind getLessThanOperatorForObjective();

 private:
  /** The parent SMT engine **/
  SmtEngine* d_parent;
  /** The objectives to optimize for **/
  Objective d_activatedObjective;
  /** A saved value of the objective from the last sat call. **/
  Node d_savedValue;
};

struct OMTSearchState 
{
  virtual ~OMTSearchState() {}
  virtual bool setLowerBound(const Node &lowerBoundNode) = 0;
  virtual bool setUpperBound(const Node &upperBoundNode) = 0;
  virtual Node getLowerBound() = 0;
  virtual Node getUpperBound() = 0;
  virtual Node constructLTExpr(NodeManager *nm, const Node &a, const Node &b) = 0;
  virtual Node constructLEQExpr(NodeManager *nm, const Node &a, const Node &b) = 0;
  virtual Node computePivot(NodeManager* nm) = 0;
  virtual bool shouldPerformBinarySearchStep() = 0;
  virtual bool shouldTerminate() = 0;
};

/**
 * The class storing the search states of the binary search. 
 * Including upper and lower bounds. 
 */
template <typename T>
struct OMTSearchStateImpl : OMTSearchState
{ // empty implementation 
};

template <>
struct OMTSearchStateImpl<Rational> : OMTSearchState
{
private:
  Node lowerBound; 
  Node upperBound;
public: 
  void checkNode(const Node &node) {
    Assert(node.isConst());
    Assert(node.getType().isInteger());
  }
  OMTSearchStateImpl(const Node &lowerBound, const Node &upperBound) {
    checkNode(lowerBound);
    checkNode(upperBound);
    this->lowerBound = lowerBound;
    this->upperBound = upperBound;
  }
  virtual ~OMTSearchStateImpl() {}
  virtual bool setLowerBound(const Node &lowerBoundNode) {
    checkNode(lowerBoundNode);
    this->lowerBound = lowerBoundNode;
    return true;
  }
  virtual bool setUpperBound(const Node &upperBoundNode) {
    checkNode(upperBoundNode);
    this->upperBound = upperBoundNode;
    return true;
  }
  virtual Node getLowerBound() {
    return this->lowerBound;
  }
  virtual Node getUpperBound() {
    return this->upperBound;
  }
  virtual Node constructLTExpr(NodeManager *nm, const Node &a, const Node &b) {
    return nm->mkNode(kind::LT, a, b);
  }
  virtual Node constructLEQExpr(NodeManager *nm, const Node &a, const Node &b) {
    return nm->mkNode(kind::LEQ, a, b);
  }
  virtual Node computePivot(NodeManager* nm) {
    Rational upper = this->upperBound.getConst<Rational>();
    Rational lower = this->lowerBound.getConst<Rational>();
    Rational pivot = (upper + lower) / Rational(2);
    return nm->mkConst(pivot);
  }
  virtual bool shouldPerformBinarySearchStep() {
    Rational upper = this->upperBound.getConst<Rational>();
    Rational lower = this->lowerBound.getConst<Rational>();
    return (upper - lower) > Rational(5);
  }
  virtual bool shouldTerminate() {
    Rational upper = this->upperBound.getConst<Rational>();
    Rational lower = this->lowerBound.getConst<Rational>();
    return (lower >= upper);
  }
};

}  // namespace smt
}  // namespace CVC4

#endif /* CVC4__SMT__OPTIMIZATION_SOLVER_H */
