/******************************************************************************
 * Top contributors (to current version):
 *   Yancheng Ou
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The file containing utilities used in solving optimization queries.
 */
#ifndef CVC5__OMT__OPT_UTIL_H
#define CVC5__OMT__OPT_UTIL_H

#include "expr/node.h"
#include "expr/type_node.h"
#include "util/result.h"
namespace cvc5 {
namespace omt {

class Objective;
class OptimizationResult;

/**
 * The type of optimization, either maximize or minimize
 */
enum class OptType : int
{
  /** the target is to be minimized, signed min for BV */
  MINIMIZE = 0,
  /** the target is to be maximized, signed max for BV */
  MAXIMIZE = 1,
  /** the target is BV and it's to be minimized */
  BV_MINIMIZE_UNSIGNED = 2,
  /** the target is BV and it's to be maximized */
  BV_MAXIMIZE_UNSIGNED = 3,
};

/**
 * An enum specifying how multiple objectives are dealt with.
 * Definition:
 *   phi(x, y): set of assertions with variables x and y
 *
 * Box: treat the objectives as independent objectives
 *   v_x = max(x) s.t. phi(x, y) = sat
 *   v_y = max(y) s.t. phi(x, y) = sat
 *
 * Lexicographic: optimize the objectives one-by-one, in the order they are
 * added:
 *   v_x = max(x) s.t. phi(x, y) = sat
 *   v_y = max(y) s.t. phi(v_x, y) = sat
 *
 * Pareto: optimize multiple goals to a state such that
 * further optimization of one goal will worsen the other goal(s)
 *   (v_x, v_y) s.t. phi(v_x, v_y) = sat, and
 *     forall (x, y), (phi(x, y) = sat) -> (x <= v_x or y <= v_y)
 **/
enum class ObjectiveCombination : int
{
  BOX = 0,
  LEXICOGRAPHIC = 1,
  PARETO = 2,
};

class OptimizationResult
{
 public: 
  /** 
   * Constructor 
   * @param r the Result of optimization
   * @param val the optimal value
   */
  OptimizationResult(Result r, TNode val);
  OptimizationResult() = default;
  ~OptimizationResult() = default;
  /** Get the optimal value */
  Node getOptimalValue() const;
  /** Get the optimization outcome */
  Result getResult() const;
  /** Whether the optimization result is infinity */
  bool isInfinity() const;
  /** Whether the result is uninitialized */
  bool isNull() const;
  /** Set the result and optimal value */
  void set(Result r, TNode val);
  /** Set the optimal value */
  void setOptimalValue(TNode val);
  /** Set the result */
  void setResult(Result r);

 private:
  Result d_result;
  Node d_value;
};
/**
 * To serialize the OptimizationResult.
 * @param out the stream to put the serialized result
 * @param result the OptimizationResult object to serialize
 * @return the parameter out
 **/
std::ostream& operator<<(std::ostream& out, const OptimizationResult& result);


/**
 * The optimization objective
 */
class Objective
{
 public:
  /**
   * Constructor
   * @param target the node of the target expression
   * @param type the type of optimization,
   * NOTE:
   *    use MINIMIZE/MAXIMIZE for BV signed optimization,
   *    and use BV_MINIMIZE_UNSIGNED/BV_MAXIMIZE_UNSIGNED
   *    for BV unsigned optimization.
   */
  Objective(TNode target, OptType type);

  /** the default destructor */
  ~Objective() = default;

  /** Whether the objective is maximize */
  bool isMaximize() const;
  /** Whether the objective is minimize */
  bool isMinimize() const;
  /** Whether the objective is unsigned for BV */
  bool isBVUnsigned() const;
  /** Whether the objective is signed for BV */
  bool isBVSigned() const;

  /** Whether the objective is BV */
  bool isBV() const;

  /** The getter for d_target */
  TNode getTarget() const;

  /** The getter for d_type */
  OptType getType() const;

  /** Whether the result is ready */
  bool hasResult() const;

  /** The getter for d_result */
  OptimizationResult getOptResult() const;

  /** The setter for d_result, notice that d_result is mutable */
  void setOptResult(const OptimizationResult& res) const;

 private:
  /** the optimization target */
  Node d_target;
  /**
   * the optimization type,
   * (minimize / maximize) cross (signed / unsigned)
   */
  OptType d_type;
  /**
   * the optimal value of the target
   * if not-yet known then it's null
   */
  mutable OptimizationResult d_result;
};

/**
 * To serialize the Objective.
 * @param out the stream to put the serialized result
 * @param objective the Objective to serialize
 * @return the parameter out
 */
std::ostream& operator<<(std::ostream& out, const Objective& objective);

}  // namespace omt
}  // namespace cvc5

#endif /* CVC5__OMT__OPT_UTIL_H */
