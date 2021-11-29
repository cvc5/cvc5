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
#include "cvc5_private.h"

#ifndef CVC5__OMT__OPT_UTIL_H
#define CVC5__OMT__OPT_UTIL_H

#include "expr/node.h"
#include "expr/type_node.h"
namespace cvc5 {
namespace omt {

class Objective;

/**
 * The optimization objective
 */
class Objective
{
 public:
  /**
   * The type of optimization, either maximize or minimize
   */
  enum Type
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
   * Constructor
   * @param target the node of the target expression
   * @param type the type of optimization,
   * NOTE:
   *    use MINIMIZE/MAXIMIZE for BV signed optimization,
   *    and use BV_MINIMIZE_UNSIGNED/BV_MAXIMIZE_UNSIGNED
   *    for BV unsigned optimization.
   */
  Objective(TNode target, Type type);

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
  Type getType() const;

  /** Whether the result is ready */
  bool hasResult() const;

  /** The getter for d_result */
  TNode getResult() const;

  /** The setter for d_result, notice that d_result is mutable */
  void setResult(TNode res) const;

 private:
  /** the optimization target */
  Node d_target;
  /**
   * the optimization type,
   * (minimize / maximize) cross (signed / unsigned)
   */
  Type d_type;
  /**
   * the optimal value of the target
   * if not-yet known then it's null
   */
  mutable Node d_result;
};

}  // namespace omt
}  // namespace cvc5

#endif /* CVC5__OMT__OPT_UTIL_H */
