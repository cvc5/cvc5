/*********************                                                        */
/*! \file optimization_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Ying Sheng
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

class SmtEngine;

namespace smt {

/**
 * A solver for optimization queries.
 *
 * This class is responsible for responding to get-interpol commands. It spawns
 * a subsolver SmtEngine for a sygus conjecture that captures the interpolation
 * query, and implements supporting utility methods such as checkInterpol.
 */
class OptimizationSolver
{
  enum CVC4_PUBLIC OptResult 
  {
    OPT_UNKNOWN, 
    OPT_UNSAT, 
    OPT_SAT_PARTIAL, 
    OPT_SAT_APPROX, 
    OPT_OPTIMAL 
  };

  enum CVC4_PUBLIC ObjectiveType 
  {
    OBJECTIVE_MINIMIZE, 
    OBJECTIVE_MAXIMIZE
  };

  enum CVC4_PUBLIC ObjectiveValue
  {
    OPTIMUM,
    FINAL_LOWER,
    FINAL_UPPER,
    FINAL_ERROR
  };

  class Objective
  {
    public:
    Objective(Node n, ObjectiveType type, OptResult result);
    //~Objective();

    /*private:*/
    ObjectiveType d_type;
    OptResult d_result;
    Node d_node;
    Node d_savedValue;
  };

 public:
  OptimizationSolver(SmtEngine* parent);
  ~OptimizationSolver();

  bool checkOpt(Result& r);
  void activateObj(const Node& obj, const int& type, const int& result);
  Node objectiveGetValue(const Node& obj);

 private:
  /** The parent SMT engine **/
  SmtEngine* d_parent;
  /** The objectives to optimize for **/
  std::vector<Objective> d_activatedObjectives;
};

}  // namespace smt
}  // namespace CVC4

#endif /* CVC4__SMT__OPTIMIZATION_SOLVER_H */