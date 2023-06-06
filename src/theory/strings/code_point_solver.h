/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Subsolver for handling code points
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__CODE_POINT_SOLVER_H
#define CVC5__THEORY__STRINGS__CODE_POINT_SOLVER_H

#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

class BaseSolver;
class CoreSolver;
class InferenceManager;
class TermRegistry;
class SolverState;

/**
 * Subsolver for handling code points, see "A Decision Procedure for String to
 * Code Point Conversion", Reynolds et al IJCAR 2020.
 */
class CodePointSolver : protected EnvObj
{
 public:
  CodePointSolver(Env& env,
                  SolverState& s,
                  InferenceManager& im,
                  TermRegistry& tr,
                  BaseSolver& bs,
                  CoreSolver& cs);
  ~CodePointSolver() {}
  /** check codes
   *
   * This inference schema ensures that constraints between str.code terms
   * are satisfied by models that correspond to extensions of the current
   * assignment. In particular, this method ensures that str.code can be
   * given an interpretation that is injective for string arguments with length
   * one. It may add lemmas of the form:
   *   str.code(x) == -1 V str.code(x) != str.code(y) V x == y
   */
  void checkCodes();

 protected:
  /** The solver state object */
  SolverState& d_state;
  /** The (custom) output channel of the theory of strings */
  InferenceManager& d_im;
  /** Reference to the term registry of theory of strings */
  TermRegistry& d_termReg;
  /** reference to the base solver, used for certain queries */
  BaseSolver& d_bsolver;
  /** The core solver */
  CoreSolver& d_csolver;
  /** Commonly used constants */
  Node d_negOne;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__CODE_POINT_SOLVER_H */
