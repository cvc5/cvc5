/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for getting model values.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__GET_VALUE_H
#define CVC5__SMT__GET_VALUE_H

#include "expr/node.h"
#include "smt/env_obj.h"
#include "smt/expand_definitions.h"

namespace cvc5::internal {

class SolverEngine;

namespace smt {

/** Utility for evaluating terms in the current model. */
class GetValue : protected EnvObj
{
 public:
  GetValue(Env& env, SolverEngine& solver);
  /**
   * Get the value of t in the current model. Applies top-level substitutions,
   * expands definitions, and rewrites t before evaluating it. Uses the SAT
   * trail for Boolean terms when possible, avoiding model construction.
   * Handles abstract values when enabled.
   *
   * If fromUser is true and --check-model-subsolver is enabled, a subsolver may
   * be used to obtain a concrete value for terms the model cannot evaluate.
   * Internal calls do not generally require a concrete value.
   *
   * @param t The term to get the value of.
   * @param fromUser Whether the call originated from an external user.
   * @return The value of t in the current model.
   */
  Node getValue(const Node& t, bool fromUser = false);

 private:
  /** The solver whose model and SAT trail are queried. */
  SolverEngine& d_solver;
  /**
   * Definition expansion with a cache valid for the lifetime of the solver,
   * including across check-sat and user-context push/pop.
   */
  ExpandDefs d_expDef;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
