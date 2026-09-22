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

namespace cvc5::internal {

namespace theory {
class TheoryModel;
}

namespace smt {

/** Utility for evaluating terms in the current model. */
class GetValue : protected EnvObj
{
 public:
  GetValue(Env& env);
  /**
   * Get the value of t in model m. Applies top-level substitutions, expands
   * definitions, and rewrites t before evaluating it. Handles abstract values
   * when enabled.
   *
   * If fromUser is true and --check-model-subsolver is enabled, a subsolver may
   * be used to obtain a concrete value for terms the model cannot evaluate.
   * Internal calls do not generally require a concrete value.
   *
   * @param m The model to evaluate in, which must be non-null.
   * @param t The term to get the value of.
   * @param fromUser Whether the call originated from an external user.
   * @return The value of t in m.
   */
  Node getValue(theory::TheoryModel* m, const Node& t, bool fromUser = false);
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
