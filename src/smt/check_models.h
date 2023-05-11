/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for checking models.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__CHECK_MODELS_H
#define CVC5__SMT__CHECK_MODELS_H

#include "context/cdlist.h"
#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

namespace theory {
class TheoryModel;
}

namespace smt {

/**
 * This utility is responsible for checking the current model.
 */
class CheckModels : protected EnvObj
{
 public:
  CheckModels(Env& e);
  /**
   * Check model m against the current set of input assertions al.
   *
   * This throws an exception if we fail to verify that m is a proper model
   * given assertion list al based on the model checking policy.
   */
  void checkModel(theory::TheoryModel* m,
                  const context::CDList<Node>& al,
                  bool hardFailure);
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
