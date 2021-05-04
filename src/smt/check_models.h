/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

namespace cvc5 {

class Env;

namespace smt {

class Model;

/**
 * This utility is responsible for checking the current model.
 */
class CheckModels
{
 public:
  CheckModels(Env& e);
  ~CheckModels();
  /**
   * Check model m against the current set of input assertions al.
   *
   * This throws an exception if we fail to verify that m is a proper model
   * given assertion list al based on the model checking policy.
   */
  void checkModel(Model* m, context::CDList<Node>* al, bool hardFailure);

 private:
  /** Reference to the environment */
  Env& d_env;
};

}  // namespace smt
}  // namespace cvc5

#endif
