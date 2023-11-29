/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for blocking the current model.
 */

#include "cvc5_private.h"

#ifndef __CVC5__THEORY__MODEL_BLOCKER_H
#define __CVC5__THEORY__MODEL_BLOCKER_H

#include <cvc5/cvc5_types.h>

#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

namespace theory {
class TheoryModel;
}

/**
 * A utility for blocking the current model.
 */
class ModelBlocker : protected EnvObj
{
 public:
  ModelBlocker(Env& e);
  /** get model blocker
   *
   * This returns a disjunction of literals ~L1 V ... V ~Ln with the following
   * properties:
   * (1) L1 ... Ln hold in the current model (given by argument m),
   * (2) if mode is set to "literals", L1 ... Ln are literals that occur in
   * assertions and propositionally entail all non-unit top-level assertions.
   * (3) if mode is set to "values", L1 ... Ln are literals of the form x=c,
   * where c is the value of x in the current model.
   * (4) if exprToBlock is not empty, L1 ... Ln are literals of the form t=c,
   * where c is the value of t in the current model. If exprToBlock is
   * non-empty, then L1 ... Ln are t1=c1 ... tn=cn where exprToBlock is
   * { t1 ... tn }; if exprToBlock is empty, then t1 ... tn are the free
   * variables of assertions.
   *
   * We expect exprToBlock to be non-empty only if mode is
   * BlockModelsMode::VALUES.
   *
   * For example, if our input is:
   *    x > 0 ^ ( y < 0 V z < 0 V w < 0 )
   * and m is { x -> 1, y -> 2, z -> -1, w -> -1 }, then this method may
   * return ~(z < 0) or ~(w < 0) when set to mode "literals".
   *
   * Notice that we do not require that L1...Ln entail unit top-level assertions
   * since these literals are trivially entailed to be true in all models of
   * our input. In other words, we do not return ~(x < 0) V ~(w < 0) since the
   * left disjunct is always false.
   */
  Node getModelBlocker(
      const std::vector<Node>& assertions,
      theory::TheoryModel* m,
      modes::BlockModelsMode mode,
      const std::vector<Node>& exprToBlock = std::vector<Node>());
}; /* class TheoryModelCoreBuilder */

}  // namespace cvc5::internal

#endif /* __CVC5__THEORY__MODEL_BLOCKER_H */
