/*********************                                                        */
/*! \file model_blocker.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for blocking the current model
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__MODEL_BLOCKER_H
#define __CVC4__THEORY__MODEL_BLOCKER_H

#include <vector>

#include "expr/expr.h"
#include "options/smt_options.h"
#include "smt/model.h"

namespace CVC4 {

/**
 * A utility for blocking the current model.
 */
class ModelBlocker
{
 public:
  /** get model blocker
   *
   * This returns a disjunction of literals ~L1 V ... V ~Ln with the following
   * properties:
   * (1) L1 ... Ln hold in the current model (given by argument m),
   * (2) L1 ... Ln are literals that occur in assertions.
   */
  static Expr getModelBlocker(const std::vector<Expr>& assertions, Model* m);
}; /* class TheoryModelCoreBuilder */

}  // namespace CVC4

#endif /* __CVC4__THEORY__MODEL_BLOCKER_H */
