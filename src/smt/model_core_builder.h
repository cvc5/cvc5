/*********************                                                        */
/*! \file model_core_builder.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for building model cores
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__MODEL_CORE_BUILDER_H
#define __CVC4__THEORY__MODEL_CORE_BUILDER_H

#include <vector>

#include "expr/expr.h"
#include "smt/model.h"

namespace CVC4 {

/**
 * A utility for building model cores.
 */
class ModelCoreBuilder
{
 public:
  /** set model core
   *
   * This function updates the model m so that it is a minimal "core" of
   * substitutions that satisfy the formulas in assertions, interpreted
   * conjunctively. This is specified via calls to
   * Model::setUsingModelCore, Model::recordModelCoreSymbol,
   * for details see smt/model.h.
   *
   * It returns true if m is a model for assertions. In this case, we set:
   *   m->usingModelCore();
   *   m->recordModelCoreSymbol(s1); ... m->recordModelCoreSymbol(sn);
   * such that each formula in assertions under the substitution
   * { s1 -> m(s1), ..., sn -> m(sn) } rewrites to true.
   *
   * If m is not a model for assertions, this method returns false and m is
   * left unchanged.
   */
  static bool setModelCore(const std::vector<Expr>& assertions, Model* m);
}; /* class TheoryModelCoreBuilder */

}  // namespace CVC4

#endif /* __CVC4__THEORY__MODEL_CORE_BUILDER_H */
