/*********************                                                        */
/*! \file model_core_builder.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for building model cores
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__MODEL_CORE_BUILDER_H
#define CVC4__THEORY__MODEL_CORE_BUILDER_H

#include <vector>

#include "expr/expr.h"
#include "options/smt_options.h"
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
   * This function updates model m so that it has information regarding its
   * "model core". A model core for m is a substitution of the form
   *    { s1 -> m(s1), ..., sn -> m(sn) }
   *
   * The criteria for what consistutes a model core given by mode. For
   * example, if mode is ModelCoresMode::SIMPLE, then a model core
   * corresponds to a subset of assignments from the model that suffice to show
   * that the set of assertions, interpreted conjunctively, evaluates to true
   * under the substitution corresponding to the model core.
   *
   * The model core is recorded on the model object m via calls to
   * m->setUsingModelCore, m->recordModelCoreSymbol, for details see
   * smt/model.h. In particular, we call:
   *   m->usingModelCore();
   *   m->recordModelCoreSymbol(s1); ... m->recordModelCoreSymbol(sn);
   * such that { s1 -> m(s1), ..., sn -> m(sn) } is the model core computed
   * by this class.
   *
   * If m is not a model for assertions, this method returns false and m is
   * left unchanged.
   */
  static bool setModelCore(const std::vector<Expr>& assertions,
                           Model* m,
                           options::ModelCoresMode mode);
}; /* class TheoryModelCoreBuilder */

}  // namespace CVC4

#endif /* CVC4__THEORY__MODEL_CORE_BUILDER_H */
