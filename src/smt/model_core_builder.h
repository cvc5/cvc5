/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for building model cores.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__MODEL_CORE_BUILDER_H
#define CVC5__THEORY__MODEL_CORE_BUILDER_H

#include <vector>

#include "expr/node.h"
#include "options/smt_options.h"
#include "smt/env_obj.h"
#include "theory/theory_model.h"

namespace cvc5::internal {

/**
 * A utility for building model cores.
 */
class ModelCoreBuilder : protected EnvObj
{
 public:
  ModelCoreBuilder(Env& env);
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
  bool setModelCore(const std::vector<Node>& assertions,
                    theory::TheoryModel* m,
                    options::ModelCoresMode mode);
}; /* class TheoryModelCoreBuilder */

}  // namespace cvc5::internal

#endif /* CVC5__THEORY__MODEL_CORE_BUILDER_H */
