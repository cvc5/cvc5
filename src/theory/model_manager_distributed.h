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
 * Management of a distributed approach for model generation.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__MODEL_MANAGER_DISTRIBUTED__H
#define CVC5__THEORY__MODEL_MANAGER_DISTRIBUTED__H

#include "theory/ee_manager.h"
#include "theory/model_manager.h"

namespace cvc5::internal {
namespace theory {

/**
 * Manager for building models where the equality engine of the model is
 * a separate instance. Notice that this manager can be used regardless of the
 * method for managing the equality engines of the theories (which is the
 * responsibility of the equality engine manager eem referenced by this class).
 *
 * Its prepare model method uses collectModelInfo to assert all equalities from
 * the equality engine of each theory into the equality engine of the model. It
 * additionally uses the model equality engine context to clear the information
 * from the model's equality engine, which is maintained by this class.
 */
class ModelManagerDistributed : public ModelManager
{
 public:
  ModelManagerDistributed(Env& env, TheoryEngine& te, EqEngineManager& eem);
  ~ModelManagerDistributed();

  /** Prepare the model, as described above. */
  bool prepareModel() override;
  /**
   * Assign values to all equivalence classes in the equality engine of the
   * model, return true if successful.
   */
  bool finishBuildModel() const override;
 protected:
  /** Initialize model equality engine */
  void initializeModelEqEngine(eq::EqualityEngineNotify* notify) override;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__MODEL_MANAGER_DISTRIBUTED__H */
