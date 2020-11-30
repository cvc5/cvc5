/*********************                                                        */
/*! \file model_manager_distributed.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a distributed approach for model generation.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__MODEL_MANAGER_DISTRIBUTED__H
#define CVC4__THEORY__MODEL_MANAGER_DISTRIBUTED__H

#include <memory>

#include "theory/ee_manager.h"
#include "theory/model_manager.h"

namespace CVC4 {

class TheoryEngine;

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
  ModelManagerDistributed(TheoryEngine& te, EqEngineManager& eem);
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
}  // namespace CVC4

#endif /* CVC4__THEORY__MODEL_MANAGER_DISTRIBUTED__H */
