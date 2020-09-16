/*********************                                                        */
/*! \file model_manager_distributed.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a distributed approach for model generation.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__MODEL_MANAGER_DISTRIBUTED__H
#define CVC4__THEORY__MODEL_MANAGER_DISTRIBUTED__H

#include <memory>

#include "theory/ee_manager_distributed.h"
#include "theory/model_manager.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * Manager for building models in a distributed architecture. Its prepare
 * model method uses collectModelInfo to assert all equalities from the equality
 * engine of each theory into the equality engine of the model. It additionally
 * uses the model equality engine context to clear the information from
 * the model's equality engine, as maintained by the distributed equality
 * engine manager.
 */
class ModelManagerDistributed : public ModelManager
{
 public:
  ModelManagerDistributed(TheoryEngine& te, EqEngineManagerDistributed& eem);
  ~ModelManagerDistributed();

  /** Prepare the model, as described above. */
  bool prepareModel() override;
  /**
   * Assign values to all equivalence classes in the equality engine of the
   * model, return true if successful.
   */
  bool finishBuildModel() const override;

 protected:
  /**
   * Distributed equality engine manager, which maintains the context of the
   * model's equality engine.
   */
  EqEngineManagerDistributed& d_eem;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__MODEL_MANAGER_DISTRIBUTED__H */
