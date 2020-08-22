/*********************                                                        */
/*! \file ee_manager_distributed.h
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

#include <map>
#include <memory>

#include "theory/ee_manager_distributed.h"
#include "theory/model_manager.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * Manager for building models in a distributed architecture. Its build
 * model internal method uses collectModelInfo from each theory of the
 * theory engine to assert all equalities from the equality engine of the
 * various theories into the equality engine of the model. It additionally
 * uses the model equality engine context to clear the information from
 * the model's equality engine, as maintained by the distributed equality
 * engine manager.
 */
class ModelManagerDistributed : public ModelManager
{
 public:
  ModelManagerDistributed(TheoryEngine& te, EqEngineManagerDistributed& eem);
  ~ModelManagerDistributed();

 protected:
  /** Build model internal method */
  bool buildModelInternal() override;
  /**
   * Distributed equality engine manager, which as a special interaction
   * for building models.
   */
  EqEngineManagerDistributed& d_eem;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__MODEL_MANAGER_DISTRIBUTED__H */
