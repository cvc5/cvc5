/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for quantifiers inference manager.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_INFERENCE_MANAGER_H
#define CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_INFERENCE_MANAGER_H

#include "theory/inference_manager_buffered.h"
#include "theory/quantifiers/quantifiers_state.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class Instantiate;
class Skolemize;
class QuantifiersRegistry;
class TermRegistry;
class FirstOrderModel;
class QuantifiersModule;

/**
 * The quantifiers inference manager.
 */
class QuantifiersInferenceManager : public InferenceManagerBuffered
{
 public:
  QuantifiersInferenceManager(Env& env,
                              Theory& t,
                              QuantifiersState& state,
                              QuantifiersRegistry& qr,
                              TermRegistry& tr);
  ~QuantifiersInferenceManager();
  /** get instantiate utility */
  Instantiate* getInstantiate();
  /** get skolemize utility */
  Skolemize* getSkolemize();
  /**
   * Do all pending lemmas, then do all pending phase requirements.
   */
  void doPending();

  // ----- For printing -o inst-strategy
  /** Begin timing call */
  void beginCallDebug(QuantifiersModule* qm);
  /** End timing call */
  void endCallDebug();

 private:
  /** instantiate utility */
  std::unique_ptr<Instantiate> d_instantiate;
  /** skolemize utility */
  std::unique_ptr<Skolemize> d_skolemize;
  // ----- for printing -o inst-strategy
  /** For debug output, the quantifiers module called in beginCallDebug */
  QuantifiersModule* d_debugQm;
  /** The number of pending lemmas */
  size_t d_debugNumPendingLemmas;
  /** The time stamp */
  clock_t d_debugTimeStamp;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_INFERENCE_MANAGER_H */
