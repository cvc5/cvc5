/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

 private:
  /** instantiate utility */
  std::unique_ptr<Instantiate> d_instantiate;
  /** skolemize utility */
  std::unique_ptr<Skolemize> d_skolemize;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_INFERENCE_MANAGER_H */
