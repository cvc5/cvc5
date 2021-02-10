/*********************                                                        */
/*! \file quantifiers_inference_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for quantifiers inference manager
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_INFERENCE_MANAGER_H
#define CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_INFERENCE_MANAGER_H

#include "theory/inference_manager_buffered.h"
#include "theory/quantifiers/quantifiers_state.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * The quantifiers inference manager.
 */
class QuantifiersInferenceManager : public InferenceManagerBuffered
{
 public:
  QuantifiersInferenceManager(Theory& t,
                              QuantifiersState& state,
                              ProofNodeManager* pnm);
  ~QuantifiersInferenceManager();
  /**
   * Do all pending lemmas, then do all pending phase requirements.
   */
  void doPending();
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_INFERENCE_MANAGER_H */
