/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Notification class for the master equality engine
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__MASTER_EQ_NOTIFY__H
#define CVC5__THEORY__QUANTIFIERS__MASTER_EQ_NOTIFY__H

#include <memory>

#include "theory/uf/equality_engine_notify.h"

namespace cvc5::internal {
namespace theory {
  
class QuantifiersEngine;

namespace quantifiers {

/** notify class for master equality engine */
class MasterNotifyClass : public theory::eq::EqualityEngineNotify
{
 public:
  MasterNotifyClass(QuantifiersEngine* qe);
  /**
    * Called when a new equivalence class is created in the master equality
    * engine.
    */
  void eqNotifyNewClass(TNode t) override;

  bool eqNotifyTriggerPredicate(CVC5_UNUSED TNode predicate,
                                CVC5_UNUSED bool value) override
  {
    return true;
  }
  bool eqNotifyTriggerTermEquality(CVC5_UNUSED TheoryId tag,
                                   CVC5_UNUSED TNode t1,
                                   CVC5_UNUSED TNode t2,
                                   CVC5_UNUSED bool value) override
  {
    return true;
  }
  void eqNotifyConstantTermMerge(CVC5_UNUSED TNode t1,
                                 CVC5_UNUSED TNode t2) override
  {
  }
  void eqNotifyMerge(CVC5_UNUSED TNode t1, CVC5_UNUSED TNode t2) override;
  void eqNotifyDisequal(CVC5_UNUSED TNode t1,
                        CVC5_UNUSED TNode t2,
                        CVC5_UNUSED TNode reason) override
  {
  }

  private:
  /** Pointer to quantifiers engine */
  QuantifiersEngine* d_quantEngine;
};


}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__MASTER_EQ_NOTIFY__H */
