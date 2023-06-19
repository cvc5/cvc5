/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

  bool eqNotifyTriggerPredicate(TNode predicate, bool value) override
  {
    return true;
  }
  bool eqNotifyTriggerTermEquality(TheoryId tag,
                                    TNode t1,
                                    TNode t2,
                                    bool value) override
  {
    return true;
  }
  void eqNotifyConstantTermMerge(TNode t1, TNode t2) override {}
  void eqNotifyMerge(TNode t1, TNode t2) override {}
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override {}

  private:
  /** Pointer to quantifiers engine */
  QuantifiersEngine* d_quantEngine;
};


}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__MASTER_EQ_NOTIFY__H */
