/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory equality notify utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__THEORY_EQ_NOTIFY_H
#define CVC5__THEORY__THEORY_EQ_NOTIFY_H

#include "expr/node.h"
#include "theory/theory_inference_manager.h"
#include "theory/uf/equality_engine_notify.h"

namespace cvc5::internal {
namespace theory {

/**
 * The default class for equality engine callbacks for a theory. This forwards
 * calls for trigger predicates, trigger term equalities and conflicts due to
 * constant merges to the provided theory inference manager.
 */
class TheoryEqNotifyClass : public eq::EqualityEngineNotify
{
 public:
  TheoryEqNotifyClass(TheoryInferenceManager& im) : d_im(im) {}
  ~TheoryEqNotifyClass() {}

  bool eqNotifyTriggerPredicate(TNode predicate, bool value) override
  {
    if (value)
    {
      return d_im.propagateLit(predicate);
    }
    return d_im.propagateLit(predicate.notNode());
  }
  bool eqNotifyTriggerTermEquality(TheoryId tag,
                                   TNode t1,
                                   TNode t2,
                                   bool value) override
  {
    if (value)
    {
      return d_im.propagateLit(t1.eqNode(t2));
    }
    return d_im.propagateLit(t1.eqNode(t2).notNode());
  }
  void eqNotifyConstantTermMerge(TNode t1, TNode t2) override
  {
    d_im.conflictEqConstantMerge(t1, t2);
  }
  void eqNotifyNewClass(TNode t) override
  {
    // do nothing
  }
  void eqNotifyMerge(TNode t1, TNode t2) override
  {
    // do nothing
  }
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override
  {
    // do nothing
  }

 protected:
  /** Reference to the theory inference manager */
  TheoryInferenceManager& d_im;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif
