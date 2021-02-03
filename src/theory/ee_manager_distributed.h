/*********************                                                        */
/*! \file ee_manager_distributed.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a distributed approach for equality engines over
 ** all theories.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__EE_MANAGER_DISTRIBUTED__H
#define CVC4__THEORY__EE_MANAGER_DISTRIBUTED__H

#include <map>
#include <memory>

#include "theory/ee_manager.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {

/**
 * The (distributed) equality engine manager. This encapsulates an architecture
 * in which all theories maintain their own copy of an equality engine.
 *
 * This class is not responsible for actually initializing equality engines in
 * theories (since this class does not have access to the internals of Theory).
 * Instead, it is only responsible for the construction of the equality
 * engine objects themselves. TheoryEngine is responsible for querying this
 * class during finishInit() to determine the equality engines to pass to each
 * theories based on getEeTheoryInfo.
 *
 * This class is also responsible for setting up the master equality engine,
 * which is used as a special communication channel to quantifiers engine (e.g.
 * for ensuring quantifiers E-matching is aware of terms from all theories).
 */
class EqEngineManagerDistributed : public EqEngineManager
{
 public:
  EqEngineManagerDistributed(TheoryEngine& te, SharedSolver& shs);
  ~EqEngineManagerDistributed();
  /**
   * Initialize theories. This method allocates unique equality engines
   * per theories and connects them to a master equality engine.
   */
  void initializeTheories() override;
  /** Notify model */
  void notifyModel(bool incomplete) override;

 private:
  /** notify class for master equality engine */
  class MasterNotifyClass : public theory::eq::EqualityEngineNotify
  {
   public:
    MasterNotifyClass(QuantifiersEngine* qe) : d_quantEngine(qe) {}
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
  /** The master equality engine notify class */
  std::unique_ptr<MasterNotifyClass> d_masterEENotify;
  /** The master equality engine. */
  std::unique_ptr<eq::EqualityEngine> d_masterEqualityEngine;
  /** The equality engine of the shared solver / shared terms database. */
  std::unique_ptr<eq::EqualityEngine> d_stbEqualityEngine;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__EE_MANAGER_DISTRIBUTED__H */
