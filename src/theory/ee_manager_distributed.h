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

class TheoryEngine;

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
  EqEngineManagerDistributed(TheoryEngine& te);
  ~EqEngineManagerDistributed();
  /**
   * Initialize theories. This method allocates unique equality engines
   * per theories and connects them to a master equality engine.
   */
  void initializeTheories() override;
  /**
   * Initialize model. This method allocates a new equality engine for the
   * model.
   */
  void initializeModel(TheoryModel* m) override;
  /**
   * Get the model equality engine context. This is a dummy context that is
   * used for clearing the contents of the model's equality engine via
   * pop/push.
   */
  context::Context* getModelEqualityEngineContext();
  /** get the model equality engine */
  eq::EqualityEngine* getModelEqualityEngine();
  /** get the core equality engine */
  eq::EqualityEngine* getCoreEqualityEngine() override;

 private:
  /** Allocate equality engine that is context-dependent on c with info esi */
  eq::EqualityEngine* allocateEqualityEngine(EeSetupInfo& esi,
                                             context::Context* c);
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
  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /** The master equality engine notify class */
  std::unique_ptr<MasterNotifyClass> d_masterEENotify;
  /** The master equality engine. */
  std::unique_ptr<eq::EqualityEngine> d_masterEqualityEngine;
  /**
   * A dummy context for the model equality engine, so we can clear it
   * independently of search context.
   */
  context::Context d_modelEeContext;
  /**
   * The equality engine of the model.
   */
  std::unique_ptr<eq::EqualityEngine> d_modelEqualityEngine;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__EE_MANAGER_DISTRIBUTED__H */
