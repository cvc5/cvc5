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
 * Equality engine manager for central equality engine architecture
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__EE_MANAGER_CENTRAL__H
#define CVC5__THEORY__EE_MANAGER_CENTRAL__H

#include <map>
#include <memory>

#include "theory/ee_manager.h"
#include "theory/quantifiers/master_eq_notify.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {

/**
 * The (central) equality engine manager. This encapsulates an architecture
 * in which all applicable theories use a single central equality engine.
 *
 * This class is not responsible for actually initializing equality engines in
 * theories (since this class does not have access to the internals of Theory).
 * Instead, it is only responsible for the construction of the equality
 * engine objects themselves. TheoryEngine is responsible for querying this
 * class during finishInit() to determine the equality engines to pass to each
 * theories based on getEeTheoryInfo.
 *
 * It also may allocate a "master" equality engine, which is intuitively the
 * equality engine of the theory of quantifiers. If all theories use the
 * central equality engine, then the master equality engine is the same as the
 * central equality engine.
 *
 * The theories that use central equality engine are determined by
 * Theory::usesCentralEqualityEngine.
 *
 * The main idea behind this class is to use a notification class on the
 * central equality engine which dispatches *multiple* notifications to the
 * theories that use the central equality engine.
 */
class EqEngineManagerCentral : public EqEngineManager
{
 public:
  EqEngineManagerCentral(Env& env, TheoryEngine& te, SharedSolver& shs);
  ~EqEngineManagerCentral();
  /**
   * Initialize theories. This method allocates unique equality engines
   * per theories and connects them to a master equality engine.
   */
  void initializeTheories() override;
  /** Notify this class that we are building the model. */
  void notifyBuildingModel();

  /**
   * Return true if the theory with the given id uses central equality engine
   * with the given options.
   */
  static bool usesCentralEqualityEngine(const Options& opts, TheoryId id);

 private:
  /**
   * Notify class for central equality engine. This class dispatches
   * notifications from the central equality engine to the appropriate
   * theory(s).
   */
  class CentralNotifyClass : public theory::eq::EqualityEngineNotify
  {
   public:
    CentralNotifyClass(EqEngineManagerCentral& eemc);
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override;
    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override;
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override;
    void eqNotifyNewClass(TNode t) override;
    void eqNotifyMerge(TNode t1, TNode t2) override;
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override;
    /** Parent */
    EqEngineManagerCentral& d_eemc;
    /** List of notify classes that need new class notification */
    std::vector<eq::EqualityEngineNotify*> d_newClassNotify;
    /** List of notify classes that need merge notification */
    std::vector<eq::EqualityEngineNotify*> d_mergeNotify;
    /** List of notify classes that need disequality notification */
    std::vector<eq::EqualityEngineNotify*> d_disequalNotify;
    /** The model notify class */
    eq::EqualityEngineNotify* d_mNotify;
    /** The quantifiers engine */
    QuantifiersEngine* d_quantEngine;
  };
  /** Notification when predicate gets value in central equality engine */
  bool eqNotifyTriggerPredicate(TNode predicate, bool value);
  bool eqNotifyTriggerTermEquality(TheoryId tag,
                                   TNode t1,
                                   TNode t2,
                                   bool value);
  /** Notification when constants are merged in central equality engine */
  void eqNotifyConstantTermMerge(TNode t1, TNode t2);
  /** The master equality engine notify class */
  std::unique_ptr<quantifiers::MasterNotifyClass> d_masterEENotify;
  /** The master equality engine. */
  eq::EqualityEngine* d_masterEqualityEngine;
  /** The master equality engine, if we allocated it */
  std::unique_ptr<eq::EqualityEngine> d_masterEqualityEngineAlloc;
  /** The central equality engine notify class */
  CentralNotifyClass d_centralEENotify;
  /** The central equality engine. */
  eq::EqualityEngine d_centralEqualityEngine;
  /** The proof equality engine for the central equality engine */
  std::unique_ptr<eq::ProofEqEngine> d_centralPfee;
  /**
   * A table of from theory IDs to notify classes.
   */
  eq::EqualityEngineNotify* d_theoryNotify[theory::THEORY_LAST];
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__EE_MANAGER_CENTRAL__H */
