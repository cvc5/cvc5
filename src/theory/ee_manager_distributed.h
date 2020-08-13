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

#include "theory/ee_setup_info.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * This is (theory-agnostic) information associated with the management of
 * an equality engine for a single theory. This information is maintained
 * by the manager class below.
 *
 * Currently, this simply is the equality engine itself, which is a unique_ptr
 * for memory management purposes.
 */
struct EeTheoryInfo
{
  /** The equality engine allocated by this theory (if it exists) */
  std::unique_ptr<eq::EqualityEngine> d_allocEe;
};

/** Virtual base class for equality engine managers */
class EqEngineManager
{
 public:
  virtual ~EqEngineManager() {}
  /**
   * Get the equality engine theory information for theory with the given id.
   */
  const EeTheoryInfo* getEeTheoryInfo(TheoryId tid) const;

 protected:
  /** Information related to the equality engine, per theory. */
  std::map<TheoryId, EeTheoryInfo> d_einfo;
};

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
   * Finish initialize, called by TheoryEngine::finishInit after theory
   * objects have been created but prior to their final initialization. This
   * sets up equality engines for all theories.
   *
   * This method is context-independent, and is applied once during
   * the lifetime of TheoryEngine (during finishInit).
   */
  void finishInit();
  /** get the master equality engine */
  eq::EqualityEngine* getMasterEqualityEngine();

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

    bool eqNotifyTriggerEquality(TNode equality, bool value) override
    {
      return true;
    }
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
    void eqNotifyPreMerge(TNode t1, TNode t2) override {}
    void eqNotifyPostMerge(TNode t1, TNode t2) override {}
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override {}

   private:
    /** Pointer to quantifiers engine */
    QuantifiersEngine* d_quantEngine;
  };
  /** Allocate equality engine that is context-dependent on c with info esi */
  eq::EqualityEngine* allocateEqualityEngine(EeSetupInfo& esi,
                                             context::Context* c);
  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /** The master equality engine notify class */
  std::unique_ptr<MasterNotifyClass> d_masterEENotify;
  /** The master equality engine. */
  std::unique_ptr<eq::EqualityEngine> d_masterEqualityEngine;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__EE_MANAGER_DISTRIBUTED__H */
