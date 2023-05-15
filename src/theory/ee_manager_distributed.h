/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Management of a distributed approach for equality engines over
 * all theories.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__EE_MANAGER_DISTRIBUTED__H
#define CVC5__THEORY__EE_MANAGER_DISTRIBUTED__H

#include <memory>

#include "theory/ee_manager.h"
#include "theory/quantifiers/master_eq_notify.h"

namespace cvc5::internal {
namespace theory {

namespace eq {
class EqualityEngine;
}

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
  EqEngineManagerDistributed(Env& env, TheoryEngine& te, SharedSolver& shs);
  ~EqEngineManagerDistributed();
  /**
   * Initialize theories. This method allocates unique equality engines
   * per theories and connects them to a master equality engine.
   */
  void initializeTheories() override;
  /** Notify model */
  void notifyModel(bool incomplete) override;

 private:
  /** The master equality engine notify class */
  std::unique_ptr<quantifiers::MasterNotifyClass> d_masterEENotify;
  /** The master equality engine. */
  std::unique_ptr<eq::EqualityEngine> d_masterEqualityEngine;
  /** The equality engine of the shared solver / shared terms database. */
  std::unique_ptr<eq::EqualityEngine> d_stbEqualityEngine;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__EE_MANAGER_DISTRIBUTED__H */
