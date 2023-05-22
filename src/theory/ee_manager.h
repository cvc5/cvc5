/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for management of equality engines.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__EE_MANAGER__H
#define CVC5__THEORY__EE_MANAGER__H

#include <map>
#include <memory>

#include "smt/env_obj.h"
#include "theory/ee_setup_info.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {

class TheoryEngine;

namespace theory {

class SharedSolver;

/**
 * This is (theory-agnostic) information associated with the management of
 * an equality engine for a single theory. This information is maintained
 * by the manager class below.
 *
 * Currently, this simply is the equality engine itself, for memory
 * management purposes.
 */
struct EeTheoryInfo
{
  EeTheoryInfo() : d_usedEe(nullptr) {}
  /** Equality engine that is used (if it exists) */
  eq::EqualityEngine* d_usedEe;
  /** Equality engine allocated specifically for this theory (if it exists) */
  std::unique_ptr<eq::EqualityEngine> d_allocEe;
};

/** Virtual base class for equality engine managers */
class EqEngineManager : protected EnvObj
{
 public:
   /**
   * @param te Reference to the theory engine
   * @param sharedSolver The shared solver that is being used in combination
   * with this equality engine manager
    */
  EqEngineManager(Env& env, TheoryEngine& te, SharedSolver& shs);
  virtual ~EqEngineManager() {}
  /**
   * Initialize theories, called during TheoryEngine::finishInit after theory
   * objects have been created but prior to their final initialization. This
   * sets up equality engines for all theories.
   *
   * This method is context-independent, and is applied once during
   * the lifetime of TheoryEngine (during finishInit).
   */
  virtual void initializeTheories() = 0;
  /**
   * Get the equality engine theory information for theory with the given id.
   */
  const EeTheoryInfo* getEeTheoryInfo(TheoryId tid) const;

  /** Allocate equality engine that is context-dependent on c with info esi */
  eq::EqualityEngine* allocateEqualityEngine(EeSetupInfo& esi,
                                             context::Context* c);
  /**
   * Notify this class that we are about to terminate with a model. This method
   * is for debugging only.
   *
   * @param incomplete Whether we are answering "unknown" instead of "sat".
   */
  virtual void notifyModel(bool incomplete) {}

 protected:
  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /** Reference to the shared solver */
  SharedSolver& d_sharedSolver;
  /** Information related to the equality engine, per theory. */
  std::map<TheoryId, EeTheoryInfo> d_einfo;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__EE_MANAGER__H */
