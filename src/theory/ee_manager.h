/*********************                                                        */
/*! \file ee_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for management of equality engines.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__EE_MANAGER__H
#define CVC4__THEORY__EE_MANAGER__H

#include <map>
#include <memory>

#include "theory/ee_setup_info.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {

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
class EqEngineManager
{
 public:
  virtual ~EqEngineManager() {}
  /**
   * Finish initialize, called by TheoryEngine::finishInit after theory
   * objects have been created but prior to their final initialization. This
   * sets up equality engines for all theories.
   *
   * This method is context-independent, and is applied once during
   * the lifetime of TheoryEngine (during finishInit).
   */
  virtual void initializeTheories() = 0;
  /**
   * Finish initialize, called by TheoryEngine::finishInit after theory
   * objects have been created but prior to their final initialization. This
   * sets up equality engines for all theories.
   *
   * This method is context-independent, and is applied once during
   * the lifetime of TheoryEngine (during finishInit).
   */
  virtual void initializeModel(TheoryModel* m,
                               eq::EqualityEngineNotify* notify) = 0;
  /**
   * Get the equality engine theory information for theory with the given id.
   */
  const EeTheoryInfo* getEeTheoryInfo(TheoryId tid) const;
  /**
   * Get the core equality engine, which is the equality engine that the
   * quantifiers engine should use. This corresponds to the master equality
   * engine if eeMode is distributed, or the central equality engine if eeMode
   * is central.
   */
  virtual eq::EqualityEngine* getCoreEqualityEngine() = 0;

 protected:
  /** Information related to the equality engine, per theory. */
  std::map<TheoryId, EeTheoryInfo> d_einfo;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__EE_MANAGER__H */
