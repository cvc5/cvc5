/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Setup information for an equality engine.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__EE_SETUP_INFO__H
#define CVC5__THEORY__EE_SETUP_INFO__H

#include <string>

namespace cvc5 {
namespace theory {

namespace eq {
class EqualityEngineNotify;
}

/**
 * This is a helper class that encapsulates instructions for how a Theory
 * wishes to initialize and setup notifications with its official equality
 * engine, e.g. via a notification class (eq::EqualityEngineNotify).
 *
 * This includes (at a basic level) the arguments to the equality engine
 * constructor that theories may wish to modify. This information is determined
 * by the Theory during needsEqualityEngine.
 */
struct EeSetupInfo
{
  EeSetupInfo()
      : d_notify(nullptr), d_constantsAreTriggers(true), d_useMaster(false)
  {
  }
  /** The notification class of the theory */
  eq::EqualityEngineNotify* d_notify;
  /** The name of the equality engine */
  std::string d_name;
  /** Constants are triggers */
  bool d_constantsAreTriggers;
  /**
   * Whether we want our state to use the master equality engine. This should
   * be true exclusively for the theory of quantifiers.
   */
  bool d_useMaster;
};

}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__EE_SETUP_INFO__H */
