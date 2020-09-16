/*********************                                                        */
/*! \file ee_setup_info.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Setup information for an equality engine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__EE_SETUP_INFO__H
#define CVC4__THEORY__EE_SETUP_INFO__H

#include <string>

namespace CVC4 {
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
  EeSetupInfo() : d_notify(nullptr), d_constantsAreTriggers(true) {}
  /** The notification class of the theory */
  eq::EqualityEngineNotify* d_notify;
  /** The name of the equality engine */
  std::string d_name;
  /** Constants are triggers */
  bool d_constantsAreTriggers;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__EE_SETUP_INFO__H */
