/*********************                                                        */
/** configuration.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** SmtEngine: the main public entry point of libcvc4.
 **/

#ifndef __CVC4__CONFIGURATION_H
#define __CVC4__CONFIGURATION_H

#include "config.h"
#include "cvc4_config.h"

namespace CVC4 {

/**
 * Represents the (static) configuration of CVC4.
 */
class CVC4_PUBLIC Configuration {

  /** Private default ctor: Disallow construction of this class */
  Configuration();

public:

  static bool isDebugBuild() {
#ifdef CVC4_DEBUG
    return true;
#else /* CVC4_DEBUG */
    return false;
#endif /* CVC4_DEBUG */
  }

  static bool isTracingBuild() {
#ifdef CVC4_TRACING
    return true;
#else /* CVC4_TRACING */
    return false;
#endif /* CVC4_TRACING */
  }

  static bool isMuzzledBuild() {
#ifdef CVC4_MUZZLE
    return true;
#else /* CVC4_MUZZLE */
    return false;
#endif /* CVC4_MUZZLE */
  }

  static bool isAssertionBuild() {
#ifdef CVC4_ASSERTIONS
    return true;
#else /* CVC4_ASSERTIONS */
    return false;
#endif /* CVC4_ASSERTIONS */
  }

  static bool isCoverageBuild() {
#ifdef CVC4_COVERAGE
    return true;
#else /* CVC4_COVERAGE */
    return false;
#endif /* CVC4_COVERAGE */
  }

  static bool isProfilingBuild() {
#ifdef CVC4_PROFILING
    return true;
#else /* CVC4_PROFILING */
    return false;
#endif /* CVC4_PROFILING */
  }

  static std::string getPackageName() {
    return PACKAGE;
  }

  static std::string getVersionString() {
    return VERSION;
  }

  static unsigned getVersionMajor() {
    return 0;
  }

  static unsigned getVersionMinor() {
    return 0;
  }

  static unsigned getVersionRelease() {
    return 0;
  }

  static std::string about() {
    return std::string("\
This is a pre-release of CVC4.\n\
Copyright (C) 2009, 2010\n\
  The ACSys Group\n\
  Courant Institute of Mathematical Sciences,\n\
  New York University\n\
  New York, NY  10012  USA\n");
  }

};

}/* CVC4 namespace */

#endif /* __CVC4__CONFIGURATION_H */
