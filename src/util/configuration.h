/*********************                                                        */
/*! \file configuration.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Interface to a public class that provides compile-time information
 ** about the CVC4 library.
 **
 ** Interface to a public class that provides compile-time information
 ** about the CVC4 library.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__CONFIGURATION_H
#define __CVC4__CONFIGURATION_H

#include <string>

namespace CVC4 {

/**
 * Represents the (static) configuration of CVC4.
 */
class CVC4_PUBLIC Configuration {

  /** Private default ctor: Disallow construction of this class */
  Configuration();

public:

  static bool isDebugBuild();

  static bool isTracingBuild();

  static bool isMuzzledBuild();

  static bool isAssertionBuild();

  static bool isCoverageBuild();

  static bool isProfilingBuild();

  static bool isCompetitionBuild();

  static std::string getPackageName();

  static std::string getVersionString();

  static unsigned getVersionMajor();

  static unsigned getVersionMinor();

  static unsigned getVersionRelease();

  static std::string about();

  static bool isBuiltWithGmp();

  static bool isBuiltWithCln();
};

}/* CVC4 namespace */

#endif /* __CVC4__CONFIGURATION_H */
