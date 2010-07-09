/*********************                                                        */
/*! \file configuration.cpp
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
 ** \brief Implementation of Configuration class, which provides compile-time
 ** configuration information about the CVC4 library.
 **
 ** Implementation of Configuration class, which provides compile-time
 ** configuration information about the CVC4 library.
 **/

#include "util/configuration.h"
#include "cvc4autoconfig.h"

using namespace std;

namespace CVC4 {

bool Configuration::isDebugBuild() {
#ifdef CVC4_DEBUG
  return true;
#else /* CVC4_DEBUG */
  return false;
#endif /* CVC4_DEBUG */
}

bool Configuration::isTracingBuild() {
#ifdef CVC4_TRACING
  return true;
#else /* CVC4_TRACING */
  return false;
#endif /* CVC4_TRACING */
}

bool Configuration::isMuzzledBuild() {
#ifdef CVC4_MUZZLE
  return true;
#else /* CVC4_MUZZLE */
  return false;
#endif /* CVC4_MUZZLE */
}

bool Configuration::isAssertionBuild() {
#ifdef CVC4_ASSERTIONS
  return true;
#else /* CVC4_ASSERTIONS */
  return false;
#endif /* CVC4_ASSERTIONS */
}

bool Configuration::isCoverageBuild() {
#ifdef CVC4_COVERAGE
  return true;
#else /* CVC4_COVERAGE */
  return false;
#endif /* CVC4_COVERAGE */
}

bool Configuration::isProfilingBuild() {
#ifdef CVC4_PROFILING
  return true;
#else /* CVC4_PROFILING */
  return false;
#endif /* CVC4_PROFILING */
}

bool Configuration::isCompetitionBuild() {
#ifdef CVC4_COMPETITION_MODE
  return true;
#else /* CVC4_COMPETITION_MODE */
  return false;
#endif /* CVC4_COMPETITION_MODE */
}

string Configuration::getPackageName() {
  return PACKAGE_NAME;
}

string Configuration::getVersionString() {
  return CVC4_RELEASE_STRING;
}

unsigned Configuration::getVersionMajor() {
  return CVC4_MAJOR;
}

unsigned Configuration::getVersionMinor() {
  return CVC4_MINOR;
}

unsigned Configuration::getVersionRelease() {
  return CVC4_RELEASE;
}

string Configuration::about() {
  return string("\
This is a pre-release of CVC4.\n\
Copyright (C) 2009, 2010\n\
  The ACSys Group\n\
  Courant Institute of Mathematical Sciences\n\
  New York University\n\
  New York, NY  10012  USA\n\n") +
    (isBuiltWithCln() ? "\
This CVC4 library uses CLN as its multi-precision arithmetic library.\n\n\
CVC4 is open-source and is covered by the BSD license (modified).\n\
However, CLN, the Class Library for Numbers, is covered by the GPL.  Thus\n\
this CVC4 library cannot be used in proprietary applications.  Please\n\
consult the CVC4 documentation for instructions about building a version\n\
of CVC4 that links against GMP, and can be used in such applications.\n" :
"This CVC4 library uses GMP as its multi-precision arithmetic library.\n\n\
CVC4 is open-source and is covered by the BSD license (modified).\n");
}

bool Configuration::isBuiltWithGmp() {
#ifdef CVC4_GMP_IMP
  return true;
#else /* CVC4_GMP_IMP */
  return false;
#endif /* CVC4_GMP_IMP */
}

bool Configuration::isBuiltWithCln() {
#ifdef CVC4_CLN_IMP
  return true;
#else /* CVC4_CLN_IMP */
  return false;
#endif /* CVC4_CLN_IMP */
}

}/* CVC4 namespace */
