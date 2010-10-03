/*********************                                                        */
/*! \file configuration.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): acsys, cconway
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
#include "util/configuration_private.h"

using namespace std;

namespace CVC4 {

bool Configuration::isDebugBuild() {
  return IS_DEBUG_BUILD;
}

bool Configuration::isTracingBuild() {
  return IS_TRACING_BUILD;
}

bool Configuration::isMuzzledBuild() {
  return IS_MUZZLED_BUILD;
}

bool Configuration::isAssertionBuild() {
  return IS_ASSERTIONS_BUILD;
}

bool Configuration::isCoverageBuild() {
  return IS_COVERAGE_BUILD;
}

bool Configuration::isProfilingBuild() {
  return IS_PROFILING_BUILD;
}

bool Configuration::isCompetitionBuild() {
  return IS_COMPETITION_BUILD;
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
  return CVC4_ABOUT_STRING;
}

bool Configuration::isBuiltWithGmp() {
  return IS_GMP_BUILD;
}

bool Configuration::isBuiltWithCln() {
  return IS_CLN_BUILD;
}

bool Configuration::isBuiltWithTlsSupport() {
  return USING_TLS;
}

}/* CVC4 namespace */
