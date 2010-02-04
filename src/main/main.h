/*********************                                                        */
/** main.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan, barrett
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Header for main CVC4 driver.
 **/

#include <exception>
#include <string>

#include "config.h"
#include "util/exception.h"

#ifndef __CVC4__MAIN__MAIN_H
#define __CVC4__MAIN__MAIN_H

namespace CVC4 {

struct Options;

namespace main {

/** Class representing an option-parsing exception. */
class OptionException : public CVC4::Exception {
public:
  OptionException(const std::string& s) throw() :
    CVC4::Exception("Error in option parsing: " + s) {
  }
};/* class OptionException */

/** Full argv[0] */
extern const char *progPath;

/** Just the basename component of argv[0] */
extern const char *progName;

/**
 * If true, will not spin on segfault even when CVC4_DEBUG is on.
 * Useful for nightly regressions, noninteractive performance runs
 * etc.  See util.cpp.
 */
extern bool segvNoSpin;

/** Parse argc/argv and put the result into a CVC4::Options struct. */
int parseOptions(int argc, char** argv, CVC4::Options*) throw(OptionException);

/** Initialize the driver.  Sets signal handlers for SIGINT and SIGSEGV. */
void cvc4_init() throw();

}/* CVC4::main namespace */
}/* CVC4 namespace */

#endif /* __CVC4__MAIN__MAIN_H */
