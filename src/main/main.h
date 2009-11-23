/*********************                                           -*- C++ -*-  */
/** main.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** [[ Add file-specific comments here ]]
 **/

#include <exception>
#include <string>

#include "config.h"
#include "util/exception.h"
#include "util/options.h"

#ifndef __CVC4__MAIN__MAIN_H
#define __CVC4__MAIN__MAIN_H

namespace CVC4 {
namespace main {

class OptionException : public CVC4::Exception {
public:
  OptionException(const std::string& s) throw() : CVC4::Exception("Error in option parsing: " + s) {}
};/* class OptionException */

int parseOptions(int argc, char** argv, CVC4::Options*) throw(CVC4::Exception*);
void cvc4_init() throw();

}/* CVC4::main namespace */
}/* CVC4 namespace */

#endif /* __CVC4__MAIN__MAIN_H */
