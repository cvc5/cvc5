/*********************                                                        */
/*! \file no_such_function_exception.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief An exception that is thrown when an option setting is not
 ** understood.
 **
 ** An exception that is thrown when an interactive-only feature while
 ** CVC4 is being used in a non-interactive setting (for example, the
 ** "(get-assertions)" command in an SMT-LIBv2 script).
 **/

#include "cvc4_public.h"

#ifndef __CVC4__SMT__NO_SUCH_FUNCTION_EXCEPTION_H
#define __CVC4__SMT__NO_SUCH_FUNCTION_EXCEPTION_H

#include "util/exception.h"

namespace CVC4 {

class CVC4_PUBLIC NoSuchFunctionException : public CVC4::Exception {
public:
  NoSuchFunctionException(Expr name) :
    Exception(std::string("Undefined function: `") + name.toString() + "': ") {
  }

  NoSuchFunctionException(Expr name, const std::string& msg) :
    Exception(std::string("Undefined function: `") + name.toString() + "': " + msg) {
  }
};/* class NoSuchFunctionException */

}/* CVC4 namespace */

#endif /* __CVC4__SMT__NO_SUCH_FUNCTION_EXCEPTION_H */
