/*********************                                                        */
/*! \file modal_exception.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An exception that is thrown when an interactive-only
 ** feature while CVC4 is being used in a non-interactive setting
 **
 ** An exception that is thrown when an interactive-only feature while
 ** CVC4 is being used in a non-interactive setting (for example, the
 ** "(get-assertions)" command in an SMT-LIBv2 script).
 **/

#include "cvc4_public.h"

#ifndef __CVC4__SMT__MODAL_EXCEPTION_H
#define __CVC4__SMT__MODAL_EXCEPTION_H

#include "base/exception.h"

namespace CVC4 {

class CVC4_PUBLIC ModalException : public CVC4::Exception {
public:
  ModalException() :
    Exception("Feature used while operating in "
              "incorrect state") {
  }

  ModalException(const std::string& msg) :
    Exception(msg) {
  }

  ModalException(const char* msg) :
    Exception(msg) {
  }
};/* class ModalException */

}/* CVC4 namespace */

#endif /* __CVC4__SMT__MODAL_EXCEPTION_H */
