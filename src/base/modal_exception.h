/*********************                                                        */
/*! \file modal_exception.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andres Noetzli, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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

#ifndef CVC4__SMT__MODAL_EXCEPTION_H
#define CVC4__SMT__MODAL_EXCEPTION_H

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

/**
 * Special case of ModalException that allows the execution of the solver to
 * continue.
 *
 * TODO(#1108): This exception should not be needed anymore in future versions
 * of the public API.
 */
class CVC4_PUBLIC RecoverableModalException : public CVC4::ModalException {
 public:
  RecoverableModalException(const std::string& msg) : ModalException(msg) {}

  RecoverableModalException(const char* msg) : ModalException(msg) {}
}; /* class RecoverableModalException */

}/* CVC4 namespace */

#endif /* CVC4__SMT__MODAL_EXCEPTION_H */
