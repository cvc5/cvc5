/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An exception that is thrown when an interactive-only feature while
 * cvc5 is being used in a non-interactive setting (for example, the
 * "(get-assertions)" command in an SMT-LIBv2 script).
 */

#include "cvc5_public.h"

#ifndef CVC5__SMT__MODAL_EXCEPTION_H
#define CVC5__SMT__MODAL_EXCEPTION_H

#include "base/exception.h"

namespace cvc5::internal {

class ModalException : public cvc5::internal::Exception
{
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
}; /* class ModalException */

/**
 * Special case of ModalException that allows the execution of the solver to
 * continue.
 *
 * TODO(#1108): This exception should not be needed anymore in future versions
 * of the public API.
 */
class RecoverableModalException : public cvc5::internal::ModalException
{
 public:
  RecoverableModalException(const std::string& msg) : ModalException(msg) {}

  RecoverableModalException(const char* msg) : ModalException(msg) {}
}; /* class RecoverableModalException */

}  // namespace cvc5::internal

#endif /* CVC5__SMT__MODAL_EXCEPTION_H */
