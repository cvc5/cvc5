/*********************                                                        */
/*! \file unsafe_interrupt_exception.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An exception that is thrown when the solver is out of time/resources
 ** and is interrupted in an unsafe state
 **/

#include "cvc4_public.h"

#ifndef CVC4__UNSAFE_INTERRUPT_EXCEPTION_H
#define CVC4__UNSAFE_INTERRUPT_EXCEPTION_H

#include "base/exception.h"
#include "cvc4_export.h"

namespace cvc5 {

class CVC4_EXPORT UnsafeInterruptException : public cvc5::Exception
{
 public:
  UnsafeInterruptException() :
    Exception("Interrupted in unsafe state due to "
              "time/resource limit.") {
  }

  UnsafeInterruptException(const std::string& msg) :
    Exception(msg) {
  }

  UnsafeInterruptException(const char* msg) :
    Exception(msg) {
  }
}; /* class UnsafeInterruptException */

}  // namespace cvc5

#endif /* CVC4__UNSAFE_INTERRUPT_EXCEPTION_H */
