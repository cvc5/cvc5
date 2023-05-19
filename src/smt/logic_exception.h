/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An exception that is thrown when a feature is used outside
 * the logic that cvc5 is currently using (for example, a quantifier
 * is used while running in a quantifier-free logic).
 */

#include "cvc5_public.h"

#ifndef CVC5__SMT__LOGIC_EXCEPTION_H
#define CVC5__SMT__LOGIC_EXCEPTION_H

#include "base/exception.h"

namespace cvc5::internal {

class LogicException : public cvc5::internal::Exception
{
 public:
  LogicException() :
    Exception("Feature used while operating in "
              "incorrect state") {
  }

  LogicException(const std::string& msg) :
    Exception(msg) {
  }

  LogicException(const char* msg) :
    Exception(msg) {
  }
}; /* class LogicException */

}  // namespace cvc5::internal

#endif /* CVC5__SMT__LOGIC_EXCEPTION_H */
