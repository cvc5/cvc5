/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

/**
 * Prepends a logic exception with the text "Logic restricted in safe mode".
 * This kind of logic exception should be thrown for any failure that is
 * admissible in safe mode. The regression testers will consider any exception
 * having text "in safe mode" as an admissible failure, and skip the benchmark.
 */
class SafeLogicException : public LogicException
{
 public:
  SafeLogicException(const std::string& s)
#if defined(CVC5_SAFE_MODE) || defined(CVC5_STABLE_MODE)
      : LogicException("Logic restricted in safe mode. " + s)
#else
      : LogicException(s)
#endif
  {
  }
};

}  // namespace cvc5::internal

#endif /* CVC5__SMT__LOGIC_EXCEPTION_H */
