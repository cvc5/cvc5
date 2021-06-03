/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Options-related exceptions.
 */

#include "cvc5_public.h"

#ifndef CVC5__OPTION_EXCEPTION_H
#define CVC5__OPTION_EXCEPTION_H

#include "base/exception.h"
#include "cvc5_export.h"

namespace cvc5 {

/**
 * Class representing an option-parsing exception such as badly-typed
 * or missing arguments, arguments out of bounds, etc.  If an option
 * name is itself unrecognized, a UnrecognizedOptionException (a derived
 * class, below) should be used instead.
 */
class CVC5_EXPORT OptionException : public cvc5::Exception
{
 public:
  OptionException(const std::string& s) : cvc5::Exception(s_errPrefix + s) {}

  /**
   * Get the error message without the prefix that is automatically added for
   * OptionExceptions.
   */
  std::string getRawMessage() const
  {
    return getMessage().substr(s_errPrefix.size());
  }

 private:
  /** The string to be added in front of the actual error message */
  static const std::string s_errPrefix;
}; /* class OptionException */

/**
 * Class representing an exception in option processing due to an
 * unrecognized or unsupported option key.
 */
class UnrecognizedOptionException : public cvc5::OptionException
{
 public:
  UnrecognizedOptionException()
      : cvc5::OptionException(
          "Unrecognized informational or option key or setting")
  {
  }

  UnrecognizedOptionException(const std::string& msg)
      : cvc5::OptionException(
          "Unrecognized informational or option key or setting: " + msg)
  {
  }
}; /* class UnrecognizedOptionException */

}  // namespace cvc5

#endif /* CVC5__OPTION_EXCEPTION_H */
