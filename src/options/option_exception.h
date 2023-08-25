/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

#include <cvc5/cvc5_export.h>

#include "base/exception.h"

namespace cvc5::internal {

/**
 * Class representing an option-parsing exception such as badly-typed
 * or missing arguments, arguments out of bounds, etc.
 */
class CVC5_EXPORT OptionException : public cvc5::internal::Exception
{
 public:
  OptionException(const std::string& s) : cvc5::internal::Exception(s_errPrefix + s) {}

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

}  // namespace cvc5::internal

#endif /* CVC5__OPTION_EXCEPTION_H */
