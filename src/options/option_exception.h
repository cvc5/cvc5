/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

/**
 * Class representing an option-parsing exception involving an illegal
 * combination of options. In contrast to OptionException, it is treated as an
 * unrecoverable exception in the API.
 *
 * At a high level, this exception is used when the user requests a illegal
 * combination of options. It is *not* used in other cases, e.g., when the
 * user requests an option that does not exist.
 *
 * In particular, we use this exception in two places:
 * (1) If the SetDefaults detects an options misconfiguration, e.g., at the
 *     beginning of a `check-sat` command, in which case any exception is
 *     treated as unrecoverable.
 * (2) If we discover an illegal combination of options during a `set-option`
 *     command (e.g., due to restrictions on `safe-options`).
 *
 * The latter is made a fatal exception for consistency, since some
 * options misconfigurations are discovered during SetDefaults and others
 * are detected eagerly. In either case we should abort.
 */
class CVC5_EXPORT FatalOptionException : public cvc5::internal::Exception
{
 public:
  FatalOptionException(const std::string& s)
      : cvc5::internal::Exception(s_errPrefix + s)
  {
  }

  /**
   * Get the error message without the prefix that is automatically added for
   * OptionExceptions.
   * @return The raw error message.
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
