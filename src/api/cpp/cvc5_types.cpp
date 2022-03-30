/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common cvc5 types. These types are used internally as well as externally and
 * the language bindings are generated automatically.
 */

#include "api/cpp/cvc5_types.h"

#include <iostream>

#include "base/check.h"

namespace cvc5 {

std::ostream& operator<<(std::ostream& out, UnknownExplanation e)
{
  switch (e)
  {
    case UnknownExplanation::REQUIRES_FULL_CHECK:
      out << "REQUIRES_FULL_CHECK";
      break;
    case UnknownExplanation::INCOMPLETE: out << "INCOMPLETE"; break;
    case UnknownExplanation::TIMEOUT: out << "TIMEOUT"; break;
    case UnknownExplanation::RESOURCEOUT: out << "RESOURCEOUT"; break;
    case UnknownExplanation::MEMOUT: out << "MEMOUT"; break;
    case UnknownExplanation::INTERRUPTED: out << "INTERRUPTED"; break;
    case UnknownExplanation::NO_STATUS: out << "NO_STATUS"; break;
    case UnknownExplanation::UNSUPPORTED: out << "UNSUPPORTED"; break;
    case UnknownExplanation::OTHER: out << "OTHER"; break;
    case UnknownExplanation::UNKNOWN_REASON: out << "UNKNOWN_REASON"; break;
    default: Unhandled() << e;
  }
  return out;
}

}  // namespace cvc5
