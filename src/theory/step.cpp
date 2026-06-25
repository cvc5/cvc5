/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A generic, reusable strategy container shared by theory solvers.
 */

#include "theory/step.h"

#include "base/check.h"

namespace cvc5::internal {
namespace theory {

std::ostream& operator<<(std::ostream& out, Step s)
{
  switch (s)
  {
    case Step::NONE: out << "NONE"; break;
    case Step::BREAK: out << "BREAK"; break;
    case Step::SETS_CHECK_BASIC: out << "SETS_CHECK_BASIC"; break;
    case Step::SETS_CHECK_CARDINALITY: out << "SETS_CHECK_CARDINALITY"; break;
    case Step::SETS_CHECK_RELATIONS: out << "SETS_CHECK_RELATIONS"; break;
    case Step::SETS_CHECK_TRANSITIVE_CLOSURE:
      out << "SETS_CHECK_TRANSITIVE_CLOSURE";
      break;
    case Step::SETS_CHECK_FILTER: out << "SETS_CHECK_FILTER"; break;
    case Step::SETS_CHECK_MAP: out << "SETS_CHECK_MAP"; break;
    case Step::UNKNOWN: out << "?"; break;
    default:
      Unreachable();
      out << "?unhandled";
      break;
  }
  return out;
}
}  // namespace theory
}  // namespace cvc5::internal
