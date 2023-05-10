/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Encapsulation of the result of a synthesis query.
 */
#include "util/synth_result.h"

#include <sstream>
#include "base/check.h"

using namespace std;

namespace cvc5::internal {

SynthResult::SynthResult()
    : d_status(NONE), d_unknownExplanation(UnknownExplanation::UNKNOWN_REASON)
{
}

SynthResult::SynthResult(Status s, UnknownExplanation unknownExplanation)
    : d_status(s), d_unknownExplanation(unknownExplanation)
{
}

SynthResult::Status SynthResult::getStatus() const { return d_status; }

UnknownExplanation SynthResult::getUnknownExplanation() const
{
  return d_unknownExplanation;
}

std::string SynthResult::toString() const
{
  std::stringstream ss;
  ss << "(" << d_status;
  if (d_unknownExplanation != UnknownExplanation::UNKNOWN_REASON)
  {
    ss << " :unknown-explanation " << d_unknownExplanation;
  }
  ss << ")";
  return ss.str();
}

std::ostream& operator<<(std::ostream& out, const SynthResult& r)
{
  out << r.toString();
  return out;
}

ostream& operator<<(ostream& out, SynthResult::Status s)
{
  switch (s)
  {
    case SynthResult::NONE: out << "NONE"; break;
    case SynthResult::SOLUTION: out << "SOLUTION"; break;
    case SynthResult::NO_SOLUTION: out << "NO_SOLUTION"; break;
    case SynthResult::UNKNOWN: out << "UNKNOWN"; break;
    default: Unhandled() << s;
  }
  return out;
}

}  // namespace cvc5::internal
