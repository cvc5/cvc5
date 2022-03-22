/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Encapsulation of the result of a synthesis query.
 */
#include "expr/synth_result.h"

#include <sstream>

using namespace std;

namespace cvc5 {

SynthResult::SynthResult()
    : d_status(NONE), d_unknownExplanation(Result::UNKNOWN_REASON)
{
}

SynthResult::SynthResult(const std::map<Node, Node>& sol)
    : d_status(FOUND_SOLUTION),
      d_unknownExplanation(Result::UNKNOWN_REASON),
      d_solution(sol)
{
}

SynthResult::SynthResult(Status s,
                         Result::UnknownExplanation unknownExplanation)
    : d_status(s), d_unknownExplanation(unknownExplanation)
{
}

SynthResult::Status SynthResult::getStatus() const { return d_status; }

Result::UnknownExplanation SynthResult::getUnknownExplanation() const
{
  return d_unknownExplanation;
}

const std::map<Node, Node>& SynthResult::getSolution() const { return d_solution; }

std::string SynthResult::toString() const
{
  std::stringstream ss;
  ss << "(" << d_status;
  if (d_unknownExplanation != Result::UNKNOWN_REASON)
  {
    ss << " :unknown-explanation " << d_unknownExplanation;
  }
  if (!d_solution.empty())
  {
    ss << " :solution (";
    for (const std::pair<const Node, Node>& s : d_solution)
    {
      ss << "(" << s.first << " " << s.second << ")";
    }
    ss << ")";
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
    case SynthResult::FOUND_SOLUTION: out << "FOUND_SOLUTION"; break;
    case SynthResult::NO_SOLUTION: out << "NO_SOLUTION"; break;
    case SynthResult::UNKNOWN: out << "UNKNOWN"; break;
    default: Unhandled() << s;
  }
  return out;
}

}  // namespace cvc5
