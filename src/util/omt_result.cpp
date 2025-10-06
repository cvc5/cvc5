/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Nestan Tsiskaridze
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Encapsulation of the result of an optimization query.
 */
#include "util/omt_result.h"

#include <sstream>

#include "base/check.h"
#include <iostream>

using namespace std;

namespace cvc5::internal {

OmtResult::OmtResult()
    : d_status(NONE), d_unknownExplanation(UnknownExplanation::UNKNOWN_REASON)
{
}

OmtResult::OmtResult(Status s, UnknownExplanation unknownExplanation)
    : d_status(s), d_unknownExplanation(unknownExplanation)
{
}

OmtResult::Status OmtResult::getStatus() const { return d_status; }

UnknownExplanation OmtResult::getUnknownExplanation() const
{
  return d_unknownExplanation;
}

bool OmtResult::operator==(const OmtResult& r) const
{
  return d_status == r.d_status
         && (d_status != UNKNOWN
             || d_unknownExplanation == r.d_unknownExplanation);
}

bool OmtResult::operator!=(const OmtResult& r) const
{
  return !(*this == r);
}

std::string OmtResult::toString() const
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

std::ostream& operator<<(std::ostream& out, const OmtResult& r)
{
  out << r.toString();
  return out;
}

ostream& operator<<(ostream& out, OmtResult::Status s)
{ 
  switch (s)
  {
    case OmtResult::NONE: out << "NONE"; break;
    case OmtResult::OPTIMAL: out << "OPTIMAL"; break;
    case OmtResult::LIMIT_OPTIMAL: out << "LIMIT_OPTIMAL"; break;
    case OmtResult::NON_OPTIMAL: out << "NON_OPTIMAL"; break;
    case OmtResult::UNBOUNDED: out << "UNBOUNDED"; break;  
    case OmtResult::UNSAT: out << "UNSAT"; break;
    case OmtResult::UNKNOWN: out << "UNKNOWN"; break;
    default: Unhandled() << s;
  }
  return out;
}

}  // namespace cvc5::internal
