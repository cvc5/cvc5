/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz, Nestan Tsiskaridze
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

#include "cvc5_public.h"

#ifndef CVC5__UTIL__OMT_RESULT_H
#define CVC5__UTIL__OMT_RESULT_H

#include <iosfwd>
#include <string>

#include "util/result.h"

namespace cvc5::internal {

/**
 * A result for an optimization query.
 */
class OmtResult
{
 public:
  enum Status
  {
    // the status has not been set
    NONE,
    // the optimization query succeeded with an optimal solution 
    OPTIMAL,
    // the optimization problem succeded with an asymptotically optimal 
    // solutions, i.e. the objective value is asymptotically approaching  
    // a finite extreme that cannot be exactly reached
    LIMIT_OPTIMAL,
    // the optimization query was interrupted providing an approximate 
    // solution, i.e. a solution from an anytime procedure
    NON_OPTIMAL,
    // the optimization query determined the problem is unbounded
    UNBOUNDED,
    // the optimization query determined the constraint in the problem is
    // unsatisfiable
    UNSAT,
    // the outcome of the optimization query is unknown
    UNKNOWN
  };

 public:
  /** Default constructor */
  OmtResult();

  /** Constructor for all outcomes, with optional explanation when 
   * solution is not optimal */
  OmtResult(Status s,
            UnknownExplanation unknownExplanation =
                UnknownExplanation::UNKNOWN_REASON);

  /** Get the status */
  Status getStatus() const;

  /** Get the unknown explanation */
  UnknownExplanation getUnknownExplanation() const;

  /** Get the string representation */
  std::string toString() const;

 private:
  /** The status */
  Status d_status;
  /** The unknown explanation */
  UnknownExplanation d_unknownExplanation;
};

std::ostream& operator<<(std::ostream& out, const OmtResult& r);
std::ostream& operator<<(std::ostream& out, OmtResult::Status s);

}  // namespace cvc5::internal

#endif /* CVC5__UTIL__OMT_RESULT_H */
