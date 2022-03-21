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

#include "cvc5_public.h"

#ifndef CVC5__UTIL__SYNTH_RESULT_H
#define CVC5__UTIL__SYNTH_RESULT_H

#include <iosfwd>
#include <string>
#include <vector>

#include "util/result.h"

namespace cvc5 {

/** A result for a synthesis query. */
class SynthResult
{
 public:
  enum Status
  {
    // the status has not been set
    NONE,
    // the
    SUCCESS,
    // the status is "sat"
    FAIL,
    // the status is "unknown"
    UNKNOWN
  };

 public:
  /** Default constructor */
  SynthResult();
  /** Constructor when the solution is successful */
  SynthResult(const std::vector<Node>& sol);
  /** Constructor when the solution is not successful */
  SynthResult(
      Status s,
      Result::UnknownExplanation unknownExplanation = Result::UNKNOWN_REASON);

  /** Get the status */
  Status getStatus() const;

  /** Get the unknown explanation */
  Result::UnknownExplanation getUnknownExplanation() const;

  /** Get the solution */
  const std::vector<Node>& getSolution() const;

 private:
  /** The status */
  Status d_status;
  /** The unknown explanation */
  UnknownExplanation d_unknownExplanation;
  /** The solution */
  std::vector<Node> d_solution;
};

std::ostream& operator<<(std::ostream& out, SynthResult::Status s);

}  // namespace cvc5

#endif /* CVC5__RESULT_H */
