/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
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

#include "cvc5_public.h"

#ifndef CVC5__EXPR__SYNTH_RESULT_H
#define CVC5__EXPR__SYNTH_RESULT_H

#include <iosfwd>
#include <string>

#include "util/result.h"

namespace cvc5::internal {

/**
 * A result for a synthesis query. This can be used for synthesis, abduction,
 * interpolation, and quantifier elimination.
 */
class SynthResult
{
 public:
  enum Status
  {
    // the status has not been set
    NONE,
    // the synthesis query was successful, i.e. there is a solution
    SOLUTION,
    // the synthesis query resulted in failure, i.e. there is no solution
    NO_SOLUTION,
    // the synthesis query is unknown, i.e. it is not known whether there is a
    // solution.
    UNKNOWN
  };

 public:
  /** Default constructor */
  SynthResult();
  /** Constructor when the solution is not successful */
  SynthResult(Status s,
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

std::ostream& operator<<(std::ostream& out, const SynthResult& r);
std::ostream& operator<<(std::ostream& out, SynthResult::Status s);

}  // namespace cvc5::internal

#endif /* CVC5__RESULT_H */
