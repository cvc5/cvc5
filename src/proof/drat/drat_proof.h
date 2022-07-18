/******************************************************************************
 * Top contributors (to current version):
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Declares C++ types that represent a DRAT proof.
 * Defines serialization for these types.
 *
 * You can find an introduction to DRAT in the drat-trim paper:
 *    http://www.cs.utexas.edu/~marijn/publications/drat-trim.pdf
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__DRAT__DRAT_PROOF_H
#define CVC5__PROOF__DRAT__DRAT_PROOF_H

#include "prop/sat_solver.h"
#include "prop/sat_solver_types.h"

namespace cvc5::internal {
namespace proof {

class InvalidDratProofException : public cvc5::internal::Exception
{
 public:
  InvalidDratProofException() : Exception("Invalid DRAT Proof") {}

  InvalidDratProofException(const std::string& msg) : Exception(msg) {}

  InvalidDratProofException(const char* msg) : Exception(msg) {}
}; /* class InvalidDratProofException */

enum DratInstructionKind
{
  ADDITION,
  DELETION
};

struct DratInstruction
{
  DratInstruction(DratInstructionKind kind, prop::SatClause clause);

  DratInstructionKind d_kind;
  prop::SatClause d_clause;
};

class DratProof
{
 public:
  DratProof(const DratProof&) = default;

  DratProof(DratProof&&) = default;

  ~DratProof() = default;

  static DratProof fromPlain(const std::string& s);

  /**
   * @return The instructions in this proof
   */
  const std::vector<DratInstruction>& getInstructions() const;

 private:
  /**
   * Create an DRAT proof with no instructions.
   */
  DratProof();

  /**
   * The instructions of the DRAT proof.
   */
  std::vector<DratInstruction> d_instructions;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif  // CVC5__PROOF__DRAT__DRAT_PROOF_H