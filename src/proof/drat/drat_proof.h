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

/**
 * A DRAT proof has two kinds of instruction, to add and to delete clauses.
 */
enum DratInstructionKind
{
  ADDITION,
  DELETION
};

/**
 * Structure to handle a line from the DRAT proof, which is an instruction.
 * The instruction must have a kind and a clause.
 */
struct DratInstruction
{
  DratInstruction(DratInstructionKind kind, const prop::SatClause& clause);

  DratInstructionKind d_kind;
  prop::SatClause d_clause;
};

/**
 * Class to handle a DRAT proof.
 *
 * A DratProof instance is a sequence of DratInstructions built from a DRAT
 * proof.
 */
class DratProof
{
 public:
  /**
   * Create a DRAT proof with no instructions.
   */
  DratProof();

  ~DratProof() = default;

  /**
   * Converts a plain format DRAT proof to a DratProof instance.
   *
   * @param s string containing the plain DRAT proof.
   * @return DratProof instance containing the instructions.
   */
  static DratProof fromPlain(const std::string& s);

  /**
   * @return The instructions in this proof.
   */
  const std::vector<DratInstruction>& getInstructions() const;

 private:
  /**
   * The instructions of the DRAT proof.
   */
  std::vector<DratInstruction> d_instructions;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif  // CVC5__PROOF__DRAT__DRAT_PROOF_H