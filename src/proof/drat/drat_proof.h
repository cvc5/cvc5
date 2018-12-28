/*********************                                                        */
/*! \file drat_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief DRAT Proof Format
 **
 ** Declares C++ types that represent a DRAT proof.
 ** Defines serialization for these types.
 **
 ** You can find an introduction to DRAT in the drat-trim paper:
 **    http://www.cs.utexas.edu/~marijn/publications/drat-trim.pdf
 **
 **/

#ifndef __CVC4__PROOF__DRAT__DRAT_PROOF_H
#define __CVC4__PROOF__DRAT__DRAT_PROOF_H

#include "cvc4_private.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_types.h"

namespace CVC4 {
namespace proof {
namespace drat {

using CVC4::prop::SatClause;
using CVC4::prop::SatLiteral;
using CVC4::prop::SatVariable;

class CVC4_PUBLIC InvalidDratProofException : public CVC4::Exception
{
 public:
  InvalidDratProofException() : Exception("Invalid DRAT Proof") {}

  InvalidDratProofException(const std::string& msg) : Exception(msg) {}

  InvalidDratProofException(const char* msg) : Exception(msg) {}
}; /* class InvalidDratProofException */

enum DratInstructionKind
{
  addition,
  deletion
};

struct DratInstruction
{
 public:
  DratInstructionKind kind;
  SatClause clause;
  DratInstruction(DratInstructionKind kind, SatClause clause);
};

class DratProof
{
 public:
  DratProof(const DratProof&) = default;

  DratProof(DratProof&&) = default;

  ~DratProof() = default;

  /**
   * Parses a DRAT proof from the binary format.
   * The format is described at:
   *    https://www.cs.utexas.edu/~marijn/drat-trim/#contact
   *
   * @param binaryProof a string containing the bytes of the "binary" proof
   *
   * @return the parsed proof
   */
  static DratProof fromBinary(const std::string& binaryProof);

  /**
   * @return The instructions in this proof
   */
  const std::vector<DratInstruction>& getInstructions() const;

  /**
   * Write the DRAT proof in textual format.
   * The format is described in:
   *    http://www.cs.utexas.edu/~marijn/publications/drat-trim.pdf
   *
   * @param os the stream to write to
   */
  void outputAsText(std::ostream& os) const;

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

/**
 * Write a DRAT instruction in textual format.
 * The format is described in:
 *    http://www.cs.utexas.edu/~marijn/publications/drat-trim.pdf
 *
 * @param out the stream to write to
 * @param instr the instruction
 *
 * @return the stream written to
 */
inline std::ostream& operator<<(std::ostream& out, const DratInstruction& instr)
{
  switch (instr.kind)
  {
    case addition:
    {
      out << instr.clause;
      break;
    }
    case deletion:
    {
      out << "d " << instr.clause;
      break;
    }
    default:
    {
      out << " unknown instruction type! ";
      break;
    }
  }
  return out;
}

}  // namespace drat
}  // namespace proof
}  // namespace CVC4

#endif  // __CVC4__PROOF__DRAT__DRAT_PROOF_H
