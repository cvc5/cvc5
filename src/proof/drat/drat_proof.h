/*********************                                                        */
/*! \file drat_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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

#ifndef CVC4__PROOF__DRAT__DRAT_PROOF_H
#define CVC4__PROOF__DRAT__DRAT_PROOF_H

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
  ADDITION,
  DELETION
};

struct DratInstruction
{
  DratInstruction(DratInstructionKind kind, SatClause clause);

  /**
   * Write the DRAT instruction in textual format.
   * The format is described in:
   *    http://www.cs.utexas.edu/~marijn/publications/drat-trim.pdf
   *
   * @param os the stream to write to
   */
  void outputAsText(std::ostream& os) const;

  DratInstructionKind d_kind;
  SatClause d_clause;
};

class DratProof
{
 public:
  DratProof(const DratProof&) = default;

  DratProof(DratProof&&) = default;

  ~DratProof() = default;

  /**
   * Parses a DRAT proof from the **binary format**.
   * The format is described at:
   *    https://www.cs.utexas.edu/~marijn/drat-trim/#contact
   *
   * What do the standard authors mean by the format being "binary"?
   * They just mean that proofs in this format should be understood as
   * sequences of bytes, not sequences of ASCII/Unicode/your favorite character
   * set characters.
   *
   * @param binaryProof a string containing the bytes of the binary proof.
   *        Even though the proof isn't text, it's safe to store it in a string
   *        because C++ strings don't make any gaurantees about the encoding of
   *        their contents. This makes them (effectively) just byte sequences.
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

  /**
   * Write the DRAT proof as an LFSC value
   * The format is from the LFSC signature drat.plf
   *
   * Reads the current `ProofManager` to determine what the variables should be
   * named.
   *
   * @param os the stream to write to
   * @param indentation the number of spaces to indent each proof instruction
   */
  void outputAsLfsc(std::ostream& os, uint8_t indentation) const;

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

}  // namespace drat
}  // namespace proof
}  // namespace CVC4

#endif  // CVC4__PROOF__DRAT__DRAT_PROOF_H
