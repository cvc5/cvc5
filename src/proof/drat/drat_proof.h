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
 **/

#pragma once

#include "cvc4_private.h"
#include "proof/bitvector_proof.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_types.h"

namespace CVC4 {
namespace proof {
namespace drat {

using CVC4::prop::SatClause;
using CVC4::prop::SatLiteral;
using CVC4::prop::SatVariable;

class CVC4_PUBLIC InvalidDRATProofException : public CVC4::Exception
{
 public:
  InvalidDRATProofException() : Exception("Invalid DRAT Proof") {}

  InvalidDRATProofException(const std::string& msg) : Exception(msg) {}

  InvalidDRATProofException(const char* msg) : Exception(msg) {}
}; /* class InvalidDRATProofException */

enum DRATInstructionKind
{
  addition,
  deletion
};

struct DRATInstruction
{
 public:
  DRATInstructionKind kind;
  SatClause clause;
  DRATInstruction(DRATInstructionKind kind, SatClause clause);
};

inline std::ostream& operator<<(std::ostream& out, const DRATInstruction& instr)
{
  switch (instr.kind)
  {
    case addition:
    {
      out << "a " << instr.clause;
      break;
    }
    case deletion:
    {
      out << "d " << instr.clause;
      break;
    }
    default: { out << " unknown instruction type! ";
    }
  }
  return out;
}

class DRATProof
{
 private:
  mutable std::vector<DRATInstruction> d_instructions;
  mutable std::ostringstream d_binary_formatted_proof;
  mutable bool d_parsed;

  void parse() const;

 public:
  DRATProof();
  std::ostringstream& getOStringStream();
  const std::vector<DRATInstruction>& getInstructions() const;
};

}  // namespace drat
}  // namespace proof
}  // namespace CVC4
