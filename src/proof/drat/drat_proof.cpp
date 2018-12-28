/*********************                                                        */
/*! \file drat_proof.cpp
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
 ** Defines deserialization for DRAT proofs.
 **/

#include "proof/drat/drat_proof.h"
#include <bitset>

namespace CVC4 {
namespace proof {
namespace drat {

// Forward-declare helper functions for parsing the binary DRAT format.

/**
 * Parses a binary clause which starts at `start` and must not go beyond `end`
 *
 * Leaves the iterator one past the last byte that is a part of the clause.
 * That is, one past the null byte.
 *
 * If the clause overruns `end`, then raises a `InvalidDratProofException`.
 */
SatClause parse_binary_clause(std::string::const_iterator& start,
                              const std::string::const_iterator& proof_end);

/**
 * Parses a binary literal which starts at `start` and must not go beyond `end`
 *
 * Leaves the iterator one past the last byte that is a part of the clause.
 *
 * If the literal overruns `end`, then raises a `InvalidDratProofException`.
 */
SatLiteral parse_binary_literal(std::string::const_iterator& start,
                                const std::string::const_iterator& proof_end);

// DratInstruction implementation

DratInstruction::DratInstruction(DratInstructionKind kind, SatClause clause)
    : d_kind(kind), d_clause(clause)
{
  // All intialized
}

void DratInstruction::outputAsText(std::ostream& os) const
{
  switch (d_kind)
  {
    case DratInstructionKind::addition:
    {
      for (const SatLiteral& l : d_clause)
      {
        if (l.isNegated())
        {
          Debug("pf::drat") << '-' << l.getSatVariable() + 1 << ' ';
        }
        else
        {
          Debug("pf::drat") << l.getSatVariable() + 1 << ' ';
        }
      }
      Debug("pf::drat") << '0' << std::endl;
      break;
    }
    case DratInstructionKind::deletion:
    {
      Debug("pf::drat") << "d ";
      for (const SatLiteral& l : d_clause)
      {
        if (l.isNegated())
        {
          Debug("pf::drat") << '-' << l.getSatVariable() + 1 << ' ';
        }
        else
        {
          Debug("pf::drat") << l.getSatVariable() + 1 << ' ';
        }
      }
      Debug("pf::drat") << '0' << std::endl;
      break;
    }
    default: { Unreachable("Unknown DRAT instruction kind");
    }
  }
}

// DratProof implementation

DratProof::DratProof() : d_instructions() {}

// See the "binary format" section of
// https://www.cs.utexas.edu/~marijn/drat-trim/
DratProof DratProof::fromBinary(const std::string& s)
{
  DratProof proof;
  if (Debug.isOn("pf::drat"))
  {
    Debug("pf::drat") << "Parsing binary DRAT proof" << std::endl;
    Debug("pf::drat") << "proof length: " << s.length() << " bytes"
                      << std::endl;
    Debug("pf::drat") << "proof as bytes: ";
    for (char i : s)
    {
      if (i == 'a' || i == 'd')
      {
        Debug("pf::drat") << std::endl << "  " << std::bitset<8>(i);
      }
      else
      {
        Debug("pf::drat") << " " << std::bitset<8>(i);
      }
    }
    Debug("pf::drat") << std::endl << "parsing proof..." << std::endl;
  }

  // For each instruction
  for (auto i = s.cbegin(), end = s.cend(); i != end;)
  {
    switch (*i)
    {
      case 'a':
      {
        ++i;
        proof.d_instructions.emplace_back(addition,
                                          parse_binary_clause(i, end));
        break;
      }
      case 'd':
      {
        ++i;
        proof.d_instructions.emplace_back(deletion,
                                          parse_binary_clause(i, end));
        break;
      }
      default:
      {
        std::ostringstream s;
        s << "Invalid instruction in Drat proof. Instruction bits: "
          << std::bitset<8>(*i)
          << ". Expected 'a' (01100001) or 'd' "
             "(01100100).";
        throw InvalidDratProofException(s.str());
      }
    }
  }

  if (Debug.isOn("pf::drat"))
  {
    Debug("pf::drat") << "Printing out DRAT in textual format:" << std::endl;
    proof.outputAsText(Debug("pf::drat"));
  }

  return proof;
};

const std::vector<DratInstruction>& DratProof::getInstructions() const
{
  return d_instructions;
};

void DratProof::outputAsText(std::ostream& os) const
{
  for (const DratInstruction& instruction : d_instructions)
  {
    instruction.outputAsText(os);
    os << "\n";
  }
};

SatClause parse_binary_clause(std::string::const_iterator& start,
                              const std::string::const_iterator& proof_end)
{
  SatClause clause;
  // A clause is a 0-terminated sequence of literals
  while (start != proof_end)
  {
    // Is the clause done?
    if (*start == 0)
    {
      ++start;
      return clause;
    }
    else
    {
      // If not, parse another literal
      clause.emplace_back(parse_binary_literal(start, proof_end));
    }
  }
  // We've overrun the end of the byte stream.
  throw InvalidDratProofException(
      "Clause in DRAT proof was not done when "
      "EOF was encountered");
}

SatLiteral parse_binary_literal(std::string::const_iterator& start,
                                const std::string::const_iterator& proof_end)
{
  // lit is encoded as uint represented by a variable-length byte sequence
  uint64_t literal_represented_as_uint = 0;
  for (int shift = 0; start != proof_end; ++start, shift += 7)
  {
    unsigned char byte = *start;
    // The MSB of the byte is an indicator of whether the sequence continues
    bool continued = (byte >> 7) & 1;
    unsigned char numeric_part = byte & 0x7f;
    literal_represented_as_uint |= numeric_part << shift;
    if (!continued)
    {
      // LSB of `literal_represented_as_uint` indicates negation.
      bool negated = literal_represented_as_uint & 1;
      // Rest is the literal number
      SatVariable var_number = literal_represented_as_uint >> 1;
      ++start;
      // Internal clauses start at 0, external ones start at 1.
      return SatLiteral(var_number - 1, negated);
    }
  }
  throw InvalidDratProofException(
      "Literal in DRAT proof was not done when "
      "EOF was encountered");
}

}  // namespace drat
}  // namespace proof
}  // namespace CVC4
