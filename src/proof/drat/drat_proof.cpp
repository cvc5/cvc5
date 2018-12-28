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

#include "proof/drat_proof.h"
#include <bitset>

namespace CVC4 {
namespace proof {
namespace drat {

// Helper functions for parsing the binary DRAT format.
SatClause parse_binary_clause(std::string::const_iterator& start,
                              const std::string::const_iterator& proof_end);

SatLiteral parse_binary_literal(std::string::const_iterator& start,
                                const std::string::const_iterator& proof_end);

DRATInstruction::DRATInstruction(DRATInstructionKind kind, SatClause clause)
    : kind(kind), clause(clause)
{
  // All intialized
}

DRATProof::DRATProof()
    : d_instructions(), d_binary_formatted_proof(), d_parsed(false)
{
}

// See the "binary format" section of
// https://www.cs.utexas.edu/~marijn/drat-trim/
void DRATProof::parse() const
{
  std::string s = d_binary_formatted_proof.str();
  if (Debug.isOn("pf::drat"))
  {
    Debug("pf::drat") << "proof length: " << s.length() << " bytes"
                      << std::endl;
    Debug("pf::drat") << "proof as bits: ";
    for (auto i = s.cbegin(); i != s.cend(); ++i)
    {
      if (*i == 'a' || *i == 'd')
      {
        Debug("pf::drat") << std::endl << "  " << std::bitset<8>(*i);
      }
      else
      {
        Debug("pf::drat") << " " << std::bitset<8>(*i);
      }
    }
    Debug("pf::drat") << std::endl << "parsing proof..." << std::endl;
  }

  Assert(!d_parsed, "Why are you trying to parse a DRAT proof more than once?");
  auto end = s.cend();
  // For each instruction
  for (auto i = s.cbegin(); i != end;)
  {
    switch (*i)
    {
      case 'a':
      {
        ++i;
        DRATInstruction d =
            DRATInstruction(addition, parse_binary_clause(i, end));
        Debug("pf::drat") << d << std::endl;
        d_instructions.push_back(d);
        break;
      }
      case 'd':
      {
        ++i;
        DRATInstruction d =
            DRATInstruction(deletion, parse_binary_clause(i, end));
        Debug("pf::drat") << d << std::endl;
        d_instructions.push_back(d);
        break;
      }
      default:
      {
        std::ostringstream s;
        s << "Invalid instruction in DRAT proof. Instruction bits: "
          << std::bitset<8>(*i)
          << ". Expected 'a' (01100001) or 'd' "
             "(01100100).";
        throw InvalidDRATProofException(s.str());
      }
    }
  }
  d_parsed = true;

  if (Debug.isOn("pf::drat"))
  {
    Debug("pf::drat") << "Printing out DRAT in textual format:" << std::endl;
    for (const auto& i : d_instructions)
    {
      switch (i.kind)
      {
        case DRATInstructionKind::addition:
        {
          for (const auto& l : i.clause)
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
        case DRATInstructionKind::deletion:
        {
          Debug("pf::drat") << "d ";
          for (const auto& l : i.clause)
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
        default: { throw InvalidDRATProofException("???");
        }
      }
    }
  }
};

std::ostringstream& DRATProof::getOStringStream()
{
  return d_binary_formatted_proof;
};

const std::vector<DRATInstruction>& DRATProof::getInstructions() const
{
  if (!d_parsed)
  {
    parse();
  };
  return d_instructions;
};

SatClause parse_binary_clause(std::string::const_iterator& start,
                              const std::string::const_iterator& proof_end)
{
  SatClause clause;
  for (; start != proof_end;)
  {
    if (*start == 0)
    {
      ++start;
      return clause;
    }
    else
    {
      clause.push_back(parse_binary_literal(start, proof_end));
    }
  }
  throw InvalidDRATProofException(
      "Clause in DRAT proof was not done when "
      "EOF was encountered");
}

// Advances `start`, parsing the binary representation of a literal
SatLiteral parse_binary_literal(std::string::const_iterator& start,
                                const std::string::const_iterator& proof_end)
{
  uint64_t literal_represented_as_uint = 0;
  for (int shift = 0; start != proof_end; ++start, shift += 7)
  {
    unsigned char byte = *start;
    bool continued = (byte >> 7) & 1;
    unsigned char numeric_part = byte & 0x7f;
    literal_represented_as_uint |= numeric_part << shift;
    if (!continued)
    {
      // LSB of `literal_represented_as_uint` indicates negation.
      bool negated = literal_represented_as_uint & 1;
      SatVariable var_number = literal_represented_as_uint >> 1;
      ++start;
      // It's not clear to me why we need to subtract 1 here..
      return SatLiteral(var_number - 1, negated);
    }
  }
  throw InvalidDRATProofException(
      "Literal in DRAT proof was not done when "
      "EOF was encountered");
}

}  // namespace drat
}  // namespace proof
}  // namespace CVC4
