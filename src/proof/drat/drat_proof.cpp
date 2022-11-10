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

#include "proof/drat/drat_proof.h"

#include <algorithm>
#include <bitset>
#include <iostream>

namespace cvc5::internal {
namespace proof {

// helper functions
namespace {

void insertSatLiteralIntoClause(prop::SatClause& clause,
                                const std::string& dratLiteral)
{
  int32_t literal = stoi(dratLiteral);
  clause.emplace_back(
      prop::SatLiteral(static_cast<uint64_t>(std::abs(literal)), literal < 0));
}

std::vector<std::string> splitString(const std::string& s, const char delim)
{
  std::stringstream ss(s);
  std::string token;
  std::vector<std::string> res;
  while (std::getline(ss, token, delim))
  {
    res.push_back(token);
  }
  return res;
}

void addFalseDerivationInstruction(std::vector<DratInstruction>& instructions)
{
  instructions.emplace_back(ADDITION, prop::SatClause({prop::SatLiteral(0)}));
}

bool addInstruction(std::vector<DratInstruction>& instructions,
                    const std::vector<std::string>& columns)
{
  DratInstructionKind kind = ADDITION;
  int32_t columnsStart = 0;
  if (columns[0] == "d")
  {
    // last but one column is the literal, last column is 0
    kind = DELETION;
    columnsStart = 1;
  }
  prop::SatClause currentClause;
  // last column is 0
  for (std::size_t i = columnsStart, size = columns.size() - 1; i < size; i++)
  {
    insertSatLiteralIntoClause(currentClause, columns[i]);
  }
  if (currentClause.size() > 0)
  {
    instructions.emplace_back(kind, currentClause);
    return true;
  }
  return false;
}

}  // namespace

// DratInstruction implementation
DratInstruction::DratInstruction(DratInstructionKind kind,
                                 const prop::SatClause& clause)
    : d_kind(kind), d_clause(clause)
{
  // All intialized
}

// DratProof implementation

DratProof::DratProof() : d_instructions() {}

DratProof DratProof::fromPlain(std::ifstream& dratEntry)
{
  DratProof dratProof;

  std::string line;
  while (std::getline(dratEntry, line))
  {
    char dratColumnSplitter = ' ';
    std::vector<std::string> columns = splitString(line, dratColumnSplitter);
    // last line, false derivation
    if (dratEntry.peek() == EOF && columns.size() == 1 && columns[0] == "0")
    {
      addFalseDerivationInstruction(dratProof.d_instructions);
      break;
    }
    if (addInstruction(dratProof.d_instructions, columns))
    {
      continue;
    }
    Unreachable() << "Invalid line in Drat proof: \"" << line << "\""
                  << std::endl;
  }
  return dratProof;
};

const std::vector<DratInstruction>& DratProof::getInstructions() const
{
  return d_instructions;
};

}  // namespace proof
}  // namespace cvc5::internal