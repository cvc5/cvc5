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

// DratInstruction implementation
DratInstruction::DratInstruction(DratInstructionKind kind,
                                 prop::SatClause clause)
    : d_kind(kind), d_clause(clause)
{
  // All intialized
}

// DratProof implementation

DratProof::DratProof() : d_instructions() {}

std::vector<std::string> splitString(std::string s, std::string splitter)
{
  std::vector<std::string> lines;
  size_t pos = 0;
  std::string token;
  while ((pos = s.find(splitter)) != std::string::npos)
  {
    token = s.substr(0, pos);
    s.erase(0, pos + splitter.length());
    if (token.length() > 0)
    {
      lines.push_back(token);
    }
  }
  token = s.substr(0, pos);
  if (token.length() > 0)
  {
    lines.push_back(token);
  }
  return lines;
}

void insertSatLiteralIntoClause(prop::SatClause* clause,
                                std::string dratLiteral)
{
  int literal = stoi(dratLiteral);
  bool negated = literal < 0;
  if (literal < 0)
  {
    literal *= -1;
  }
  clause->emplace_back(prop::SatLiteral((uint64_t)literal, negated));
}

DratProof DratProof::fromPlain(const std::string& s)
{
  DratProof dratProof;
  std::string dratLineSplitter = "\n";
  std::vector<std::string> lines = splitString(s, dratLineSplitter);

  for (const std::string& line : lines)
  {
    std::string dratColumnSplitter = " ";
    std::vector<std::string> columns = splitString(line, dratColumnSplitter);
    // last line, false derivation
    if (line == lines[lines.size() - 1] && columns.size() == 1
        && columns[0] == "0")
    {
      dratProof.d_instructions.emplace_back(
          ADDITION, prop::SatClause({prop::SatLiteral(0)}));
      break;
    }
    DratInstructionKind kind = ADDITION;
    int columnsStart = 0;
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
      insertSatLiteralIntoClause(&currentClause, columns[i]);
    }
    if (currentClause.size() > 0)
    {
      dratProof.d_instructions.emplace_back(kind, currentClause);
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