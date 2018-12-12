/*********************                                                        */
/*! \file lrat_proof.cpp
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

#include "proof/lrat/lrat_proof.h"

#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <unordered_map>

#include "base/cvc4_assert.h"
#include "base/output.h"

namespace CVC4 {
namespace proof {
namespace lrat {

using prop::SatClause;
using prop::SatLiteral;
using prop::SatVariable;

namespace {
// Prints the literal as a (+) or (-) int
// Not operator<< b/c that represents negation as ~
inline std::ostream& textOut(std::ostream& o, const SatLiteral& l)
{
  if (l.isNegated())
  {
    o << "-";
  }
  return o << l.getSatVariable();
}

// Prints the clause as a space-separated list of ints
// Not operator<< b/c that represents negation as ~
inline std::ostream& textOut(std::ostream& o, const SatClause& c)
{
  for (const auto l : c)
  {
    textOut(o, l) << " ";
  }
  return o << "0";
}

// Prints the trace as a space-separated list of (+) ints with a space at the
// end.
inline std::ostream& operator<<(std::ostream& o, const LratUPTrace& trace)
{
  for (const auto& i : trace)
  {
    o << i << " ";
  }
  return o;
}

// Prints the LRAT addition line in textual format
inline std::ostream& operator<<(std::ostream& o, const LratAdditionData& add)
{
  o << add.d_idxOfClause << " ";
  textOut(o, add.d_clause) << " ";
  o << add.d_atTrace;  // Inludes a space at the end.
  for (const auto& rat : add.d_resolvants)
  {
    o << "-" << rat.first << " ";
    o << rat.second;  // Includes a space at the end.
  }
  o << "0\n";
  return o;
}

// Prints the LRAT addition line in textual format
inline std::ostream& operator<<(std::ostream& o, const LratDeletionData& del)
{
  o << del.d_idxOfClause << " d ";
  for (const auto& idx : del.d_clauses)
  {
    o << idx << " ";
  }
  return o << "0\n";
}

// Prints the LRAT line in textual format
inline std::ostream& operator<<(std::ostream& o, const LratInstruction& i)
{
  switch (i.d_kind)
  {
    case LRAT_ADDITION: return o << i.d_data.d_addition;
    case LRAT_DELETION: return o << i.d_data.d_deletion;
    default: return o;
  }
}

}

LratInstruction::LratInstruction(LratInstruction&& instr) : d_kind(instr.d_kind)
{
  switch (d_kind)
  {
    case LRAT_ADDITION:
    {
      d_data.d_addition = instr.d_data.d_addition;
      break;
    }
    case LRAT_DELETION:
    {
      d_data.d_deletion = instr.d_data.d_deletion;
      break;
    }
  }
}

LratInstruction::LratInstruction(LratInstruction& instr) : d_kind(instr.d_kind)
{
  switch (d_kind)
  {
    case LRAT_ADDITION:
    {
      d_data.d_addition = instr.d_data.d_addition;
      break;
    }
    case LRAT_DELETION:
    {
      d_data.d_deletion = instr.d_data.d_deletion;
      break;
    }
  }
}

LratInstruction::LratInstruction(LratAdditionData&& addition)
    : d_kind(LRAT_ADDITION)
{
  d_data.d_addition = std::move(addition);
}

LratInstruction::LratInstruction(LratDeletionData&& deletion)
    : d_kind(LRAT_DELETION)
{
  d_data.d_deletion = std::move(deletion);
}

LratInstruction::~LratInstruction()
{
  switch (d_kind)
  {
    case LRAT_ADDITION:
    {
      d_data.d_addition.~LratAdditionData();
      break;
    }
    case LRAT_DELETION:
    {
      d_data.d_deletion.~LratDeletionData();
      break;
    }
  }
}

LratProof LratProof::fromDratProof(
    const std::unordered_map<ClauseId, SatClause*>& usedClauses,
    const std::vector<ClauseId>& clauseOrder,
    const std::string& dratBinary)
{
  std::ostringstream cmd;
  char formulaFilename[] = "/tmp/cvc4-dimacs-XXXXXX";
  char dratFilename[] = "/tmp/cvc4-drat-XXXXXX";
  char lratFilename[] = "/tmp/cvc4-lrat-XXXXXX";
  int r;
  r = mkstemp(formulaFilename);
  AlwaysAssert(r > 0);
  close(r);
  r = mkstemp(dratFilename);
  AlwaysAssert(r > 0);
  close(r);
  r = mkstemp(lratFilename);
  AlwaysAssert(r > 0);
  close(r);
  std::ofstream formStream(formulaFilename);
  size_t maxVar = 0;
  for (auto& c : usedClauses)
  {
    for (auto l : *(c.second))
    {
      if (l.getSatVariable() + 1 > maxVar)
      {
        maxVar = l.getSatVariable() + 1;
      }
    }
  }
  formStream << "p cnf " << maxVar << " " << usedClauses.size() << '\n';
  for (auto ci : clauseOrder)
  {
    auto iterator = usedClauses.find(ci);
    Assert(iterator != usedClauses.end());
    for (auto l : *(iterator->second))
    {
      if (l.isNegated())
      {
        formStream << '-';
      }
      formStream << l.getSatVariable() + 1 << " ";
    }
    formStream << "0\n";
  }
  formStream.close();

  std::ofstream dratStream(dratFilename);
  dratStream << dratBinary;
  dratStream.close();

  // TODO(aozdemir) Add invocation of DRAT trim, once I get CMake to bundle it
  // into CVC4 correctly.
  Unimplemented();

  std::ifstream lratStream(lratFilename);
  LratProof lrat(lratStream);
  remove(formulaFilename);
  remove(dratFilename);
  remove(lratFilename);
  return lrat;
}

std::istream& operator>>(std::istream& in, SatLiteral& l)
{
  int64_t i;
  in >> i;
  l = SatLiteral(labs(i), i < 0);
  return in;
}

// This parser is implemented to parse the textual RAT format found in
// "Efficient Certified RAT Verification", by Cruz-Filipe et. All
LratProof::LratProof(std::istream& textualProof)
{
  for (size_t line = 0;; ++line)
  {
    // Read beginning of instruction. EOF indicates that we're done.
    size_t clauseIdx;
    textualProof >> clauseIdx;
    if (textualProof.eof())
    {
      return;
    }

    // Read the first word of the instruction. A 'd' indicates deletion.
    std::string first;
    textualProof >> first;
    Trace("pf::lrat") << "First word: " << first << std::endl;
    Assert(textualProof.good());
    if (first == "d")
    {
      std::vector<ClauseIdx> clauses;
      while (true)
      {
        ClauseIdx di;
        textualProof >> di;
        Assert(textualProof.good());
        if (di == 0)
        {
          break;
        }
        clauses.push_back(di);
      }
      std::sort(clauses.begin(), clauses.end());
      d_instructions.emplace_back(
          LratDeletionData(clauseIdx, std::move(clauses)));
    }
    else
    {
      // We need to reparse the first word as a literal to read the clause
      // we're parsing. It ends with a 0;
      std::istringstream firstS(first);
      SatLiteral lit;
      firstS >> lit;
      Trace("pf::lrat") << "First lit: " << lit << std::endl;
      Assert(!firstS.fail(), "Couldn't parse first literal from addition line");

      SatClause clause;
      for (; lit != 0; textualProof >> lit)
      {
        Assert(textualProof.good());
        clause.emplace_back(lit.getSatVariable() - 1, lit.isNegated());
      }

      // Now we read the AT UP trace. It ends at the first non-(+) #
      std::vector<ClauseIdx> atTrace;
      int64_t i;
      textualProof >> i;
      for (; i > 0; textualProof >> i)
      {
        Assert(textualProof.good());
        atTrace.push_back(i);
      }

      // For each RAT hint... (each RAT hint starts with a (-)).
      std::vector<std::pair<ClauseIdx, LratUPTrace>> resolvants;
      for (; i<0; textualProof>> i)
      {
        Assert(textualProof.good());
        // Create an entry in the RAT hint list
        resolvants.emplace_back(i, std::vector<ClauseIdx>());

        // Record the UP trace. It ends with a (-) or 0.
        textualProof >> i;
        for (; i > 0; textualProof >> i)
        {
          resolvants.back().second.push_back(i);
        }
      }
      // Pairs compare based on the first element, so this sorts by the
      // resolution target index
      std::sort(resolvants.begin(), resolvants.end());
      d_instructions.emplace_back(LratAdditionData(clauseIdx,
                                                   std::move(clause),
                                                   std::move(atTrace),
                                                   std::move(resolvants)));
    }
  }
}

inline std::ostream& operator<<(std::ostream& o, const LratProof& p)
{
  for (const auto& instr : p.getInstructions())
  {
    o << instr;
  }
  return o;
}

}  // namespace lrat
}  // namespace proof
}  // namespace CVC4
