/*********************                                                        */
/*! \file lrat_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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
#include <memory>
#include <sstream>
#include <unordered_map>

#include "base/cvc4_assert.h"
#include "base/output.h"
#include "proof/dimacs.h"
#include "proof/lfsc_proof_printer.h"
#include "util/utility.h"

#if CVC4_USE_DRAT2ER
#include "drat2er_options.h"
#include "drat_trim_interface.h"
#endif

namespace CVC4 {
namespace proof {
namespace lrat {

using prop::SatClause;
using prop::SatLiteral;
using prop::SatVariable;

namespace {

// Prints the trace as a space-separated list of (+) ints with a space at the
// end.
std::ostream& operator<<(std::ostream& o, const LratUPTrace& trace)
{
  for (const auto& i : trace)
  {
    o << i << " ";
  }
  return o;
}

/**
 * Print a list of clause indices to go to while doing UP.
 *
 * i.e. a value of type Trace
 *
 * @param o where to print to
 * @param trace the trace (list of clauses) to print
 */
void printTrace(std::ostream& o, const LratUPTrace& trace)
{
  for (ClauseIdx idx : trace)
  {
    o << "(Tracec " << idx << " ";
  }
  o << "Tracen";
  std::fill_n(std::ostream_iterator<char>(o), trace.size(), ')');
}

/**
 * Print the RAT hints for a clause addition.
 *
 * i.e. prints an LFSC value of type RATHints
 *
 * @param o where to print to
 * @param hints the RAT hints to print
 */
void printHints(std::ostream& o,
                const std::vector<std::pair<ClauseIdx, LratUPTrace>>& hints)
{
  for (auto& hint : hints)
  {
    o << "\n    (RATHintsc " << hint.first << " ";
    printTrace(o, hint.second);
    o << " ";
  }
  o << "RATHintsn";
  std::fill_n(std::ostream_iterator<char>(o), hints.size(), ')');
}

/**
 * Print an index list
 *
 * i.e. prints an LFSC value of type CIList
 *
 * @param o where to print to
 * @param indices the list of indices to print
 */
void printIndices(std::ostream& o, const std::vector<ClauseIdx>& indices)
{
  Assert(indices.size() > 0);
  // Verify that the indices are sorted!
  for (size_t i = 0, n = indices.size() - 1; i < n; ++i)
  {
    Assert(indices[i] < indices[i + 1]);
  }

  for (ClauseIdx idx : indices)
  {
    o << "(CIListc " << idx << " ";
  }
  o << "CIListn";
  std::fill_n(std::ostream_iterator<char>(o), indices.size(), ')');
}

}  // namespace

// Prints the LRAT addition line in textual format

LratProof LratProof::fromDratProof(
    const std::unordered_map<ClauseId, prop::SatClause>& clauses,
    const std::vector<ClauseId> usedIds,
    const std::string& dratBinary,
    TimerStat& toolTimer)
{
  std::ostringstream cmd;
  std::string formulaFilename("cvc4-dimacs-XXXXXX");
  std::string dratFilename("cvc4-drat-XXXXXX");
  std::string lratFilename("cvc4-lrat-XXXXXX");

  std::fstream formStream = openTmpFile(&formulaFilename);
  printDimacs(formStream, clauses, usedIds);
  formStream.close();

  std::fstream dratStream = openTmpFile(&dratFilename);
  dratStream << dratBinary;
  dratStream.close();

  std::fstream lratStream = openTmpFile(&lratFilename);

  {
    CodeTimer blockTimer{toolTimer};
#if CVC4_USE_DRAT2ER
    drat2er::drat_trim::CheckAndConvertToLRAT(
        formulaFilename, dratFilename, lratFilename, drat2er::options::QUIET);
#else
    Unimplemented(
        "LRAT proof production requires drat2er.\n"
        "Run contrib/get-drat2er, reconfigure with --drat2er, and rebuild");
#endif
  }

  LratProof lrat(lratStream);
  remove(formulaFilename.c_str());
  remove(dratFilename.c_str());
  remove(lratFilename.c_str());
  return lrat;
}

std::istream& operator>>(std::istream& in, SatLiteral& l)
{
  int64_t i;
  in >> i;
  l = SatLiteral(std::abs(i), i < 0);
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
      if (clauses.size() > 0)
      {
        std::sort(clauses.begin(), clauses.end());
        std::unique_ptr<LratInstruction> instr(
            new LratDeletion(clauseIdx, std::move(clauses)));
        d_instructions.push_back(std::move(instr));
      }
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
        resolvants.emplace_back(-i, std::vector<ClauseIdx>());

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
      std::unique_ptr<LratInstruction> instr(
          new LratAddition(clauseIdx,
                           std::move(clause),
                           std::move(atTrace),
                           std::move(resolvants)));
      d_instructions.push_back(std::move(instr));
    }
  }
}

void LratProof::outputAsLfsc(std::ostream& o) const
{
  std::ostringstream closeParen;
  for (const auto& i : d_instructions)
  {
    i->outputAsLfsc(o, closeParen);
  }
  o << "LRATProofn";
  o << closeParen.str();
}

void LratAddition::outputAsText(std::ostream& o) const
{
  o << d_idxOfClause << " ";
  textOut(o, d_clause) << " ";
  o << d_atTrace;  // Inludes a space at the end.
  for (const auto& rat : d_resolvants)
  {
    o << "-" << rat.first << " ";
    o << rat.second;  // Includes a space at the end.
  }
  o << "0\n";
}

void LratAddition::outputAsLfsc(std::ostream& o, std::ostream& closeParen) const
{
  o << "\n    (LRATProofa " << d_idxOfClause << " ";
  closeParen << ")";
  LFSCProofPrinter::printSatClause(d_clause, o, "bb");
  o << " ";
  printTrace(o, d_atTrace);
  o << " ";
  printHints(o, d_resolvants);
  o << " ";
}

void LratDeletion::outputAsText(std::ostream& o) const
{
  o << d_idxOfClause << " d ";
  for (const auto& idx : d_clauses)
  {
    o << idx << " ";
  }
  o << "0\n";
}

void LratDeletion::outputAsLfsc(std::ostream& o, std::ostream& closeParen) const
{
  o << "\n    (LRATProofd ";
  closeParen << ")";
  printIndices(o, d_clauses);
  o << " ";
}

std::ostream& operator<<(std::ostream& o, const LratProof& p)
{
  for (const auto& instr : p.getInstructions())
  {
    o << *instr;
  }
  return o;
}

std::ostream& operator<<(std::ostream& o, const LratInstruction& i)
{
  i.outputAsText(o);
  return o;
}

}  // namespace lrat
}  // namespace proof
}  // namespace CVC4
