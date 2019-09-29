/*********************                                                        */
/*! \file er_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief ER Proof Format
 **
 ** Declares C++ types that represent an ER/TRACECHECK proof.
 ** Defines serialization for these types.
 **
 ** You can find details about the way ER is encoded in the TRACECHECK
 ** format at these locations:
 **    https://github.com/benjaminkiesl/drat2er
 **    http://www.cs.utexas.edu/users/marijn/publications/ijcar18.pdf
 **/

#include "proof/er/er_proof.h"

#include <unistd.h>
#include <algorithm>
#include <fstream>
#include <iostream>
#include <iterator>
#include <unordered_set>

#include "base/cvc4_assert.h"
#include "base/map_util.h"
#include "proof/dimacs.h"
#include "proof/lfsc_proof_printer.h"
#include "proof/proof_manager.h"

#if CVC4_USE_DRAT2ER
#include "drat2er.h"
#include "drat2er_options.h"
#endif

namespace CVC4 {
namespace proof {
namespace er {

TraceCheckProof TraceCheckProof::fromText(std::istream& in)
{
  TraceCheckProof pf;
  TraceCheckIdx idx = 0;
  int64_t token = 0;

  // For each line of the proof, start with the idx
  // If there is no idx, then you're done!
  in >> idx;
  for (; !in.eof(); in >> idx)
  {
    Assert(in.good());

    // Then parse the clause (it's 0-terminated)
    std::vector<prop::SatLiteral> clause;
    in >> token;
    for (; token != 0; in >> token)
    {
      clause.emplace_back(std::abs(token) - 1, token < 0);
    }

    // Then parse the chain of literals (it's also 0-terminated)
    std::vector<TraceCheckIdx> chain;
    in >> token;
    for (; token != 0; in >> token)
    {
      Assert(token > 0);
      chain.push_back(token);
    }

    // Add the line to the proof
    pf.d_lines.emplace_back(idx, std::move(clause), std::move(chain));
  }
  return pf;
}

ErProof ErProof::fromBinaryDratProof(
    const std::unordered_map<ClauseId, prop::SatClause>& clauses,
    const std::vector<ClauseId>& usedIds,
    const std::string& dratBinary,
    TimerStat& toolTimer)
{
  std::string formulaFilename("cvc4-dimacs-XXXXXX");
  std::string dratFilename("cvc4-drat-XXXXXX");
  std::string tracecheckFilename("cvc4-tracecheck-er-XXXXXX");

  // Write the formula
  std::unique_ptr<std::fstream> formStream = openTmpFile(&formulaFilename);
  printDimacs(*formStream, clauses, usedIds);
  formStream->close();

  // Write the (binary) DRAT proof
  std::unique_ptr<std::fstream> dratStream = openTmpFile(&dratFilename);
  (*dratStream) << dratBinary;
  dratStream->close();

  std::unique_ptr<std::fstream> tracecheckStream =
      openTmpFile(&tracecheckFilename);

  // Invoke drat2er
  {
    CodeTimer blockTimer{toolTimer};
#if CVC4_USE_DRAT2ER
    drat2er::TransformDRATToExtendedResolution(formulaFilename,
                                               dratFilename,
                                               tracecheckFilename,
                                               false,
                                               drat2er::options::QUIET,
                                               false);
#else
    Unimplemented(
        "ER proof production requires drat2er.\n"
        "Run contrib/get-drat2er, reconfigure with --drat2er, and rebuild");
#endif
  }

  // Parse the resulting TRACECHECK proof into an ER proof.
  TraceCheckProof pf = TraceCheckProof::fromText(*tracecheckStream);
  ErProof proof(clauses, usedIds, std::move(pf));
  tracecheckStream->close();

  remove(formulaFilename.c_str());
  remove(dratFilename.c_str());
  remove(tracecheckFilename.c_str());

  return proof;
}

ErProof::ErProof(const std::unordered_map<ClauseId, prop::SatClause>& clauses,
                 const std::vector<ClauseId>& usedIds,
                 TraceCheckProof&& tracecheck)
    : d_inputClauseIds(), d_definitions(), d_tracecheck(tracecheck)
{
  // Step zero, save input clause Ids for future printing
  d_inputClauseIds = usedIds;

  // Make a list of (idx, clause pairs), the used ones.
  std::vector<std::pair<ClauseId, prop::SatClause>> usedClauses;
  std::transform(
      usedIds.begin(),
      usedIds.end(),
      std::back_inserter(usedClauses),
      [&](const ClauseId& i) { return make_pair(i, clauses.at(i)); });

  // Step one, verify the formula starts the proof
  if (Configuration::isAssertionBuild())
  {
    for (size_t i = 0, n = usedClauses.size(); i < n; ++i)
    {
      Assert(d_tracecheck.d_lines[i].d_idx = i + 1);
      Assert(d_tracecheck.d_lines[i].d_chain.size() == 0);
      std::unordered_set<prop::SatLiteral, prop::SatLiteralHashFunction>
          traceCheckClause{d_tracecheck.d_lines[i].d_clause.begin(),
                           d_tracecheck.d_lines[i].d_clause.end()};
      std::unordered_set<prop::SatLiteral, prop::SatLiteralHashFunction>
          originalClause{usedClauses[i].second.begin(),
                         usedClauses[i].second.end()};
      Assert(traceCheckClause == originalClause);
    }
  }

  // Step two, identify definitions. They correspond to lines that follow the
  // input lines, are in bounds, and have no justifying chain.
  for (size_t i = usedClauses.size(), n = d_tracecheck.d_lines.size();
       i < n && d_tracecheck.d_lines[i].d_chain.size() == 0;)
  {
    prop::SatClause c = d_tracecheck.d_lines[i].d_clause;
    Assert(c.size() > 0);
    Assert(!c[0].isNegated());

    // Get the new variable of the definition -- the first variable of the
    // first clause
    prop::SatVariable newVar = c[0].getSatVariable();

    // The rest of the literals in the clause of the 'other literals' of the def
    std::vector<prop::SatLiteral> otherLiterals{++c.begin(), c.end()};

    size_t nLinesForThisDef = 2 + otherLiterals.size();
    // Look at the negation of the second literal in the second clause to get
    // the old literal
    AlwaysAssert(d_tracecheck.d_lines.size() > i + 1,
                 "Malformed definition in TRACECHECK proof from drat2er");
    d_definitions.emplace_back(newVar,
                               ~d_tracecheck.d_lines[i + 1].d_clause[1],
                               std::move(otherLiterals));

    // Advance over the lines for this definition
    i += nLinesForThisDef;
  }
}

void ErProof::outputAsLfsc(std::ostream& os) const
{
  // How many parens to close?
  size_t parenCount = 0;
  std::unordered_set<prop::SatVariable> newVariables;

  // Print Definitions
  for (const ErDefinition& def : d_definitions)
  {
    os << "\n    (decl_rat_elimination_def ("
       << (def.d_oldLiteral.isNegated() ? "neg " : "pos ")
       << ProofManager::getVarName(def.d_oldLiteral.getSatVariable(), "bb")
       << ") ";
    LFSCProofPrinter::printSatClause(def.d_otherLiterals, os, "bb");
    os << " (\\ er.v" << def.d_newVariable << " (\\ er.def"
       << def.d_newVariable;
    newVariables.insert(def.d_newVariable);
  }
  parenCount += 3 * d_definitions.size();

  // Clausify Definitions
  TraceCheckIdx firstDefClause = d_inputClauseIds.size() + 1;
  for (const ErDefinition& def : d_definitions)
  {
    os << "\n    (clausify_rat_elimination_def _ _ _ "
       << "er.def " << def.d_newVariable << " _ _ (\\ er.c" << firstDefClause
       << " (\\ er.c" << (firstDefClause + 1) << " (\\ er.cnf"
       << def.d_newVariable;

    firstDefClause += 2 + def.d_otherLiterals.size();
  }
  parenCount += 4 * d_definitions.size();

  // Unroll proofs of CNFs to proofs of clauses
  firstDefClause = d_inputClauseIds.size() + 1;
  for (const ErDefinition& def : d_definitions)
  {
    for (size_t i = 0, n = def.d_otherLiterals.size(); i < n; ++i)
    {
      os << "\n    (cnfc_unroll _ _ ";
      os << "er.cnf" << def.d_newVariable;
      if (i != 0)
      {
        os << ".u" << i;
      }
      os << " (\\ er.c" << (firstDefClause + 2 + i);
      os << " (\\ er.cnf" << def.d_newVariable << ".u" << (i + 1);
    }
    parenCount += 3 * def.d_otherLiterals.size();

    firstDefClause += 2 + def.d_otherLiterals.size();
  }

  // NB: At this point `firstDefClause` points to the first clause resulting
  // from a resolution chain

  // Now, elaborate each resolution chain
  for (size_t cId = firstDefClause, nLines = d_tracecheck.d_lines.size();
       cId <= nLines;
       ++cId)
  {
    const std::vector<TraceCheckIdx>& chain =
        d_tracecheck.d_lines[cId - 1].d_chain;
    const std::vector<prop::SatLiteral> pivots = computePivotsForChain(chain);
    Assert(chain.size() > 0);
    Assert(chain.size() == pivots.size() + 1);

    os << "\n    (satlem_simplify _ _ _ ";
    parenCount += 1;

    // Print resolution openings (reverse order)
    for (int64_t i = pivots.size() - 1; i >= 0; --i)
    {
      prop::SatLiteral pivot = pivots[i];
      os << "(" << (pivot.isNegated() ? 'Q' : 'R') << " _ _ ";
    }

    // Print resolution start
    writeIdForClauseProof(os, chain[0]);
    os << " ";

    // Print resolution closings (forward order)
    for (size_t i = 0, n = pivots.size(); i < n; ++i)
    {
      prop::SatVariable pivotVar = pivots[i].getSatVariable();
      TraceCheckIdx clauseId = chain[i + 1];
      writeIdForClauseProof(os, clauseId);
      os << " ";
      if (ContainsKey(newVariables, pivotVar))
      {
        // This is a defined variable
        os << "er.v" << pivotVar;
      }
      else
      {
        os << ProofManager::getVarName(pivotVar, "bb");
      }
      os << ") ";
    }
    os << "(\\ er.c" << cId;
    parenCount += 1;
  }

  // Write proof of bottom
  Assert(d_tracecheck.d_lines.back().d_clause.size() == 0,
         "The TRACECHECK proof from drat2er did not prove bottom.");
  os << "\n      er.c" << d_tracecheck.d_lines.back().d_idx
     << " ; (holds cln)\n";

  // Finally, close the parentheses!
  std::fill_n(std::ostream_iterator<char>(os), parenCount, ')');
}

namespace {
/**
 * Resolves two clauses
 *
 * @param dest one of the inputs, and the output too. **This is an input and
 *             output**
 * @param src the other input
 *
 * @return the unique literal that was resolved on, with the polarization that
 *         it originally had in `dest`.
 *
 * For example, if dest = (1 3 -4 5) and src = (1 -3 5), then 3 is returned and
 * after the call dest = (1 -4 5).
 */
prop::SatLiteral resolveModify(
    std::unordered_set<prop::SatLiteral, prop::SatLiteralHashFunction>& dest,
    const prop::SatClause& src)
{
  CVC4_UNUSED bool foundPivot = false;
  prop::SatLiteral pivot(0, false);

  for (prop::SatLiteral lit : src)
  {
    auto negationLocation = dest.find(~lit);
    if (negationLocation != dest.end())
    {
#ifdef CVC4_ASSERTIONS
      Assert(!foundPivot);
      foundPivot = true;
#endif
      dest.erase(negationLocation);
      pivot = ~lit;
    }
    dest.insert(lit);
  }

  Assert(foundPivot);
  return pivot;
}
}  // namespace

std::vector<prop::SatLiteral> ErProof::computePivotsForChain(
    const std::vector<TraceCheckIdx>& chain) const
{
  std::vector<prop::SatLiteral> pivots;

  const prop::SatClause& first = d_tracecheck.d_lines[chain[0] - 1].d_clause;
  std::unordered_set<prop::SatLiteral, prop::SatLiteralHashFunction>
      runningClause{first.begin(), first.end()};

  for (auto idx = ++chain.cbegin(), end = chain.cend(); idx != end; ++idx)
  {
    pivots.push_back(
        resolveModify(runningClause, d_tracecheck.d_lines[*idx - 1].d_clause));
  }
  return pivots;
}

void ErProof::writeIdForClauseProof(std::ostream& o, TraceCheckIdx i) const
{
  if (i <= d_inputClauseIds.size())
  {
    // This clause is an input clause! Ask the ProofManager for its name
    o << ProofManager::getInputClauseName(d_inputClauseIds[i - 1], "bb");
  }
  else
  {
    // This clause was introduced by a definition or resolution chain
    o << "er.c" << i;
  }
}

}  // namespace er
}  // namespace proof
}  // namespace CVC4
