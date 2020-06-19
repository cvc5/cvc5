/*********************                                                        */
/*! \file lfsc_proof_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Alex Ozdemir, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Prints proofs in the LFSC format
 **
 ** Prints proofs in the LFSC format.
 **/

#include "proof/lfsc_proof_printer.h"

#include <algorithm>
#include <iostream>
#include <iterator>

#include "prop/bvminisat/core/Solver.h"
#include "prop/minisat/core/Solver.h"

namespace CVC4 {
namespace proof {

template <class Solver>
std::string LFSCProofPrinter::clauseName(TSatProof<Solver>* satProof,
                                         ClauseId id)
{
  std::ostringstream os;
  if (satProof->isInputClause(id))
  {
    os << ProofManager::getInputClauseName(id, satProof->getName());
  }
  else if (satProof->isLemmaClause(id))
  {
    os << ProofManager::getLemmaClauseName(id, satProof->getName());
  }
  else
  {
    os << ProofManager::getLearntClauseName(id, satProof->getName());
  }
  return os.str();
}

template <class Solver>
void LFSCProofPrinter::printResolution(TSatProof<Solver>* satProof,
                                       ClauseId id,
                                       std::ostream& out,
                                       std::ostream& paren)
{
  out << "(satlem_simplify _ _ _";
  paren << ")";

  const ResChain<Solver>& res = satProof->getResolutionChain(id);
  const typename ResChain<Solver>::ResSteps& steps = res.getSteps();

  for (int i = steps.size() - 1; i >= 0; i--)
  {
    out << " (";
    out << (steps[i].sign ? "R" : "Q") << " _ _";
  }

  ClauseId start_id = res.getStart();
  out << " " << clauseName(satProof, start_id);

  for (unsigned i = 0; i < steps.size(); i++)
  {
    prop::SatVariable v =
        prop::MinisatSatSolver::toSatVariable(var(steps[i].lit));
    out << " " << clauseName(satProof, steps[i].id) << " "
        << ProofManager::getVarName(v, satProof->getName()) << ")";
  }

  if (id == satProof->getEmptyClauseId())
  {
    out << " (\\ empty empty)";
    return;
  }

  out << " (\\ " << clauseName(satProof, id) << "\n";  // bind to lemma name
  paren << ")";
}

template <class Solver>
void LFSCProofPrinter::printAssumptionsResolution(TSatProof<Solver>* satProof,
                                                  ClauseId id,
                                                  std::ostream& out,
                                                  std::ostream& paren)
{
  Assert(satProof->isAssumptionConflict(id));
  // print the resolution proving the assumption conflict
  printResolution(satProof, id, out, paren);
  // resolve out assumptions to prove empty clause
  out << "(satlem_simplify _ _ _ ";
  const std::vector<typename Solver::TLit>& confl =
      *(satProof->getAssumptionConflicts().at(id));

  Assert(confl.size());

  for (unsigned i = 0; i < confl.size(); ++i)
  {
    prop::SatLiteral lit = toSatLiteral<Solver>(confl[i]);
    out << "(";
    out << (lit.isNegated() ? "Q" : "R") << " _ _ ";
  }

  out << clauseName(satProof, id) << " ";
  for (int i = confl.size() - 1; i >= 0; --i)
  {
    prop::SatLiteral lit = toSatLiteral<Solver>(confl[i]);
    prop::SatVariable v = lit.getSatVariable();
    out << "unit" << v << " ";
    out << ProofManager::getVarName(v, satProof->getName()) << ")";
  }
  out << "(\\ e e)\n";
  paren << ")";
}

template <class Solver>
void LFSCProofPrinter::printResolutions(TSatProof<Solver>* satProof,
                                        std::ostream& out,
                                        std::ostream& paren)
{
  Debug("bv-proof") << "; print resolutions" << std::endl;
  std::set<ClauseId>::iterator it = satProof->getSeenLearnt().begin();
  for (; it != satProof->getSeenLearnt().end(); ++it)
  {
    if (*it != satProof->getEmptyClauseId())
    {
      Debug("bv-proof") << "; print resolution for " << *it << std::endl;
      printResolution(satProof, *it, out, paren);
    }
  }
  Debug("bv-proof") << "; done print resolutions" << std::endl;
}

template <class Solver>
void LFSCProofPrinter::printResolutionEmptyClause(TSatProof<Solver>* satProof,
                                                  std::ostream& out,
                                                  std::ostream& paren)
{
  printResolution(satProof, satProof->getEmptyClauseId(), out, paren);
}

void LFSCProofPrinter::printSatInputProof(const std::vector<ClauseId>& clauses,
                                      std::ostream& out,
                                      const std::string& namingPrefix)
{
  for (auto i = clauses.begin(), end = clauses.end(); i != end; ++i)
  {
    out << "\n    (cnfc_proof _ _ _ "
        << ProofManager::getInputClauseName(*i, namingPrefix) << " ";
  }
  out << "cnfn_proof";
  std::fill_n(std::ostream_iterator<char>(out), clauses.size(), ')');
}

void LFSCProofPrinter::printCMapProof(const std::vector<ClauseId>& clauses,
                                      std::ostream& out,
                                      const std::string& namingPrefix)
{
  for (size_t i = 0, n = clauses.size(); i < n; ++i)
  {
    out << "\n    (CMapc_proof " << (i + 1) << " _ _ _ "
        << ProofManager::getInputClauseName(clauses[i], namingPrefix) << " ";
  }
  out << "CMapn_proof";
  std::fill_n(std::ostream_iterator<char>(out), clauses.size(), ')');
}

void LFSCProofPrinter::printSatClause(const prop::SatClause& clause,
                                      std::ostream& out,
                                      const std::string& namingPrefix)
{
  for (auto i = clause.cbegin(); i != clause.cend(); ++i)
  {
    out << "(clc " << (i->isNegated() ? "(neg " : "(pos ")
        << ProofManager::getVarName(i->getSatVariable(), namingPrefix) << ") ";
  }
  out << "cln";
  std::fill_n(std::ostream_iterator<char>(out), clause.size(), ')');
}

// Template specializations
template void LFSCProofPrinter::printAssumptionsResolution(
    TSatProof<CVC4::Minisat::Solver>* satProof,
    ClauseId id,
    std::ostream& out,
    std::ostream& paren);
template void LFSCProofPrinter::printResolutions(
    TSatProof<CVC4::Minisat::Solver>* satProof,
    std::ostream& out,
    std::ostream& paren);
template void LFSCProofPrinter::printResolutionEmptyClause(
    TSatProof<CVC4::Minisat::Solver>* satProof,
    std::ostream& out,
    std::ostream& paren);

template void LFSCProofPrinter::printAssumptionsResolution(
    TSatProof<CVC4::BVMinisat::Solver>* satProof,
    ClauseId id,
    std::ostream& out,
    std::ostream& paren);
template void LFSCProofPrinter::printResolutions(
    TSatProof<CVC4::BVMinisat::Solver>* satProof,
    std::ostream& out,
    std::ostream& paren);
template void LFSCProofPrinter::printResolutionEmptyClause(
    TSatProof<CVC4::BVMinisat::Solver>* satProof,
    std::ostream& out,
    std::ostream& paren);
}  // namespace proof
}  // namespace CVC4
