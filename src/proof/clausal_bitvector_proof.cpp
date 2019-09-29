/*********************                                                        */
/*! \file clausal_bitvector_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitvector proof using the DRAT proof format
 **
 ** Contains DRAT-specific printing logic.
 **/

#include "cvc4_private.h"

#include <algorithm>
#include <iostream>
#include <iterator>
#include <map>

#include "options/bv_options.h"
#include "proof/clausal_bitvector_proof.h"
#include "proof/dimacs.h"
#include "proof/drat/drat_proof.h"
#include "proof/er/er_proof.h"
#include "proof/lfsc_proof_printer.h"
#include "proof/lrat/lrat_proof.h"
#include "prop/sat_solver_types.h"
#include "smt/smt_statistics_registry.h"
#include "theory/bv/theory_bv.h"

#if CVC4_USE_DRAT2ER
#include "drat2er_options.h"
#include "drat_trim_interface.h"
#endif

namespace CVC4 {

namespace proof {

ClausalBitVectorProof::ClausalBitVectorProof(theory::bv::TheoryBV* bv,
                                             TheoryProofEngine* proofEngine)
    : BitVectorProof(bv, proofEngine),
      d_clauses(),
      d_originalClauseIndices(),
      d_binaryDratProof(),
      d_coreClauseIndices(),
      d_dratTranslationStatistics(),
      d_dratOptimizationStatistics()
{
}

void ClausalBitVectorProof::attachToSatSolver(prop::SatSolver& sat_solver)
{
  sat_solver.setClausalProofLog(this);
}

void ClausalBitVectorProof::initCnfProof(prop::CnfStream* cnfStream,
                                         context::Context* cnf,
                                         prop::SatVariable trueVar,
                                         prop::SatVariable falseVar)
{
  Assert(d_cnfProof == nullptr);
  d_cnfProof.reset(new LFSCCnfProof(cnfStream, cnf, "bb"));

  // Create a clause which forces the true variable to be true, and register it
  int trueClauseId = ClauseId(ProofManager::currentPM()->nextId());
  // with the CNF proof
  d_cnfProof->registerTrueUnitClause(trueClauseId);
  // and with (this) bit-vector proof
  prop::SatClause c{prop::SatLiteral(trueVar, false)};
  registerUsedClause(trueClauseId, c);

  // The same for false.
  int falseClauseId = ClauseId(ProofManager::currentPM()->nextId());
  d_cnfProof->registerFalseUnitClause(falseClauseId);
  c[0] = prop::SatLiteral(falseVar, true);
  registerUsedClause(falseClauseId, c);
}

void ClausalBitVectorProof::registerUsedClause(ClauseId id,
                                               prop::SatClause& clause)
{
  prop::SatClause& emplaced_clause =
      d_clauses.emplace(id, clause).first->second;
  canonicalizeClause(emplaced_clause);
  d_originalClauseIndices.push_back(id);
};

void ClausalBitVectorProof::calculateAtomsInBitblastingProof()
{
  optimizeDratProof();

  // Debug dump of DRAT Proof
  if (Debug.isOn("bv::clausal"))
  {
    std::string serializedDratProof = d_binaryDratProof.str();
    Debug("bv::clausal") << "option: " << options::bvOptimizeSatProof()
                         << std::endl;
    Debug("bv::clausal") << "binary DRAT proof byte count: "
                         << serializedDratProof.size() << std::endl;
    Debug("bv::clausal") << "clause count: " << d_coreClauseIndices.size()
                         << std::endl;
  }

  // Empty any old record of which atoms were used
  d_atomsInBitblastingProof.clear();
  Assert(d_atomsInBitblastingProof.size() == 0);

  // For each used clause, ask the CNF proof which atoms are used in it
  for (const ClauseId usedIdx : d_coreClauseIndices)
  {
    d_cnfProof->collectAtoms(&d_clauses.at(usedIdx), d_atomsInBitblastingProof);
  }
}

struct SatClausePointerComparator
{
  inline bool operator()(const prop::SatClause* const& l,
                         const prop::SatClause* const& r) const
  {
    prop::SatClauseLessThan cmp;
    return cmp(*l, *r);
  }
};

void ClausalBitVectorProof::optimizeDratProof()
{
  TimerStat::CodeTimer optimizeDratProofTimer{
      d_dratOptimizationStatistics.d_totalTime};
  if (options::bvOptimizeSatProof()
          == theory::bv::BvOptimizeSatProof::BITVECTOR_OPTIMIZE_SAT_PROOF_PROOF
      || options::bvOptimizeSatProof()
             == theory::bv::BvOptimizeSatProof::
                    BITVECTOR_OPTIMIZE_SAT_PROOF_FORMULA)
  {
    Debug("bv::clausal") << "Optimizing DRAT" << std::endl;
    std::string formulaFilename("cvc4-dimacs-XXXXXX");
    std::string dratFilename("cvc4-drat-XXXXXX");
    std::string optDratFilename("cvc4-optimized-drat-XXXXXX");
    std::string optFormulaFilename("cvc4-optimized-formula-XXXXXX");

    {
      std::unique_ptr<std::fstream> formStream = openTmpFile(&formulaFilename);
      const int64_t startPos = static_cast<int64_t>(formStream->tellp());
      printDimacs(*formStream, d_clauses, d_originalClauseIndices);
      d_dratOptimizationStatistics.d_initialFormulaSize.setData(
          static_cast<int64_t>(formStream->tellp()) - startPos);
      formStream->close();
    }

    {
      std::unique_ptr<std::fstream> dratStream = openTmpFile(&dratFilename);
      const int64_t startPos = static_cast<int64_t>(dratStream->tellp());
      (*dratStream) << d_binaryDratProof.str();
      d_dratOptimizationStatistics.d_initialDratSize.setData(
          static_cast<int64_t>(dratStream->tellp()) - startPos);
      dratStream->close();
    }

    std::unique_ptr<std::fstream> optDratStream = openTmpFile(&optDratFilename);
    std::unique_ptr<std::fstream> optFormulaStream =
        openTmpFile(&optFormulaFilename);

#if CVC4_USE_DRAT2ER
    {
      TimerStat::CodeTimer runDratTimeOptimizationTimer{
          d_dratOptimizationStatistics.d_toolTime};
      int dratTrimExitCode =
          drat2er::drat_trim::OptimizeWithDratTrim(formulaFilename,
                                                   dratFilename,
                                                   optFormulaFilename,
                                                   optDratFilename,
                                                   drat2er::options::QUIET);
      AlwaysAssert(
          dratTrimExitCode == 0, "drat-trim exited with %d", dratTrimExitCode);
    }
#else
    Unimplemented(
        "Proof production when using CryptoMiniSat requires drat2er.\n"
        "Run contrib/get-drat2er, reconfigure with --drat2er, and rebuild");
#endif

    {
      d_binaryDratProof.str("");
      Assert(d_binaryDratProof.str().size() == 0);

      const int64_t startPos = static_cast<int64_t>(d_binaryDratProof.tellp());
      std::ifstream lratStream(optDratFilename);
      std::copy(std::istreambuf_iterator<char>(lratStream),
                std::istreambuf_iterator<char>(),
                std::ostreambuf_iterator<char>(d_binaryDratProof));
      d_dratOptimizationStatistics.d_optimizedDratSize.setData(
          static_cast<int64_t>(d_binaryDratProof.tellp()) - startPos);
    }

    if (options::bvOptimizeSatProof()
        == theory::bv::BvOptimizeSatProof::BITVECTOR_OPTIMIZE_SAT_PROOF_FORMULA)
    {
      std::ifstream optFormulaStream{optFormulaFilename};
      const int64_t startPos = static_cast<int64_t>(optFormulaStream.tellg());
      std::vector<prop::SatClause> core = parseDimacs(optFormulaStream);
      d_dratOptimizationStatistics.d_optimizedFormulaSize.setData(
          static_cast<int64_t>(optFormulaStream.tellg()) - startPos);

      CodeTimer clauseMatchingTimer{
          d_dratOptimizationStatistics.d_clauseMatchingTime};

      // Now we need to compute the clause indices for the UNSAT core. This is a
      // bit difficult because drat-trim may have reordered clauses, and/or
      // removed duplicate literals. We use literal sets as the canonical clause
      // form.
      //
      // TODO (aozdemir) It may be better to use a hash map instead of a tree
      // map here.
      std::map<const prop::SatClause*, ClauseId, SatClausePointerComparator>
          cannonicalClausesToIndices;
      for (const auto& kv : d_clauses)
      {
        cannonicalClausesToIndices[&kv.second] = kv.first;
      }

      d_coreClauseIndices.clear();

      for (prop::SatClause& coreClause : core)
      {
        canonicalizeClause(coreClause);
        d_coreClauseIndices.push_back(
            cannonicalClausesToIndices.at(&coreClause));
      }
      Debug("bv::clausal") << "Optimizing the DRAT proof and the formula"
                           << std::endl;
    }
    else
    {
      Debug("bv::clausal") << "Optimizing the DRAT proof but not the formula"
                           << std::endl;
      d_coreClauseIndices = d_originalClauseIndices;
    }

    optFormulaStream->close();

    Assert(d_coreClauseIndices.size() > 0);
    remove(formulaFilename.c_str());
    remove(dratFilename.c_str());
    remove(optDratFilename.c_str());
    remove(optFormulaFilename.c_str());
    Debug("bv::clausal") << "Optimized DRAT" << std::endl;
  }
  else
  {
    Debug("bv::clausal") << "Not optimizing the formula or the DRAT proof"
                         << std::endl;
    d_coreClauseIndices = d_originalClauseIndices;
  }
}

void ClausalBitVectorProof::canonicalizeClause(prop::SatClause& clause)
{
  std::sort(clause.begin(), clause.end());
  clause.erase(std::unique(clause.begin(), clause.end()), clause.end());
}

ClausalBitVectorProof::DratTranslationStatistics::DratTranslationStatistics()
    : d_totalTime("proof::bv::dratTranslation::totalTime"),
      d_toolTime("proof::bv::dratTranslation::toolTime")
{
  smtStatisticsRegistry()->registerStat(&d_totalTime);
  smtStatisticsRegistry()->registerStat(&d_toolTime);
}

ClausalBitVectorProof::DratTranslationStatistics::~DratTranslationStatistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_totalTime);
  smtStatisticsRegistry()->unregisterStat(&d_toolTime);
}

ClausalBitVectorProof::DratOptimizationStatistics::DratOptimizationStatistics()
    : d_totalTime("proof::bv::dratOptimization::totalTime"),
      d_toolTime("proof::bv::dratOptimization::toolTime"),
      d_clauseMatchingTime("proof::bv::dratOptimization::clauseMatchingTime"),
      d_initialDratSize("proof::bv::dratOptimization::initialDratSize", 0),
      d_optimizedDratSize("proof::bv::dratOptimization::optimizedDratSize", 0),
      d_initialFormulaSize("proof::bv::dratOptimization::initialFormulaSize",
                           0),
      d_optimizedFormulaSize(
          "proof::bv::dratOptimization::optimizedFormulaSize", 0)
{
  smtStatisticsRegistry()->registerStat(&d_totalTime);
  smtStatisticsRegistry()->registerStat(&d_toolTime);
  smtStatisticsRegistry()->registerStat(&d_clauseMatchingTime);
  smtStatisticsRegistry()->registerStat(&d_initialDratSize);
  smtStatisticsRegistry()->registerStat(&d_optimizedDratSize);
  smtStatisticsRegistry()->registerStat(&d_initialFormulaSize);
  smtStatisticsRegistry()->registerStat(&d_optimizedFormulaSize);
}

ClausalBitVectorProof::DratOptimizationStatistics::~DratOptimizationStatistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_totalTime);
  smtStatisticsRegistry()->unregisterStat(&d_toolTime);
  smtStatisticsRegistry()->unregisterStat(&d_clauseMatchingTime);
  smtStatisticsRegistry()->unregisterStat(&d_initialDratSize);
  smtStatisticsRegistry()->unregisterStat(&d_optimizedDratSize);
  smtStatisticsRegistry()->unregisterStat(&d_initialFormulaSize);
  smtStatisticsRegistry()->unregisterStat(&d_optimizedFormulaSize);
}

void LfscClausalBitVectorProof::printTheoryLemmaProof(std::vector<Expr>& lemma,
                                                      std::ostream& os,
                                                      std::ostream& paren,
                                                      const ProofLetMap& map)
{
  Unreachable(
      "Clausal bit-vector proofs should only be used in combination with eager "
      "bitblasting, which **does not use theory lemmas**");
}

void LfscClausalBitVectorProof::printBBDeclarationAndCnf(std::ostream& os,
                                                         std::ostream& paren,
                                                         ProofLetMap& letMap)
{
  os << "\n;; Bitblasting mappings\n";
  printBitblasting(os, paren);

  os << "\n;; BB-CNF mappings\n";
  d_cnfProof->printAtomMapping(d_atomsInBitblastingProof, os, paren, letMap);

  os << "\n;; BB-CNF proofs\n";
  for (const ClauseId id : d_coreClauseIndices)
  {
    d_cnfProof->printCnfProofForClause(id, &d_clauses.at(id), os, paren);
  }
}

void LfscDratBitVectorProof::printEmptyClauseProof(std::ostream& os,
                                                   std::ostream& paren)
{
  Assert(options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER,
         "the BV theory should only be proving bottom directly in the eager "
         "bitblasting mode");

  os << "\n;; Proof of input to SAT solver\n";
  os << "(@ proofOfSatInput ";
  paren << ")";

  LFSCProofPrinter::printSatInputProof(d_coreClauseIndices, os, "bb");

  os << "\n;; DRAT Proof Value\n";
  os << "(@ dratProof ";
  paren << ")";
  d_dratTranslationStatistics.d_totalTime.start();
  drat::DratProof pf = drat::DratProof::fromBinary(d_binaryDratProof.str());
  d_dratTranslationStatistics.d_totalTime.stop();
  pf.outputAsLfsc(os, 2);
  os << "\n";

  os << "\n;; Verification of DRAT Proof\n";
  os << "(drat_proof_of_bottom _ proofOfSatInput dratProof "
     << "\n)";
}

void LfscLratBitVectorProof::printEmptyClauseProof(std::ostream& os,
                                                   std::ostream& paren)
{
  Assert(options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER,
         "the BV theory should only be proving bottom directly in the eager "
         "bitblasting mode");

  os << "\n;; Proof of input to SAT solver\n";
  os << "(@ proofOfCMap ";
  paren << ")";
  LFSCProofPrinter::printCMapProof(d_coreClauseIndices, os, "bb");

  os << "\n;; DRAT Proof Value\n";
  os << "(@ lratProof ";
  paren << ")";
  d_dratTranslationStatistics.d_totalTime.start();
  lrat::LratProof pf =
      lrat::LratProof::fromDratProof(d_clauses,
                                     d_coreClauseIndices,
                                     d_binaryDratProof.str(),
                                     d_dratTranslationStatistics.d_toolTime);
  d_dratTranslationStatistics.d_totalTime.stop();
  pf.outputAsLfsc(os);
  os << "\n";

  os << "\n;; Verification of DRAT Proof\n";
  os << "(lrat_proof_of_bottom _ proofOfCMap lratProof "
     << "\n)";
}

void LfscErBitVectorProof::printEmptyClauseProof(std::ostream& os,
                                                 std::ostream& paren)
{
  Assert(options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER,
         "the BV theory should only be proving bottom directly in the eager "
         "bitblasting mode");

  d_dratTranslationStatistics.d_totalTime.start();
  er::ErProof pf =
      er::ErProof::fromBinaryDratProof(d_clauses,
                                       d_coreClauseIndices,
                                       d_binaryDratProof.str(),
                                       d_dratTranslationStatistics.d_toolTime);
  d_dratTranslationStatistics.d_totalTime.stop();

  pf.outputAsLfsc(os);
}

}  // namespace proof

};  // namespace CVC4
