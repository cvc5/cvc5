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
#include <iterator>
#include <set>

#include "options/bv_options.h"
#include "proof/clausal_bitvector_proof.h"
#include "proof/drat/drat_proof.h"
#include "proof/er/er_proof.h"
#include "proof/lfsc_proof_printer.h"
#include "proof/lrat/lrat_proof.h"
#include "theory/bv/theory_bv.h"

namespace CVC4 {

namespace proof {

ClausalBitVectorProof::ClausalBitVectorProof(theory::bv::TheoryBV* bv,
                                             TheoryProofEngine* proofEngine)
    : BitVectorProof(bv, proofEngine), d_usedClauses(), d_binaryDratProof()
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
  d_usedClauses.emplace_back(id, clause);
};

void ClausalBitVectorProof::calculateAtomsInBitblastingProof()
{
  // Debug dump of DRAT Proof
  if (Debug.isOn("bv::clausal"))
  {
    std::string serializedDratProof = d_binaryDratProof.str();
    Debug("bv::clausal") << "binary DRAT proof byte count: "
                         << serializedDratProof.size() << std::endl;
    Debug("bv::clausal") << "Parsing DRAT proof ... " << std::endl;
    drat::DratProof dratProof =
        drat::DratProof::fromBinary(serializedDratProof);

    Debug("bv::clausal") << "Printing DRAT proof ... " << std::endl;
    dratProof.outputAsText(Debug("bv::clausal"));
  }

  // Empty any old record of which atoms were used
  d_atomsInBitblastingProof.clear();

  // For each used clause, ask the CNF proof which atoms are used in it
  for (const auto& usedIndexAndClause : d_usedClauses)
  {
    d_cnfProof->collectAtoms(&usedIndexAndClause.second,
                             d_atomsInBitblastingProof);
  }
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
  for (const auto& idAndClause : d_usedClauses)
  {
    d_cnfProof->printCnfProofForClause(
        idAndClause.first, &idAndClause.second, os, paren);
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
  std::vector<ClauseId> usedIds;
  usedIds.reserve(d_usedClauses.size());
  for (const auto& idAnd : d_usedClauses)
  {
    usedIds.push_back(idAnd.first);
  };
  LFSCProofPrinter::printSatInputProof(usedIds, os, "bb");

  os << "\n;; DRAT Proof Value\n";
  os << "(@ dratProof ";
  paren << ")";
  drat::DratProof::fromBinary(d_binaryDratProof.str()).outputAsLfsc(os, 2);
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
  std::vector<ClauseId> usedIds;
  usedIds.reserve(d_usedClauses.size());
  for (const auto& idAnd : d_usedClauses)
  {
    usedIds.push_back(idAnd.first);
  };
  LFSCProofPrinter::printCMapProof(usedIds, os, "bb");

  os << "\n;; DRAT Proof Value\n";
  os << "(@ lratProof ";
  paren << ")";
  lrat::LratProof pf =
      lrat::LratProof::fromDratProof(d_usedClauses, d_binaryDratProof.str());
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

  er::ErProof pf =
      er::ErProof::fromBinaryDratProof(d_usedClauses, d_binaryDratProof.str());

  pf.outputAsLfsc(os);
}

}  // namespace proof

};  // namespace CVC4
