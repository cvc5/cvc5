/*********************                                                        */
/*! \file clausal_bitvector_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
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
#include "proof/lfsc_proof_printer.h"
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
  // and with (this) bitvector proof
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
  d_usedClauses.push_back(std::make_pair(
      id, std::unique_ptr<prop::SatClause>(new prop::SatClause(clause))));
};

LFSCClausalBitVectorProof::LFSCClausalBitVectorProof(
    theory::bv::TheoryBV* bv, TheoryProofEngine* proofEngine)
    : ClausalBitVectorProof(bv, proofEngine)
{
  // That's all!
}

std::string LFSCClausalBitVectorProof::printLRATProotLet(std::ostream& os,
                                                         std::ostream& paren)
{
  Unimplemented();
}

void LFSCClausalBitVectorProof::printTheoryLemmaProof(std::vector<Expr>& lemma,
                                                      std::ostream& os,
                                                      std::ostream& paren,
                                                      const ProofLetMap& map)
{
  Unreachable(
      "Clausal bitvector proofs should only be used in combination with eager "
      "bitblasting, which **does not use theory lemmas**");
}

void LFSCClausalBitVectorProof::printBBDeclarationAndCnf(std::ostream& os,
                                                         std::ostream& paren,
                                                         ProofLetMap& letMap)
{
  Unimplemented();
}

void LFSCClausalBitVectorProof::printEmptyClauseProof(std::ostream& os,
                                                      std::ostream& paren)
{
  Assert(options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER,
         "the BV theory should only be proving bottom directly in the eager "
         "bitblasting mode");

  Unimplemented();
}

void ClausalBitVectorProof::calculateAtomsInBitblastingProof()
{
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
  Unimplemented();
}

}  // namespace proof

};  // namespace CVC4
