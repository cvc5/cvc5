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
  d_usedClauses.emplace_back(
      id, std::unique_ptr<prop::SatClause>(new prop::SatClause(clause)));
};

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
  Unimplemented();
}

void LfscClausalBitVectorProof::printEmptyClauseProof(std::ostream& os,
                                                      std::ostream& paren)
{
  Unimplemented();
}

}  // namespace proof

};  // namespace CVC4
