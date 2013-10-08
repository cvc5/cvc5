/*********************                                                        */
/*! \file proof_manager.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "proof/proof_manager.h"
#include "util/proof.h"
#include "proof/sat_proof.h"
#include "proof/cnf_proof.h"
#include "proof/theory_proof.h"
#include "util/cvc4_assert.h"

namespace CVC4 {

bool          ProofManager::isInitialized = false;
ProofManager* ProofManager::proofManager = NULL;

ProofManager::ProofManager(ProofFormat format):
  d_satProof(NULL),
  d_cnfProof(NULL),
  d_theoryProof(NULL),
  d_fullProof(NULL),
  d_format(format)
{
}

ProofManager::~ProofManager() {
  delete d_satProof;
  delete d_cnfProof;
  delete d_theoryProof;
  delete d_fullProof; 
}

ProofManager* ProofManager::currentPM() {
  if (isInitialized) {
    return proofManager; 
  } else {
    proofManager = new ProofManager();
    isInitialized = true; 
    return proofManager; 
  }
}

Proof* ProofManager::getProof() {
  if (currentPM()->d_fullProof != NULL)
    return currentPM()->d_fullProof;
  Assert (currentPM()->d_format == LFSC);

  currentPM()->d_fullProof = new LFSCProof((LFSCSatProof*)getSatProof(),
                                           (LFSCCnfProof*)getCnfProof(),
                                           (LFSCTheoryProof*)getTheoryProof()); 
  return currentPM()->d_fullProof;
}

SatProof* ProofManager::getSatProof() {
  Assert (currentPM()->d_satProof);
  return currentPM()->d_satProof; 
}

CnfProof* ProofManager::getCnfProof() {
  Assert (currentPM()->d_cnfProof);
  return currentPM()->d_cnfProof;
}

TheoryProof* ProofManager::getTheoryProof() {
  Assert (currentPM()->d_theoryProof);
  return currentPM()->d_theoryProof;
}


void ProofManager::initSatProof(Minisat::Solver* solver) {
  Assert (currentPM()->d_satProof == NULL);
  Assert(currentPM()->d_format == LFSC);
  currentPM()->d_satProof = new LFSCSatProof(solver);
}

void ProofManager::initCnfProof(prop::CnfStream* cnfStream) {
  Assert (currentPM()->d_cnfProof == NULL);
  Assert (currentPM()->d_format == LFSC);
  currentPM()->d_cnfProof = new LFSCCnfProof(cnfStream); 
}

void ProofManager::initTheoryProof() {
  Assert (currentPM()->d_theoryProof == NULL);
  Assert (currentPM()->d_format == LFSC);
  currentPM()->d_theoryProof = new LFSCTheoryProof();
}

LFSCProof::LFSCProof(LFSCSatProof* sat, LFSCCnfProof* cnf, LFSCTheoryProof* theory)
  : d_satProof(sat)
  , d_cnfProof(cnf)
  , d_theoryProof(theory)
{
  // link the proofs
  d_satProof->setCnfProof(d_cnfProof);
  d_cnfProof->setTheoryProof(d_theoryProof);
  // build the resolution proof out of the traces
  // this sets up the other proofs with the necessary information
  d_satProof->constructProof();
}

void LFSCProof::toStream(std::ostream& out) {
  std::ostringstream paren;
  out << "(check \n";
  d_theoryProof->printDeclarations(out, paren);
  out << "(: (holds cln) \n";
  d_cnfProof->printAtomMapping(out, paren);
  d_cnfProof->printClauses(out, paren);
  d_satProof->printResolutions(out, paren); 
  paren <<"))";
  out << paren.str(); 
}

// void ProofManager::declareAtom(Expr atom, SatLiteral lit) {
//   ::Minisat::Lit mlit = toMinisatLit(lit); 
//   d_satProof->addLiteral(mlit);
//   d_cnfProof->declareAtom(atom, mlit); 
// }

// void ProofManager::addInputClause(SatClause clause) {
//   d_satProof->registerClause(clause, true); 
//   d_cnfProof->registerClause(clause, true); 
// }


} /* CVC4  namespace */ 
