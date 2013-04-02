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
#include "util/cvc4_assert.h"

namespace CVC4 {

bool          ProofManager::isInitialized = false;
ProofManager* ProofManager::proofManager = NULL;

ProofManager::ProofManager(ProofFormat format):
  d_satProof(NULL),
  d_cnfProof(NULL),
  d_format(format)
{}

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
  // for now, this is just the SAT proof
  return getSatProof();
}

SatProof* ProofManager::getSatProof() {
  Assert (currentPM()->d_satProof);
  return currentPM()->d_satProof; 
}

CnfProof* ProofManager::getCnfProof() {
  Assert (currentPM()->d_cnfProof);
  return currentPM()->d_cnfProof;
}

void ProofManager::initSatProof(Minisat::Solver* solver) {
  Assert (currentPM()->d_satProof == NULL);
  switch(currentPM()->d_format) {
  case LFSC :
    currentPM()->d_satProof = new LFSCSatProof(solver);
    break;
  case NATIVE :
    currentPM()->d_satProof = new SatProof(solver);
    break;
  default:
    Assert(false); 
  }
  
}

void ProofManager::initCnfProof(prop::CnfStream* cnfStream) {
  Assert (currentPM()->d_cnfProof == NULL);

  switch(currentPM()->d_format) {
  case LFSC :
    currentPM()->d_cnfProof = new CnfProof(cnfStream); // FIXME
    break;
  case NATIVE :
    currentPM()->d_cnfProof = new CnfProof(cnfStream);
    break;
  default:
    Assert(false); 
  }

}



} /* CVC4  namespace */ 
