#include "proof/proof_manager.h"
#include "proof/sat_proof.h"
#include "proof/cnf_proof.h"
#include "util/Assert.h"

namespace CVC4 {

bool          ProofManager::isInitialized = false;
ProofManager* ProofManager::proofManager = NULL;

ProofManager::ProofManager(ProofFormat format = LFSC):
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
