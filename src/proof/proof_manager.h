/*********************                                                        */
/*! \file proof_manager.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A manager for Proofs.
 **
 ** A manager for Proofs.
 **
 ** 
 **/

#ifndef __CVC4__PROOF_MANAGER_H
#define __CVC4__PROOF_MANAGER_H

#include <iostream> 
#include "proof.h"

// forward declarations
namespace Minisat {
class Solver;
}

namespace CVC4 {
namespace prop {
class CnfStream;
}
class SatProof;
class CnfProof;

// different proof modes
enum ProofFormat {
  LFSC,
  NATIVE
};

class ProofManager {
  SatProof*   d_satProof;
  CnfProof*   d_cnfProof;
  ProofFormat d_format;
  
  static ProofManager* proofManager; 
  static bool isInitialized; 
  ProofManager(ProofFormat format);
public:
  static ProofManager* currentPM();

  static void      initSatProof(Minisat::Solver* solver); 
  static void      initCnfProof(CVC4::prop::CnfStream* cnfStream);

  static SatProof* getSatProof();
  static CnfProof* getCnfProof();

};

} /* CVC4 namespace*/ 
#endif /* __CVC4__PROOF_MANAGER_H */
