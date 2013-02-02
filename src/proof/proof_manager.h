/*********************                                                        */
/*! \file proof_manager.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A manager for Proofs.
 **
 ** A manager for Proofs.
 **
 ** 
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROOF_MANAGER_H
#define __CVC4__PROOF_MANAGER_H

#include <iostream> 
#include "proof/proof.h"

// forward declarations
namespace Minisat {
  class Solver;
}

namespace CVC4 {

namespace prop {
  class CnfStream;
}

class Proof;
class SatProof;
class CnfProof;

// different proof modes
enum ProofFormat {
  LFSC,
  NATIVE
};/* enum ProofFormat */

class ProofManager {
  SatProof*   d_satProof;
  CnfProof*   d_cnfProof;
  ProofFormat d_format;
  
  static ProofManager* proofManager; 
  static bool isInitialized; 
  ProofManager(ProofFormat format = LFSC);
public:
  static ProofManager* currentPM();

  static void      initSatProof(Minisat::Solver* solver); 
  static void      initCnfProof(CVC4::prop::CnfStream* cnfStream);

  static Proof* getProof();
  static SatProof* getSatProof();
  static CnfProof* getCnfProof();

};/* class ProofManager */

}/* CVC4 namespace */

#endif /* __CVC4__PROOF_MANAGER_H */
