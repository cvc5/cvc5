/*********************                                                        */
/*! \file proof_manager.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
#include "util/proof.h"

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
class TheoryProof;

class LFSCSatProof;
class LFSCCnfProof;
class LFSCTheoryProof;
  
// different proof modes
enum ProofFormat {
  LFSC,
  NATIVE
};/* enum ProofFormat */

class ProofManager {
  SatProof*   d_satProof;
  CnfProof*   d_cnfProof;
  TheoryProof* d_theoryProof; 

  Proof* d_fullProof; 
  ProofFormat d_format;
  
  static ProofManager* proofManager; 
  static bool isInitialized; 
  ProofManager(ProofFormat format = LFSC);
  ~ProofManager(); 
public:
  static ProofManager* currentPM();
  static void      initSatProof(Minisat::Solver* solver); 
  static void      initCnfProof(CVC4::prop::CnfStream* cnfStream);
  static void      initTheoryProof();
  static Proof*    getProof();
  static SatProof* getSatProof();
  static CnfProof* getCnfProof();
  static TheoryProof* getTheoryProof();

  // variable prefixes
  static std::string getInputClausePrefix() { return "pb"; }
  static std::string getLemmaClausePrefix() { return "lem"; }
  static std::string getLearntClausePrefix() { return "cl"; }
  static std::string getVarPrefix() { return "v"; }
  static std::string getAtomPrefix() { return "a"; }
  static std::string getLitPrefix() {return "l"; }
};/* class ProofManager */

class LFSCProof : public Proof {
  LFSCSatProof* d_satProof;
  LFSCCnfProof* d_cnfProof;
  LFSCTheoryProof* d_theoryProof; 
public:
  LFSCProof(LFSCSatProof* sat, LFSCCnfProof* cnf, LFSCTheoryProof* theory); 
  virtual void toStream(std::ostream& out);
  virtual ~LFSCProof() {}
};
  
}/* CVC4 namespace */

#endif /* __CVC4__PROOF_MANAGER_H */
