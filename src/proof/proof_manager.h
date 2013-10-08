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
typedef int ClauseId;

class Proof;
class SatProof;
class CnfProof;
class TheoryProof;

class LFSCSatProof;
class LFSCCnfProof;
class LFSCTheoryProof;

namespace prop {
typedef uint64_t SatVariable;
class SatLiteral;
}

// different proof modes
enum ProofFormat {
  LFSC,
  NATIVE
};/* enum ProofFormat */

std::string append(const std::string& str, uint64_t num);

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
  static std::string printInputClauseName(ClauseId id);
  static std::string printLemmaClauseName(ClauseId id);
  static std::string printLearntClauseName(ClauseId id);

  static std::string printVarName(prop::SatVariable var);
  static std::string printAtomName(prop::SatVariable var);
  static std::string printLitName(prop::SatLiteral lit);
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
