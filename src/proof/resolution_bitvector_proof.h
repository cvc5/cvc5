/*********************                                                        */
/*! \file resolution_bitvector_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Mathias Preiner, Guy Katz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitvector proof
 **
 ** Bitvector proof
 **/

#include "cvc4_private.h"

#ifndef __CVC4__RESOLUTION__BITVECTOR__PROOF_H
#define __CVC4__RESOLUTION__BITVECTOR__PROOF_H

#include <iostream>
#include <sstream>

#include "expr/expr.h"
#include "proof/bitvector_proof.h"
#include "proof/theory_proof.h"
#include "prop/bvminisat/core/Solver.h"


namespace CVC4 {

namespace prop {
class CnfStream;
} /* namespace CVC4::prop */

namespace theory {
namespace bv {
class TheoryBV;
template <class T> class TBitblaster;
} /* namespace CVC4::theory::bv */
} /* namespace CVC4::theory */

class CnfProof;
} /* namespace CVC4 */

namespace CVC4 {

template <class Solver> class TSatProof;
typedef TSatProof< CVC4::BVMinisat::Solver> BVSatProof;

class ResolutionBitVectorProof : public BitVectorProof {
public:
  ResolutionBitVectorProof(theory::bv::TheoryBV* bv, TheoryProofEngine* proofEngine);

  void initSatProof(CVC4::BVMinisat::Solver* solver);
  void initCnfProof(prop::CnfStream* cnfStream, context::Context* ctx);
  void setBitblaster(theory::bv::TBitblaster<Node>* bb);

  BVSatProof* getSatProof();
  CnfProof* getCnfProof() { return d_cnfProof; }
  void finalizeConflicts(std::vector<Expr>& conflicts);

  void startBVConflict(CVC4::BVMinisat::Solver::TCRef cr);
  void startBVConflict(CVC4::BVMinisat::Solver::TLit lit);
  void endBVConflict(const BVMinisat::Solver::TLitVec& confl);

  void markAssumptionConflict() { d_isAssumptionConflict = true; }
  bool isAssumptionConflict() { return d_isAssumptionConflict; }

  virtual void printResolutionProof(std::ostream& os, std::ostream& paren, ProofLetMap& letMap) = 0;

protected:
  BVSatProof* d_resolutionProof;

  CnfProof* d_cnfProof;

  bool d_isAssumptionConflict;

  theory::TheoryId getTheoryId() override;
  context::Context d_fakeContext;
};

class LFSCBitVectorProof: public ResolutionBitVectorProof {

public:
  LFSCBitVectorProof(theory::bv::TheoryBV* bv, TheoryProofEngine* proofEngine)
    :ResolutionBitVectorProof(bv, proofEngine)
  {}
  void printTheoryLemmaProof(std::vector<Expr>& lemma,
                             std::ostream& os,
                             std::ostream& paren,
                             const ProofLetMap& map) override;
  void printResolutionProof(std::ostream& os,
                            std::ostream& paren,
                            ProofLetMap& letMap) override;
  void calculateAtomsInBitblastingProof() override;
};

}/* CVC4 namespace */

#endif /* __CVC4__RESOLUTION__BITVECTOR__PROOF_H */
