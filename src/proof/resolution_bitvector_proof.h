/*********************                                                        */
/*! \file resolution_bitvector_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir, Mathias Preiner, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitvector proof
 **
 ** Bitvector proof
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__RESOLUTION_BITVECTOR_PROOF_H
#define CVC4__PROOF__RESOLUTION_BITVECTOR_PROOF_H

#include <iosfwd>

#include "context/context.h"
#include "expr/expr.h"
#include "proof/bitvector_proof.h"
#include "proof/sat_proof.h"
#include "proof/theory_proof.h"
#include "prop/bvminisat/core/Solver.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver_types.h"
#include "theory/bv/bitblast/bitblaster.h"
#include "theory/bv/theory_bv.h"

namespace CVC4 {

typedef TSatProof<CVC4::BVMinisat::Solver> BVSatProof;

namespace proof {

/**
 * Represents a bitvector proof which is backed by
 * (a) bitblasting and
 * (b) a resolution unsat proof.
 *
 * Contains tools for constructing BV conflicts
 */
class ResolutionBitVectorProof : public BitVectorProof
{
 public:
  ResolutionBitVectorProof(theory::bv::TheoryBV* bv,
                           TheoryProofEngine* proofEngine);

  /**
   * Create an (internal) SAT proof object
   * Must be invoked before manipulating BV conflicts,
   * or initializing a BNF proof
   */
  void initSatProof(CVC4::BVMinisat::Solver* solver);

  BVSatProof* getSatProof();

  void finalizeConflicts(std::vector<Expr>& conflicts) override;

  void startBVConflict(CVC4::BVMinisat::Solver::TCRef cr);
  void startBVConflict(CVC4::BVMinisat::Solver::TLit lit);
  void endBVConflict(const BVMinisat::Solver::TLitVec& confl);

  void markAssumptionConflict() { d_isAssumptionConflict = true; }
  bool isAssumptionConflict() const { return d_isAssumptionConflict; }

  void initCnfProof(prop::CnfStream* cnfStream,
                    context::Context* cnf,
                    prop::SatVariable trueVar,
                    prop::SatVariable falseVar) override;

 protected:
  void attachToSatSolver(prop::SatSolver& sat_solver) override;

  context::Context d_fakeContext;

  // The CNF formula that results from bit-blasting will need a proof.
  // This is that proof.
  std::unique_ptr<BVSatProof> d_resolutionProof;

  bool d_isAssumptionConflict;

};

class LfscResolutionBitVectorProof : public ResolutionBitVectorProof
{
 public:
  LfscResolutionBitVectorProof(theory::bv::TheoryBV* bv,
                               TheoryProofEngine* proofEngine)
      : ResolutionBitVectorProof(bv, proofEngine)
  {
  }
  void printTheoryLemmaProof(std::vector<Expr>& lemma,
                             std::ostream& os,
                             std::ostream& paren,
                             const ProofLetMap& map) override;
  void printBBDeclarationAndCnf(std::ostream& os,
                                std::ostream& paren,
                                ProofLetMap& letMap) override;
  void printEmptyClauseProof(std::ostream& os, std::ostream& paren) override;
  void calculateAtomsInBitblastingProof() override;
};

}  // namespace proof

}  // namespace CVC4

#endif /* CVC4__PROOF__RESOLUTIONBITVECTORPROOF_H */
