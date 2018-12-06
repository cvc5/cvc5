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

#ifndef __CVC4__PROOF__RESOLUTION_BITVECTOR_PROOF_H
#define __CVC4__PROOF__RESOLUTION_BITVECTOR_PROOF_H

#include <iosfwd>

#include "context/context.h"
#include "expr/expr.h"
#include "proof/bitvector_proof.h"
#include "proof/theory_proof.h"
#include "prop/bvminisat/core/Solver.h"

namespace CVC4 {

namespace theory {
namespace bv {
class TheoryBV;
template <class T>
class TBitblaster;
}  // namespace bv
}  // namespace theory

// TODO(aozdemir) break the sat_solver - resolution_bitvectorproof - cnf_stream
// header cycle and remove this.
namespace prop {
class CnfStream;
}

} /* namespace CVC4 */


namespace CVC4 {

template <class Solver>
class TSatProof;
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

  /**
   * Kind of a mess.
   * In eager mode this must be invoked before printing a proof of the empty
   * clause. In lazy mode the behavior is ???
   * TODO(aozdemir) clean this up.
   */
  void finalizeConflicts(std::vector<Expr>& conflicts);

  void startBVConflict(CVC4::BVMinisat::Solver::TCRef cr);
  void startBVConflict(CVC4::BVMinisat::Solver::TLit lit);
  void endBVConflict(const BVMinisat::Solver::TLitVec& confl);

  void markAssumptionConflict() { d_isAssumptionConflict = true; }
  bool isAssumptionConflict() const { return d_isAssumptionConflict; }

  virtual void printResolutionProof(std::ostream& os,
                                    std::ostream& paren,
                                    ProofLetMap& letMap) = 0;

  void initCnfProof(prop::CnfStream* cnfStream, context::Context* cnf) override;

 protected:
  context::Context d_fakeContext;

  // The CNF formula that results from bit-blasting will need a proof.
  // This is that proof.
  std::unique_ptr<BVSatProof> d_resolutionProof;

  bool d_isAssumptionConflict;

  theory::TheoryId getTheoryId() override;
};

class LFSCBitVectorProof : public ResolutionBitVectorProof
{
 public:
  LFSCBitVectorProof(theory::bv::TheoryBV* bv, TheoryProofEngine* proofEngine)
      : ResolutionBitVectorProof(bv, proofEngine)
  {
  }
  void printTheoryLemmaProof(std::vector<Expr>& lemma,
                             std::ostream& os,
                             std::ostream& paren,
                             const ProofLetMap& map) override;
  void printResolutionProof(std::ostream& os,
                            std::ostream& paren,
                            ProofLetMap& letMap) override;
  void calculateAtomsInBitblastingProof() override;
};

}  // namespace proof

}  // namespace CVC4

#endif /* __CVC4__PROOF__RESOLUTIONBITVECTORPROOF_H */
