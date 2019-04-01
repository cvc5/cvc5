/*********************                                                        */
/*! \file clausal_bitvector_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitvector proof for clausal (DRAT/LRAT) formats
 **
 ** An internal string stream is hooked up to CryptoMiniSat, which spits out a
 ** binary DRAT proof. Depending on which kind of proof we're going to turn
 ** that into, we process it in different ways.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROOF__CLAUSAL_BITVECTOR_PROOF_H
#define __CVC4__PROOF__CLAUSAL_BITVECTOR_PROOF_H

#include <iostream>
#include <sstream>
#include <unordered_map>

#include "expr/expr.h"
#include "proof/bitvector_proof.h"
#include "proof/drat/drat_proof.h"
#include "proof/lrat/lrat_proof.h"
#include "proof/theory_proof.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver_types.h"
#include "theory/bv/theory_bv.h"

namespace CVC4 {

namespace proof {

class ClausalBitVectorProof : public BitVectorProof
{
 public:
  ClausalBitVectorProof(theory::bv::TheoryBV* bv,
                        TheoryProofEngine* proofEngine);

  ~ClausalBitVectorProof() = default;

  void attachToSatSolver(prop::SatSolver& sat_solver) override;

  void initCnfProof(prop::CnfStream* cnfStream,
                    context::Context* cnf,
                    prop::SatVariable trueVar,
                    prop::SatVariable falseVar) override;

  std::ostream& getDratOstream() { return d_binaryDratProof; }

  void registerUsedClause(ClauseId id, prop::SatClause& clause);

  void calculateAtomsInBitblastingProof() override;

 protected:
  // A list of all clauses and their ids which are passed into the SAT solver
  std::vector<std::pair<ClauseId, prop::SatClause>> d_usedClauses;
  // Stores the proof recieved from the SAT solver.
  std::ostringstream d_binaryDratProof;
};

/**
 * A representation of a clausal proof of a bitvector problem's UNSAT nature
 */
class LfscClausalBitVectorProof : public ClausalBitVectorProof
{
 public:
  LfscClausalBitVectorProof(theory::bv::TheoryBV* bv,
                            TheoryProofEngine* proofEngine)
      : ClausalBitVectorProof(bv, proofEngine)
  {
  }

  void printTheoryLemmaProof(std::vector<Expr>& lemma,
                             std::ostream& os,
                             std::ostream& paren,
                             const ProofLetMap& map) override;
  void printBBDeclarationAndCnf(std::ostream& os,
                                std::ostream& paren,
                                ProofLetMap& letMap) override;
};

/**
 * A DRAT proof for a bit-vector problem
 */
class LfscDratBitVectorProof : public LfscClausalBitVectorProof
{
 public:
  LfscDratBitVectorProof(theory::bv::TheoryBV* bv,
                         TheoryProofEngine* proofEngine)
      : LfscClausalBitVectorProof(bv, proofEngine)
  {
  }

  void printEmptyClauseProof(std::ostream& os, std::ostream& paren) override;
};

/**
 * An LRAT proof for a bit-vector problem
 */
class LfscLratBitVectorProof : public LfscClausalBitVectorProof
{
 public:
  LfscLratBitVectorProof(theory::bv::TheoryBV* bv,
                         TheoryProofEngine* proofEngine)
      : LfscClausalBitVectorProof(bv, proofEngine)
  {
  }

  void printEmptyClauseProof(std::ostream& os, std::ostream& paren) override;
};

/**
 * An Extended Resolution proof for a bit-vector problem
 */
class LfscErBitVectorProof : public LfscClausalBitVectorProof
{
 public:
  LfscErBitVectorProof(theory::bv::TheoryBV* bv, TheoryProofEngine* proofEngine)
      : LfscClausalBitVectorProof(bv, proofEngine)
  {
  }

  void printEmptyClauseProof(std::ostream& os, std::ostream& paren) override;
};

}  // namespace proof

}  // namespace CVC4

#endif /* __CVC4__PROOF__CLAUSAL_BITVECTOR_PROOF_H */
