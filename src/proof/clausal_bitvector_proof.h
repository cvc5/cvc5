/*********************                                                        */
/*! \file clausal_bitvector_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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

#ifndef CVC4__PROOF__CLAUSAL_BITVECTOR_PROOF_H
#define CVC4__PROOF__CLAUSAL_BITVECTOR_PROOF_H

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
#include "util/statistics_registry.h"

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
  std::unordered_map<ClauseId, prop::SatClause> d_clauses{};
  std::vector<ClauseId> d_originalClauseIndices{};
  // Stores the proof recieved from the SAT solver.
  std::ostringstream d_binaryDratProof{};
  std::vector<ClauseId> d_coreClauseIndices{};

  struct DratTranslationStatistics
  {
    DratTranslationStatistics();
    ~DratTranslationStatistics();

    // Total time spent doing translation (optimized binary DRAT -> in memory
    // target format including IO, postprocessing, etc.)
    TimerStat d_totalTime;
    // Time that the external tool actually spent
    TimerStat d_toolTime;
  };

  DratTranslationStatistics d_dratTranslationStatistics;

 private:
  // Optimizes the DRAT proof stored in `d_binaryDratProof` and returns a list
  // of clause actually needed to check that proof (a smaller UNSAT core)
  void optimizeDratProof();

  // Given reference to a SAT clause encoded as a vector of literals, puts the
  // literals into a canonical order
  static void canonicalizeClause(prop::SatClause& clause);

  struct DratOptimizationStatistics
  {
    DratOptimizationStatistics();
    ~DratOptimizationStatistics();

    // Total time spent using drat-trim to optimize the DRAT proof/formula
    // (including IO, etc.)
    TimerStat d_totalTime;
    // Time that drat-trim actually spent optimizing the DRAT proof/formula
    TimerStat d_toolTime;
    // Time that was spent matching clauses in drat-trim's output to clauses in
    // its input
    TimerStat d_clauseMatchingTime;
    // Bytes in binary DRAT proof before optimization
    IntStat d_initialDratSize;
    // Bytes in binary DRAT proof after optimization
    IntStat d_optimizedDratSize;
    // Bytes in textual DIMACS bitblasted formula before optimization
    IntStat d_initialFormulaSize;
    // Bytes in textual DIMACS bitblasted formula after optimization
    IntStat d_optimizedFormulaSize;
  };

  DratOptimizationStatistics d_dratOptimizationStatistics;
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

#endif /* CVC4__PROOF__CLAUSAL_BITVECTOR_PROOF_H */
