/*********************                                                        */
/*! \file lrat_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief LRAT Proof Format
 **
 ** Declares C++ types that represent a LRAT proof.
 ** Defines serialization for these types.
 **
 ** Represents an **abstract** LRAT proof.
 ** Does **not** represent an LFSC LRAT proof, or an LRAT proof being used to
 ** prove things about bit-vectors.
 **
 ** Paper on LRAT: https://www.cs.utexas.edu/~marijn/publications/lrat.pdf
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROOF__LRAT__LRAT_PROOF_H
#define __CVC4__PROOF__LRAT__LRAT_PROOF_H

#include <string>
#include <unordered_map>
#include <vector>

#include "base/output.h"
#include "proof/clause_id.h"
// Included because we need operator<< for the SAT types
#include "prop/sat_solver.h"

namespace CVC4 {
namespace proof {
namespace lrat {

// Refers to clause position within an LRAT proof
using ClauseIdx = size_t;

enum LratInstructionKind
{
  LRAT_DELETION,
  LRAT_ADDITION,
};

struct LratDeletionData
{
  LratDeletionData(ClauseIdx idxOfClause, std::vector<ClauseIdx>&& clauses)
      : d_idxOfClause(idxOfClause), d_clauses(clauses)
  {
    // Nothing left to do
  }

  ~LratDeletionData() = default;

  // This idx doesn't really matter, but it's in the format anyway, so we parse
  // it.
  ClauseIdx d_idxOfClause;

  // Clauses to delete
  std::vector<ClauseIdx> d_clauses;
};

// A sequence of locations that will contain unit clauses during unit
// propegation
using LratUPTrace = std::vector<ClauseIdx>;

struct LratAdditionData
{
  LratAdditionData(ClauseIdx idxOfClause,
                   prop::SatClause&& clause,
                   LratUPTrace&& atTrace,
                   std::vector<std::pair<ClauseIdx, LratUPTrace>> resolvants)
      : d_idxOfClause(idxOfClause),
        d_clause(clause),
        d_atTrace(atTrace),
        d_resolvants(resolvants)
  {
    // Nothing left to do
  }

  ~LratAdditionData() = default;

  // The idx for the new clause
  ClauseIdx d_idxOfClause;
  // The new clause
  prop::SatClause d_clause;
  // UP trace based on the negation of that clause
  LratUPTrace d_atTrace;

  // Clauses that can resolve with `clause` on its first variable,
  // together with a UP trace after that resolution.
  // Used for RAT checks.
  std::vector<std::pair<ClauseIdx, LratUPTrace>> d_resolvants;
};

// This is conceptually an Either<Addition,Deletion>
struct LratInstruction
{
  LratInstructionKind d_kind;
  union LratInstructionData
  {
    LratAdditionData d_addition;
    LratDeletionData d_deletion;
    ~LratInstructionData(){/* Empty destructor */};
    LratInstructionData(){/* Empty constructor */};
  } d_data;

 public:
  LratInstruction(LratInstruction&& instr);
  LratInstruction(LratInstruction& instr);
  LratInstruction(LratAdditionData&& addition);
  LratInstruction(LratDeletionData&& deletion);
  ~LratInstruction();
};

class LratProof
{
 public:
  /**
   * @brief Construct an LRAT proof from a DRAT proof, using drat-trim
   *
   * @param usedClauses The CNF formula that we're deriving bottom from.
   *                    It's a map because other parts of the system represent
   *                    it this way.
   * @param clauseOrder A record of the order in which those clauses were
   *                    given to the SAT solver.
   * @param dratBinary  The DRAT proof from the SAT solver, as a binary stream.
   */
  static LratProof fromDratProof(
      const std::unordered_map<ClauseId, prop::SatClause*>& usedClauses,
      const std::vector<ClauseId>& clauseOrder,
      const std::string& dratBinary);
  /**
   * @brief Construct an LRAT proof from its textual representation
   *
   * @param textualProof the textual encoding of the LRAT proof. See the paper
   *                     in the file's header comment.
   */
  LratProof(std::istream& textualProof);

  inline const std::vector<LratInstruction>& getInstructions() const
  {
    return d_instructions;
  }

 private:
  // The instructions in the proof. Each is a deletion or addition.
  std::vector<LratInstruction> d_instructions;
};

// Prints the LRAT proof in textual format
std::ostream& operator<<(std::ostream& o, const LratProof& p);

}  // namespace lrat
}  // namespace proof
}  // namespace CVC4

#endif
